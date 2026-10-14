#!/usr/bin/env python3
"""Fail closed on unbuilt tracked Lean modules and proof placeholders."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys
import tomllib


FORBIDDEN = re.compile(r"\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|partial)\b")
CHAR_LITERAL = re.compile(r"'(?:[^'\\\n]|\\(?:[\\\"'rnt]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}))'")
SEPARATELY_CHECKED = {"AxiomAudit.lean"}
OPTIONAL_AUDITS = {"AllDeclarationsAudit.lean"}


def strip_comments_and_strings(source: str) -> str:
    """Blank Lean comments and strings, preserving newlines for diagnostics."""
    out = list(source)
    i, size = 0, len(source)

    def blank(start: int, end: int) -> None:
        for k in range(start, end):
            if out[k] != "\n":
                out[k] = " "

    while i < size:
        start = i
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = size if end < 0 else end
            blank(start, i)
        elif source.startswith("/-", i):
            depth = 1
            i += 2
            while i < size and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated block comment")
            blank(start, i)
        elif source[i] == "«":
            # Escaped identifiers may contain quote/comment characters. Keep
            # their text conservatively visible to the token guard.
            end = source.find("»", i + 1)
            if end < 0:
                raise ValueError("unterminated escaped identifier")
            i = end + 1
        else:
            # A quote character, e.g. '\"', is not the start of a string.
            # Do not consume apostrophes belonging to Lean identifiers.
            char = None
            if source[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
                char = CHAR_LITERAL.match(source, i)
            if char:
                i = char.end()
                blank(start, i)
                continue
            raw = re.match(r'r(#*)"', source[i:])
            if raw:
                close = '"' + raw.group(1)
                end = source.find(close, i + len(raw.group(0)))
                if end < 0:
                    raise ValueError("unterminated raw string")
                i = end + len(close)
                blank(start, i)
            elif source[i] == '"':
                i += 1
                while i < size:
                    if source[i] == "\\":
                        i += 2
                    elif source[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
                else:
                    raise ValueError("unterminated string")
                blank(start, min(i, size))
            else:
                i += 1
    return "".join(out)


def tracked_lean_files(root: Path) -> list[str]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"],
        cwd=root, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    files = sorted(x for x in result.stdout.decode("utf-8").split("\0") if x)
    if not files:
        raise ValueError("git reported no tracked Lean sources")
    return files


def verify(root: Path) -> list[str]:
    files = tracked_lean_files(root)
    untracked = subprocess.run(
        ["git", "ls-files", "-z", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=root, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    config = tomllib.loads((root / "lakefile.toml").read_text())
    roots: set[str] = set()
    modules: set[str] = set()
    libraries: set[str] = set()
    errors = []
    for library in config.get("lean_lib", []):
        libraries.add(library["name"])
        # Lake's roots name module hierarchies; overridden globs or facets can
        # silently stop the default build from checking those roots.
        if library.get("globs", library.get("roots", [])) != library.get("roots", []):
            errors.append(f"{library['name']}: non-default globs may omit declared roots from the build")
        if library.get("defaultFacets", ["leanArts"]) != ["leanArts"]:
            errors.append(f"{library['name']}: non-default defaultFacets may skip Lean proof checking")
        for module in library.get("roots", []):
            modules.add(module)
            path = Path(library.get("srcDir", ".")) / (module.replace(".", "/") + ".lean")
            roots.add(path.as_posix())
    if not roots:
        raise ValueError("lakefile.toml declares no explicit library roots")
    errors.extend(
        f"{file}: untracked Lean source; track it and add its library root before verification"
        for file in untracked.stdout.decode("utf-8").split("\0") if file
    )
    for library in sorted(libraries - set(config.get("defaultTargets", []))):
        errors.append(f"{library}: library is absent from defaultTargets and may not be built")
    for file in sorted(set(files) - roots - SEPARATELY_CHECKED - OPTIONAL_AUDITS):
        errors.append(f"{file}: tracked module is absent from the library roots")
    for file in sorted((roots | SEPARATELY_CHECKED) - set(files)):
        errors.append(f"{file}: required source is not tracked")
    for file in files:
        try:
            source = strip_comments_and_strings((root / file).read_text())
        except (OSError, UnicodeError, ValueError) as exc:
            errors.append(f"{file}: cannot scan source: {exc}")
            continue
        if file == "AllDeclarationsAudit.lean":
            imports = set(re.findall(r"^import[ \t]+([\w.']+)[ \t]*$", source, re.MULTILINE))
            for module in sorted(modules - imports):
                errors.append(f"{file}: proof root {module} needs its own explicit import line")
        for match in FORBIDDEN.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            errors.append(f"{file}:{line}: forbidden proof token {match.group()!r}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    try:
        errors = verify(args.root.resolve())
    except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"Source verification failed: {exc}", file=sys.stderr)
        return 1
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("PASS: every tracked Lean module is built or separately audited; lexical proof-token check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
