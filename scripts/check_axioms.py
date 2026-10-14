#!/usr/bin/env python3
"""Enforce the allowed axioms and exact target coverage of a fresh Lean audit."""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import sys

from verify_sources import strip_comments_and_strings


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGET = re.compile(r"^\s*#print\s+axioms\s+([\w.']+)\s*$", re.MULTILINE)
FOOTPRINT = re.compile(
    r"'([^'\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
)


def validate(
    audit_source: str, audit_output: str, required_targets: tuple[str, ...] | list[str] = ()
) -> tuple[list[str], int]:
    source = strip_comments_and_strings(audit_source)
    targets = TARGET.findall(source)
    errors = []
    if not targets:
        errors.append("audit source contains no #print axioms targets")
    duplicates = [name for name, count in Counter(targets).items() if count != 1]
    if duplicates:
        errors.append("duplicate audit targets: " + ", ".join(sorted(duplicates)))
    for name in sorted(set(required_targets) - set(targets)):
        errors.append(f"required public declaration missing from audit source: {name}")
    # A malformed/unsupported target line must not silently shrink the expected set.
    if len(re.findall(r"#print\s+axioms\b", source)) != len(targets):
        errors.append("unsupported or malformed #print axioms command")
    entries = FOOTPRINT.findall(audit_output)
    reported = [name for name, _ in entries]
    for name, count in Counter(reported).items():
        if count != 1:
            errors.append(f"duplicate audit output for {name}")
    for name in sorted(set(targets) - set(reported)):
        errors.append(f"missing axiom audit output for {name}")
    for name in sorted(set(reported) - set(targets)):
        errors.append(f"unexpected axiom audit output for {name}")
    for name, body in entries:
        axioms = {item.strip() for item in body.split(",") if item.strip()}
        forbidden = axioms - ALLOWED
        if forbidden:
            errors.append(f"{name}: disallowed axioms: {', '.join(sorted(forbidden))}")
    if re.search(r"\b(?:error:|PANIC|uncaught exception)", audit_output, re.IGNORECASE):
        errors.append("audit output contains an error diagnostic")
    return errors, len(entries)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="stdout/stderr captured from lake env lean AxiomAudit.lean")
    parser.add_argument("--audit", type=Path, default=Path(__file__).resolve().parents[1] / "AxiomAudit.lean")
    parser.add_argument(
        "--required", type=Path,
        default=Path(__file__).resolve().parents[1] / "audit" / "public-declarations.txt",
        help="required public declarations, one name per line; blank lines and # comments ignored",
    )
    args = parser.parse_args()
    try:
        required = [line.strip() for line in args.required.read_text().splitlines()
                    if line.strip() and not line.lstrip().startswith("#")]
        if not required or len(required) != len(set(required)):
            raise ValueError("required public-declaration list must be nonempty and have no duplicates")
        if any(not re.fullmatch(r"[\w.']+", name) for name in required):
            raise ValueError("malformed name in required public-declaration list")
        errors, count = validate(args.audit.read_text(), args.output.read_text(), required)
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"Axiom verification failed: {exc}", file=sys.stderr)
        return 1
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"PASS: {count} exact audit targets use only the allowed standard axioms")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
