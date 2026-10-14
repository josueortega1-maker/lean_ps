#!/usr/bin/env python3
"""Verify the running Lean version and clean dependency trees against the pins."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=root, text=True,
                                   stderr=subprocess.PIPE).strip()


def inspect_environment(root: Path, lean_output: str) -> dict:
    declared = (root / "lean-toolchain").read_text().strip()
    expected = re.fullmatch(r"leanprover/lean4:v([^\s]+)", declared)
    actual = re.search(r"Lean \(version ([^,\s)]+)[,)]", lean_output)
    if not expected or not actual:
        raise ValueError("cannot parse pinned toolchain or actual Lean version")
    if actual.group(1) != expected.group(1):
        raise ValueError(f"Lean version mismatch: pinned {expected.group(1)}, running {actual.group(1)}")

    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = manifest.get("packages", [])
    if not packages:
        raise ValueError("dependency manifest has no packages")
    package_dir = root / manifest.get("packagesDir", ".lake/packages")
    dependencies = {}
    for package in packages:
        name, revision = package["name"], package["rev"]
        if name in dependencies:
            raise ValueError(f"duplicate dependency in manifest: {name}")
        if package.get("type") != "git" or not re.fullmatch(r"[0-9a-fA-F]{40}", revision):
            raise ValueError(f"{name}: dependency is not pinned to a full git commit")
        location = (package_dir / name).resolve()
        if not location.is_dir():
            raise ValueError(f"{name}: dependency checkout is missing; fetch the pinned cache first")
        top = Path(git(location, "rev-parse", "--show-toplevel")).resolve()
        if top != location:
            raise ValueError(f"{name}: package directory is not its own git checkout")
        head = git(location, "rev-parse", "HEAD")
        if head.lower() != revision.lower():
            raise ValueError(f"{name}: dependency revision mismatch: expected {revision}, got {head}")
        status = git(location, "status", "--porcelain", "--untracked-files=all")
        if status:
            raise ValueError(f"{name}: dependency has tracked or untracked changes:\n{status}")
        dependencies[name] = {"commit": head, "clean": True}
    return {"declared_toolchain": declared, "actual_lean_version": actual.group(1),
            "actual_lean_output": lean_output.strip(), "dependencies": dependencies}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        version = subprocess.check_output(["lake", "env", "lean", "--version"],
                                          cwd=root, text=True, stderr=subprocess.STDOUT)
        result = inspect_environment(root, version)
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        print(f"Environment verification failed: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
