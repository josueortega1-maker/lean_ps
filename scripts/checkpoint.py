#!/usr/bin/env python3
"""Save a verified full-history local bundle of a committed work step."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("step", type=int, choices=range(1, 13))
    args = parser.parse_args()
    if git("diff", "--cached", "--name-only"):
        raise SystemExit("Commit staged changes before checkpointing.")
    commit = git("rev-parse", "HEAD")
    destination = ROOT.parent / "lean-checkpoints"
    destination.mkdir(exist_ok=True)
    bundle = destination / f"step-{args.step:02d}-{commit[:12]}.bundle"
    if not bundle.exists():
        git("bundle", "create", str(bundle), "--all")
    git("bundle", "verify", str(bundle))
    state = {
        "step": args.step, "commit": commit,
        "upstream_base": "8926a649fba448075de751ca0014c5dd29eaf7d5",
        "bundle": bundle.name,
        "sha256": hashlib.sha256(bundle.read_bytes()).hexdigest(),
        "unstaged_not_in_bundle": git("diff", "--name-only").splitlines(),
        "untracked_not_in_bundle": git("ls-files", "--others", "--exclude-standard").splitlines(),
        "pushed": False,
    }
    record = destination / f"step-{args.step:02d}.json"
    record.write_text(json.dumps(state, indent=2) + "\n")
    temporary = destination / "LATEST.json.tmp"
    temporary.write_text(record.read_text())
    temporary.replace(destination / "LATEST.json")
    print(json.dumps(state, indent=2))


if __name__ == "__main__":
    main()
