#!/usr/bin/env python3
"""Build and audit this source revision, retaining evidence even on failure."""
from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def source_hashes():
    paths = git("ls-files", "-z").split("\0")
    selected = [p for p in paths if p and (
        p.endswith((".lean", ".py", ".yml")) or
        p in {".gitignore", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
              "audit/public-declarations.txt"})]
    if not selected:
        raise RuntimeError("No tracked verification inputs")
    return {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
            for p in sorted(selected)}


def write_receipt(output, receipt):
    temporary = output / "verification.json.tmp"
    temporary.write_text(json.dumps(receipt, indent=2) + "\n")
    temporary.replace(output / "verification.json")


def project_build_outputs():
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    build_dir = ROOT / config.get("buildDir", ".lake/build")
    lean_dir = build_dir / config.get("leanLibDir", "lib/lean")
    outputs = {module: lean_dir / (module.replace(".", "/") + ".olean")
               for library in config.get("lean_lib", []) for module in library.get("roots", [])}
    if not outputs:
        raise RuntimeError("No explicit project roots to check for fresh build outputs")
    return build_dir, outputs


def require_absent_build_dir(build_dir):
    if build_dir.exists() or build_dir.is_symlink():
        raise RuntimeError(f"Clean build failed: project build directory still exists: {build_dir}")


def check_fresh_build_outputs(outputs, started_ns, build_log):
    replayed = set(re.findall(r"\] Replayed (\S+)", build_log)) & outputs.keys()
    if replayed:
        raise RuntimeError("Clean build replayed project roots: " + ", ".join(sorted(replayed)))
    times = {}
    for module, path in sorted(outputs.items()):
        if not path.is_file() or path.stat().st_mtime_ns < started_ns:
            raise RuntimeError(f"Clean build output missing or older than this build: {module}: {path}")
        times[module] = path.stat().st_mtime_ns
    return times


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "verification-output")
    parser.add_argument("--clean", action="store_true",
                        help="remove this project's build outputs before checking; retain dependency caches")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    receipt = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "checks": [], "success": False,
    }
    # Replace any previous success before touching metadata or logs. An abrupt
    # process termination cannot run finally, but still leaves this failed/
    # incomplete receipt rather than certifying the new run with old evidence.
    write_receipt(output, receipt)
    commands = [
        ("environment", [sys.executable, "scripts/check_environment.py"]),
        ("sources", [sys.executable, "scripts/verify_sources.py"]),
        ("gate-tests", [sys.executable, "-m", "unittest", "discover", "-s", "tests"]),
        *([("clean", ["lake", "--no-cache", "clean", "PSTheorem1"])] if args.clean else []),
        ("build", ["lake", "--no-cache", "-v", "build"] if args.clean else ["lake", "build"]),
        ("all-declarations", ["lake", "env", "lean", "AllDeclarationsAudit.lean"]),
        ("axioms", ["lake", "env", "lean", "AxiomAudit.lean"]),
        ("axiom-policy", [sys.executable, "scripts/check_axioms.py", str(output / "axioms.log")]),
        ("sources-final", [sys.executable, "scripts/verify_sources.py"]),
        ("environment-final", [sys.executable, "scripts/check_environment.py"]),
    ]
    try:
        receipt.update({
            "commit": git("rev-parse", "HEAD"),
            "working_tree_status": git("status", "--short"),
            "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "clean_project_build": args.clean,
            "sources_sha256": source_hashes(),
        })
        if args.clean:
            build_dir, build_outputs = project_build_outputs()
        for name, command in commands:
            print(f"Checking {name}...", flush=True)
            if args.clean and name == "build":
                require_absent_build_dir(build_dir)
                build_started_ns = time.time_ns()
            with (output / f"{name}.log").open("w") as stream:
                result = subprocess.run(command, cwd=ROOT, stdout=stream,
                                        stderr=subprocess.STDOUT, check=False)
            receipt["checks"].append({"name": name, "command": command,
                                      "exit_code": result.returncode})
            if result.returncode:
                raise RuntimeError(f"{name} failed; see {output / (name + '.log')}")
            if args.clean and name == "clean":
                require_absent_build_dir(build_dir)
                receipt["build_directory_absent_after_clean"] = True
            if args.clean and name == "build":
                receipt["fresh_project_outputs"] = {
                    "build_started_ns": build_started_ns,
                    "olean_mtime_ns": check_fresh_build_outputs(
                        build_outputs, build_started_ns, (output / "build.log").read_text()),
                }
        if source_hashes() != receipt["sources_sha256"]:
            raise RuntimeError("Verification inputs changed during checking")
        receipt["success"] = True
    except (OSError, ValueError, subprocess.CalledProcessError, RuntimeError) as error:
        receipt["error"] = str(error)
        print(str(error), file=sys.stderr)
    finally:
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        write_receipt(output, receipt)
    if not receipt["success"]:
        return 1
    print(f"PASS: pinned environment, build, contracts, source coverage and all-declaration axiom audit; evidence in {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
