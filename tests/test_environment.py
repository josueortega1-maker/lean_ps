"""Reject mismatched toolchains and modified dependency checkouts."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_environment import inspect_environment


class EnvironmentTests(unittest.TestCase):
    version = "Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)"

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
        self.dep = self.root / ".lake/packages/demo"
        self.dep.mkdir(parents=True)
        self.git("init", "-q")
        self.git("config", "user.name", "Verification Test")
        self.git("config", "user.email", "test@example.invalid")
        (self.dep / "Proof.lean").write_text("theorem good : True := True.intro\n")
        (self.dep / ".gitignore").write_text(".lake/\n")
        self.git("add", ".")
        self.git("commit", "-qm", "baseline")
        self.revision = self.git("rev-parse", "HEAD")
        self.write_manifest(self.revision)

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.dep, text=True).strip()

    def write_manifest(self, revision):
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "packagesDir": ".lake/packages", "packages": [
                {"name": "demo", "type": "git", "rev": revision}]}))

    def test_exact_clean_pins_pass_and_ignored_build_files_are_allowed(self):
        (self.dep / ".lake").mkdir()
        (self.dep / ".lake/generated.lean").write_text("generated build input")
        result = inspect_environment(self.root, self.version)
        self.assertEqual(result["dependencies"]["demo"]["commit"], self.revision)

    def test_running_version_must_match_declared_pin(self):
        with self.assertRaisesRegex(ValueError, "Lean version mismatch"):
            inspect_environment(self.root, self.version.replace("4.19.0", "4.20.0"))

    def test_actual_dependency_revision_must_match_manifest(self):
        self.write_manifest("0" * 40)
        with self.assertRaisesRegex(ValueError, "dependency revision mismatch"):
            inspect_environment(self.root, self.version)

    def test_modified_tracked_dependency_file_fails(self):
        (self.dep / "Proof.lean").write_text("theorem changed : False := sorry\n")
        with self.assertRaisesRegex(ValueError, "tracked or untracked changes"):
            inspect_environment(self.root, self.version)

    def test_new_untracked_dependency_source_fails(self):
        (self.dep / "Unchecked.lean").write_text("theorem unchecked : True := True.intro\n")
        with self.assertRaisesRegex(ValueError, "tracked or untracked changes"):
            inspect_environment(self.root, self.version)

    def test_missing_checkout_fails(self):
        self.dep.rename(self.dep.with_name("missing-demo"))
        with self.assertRaisesRegex(ValueError, "checkout is missing"):
            inspect_environment(self.root, self.version)


if __name__ == "__main__":
    unittest.main()
