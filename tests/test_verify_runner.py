"""A failed new verification must never leave a previous successful receipt."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    "verify_runner", Path(__file__).resolve().parents[1] / "scripts" / "verify.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class VerificationReceiptTests(unittest.TestCase):
    def test_abrupt_exit_replaces_previous_success_before_finally(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
            output = root / "output"
            output.mkdir()
            receipt = output / "verification.json"
            receipt.write_text(json.dumps({"success": True, "commit": "old"}))
            child = '''import importlib.util, os, sys
from pathlib import Path
spec = importlib.util.spec_from_file_location("runner", sys.argv[1])
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
runner.ROOT = Path(sys.argv[2])
runner.git = lambda *args: "current"
runner.source_hashes = lambda: os._exit(73)
sys.argv = ["verify.py", "--output", sys.argv[3]]
runner.main()
'''
            result = subprocess.run([sys.executable, "-c", child, runner.__file__,
                                     str(root), str(output)], check=False)
            self.assertEqual(result.returncode, 73)
            actual = json.loads(receipt.read_text())
            self.assertIs(actual["success"], False)
            self.assertNotIn("finished_utc", actual)
            self.assertNotIn("commit", actual)

    def test_missing_source_replaces_old_success_with_current_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
            output = root / "output"
            output.mkdir()
            receipt = output / "verification.json"
            receipt.write_text(json.dumps({"success": True, "commit": "old"}))
            with patch.object(runner, "ROOT", root), \
                 patch.object(runner, "git", return_value="current"), \
                 patch.object(runner, "source_hashes", side_effect=FileNotFoundError("Lost.lean")), \
                 patch("sys.argv", ["verify.py", "--output", str(output)]):
                self.assertEqual(runner.main(), 1)
            actual = json.loads(receipt.read_text())
            self.assertIs(actual["success"], False)
            self.assertIn("Lost.lean", actual["error"])
            self.assertIn("finished_utc", actual)

    def test_each_final_guard_can_reject_a_run_after_the_build_passes(self):
        for guard in ("scripts/verify_sources.py", "scripts/check_environment.py"):
            with self.subTest(guard=guard), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
                calls = []

                def command_result(command, **kwargs):
                    calls.append(command)
                    count = sum(guard in call for call in calls)
                    return subprocess.CompletedProcess(command, 1 if guard in command and count == 2 else 0)

                with patch.object(runner, "ROOT", root), \
                     patch.object(runner, "git", return_value="current"), \
                     patch.object(runner, "source_hashes", return_value={"Main.lean": "fixed"}), \
                     patch.object(runner.subprocess, "run", side_effect=command_result), \
                     patch("sys.argv", ["verify.py", "--output", str(root / "output")]):
                    self.assertEqual(runner.main(), 1)
                actual = json.loads((root / "output/verification.json").read_text())
                self.assertIs(actual["success"], False)
                self.assertEqual(sum(guard in call for call in calls), 2)
                self.assertIn(["lake", "build"], calls)
                self.assertTrue(actual["checks"][-1]["name"].endswith("-final"))

    def test_gitignore_changes_are_part_of_source_hashes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / ".gitignore").write_text(".lake/\n")
            (root / "Main.lean").write_text("theorem good : True := True.intro\n")
            with patch.object(runner, "ROOT", root), \
                 patch.object(runner, "git", return_value=".gitignore\0Main.lean\0"):
                before = runner.source_hashes()
                (root / ".gitignore").write_text(".lake/\nUnchecked.lean\n")
                after = runner.source_hashes()
            self.assertIn(".gitignore", before)
            self.assertNotEqual(before, after)


class CleanBuildEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.build_dir = self.root / ".lake/build"
        self.olean = self.build_dir / "lib/lean/Main.olean"
        self.outputs = {"Main": self.olean}
        self.started_ns = 2_000_000_000

    def artifact(self, mtime_ns):
        self.olean.parent.mkdir(parents=True, exist_ok=True)
        self.olean.write_bytes(b"test artifact")
        os.utime(self.olean, ns=(mtime_ns, mtime_ns))

    def test_clean_must_actually_remove_the_build_directory(self):
        runner.require_absent_build_dir(self.build_dir)
        self.build_dir.mkdir(parents=True)
        with self.assertRaisesRegex(RuntimeError, "still exists"):
            runner.require_absent_build_dir(self.build_dir)

    def test_restored_old_output_cannot_certify_a_clean_build(self):
        self.artifact(self.started_ns - 1)
        with self.assertRaisesRegex(RuntimeError, "older than this build"):
            runner.check_fresh_build_outputs(self.outputs, self.started_ns, "Built Main\n")

    def test_missing_output_cannot_certify_a_clean_build(self):
        with self.assertRaisesRegex(RuntimeError, "missing"):
            runner.check_fresh_build_outputs(self.outputs, self.started_ns, "Built Main\n")

    def test_project_replay_is_rejected_even_if_mtime_looks_fresh(self):
        self.artifact(self.started_ns + 1)
        with self.assertRaisesRegex(RuntimeError, "replayed project roots: Main"):
            runner.check_fresh_build_outputs(self.outputs, self.started_ns, "⚠ [1/1] Replayed Main\n")

    def test_fresh_project_output_allows_dependency_replays(self):
        self.artifact(self.started_ns + 1)
        times = runner.check_fresh_build_outputs(
            self.outputs, self.started_ns, "⚠ [1/2] Replayed Mathlib.Data.Nat.Basic\n✔ [2/2] Built Main\n")
        self.assertEqual(times, {"Main": self.started_ns + 1})

    def test_clean_runner_uses_no_cache_and_records_fresh_outputs(self):
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
        (self.root / "lakefile.toml").write_text('[[lean_lib]]\nname="Main"\nroots=["Main"]\n')
        calls = []

        def command_result(command, **kwargs):
            calls.append(command)
            if command[-1] == "build":
                self.artifact(self.started_ns + 1)
                kwargs["stdout"].write("✔ [1/1] Built Main\n")
            return subprocess.CompletedProcess(command, 0)

        with patch.object(runner, "ROOT", self.root), \
             patch.object(runner, "git", return_value="current"), \
             patch.object(runner, "source_hashes", return_value={"Main.lean": "fixed"}), \
             patch.object(runner.time, "time_ns", return_value=self.started_ns), \
             patch.object(runner.subprocess, "run", side_effect=command_result), \
             patch("sys.argv", ["verify.py", "--clean", "--output", str(self.root / "output")]):
            self.assertEqual(runner.main(), 0)
        self.assertIn(["lake", "--no-cache", "-v", "build"], calls)
        actual = json.loads((self.root / "output/verification.json").read_text())
        self.assertTrue(actual["build_directory_absent_after_clean"])
        self.assertEqual(actual["fresh_project_outputs"]["olean_mtime_ns"], {"Main": self.started_ns + 1})


if __name__ == "__main__":
    unittest.main()
