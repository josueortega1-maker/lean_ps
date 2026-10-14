"""Regression checks for fail-closed source and axiom verification."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import check_axioms
import verify_sources


class SourceVerificationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        (self.root / "lakefile.toml").write_text(
            'defaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\nroots = ["Main"]\n'
        )
        self.track("Main.lean", "theorem good : True := True.intro\n")
        self.track("AxiomAudit.lean", "#print axioms good\n")

    def track(self, name, text):
        (self.root / name).write_text(text)
        subprocess.run(["git", "add", "--", name], cwd=self.root, check=True)

    def test_complete_clean_project_passes(self):
        self.assertEqual(verify_sources.verify(self.root), [])

    def test_new_tracked_module_must_be_built(self):
        self.track("Forgotten.lean", "theorem forgotten : True := True.intro\n")
        self.assertTrue(any("absent from" in e for e in verify_sources.verify(self.root)))

    def test_new_untracked_module_is_not_silently_ignored(self):
        (self.root / "Untracked.lean").write_text("theorem unchecked : False := sorry\n")
        self.assertTrue(any("untracked Lean source" in e for e in verify_sources.verify(self.root)))

    def test_missing_tracked_root_fails(self):
        (self.root / "lakefile.toml").write_text(
            '[[lean_lib]]\nname = "Main"\nroots = ["Main", "Missing"]\n'
        )
        self.assertTrue(any("Missing.lean" in e for e in verify_sources.verify(self.root)))

    def test_library_omitted_from_default_build_is_rejected(self):
        self.track("Empty.lean", "def empty : Nat := 0\n")
        (self.root / "lakefile.toml").write_text(
            'defaultTargets = ["Empty"]\n'
            '[[lean_lib]]\nname = "Main"\nroots = ["Main"]\n'
            '[[lean_lib]]\nname = "Empty"\nroots = ["Empty"]\n'
        )
        self.assertTrue(any("Main: library is absent from defaultTargets" in e
                            for e in verify_sources.verify(self.root)))

    def test_library_globs_cannot_omit_a_declared_root(self):
        self.track("Unbuilt.lean", "theorem broken : False := nonexistent_proof\n")
        with (self.root / "lakefile.toml").open("a") as config:
            config.write('globs = ["Main"]\n')
        config = self.root / "lakefile.toml"
        config.write_text(config.read_text().replace('roots = ["Main"]', 'roots = ["Main", "Unbuilt"]'))
        self.assertTrue(any("non-default globs" in e for e in verify_sources.verify(self.root)))

    def test_library_facets_cannot_skip_proof_checking(self):
        with (self.root / "lakefile.toml").open("a") as config:
            config.write('defaultFacets = []\n')
        self.assertTrue(any("non-default defaultFacets" in e for e in verify_sources.verify(self.root)))

    def test_optional_all_declarations_audit_imports_every_root(self):
        self.track("AllDeclarationsAudit.lean", "import Main\n")
        self.assertEqual(verify_sources.verify(self.root), [])

    def test_all_declarations_audit_cannot_silently_omit_a_root(self):
        self.track("AllDeclarationsAudit.lean", "/- import Main -/\n")
        self.assertTrue(any("proof root Main" in e for e in verify_sources.verify(self.root)))

    def test_nested_comments_strings_and_identifier_substrings_are_ignored(self):
        self.track("Main.lean", '''/- sorry /- unsafe -/ axiom -/
-- admit
def explanation := "sorry \\" unsafe"
def raw := r##"axiom " sorry"##
def sorryLookingName := 1
theorem good : True := True.intro
'''.replace('\\\\"', '\\"'))
        self.assertEqual(verify_sources.verify(self.root), [])

    def test_direct_sorry_axiom_reference_is_rejected(self):
        self.track("Main.lean", "theorem bad : False := sorryAx False true\n")
        self.assertTrue(any("sorryAx" in e for e in verify_sources.verify(self.root)))

    def test_zero_hash_raw_string_backslash_does_not_hide_next_declaration(self):
        self.track("Main.lean", 'def raw := r"\\"\ntheorem bad : False := sorry\n')
        self.assertTrue(any("sorry" in e for e in verify_sources.verify(self.root)))

    def test_quote_characters_do_not_hide_intervening_proof(self):
        self.track("Main.lean", '''def c : Char := '"'
theorem hidden : False := sorry
def d : Char := '"'
''')
        self.assertTrue(any("sorry" in e for e in verify_sources.verify(self.root)))

    def test_escaped_identifier_quotes_do_not_hide_intervening_proof(self):
        self.track("Main.lean", '''def «quoted"name» := 1
theorem hidden : False := sorry
def «another"name» := 2
''')
        self.assertTrue(any("sorry" in e for e in verify_sources.verify(self.root)))

    def test_character_literals_and_identifier_primes_scan_cleanly(self):
        self.track("Main.lean", r'''def quoteChar : Char := '\"'
def slash : Char := '\\'
def code : Char := '\u1234'
def x' := 1
def x'a' := 2
''')
        self.assertEqual(verify_sources.verify(self.root), [])

    def test_multiline_partial_definition_is_rejected(self):
        self.track("Main.lean", "partial /- comment -/\ndef loop : Nat := loop\n")
        self.assertTrue(any("partial" in e for e in verify_sources.verify(self.root)))

    def test_unterminated_comment_fails_instead_of_hiding_code(self):
        self.track("Main.lean", "/- unfinished\ntheorem bad : False := sorry\n")
        self.assertTrue(any("unterminated" in e for e in verify_sources.verify(self.root)))

    def test_git_error_is_not_a_clean_scan(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(subprocess.CalledProcessError):
                verify_sources.verify(Path(directory))


class AxiomVerificationTests(unittest.TestCase):
    source = "#print axioms Demo.first\n#print axioms Demo.second\n"
    output = (
        "'Demo.first' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
        "'Demo.second' does not depend on any axioms\n"
    )

    def test_allowed_multiline_and_axiom_free_output_pass(self):
        self.assertEqual(check_axioms.validate(self.source, self.output), ([], 2))

    def test_new_axiom_is_rejected(self):
        errors, _ = check_axioms.validate(self.source, self.output.replace("propext", "sorryAx"))
        self.assertTrue(any("disallowed" in e for e in errors))

    def test_missing_target_is_rejected(self):
        errors, _ = check_axioms.validate(self.source, self.output.split("'Demo.second'")[0])
        self.assertTrue(any("missing" in e for e in errors))

    def test_required_headline_cannot_be_removed_from_source_and_output(self):
        errors, _ = check_axioms.validate(
            self.source, self.output, ["Demo.first", "Demo.requiredHeadline"]
        )
        self.assertTrue(any("required public declaration" in e for e in errors))

    def test_unexpected_and_duplicate_outputs_are_rejected(self):
        errors, _ = check_axioms.validate(self.source, self.output + self.output)
        self.assertTrue(any("duplicate" in e for e in errors))
        errors, _ = check_axioms.validate(self.source, self.output + "'Extra' depends on axioms: []\n")
        self.assertTrue(any("unexpected" in e for e in errors))

    def test_empty_or_malformed_target_contract_fails(self):
        for source in ["", "#print axioms\n", "#print axioms Demo.first\n#print axioms Demo.first\n"]:
            with self.subTest(source=source):
                self.assertTrue(check_axioms.validate(source, self.output)[0])

    def test_diagnostics_fail_even_when_all_footprints_are_present(self):
        errors, _ = check_axioms.validate(self.source, self.output + "AxiomAudit.lean:9:0: error: broken\n")
        self.assertTrue(any("diagnostic" in e for e in errors))

    def test_comments_do_not_add_fake_targets(self):
        source = self.source + "/- #print axioms Fake -/\n"
        self.assertEqual(check_axioms.validate(source, self.output), ([], 2))


if __name__ == "__main__":
    unittest.main()
