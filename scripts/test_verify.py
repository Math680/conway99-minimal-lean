"""Regression tests for the lightweight verification helper, not for Lean proofs."""
import unittest

from verify import check_axioms, without_comments


class VerificationHelperTests(unittest.TestCase):
    def test_nested_comments(self):
        source = "/- outer /- sorry -/ end -/ theorem ok := by trivial -- admit\n"
        self.assertEqual(without_comments(source).strip(), "theorem ok := by trivial")

    def test_string_is_not_a_comment(self):
        self.assertEqual(without_comments('"https://example.org"'), '"https://example.org"')

    def test_standard_multiline_axioms(self):
        output = "'final' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
        self.assertEqual(check_axioms(output, "final"), 1)

    def test_rejects_admission(self):
        with self.assertRaises(ValueError):
            check_axioms("'final' depends on axioms: [sorryAx]", "final")

    def test_rejects_custom_axiom(self):
        with self.assertRaises(ValueError):
            check_axioms("'final' depends on axioms: [propext, assumed_milgram]", "final")

    def test_requires_final_theorem(self):
        with self.assertRaises(ValueError):
            check_axioms("'helper' depends on axioms: [propext]", "final")


if __name__ == "__main__":
    unittest.main()
