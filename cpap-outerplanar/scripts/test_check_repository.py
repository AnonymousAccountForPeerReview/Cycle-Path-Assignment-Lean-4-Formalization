"""Tests for the source rules of the repository check."""
import unittest

from check_repository import FORBIDDEN, statement_problems
from generate_challenge import without_comments


class ForbiddenTests(unittest.TestCase):
    def test_forbidden_constructs(self):
        for code in ['theorem t : 1 = 1 := by native_decide', 'axiom bad : False',
                     'private axiom bad : False', '@[implemented_by f] def g := 0',
                     '@[extern "c_fn"] opaque h : Nat', 'unsafe def u : Nat := 0',
                     'set_option maxHeartbeats 0 in', 'set_option debug.skipKernelTC true',
                     'theorem t : True := by admit']:
            self.assertIsNotNone(FORBIDDEN.search(code), code)

    def test_allowed_constructs(self):
        for code in ['theorem t : 1 = 1 := by decide +kernel', 'set_option maxHeartbeats 400000 in',
                     'theorem axiom_free : True := trivial', 'def externalNodes : Nat := 0',
                     '/-- `native_decide` is not used. -/ theorem t : True := trivial']:
            self.assertIsNone(FORBIDDEN.search(without_comments(code)), code)


class StatementTests(unittest.TestCase):
    OK = {
        'outerplanar_block_structure': '/-- Not `TwoConnectedK23Structure → …`. -/\ntheorem outerplanar_block_structure (g : Graph) :\n'
                   '    (OuterplanarDrawing g ↔ (¬ HasMinor g 4 k4 ∧ ¬ HasMinor g 5 k23)) := by sorry',
        'k23_perfect': '/-- Without `TwoConnectedK23Structure`. -/\ntheorem k23_perfect {g : Graph}\n'
                     '    (hg : K23MinorFree g) : HasAssignment g 4 0 := by sorry',
        'outerplanar_linear_ram': 'theorem outerplanar_linear_ram : ∀ g : Graph, OuterplanarDrawing g → True := by sorry',
    }

    def test_accepted(self):
        self.assertEqual(statement_problems(self.OK), [])

    def test_hypotheses_rejected(self):
        for hypothesis in ['TwoConnectedK23Structure', 'HypermapEuler']:
            bad = dict(self.OK, k23_perfect=f'theorem k23_perfect (hL : {hypothesis}) {{g : Graph}} : True := by sorry')
            self.assertEqual(len(statement_problems(bad)), 1, hypothesis)

    def test_outerplanar_block_structure_required(self):
        self.assertEqual(len(statement_problems({'k23_perfect': self.OK['k23_perfect']})), 1)

    def test_outerplanar_drawing_required(self):
        bad = dict(self.OK, outerplanar_linear_ram='theorem outerplanar_linear_ram : ∀ g : Graph, Outerplanar g → True := by sorry')
        self.assertEqual(len(statement_problems(bad)), 1)


if __name__ == '__main__':
    unittest.main()
