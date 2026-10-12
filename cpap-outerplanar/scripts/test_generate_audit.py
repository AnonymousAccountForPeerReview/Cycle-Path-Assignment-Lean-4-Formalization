"""Tests for the audit generator's recognition of declarations that Lean generates."""
import unittest

from generate_audit import generated

SCANNED = {
    'A.R0.Glob': 'structure',
    'A.Problem': 'structure',
    'A.run': 'def',
    'A.lemma': 'theorem',
}


class GeneratedTests(unittest.TestCase):
    def test_lean_generated_declarations(self):
        for name, kind in [('A.run.eq_def', 'theorem'), ('A.run.eq_1', 'theorem'),
                           ('A.Problem.mk.injEq', 'theorem'), ('A.Problem.ctorIdx', 'def'),
                           ('A.Problem.mk.sizeOf_spec', 'theorem'), ('A.Stmt.brecOn.go', 'def'),
                           ('A.instDecidableAdj', 'def'), ('A.tacticStab', 'syntax'),
                           ('A.R0.glob_iff', 'theorem'), ('A.own.congr_simp', 'theorem')]:
            self.assertTrue(generated(name, kind, SCANNED), name)

    def test_written_declarations_are_not_generated(self):
        for name, kind in [('A.lemma2', 'theorem'), ('A.R0.other_iff', 'theorem'),
                           ('A.run_iff', 'theorem'), ('A.instance_count', 'theorem')]:
            self.assertFalse(generated(name, kind, SCANNED), name)


if __name__ == '__main__':
    unittest.main()
