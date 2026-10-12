"""Tests for the Challenge generator's extraction of declarations and statements."""
import unittest

import generate_challenge as gc

SOURCE = '''module

public import Init

/-! A module docstring with a fake `theorem fake : False := by sorry`. -/

@[expose] public section

namespace STACS2027

variable {Ω : Type} [Inhabited Ω]

/-- The walk predicate. -/
def WalkWithin (S : ℕ → Prop) : List ℕ → Prop
  | [] => True
  | a :: rest => S a ∧ WalkWithin S rest -- a trailing comment

/-- A noise. -/
noncomputable def noise (ω : Ω) : Nat := 0

namespace Arr
/-- One `get`. -/
theorem get : True := trivial
end Arr

namespace Tab
/-- Another `get`. -/
theorem get : True := trivial
end Tab

omit [Inhabited Ω] in
/-- A theorem whose statement spans
two lines of documentation. -/
theorem common_neighbours_le_two (k : ℕ) : ∃ B : ℕ,
    k ≤ k + B := by
  exact ⟨0, Nat.le_refl _⟩

theorem undocumented : True := trivial

@[simp] theorem tagged : True := trivial

end STACS2027
'''


class ExtractionTests(unittest.TestCase):
    def test_without_comments_preserves_offsets(self):
        text = 'a /- b /- c -/ d -/ e -- f\n"-- g"'
        blank = gc.without_comments(text)
        self.assertEqual(len(blank), len(text))
        self.assertEqual(blank.split(), ['a', 'e', '"--', 'g"'])

    def test_chunks_stop_at_variable_and_omit(self):
        keys = dict(gc.chunks(SOURCE))
        self.assertEqual(keys['WalkWithin'],
                         '/-- The walk predicate. -/\ndef WalkWithin (S : ℕ → Prop) : List ℕ → Prop\n'
                         '  | [] => True\n  | a :: rest => S a ∧ WalkWithin S rest')
        self.assertTrue(keys['noise'].startswith('/-- A noise. -/\nnoncomputable def noise'))
        self.assertNotIn('omit', keys['noise'])
        self.assertNotIn('variable', ''.join(v for k, v in keys.items() if not k.startswith('#')))

    def test_statement_replaces_proof_by_sorry(self):
        text = gc.statement_text(SOURCE, 'common_neighbours_le_two', 'Source.lean')
        self.assertEqual(text, '/-- A theorem whose statement spans\ntwo lines of documentation. -/\n'
                               'theorem common_neighbours_le_two (k : ℕ) : ∃ B : ℕ,\n    k ≤ k + B := by sorry')

    def test_statement_requires_documented_plain_theorem(self):
        for name in ['undocumented', 'tagged', 'missing']:
            with self.assertRaises(ValueError):
                gc.statement_text(SOURCE, name, 'Source.lean')

    def test_select_adds_fresh_matcher_prefix_and_checks_order(self):
        text = gc.select(SOURCE, ['WalkWithin'], 'Source.lean')
        self.assertTrue(text.startswith(gc.FRESH_MATCHER_PREFIX + '/-- The walk predicate. -/\ndef WalkWithin'))
        with self.assertRaises(ValueError):
            gc.select(SOURCE, ['noise', 'WalkWithin'], 'Source.lean')
        with self.assertRaises(ValueError):
            gc.select(SOURCE, ['nothing'], 'Source.lean')

    def test_select_adds_core_instance_prefix(self):
        old_core = dict(gc.CORE_INSTANCES)
        try:
            gc.CORE_INSTANCES.clear()
            gc.CORE_INSTANCES['noise'] = ['attribute [local instance high] Zero.ofOfNat0 in']
            text = gc.select(SOURCE, ['noise'], 'Source.lean')
        finally:
            gc.CORE_INSTANCES.clear(); gc.CORE_INSTANCES.update(old_core)
        self.assertTrue(text.startswith('attribute [local instance high] Zero.ofOfNat0 in\n/-- A noise. -/'))

    def test_decidable_pred_instances_are_keyed(self):
        keys = dict(gc.chunks('instance (g : Graph) : DecidablePred (ConvexCycle g) := fun _ =>\n'
                              '  inferInstanceAs (Decidable (_ ∧ _))\n'))
        self.assertIn('instance:ConvexCycle', keys)

    def test_repeated_names_are_ambiguous_only_when_selected(self):
        self.assertIn('/-- A noise. -/', gc.select(SOURCE, ['noise'], 'Source.lean'))
        with self.assertRaises(ValueError):
            gc.select(SOURCE, ['get'], 'Source.lean')


@unittest.skipUnless((gc.SECTION5 / 'NPHardness/FiniteCycles.lean').is_file()
                     and (gc.SECTION8 / 'MinorFree/K4.lean').is_file()
                     and (gc.FOUNDATION / 'Complexity/Planarity.lean').is_file(),
                     'the pinned dependencies are not fetched (run `lake build` first)')
class ChallengeTests(unittest.TestCase):
    def test_challenge_shape(self):
        text = gc.challenge_text()
        self.assertTrue(text.startswith('module\n\n' + '\n'.join(
            f'public import {m}' for m in gc.MATHLIB_IMPORTS) + '\n\n/-!'))
        self.assertEqual(text.count('by sorry'), len(gc.TARGETS))
        self.assertLessEqual(len(text.splitlines()), 1000)
        self.assertLessEqual(len(text.encode('utf-8')), 100 * 1024)
        for _, name in gc.TARGETS:
            self.assertIn(f'\ntheorem {name.split(".")[-1]} ', text)
        self.assertEqual(text.count(gc.FRESH_MATCHER_PREFIX), len(gc.FRESH_MATCHER))
        code = gc.without_comments(text)
        self.assertEqual(code.count('attribute [local instance high]'),
                         sum(len(v) for v in gc.CORE_INSTANCES.values()))
        self.assertNotIn('run_cmd', code)
        self.assertNotIn('meta import', code)
        self.assertIn('\nnamespace IsPolygon\n\nvariable {g : Graph} {n : ℕ}\n', text)
        self.assertIn('\n@[expose] public section\n\nnamespace Complexity\n', text)
        self.assertIn('\nend Complexity\n\nnamespace STACS2027\n', text)
        self.assertIn('\ntheorem outerplanar_block_structure (g : Graph) :\n    (OuterplanarDrawing g ↔', text)
        self.assertIn('∀ g : Graph, OuterplanarDrawing g →', text)
        self.assertNotIn('TwoConnectedK23Structure', code)


if __name__ == '__main__':
    unittest.main()
