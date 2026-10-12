"""Tests for the module discovery and declaration scanner used by the axiom-guard generator."""
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from lean_declarations import declarations, library_declarations, library_modules, plain, stray_modules


class DeclarationScopeTests(unittest.TestCase):
    def scan(self, text):
        with TemporaryDirectory() as directory:
            path = Path(directory) / 'Scope.lean'
            path.write_text(text)
            return declarations(path)

    def test_nested_namespaces_and_sections(self):
        ds = self.scan('''module
@[expose] public section
namespace STACS2027
/- theorem fake : False := by sorry -/
section auxiliary
namespace Oriented
@[simp] theorem graph_iff : True := by trivial
noncomputable def A.value : Nat := 0
end Oriented
end auxiliary
theorem ordinary : True := by trivial
end STACS2027
''')
        self.assertEqual([d.name for d in ds],
                         ['STACS2027.Oriented.graph_iff',
                          'STACS2027.Oriented.A.value', 'STACS2027.ordinary'])
        self.assertEqual([d.kind for d in ds], ['theorem', 'def', 'theorem'])

    def test_fully_qualified_namespace_and_root(self):
        ds = self.scan('''module
namespace STACS2027.WordConstructor
theorem executes : True := by trivial
def _root_.auditMarker : Nat := 0
end STACS2027.WordConstructor
''')
        self.assertEqual([d.name for d in ds],
                         ['STACS2027.WordConstructor.executes', 'auditMarker'])

    def test_private_and_mismatched_scopes_rejected(self):
        for text in ['private theorem hidden : True := by trivial',
                     'namespace X\nend Y', 'namespace X\ndef x := 0']:
            with self.assertRaises(ValueError):
                self.scan(text)

    def test_partial_close_of_dotted_namespace(self):
        ds = self.scan('''module
namespace A.B.C
theorem inner : True := by trivial
end C
theorem outer : True := by trivial
end A.B
''')
        self.assertEqual([d.name for d in ds], ['A.B.C.inner', 'A.B.outer'])

    def test_question_and_exclamation_identifiers(self):
        ds = self.scan('''module
namespace A
theorem getElem?_flatMap_two : True := by trivial
def value! : Nat := 0
theorem flatten_piece_getElem? : True := by trivial
end A
''')
        self.assertEqual([d.name for d in ds],
                         ['A.getElem?_flatMap_two', 'A.value!', 'A.flatten_piece_getElem?'])

    def test_guillemets_named_instances_and_classes(self):
        ds = self.scan('''module
namespace A.Indep
theorem «forall» : True := by trivial
instance decide : Decidable True := inferInstance
instance (n : Nat) : Inhabited (Fin (n + 1)) := ⟨0⟩
instance : Inhabited Nat := ⟨0⟩
instance (priority := low) lowInst : Inhabited Bool := ⟨true⟩
class inductive Shape where
  | round
class Sized (α : Type) where
  size : α → Nat
end A.Indep
''')
        self.assertEqual([d.name for d in ds],
                         ['A.Indep.«forall»', 'A.Indep.decide', 'A.Indep.lowInst', 'A.Indep.Shape',
                          'A.Indep.Sized'])
        self.assertEqual([d.kind for d in ds],
                         ['theorem', 'instance', 'instance', 'class inductive', 'class'])
        self.assertEqual(plain(ds[0].name), 'A.Indep.forall')

    def test_set_option_prefix(self):
        ds = self.scan('''module
namespace A
set_option maxRecDepth 1000 in theorem hidden : True := trivial
set_option maxHeartbeats 400000 in
@[simp] theorem slow : True := trivial
end A
''')
        self.assertEqual([d.name for d in ds], ['A.hidden', 'A.slow'])


class LibraryModuleTests(unittest.TestCase):
    def test_import_closure_and_strays(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Lib/Sub').mkdir(parents=True)
            (root / 'Lib.lean').write_text('module\n\npublic import Lib.A\n-- import Lib.Commented\n')
            (root / 'Lib/A.lean').write_text(
                'module\n\npublic import Lib.Sub.B\nimport Mathlib.Tactic\nnamespace X\ntheorem a : True := trivial\nend X\n')
            (root / 'Lib/Sub/B.lean').write_text('module\n\nnamespace X\ndef b : Nat := 0\nend X\n')
            (root / 'Lib/WorkInProgress.lean').write_text('module\n\ntheorem w : True := sorry\n')
            self.assertEqual(library_modules(root, 'Lib'), ['Lib.A', 'Lib.Sub.B'])
            self.assertEqual(stray_modules(root, 'Lib'), [root / 'Lib/WorkInProgress.lean'])
            self.assertEqual([d.name for d in library_declarations(root, 'Lib')], ['X.a', 'X.b'])
            (root / 'Lib.lean').write_text('module\n\npublic import Lib.A\npublic import Lib.Missing\n')
            with self.assertRaises(ValueError):
                library_modules(root, 'Lib')


if __name__ == '__main__':
    unittest.main()
