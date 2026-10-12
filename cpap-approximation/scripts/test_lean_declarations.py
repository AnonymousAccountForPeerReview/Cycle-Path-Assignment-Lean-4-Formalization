"""Tests for the declaration scanner used by the axiom-guard generator."""
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from lean_declarations import declarations


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


if __name__ == '__main__':
    unittest.main()
