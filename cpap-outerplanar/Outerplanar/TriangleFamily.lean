module

public import Outerplanar.TriangleMatching

/-! Finite unordered vertex triples and their edge unions. -/

@[expose] public section
namespace STACS2027.TriangleMatching

/-- The edges of a finite vertex set, without loops. -/
def vertexSides (T : Finset Nat) : Finset Edge :=
  T.biUnion fun u => (T.erase u).image (edge u)

/-- A finite triangle family, represented without vertex-order choices. -/
def VertexTriangleFamily (S : Finset (Finset Nat)) : Prop :=
  ∀ T∈S,T.card=3

/-- All edges used by a finite triangle family. -/
def vertexSideUnion (S : Finset (Finset Nat)) : Finset Edge := S.biUnion vertexSides

/-- Its simple canonical graph. -/
noncomputable def vertexFamilyGraph (S : Finset (Finset Nat)) : Graph := (vertexSideUnion S).toList

/-- Vertices present in a finite edge set. -/
def edgeVertices (E : Finset Edge) : Finset Nat := E.biUnion fun e => {e.1,e.2}

/-- Common neighbors of two distinct vertices in a finite canonical edge set. -/
def commonVertices (E : Finset Edge) (u v : Nat) : Finset Nat :=
  (edgeVertices E).filter fun w => w≠u ∧ w≠v ∧ edge u w∈E ∧ edge v w∈E

/-- Identify vertex v with u. -/
def identifyVertex (u v w : Nat) : Nat := if w=v then u else w

/-- Image of a vertex triple under a contraction. -/
def identifyTriangle (u v : Nat) (T : Finset Nat) : Finset Nat :=
  T.image (identifyVertex u v)

/-- Discard collapsed triangles and retain every other image. -/
def identifyFamily (u v : Nat) (S : Finset (Finset Nat)) : Finset (Finset Nat) :=
  (S.filter fun T => ¬ (u∈T ∧ v∈T)).image (identifyTriangle u v)

/-- The canonical edges remaining after identifying the two ends of one edge. -/
def identifyEdges (u v : Nat) (E : Finset Edge) : Finset Edge :=
  (E.erase (edge u v)).image fun e => edge (identifyVertex u v e.1) (identifyVertex u v e.2)

end STACS2027.TriangleMatching
