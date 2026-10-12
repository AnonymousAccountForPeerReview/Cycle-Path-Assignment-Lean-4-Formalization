module

public import NPHardness.FiniteCycles

/-!
Explicit graph constructors for the gadgets of Appendix C, Steps 1-3, drawn in
Figure 4 of the manuscript. In both clause gadgets, Lean vertex `v` is
Appendix C vertex `v + 1`, and the links appear in printed order
(`NPHardness.Paper` proves the transcription). Subdivision counts, including the
special case k = 6, are those of Step 3 and the Figure 4 caption.
-/

@[expose] public section
namespace STACS2027

structure Link where
  source : Nat
  target : Nat
  subdivisions : Nat := 0
deriving DecidableEq, Repr

/-- Fresh vertices are `next, ..., next + subdivisions - 1`. -/
def subdividedEdge (a b next : Nat) : Nat → Graph
  | 0 => [edge a b]
  | s + 1 => edge a next :: subdividedEdge next b (next + 1) s

def realizeLinks (next : Nat) : List Link → Graph
  | [] => []
  | l :: ls => subdividedEdge l.source l.target next l.subdivisions ++
      realizeLinks (next + l.subdivisions) ls

theorem subdividedEdge_length (a b next s : Nat) :
    (subdividedEdge a b next s).length = s + 1 := by
  induction s generalizing a next with
  | zero => rfl
  | succ s ih => simp [subdividedEdge, ih, Nat.add_assoc]

theorem realizeLinks_length (next : Nat) (ls : List Link) :
    (realizeLinks next ls).length = ls.length + (ls.map Link.subdivisions).sum := by
  induction ls generalizing next with
  | nil => rfl
  | cons l ls ih => simp [realizeLinks, subdividedEdge_length, ih]; omega

/-- Step 1 and Figure 4(a). Vertices 0-6 are the corners of the figure:
0 top left, 1 top middle, 2 top right, 3 middle left, 4 middle,
5 bottom middle, 6 bottom right. The first four links are the dashed gray
paths of lengths ⌊(k-1)/2⌋, ⌊(k-3)/2⌋, ⌊(k-2)/2⌋, ⌊(k-2)/2⌋. -/
def variableLinks (k : Nat) : List Link :=
  [⟨0, 1, (k - 1) / 2 - 1⟩, ⟨1, 2, (k - 3) / 2 - 1⟩,
   ⟨3, 4, (k - 2) / 2 - 1⟩, ⟨5, 6, (k - 2) / 2 - 1⟩,
   ⟨0, 3, 0⟩, ⟨1, 4, 0⟩, ⟨4, 5, 0⟩, ⟨2, 6, 0⟩]

def variableGraph (k : Nat) : Graph := realizeLinks 7 (variableLinks k)

/-- `e_(x,True,1)`, `e_(x,False,1)`, `e_(x,False,2)` (Step 1). Step 4 allocates
negative occurrences to the two red edges in this order. -/
def variablePorts : List Edge := [(2, 6), (4, 5), (0, 3)]

/-- Step 2 and Figure 4(b): Appendix C's edge list in printed order, vertices
shifted by one, with the dashed green edges subdivided k-5 times. -/
def clauseThreeLinks (k : Nat) : List Link :=
  [⟨0, 1, 0⟩, ⟨0, 12, k-5⟩, ⟨0, 13, 0⟩, ⟨1, 2, k-5⟩,
   ⟨2, 3, k-5⟩, ⟨2, 14, 0⟩, ⟨3, 4, 0⟩, ⟨3, 10, 0⟩,
   ⟨4, 5, 0⟩, ⟨4, 15, 0⟩, ⟨5, 6, k-5⟩, ⟨6, 7, 0⟩,
   ⟨6, 16, 0⟩, ⟨7, 8, k-5⟩, ⟨8, 9, k-5⟩, ⟨8, 17, 0⟩,
   ⟨9, 10, k-5⟩, ⟨9, 15, 0⟩, ⟨10, 11, 0⟩, ⟨11, 12, 0⟩,
   ⟨11, 14, 0⟩, ⟨13, 14, 0⟩, ⟨15, 16, 0⟩, ⟨16, 17, 0⟩]

def clauseThreeGraph (k : Nat) : Graph := realizeLinks 18 (clauseThreeLinks k)

/-- `e_(c,1)`, `e_(c,2)`, `e_(c,3)`: Appendix C edges (1,2), (5,6), (11,12). -/
def clausePorts : List Edge := [(0, 1), (4, 5), (10, 11)]

def orangeSubdivisions (k : Nat) : Nat := if k = 6 then 0 else (k - 5) / 2
def blueSubdivisions (k : Nat) : Nat := if k = 6 then 0 else (k - 4) / 2
def redSubdivisions (k : Nat) : Nat := if k = 6 then 1 else 0

/-- Step 3 and Figure 4(c): the 3-literal links followed by Step 3's ten
edges in printed order (Appendix C vertices 19-24 are Lean 18-23). The edge
`e_(c,3)` = (10,11) remains an ordinary edge. -/
def clauseTwoLinks (k : Nat) : List Link :=
  clauseThreeLinks k ++
  [⟨10, 18, 0⟩, ⟨11, 20, 0⟩, ⟨18, 19, k-5⟩,
   ⟨19, 20, 0⟩, ⟨19, 22, 0⟩,
   ⟨20, 21, orangeSubdivisions k⟩, ⟨20, 23, orangeSubdivisions k⟩,
   ⟨21, 22, blueSubdivisions k⟩, ⟨21, 23, redSubdivisions k⟩,
   ⟨22, 23, blueSubdivisions k⟩]

def clauseTwoGraph (k : Nat) : Graph := realizeLinks 24 (clauseTwoLinks k)

theorem variableGraph_edge_count (k : Nat) (hk : 5 ≤ k) :
    (variableGraph k).length = 2 * k - 1 := by
  rw [variableGraph, realizeLinks_length]
  simp only [variableLinks, List.length_cons, List.length_nil, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem clauseThreeGraph_edge_count (k : Nat) (hk : 5 ≤ k) :
    (clauseThreeGraph k).length = 7 * k - 11 := by
  rw [clauseThreeGraph, realizeLinks_length]
  simp only [clauseThreeLinks, List.length_cons, List.length_nil, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem clauseTwoGraph_edge_count (k : Nat) (hk : 5 ≤ k) :
    (clauseTwoGraph k).length = if k = 6 then 43 else 10 * k - 16 := by
  rw [clauseTwoGraph, realizeLinks_length]
  simp only [clauseTwoLinks, clauseThreeLinks, List.length_append, List.length_cons,
    List.length_nil, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  by_cases h : k = 6
  · subst k; decide
  · simp only [orangeSubdivisions, blueSubdivisions, redSubdivisions, h, ↓reduceIte]
    omega

end STACS2027
