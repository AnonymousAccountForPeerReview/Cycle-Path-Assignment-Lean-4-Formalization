module

public import NPHardness.CPAP
public import MinorFree.K4
public import MinorFree.Elimination
public import NPHardness.GlobalReduction

/-!
# Definitions: minors, 2-connectivity, outerplanarity, Lemma 19, optimal outputs

Lean-core definitions on the edge lists of the Section 5 formalization (`Graph`), copied
verbatim into the Challenge.

* `Adj g u v`: the simple graph of an edge list — distinct `u`, `v` joined by an edge
  `edge u v` of `g` (loops, repeated entries and entries not written smaller endpoint
  first are ignored, as by `IsCycle`).
* Walks, connectivity of a vertex set, 2-connectivity (at least three vertices, connected,
  no cut vertex), minors given by branch sets, `K_{2,3}`, `K_{2,3}`-minor-free and
  outerplanar graphs (no `K₄` and no `K_{2,3}` minor, the characterization stated in
  Lemma 19).
* `OuterplanarHam g ham`: `ham` is a Hamiltonian cycle of `g` with respect to whose
  cyclic order no two edges of `g` cross — the outer cycle and the chords of a
  2-connected outerplanar graph with its outerplanar embedding.
* `TwoConnectedK23Structure`: the third sentence of Lemma 19 (cited from ANONYMIZED, ANONYMIZED, ANONYMIZED and
  ANONYMIZED), in combinatorial form, as a proposition (proved as `twoConnectedK23_structure` in
  `Outerplanar/TwoConnectedK23Structure.lean`).
* `IsMinCost g k C`: `C` is the optimum of `CPAP(g, k)` (the definition of the Section 6
  formalization); `OptimalAssignmentOutput`: the output format of an optimal assignment.
-/

@[expose] public section

namespace STACS2027

/-- `u` and `v` are adjacent in the simple graph of `g`: they are distinct and `edge u v`
is an edge of `g`. -/
def Adj (g : Graph) (u v : Nat) : Prop := u ≠ v ∧ edge u v ∈ g

/-- `v` is a vertex of the simple graph of `g`: it is adjacent to some vertex. -/
def IsVertex (g : Graph) (v : Nat) : Prop := ∃ u, Adj g u v

/-- `w` is a walk in `g` all of whose vertices satisfy `S`: consecutive vertices are
adjacent. -/
def WalkWithin (g : Graph) (S : Nat → Prop) : List Nat → Prop
  | [] => True
  | [a] => S a
  | a :: b :: rest => S a ∧ Adj g a b ∧ WalkWithin g S (b :: rest)

/-- Any two vertices satisfying `S` are joined by a walk in `g` within `S`. -/
def ConnectedWithin (g : Graph) (S : Nat → Prop) : Prop :=
  ∀ u v, S u → S v →
    ∃ w : List Nat, w.head? = some u ∧ w.getLast? = some v ∧ WalkWithin g S w

/-- `g` is 2-connected: it has at least three vertices, it is connected, and it stays
connected after the deletion of any one vertex. -/
def TwoConnected (g : Graph) : Prop :=
  (∃ a b c, IsVertex g a ∧ IsVertex g b ∧ IsVertex g c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
  ConnectedWithin g (IsVertex g) ∧
  ∀ x, ConnectedWithin g (fun v => IsVertex g v ∧ v ≠ x)

/-- `g` has the graph `h` on the vertices `0, …, size - 1` as a minor: there are nonempty,
pairwise disjoint branch sets `branch 0, …, branch (size - 1)`, each connected in `g`,
with an edge of `g` between the branch sets of the two ends of every edge of `h`. -/
def HasMinor (g : Graph) (size : Nat) (h : Graph) : Prop :=
  ∃ branch : Nat → List Nat,
    (∀ i, i < size → branch i ≠ []) ∧
    (∀ i j, i < size → j < size → i ≠ j → ∀ v, v ∈ branch i → v ∉ branch j) ∧
    (∀ i, i < size → ConnectedWithin g (fun v => v ∈ branch i)) ∧
    ∀ e ∈ h, ∃ u v, u ∈ branch e.1 ∧ v ∈ branch e.2 ∧ Adj g u v

/-- `K_{2,3}`: the vertices `0` and `1` each joined to `2`, `3` and `4`. -/
def k23 : Graph := [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]

/-- `g` has no `K_{2,3}` minor. -/
def K23MinorFree (g : Graph) : Prop := ¬ HasMinor g 5 k23

/-- `g` is outerplanar: it has neither `K₄` nor `K_{2,3}` as a minor (Lemma 19's
characterization of the graphs with a planar drawing with every vertex on the outer
face). -/
def Outerplanar (g : Graph) : Prop := ¬ HasMinor g 4 k4 ∧ ¬ HasMinor g 5 k23

/-- The simple graph of `g` is a `K₄`: four distinct vertices, any two adjacent, and no
other adjacency. -/
def IsK4Graph (g : Graph) : Prop :=
  ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ∀ u v, Adj g u v ↔ u ≠ v ∧ (u = a ∨ u = b ∨ u = c ∨ u = d) ∧ (v = a ∨ v = b ∨ v = c ∨ v = d)

/-- `ham` is a Hamiltonian cycle of `g` with respect to whose cyclic order no two edges of
`g` cross: the outer cycle of a 2-connected outerplanar graph in an outerplanar embedding,
every other edge being a chord, and chords not crossing. -/
def OuterplanarHam (g : Graph) (ham : List Nat) : Prop :=
  IsCycle g ham.length ham ∧ (∀ v, IsVertex g v → v ∈ ham) ∧
  ∀ i j k l, i < j → j < k → k < l → l < ham.length →
    ¬ (Adj g (ham.getD i 0) (ham.getD k 0) ∧ Adj g (ham.getD j 0) (ham.getD l 0))

/-- **Lemma 19, third sentence**, as cited (ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED 2016), with the
standard structure of 2-connected outerplanar graphs: every 2-connected `K_{2,3}`-minor-free
graph is a `K₄` or has a Hamiltonian cycle with respect to which no two edges cross. The
statement; it is proved as `twoConnectedK23_structure` (`Outerplanar/TwoConnectedK23Structure.lean`). -/
def TwoConnectedK23Structure : Prop :=
  ∀ g : Graph, TwoConnected g → K23MinorFree g → IsK4Graph g ∨ ∃ ham, OuterplanarHam g ham

/-- `C` is the optimum `C*` of `CPAP(g, k)`: the least budget admitting an assignment.
(The same definition as in the Section 6 formalization, `ApproximationHardness/Optimization.lean`.) -/
def IsMinCost (g : Graph) (k C : Nat) : Prop :=
  HasAssignment g k C ∧ ∀ B, HasAssignment g k B → C ≤ B

/-- `out` writes an optimal cycle-path assignment of `CPAP(g, k)`: it is the concatenation
of a list `cs` of `k`-cycles of `g` with pairwise different edge sets, one for each
`k`-cycle of `g` (every `k`-cycle of `g` has the edges of one of them), each written from
the vertex that its path omits, and the cost of the paths `selected c 0` is the optimum. -/
def OptimalAssignmentOutput (g : Graph) (k : Nat) (out : List Nat) : Prop :=
  ∃ cs : List Cycle, out = cs.flatten ∧ (∀ c ∈ cs, IsCycle g k c) ∧
    cs.Pairwise (fun c d => ¬ SameCycle c d) ∧ (∀ c, IsCycle g k c → ∃ d ∈ cs, SameCycle c d) ∧
    IsMinCost g k (cost (cs.map fun c => selected c 0))

end STACS2027
