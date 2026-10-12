module

public import Tractability.FlowTools

/-!
# The min-cost flow network for triangles (Corollary `K3TimeComplexity`)

"Modify the network of Theorem 2 by replacing the opposing-pair nodes with one node
`x_C` for each triangle `C`. Add a unit-capacity, zero-cost arc from the source to
`x_C` and from `x_C` to each of the three edge nodes `y_e` with `e ∈ E(C)`. Keep the
same bundles of unit-capacity arcs from each `y_e` to the sink, with costs
`0, …, ϖ(e) − 1`. An integral flow of value `t` selects one edge per triangle and has
minimum cost exactly when the corresponding assignment is optimal."

The triangles are those enumerated by `cycles g 3`, each counted once by its edge
set, as in `HasAssignment`; a triangle's path of `k − 2 = 1` edge is one of its edges.
-/

@[expose] public section
namespace STACS2027

/-- `C_i`, the `i`-th enumerated triangle of `g` (the empty list if there is none). -/
def triangleAt (g : Graph) (i : Nat) : Cycle := (cycles g 3).getD i []

/-- The edges lying on a triangle of `g`, each once, in order of first appearance. -/
def triangleEdgeList (g : Graph) : List Edge :=
  ((cycles g 3).flatMap cycleEdges).eraseDups

/-- `ϖ(e)`: the number of triangles of `g` containing `e`. -/
def triangleCount (g : Graph) (e : Edge) : Nat :=
  (cycles g 3).countP fun c => (cycleEdges c).contains e

/-- The arcs `s → x_{C_i}`, of cost `0`. -/
def triangleSourceArcs (g : Graph) : List Arc :=
  (List.range (cycles g 3).length).map fun i => ⟨.source, .triangle i, 0⟩

/-- The arcs `x_{C_i} → y_e` for the three edges `e` of `C_i`, of cost `0`. -/
def triangleEdgeArcs (g : Graph) : List Arc :=
  (List.range (cycles g 3).length).flatMap fun i =>
    (cycleEdges (triangleAt g i)).map fun e => ⟨.triangle i, .edgeNode e, 0⟩

/-- The `ϖ(e)` parallel arcs `y_e → z`, with costs `0, …, ϖ(e) - 1`. -/
def triangleSinkArcs (g : Graph) : List Arc :=
  (triangleEdgeList g).flatMap fun e =>
    (List.range (triangleCount g e)).map fun j => ⟨.edgeNode e, .sink, j⟩

/-- The triangle network: all arcs, in the order source arcs, triangle arcs, sink arcs. -/
def triangleNetwork (g : Graph) : List Arc :=
  triangleSourceArcs g ++ triangleEdgeArcs g ++ triangleSinkArcs g

/-- The nodes of the triangle network: `s`, `z`, the triangle nodes, and the edge nodes. -/
def triangleNodes (g : Graph) : List FlowNode :=
  .source :: .sink :: ((List.range (cycles g 3).length).map .triangle) ++
    (triangleEdgeList g).map .edgeNode

/-! ## Triangles -/

/-- The vertices of a simple triangle. -/
theorem triangle_shape {g : Graph} {c : Cycle} (hc : IsCycle g 3 c) :
    ∃ a b u, c = [a, b, u] ∧ a ≠ b ∧ a ≠ u ∧ b ≠ u := by
  obtain ⟨_, hlen, hnodup, _⟩ := hc
  match c, hlen with
  | [a, b, u], _ =>
    refine ⟨a, b, u, rfl, ?_⟩
    simp only [List.nodup_cons, List.mem_cons, not_or, not_false_eq_true, List.nodup_nil,
      and_true, List.mem_nil_iff] at hnodup
    omega

theorem cycleEdges_three (a b u : Nat) :
    cycleEdges [a, b, u] = [edge a b, edge b u, edge u a] := by
  simp [cycleEdges, pathEdges]

theorem triangle_edges_distinct {a b u : Nat} (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u) :
    edge a b ≠ edge b u ∧ edge a b ≠ edge u a ∧ edge b u ≠ edge u a := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rcases (edge_eq_iff _ _ _ _).mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    omega

theorem cycleEdges_three_nodup {a b u : Nat} (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u) :
    (cycleEdges [a, b, u]).Nodup := by
  obtain ⟨d1, d2, d3⟩ := triangle_edges_distinct hab hau hbu
  rw [cycleEdges_three]
  simp [d1, d2, d3]

theorem selectedOptions_three (a b u : Nat) :
    selectedOptions [a, b, u] = [[edge b u], [edge u a], [edge a b]] := by
  simp [selectedOptions, List.range_succ, selected, pathEdges]

/-- The paths of a triangle are its three edges, as singleton lists. -/
theorem mem_selectedOptions_three (a b u : Nat) (q : List Edge) :
    q ∈ selectedOptions [a, b, u] ↔ ∃ e ∈ cycleEdges [a, b, u], q = [e] := by
  rw [selectedOptions_three, cycleEdges_three]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨edge b u, by simp, rfl⟩
    · exact ⟨edge u a, by simp, rfl⟩
    · exact ⟨edge a b, by simp, rfl⟩
  · rintro ⟨e, he, rfl⟩
    rcases he with rfl | rfl | rfl <;> simp

theorem triangleAt_isCycle (g : Graph) {i : Nat} (hi : i < (cycles g 3).length) :
    IsCycle g 3 (triangleAt g i) := by
  apply enumerated_isCycle
  rw [triangleAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem triangleAt_mem (g : Graph) {i : Nat} (hi : i < (cycles g 3).length) :
    triangleAt g i ∈ cycles g 3 := by
  rw [triangleAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem triangleAt_edges_nodup (g : Graph) {i : Nat} (hi : i < (cycles g 3).length) :
    (cycleEdges (triangleAt g i)).Nodup := by
  obtain ⟨a, b, u, hc, hab, hau, hbu⟩ := triangle_shape (triangleAt_isCycle g hi)
  rw [hc]
  exact cycleEdges_three_nodup hab hau hbu

theorem triangleAt_edges_length (g : Graph) {i : Nat} (hi : i < (cycles g 3).length) :
    (cycleEdges (triangleAt g i)).length = 3 := by
  obtain ⟨a, b, u, hc, _⟩ := triangle_shape (triangleAt_isCycle g hi)
  rw [hc, cycleEdges_three]; rfl

theorem triangleEdgeList_nodup (g : Graph) : (triangleEdgeList g).Nodup := nodup_eraseDups _

theorem mem_triangleEdgeList (g : Graph) (e : Edge) :
    e ∈ triangleEdgeList g ↔ ∃ c ∈ cycles g 3, e ∈ cycleEdges c := by
  simp [triangleEdgeList, List.mem_eraseDups, List.mem_flatMap]

theorem triangleCount_eq_countP (g : Graph) (e : Edge) :
    triangleCount g e = (cycles g 3).countP fun c => decide (e ∈ cycleEdges c) := by
  rw [triangleCount]
  apply List.countP_congr
  intro c _
  simp

theorem triangleCount_eq_sum (g : Graph) (e : Edge) :
    triangleCount g e = ((List.range (cycles g 3).length).map fun i =>
      if e ∈ cycleEdges (triangleAt g i) then 1 else 0).sum := by
  rw [triangleCount_eq_countP, countP_eq_sum_range _ []]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [triangleAt]

end STACS2027
