module

public import MinorFree.FourCycles

/-!
The complete graph `K₄`: its three four-cycles have three edge-disjoint paths
of two edges (the assignment of Theorem 20's proof), and it has no `k`-cycle
for `k ≥ 5`. Both transfer to every copy of `K₄` on other vertices.
-/

@[expose] public section
namespace STACS2027

/-- `K₄` on the vertices `0, 1, 2, 3`. -/
def k4 : Graph := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The assignment of Theorem 20's proof: `(0,1,2,3) ↦ {01, 12}`, `(0,1,3,2) ↦ {13, 23}`,
`(0,2,1,3) ↦ {02, 03}`, on the enumerated cycles of `k4` (in their enumerated order and
orientation). -/
def k4Assignment : List (List Edge) := [[(0, 1), (1, 2)], [(1, 3), (2, 3)], [(0, 3), (0, 2)]]

theorem k4Assignment_valid : ValidChoices ((cycles k4 4).map selectedOptions) k4Assignment := by
  decide

theorem k4Assignment_cost : cost k4Assignment = 0 := by decide

/-- `K₄` has a perfect cycle-path assignment for `k = 4`: "these paths use every edge exactly
once". -/
theorem k4_perfect : HasAssignment k4 4 0 :=
  ⟨k4Assignment, k4Assignment_valid, Nat.le_of_eq k4Assignment_cost⟩

theorem k4_verticesBelow : VerticesBelow k4 4 := by
  show ∀ e ∈ k4, e.1 < 4 ∧ e.2 < 4
  decide

theorem k4_normalized : ∀ e ∈ k4, edge e.1 e.2 = e := by decide

/-- A simple `k`-cycle of a graph on `n` vertices has `k ≤ n`. -/
theorem IsCycle.length_le_vertices {g : Graph} {k n : Nat} {c : Cycle} (hc : IsCycle g k c)
    (hb : VerticesBelow g n) : k ≤ n := by
  have hsub : c ⊆ List.range n := fun v hv => List.mem_range.mpr (hc.vertex_bound hb v hv)
  have := List.Nodup.length_le_of_subset hc.2.2.1 hsub
  rw [hc.2.1, List.length_range] at this
  exact this

/-- `K₄` contains no `k`-cycles when `k ≥ 5`. -/
theorem k4_cycles_nil {k : Nat} (hk : 5 ≤ k) : cycles k4 k = [] := by
  cases h : cycles k4 k with
  | nil => rfl
  | cons c cs =>
    have hc : c ∈ cycles k4 k := h ▸ List.mem_cons_self
    have := (enumerated_isCycle hc).length_le_vertices k4_verticesBelow
    omega

/-- For `k ≥ 5`, `K₄` has a (vacuous) perfect assignment. -/
theorem k4_perfect_large {k : Nat} (hk : 5 ≤ k) : HasAssignment k4 k 0 :=
  ⟨[], by rw [k4_cycles_nil hk]; trivial, Nat.le_refl _⟩

/-- `K₄` has a perfect four-cycle assignment and no `k`-cycle for `k ≥ 5`. -/
theorem k4_cycle_assignments : HasAssignment k4 4 0 ∧ ∀ k, 5 ≤ k → cycles k4 k = [] :=
  ⟨k4_perfect, fun _ hk => k4_cycles_nil hk⟩

/-- `h` is a copy of `K₄`: its edges are those of `k4` under an injective renaming of
`0, 1, 2, 3`. -/
def IsK4 (h : Graph) : Prop :=
  ∃ t : Nat → Nat, (∀ a, a < 4 → ∀ b, b < 4 → t a = t b → a = b) ∧ ∀ e, e ∈ h ↔ e ∈ mapGraph t k4

/-- Every copy of `K₄` has a perfect cycle-path assignment for `k = 4`. -/
theorem IsK4.perfect {h : Graph} (hh : IsK4 h) : HasAssignment h 4 0 := by
  obtain ⟨t, ht, he⟩ := hh
  rw [hasAssignment_graph_equiv he, hasAssignment_relabel k4_verticesBelow k4_normalized t ht]
  exact k4_perfect

/-- Every copy of `K₄` has a (vacuous) perfect cycle-path assignment for `k ≥ 5`. -/
theorem IsK4.perfect_large {h : Graph} (hh : IsK4 h) {k : Nat} (hk : 5 ≤ k) :
    HasAssignment h k 0 := by
  obtain ⟨t, ht, he⟩ := hh
  rw [hasAssignment_graph_equiv he, hasAssignment_relabel k4_verticesBelow k4_normalized t ht]
  exact k4_perfect_large hk

end STACS2027
