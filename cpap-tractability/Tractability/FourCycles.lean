module

public import Tractability.FlowNetwork
public import NPHardness.SelectedPaths

/-!
# Four-cycles, their opposing pairs and their four paths

A simple four-cycle `[a, b, u, v]` has the edges `e₁ = ab, e₂ = bu, e₃ = uv, e₄ = va`,
pairwise distinct. Its four paths of two edges (`selected c j`, deleting vertex `c[j]`)
each take exactly one edge from the opposing pair `{e₁, e₃}` and one from `{e₂, e₄}`,
and every such choice is one of the four paths. This is the observation behind the
network of Theorem 2.
-/

@[expose] public section
namespace STACS2027

theorem edge_eq_iff (a b u v : Nat) :
    edge a b = edge u v ↔ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  simp only [edge, Prod.mk.injEq]
  omega

theorem edge_comm (a b : Nat) : edge a b = edge b a := by
  simp only [edge, Prod.mk.injEq]
  omega

/-- The vertices of a simple four-cycle. -/
theorem fourCycle_shape {g : Graph} {c : Cycle} (hc : IsCycle g 4 c) :
    ∃ a b u v, c = [a, b, u, v] ∧ a ≠ b ∧ a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v ∧ u ≠ v := by
  obtain ⟨_, hlen, hnodup, _⟩ := hc
  match c, hlen with
  | [a, b, u, v], _ =>
    refine ⟨a, b, u, v, rfl, ?_⟩
    simp only [List.nodup_cons, List.mem_cons, not_or, not_false_eq_true, List.nodup_nil,
      and_true, List.mem_nil_iff] at hnodup
    omega

theorem cycleEdges_four (a b u v : Nat) :
    cycleEdges [a, b, u, v] = [edge a b, edge b u, edge u v, edge v a] := by
  simp [cycleEdges, pathEdges]

theorem opposingPair_four (a b u v : Nat) :
    opposingPair [a, b, u, v] false = [edge a b, edge u v] ∧
      opposingPair [a, b, u, v] true = [edge b u, edge v a] := by
  simp [opposingPair, cycleEdges, pathEdges]

theorem selected_four (a b u v : Nat) :
    selected [a, b, u, v] 0 = [edge b u, edge u v] ∧
      selected [a, b, u, v] 1 = [edge u v, edge v a] ∧
      selected [a, b, u, v] 2 = [edge v a, edge a b] ∧
      selected [a, b, u, v] 3 = [edge a b, edge b u] := by
  simp [selected, pathEdges]

theorem selectedOptions_four (a b u v : Nat) :
    selectedOptions [a, b, u, v] =
      [selected [a, b, u, v] 0, selected [a, b, u, v] 1,
        selected [a, b, u, v] 2, selected [a, b, u, v] 3] := by
  simp [selectedOptions, List.range_succ]

/-- The four edges of a simple four-cycle are pairwise distinct. -/
theorem fourCycle_edges_distinct {a b u v : Nat} (_hab : a ≠ b) (hau : a ≠ u) (hav : a ≠ v)
    (hbu : b ≠ u) (hbv : b ≠ v) (huv : u ≠ v) :
    edge a b ≠ edge b u ∧ edge a b ≠ edge u v ∧ edge a b ≠ edge v a ∧
      edge b u ≠ edge u v ∧ edge b u ≠ edge v a ∧ edge u v ≠ edge v a := by
  simp only [ne_eq, edge_eq_iff]
  omega

/-- The edge of the opposing pair `p` of the four-cycle `c` used by the path `selected c j`:
for `p = false`, `e₃` when `j ∈ {0, 1}` and `e₁` otherwise; for `p = true`, `e₄` when
`j ∈ {1, 2}` and `e₂` otherwise. -/
def chosenEdge (c : Cycle) (j : Nat) (p : Bool) : Edge :=
  if p then (if j = 1 ∨ j = 2 then (cycleEdges c)[3]! else (cycleEdges c)[1]!)
  else (if j < 2 then (cycleEdges c)[2]! else (cycleEdges c)[0]!)

/-- The path index whose chosen edges are `e₃` (if `q₀`) or `e₁` from the first pair and `e₄`
(if `q₁`) or `e₂` from the second. -/
def optionIndex (q₀ q₁ : Bool) : Nat :=
  if q₀ then (if q₁ then 1 else 0) else (if q₁ then 2 else 3)

theorem optionIndex_lt (q₀ q₁ : Bool) : optionIndex q₀ q₁ < 4 := by
  cases q₀ <;> cases q₁ <;> simp [optionIndex]

theorem chosenEdge_four (a b u v : Nat) (j : Nat) :
    chosenEdge [a, b, u, v] j false = (if j < 2 then edge u v else edge a b) ∧
      chosenEdge [a, b, u, v] j true = (if j = 1 ∨ j = 2 then edge v a else edge b u) := by
  simp [chosenEdge, cycleEdges_four]

theorem chosenEdge_optionIndex (a b u v : Nat) (q₀ q₁ : Bool) :
    chosenEdge [a, b, u, v] (optionIndex q₀ q₁) false = (if q₀ then edge u v else edge a b) ∧
      chosenEdge [a, b, u, v] (optionIndex q₀ q₁) true = (if q₁ then edge v a else edge b u) := by
  cases q₀ <;> cases q₁ <;> simp [chosenEdge_four, optionIndex]

/-- Each path of the cycle contains exactly the two chosen edges. -/
theorem mem_selected_four_iff (a b u v : Nat) {j : Nat} (hj : j < 4) (e : Edge) :
    e ∈ selected [a, b, u, v] j ↔
      e = chosenEdge [a, b, u, v] j false ∨ e = chosenEdge [a, b, u, v] j true := by
  obtain ⟨h0, h1, h2, h3⟩ := selected_four a b u v
  obtain ⟨hf, ht⟩ := chosenEdge_four a b u v j
  match j, hj with
  | 0, _ => simp [h0, hf, ht, or_comm]
  | 1, _ => simp [h1, hf, ht]
  | 2, _ => simp [h2, hf, ht, or_comm]
  | 3, _ => simp [h3, hf, ht]

theorem chosenEdge_mem_pair (a b u v : Nat) (j : Nat) (p : Bool) :
    chosenEdge [a, b, u, v] j p ∈ opposingPair [a, b, u, v] p := by
  obtain ⟨hf, ht⟩ := chosenEdge_four a b u v j
  obtain ⟨pf, pt⟩ := opposingPair_four a b u v
  cases p
  · rw [hf, pf]; split <;> simp
  · rw [ht, pt]; split <;> simp

theorem chosenEdge_mem_selected (a b u v : Nat) {j : Nat} (hj : j < 4) (p : Bool) :
    chosenEdge [a, b, u, v] j p ∈ selected [a, b, u, v] j := by
  rw [mem_selected_four_iff a b u v hj]
  cases p <;> simp

/-- The chosen edge of a pair is the only edge of that pair on the path. -/
theorem pair_mem_selected_unique {a b u v : Nat} (hab : a ≠ b) (hau : a ≠ u) (hav : a ≠ v)
    (hbu : b ≠ u) (hbv : b ≠ v) (huv : u ≠ v) {j : Nat} (hj : j < 4) (p : Bool) {e : Edge}
    (hp : e ∈ opposingPair [a, b, u, v] p) (hs : e ∈ selected [a, b, u, v] j) :
    e = chosenEdge [a, b, u, v] j p := by
  obtain ⟨d12, d13, d14, d23, d24, d34⟩ := fourCycle_edges_distinct hab hau hav hbu hbv huv
  obtain ⟨pf, pt⟩ := opposingPair_four a b u v
  obtain ⟨hf, ht⟩ := chosenEdge_four a b u v j
  rw [mem_selected_four_iff a b u v hj, hf, ht] at hs
  cases p
  · rw [pf] at hp; rw [hf]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    by_cases h2 : j < 2 <;> by_cases h12 : j = 1 ∨ j = 2 <;> simp only [h2, h12, ite_true, ite_false] at hs ⊢
    all_goals rcases hp with rfl | rfl
    all_goals first | rfl | (exfalso; rcases hs with hs | hs) <;> simp_all
  · rw [pt] at hp; rw [ht]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    by_cases h2 : j < 2 <;> by_cases h12 : j = 1 ∨ j = 2 <;> simp only [h2, h12, ite_true, ite_false] at hs ⊢
    all_goals rcases hp with rfl | rfl
    all_goals first | rfl | (exfalso; rcases hs with hs | hs) <;> simp_all

/-- Every edge of the cycle lies in exactly one opposing pair. -/
theorem mem_opposingPair_four {a b u v : Nat} (hab : a ≠ b) (hau : a ≠ u) (hav : a ≠ v)
    (hbu : b ≠ u) (hbv : b ≠ v) (huv : u ≠ v) (e : Edge) :
    (e ∈ cycleEdges [a, b, u, v] ↔
      e ∈ opposingPair [a, b, u, v] false ∨ e ∈ opposingPair [a, b, u, v] true) ∧
    ¬ (e ∈ opposingPair [a, b, u, v] false ∧ e ∈ opposingPair [a, b, u, v] true) := by
  have hd := fourCycle_edges_distinct hab hau hav hbu hbv huv
  obtain ⟨pf, pt⟩ := opposingPair_four a b u v
  rw [pf, pt, cycleEdges_four]
  constructor
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h | h | h) <;> simp [h]
    · rintro ((h | h) | (h | h)) <;> simp [h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro ⟨h₁ | h₁, h₂ | h₂⟩ <;> subst h₁ <;> simp_all

theorem opposingPair_sub_cycleEdges (c : Cycle) (p : Bool) :
    ∀ e ∈ opposingPair c p, e ∈ cycleEdges c := by
  intro e he
  simp only [opposingPair, List.mem_map, List.mem_filter] at he
  obtain ⟨x, ⟨hx, _⟩, rfl⟩ := he
  rw [(List.mem_zipIdx' hx).2]
  exact List.getElem_mem _

theorem opposingPair_nodup {a b u v : Nat} (hab : a ≠ b) (hau : a ≠ u) (hav : a ≠ v)
    (hbu : b ≠ u) (hbv : b ≠ v) (huv : u ≠ v) (p : Bool) :
    (opposingPair [a, b, u, v] p).Nodup := by
  have hd := fourCycle_edges_distinct hab hau hav hbu hbv huv
  obtain ⟨pf, pt⟩ := opposingPair_four a b u v
  cases p
  · rw [pf]; simp [hd.2.1]
  · rw [pt]; simp [hd.2.2.2.2.1]

theorem opposingPair_length_four (a b u v : Nat) (p : Bool) :
    (opposingPair [a, b, u, v] p).length = 2 := by
  obtain ⟨pf, pt⟩ := opposingPair_four a b u v
  cases p <;> simp [pf, pt]

theorem cycleEdges_four_nodup {a b u v : Nat} (hab : a ≠ b) (hau : a ≠ u) (hav : a ≠ v)
    (hbu : b ≠ u) (hbv : b ≠ v) (huv : u ≠ v) : (cycleEdges [a, b, u, v]).Nodup := by
  have hd := fourCycle_edges_distinct hab hau hav hbu hbv huv
  rw [cycleEdges_four]
  simp [hd]

/-- `selected c j` for `j < 4` is one of the four options, and conversely. -/
theorem mem_selectedOptions_four (a b u v : Nat) (q : List Edge) :
    q ∈ selectedOptions [a, b, u, v] ↔ ∃ j, j < 4 ∧ q = selected [a, b, u, v] j := by
  rw [selectedOptions_four]
  constructor
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨2, by omega, rfl⟩
    · exact ⟨3, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    match j, hj with
    | 0, _ => simp
    | 1, _ => simp
    | 2, _ => simp
    | 3, _ => simp

end STACS2027
