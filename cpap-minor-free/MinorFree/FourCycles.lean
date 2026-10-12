module

public import NPHardness.AssignmentFamilies
public import NPHardness.AssignmentRelabel
public import NPHardness.GlobalCost

/-!
Four-cycles. A simple `4`-cycle `c` rotated to start at its `i`-th vertex is
`[v, u, x, w]`; its edges are `vu, ux, xw, wv`, and the path omitting `x` (the
vertex opposite `v`) consists of the two edges at `v`. The cost of a family of
pairwise edge-disjoint paths is zero.
-/

@[expose] public section
namespace STACS2027

theorem cost_eq_zero_of_pairwise {ps : List (List Edge)}
    (h : ps.Pairwise fun p q => overlap p q = 0) : cost ps = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨hp, ht⟩ := List.pairwise_cons.mp h
    simp only [cost, ih ht, Nat.add_zero]
    exact List.sum_eq_zero_iff_forall_eq_nat.mpr (fun n hn => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hn
      exact hp q hq)

theorem overlap_eq_zero_of_disjoint {p q : List Edge} (h : ∀ e ∈ p, e ∉ q) : overlap p q = 0 := by
  unfold overlap
  exact List.sum_eq_zero_iff_forall_eq_nat.mpr (fun n hn => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
    exact List.count_eq_zero.mpr (h e he))

theorem overlap_eq_zero_iff (p q : List Edge) : overlap p q = 0 ↔ ∀ e ∈ p, e ∉ q := by
  constructor
  · intro h e he hq
    unfold overlap at h
    have := List.sum_eq_zero_iff_forall_eq_nat.mp h _ (List.mem_map.mpr ⟨e, he, rfl⟩)
    exact (List.count_eq_zero.mp this) hq
  · exact overlap_eq_zero_of_disjoint

/-- A simple `4`-cycle, as seen from its `i`-th vertex `v`: its vertices are `v, u, x, w` in
cyclic order. -/
theorem four_cycle_rotation {c : Cycle} (hl : c.length = 4) {i : Nat} (hi : i < 4) :
    ∃ v u x w, c.drop i ++ c.take i = [v, u, x, w] ∧ c[i]? = some v ∧ c[(i + 2) % 4]? = some x := by
  match c, hl with
  | [c0, c1, c2, c3], _ =>
    match i, hi with
    | 0, _ => exact ⟨c0, c1, c2, c3, rfl, rfl, rfl⟩
    | 1, _ => exact ⟨c1, c2, c3, c0, rfl, rfl, rfl⟩
    | 2, _ => exact ⟨c2, c3, c0, c1, rfl, rfl, rfl⟩
    | 3, _ => exact ⟨c3, c0, c1, c2, rfl, rfl, rfl⟩

theorem cycleEdges_four (v u x w : Nat) :
    cycleEdges [v, u, x, w] = [edge v u, edge u x, edge x w, edge w v] := rfl

theorem mem_cycleEdges_four (v u x w : Nat) (e : Edge) :
    e ∈ cycleEdges [v, u, x, w] ↔ e = edge v u ∨ e = edge u x ∨ e = edge x w ∨ e = edge w v := by
  rw [cycleEdges_four]; simp

theorem edge_has_endpoint (a b x : Nat) (h : a = x ∨ b = x) :
    (edge a b).1 = x ∨ (edge a b).2 = x := by
  rcases h with rfl | rfl
  · rcases edge_left_endpoint a b with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rcases edge_left_endpoint b a with h | h
    · exact Or.inl (by rw [edge_comm]; exact h.symm)
    · exact Or.inr (by rw [edge_comm]; exact h.symm)

theorem edge_avoids (a b x : Nat) (ha : a ≠ x) (hb : b ≠ x) :
    (edge a b).1 ≠ x ∧ (edge a b).2 ≠ x := by
  obtain ⟨h₁, h₂⟩ := edge_endpoints a b
  constructor
  · rcases h₁ with h | h <;> rw [h] <;> assumption
  · rcases h₂ with h | h <;> rw [h] <;> assumption

/-- In the `4`-cycle `[v, u, x, w]`, the path omitting `x` consists of the two edges at `v`. -/
theorem mem_selectedAt_four {v u x w : Nat} (hvx : v ≠ x) (hux : u ≠ x) (hwx : w ≠ x) (e : Edge) :
    e ∈ selectedAt [v, u, x, w] x ↔ e = edge v u ∨ e = edge w v := by
  rw [selectedAt_mem, mem_cycleEdges_four]
  constructor
  · rintro ⟨h, h1, h2⟩
    rcases h with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd (edge_has_endpoint u x x (Or.inr rfl)) (by rintro (h | h) <;> contradiction)
    · exact absurd (edge_has_endpoint x w x (Or.inl rfl)) (by rintro (h | h) <;> contradiction)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, edge_avoids v u x hvx hux⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)), edge_avoids w v x hwx hvx⟩

/-- The cycle `c` and its rotation `c.drop i ++ c.take i` are the same cycle. -/
theorem sameCycle_rotation (c : Cycle) (i : Nat) : SameCycle c (c.drop i ++ c.take i) := by
  have h := sameCycle_append_swap (c.take i) (c.drop i)
  rwa [List.take_append_drop] at h

theorem IsCycle.rotation {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) (i : Nat) :
    IsCycle g k (c.drop i ++ c.take i) := by
  have h : IsCycle g k (c.take i ++ c.drop i) := by rwa [List.take_append_drop]
  exact h.append_swap

theorem nodup_four {v u x w : Nat} (h : [v, u, x, w].Nodup) :
    v ≠ u ∧ v ≠ x ∧ v ≠ w ∧ u ≠ x ∧ u ≠ w ∧ x ≠ w := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6.1⟩

end STACS2027
