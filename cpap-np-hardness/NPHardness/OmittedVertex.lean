module

public import NPHardness.SubdivisionProjection

/-!
An orientation-independent description of a selected path: remove the two
cycle edges incident with the omitted vertex. The permutation statements
below connect this description to the executable CPAP choices.
-/

@[expose] public section
namespace STACS2027

def avoidsVertex (v : Nat) (e : Edge) : Bool :=
  e.1 != v && e.2 != v

def selectedAt (c : Cycle) (v : Nat) : List Edge :=
  (cycleEdges c).filter (avoidsVertex v)

theorem avoidsVertex_edge (v a b : Nat) :
    avoidsVertex v (edge a b) = true ↔ a ≠ v ∧ b ≠ v := by
  simp only [avoidsVertex, Bool.and_eq_true, bne_iff_ne, edge]
  by_cases h : a ≤ b
  · simp [Nat.min_eq_left h, Nat.max_eq_right h]
  · simp [Nat.min_eq_right (by omega : b ≤ a), Nat.max_eq_left (by omega : b ≤ a), and_comm]

theorem pathEdges_avoid_vertex {vs : List Nat} {v : Nat} (hv : v ∉ vs) :
    (pathEdges vs).filter (avoidsVertex v) = pathEdges vs := by
  apply List.filter_eq_self.mpr
  intro e he
  obtain ⟨h₁, h₂⟩ := pathEdges_endpoints he
  simp only [avoidsVertex, Bool.and_eq_true, bne_iff_ne]
  exact ⟨fun h => hv (h ▸ h₁), fun h => hv (h ▸ h₂)⟩

theorem selectedAt_head {g : Graph} {k v : Nat} {rest : Cycle}
    (hc : IsCycle g k (v :: rest)) : selectedAt (v :: rest) v = pathEdges rest := by
  have hl := hc.2.1
  have hk := hc.1
  cases rest with
  | nil => simp at hl; omega
  | cons u us =>
    have hne : us ≠ [] := by intro h; subst us; simp at hl; omega
    obtain he | ⟨middle, w, he⟩ := List.eq_nil_or_concat us
    · exact False.elim (hne he)
    rw [List.concat_eq_append] at he
    subst us
    have hv := (List.nodup_cons.mp hc.2.2.1).1
    unfold selectedAt
    rw [cycleEdges_leading]
    simp only [List.filter_cons, List.filter_append, List.filter_nil]
    have huv : avoidsVertex v (edge v u) = false := by
      apply Bool.eq_false_iff.mpr; intro h
      exact (avoidsVertex_edge v v u).mp h |>.1 rfl
    have hwv : avoidsVertex v (edge w v) = false := by
      apply Bool.eq_false_iff.mpr; intro h
      exact (avoidsVertex_edge v w v).mp h |>.2 rfl
    rw [huv, hwv]
    simpa using pathEdges_avoid_vertex hv

theorem SameCycle.selectedAt_perm {g h : Graph} {k l : Nat} {c d : Cycle}
    (hs : SameCycle c d) (hc : IsCycle g k c) (hd : IsCycle h l d) (v : Nat) :
    (selectedAt c v).Perm (selectedAt d v) :=
  (hs.edge_perm hc hd).filter (avoidsVertex v)

theorem selected_at_split (xs ys : Cycle) (v : Nat) :
    selected (xs ++ v :: ys) xs.length = pathEdges (ys ++ xs) := by
  unfold selected
  have hd : (xs ++ v :: ys).drop (xs.length + 1) = ys := by simp
  have ht : (xs ++ v :: ys).take (xs.length + 1) = xs ++ [v] := by
    rw [List.take_append]
    simp
    exact List.take_of_length_le (by omega)
  rw [hd, ht]
  simp only [List.length_append, List.length_cons]
  have hn : xs.length + (ys.length + 1) - 1 = (ys ++ xs).length := by simp; omega
  rw [hn, ← List.append_assoc, List.take_left]

theorem selected_perm_selectedAt {g : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) {i : Nat} (hi : i < c.length) :
    (selected c i).Perm (selectedAt c c[i]) := by
  have hsplit : c = c.take i ++ c[i] :: c.drop (i + 1) := by
    have h := List.take_append_drop i c
    rw [List.drop_eq_getElem_cons hi] at h
    exact h.symm
  have hrot : IsCycle g k (c[i] :: (c.drop (i + 1) ++ c.take i)) := by
    rw [hsplit] at hc
    exact hc.append_swap
  have hs : SameCycle c (c[i] :: (c.drop (i + 1) ++ c.take i)) := by
    have h := sameCycle_append_swap (c.take i) (c[i] :: c.drop (i + 1))
    rw [← hsplit] at h
    exact h
  have hp := hs.selectedAt_perm hc hrot c[i]
  rw [selectedAt_head hrot] at hp
  have heq : selected c i = pathEdges (c.drop (i + 1) ++ c.take i) := by
    have h := selected_at_split (c.take i) (c.drop (i + 1)) c[i]
    rw [← hsplit, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at h
    exact h
  rw [heq]
  exact hp.symm

theorem selectedAt_nodup {g : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) (v : Nat) : (selectedAt c v).Nodup :=
  hc.edges_nodup.filter _

theorem selectedAt_mem {c : Cycle} {v : Nat} {e : Edge} :
    e ∈ selectedAt c v ↔ e ∈ cycleEdges c ∧ e.1 ≠ v ∧ e.2 ≠ v := by
  simp [selectedAt, avoidsVertex]

theorem selectedAt_has_option {g : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) {v : Nat} (hv : v ∈ c) :
    ∃ p ∈ selectedOptions c, p.Perm (selectedAt c v) := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hv
  refine ⟨selected c i, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ?_⟩
  rw [← he]
  exact selected_perm_selectedAt hc hi

theorem selected_option_has_vertex {g : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) {p : List Edge} (hp : p ∈ selectedOptions c) :
    ∃ v ∈ c, p.Perm (selectedAt c v) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have hi' := List.mem_range.mp hi
  exact ⟨c[i], List.getElem_mem hi', selected_perm_selectedAt hc hi'⟩

end STACS2027
