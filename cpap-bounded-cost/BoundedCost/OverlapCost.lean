module

public import BoundedCost.PathConstraints

/-!
# The cost as the number of violated overlap constraints

`c(τ) = |𝒪_τ|`: the cost of an assignment is the number of candidate overlaps
`(e, {C, C'})` whose two paths both contain `e`, i.e. the number of overlap
constraints that the omission variables of the assignment falsify.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- The candidate overlap `u = (i, i', e)` is an overlap of the paths `f`: both paths contain `e`. -/
def violatedBy (f : Nat → List Edge) (u : Nat × Nat × Edge) : Bool :=
  (f u.1).contains u.2.2 && (f u.2.1).contains u.2.2

theorem mem_candidateOverlaps (g : Graph) (k : Nat) (u : Nat × Nat × Edge) :
    u ∈ candidateOverlaps g k ↔
      ∃ i i' e, i < i' ∧ i' < (cycles g k).length ∧ e ∈ cycleEdges (kCycle g k i) ∧
        e ∈ cycleEdges (kCycle g k i') ∧ u = (i, i', e) := by
  simp only [candidateOverlaps, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, i', hi', hu⟩
    split at hu
    · rename_i hlt
      simp only [List.mem_map, List.mem_filter, List.contains_iff_mem] at hu
      obtain ⟨e, ⟨he, he'⟩, rfl⟩ := hu
      exact ⟨i, i', e, hlt, hi', he, he', rfl⟩
    · simp at hu
  · rintro ⟨i, i', e, hlt, hi', he, he', rfl⟩
    refine ⟨i, by omega, i', hi', ?_⟩
    simp only [hlt, ↓reduceIte, List.mem_map, List.mem_filter, List.contains_iff_mem]
    exact ⟨e, ⟨he, he'⟩, rfl⟩

/-- An element of the row `(i, i')` of `𝒰` has first component `i` and second `i'`. -/
theorem overlap_row_components {g : Graph} {k i i' : Nat} {u : Nat × Nat × Edge}
    (hu : u ∈ (if i < i' then ((cycleEdges (kCycle g k i)).filter fun e =>
      (cycleEdges (kCycle g k i')).contains e).map (fun e => (i, i', e)) else [])) :
    u.1 = i ∧ u.2.1 = i' := by
  split at hu
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hu
    exact ⟨rfl, rfl⟩
  · simp at hu

/-- `𝒰` lists each candidate overlap once. -/
theorem candidateOverlaps_nodup (g : Graph) (k : Nat) : (candidateOverlaps g k).Nodup := by
  unfold candidateOverlaps
  rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [List.pairwise_flatMap]
    refine ⟨?_, ?_⟩
    · intro i' _
      split
      · rw [List.pairwise_map]
        have hn := (kCycle_isCycle g (List.mem_range.mp hi)).edges_nodup
        rw [List.nodup_iff_pairwise_ne] at hn
        exact (hn.filter _).imp fun h h' => h (by simpa using h')
      · exact List.Pairwise.nil
    · refine List.nodup_range.imp ?_
      intro a b hab x hx y hy hxy
      have := (overlap_row_components hx).2
      have := (overlap_row_components hy).2
      exact hab (by rw [← ‹x.2.1 = a›, ← ‹y.2.1 = b›, hxy])
  · refine List.nodup_range.imp ?_
    intro a b hab x hx y hy hxy
    obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp hx
    obtain ⟨r', hr', hyr⟩ := List.mem_flatMap.mp hy
    have := (overlap_row_components hxr).1
    have := (overlap_row_components hyr).1
    exact hab (by rw [← ‹x.1 = a›, ← ‹y.1 = b›, hxy])

/-! ## The cost as a double sum -/

theorem double_sum_succ (t : Nat) (h : Nat → Nat → Nat) :
    ((List.range (t + 1)).map fun i =>
      ((List.range (t + 1)).map fun i' => if i < i' then h i i' else 0).sum).sum =
    ((List.range t).map fun i =>
      ((List.range t).map fun i' => if i < i' then h i i' else 0).sum).sum +
    ((List.range t).map fun i => h i t).sum := by
  rw [List.range_succ]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.lt_irrefl, ↓reduceIte]
  rw [sum_map_add]
  have h1 : ((List.range t).map fun i => if i < t then h i t else 0).sum =
      ((List.range t).map fun i => h i t).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    simp [List.mem_range.mp hi]
  have h2 : ((List.range t).map fun i' => if t < i' then h t i' else 0).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hx
    have := List.mem_range.mp hi'
    simp [Nat.lt_asymm this]
  rw [h1, h2]
  omega

theorem cost_map_range (t : Nat) (f : Nat → List Edge) :
    cost ((List.range t).map f) =
      ((List.range t).map fun i =>
        ((List.range t).map fun i' => if i < i' then overlap (f i) (f i') else 0).sum).sum := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [double_sum_succ, List.range_succ, List.map_append, List.map_cons, List.map_nil, cost_snoc, ih,
      List.map_map]
    have : ((List.range t).map (overlap (f t) ∘ f)).sum =
        ((List.range t).map fun i => overlap (f i) (f t)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro i _
      simp [overlap_comm]
    rw [this]
    omega

theorem overlap_eq_countP (p q : List Edge) (hq : q.Nodup) :
    overlap p q = p.countP fun e => decide (e ∈ q) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    rw [overlap_cons_left, ih, List.countP_cons]
    by_cases hm : e ∈ q
    · simp [hm, hq.count_of_mem hm]; omega
    · simp [hm, List.count_eq_zero.mpr hm]

/-! ## Counting the violated candidate overlaps -/

theorem countP_candidateOverlaps (g : Graph) (k : Nat) (q : Nat × Nat × Edge → Bool) :
    (candidateOverlaps g k).countP q =
      ((List.range (cycles g k).length).map fun i =>
        ((List.range (cycles g k).length).map fun i' =>
          if i < i' then
            (cycleEdges (kCycle g k i)).countP fun e =>
              (cycleEdges (kCycle g k i')).contains e && q (i, i', e)
          else 0).sum).sum := by
  rw [candidateOverlaps, List.countP_flatMap]
  simp only [Function.comp_def, List.countP_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  apply congrArg List.sum
  apply List.map_congr_left
  intro i' _
  split
  · rw [List.countP_map, List.countP_filter]
    apply List.countP_congr
    intro e _
    simp [Bool.and_comm]
  · rfl

/-- The paths of an assignment: one of the `k` options of each cycle. -/
def PathsOf (g : Graph) (k : Nat) (f : Nat → List Edge) : Prop :=
  ∀ i, i < (cycles g k).length → ∃ i₀, i₀ < k ∧ f i = selected (kCycle g k i) i₀

theorem PathsOf.nodup {g : Graph} {k : Nat} {f : Nat → List Edge} (hf : PathsOf g k f) {i : Nat}
    (hi : i < (cycles g k).length) : (f i).Nodup := by
  obtain ⟨i₀, _, hfi⟩ := hf i hi
  rw [hfi]
  exact selected_nodup (kCycle_isCycle g hi).2.2.1 i₀

theorem PathsOf.subset {g : Graph} {k : Nat} {f : Nat → List Edge} (hf : PathsOf g k f) {i : Nat}
    (hi : i < (cycles g k).length) : ∀ e ∈ f i, e ∈ cycleEdges (kCycle g k i) := by
  obtain ⟨i₀, _, hfi⟩ := hf i hi
  rw [hfi]
  intro e he
  exact selected_mem_cycleEdges he

/-- Counting a property over the edges of a cycle that lie on its path is counting it over the
path. -/
theorem countP_path_of_cycle {g : Graph} {k : Nat} {f : Nat → List Edge} (hf : PathsOf g k f)
    {i : Nat} (hi : i < (cycles g k).length) (P : Edge → Bool) :
    (cycleEdges (kCycle g k i)).countP (fun e => (f i).contains e && P e) = (f i).countP P := by
  obtain ⟨i₀, hi₀, hfi⟩ := hf i hi
  have hc := kCycle_isCycle g hi
  have hlen := hc.2.1
  have hperm := selected_perm_selectedAt hc (show i₀ < (kCycle g k i).length by omega)
  rw [hfi, hperm.countP_eq, selectedAt, List.countP_filter]
  apply List.countP_congr
  intro e he
  have hmem : e ∈ selected (kCycle g k i) i₀ ↔ avoidsVertex (kCycle g k i)[i₀] e = true := by
    rw [hperm.mem_iff, selectedAt_mem]
    simp only [avoidsVertex, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩
  simp only [List.contains_iff_mem, Bool.and_eq_true, hmem]
  exact and_comm

/-- `c(τ) = |𝒪_τ|`. -/
theorem cost_eq_countP_violated (g : Graph) (k : Nat) {f : Nat → List Edge} (hf : PathsOf g k f) :
    cost ((List.range (cycles g k).length).map f) =
      (candidateOverlaps g k).countP (violatedBy f) := by
  rw [cost_map_range, countP_candidateOverlaps]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  apply congrArg List.sum
  apply List.map_congr_left
  intro i' hi'm
  have hi'' := List.mem_range.mp hi'm
  split
  · -- on the cycle `C_i`: edges in both paths, counted once each
    have h1 : (cycleEdges (kCycle g k i)).countP
        (fun e => (cycleEdges (kCycle g k i')).contains e && violatedBy f (i, i', e)) =
        (cycleEdges (kCycle g k i)).countP (fun e => (f i).contains e && (f i').contains e) := by
      apply List.countP_congr
      intro e _
      simp only [violatedBy, List.contains_iff_mem, Bool.and_eq_true]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro ⟨h₁, h₂⟩; exact ⟨hf.subset hi'' e h₂, h₁, h₂⟩
    rw [h1, countP_path_of_cycle hf hi', overlap_eq_countP _ _ (hf.nodup hi'')]
    apply List.countP_congr
    intro e _
    simp
  · rfl

end STACS2027
