module

public import Tractability.NetworkCounts

/-!
# Tools for the two directions of Theorem 2

Index-based access to the cycles and the chosen paths, the load of a family of paths
as a sum of indicators, the network has no repeated arc, and two arithmetic facts
about the costs `0, …, ϖ(e) - 1` of the sink arcs.
-/

@[expose] public section
namespace STACS2027

/-! ## Index-based access -/

theorem getD_map_range {α : Type} (t : Nat) (f : Nat → α) (d : α) {i : Nat} (hi : i < t) :
    ((List.range t).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem map_getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
    rw [ih]

theorem fourCycle_isCycle (g : Graph) {i : Nat} (hi : i < (cycles g 4).length) :
    IsCycle g 4 (fourCycle g i) := by
  apply enumerated_isCycle
  rw [fourCycle, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem fourCycle_mem (g : Graph) {i : Nat} (hi : i < (cycles g 4).length) :
    fourCycle g i ∈ cycles g 4 := by
  rw [fourCycle, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem opposingPair_fourCycle_nodup (g : Graph) {i : Nat} (hi : i < (cycles g 4).length)
    (p : Bool) : (opposingPair (fourCycle g i) p).Nodup := by
  obtain ⟨a, b, u, v, hc, hab, hau, hav, hbu, hbv, huv⟩ := fourCycle_shape (fourCycle_isCycle g hi)
  rw [hc]
  exact opposingPair_nodup hab hau hav hbu hbv huv p

/-- `countP` over a list as a sum over its indices. -/
theorem countP_eq_sum_range {α : Type} (l : List α) (d : α) (q : α → Bool) :
    l.countP q = ((List.range l.length).map fun i => if q (l.getD i d) then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.countP_cons, ih]
    simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
    omega

theorem cycleCount_eq_countP (g : Graph) (e : Edge) :
    cycleCount g e = (cycles g 4).countP fun c => decide (e ∈ cycleEdges c) := by
  rw [cycleCount]
  apply List.countP_congr
  intro c _
  simp

theorem cycleCount_eq_sum (g : Graph) (e : Edge) :
    cycleCount g e = ((List.range (cycles g 4).length).map fun i =>
      if e ∈ cycleEdges (fourCycle g i) then 1 else 0).sum := by
  rw [cycleCount_eq_countP, countP_eq_sum_range _ []]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [fourCycle]

/-! ## Valid choices, index by index -/

theorem validChoices_getD {cs : List Cycle} {ps : List (List Edge)}
    (hv : ValidChoices (cs.map selectedOptions) ps) :
    ps.length = cs.length ∧ ∀ i, i < cs.length → ps.getD i [] ∈ selectedOptions (cs.getD i []) := by
  induction cs generalizing ps with
  | nil =>
    cases ps with
    | nil => exact ⟨rfl, fun i hi => by simp at hi⟩
    | cons p ps => exact False.elim hv
  | cons c cs ih =>
    cases ps with
    | nil => exact False.elim hv
    | cons p ps =>
      obtain ⟨hp, hv⟩ := hv
      obtain ⟨hlen, hall⟩ := ih hv
      refine ⟨by simp [hlen], ?_⟩
      intro i hi
      cases i with
      | zero => simpa using hp
      | succ i => simpa using hall i (by simpa using hi)

theorem validChoices_of_getD {cs : List Cycle} {ps : List (List Edge)}
    (hlen : ps.length = cs.length)
    (hall : ∀ i, i < cs.length → ps.getD i [] ∈ selectedOptions (cs.getD i [])) :
    ValidChoices (cs.map selectedOptions) ps := by
  induction cs generalizing ps with
  | nil =>
    cases ps with
    | nil => trivial
    | cons p ps => simp at hlen
  | cons c cs ih =>
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      refine ⟨by simpa using hall 0 (by simp), ?_⟩
      apply ih (by simpa using hlen)
      intro i hi
      simpa using hall (i + 1) (by simpa using hi)

/-! ## Loads as sums of indicators -/

theorem load_eq_sum_indicator (t : Nat) (f : Nat → List Edge) (hn : ∀ i, i < t → (f i).Nodup)
    (e : Edge) :
    load ((List.range t).map f) e = ((List.range t).map fun i => if e ∈ f i then 1 else 0).sum := by
  simp only [load, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hni := hn i (List.mem_range.mp hi)
  by_cases hm : e ∈ f i
  · simp [hm, hni.count_of_mem hm]
  · simp [hm, List.count_eq_zero.mpr hm]

/-! ## The network has no repeated arc -/

theorem sourceLayer_nodup (t : Nat) : (sourceLayer t).Nodup := by
  rw [sourceLayer, List.Nodup, List.pairwise_flatMap]
  constructor
  · intro i _; simp
  · apply List.Pairwise.imp_of_mem (R := (· < ·))
    · intro i j _ _ hij x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp <;> omega
    · exact List.pairwise_lt_range

theorem pairLayer_nodup (t : Nat) (C : Nat → Cycle) (hn : ∀ i, i < t → ∀ p, (opposingPair (C i) p).Nodup) :
    (pairLayer t C).Nodup := by
  rw [pairLayer, List.Nodup, List.pairwise_flatMap]
  constructor
  · intro i hi
    have hi' := List.mem_range.mp hi
    have hmap : ∀ p : Bool, ((opposingPair (C i) p).map fun e =>
        (⟨.pair i p, .edgeNode e, 0⟩ : Arc)).Nodup := by
      intro p
      rw [List.Nodup, List.pairwise_map]
      apply List.Pairwise.imp (R := (· ≠ ·))
      · intro e e' hee' h
        simp only [Arc.mk.injEq, FlowNode.edgeNode.injEq] at h
        exact hee' h.2.1
      · exact hn i hi' p
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change List.Nodup (_ ++ _)
    rw [List.nodup_append]
    refine ⟨hmap false, hmap true, ?_⟩
    intro a ha b hb
    simp only [List.mem_map] at ha hb
    obtain ⟨e, _, rfl⟩ := ha
    obtain ⟨e', _, rfl⟩ := hb
    simp
  · apply List.Pairwise.imp_of_mem (R := (· < ·))
    · intro i j _ _ hij x hx y hy
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hx hy
      obtain ⟨p, _, e, _, rfl⟩ := hx
      obtain ⟨q, _, e', _, rfl⟩ := hy
      simp; omega
    · exact List.pairwise_lt_range

theorem sinkLayer_nodup (es : List Edge) (hes : es.Nodup) (w : Edge → Nat) :
    (sinkLayer es w).Nodup := by
  rw [sinkLayer, List.Nodup, List.pairwise_flatMap]
  constructor
  · intro e _
    rw [List.pairwise_map]
    apply List.Pairwise.imp (R := (· < ·))
    · intro j j' hjj' h
      simp only [Arc.mk.injEq] at h
      omega
    · exact List.pairwise_lt_range
  · apply List.Pairwise.imp (R := (· ≠ ·))
    · intro e e' hee' x hx y hy
      simp only [List.mem_map, List.mem_range] at hx hy
      obtain ⟨j, _, rfl⟩ := hx
      obtain ⟨j', _, rfl⟩ := hy
      simp [hee']
    · exact hes

theorem fourCycleNetwork_nodup (g : Graph) : (fourCycleNetwork g).Nodup := by
  rw [fourCycleNetwork, sourceArcs_eq, pairArcs_eq, sinkArcs_eq, List.nodup_append,
    List.nodup_append]
  refine ⟨⟨sourceLayer_nodup _, pairLayer_nodup _ _ (fun i hi p => opposingPair_fourCycle_nodup g hi p), ?_⟩,
    sinkLayer_nodup _ (cycleEdgeList_nodup g) _, ?_⟩
  · intro a ha b hb
    obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer _ a).mp ha
    obtain ⟨i', p', e, _, _, rfl⟩ := (mem_pairLayer _ _ b).mp hb
    simp
  · intro a ha b hb
    obtain ⟨e, j, _, _, rfl⟩ := (mem_sinkLayer _ _ b).mp hb
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, p, _, rfl⟩ := (mem_sourceLayer _ a).mp ha
      simp
    · obtain ⟨i', p', e', _, _, rfl⟩ := (mem_pairLayer _ _ a).mp ha
      simp

/-- A sublist of a list without repetitions is the filter by membership. -/
theorem Sublist.filter_mem_eq {α : Type} [DecidableEq α] {F L : List α} (hs : F.Sublist L)
    (hn : L.Nodup) : L.filter (fun a => decide (a ∈ F)) = F := by
  induction hs with
  | slnil => rfl
  | cons a hs ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hn
    have haF : a ∉ _ := fun h => ha (hs.subset h)
    simp only [List.filter_cons, haF, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ih hn
  | cons_cons a hs ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hn
    simp only [List.filter_cons, List.mem_cons, true_or, decide_true, ↓reduceIte, List.cons.injEq,
      true_and]
    rw [← ih hn]
    apply List.filter_congr
    intro x hx
    have hxa : x ≠ a := fun e => ha (e ▸ hx)
    simp [hxa]
    exact fun h => hs.subset h

/-! ## Arithmetic of the sink costs -/

theorem countP_lt_range (n m : Nat) :
    (List.range n).countP (fun j => decide (j < m)) = min n m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add]
    split <;> simp_all <;> omega

/-- Sending the `m` cheapest of `n ≥ m` unit arcs costs `0 + 1 + ⋯ + (m - 1)`. -/
theorem sum_range_if_lt (n : Nat) : ∀ m, m ≤ n →
    ((List.range n).map fun j => if j < m then j else 0).sum = pairCount m := by
  induction n with
  | zero =>
    intro m hm
    have : m = 0 := by omega
    subst this; rfl
  | succ n ih =>
    intro m hmn
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h : m ≤ n
    · rw [ih m h]
      have : ¬ n < m := by omega
      simp [this]
    · have hm : m = n + 1 := by omega
      subst hm
      have hsum : ((List.range n).map fun j => if j < n + 1 then j else 0).sum =
          ((List.range n).map fun j => if j < n then j else 0).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro j hj
        have := List.mem_range.mp hj
        simp [this, Nat.lt_succ_of_lt this]
      rw [hsum, ih n (Nat.le_refl n)]
      simp [pairCount]

/-- Any `m` of the arcs with costs `0, …, n - 1` cost at least `0 + 1 + ⋯ + (m - 1)`. -/
theorem sum_range_if_ge_pairCount (n : Nat) (b : Nat → Bool) :
    pairCount ((List.range n).countP b) ≤ ((List.range n).map fun j => if b j then j else 0).sum := by
  induction n with
  | zero => simp [pairCount]
  | succ n ih =>
    rw [List.range_succ, List.countP_append, List.map_append, List.sum_append]
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    have hle : (List.range n).countP b ≤ n := by
      have := List.countP_le_length (p := b) (l := List.range n)
      simpa using this
    cases hb : b n
    · simpa using ih
    · simp only [↓reduceIte]
      rw [pairCount]
      omega

end STACS2027
