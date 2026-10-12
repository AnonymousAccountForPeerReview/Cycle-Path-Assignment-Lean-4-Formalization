module

public import BoundedCost.Equivalence

/-!
# The prefix variables of Corollary 5

The variable `s_{e,x}` is numbered `kt + (sum, over the edges listed before `e`, of
`p − 1`) + x`. These numbers are all at least `kt`, hence distinct from the path
variables, pairwise distinct, and below `2kt`.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-! ## The edges on cycles and the cycles through an edge -/

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  match l with
  | [] => simp
  | a :: l =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · intro h
      rw [List.mem_eraseDups, List.mem_filter] at h
      simp at h
    · have : (l.filter fun b => !b == a).length < (a :: l).length :=
        Nat.lt_of_le_of_lt (List.length_filter_le _ _) (by simp)
      exact nodup_eraseDups _
termination_by l.length

theorem edgesOnCycles_nodup (g : Graph) (k : Nat) : (edgesOnCycles g k).Nodup := nodup_eraseDups _

theorem mem_edgesOnCycles (g : Graph) (k : Nat) (e : Edge) :
    e ∈ edgesOnCycles g k ↔ ∃ i, i < (cycles g k).length ∧ e ∈ cycleEdges (kCycle g k i) := by
  simp only [edgesOnCycles, List.mem_eraseDups, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, he⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    refine ⟨i, hi, ?_⟩
    rw [kCycle, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact he
  · rintro ⟨i, hi, he⟩
    exact ⟨kCycle g k i, kCycle_mem g hi, he⟩

theorem mem_cyclesThrough (g : Graph) (k : Nat) (e : Edge) (i : Nat) :
    i ∈ cyclesThrough g k e ↔ i < (cycles g k).length ∧ e ∈ cycleEdges (kCycle g k i) := by
  simp [cyclesThrough, List.mem_filter]

theorem cyclesThrough_nodup (g : Graph) (k : Nat) (e : Edge) : (cyclesThrough g k e).Nodup :=
  List.nodup_range.filter _

theorem cyclesThrough_getD_lt (g : Graph) (k : Nat) (e : Edge) {x : Nat}
    (hx : x < (cyclesThrough g k e).length) : (cyclesThrough g k e).getD x 0 < (cycles g k).length :=
  ((mem_cyclesThrough g k e _).mp (getD_mem _ _ hx)).1

theorem cyclesThrough_getD_mem (g : Graph) (k : Nat) (e : Edge) {x : Nat}
    (hx : x < (cyclesThrough g k e).length) : e ∈ cycleEdges (kCycle g k ((cyclesThrough g k e).getD x 0)) :=
  ((mem_cyclesThrough g k e _).mp (getD_mem _ _ hx)).2

theorem cyclesThrough_getD_inj (g : Graph) (k : Nat) (e : Edge) {x y : Nat}
    (hx : x < (cyclesThrough g k e).length) (hy : y < (cyclesThrough g k e).length)
    (h : (cyclesThrough g k e).getD x 0 = (cyclesThrough g k e).getD y 0) : x = y := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx,
    List.getElem?_eq_getElem hy] at h
  simp only [Option.getD_some] at h
  exact ((cyclesThrough_nodup g k e).getElem_inj (hi := hx) (hj := hy)).mp h

/-! ## The sum of `p(e)` over the edges is `kt` -/

theorem countP_contains_eq_sum_count (L S : List Edge) (hS : S.Nodup) :
    L.countP (fun e => S.contains e) = (L.map fun e => S.count e * 1).sum := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]
    by_cases hm : x ∈ S
    · simp only [List.contains_iff_mem, hm, hS.count_of_mem hm, ↓reduceIte]
      omega
    · simp [hm, List.count_eq_zero.mpr hm]

theorem countP_edgesOnCycles_eq_k (g : Graph) {k i : Nat} (hi : i < (cycles g k).length) :
    (edgesOnCycles g k).countP (fun e => (cycleEdges (kCycle g k i)).contains e) = k := by
  have hc := kCycle_isCycle g hi
  have hsub : ∀ e ∈ cycleEdges (kCycle g k i), e ∈ edgesOnCycles g k :=
    fun e he => (mem_edgesOnCycles g k e).mpr ⟨i, hi, he⟩
  rw [countP_contains_eq_sum_count _ _ hc.edges_nodup,
    sum_counts _ _ _ (edgesOnCycles_nodup g k) hsub, sum_map_const, hc.edge_length]
  omega

theorem sum_cyclesThrough_length (g : Graph) (k : Nat) :
    ((edgesOnCycles g k).map fun e => (cyclesThrough g k e).length).sum = k * (cycles g k).length := by
  have hl : ∀ (l : List Nat) (q : Nat → Bool), (l.filter q).length = (l.map fun c => if q c then 1 else 0).sum := by
    intro l q
    induction l with
    | nil => rfl
    | cons c l ih => simp only [List.filter_cons]; split <;> simp_all <;> omega
  have hl' : ∀ (l : List Edge) (q : Edge → Bool), (l.filter q).length = (l.map fun e => if q e then 1 else 0).sum := by
    intro l q
    induction l with
    | nil => rfl
    | cons c l ih => simp only [List.filter_cons]; split <;> simp_all <;> omega
  simp only [cyclesThrough, hl]
  rw [sum_map_swap (edgesOnCycles g k) (List.range (cycles g k).length)
    fun e i => if (cycleEdges (kCycle g k i)).contains e then 1 else 0]
  have : ((List.range (cycles g k).length).map fun i =>
      ((edgesOnCycles g k).map fun e => if (cycleEdges (kCycle g k i)).contains e then 1 else 0).sum) =
      (List.range (cycles g k).length).map fun _ => k := by
    apply List.map_congr_left
    intro i hi
    rw [← hl', ← List.countP_eq_length_filter]
    exact countP_edgesOnCycles_eq_k g (List.mem_range.mp hi)
  rw [this, sum_map_const, List.length_range, Nat.mul_comm]

theorem sum_sub_one_le {α : Type} (L : List α) (w : α → Nat) :
    (L.map fun e => w e - 1).sum ≤ (L.map w).sum := by
  induction L with
  | nil => exact Nat.le_refl _
  | cons x L ih => simp only [List.map_cons, List.sum_cons]; omega

theorem Sublist.sum_le_sum {α : Type} {L L' : List α} (hs : L.Sublist L') (w : α → Nat) :
    (L.map w).sum ≤ (L'.map w).sum := by
  induction hs with
  | slnil => exact Nat.le_refl _
  | cons b hs ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons_cons b hs ih => simp only [List.map_cons, List.sum_cons]; omega

/-! ## Prefix sums along a list without repetition -/

section PrefixSums
variable {α : Type} [BEq α] [LawfulBEq α]

theorem dropWhile_ne_of_mem {L : List α} {e : α} (he : e ∈ L) :
    ∃ rest, L.dropWhile (fun x => x != e) = e :: rest := by
  induction L with
  | nil => simp at he
  | cons x l ih =>
    by_cases hx : x = e
    · subst hx
      exact ⟨l, by simp⟩
    · have hne : (x != e) = true := by simp [hx]
      have hstep : (x :: l).dropWhile (fun y => y != e) = l.dropWhile (fun y => y != e) :=
        List.dropWhile_cons_of_pos hne
      rw [hstep]
      apply ih
      rcases List.mem_cons.mp he with h | h
      · exact absurd h.symm hx
      · exact h

/-- `L = A ++ e :: rest` with `A` the elements before `e`. -/
theorem split_at_mem {L : List α} {e : α} (he : e ∈ L) :
    ∃ rest, L = L.takeWhile (fun x => x != e) ++ e :: rest := by
  obtain ⟨rest, hrest⟩ := dropWhile_ne_of_mem he
  exact ⟨rest, by rw [← hrest]; exact List.takeWhile_append_dropWhile.symm⟩

/-- The prefix sum before an element listed later is at least the prefix sum before `e`
plus the weight of `e`. -/
theorem prefixSum_le_of_after {L : List α} (hL : L.Nodup) {e e' : α} (he : e ∈ L)
    (he' : e' ∈ L.dropWhile fun x => x != e) (hne : e' ≠ e) (w : α → Nat) :
    ((L.takeWhile fun x => x != e).map w).sum + w e ≤ ((L.takeWhile fun x => x != e').map w).sum := by
  obtain ⟨rest, hrest⟩ := dropWhile_ne_of_mem he
  have hsplit : L = L.takeWhile (fun x => x != e) ++ e :: rest := by
    rw [← hrest]; exact List.takeWhile_append_dropWhile.symm
  rw [hrest] at he'
  have he'rest : e' ∈ rest := by
    rcases List.mem_cons.mp he' with h | h
    · exact absurd h hne
    · exact h
  generalize hA : L.takeWhile (fun x => x != e) = A at hsplit ⊢
  rw [hsplit] at hL
  rw [List.nodup_append] at hL
  have hpos : ∀ a ∈ A, (a != e') = true := by
    intro a ha
    have := hL.2.2 a ha e' (List.mem_cons_of_mem e he'rest)
    simp [this]
  have hne' : (e != e') = true := by simp [Ne.symm hne]
  have hstep : (e :: rest).takeWhile (fun a => a != e') = e :: rest.takeWhile (fun a => a != e') :=
    List.takeWhile_cons_of_pos hne'
  rw [hsplit, List.takeWhile_append_of_pos hpos, hstep, List.map_append,
    List.sum_append, List.map_cons, List.sum_cons]
  omega

theorem prefixSum_add_le (L : List α) {e : α} (he : e ∈ L) (w : α → Nat) :
    ((L.takeWhile fun x => x != e).map w).sum + w e ≤ (L.map w).sum := by
  obtain ⟨rest, hsplit⟩ := split_at_mem he
  generalize hA : L.takeWhile (fun x => x != e) = A at hsplit ⊢
  rw [hsplit, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  omega

/-- In a list without repetition, if `e'` is listed before `e` then `e` comes after `e'`. -/
theorem mem_dropWhile_of_mem_takeWhile {L : List α} (hL : L.Nodup) {e e' : α} (he : e ∈ L)
    (he' : e' ∈ L.takeWhile fun x => x != e) : e ∈ L.dropWhile fun x => x != e' := by
  obtain ⟨rest, hsplit⟩ := split_at_mem he
  generalize hA : L.takeWhile (fun x => x != e) = A at hsplit he'
  obtain ⟨A₁, A₂, hA'⟩ := List.append_of_mem he'
  rw [hsplit, hA'] at hL ⊢
  rw [List.append_assoc, List.cons_append]
  have hnd₁ : ∀ a ∈ A₁, (a != e') = true := by
    intro a ha
    rw [List.nodup_append] at hL
    have hnd := hL.1
    rw [List.nodup_append] at hnd
    have := hnd.2.2 a ha e' List.mem_cons_self
    simp [this]
  rw [List.dropWhile_append_of_pos hnd₁, List.dropWhile_cons_of_neg (by simp)]
  simp

end PrefixSums

/-! ## The numbering of the prefix variables -/

theorem prefixOffset_ge (g : Graph) (k : Nat) (e : Edge) :
    k * (cycles g k).length ≤ prefixOffset g k e := by
  unfold prefixOffset; omega

theorem prefixVariable_lt {g : Graph} {k : Nat} {e : Edge} (he : e ∈ edgesOnCycles g k) {x : Nat}
    (hx : x < (cyclesThrough g k e).length - 1) :
    prefixVariable g k e x < 2 * (k * (cycles g k).length) := by
  unfold prefixVariable prefixOffset
  have h1 := prefixSum_add_le (edgesOnCycles g k) he fun e => (cyclesThrough g k e).length - 1
  have h2 := sum_sub_one_le (edgesOnCycles g k) fun e => (cyclesThrough g k e).length
  rw [sum_cyclesThrough_length] at h2
  omega

/-- Distinct edges, or distinct indices, give distinct prefix variables. -/
theorem prefixVariable_inj {g : Graph} {k : Nat} {e e' : Edge} (he : e ∈ edgesOnCycles g k)
    (he' : e' ∈ edgesOnCycles g k) {x x' : Nat} (hx : x < (cyclesThrough g k e).length - 1)
    (hx' : x' < (cyclesThrough g k e').length - 1)
    (h : prefixVariable g k e x = prefixVariable g k e' x') : e = e' ∧ x = x' := by
  by_cases hee : e = e'
  · subst hee
    unfold prefixVariable at h
    exact ⟨rfl, by omega⟩
  · exfalso
    unfold prefixVariable prefixOffset at h
    have hsplit := (List.takeWhile_append_dropWhile (p := fun x => x != e) (l := edgesOnCycles g k)).symm
    have he'' := he'
    rw [hsplit] at he''
    rcases List.mem_append.mp he'' with hbefore | hafter
    · have := prefixSum_le_of_after (edgesOnCycles_nodup g k) he'
        (mem_dropWhile_of_mem_takeWhile (edgesOnCycles_nodup g k) he hbefore) hee
        fun e => (cyclesThrough g k e).length - 1
      omega
    · have := prefixSum_le_of_after (edgesOnCycles_nodup g k) he hafter (Ne.symm hee)
        fun e => (cyclesThrough g k e).length - 1
      omega

end STACS2027
