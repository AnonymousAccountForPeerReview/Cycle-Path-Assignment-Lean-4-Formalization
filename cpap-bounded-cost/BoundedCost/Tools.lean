module

public import BoundedCost.OverlapCost
public import NPHardness.CPAP

/-!
# Tools: valid choices by index, and counting under sublists
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-! ## Valid choices, index by index -/

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

theorem mem_selectedOptions_iff {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) (q : List Edge) :
    q ∈ selectedOptions c ↔ ∃ i₀, i₀ < k ∧ q = selected c i₀ := by
  simp only [selectedOptions, List.mem_map, List.mem_range, hc.2.1]
  constructor
  · rintro ⟨i₀, hi₀, rfl⟩; exact ⟨i₀, hi₀, rfl⟩
  · rintro ⟨i₀, hi₀, rfl⟩; exact ⟨i₀, hi₀, rfl⟩

/-- The paths of a valid choice, as a function of the cycle index. -/
theorem pathsOf_of_validChoices {g : Graph} {k : Nat} {ps : List (List Edge)}
    (hv : ValidChoices ((cycles g k).map selectedOptions) ps) :
    PathsOf g k (fun i => ps.getD i []) ∧ ps = (List.range (cycles g k).length).map fun i => ps.getD i [] := by
  obtain ⟨hlen, hall⟩ := validChoices_getD hv
  refine ⟨?_, by rw [← hlen]; exact (map_getD_range ps []).symm⟩
  intro i hi
  exact (mem_selectedOptions_iff (kCycle_isCycle g hi) _).mp (hall i hi)

theorem validChoices_of_pathsOf {g : Graph} {k : Nat} {f : Nat → List Edge} (hf : PathsOf g k f) :
    ValidChoices ((cycles g k).map selectedOptions) ((List.range (cycles g k).length).map f) := by
  apply validChoices_of_getD
  · simp
  · intro i hi
    rw [getD_map_range _ f [] hi]
    obtain ⟨i₀, hi₀, hfi⟩ := hf i hi
    rw [hfi]
    exact (mem_selectedOptions_iff (kCycle_isCycle g hi) _).mpr ⟨i₀, hi₀, rfl⟩

/-! ## Counting under sublists -/

theorem contains_eq_false_iff {α : Type} [BEq α] [LawfulBEq α] (l : List α) (a : α) :
    l.contains a = false ↔ a ∉ l := by
  rw [← Bool.not_eq_true, List.contains_iff_mem]

/-- Deleting `d` elements removes at most `d` occurrences of any element. -/
theorem Sublist.count_add_le {α : Type} [BEq α] {l L : List α} (hs : l.Sublist L) (a : α) :
    L.count a ≤ l.count a + (L.length - l.length) := by
  induction hs with
  | slnil => simp
  | cons b hs ih =>
    have := hs.length_le
    rw [List.count_cons, List.length_cons]
    split <;> omega
  | cons_cons b hs ih =>
    have := hs.length_le
    rw [List.count_cons, List.count_cons, List.length_cons, List.length_cons]
    split <;> omega

/-- A sublist's length is at most the number of elements of the list that it contains. -/
theorem Sublist.length_le_countP_contains {α : Type} [BEq α] [LawfulBEq α] {l L : List α}
    (hs : l.Sublist L) : l.length ≤ L.countP fun a => l.contains a := by
  induction hs with
  | slnil => simp
  | cons b hs ih =>
    rw [List.countP_cons]
    omega
  | @cons_cons l L b hs ih =>
    rw [List.length_cons, List.countP_cons]
    have hmono : L.countP (fun a => l.contains a) ≤ L.countP (fun a => (b :: l).contains a) := by
      apply List.countP_mono_left
      intro x _ hx
      rw [List.contains_iff_mem] at hx ⊢
      exact List.mem_cons_of_mem b hx
    have hb : (b :: l).contains b = true := by simp
    rw [hb]
    simp only [↓reduceIte]
    omega

/-! ## Sums and counts -/

theorem sum_map_le_sum_map {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x List.mem_cons_self
    have := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

theorem countP_lt_range (n m : Nat) :
    (List.range n).countP (fun j => decide (j < m)) = min n m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add]
    split <;> simp_all <;> omega

theorem sum_map_range_single (n i₀ : Nat) (f : Nat → Nat) (h : ∀ i, i ≠ i₀ → f i = 0) :
    ((List.range n).map f).sum = if i₀ < n then f i₀ else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h₁ : i₀ < n
    · have h₂ : n ≠ i₀ := by omega
      have h₃ : i₀ < n + 1 := by omega
      simp [h₁, h₃, h n h₂]
    · by_cases h₃ : i₀ = n
      · subst h₃
        simp [h₁]
      · have h₄ : n ≠ i₀ := fun e => h₃ e.symm
        have h₅ : ¬ i₀ < n + 1 := by omega
        simp [h₁, h₅, h n h₄]

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

theorem evalCNF_iff (σ : Assignment) (f : CNF) :
    evalCNF σ f = true ↔ ∀ c ∈ f, evalClause σ c = true := by
  simp [evalCNF, List.all_eq_true]

theorem mem_flatten_replicate {α : Type} {n : Nat} {L : List α} {x : α} :
    x ∈ (List.replicate n L).flatten ↔ 0 < n ∧ x ∈ L := by
  simp only [List.mem_flatten, List.mem_replicate]
  constructor
  · rintro ⟨l, ⟨hn, rfl⟩, hx⟩; exact ⟨Nat.pos_of_ne_zero hn, hx⟩
  · rintro ⟨hn, hx⟩; exact ⟨L, ⟨Nat.pos_iff_ne_zero.mp hn, rfl⟩, hx⟩

theorem count_flatten_replicate {α : Type} [BEq α] (n : Nat) (L : List α) (x : α) :
    (List.replicate n L).flatten.count x = n * L.count x := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.count_append, ih, Nat.add_mul, Nat.add_comm]

theorem length_flatten_replicate {α : Type} (n : Nat) (L : List α) :
    (List.replicate n L).flatten.length = n * L.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.add_mul, Nat.add_comm]

end STACS2027
