module

public import Hardness.MaxSNP.Hard.Defs
public import Hardness.Verifier.Words
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Perm.Subperm

/-!
# The averaging argument, as double counting over the words of a fixed length

* `sum_map_countP_comm`: double counting for a Boolean relation between two lists;
* `exists_le_of_mul_length_le_sum`: some element is at least the average;
* `countP_matchPat`: the number of words extending a partial assignment (a *pattern*);
* `count_extend`: among the words of length `M`, at least the fraction `2 ^ (-a)` gives
  prescribed consistent values to `a` variables.
-/

@[expose] public section

namespace Complexity

/-! ### Sums and counting -/

theorem sum_map_ite_add {β : Type} (l : List β) (q : β → Bool) (f : β → Nat) :
    (l.map fun y => (if q y then 1 else 0) + f y).sum = l.countP q + (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    omega

/-- Double counting. -/
theorem sum_map_countP_comm {α β : Type} (l₁ : List α) (l₂ : List β) (p : α → β → Bool) :
    (l₁.map fun x => l₂.countP (p x)).sum = (l₂.map fun y => l₁.countP fun x => p x y).sum := by
  induction l₁ with
  | nil =>
    simp only [List.map_nil, List.sum_nil, List.countP_nil]
    induction l₂ with
    | nil => rfl
    | cons y l₂ ih => simp
  | cons x l₁ ih =>
    have e : (fun y => (x :: l₁).countP fun x => p x y) =
        fun y => (if p x y then 1 else 0) + l₁.countP fun x => p x y := by
      funext y
      rw [List.countP_cons]
      omega
    rw [List.map_cons, List.sum_cons, ih, e, sum_map_ite_add]

theorem sum_map_mul_const {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun x => f x * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem mul_length_le_sum {α : Type} (l : List α) (g : α → Nat) (c : Nat)
    (h : ∀ x ∈ l, c ≤ g x) : c * l.length ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h₁ := h x List.mem_cons_self
    have h₂ := ih fun x' hx' => h x' (List.mem_cons_of_mem _ hx')
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

/-- Some element is at least the average. -/
theorem exists_le_of_mul_length_le_sum {α : Type} (l : List α) (f : α → Nat) (N : Nat)
    (hne : l ≠ []) (h : N * l.length ≤ (l.map f).sum) : ∃ x ∈ l, N ≤ f x := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x l ih =>
    by_cases hx : N ≤ f x
    · exact ⟨x, List.mem_cons_self, hx⟩
    · simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ] at h
      by_cases hl : l = []
      · subst hl
        simp at h
        omega
      · obtain ⟨x', hx', hle⟩ := ih hl (by omega)
        exact ⟨x', List.mem_cons_of_mem _ hx', hle⟩

/-! ### Patterns -/

/-- The word `w` extends the partial assignment `p` of its first positions. -/
def matchPat : List (Option Bool) → Word → Bool
  | [], _ => true
  | o :: p, w => (o.elim true fun b => b == w.headD false) && matchPat p w.tail

/-- A pattern with `s` prescribed positions is extended by the fraction `2 ^ (-s)` of the
words. -/
theorem countP_matchPat (p : List (Option Bool)) :
    (allWords p.length).countP (matchPat p) * 2 ^ p.countP Option.isSome = 2 ^ p.length := by
  induction p with
  | nil => simp [allWords_zero, matchPat]
  | cons o p ih =>
    rw [List.length_cons, allWords_countP_succ]
    have hz : (allWords p.length).countP (fun _ => false) = 0 :=
      List.countP_eq_zero.mpr (by simp)
    cases o with
    | none =>
      have e : ∀ b : Bool, (fun w => matchPat (none :: p) (b :: w)) = matchPat p := fun b => rfl
      have e' : (none :: p).countP Option.isSome = p.countP Option.isSome := by
        simp
      rw [e, e, e', Nat.pow_succ, ← ih, Nat.add_mul]
      omega
    | some b =>
      have e' : (some b :: p).countP Option.isSome = p.countP Option.isSome + 1 := by
        simp
      have e₁ : (fun w => matchPat (some b :: p) (b :: w)) = matchPat p := by
        funext w
        simp [matchPat]
      have e₂ : (fun w => matchPat (some b :: p) ((!b) :: w)) = fun _ => false := by
        funext w
        cases b <;> simp [matchPat]
      have hc : (allWords p.length).countP (fun w => matchPat (some b :: p) (false :: w)) +
          (allWords p.length).countP (fun w => matchPat (some b :: p) (true :: w)) =
            (allWords p.length).countP (matchPat p) := by
        cases b with
        | false =>
          have e₂' := e₂
          simp only [Bool.not_false] at e₂'
          rw [e₁, e₂', hz, Nat.add_zero]
        | true =>
          have e₂' := e₂
          simp only [Bool.not_true] at e₂'
          rw [e₁, e₂', hz, Nat.zero_add]
      rw [hc, e', Nat.pow_succ, Nat.pow_succ, ← ih, Nat.mul_assoc]

/-- A word extending a pattern has the prescribed values. -/
theorem getD_of_matchPat {p : List (Option Bool)} :
    ∀ {w : Word} {v : Nat} {b : Bool}, matchPat p w = true → p[v]? = some (some b) →
      w.getD v false = b := by
  induction p with
  | nil => intro w v b _ hv; simp at hv
  | cons o p ih =>
    intro w v b hm hv
    simp only [matchPat, Bool.and_eq_true] at hm
    cases v with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
      subst hv
      have h := hm.1
      simp only [Option.elim_some, beq_iff_eq] at h
      cases w <;> simp_all
    | succ v =>
      simp only [List.getElem?_cons_succ] at hv
      have h := ih hm.2 hv
      cases w <;> simp_all

/-! ### Values of a list of variables -/

theorem lookup_zip_isSome (vs : List Nat) :
    ∀ (β : List Bool) (v : Nat), β.length = vs.length →
      (((vs.zip β).lookup v).isSome ↔ v ∈ vs) := by
  induction vs with
  | nil => intro β v _; simp
  | cons u vs ih =>
    intro β v hlen
    cases β with
    | nil => simp at hlen
    | cons b β =>
      simp only [List.zip_cons_cons, List.lookup_cons, List.mem_cons]
      by_cases h : v = u
      · simp [h]
      · have h' : (v == u) = false := by simpa using h
        rw [h']
        simp only [h, false_or]
        exact ih β v (by simpa using hlen)

theorem lookup_zip_map (y : Nat → Bool) (vs : List Nat) (v : Nat) :
    (vs.zip (vs.map y)).lookup v = if v ∈ vs then some (y v) else none := by
  induction vs with
  | nil => simp
  | cons u vs ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons, List.mem_cons]
    by_cases h : v = u
    · simp [h]
    · have h' : (v == u) = false := by simpa using h
      rw [h', ih]
      simp [h]

/-- Values read from an assignment are consistent. -/
theorem normWord_map (y : Nat → Bool) (vs : List Nat) : normWord vs (vs.map y) = vs.map y := by
  unfold normWord
  refine List.map_congr_left fun v hv => ?_
  rw [lookup_zip_map]
  simp [hv]

theorem length_normWord (vs : List Nat) (β : List Bool) : (normWord vs β).length = vs.length := by
  simp [normWord]

/-- Among the words of length `M`, at least the fraction `2 ^ (-a)` gives the consistent
values `normWord vs β` to the `a` variables `vs`. -/
theorem count_extend (M : Nat) (vs : List Nat) (β : List Bool) (hv : ∀ v ∈ vs, v < M)
    (hlen : β.length = vs.length) :
    2 ^ M ≤ (allWords M).countP
      (fun w => decide (vs.map (fun v => w.getD v false) = normWord vs β)) * 2 ^ vs.length := by
  let p : List (Option Bool) := (List.range M).map fun v => (vs.zip β).lookup v
  have hpl : p.length = M := by simp [p]
  have h₁ := countP_matchPat p
  rw [hpl] at h₁
  have h₂ : (allWords M).countP (matchPat p) ≤ (allWords M).countP
      (fun w => decide (vs.map (fun v => w.getD v false) = normWord vs β)) := by
    refine List.countP_mono_left fun w _ hw => ?_
    rw [decide_eq_true_eq]
    unfold normWord
    refine List.map_congr_left fun v hvm => ?_
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((lookup_zip_isSome vs β v hlen).mpr hvm)
    rw [hb]
    refine getD_of_matchPat hw ?_
    simp [p, hv v hvm, hb]
  have h₃ : p.countP Option.isSome ≤ vs.length := by
    have e : p.countP Option.isSome =
        ((List.range M).filter fun v => ((vs.zip β).lookup v).isSome).length := by
      show ((List.range M).map fun v => (vs.zip β).lookup v).countP Option.isSome = _
      rw [List.countP_map, List.countP_eq_length_filter]
      rfl
    rw [e]
    refine (List.subperm_of_subset (List.nodup_range.filter _) ?_).length_le
    intro v hvm
    exact (lookup_zip_isSome vs β v hlen).mp (List.mem_filter.mp hvm).2
  calc 2 ^ M = (allWords M).countP (matchPat p) * 2 ^ p.countP Option.isSome := h₁.symm
    _ ≤ _ := Nat.mul_le_mul h₂ (Nat.pow_le_pow_right (by omega) h₃)

end Complexity
