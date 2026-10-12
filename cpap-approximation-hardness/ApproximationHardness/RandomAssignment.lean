module

public import ApproximationHardness.Optimization
public import ApproximationHardness.Sums

/-!
# A random assignment satisfies at least three quarters of the clauses

"A uniformly random truth assignment satisfies each clause with probability at least
`3/4`, so `S* ≥ 3m/4`" (proof of Theorem 11). The argument is carried out by counting:
among the `2^n` assignments of the variables `0, …, n − 1`, a clause with two literals
on distinct variables is falsified by exactly `2^(n−2)` of them, so the clauses satisfied
by all assignments number at least `3m · 2^(n−2)`, and some assignment satisfies at least
the average.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-! ## All assignments of `n` variables -/

/-- All lists of `n` Booleans, each once. -/
def boolLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolLists n).flatMap fun l => [l ++ [false], l ++ [true]]

/-- The assignment reading the list `l` (false beyond its end). -/
def ofList (l : List Bool) : Assignment := fun v => l.getD v false

theorem boolLists_length (n : Nat) : (boolLists n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [boolLists, List.length_flatMap]
    rw [show (fun l : List Bool => [l ++ [false], l ++ [true]].length) = fun _ => 2 from rfl,
      sum_map_const, ih, Nat.pow_succ]

theorem length_of_mem_boolLists {n : Nat} {l : List Bool} (h : l ∈ boolLists n) : l.length = n := by
  induction n generalizing l with
  | zero => simp [boolLists] at h; simp [h]
  | succ n ih =>
    simp only [boolLists, List.mem_flatMap] at h
    obtain ⟨l', hl', h⟩ := h
    have := ih hl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp [this]

theorem getD_append_left {l : List Bool} {x : Nat} (hx : x < l.length) (c : Bool) :
    (l ++ [c]).getD x false = l.getD x false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hx]

theorem getD_append_end (l : List Bool) (c : Bool) : (l ++ [c]).getD l.length false = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem countP_flatMap_pair (n : Nat) (p : List Bool → Bool) :
    (boolLists (n + 1)).countP p =
      ((boolLists n).map fun l => (if p (l ++ [false]) then 1 else 0) + (if p (l ++ [true]) then 1 else 0)).sum := by
  simp only [boolLists, List.countP_flatMap, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l _
  simp only [List.countP_cons, List.countP_nil]
  cases p (l ++ [false]) <;> cases p (l ++ [true]) <;> simp

/-- Exactly half of the assignments give variable `x < n` the value `b`. -/
theorem count_one (n x : Nat) (hx : x < n) (b : Bool) :
    (boolLists n).countP (fun l => l.getD x false == b) = 2 ^ (n - 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [countP_flatMap_pair]
    by_cases hxn : x < n
    · have hcongr : ((boolLists n).map fun l => (if (l ++ [false]).getD x false == b then 1 else 0) +
          (if (l ++ [true]).getD x false == b then 1 else 0)) =
          (boolLists n).map fun l => 2 * (if l.getD x false == b then 1 else 0) := by
        apply List.map_congr_left
        intro l hl
        have hlen : x < l.length := by rw [length_of_mem_boolLists hl]; exact hxn
        rw [getD_append_left hlen, getD_append_left hlen]
        split <;> omega
      rw [hcongr, sum_map_mul_left, sum_map_countP_eq_length, ih hxn]
      have : n = (n - 1) + 1 := by omega
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, Nat.pow_succ]
      omega
    · have hxn' : x = n := by omega
      subst hxn'
      have hcongr : ((boolLists x).map fun l => (if (l ++ [false]).getD x false == b then 1 else 0) +
          (if (l ++ [true]).getD x false == b then 1 else 0)) = (boolLists x).map fun _ => 1 := by
        apply List.map_congr_left
        intro l hl
        have hlen : l.length = x := length_of_mem_boolLists hl
        rw [← hlen, getD_append_end, getD_append_end]
        cases b <;> simp
      rw [hcongr, sum_map_const_one, boolLists_length]
      simp

/-- Exactly a quarter of the assignments give two distinct variables `x, y < n` the values
`b₁, b₂`. -/
theorem count_two (n x y : Nat) (hx : x < n) (hy : y < n) (hxy : x ≠ y) (b₁ b₂ : Bool) :
    (boolLists n).countP (fun l => l.getD x false == b₁ && l.getD y false == b₂) = 2 ^ (n - 2) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [countP_flatMap_pair]
    by_cases hxn : x < n
    · by_cases hyn : y < n
      · have hcongr : ((boolLists n).map fun l =>
            (if ((l ++ [false]).getD x false == b₁ && (l ++ [false]).getD y false == b₂) then 1 else 0) +
            (if ((l ++ [true]).getD x false == b₁ && (l ++ [true]).getD y false == b₂) then 1 else 0)) =
            (boolLists n).map fun l => 2 * (if (l.getD x false == b₁ && l.getD y false == b₂) then 1 else 0) := by
          apply List.map_congr_left
          intro l hl
          have hlx : x < l.length := by rw [length_of_mem_boolLists hl]; exact hxn
          have hly : y < l.length := by rw [length_of_mem_boolLists hl]; exact hyn
          rw [getD_append_left hlx, getD_append_left hlx, getD_append_left hly, getD_append_left hly]
          split <;> omega
        rw [hcongr, sum_map_mul_left, sum_map_countP_eq_length, ih hxn hyn]
        have h2 : 2 ≤ n := by omega
        rw [show n + 1 - 2 = (n - 2) + 1 by omega, Nat.pow_succ]
        omega
      · have hyn' : y = n := by omega
        subst hyn'
        have hcongr : ((boolLists y).map fun l =>
            (if ((l ++ [false]).getD x false == b₁ && (l ++ [false]).getD y false == b₂) then 1 else 0) +
            (if ((l ++ [true]).getD x false == b₁ && (l ++ [true]).getD y false == b₂) then 1 else 0)) =
            (boolLists y).map fun l => if l.getD x false == b₁ then 1 else 0 := by
          apply List.map_congr_left
          intro l hl
          have hlen : l.length = y := length_of_mem_boolLists hl
          have hlx : x < l.length := by rw [hlen]; exact hxn
          rw [getD_append_left hlx, getD_append_left hlx, ← hlen, getD_append_end, getD_append_end]
          cases b₂ <;> cases l.getD x false == b₁ <;> simp
        rw [hcongr, sum_map_countP_eq_length, count_one y x hxn b₁]
        rfl
    · have hxn' : x = n := by omega
      subst hxn'
      have hyn : y < x := by omega
      have hcongr : ((boolLists x).map fun l =>
          (if ((l ++ [false]).getD x false == b₁ && (l ++ [false]).getD y false == b₂) then 1 else 0) +
          (if ((l ++ [true]).getD x false == b₁ && (l ++ [true]).getD y false == b₂) then 1 else 0)) =
          (boolLists x).map fun l => if l.getD y false == b₂ then 1 else 0 := by
        apply List.map_congr_left
        intro l hl
        have hlen : l.length = x := length_of_mem_boolLists hl
        have hly : y < l.length := by rw [hlen]; exact hyn
        rw [getD_append_left hly, getD_append_left hly, ← hlen, getD_append_end, getD_append_end]
        cases b₁ <;> cases l.getD y false == b₂ <;> simp
      rw [hcongr, sum_map_countP_eq_length, count_one x y hyn b₂]
      rfl

/-! ## Clauses with two literals on distinct variables -/

/-- A clause with two literals on distinct variables below `n` is falsified by at most a
quarter of the assignments: `4 · (number satisfying it) ≥ 3 · 2^n`. -/
theorem clause_satisfied_count {n : Nat} {c : Clause} (hc : 2 ≤ c.length)
    (hvar : ∀ l ∈ c, l.var < n) (hdist : (c.map Literal.var).Nodup) :
    3 * 2 ^ n ≤ 4 * (boolLists n).countP fun l => evalClause (ofList l) c := by
  match c, hc with
  | l₁ :: l₂ :: rest, _ =>
    have h1 : l₁.var < n := hvar l₁ (by simp)
    have h2 : l₂.var < n := hvar l₂ (by simp)
    have hne : l₁.var ≠ l₂.var := by
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map, not_or] at hdist
      exact hdist.1.1
    have hfalse : ((boolLists n).countP fun l => !evalClause (ofList l) (l₁ :: l₂ :: rest)) ≤
        (boolLists n).countP fun l => l.getD l₁.var false == !l₁.positive && l.getD l₂.var false == !l₂.positive := by
      apply List.countP_mono_left
      intro l _ h
      simp only [Bool.not_eq_true', evalClause, List.any_cons, Bool.or_eq_false_iff] at h
      obtain ⟨h1', h2', _⟩ := h
      simp only [evalLiteral, ofList] at h1' h2'
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · cases hp : l₁.positive <;> simp [hp] at h1' <;> simp [h1']
      · cases hp : l₂.positive <;> simp [hp] at h2' <;> simp [h2']
    rw [count_two n l₁.var l₂.var h1 h2 hne] at hfalse
    have hlen := List.length_eq_countP_add_countP (fun l => evalClause (ofList l) (l₁ :: l₂ :: rest))
      (l := boolLists n)
    rw [boolLists_length] at hlen
    have hc' : ((boolLists n).countP fun l => ¬ evalClause (ofList l) (l₁ :: l₂ :: rest) = true) =
        (boolLists n).countP fun l => !evalClause (ofList l) (l₁ :: l₂ :: rest) := by
      apply List.countP_congr; intro l _; simp
    rw [hc'] at hlen
    have hpow : 2 ^ n = 4 * 2 ^ (n - 2) := by
      have : n = (n - 2) + 2 := by omega
      conv => lhs; rw [this]
      rw [Nat.pow_add]
      omega
    omega

theorem sum_satisfiedCount (n : Nat) (f : CNF) :
    ((boolLists n).map fun l => satisfiedCount (ofList l) f).sum =
      (f.map fun c => (boolLists n).countP fun l => evalClause (ofList l) c).sum := by
  unfold satisfiedCount
  have h1 : ((boolLists n).map fun l => f.countP (evalClause (ofList l))) =
      (boolLists n).map fun l => (f.map fun c => if evalClause (ofList l) c then 1 else 0).sum := by
    apply List.map_congr_left
    intro l _
    rw [sum_map_countP_eq_length]
  have h2 : (f.map fun c => (boolLists n).countP fun l => evalClause (ofList l) c) =
      f.map fun c => ((boolLists n).map fun l => if evalClause (ofList l) c then 1 else 0).sum := by
    apply List.map_congr_left
    intro c _
    rw [sum_map_countP_eq_length]
  rw [h1, h2, sum_map_swap]

theorem exists_ge_of_sum {α : Type} (l : List α) (g : α → Nat) (hl : l ≠ []) (T : Nat)
    (h : T * l.length ≤ (l.map g).sum) : ∃ x ∈ l, T ≤ g x := by
  apply Classical.byContradiction
  intro hnot
  have hall : ∀ x ∈ l, g x ≤ T - 1 := by
    intro x hx
    have : ¬ T ≤ g x := fun h' => hnot ⟨x, hx, h'⟩
    omega
  have hsum := sum_map_le_sum_map l g (fun _ => T - 1) hall
  rw [sum_map_const] at hsum
  have hpos : 0 < l.length := List.length_pos_iff.mpr hl
  have hT : 0 < T := by
    apply Classical.byContradiction
    intro hT
    have hT0 : T = 0 := by omega
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hl
    exact hnot ⟨x, hx, by omega⟩
  have : l.length * (T - 1) < T * l.length := by
    rw [Nat.mul_comm]
    apply Nat.mul_lt_mul_of_pos_right _ hpos
    omega
  omega

/-- `S* ≥ 3m/4`: some truth assignment satisfies at least three quarters of the clauses of a
formula whose clauses have two or more literals on distinct variables. -/
theorem exists_three_quarters {f : CNF} (hc : ∀ c ∈ f, 2 ≤ c.length)
    (hdist : ClauseVariablesDistinct f) :
    ∃ a : Assignment, 3 * f.length ≤ 4 * satisfiedCount a f := by
  have hsum := sum_satisfiedCount (variableBound f) f
  have hclauses : 3 * f.length * 2 ^ (variableBound f) ≤
      4 * (f.map fun c => (boolLists (variableBound f)).countP fun l => evalClause (ofList l) c).sum := by
    rw [← sum_map_mul_left]
    have := sum_map_le_sum_map f (fun _ => 3 * 2 ^ (variableBound f))
      (fun c => 4 * (boolLists (variableBound f)).countP fun l => evalClause (ofList l) c)
      (fun c hcm => clause_satisfied_count (hc c hcm) (fun l hl => literal_lt_variableBound hcm hl) (hdist c hcm))
    rw [sum_map_const] at this
    have e : 3 * f.length * 2 ^ (variableBound f) = f.length * (3 * 2 ^ (variableBound f)) := by
      rw [Nat.mul_comm 3, Nat.mul_assoc]
    rw [e]
    exact this
  have hne : boolLists (variableBound f) ≠ [] := by
    intro h
    have := boolLists_length (variableBound f)
    rw [h] at this
    simp at this
    have := Nat.two_pow_pos (variableBound f)
    omega
  obtain ⟨l, _, hl⟩ := exists_ge_of_sum (boolLists (variableBound f)) (fun l => 4 * satisfiedCount (ofList l) f)
    hne (3 * f.length) (by
      rw [sum_map_mul_left, hsum, boolLists_length]
      exact hclauses)
  exact ⟨ofList l, hl⟩

end STACS2027
