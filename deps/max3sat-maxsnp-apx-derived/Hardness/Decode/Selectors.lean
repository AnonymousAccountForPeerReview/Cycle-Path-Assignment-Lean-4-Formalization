module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Deterministic selectors for the gap-amplification decoder

The soundness proofs of the gap-amplification rounds decode by "a most frequent label",
"a most frequent opinion" and "a nearest code word".  For the decoder to be an explicitly
described function, ties are broken here by a fixed rule: the *least* index (in the numeric
order of `Fin n`) attaining the maximum, respectively the minimum.

* `argMaxUpTo count k` is the least `i ≤ k` maximising `count` on `{0, …, k}`; it is computed by
  one left-to-right scan that replaces the current best only on a strictly larger value.
* `argMinUpTo count k` is the least `i ≤ k` minimising `count` on `{0, …, k}` (one scan, replace
  only on a strictly smaller value).
* `leastArgMax h count`, `leastArgMin h count` are the versions for `count : Fin n → Nat`,
  `0 < n`.

Each selector is characterised uniquely by `…_max`/`…_min` (optimality) together with `…_least`
(every smaller index is strictly worse).
-/

@[expose] public section

namespace OAI.UniqueGamesTheorem.Foundations.PCP.Decode

/-- Least maximiser of `count` on `{0, …, k}`: scan `0, 1, …, k`, keeping the current best and
replacing it only by a strictly larger value. -/
def argMaxUpTo (count : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if count (argMaxUpTo count k) < count (k + 1) then k + 1 else argMaxUpTo count k

theorem argMaxUpTo_le (count : Nat → Nat) (k : Nat) : argMaxUpTo count k ≤ k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [argMaxUpTo]
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le ih

theorem argMaxUpTo_max (count : Nat → Nat) (k i : Nat) (hi : i ≤ k) :
    count i ≤ count (argMaxUpTo count k) := by
  induction k with
  | zero =>
    obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
    exact Nat.le_refl _
  | succ k ih =>
    simp only [argMaxUpTo]
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · have hk := ih (Nat.le_of_lt_succ h)
      split <;> omega
    · obtain rfl : i = k + 1 := Nat.le_antisymm hi h
      split <;> omega

theorem argMaxUpTo_least (count : Nat → Nat) (k j : Nat) (hj : j < argMaxUpTo count k) :
    count j < count (argMaxUpTo count k) := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    simp only [argMaxUpTo] at hj ⊢
    by_cases hlt : count (argMaxUpTo count k) < count (k + 1)
    · simp only [hlt, ↓reduceIte] at hj ⊢
      have := argMaxUpTo_max count k j (Nat.le_of_lt_succ hj)
      omega
    · simp only [hlt, ↓reduceIte] at hj ⊢
      exact ih hj

/-- Least minimiser of `count` on `{0, …, k}`: scan `0, 1, …, k`, keeping the current best and
replacing it only by a strictly smaller value. -/
def argMinUpTo (count : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if count (k + 1) < count (argMinUpTo count k) then k + 1 else argMinUpTo count k

theorem argMinUpTo_le (count : Nat → Nat) (k : Nat) : argMinUpTo count k ≤ k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [argMinUpTo]
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le ih

theorem argMinUpTo_min (count : Nat → Nat) (k i : Nat) (hi : i ≤ k) :
    count (argMinUpTo count k) ≤ count i := by
  induction k with
  | zero =>
    obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
    exact Nat.le_refl _
  | succ k ih =>
    simp only [argMinUpTo]
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · have hk := ih (Nat.le_of_lt_succ h)
      split <;> omega
    · obtain rfl : i = k + 1 := Nat.le_antisymm hi h
      split <;> omega

theorem argMinUpTo_least (count : Nat → Nat) (k j : Nat) (hj : j < argMinUpTo count k) :
    count (argMinUpTo count k) < count j := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    simp only [argMinUpTo] at hj ⊢
    by_cases hlt : count (k + 1) < count (argMinUpTo count k)
    · simp only [hlt, ↓reduceIte] at hj ⊢
      have := argMinUpTo_min count k j (Nat.le_of_lt_succ hj)
      omega
    · simp only [hlt, ↓reduceIte] at hj ⊢
      exact ih hj

/-- Extension by zero of a function on `Fin n` to all natural numbers. -/
def extendCount {n : Nat} (count : Fin n → Nat) (i : Nat) : Nat :=
  if h : i < n then count ⟨i, h⟩ else 0

@[simp] theorem extendCount_val {n : Nat} (count : Fin n → Nat) (i : Fin n) :
    extendCount count i.val = count i := by
  simp [extendCount]

/-- The least index of `Fin n` at which `count` is maximal. -/
def leastArgMax {n : Nat} (h : 0 < n) (count : Fin n → Nat) : Fin n :=
  ⟨argMaxUpTo (extendCount count) (n - 1),
    Nat.lt_of_le_of_lt (argMaxUpTo_le _ _) (Nat.sub_lt h Nat.one_pos)⟩

theorem leastArgMax_max {n : Nat} (h : 0 < n) (count : Fin n → Nat) (i : Fin n) :
    count i ≤ count (leastArgMax h count) := by
  have := argMaxUpTo_max (extendCount count) (n - 1) i.val (by have := i.isLt; omega)
  rw [extendCount_val] at this
  have e : extendCount count (argMaxUpTo (extendCount count) (n - 1)) =
      count (leastArgMax h count) := extendCount_val count (leastArgMax h count)
  omega

theorem leastArgMax_least {n : Nat} (h : 0 < n) (count : Fin n → Nat) (j : Fin n)
    (hj : j < leastArgMax h count) : count j < count (leastArgMax h count) := by
  have := argMaxUpTo_least (extendCount count) (n - 1) j.val hj
  rw [extendCount_val] at this
  have e : extendCount count (argMaxUpTo (extendCount count) (n - 1)) =
      count (leastArgMax h count) := extendCount_val count (leastArgMax h count)
  omega

/-- The least index of `Fin n` at which `count` is minimal. -/
def leastArgMin {n : Nat} (h : 0 < n) (count : Fin n → Nat) : Fin n :=
  ⟨argMinUpTo (extendCount count) (n - 1),
    Nat.lt_of_le_of_lt (argMinUpTo_le _ _) (Nat.sub_lt h Nat.one_pos)⟩

theorem leastArgMin_min {n : Nat} (h : 0 < n) (count : Fin n → Nat) (i : Fin n) :
    count (leastArgMin h count) ≤ count i := by
  have := argMinUpTo_min (extendCount count) (n - 1) i.val (by have := i.isLt; omega)
  rw [extendCount_val] at this
  have e : extendCount count (argMinUpTo (extendCount count) (n - 1)) =
      count (leastArgMin h count) := extendCount_val count (leastArgMin h count)
  omega

theorem leastArgMin_least {n : Nat} (h : 0 < n) (count : Fin n → Nat) (j : Fin n)
    (hj : j < leastArgMin h count) : count (leastArgMin h count) < count j := by
  have := argMinUpTo_least (extendCount count) (n - 1) j.val hj
  rw [extendCount_val] at this
  have e : extendCount count (argMinUpTo (extendCount count) (n - 1)) =
      count (leastArgMin h count) := extendCount_val count (leastArgMin h count)
  omega

/-- A maximiser of counts that add up to `total` has count at least `total / n`
(in the multiplied-out form). -/
theorem leastArgMax_mass {n : Nat} (h : 0 < n) (count : Fin n → Nat) :
    (∑ i, count i) ≤ n * count (leastArgMax h count) := by
  calc (∑ i, count i) ≤ ∑ _i : Fin n, count (leastArgMax h count) :=
        Finset.sum_le_sum (fun i _ => leastArgMax_max h count i)
    _ = n * count (leastArgMax h count) := by simp

end OAI.UniqueGamesTheorem.Foundations.PCP.Decode
