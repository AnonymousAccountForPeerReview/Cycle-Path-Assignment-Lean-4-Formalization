module

public import Runtimes.BoundedCost.SearchBound
import Mathlib.Tactic

/-! The bounded-cost budget search has a uniform last-call bound for its full
geometric and graph-preparation cost, including the budget-zero call. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

def optimalBudgetCost (k cycles budget : ℕ) : ℕ :=
  15 ^ budget * budget * ((budget + 1) * k * k * cycles + k * cycles * cycles) ^ 3 +
    k * k * cycles + k * cycles * cycles + k * cycles + 1

theorem optimalBudgetCost_sum_le {k cycles : ℕ} (hk : 3 ≤ k) (ht : 1 ≤ cycles) (last : ℕ) :
    (∑ budget ∈ Finset.range (last + 1), (optimalBudgetCost k cycles budget + 1)) ≤
      3 * (optimalBudgetCost k cycles last + 1) := by
  let A : ℕ → ℕ := fun budget => (budget + 1) * k * k * cycles + k * cycles * cycles
  let B := k * k * cycles + k * cycles * cycles + k * cycles + 2
  let H := 15 ^ last * last * (A last) ^ 3
  have hw : Monotone (fun budget => budget * (A budget) ^ 3) := by
    intro i j hij
    apply Nat.mul_le_mul hij
    apply Nat.pow_le_pow_left
    dsimp [A]
    have hmul := Nat.mul_le_mul_right (k * k * cycles) (show i + 1 ≤ j + 1 by omega)
    simpa only [Nat.mul_assoc] using Nat.add_le_add_right hmul (k * cycles * cycles)
  have hweight : (∑ budget ∈ Finset.range (last + 1), 15 ^ budget * (budget * (A budget) ^ 3)) ≤
      2 * H := by
    simpa only [H, Nat.mul_assoc] using sum_geometric_weight_le _ hw last
  have hsum : (∑ budget ∈ Finset.range (last + 1), (optimalBudgetCost k cycles budget + 1)) =
      (∑ budget ∈ Finset.range (last + 1), 15 ^ budget * (budget * (A budget) ^ 3)) +
        (last + 1) * B := by
    calc
      _ = ∑ budget ∈ Finset.range (last + 1),
          (15 ^ budget * (budget * (A budget) ^ 3) + B) := by
        apply Finset.sum_congr rfl
        intro budget hb
        dsimp [optimalBudgetCost, A, B]
        ring
      _ = _ := by simp [Finset.sum_add_distrib]
  by_cases hzero : last = 0
  · subst last
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    omega
  have hlast : 1 ≤ last := by omega
  have hsquare : k + 2 ≤ k * k := by nlinarith
  have hlinear : k * cycles + 2 ≤ k * k * cycles := by
    have hmul := Nat.mul_le_mul_right cycles hsquare
    nlinarith
  have hscale : 2 * (k * k * cycles) ≤ (last + 1) * (k * k * cycles) :=
    Nat.mul_le_mul_right _ (by omega)
  have hBA : B ≤ A last := by dsimp [A, B]; nlinarith
  have hpositive : 1 ≤ A last := by dsimp [B] at hBA; omega
  have hpower : A last ≤ (A last) ^ 3 := le_self_pow hpositive (by decide)
  have hBpower : B ≤ (A last) ^ 3 := hBA.trans hpower
  have hbase : last * B ≤ H := by
    have hfirst := Nat.mul_le_mul_left last hBpower
    have hsecond : last * (A last) ^ 3 ≤ 15 ^ last * (last * (A last) ^ 3) :=
      Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by decide))
    simpa only [H, Nat.mul_assoc] using hfirst.trans hsecond
  rw [hsum]
  calc
    _ ≤ 2 * H + (H + B) := Nat.add_le_add hweight (by nlinarith)
    _ = 3 * H + B := by ring
    _ ≤ 3 * (optimalBudgetCost k cycles last + 1) := by
      dsimp [H, A, B, optimalBudgetCost]
      nlinarith

end STACS2027.Runtimes.BoundedCost
