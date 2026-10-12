module

public import Runtimes.BoundedCost.OptimalBudgetSum
public import Runtimes.BoundedCost.OptSpanBounds
public import Runtimes.BoundedCost.Top
import Mathlib.Tactic

/-! The cached cycle core makes the budget loop geometric. The original graph
is read once; its edge count is retained in the manuscript's final bound. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptSpanRAM

open STACS2027

theorem Q_sum_le {k t : ℕ} (hk : 3 ≤ k) (ht : 1 ≤ t) (last : ℕ) :
    (∑ p ∈ Finset.range (last + 1), (Q k t p + 1)) ≤ 3 * (Q k t last + 1) := by
  simpa only [Q, z, optimalBudgetCost] using optimalBudgetCost_sum_le hk ht last

theorem span_sum_le {k t : ℕ} (hk : 3 ≤ k) (ht : 1 ≤ t) (C last : ℕ) :
    (∑ p ∈ Finset.range (last + 1), (span C k t p + 1)) ≤
      6 * (span C k t last + 1) := by
  let scale := 8 * (C + 1)
  have hscale : 1 ≤ scale := by dsimp [scale]; omega
  have hpoint (p : ℕ) : span C k t p + 1 ≤ scale * (Q k t p + 1) := by
    dsimp [span, scale]
    nlinarith
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ Finset.range (last + 1)) => hpoint p)
  have hweight := Nat.mul_le_mul_left scale (Q_sum_le hk ht last)
  have hpositive := Q_positive k t last
  calc
    _ ≤ ∑ p ∈ Finset.range (last + 1), scale * (Q k t p + 1) := hsum
    _ = scale * (∑ p ∈ Finset.range (last + 1), (Q k t p + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ scale * (3 * (Q k t last + 1)) := hweight
    _ ≤ 6 * (span C k t last + 1) := by dsimp [span, scale]; nlinarith

theorem Q_le_twice_paper (g : Graph) {k : ℕ} (hk : 3 ≤ k) (p : ℕ) :
    Q k (cycles g k).length p ≤ 2 * paper5 g k p := by
  have hkt : k * (cycles g k).length ≤ k * k * (cycles g k).length := by
    have hkk : k ≤ k * k := by nlinarith
    exact Nat.mul_le_mul_right _ hkk
  unfold Q z paper5
  omega

theorem original_m_add_Q_le_twice_paper (g : Graph) {k : ℕ} (hk : 3 ≤ k) (p : ℕ) :
    g.length + Q k (cycles g k).length p + 1 ≤ 2 * paper5 g k p := by
  have hkt : k * (cycles g k).length ≤ k * k * (cycles g k).length := by
    have hkk : k ≤ k * k := by nlinarith
    exact Nat.mul_le_mul_right _ hkk
  unfold Q z paper5
  omega

theorem span_le_paper (g : Graph) {k : ℕ} (hk : 3 ≤ k) (C p : ℕ) :
    span C k (cycles g k).length p ≤ 16 * (C + 1) * paper5 g k p := by
  have h := Nat.mul_le_mul_left (8 * (C + 1)) (Q_le_twice_paper g hk p)
  dsimp only [span]
  convert h using 1
  ring

end STACS2027.Runtimes.BoundedCost.OptSpanRAM
