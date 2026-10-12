module

public import Runtimes.BoundedCost.OptGeometric
import Mathlib.Tactic

/-! A uniform manuscript bound for the cached core, all budget calls, and final
output, including a one-time reading of the original graph. -/

@[expose] public section
namespace STACS2027.Runtimes.BoundedCost.OptSpanRAM

open STACS2027

theorem optimization_total_cost_le_paper (g : Graph) {k : ℕ} (hk : 3 ≤ k)
    (ht : 1 ≤ (cycles g k).length) (C footprint last : ℕ) :
    g.length + 100 * (k * (cycles g k).length + 1) + 6 +
      (∑ p ∈ Finset.range (last + 1),
        ((1150 + footprint) * (span C k (cycles g k).length p + 1) + 1)) + 1 +
      12 * (span C k (cycles g k).length last + 1) ≤
      (108 + (6 * (1151 + footprint) + 12) * (16 * (C + 1) + 1)) * paper5 g k last := by
  let t := (cycles g k).length
  let A := 1150 + footprint
  let B := span C k t last + 1
  let P := paper5 g k last
  have hsum : (∑ p ∈ Finset.range (last + 1), (A * (span C k t p + 1) + 1)) ≤
      6 * (A + 1) * B := by
    have hpoint (p : ℕ) : A * (span C k t p + 1) + 1 ≤
        (A + 1) * (span C k t p + 1) := by nlinarith
    calc
      _ ≤ ∑ p ∈ Finset.range (last + 1), (A + 1) * (span C k t p + 1) :=
        Finset.sum_le_sum (fun p _ => hpoint p)
      _ = (A + 1) * (∑ p ∈ Finset.range (last + 1), (span C k t p + 1)) := by
        rw [Finset.mul_sum]
      _ ≤ (A + 1) * (6 * B) := Nat.mul_le_mul_left _ (span_sum_le hk ht C last)
      _ = _ := by ring
  have hP : 1 ≤ P := by dsimp [P, paper5]; omega
  have hspan : B ≤ (16 * (C + 1) + 1) * P := by
    have h := span_le_paper g hk C last
    dsimp [B, t, P]
    nlinarith
  have hkt : k * t + 1 ≤ P := by
    have hsquare : k ≤ k * k := by nlinarith
    have hmul := Nat.mul_le_mul_right t hsquare
    dsimp [P, paper5, t] at *
    omega
  have hm : g.length ≤ P := by dsimp [P, paper5]; omega
  have hscaled := Nat.mul_le_mul_left (6 * (A + 1) + 12) hspan
  dsimp [A, B, P, t] at *
  nlinarith

end STACS2027.Runtimes.BoundedCost.OptSpanRAM
