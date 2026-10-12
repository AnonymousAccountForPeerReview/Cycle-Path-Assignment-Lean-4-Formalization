module

public import Runtimes.BoundedCost.Solver
import Mathlib.Tactic

/-!
# Geometric accumulation of bounded-cost solver calls

The manuscript computes `OPT` by testing budgets `0, 1, 2, …` until success.
The correctness and termination of that search are proved by `searchOptimum_correct`.
This module proves its additional arithmetic claim: the sum of the Almost 2-SAT
call bounds is at most twice the final geometric bound when input lengths grow
monotonically. For `Γ'` their lengths are `2|Γ'| + 2`, which is monotone in the budget.

`FPTBound T` remains an explicit hypothesis. These theorems prove no existence of
an FPT solver, no RAM search-loop program, and no caching of the graph or clauses.
They do not include repeated graph-reading or reconstruction costs.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027

/-- The sum of the powers `15^0, …, 15^B` is at most twice the last power. -/
theorem sum_geometric_powers_le (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), 15 ^ i) ≤ 2 * 15 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- Monotone nonnegative weights preserve the geometric last-call bound. -/
theorem sum_geometric_weight_le (w : ℕ → ℕ) (hw : Monotone w) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), 15 ^ i * w i) ≤ 2 * 15 ^ n * w n := by
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), 15 ^ i * w n := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (hw (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = (∑ i ∈ Finset.range (n + 1), 15 ^ i) * w n := by rw [Finset.sum_mul]
    _ ≤ 2 * 15 ^ n * w n := Nat.mul_le_mul_right _ (sum_geometric_powers_le n)

/-- Summing the pointwise FPT bound over budgets `0, …, B`, with monotone input lengths. -/
theorem fptBound_sum_of_constant {T : ℕ → ℕ → ℕ} {Cf : ℕ}
    (hT : ∀ Ψ N : ℕ, T Ψ N ≤ Cf * 15 ^ Ψ * (Ψ + 1) * (N + 1) ^ 3)
    (N : ℕ → ℕ) (hN : Monotone N) (B : ℕ) :
    (∑ Ψ ∈ Finset.range (B + 1), T Ψ (N Ψ)) ≤
      2 * Cf * 15 ^ B * (B + 1) * (N B + 1) ^ 3 := by
  have hw : Monotone (fun Ψ => (Ψ + 1) * (N Ψ + 1) ^ 3) := by
    intro i j hij
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by have := hN hij; omega) 3)
  calc
    _ ≤ ∑ Ψ ∈ Finset.range (B + 1), Cf * (15 ^ Ψ * ((Ψ + 1) * (N Ψ + 1) ^ 3)) := by
      apply Finset.sum_le_sum
      intro Ψ hΨ
      simpa only [Nat.mul_assoc] using hT Ψ (N Ψ)
    _ = Cf * (∑ Ψ ∈ Finset.range (B + 1), 15 ^ Ψ * ((Ψ + 1) * (N Ψ + 1) ^ 3)) := by
      rw [Finset.mul_sum]
    _ ≤ Cf * (2 * 15 ^ B * ((B + 1) * (N B + 1) ^ 3)) :=
      Nat.mul_le_mul_left _ (sum_geometric_weight_le _ hw B)
    _ = _ := by ring


/-- Under the explicit cited FPT-bound hypothesis, all calls through budget `B`
are within a constant factor of the bound at `B`. -/
theorem fptBound_accumulated {T : ℕ → ℕ → ℕ} (hT : FPTBound T)
    (N : ℕ → ℕ) (hN : Monotone N) :
    ∃ C : ℕ, ∀ B : ℕ, (∑ Ψ ∈ Finset.range (B + 1), T Ψ (N Ψ)) ≤
      2 * C * 15 ^ B * (B + 1) * (N B + 1) ^ 3 := by
  obtain ⟨C, hC⟩ := hT
  exact ⟨C, fun B => fptBound_sum_of_constant hC N hN B⟩

/-- The replicated bounded-cost formula's solver-input length is monotone in the budget. -/
theorem almostFormula_solverInputLength_mono (g : Graph) (k : ℕ) :
    Monotone (fun Ψ => 2 * (almostFormula g k Ψ).length + 2) := by
  intro i j hij
  dsimp only
  rw [almostFormula_length, almostFormula_length]
  have hm := Nat.mul_le_mul_right (pathConstraints g k).length
    (show i + 1 ≤ j + 1 by omega)
  omega

/-- The solver-call costs of the search over budgets `0, …, B` for `Γ'` sum to
at most twice the bound for the final call, under the explicit FPT-bound hypothesis. -/
theorem boundedCost_solverCalls_accumulated {T : ℕ → ℕ → ℕ} (hT : FPTBound T) :
    ∃ C : ℕ, ∀ (g : Graph) (k B : ℕ),
      (∑ Ψ ∈ Finset.range (B + 1), T Ψ (2 * (almostFormula g k Ψ).length + 2)) ≤
        2 * C * 15 ^ B * (B + 1) * (2 * (almostFormula g k B).length + 3) ^ 3 := by
  obtain ⟨C, hC⟩ := hT
  refine ⟨C, fun g k B => ?_⟩
  simpa only [Nat.add_assoc] using
    fptBound_sum_of_constant hC (fun Ψ => 2 * (almostFormula g k Ψ).length + 2)
      (almostFormula_solverInputLength_mono g k) B

end STACS2027.Runtimes.BoundedCost
