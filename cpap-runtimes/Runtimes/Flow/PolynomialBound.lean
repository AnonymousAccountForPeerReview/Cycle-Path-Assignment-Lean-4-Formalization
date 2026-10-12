module

public import Runtimes.Flow.Solver
public import Runtimes.NamedHoles
import Mathlib.Tactic

/-!
# Polynomial bounds from the cited almost-linear flow contract

The only external algorithmic contract here remains the manuscript's cited almost-linear
minimum-cost-flow result. Taking exponent parameter one yields an ordinary quadratic bound.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

/-- The cited almost-linear bound entails a uniform natural-number quadratic bound,
including the unused input length zero. -/
theorem AlmostLinear.polynomialBound {T : ℕ → ℕ} (hT : AlmostLinear T) :
    ∃ C : ℕ, ∀ N : ℕ, T N ≤ C * (N + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := hT 1 (by norm_num)
  let K : ℕ := ⌈max C 0⌉₊ + T 0 + 1
  refine ⟨K, fun N => ?_⟩
  by_cases hN : N = 0
  · subst N
    simp only [zero_add, one_pow, mul_one]
    dsimp [K]
    omega
  have hNpos : 1 ≤ N := by omega
  have hbound := hC N hNpos
  have hceil : C ≤ (K : ℝ) := by
    have hc : C ≤ max C 0 := le_max_left _ _
    have hmax : max C 0 ≤ (⌈max C 0⌉₊ : ℝ) := Nat.le_ceil _
    have hk : (⌈max C 0⌉₊ : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast (show ⌈max C 0⌉₊ ≤ K by dsimp [K]; omega)
    exact hc.trans (hmax.trans hk)
  have hpow : (N : ℝ) ^ ((1 : ℝ) + 1) = (N : ℝ) ^ 2 := by
    norm_num [Real.rpow_natCast]
  rw [hpow] at hbound
  have hcast : (T N : ℝ) ≤ (K : ℝ) * ((N + 1 : ℕ) : ℝ) ^ 2 := by
    calc
      (T N : ℝ) ≤ C * (N : ℝ) ^ 2 := hbound
      _ ≤ (K : ℝ) * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hceil (sq_nonneg _)
      _ ≤ (K : ℝ) * ((N + 1 : ℕ) : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · norm_cast
          exact Nat.pow_le_pow_left (by omega) _
        · positivity
  exact_mod_cast hcast

/-- Any min-cost-flow program satisfying the sole external cited contract also has an
ordinary polynomial bound; this does not require another external solver assumption. -/
theorem polynomialMinCostFlowSolver_of_almostLinear {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : MinCostFlowSolver F T) (hT : AlmostLinear T) :
    ∃ (C exponent : ℕ), MinCostFlowSolver F T ∧
      ∀ N : ℕ, T N ≤ C * (N + 1) ^ exponent := by
  obtain ⟨C, hC⟩ := hT.polynomialBound
  exact ⟨C, 2, hF, hC⟩


/-- The ordinary polynomial solver obligation follows from the sole cited flow contract. -/
theorem polynomialMinCostFlowSolverExists_of_almostLinear {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : MinCostFlowSolver F T) (hT : AlmostLinear T) :
    PolynomialMinCostFlowSolverExists := by
  obtain ⟨C,e,hF',hbound⟩ := polynomialMinCostFlowSolver_of_almostLinear hF hT
  exact ⟨F,T,C,e,hF',hbound⟩

end STACS2027.Runtimes.Flow
