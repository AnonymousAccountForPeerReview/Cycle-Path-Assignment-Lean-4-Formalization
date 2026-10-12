module

public import Runtimes.BoundedCost.ActualOuterRAM
public import Runtimes.BoundedCost.CompilerBounds
import Mathlib.Tactic

/-! The exact costs of the executed nested scans meet the common compiler
accounting bound, with the same fixed flow-program footprint. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM

theorem actualInnerCost_le (F : Stmt) (constant clauses budget : ℕ) :
    actualInnerCost F (compilerLayout constant clauses budget) (2 * clauses + 1) clauses
      (min budget clauses + 1) ≤
        compilerInnerTime constant (wregs (Flow.hornSeparator F)).length clauses budget := by
  unfold actualInnerCost innerSearchCost innerPathBodyCost compilerInnerTime compilerPathTime
    compilerNodeTime
  dsimp only [compilerLayout]
  ring_nf
  omega

theorem outerCompleteCost_le (F : Stmt) (constant clauses budget special : ℕ) :
    outerCompleteCost F (compilerLayout constant clauses budget) (2 * clauses + 1) clauses
      (min budget clauses + 1) special ≤
        compilerOuterTime constant (wregs (Flow.hornSeparator F)).length clauses budget special := by
  have hi := actualInnerCost_le F constant clauses budget
  have hm := Nat.mul_le_mul_left (3 ^ special) hi
  dsimp only [outerCompleteCost, outerSearchCost, outerBodyCost, compilerOuterTime]
  ring_nf at hm ⊢
  omega

theorem compilerOuterTime_mono_special (constant registers clauses budget : ℕ)
    {s t : ℕ} (hst : s ≤ t) :
    compilerOuterTime constant registers clauses budget s ≤
      compilerOuterTime constant registers clauses budget t := by
  dsimp only [compilerOuterTime]
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 3) hst
  have hi : 12 * (2 * clauses + 1) + 44 * s + 11 +
      compilerInnerTime constant registers clauses budget + 19 * s + 12 ≤
        12 * (2 * clauses + 1) + 44 * t + 11 +
          compilerInnerTime constant registers clauses budget + 19 * t + 12 := by omega
  have hm := Nat.mul_le_mul hp hi
  omega

end STACS2027.Runtimes.BoundedCost
