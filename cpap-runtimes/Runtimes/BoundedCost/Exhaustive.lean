module

public import Runtimes.BoundedCost.Solver
import Mathlib.Tactic

/-!
# A verified exhaustive Almost 2-SAT decision procedure

This executable decision procedure tests clause-occurrence sublists with the verified
ordinary 2-SAT solver. Its correctness is unconditional. It does not implement the cited
fixed-parameter algorithm and gives no proof of the `FPTBound` RAM running time.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

/-- The retained formula still has two literals per clause and the same variable bound. -/
theorem exhaustiveTwoCNF_sublist {n : ℕ} {f sub : CNF} (hf : TwoSat.IsTwoCNF n f)
    (hsub : sub.Sublist f) : TwoSat.IsTwoCNF n sub :=
  fun c hc => hf c (hsub.subset hc)

/-- Test every retained clause-occurrence sublist within the deletion budget. -/
def almostTwoSatExhaustive (n : ℕ) (f : CNF) (Ψ : ℕ) : Bool :=
  f.sublists.any fun sub =>
    decide (f.length ≤ sub.length + Ψ) && TwoSat.okB n (TwoSat.codes sub)

/-- The exhaustive procedure accepts exactly the Almost 2-SAT instances with the given
budget; its ordinary 2-SAT subroutine is already proved correct. -/
theorem almostTwoSatExhaustive_correct {n : ℕ} {f : CNF}
    (hf : TwoSat.IsTwoCNF n f) (Ψ : ℕ) :
    almostTwoSatExhaustive n f Ψ = true ↔ AlmostSatisfiable f Ψ := by
  simp only [almostTwoSatExhaustive, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, List.mem_sublists]
  constructor
  · rintro ⟨sub, hsub, hbudget, hs⟩
    exact ⟨sub, hsub, hbudget, (TwoSat.twoSat_correct (exhaustiveTwoCNF_sublist hf hsub)).1.mp hs⟩
  · rintro ⟨sub, hsub, hbudget, hs⟩
    exact ⟨sub, hsub, hbudget, (TwoSat.twoSat_correct (exhaustiveTwoCNF_sublist hf hsub)).1.mpr hs⟩

end STACS2027.Runtimes.BoundedCost
