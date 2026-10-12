module
public import NPHardness.PlanarSourcePackedRingCorrect
public import NPHardness.PlanarSourcePackedReduction
import Lean.Elab.Tactic.Omega
@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Emit

/-- The actual polynomial two-stage constructor emits the incidence-ordered
ring expansion of the registered grid output, on every binary input. -/
theorem output_ringFormula (P : ClauseProgram 1) (w : SAT.Word) :
    output P w = Formula.ringFormula (gridOut P w)
      (incidenceNext (gridOut P w)) (Formula.sourceSigns (gridOut P w)) := by
  rw [output_eq,Layout.program_ringFormula]
  · have hs :
        (Layout.source ⟨(at1 (Ax P)).lift,(NumExpr.var (0 : Fin 3)).lift,
          (at1 (Rx P)).lift,(at1 (Wx P)).lift,.var 0⟩) (word1 P w)
          (extend (((P.emit w (fun _ => w.length)).length+1)/2)
            (extend (P.emit w (fun _ => w.length)).length
              (extend w.length (fun _ => (word1 P w).length)))) = gridOut P w := by
      rw [gridOut_eq]
      simp only [Layout.source,Layout.bits,NumExpr.eval_lift,at1_eval,NumExpr.eval,extend_zero]
      rfl
    rw [hs]
  · simp only [NumExpr.eval_lift,NumExpr.eval,extend_zero]
    omega

end STACS2027.PlanarSource.Packed
