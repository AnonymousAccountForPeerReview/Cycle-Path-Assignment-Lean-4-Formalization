module

public import NPHardness.PlanarSourcePackedCorrect
public import NPHardness.PlanarSourceClean

/-! The actual polynomial source output has distinct variables within every
clause. The registered grid has at least two occurrences of each used variable,
so its occurrence rings have no singleton or tautological implication. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.Planar Grid

theorem ringGrid_distinct (W m : Nat) (bits : Nat → Nat → Bool×Bool) :
    ClauseVariablesDistinct (Formula.ringFormula (gridCNF W m bits)
      (incidenceNext (gridCNF W m bits)) (Formula.sourceSigns (gridCNF W m bits))) := by
  cases m with
  | zero =>
    rw [gridCNF_zero,ringFormula_nil]
    intro c hc
    cases hc
  | succ m =>
    let G := ComputableComb.gridIncidenceEmbedding W (m+1) bits (by omega)
    apply Formula.grid_ringFormula_distinct W (m+1) bits
      (ComputableFormula.formulaData _ G).rotation.varRot
    · intro i
      exact (incidenceNext_grid W (m+1) bits (by omega) i).trans (Formula.nextIndex_at _ i)
    · exact ComputableFormula.formulaData_variable_orbit _ G

theorem output_distinct (P : Complexity.StackTableauEmitter.ClauseProgram 1)
    (w : SAT.Word) : ClauseVariablesDistinct (output P w) := by
  rw [output_ringFormula,Emit.gridOut_eq]
  exact ringGrid_distinct _ _ _

end STACS2027.PlanarSource.Packed
