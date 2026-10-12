module

public import NPHardness.SourceWordConstruction
public import NPHardness.PlanarSourceGraphPlanarity

/-! Variable bounds for the grid occurrence-ring inputs of the word machine. -/

@[expose] public section
namespace STACS2027.SourceWord
open Complexity Complexity.SAT Complexity.Planar Grid WordPipeline PlanarSource

/-- The arithmetic grid successor names an actual source occurrence. -/
theorem grid_next_bounded (W m : Nat) (bits : Nat→Nat→Bool×Bool) :
    ∀i,i<(gridCNF W m bits).flatten.length→
      Packed.incidenceNext (gridCNF W m bits) i<(gridCNF W m bits).flatten.length := by
  obtain ⟨rot,hn⟩ := Packed.incidenceNext_grid_permutation W m bits
  intro i hi
  rw [hn ⟨i,hi⟩]
  exact (rot.toFun ⟨i,hi⟩).isLt

@[simp] theorem ringGrid_input_variableBound (W m : Nat) (bits : Nat→Nat→Bool×Bool) :
    variableBound (Formula.ringFormula (gridCNF W m bits)
      (Packed.incidenceNext (gridCNF W m bits)) (Formula.sourceSigns (gridCNF W m bits)))=
        (gridCNF W m bits).flatten.length :=
  Formula.ringFormula_variableBound_of_bounded _ _ _ (grid_next_bounded W m bits)

end STACS2027.SourceWord
