module
public import NPHardness.PlanarSourceFormulaSemantics
public import Complexity.Planar.GridTarget
@[expose] public section
namespace STACS2027.PlanarSource
open Complexity Complexity.SAT Complexity.Planar Grid

theorem gridCNF_zero (W : Nat) (bits : Nat → Nat → Bool×Bool) : gridCNF W 0 bits=[] := by
  simp [gridCNF]

theorem ringFormula_nil (next : Nat → Nat) (signs : Nat → Bool) :
    Formula.ringFormula [] next signs=[] := rfl

theorem empty_source_properties : BoundedOccurrence ([] : CNF) ∧
    PlanarGraph (incidenceGraph ([] : CNF)) ∧ Satisfiable ([] : CNF) := by
  refine ⟨?_,planarGraph_nil,⟨fun _ => false,rfl⟩⟩
  simp [BoundedOccurrence,occurrences]

end STACS2027.PlanarSource
