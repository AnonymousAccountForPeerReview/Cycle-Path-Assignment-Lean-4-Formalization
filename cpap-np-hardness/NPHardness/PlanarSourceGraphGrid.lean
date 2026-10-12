module
public import NPHardness.PlanarSourceGraphSerialization
public import NPHardness.PlanarSourceEndpointChoices
public import NPHardness.PlanarSourcePackedClean
@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.Planar Grid STACS2027.PlanarGluing

@[simp] theorem orientedFormulaGraph_nil (flips : EndpointChoices) (k : Nat) :
    orientedFormulaGraph flips k []=[] := by
  simp [orientedFormulaGraph,Oriented.formulaGraph,variableBound,placeFormula]

theorem ringGrid_graph_planar_empty (k W : Nat) (bits : Nat → Nat → Bool×Bool) :
    let f := gridCNF W 0 bits
    PlanarGraph (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k
      (Formula.ringFormula f (incidenceNext f) (Formula.sourceSigns f))) := by
  dsimp only
  rw [gridCNF_zero,ringFormula_nil,orientedFormulaGraph_nil]
  exact planarGraph_nil

/-- The arithmetic successor is a permutation of exactly the actual source
occurrences; the empty grid is included. This statement is used only in graph
correctness proofs, never as an oracle for the compiled constructor. -/
theorem incidenceNext_grid_permutation (W m : Nat) (bits : Nat → Nat → Bool×Bool) :
    ∃ rot : DartEquiv (gridCNF W m bits).flatten.length (gridCNF W m bits).flatten.length,
      ∀ i : Fin (gridCNF W m bits).flatten.length,
        incidenceNext (gridCNF W m bits) i.val=(rot.toFun i).val := by
  cases m with
  | zero =>
    rw [gridCNF_zero]
    refine ⟨DartEquiv.refl _,?_⟩
    intro i
    exact Fin.elim0 i
  | succ m =>
    let B := (ComputableFormula.formulaData (gridCNF W (m+1) bits)
      (ComputableComb.gridIncidenceEmbedding W (m+1) bits (by omega))).rotation
    refine ⟨B.varRot,?_⟩
    intro i
    exact (incidenceNext_grid W (m+1) bits (by omega) i).trans (Formula.nextIndex_at B i)

/-- Exact decoded graph and budget for the source ring serialization. -/
theorem ringGrid_records_output (k W m : Nat) (bits : Nat → Nat → Bool×Bool) :
    let f := gridCNF W m bits
    let flips := sourceEndpointChoices (Formula.sourceSigns f)
    let g := Formula.ringFormula f (incidenceNext f) (Formula.sourceSigns f)
    GraphOutput (Formula.ringGraphRecords flips k f (incidenceNext f) (Formula.sourceSigns f))
      (orientedFormulaGraph flips k g) g.length := by
  dsimp only
  obtain ⟨rot,hn⟩ := incidenceNext_grid_permutation W m bits
  rw [Formula.ringFormula_length]
  exact Formula.ringGraphRecords_output _ k _ rot _ _ hn

end STACS2027.PlanarSource.Packed
