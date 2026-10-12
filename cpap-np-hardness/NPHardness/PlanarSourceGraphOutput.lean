module
public import NPHardness.PlanarSourceGraphReduction
public import NPHardness.PlanarSourceGraphGrid
public import NPHardness.PlanarSourceGraphProgramCorrect

/-! Exact semantics of the complete target constructor on binary inputs.
The graph, original clause budget, and satisfiability equivalence are proved
for the concrete machine-compiled output. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Emit

/-- The actual target program emits precisely the source-ring graph records. -/
theorem graphOutput_ringGraphRecords (k : Nat) (P : ClauseProgram 1) (w : SAT.Word) :
    graphOutput k P w =
      Formula.ringGraphRecords (sourceEndpointChoices (Formula.sourceSigns (gridOut P w)))
        k (gridOut P w) (incidenceNext (gridOut P w)) (Formula.sourceSigns (gridOut P w)) := by
  rw [graphOutput_eq,Layout.graphProgram_emit]
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

/-- Exact decoded graph, valid instruction encoding, and exact budget. -/
theorem graphOutput_spec (k : Nat) (P : ClauseProgram 1) (w : SAT.Word) :
    GraphOutput (graphOutput k P w)
      (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns (gridOut P w))) k (output P w))
      (output P w).length := by
  rw [graphOutput_ringGraphRecords,output_ringFormula,gridOut_eq]
  exact ringGrid_records_output _ _ _ _

/-- Assignment feasibility of the actual decoded output is equivalent to
satisfiability of the original emitter formula. -/
theorem graphOutput_assignment_iff (k : Nat) (hk : 5≤k) (P : ClauseProgram 1) (w : SAT.Word) :
    HasAssignment (instructionGraph (graphOutput k P w)) k (instructionBudget (graphOutput k P w)) ↔
      Satisfiable (P.emit w (fun _ => w.length)) := by
  have hg := graphOutput_spec k P w
  rw [hg.2.1,hg.2.2]
  exact (orientedFormulaGraph_sat_iff_assignment _ hk (output_correct P w).1
    (output_distinct P w)).symm.trans (output_correct P w).2.2

end STACS2027.PlanarSource.Packed
