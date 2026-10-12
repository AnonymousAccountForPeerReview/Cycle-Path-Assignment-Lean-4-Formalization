module
public import NPHardness.PlanarSourceGraphCopyPhase
public import NPHardness.PlanarSourceGraphRingPhase

/-! Exact assembly of all concrete target-program phases. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter

theorem Layout.graphProgram_emit {n : Nat} (d : Layout n) (k : Nat)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1) :
    (d.graphProgram k).emit w env =
      Formula.ringGraphRecords (sourceEndpointChoices (Formula.sourceSigns (d.source w env)))
        k (d.source w env) (incidenceNext (d.source w env)) (Formula.sourceSigns (d.source w env)) := by
  have hV := d.occurrenceCount_eval w env hq
  have hN : d.formulaLength.eval env=(d.source w env).length :=
    d.formulaLength_eval env (d.bits w env) hq
  have hr :
      expandCopyRecords (d.sourceRingRecords k w env) (copiesAt 0 (d.source w env))=
        orientedClauseRecordsAt (sourceEndpointChoices (Formula.sourceSigns (d.source w env)))
          k (d.source w env).flatten.length (d.source w env).length
          (Formula.ringPlaced (d.source w env).flatten.length (incidenceNext (d.source w env))
            (Formula.sourceSigns (d.source w env))) := by
    change expandCopyRecords (fun i => ringRecords (Formula.sourceSigns (d.source w env))
      k (d.occurrenceCount.eval env) (d.formulaLength.eval env+i) (ringEdge (d.source w env) i)) _=_
    simp only [ringRecords,ringEdge,List.map_cons,List.map_nil,hV,hN]
    exact ringGraphRecords_expandCopies _ _ _ _ _ _ _
  rw [Layout.graphProgram,ClauseProgram.emit_seq,ClauseProgram.emit_seq,
    ascendingVariableGraphProgram_emit,Layout.graphPhase_copies d k w env hq,
    Layout.graphPhase_rings d k w env hq,gridPhase_copies d w env hq]
  change _ ++ _ ++ expandCopyRecords (d.sourceRingRecords k w env) (copiesAt 0 (d.source w env))=_
  rw [hr,hV]
  simp only [Formula.ringGraphRecords,copyGraphAt,copiesAt_zero,Formula.copyPlaced]

end STACS2027.PlanarSource.Packed
