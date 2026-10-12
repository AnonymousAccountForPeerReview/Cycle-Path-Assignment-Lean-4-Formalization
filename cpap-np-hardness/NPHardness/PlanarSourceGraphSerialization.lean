module

public import NPHardness.OrientedGraphSerialization
public import NPHardness.PlanarSourceDimensions

/-! The graph-and-budget records for the actual occurrence-ring source.
Dense tags are the real copied-clause indices followed by implication indices;
each allocated literal keeps its individually verified occurrence rank. -/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar STACS2027.PlanarGluing

def copyPlaced (f : CNF) : List (List PlacedLiteral) :=
  (copyFormula f).map (List.map (fun l => PlacedLiteral.mk l 0))

def ringPlaced (E : Nat) (next : Nat→Nat) (signs : Nat→Bool) : List (List PlacedLiteral) :=
  (ringClauses E next signs).map (List.map (fun l => PlacedLiteral.mk l (if l.positive then 0 else 1)))

def ringGraphRecords (flips : EndpointChoices) (k : Nat) (f : CNF)
    (next : Nat→Nat) (signs : Nat→Bool) : CNF :=
  graphRecords ((List.range f.flatten.length).flatMap (placedVariableGraph k)) ++
    orientedClauseRecordsAt flips k f.flatten.length 0 (copyPlaced f) ++
    orientedClauseRecordsAt flips k f.flatten.length f.length (ringPlaced f.flatten.length next signs)

@[simp] theorem copyPlaced_length (f : CNF) : (copyPlaced f).length=f.length := by
  simp only [copyPlaced,List.length_map,copyFormula_length]

theorem ringGraphRecords_eq (flips : EndpointChoices) (k : Nat) (f : CNF)
    (rot : DartEquiv f.flatten.length f.flatten.length) (next : Nat→Nat) (signs : Nat→Bool)
    (hn : ∀ i : Fin f.flatten.length,next i.val=(rot.toFun i).val) :
    ringGraphRecords flips k f next signs =
      orientedFormulaGraphRecords flips k (ringFormula f next signs) := by
  unfold orientedFormulaGraphRecords
  rw [ringFormula_variableBound f rot next signs hn,ringFormula_placement f rot next signs hn]
  change ringGraphRecords flips k f next signs =
    graphRecords ((List.range f.flatten.length).flatMap (placedVariableGraph k)) ++
      orientedClauseRecordsAt flips k f.flatten.length 0 (copyPlaced f ++ ringPlaced f.flatten.length next signs)
  rw [orientedClauseRecordsAt_append,copyPlaced_length,Nat.zero_add]
  exact List.append_assoc _ _ _

/-- Exact emitted graph and exact clause-count budget, not merely a
satisfiability-preserving semantic encoding. -/
theorem ringGraphRecords_output (flips : EndpointChoices) (k : Nat) (f : CNF)
    (rot : DartEquiv f.flatten.length f.flatten.length) (next : Nat→Nat) (signs : Nat→Bool)
    (hn : ∀ i : Fin f.flatten.length,next i.val=(rot.toFun i).val) :
    GraphOutput (ringGraphRecords flips k f next signs)
      (orientedFormulaGraph flips k (ringFormula f next signs)) (f.length+f.flatten.length) := by
  rw [ringGraphRecords_eq flips k f rot next signs hn,←ringFormula_length f next signs]
  exact orientedFormulaGraphRecords_output _ _ _

/-- The dense implication phase is a range of actual two-literal placed
clauses. This is the exact local block expected by the compiled emitter. -/
theorem ringClauseRecordsAt_explicit (flips : EndpointChoices) (k n base E : Nat)
    (next : Nat→Nat) (signs : Nat→Bool) :
    orientedClauseRecordsAt flips k n base (ringPlaced E next signs) =
      (List.range E).flatMap (fun i => orientedClauseGraphRecords flips k n (base+i)
        [⟨⟨i,signs i⟩,if signs i then 0 else 1⟩,
         ⟨⟨next i,!(signs (next i))⟩,if !(signs (next i)) then 0 else 1⟩]) := by
  simp only [orientedClauseRecordsAt,ringPlaced,ringClauses,List.map_map,
    Grid.zipIdx_map_range,List.flatMap_map,Function.comp_apply,List.map_cons,List.map_nil]

end STACS2027.PlanarSource.Formula
