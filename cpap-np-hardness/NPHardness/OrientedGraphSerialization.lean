module

public import NPHardness.OrientedGluing
public import NPHardness.GraphEncoding

/-! Exact graph serialization with individual occurrence ranks and endpoint
choices. Every clause gadget contributes one budget tick and its real edges. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- Serialize one actual placed clause, retaining every occurrence's rank. -/
def orientedClauseGraphRecords (flips : EndpointChoices) (k n j : Nat)
    (c : List PlacedLiteral) : CNF :=
  [] :: graphRecords (orientedPlacedClauseGraph flips k n j c)

theorem orientedClauseGraphRecords_output (flips : EndpointChoices) (k n j : Nat)
    (c : List PlacedLiteral) :
    GraphOutput (orientedClauseGraphRecords flips k n j c)
      (orientedPlacedClauseGraph flips k n j c) 1 :=
  GraphOutput.tick.append (graphRecords_output _ (mapGraph_normalized _ _))

/-- Consecutive clause labels starting at an explicit dense base. -/
def orientedClauseRecordsAt (flips : EndpointChoices) (k n base : Nat)
    (cs : List (List PlacedLiteral)) : CNF :=
  (cs.zipIdx base).flatMap (fun p => orientedClauseGraphRecords flips k n p.2 p.1)

def orientedClauseGraphsAt (flips : EndpointChoices) (k n base : Nat)
    (cs : List (List PlacedLiteral)) : Graph :=
  (cs.zipIdx base).flatMap (fun p => orientedPlacedClauseGraph flips k n p.2 p.1)

theorem orientedClauseRecordsAt_output (flips : EndpointChoices) (k n base : Nat)
    (cs : List (List PlacedLiteral)) :
    GraphOutput (orientedClauseRecordsAt flips k n base cs)
      (orientedClauseGraphsAt flips k n base cs) cs.length := by
  have h := GraphOutput.flatMap (cs.zipIdx base)
    (fun p => orientedClauseGraphRecords flips k n p.2 p.1)
    (fun p => orientedPlacedClauseGraph flips k n p.2 p.1) (fun _ => 1)
    (fun p _ => orientedClauseGraphRecords_output flips k n p.2 p.1)
  simpa only [orientedClauseRecordsAt,orientedClauseGraphsAt,sum_map_const,List.length_zipIdx,Nat.mul_one] using h

theorem orientedClauseRecordsAt_append (flips : EndpointChoices) (k n base : Nat)
    (cs ds : List (List PlacedLiteral)) :
    orientedClauseRecordsAt flips k n base (cs++ds) =
      orientedClauseRecordsAt flips k n base cs ++
      orientedClauseRecordsAt flips k n (base+cs.length) ds := by
  simp only [orientedClauseRecordsAt,List.zipIdx_append,List.flatMap_append]

theorem orientedClauseGraphsAt_zero (flips : EndpointChoices) (k n : Nat)
    (cs : List (List PlacedLiteral)) :
    orientedClauseGraphsAt flips k n 0 cs =
      (cs.mapIdx (fun j c => orientedPlacedClauseGraph flips k n j c)).flatten := by
  simp only [orientedClauseGraphsAt,List.mapIdx_eq_zipIdx_map,List.flatMap]

theorem variableGraphRecords_output (k n : Nat) :
    GraphOutput (graphRecords ((List.range n).flatMap (placedVariableGraph k)))
      ((List.range n).flatMap (placedVariableGraph k)) 0 := by
  apply graphRecords_output
  intro e he
  obtain ⟨v,_,he⟩ := List.mem_flatMap.mp he
  exact mapGraph_normalized _ _ e he

def orientedFormulaGraphRecords (flips : EndpointChoices) (k : Nat) (f : CNF) : CNF :=
  graphRecords ((List.range (variableBound f)).flatMap (placedVariableGraph k)) ++
    orientedClauseRecordsAt flips k (variableBound f) 0 (placeFormula [] f)

theorem orientedFormulaGraphRecords_output (flips : EndpointChoices) (k : Nat) (f : CNF) :
    GraphOutput (orientedFormulaGraphRecords flips k f) (orientedFormulaGraph flips k f) f.length := by
  have h := (variableGraphRecords_output k (variableBound f)).append
    (orientedClauseRecordsAt_output flips k (variableBound f) 0 (placeFormula [] f))
  rw [orientedClauseGraphsAt_zero,placeFormula_length,Nat.zero_add] at h
  exact h

end STACS2027
