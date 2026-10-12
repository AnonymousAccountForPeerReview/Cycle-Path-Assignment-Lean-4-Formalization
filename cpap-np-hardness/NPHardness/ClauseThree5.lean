module

public import NPHardness.Enumerate
public import NPHardness.CostSearch

/-!
Figure 4(b) at k = 5: the edge set of Appendix C, Step 2, with vertices shifted by one.
Figure positions of the vertices are listed in docs/gadget-map.md.
All finite certificates use kernel reduction (`decide`), not `native_decide`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

def clauseThree5 : Graph :=
  [(0, 1), (0, 12), (0, 13), (1, 2), (2, 3), (2, 14),
   (3, 4), (3, 10), (4, 5), (4, 15), (5, 6), (6, 7),
   (6, 16), (7, 8), (8, 9), (8, 17), (9, 10), (9, 15),
   (10, 11), (11, 12), (11, 14), (13, 14), (15, 16), (16, 17)]

def clauseThreeCycles5 : List Cycle :=
  [[0, 1, 2, 14, 13], [0, 12, 11, 14, 13], [2, 3, 10, 11, 14],
   [3, 4, 15, 9, 10], [4, 5, 6, 16, 15], [6, 7, 8, 17, 16],
   [8, 9, 15, 16, 17]]

def clauseThreePorts5 : List Edge := [(0, 1), (4, 5), (10, 11)]

theorem clauseThree5_enumeration : cycles clauseThree5 5 = clauseThreeCycles5 := by
  decide

theorem clauseThree5_distinct :
    clauseThreeCycles5.Pairwise (fun c d => ¬ SameCycle c d) := by decide

theorem clauseThree5_cycles_valid :
    ∀ c ∈ clauseThreeCycles5, IsCycle clauseThree5 5 c := by decide

theorem clauseThree5_no_zero :
    searchBudget (clauseThreeCycles5.map selectedOptions) [] 0 = false := by decide

theorem clauseThree5_cost_positive (ps : List (List Edge))
    (h : ValidChoices (clauseThreeCycles5.map selectedOptions) ps) :
    1 ≤ cost ps := by
  have := searchBudget_excludes_cost _ ps 0 clauseThree5_no_zero h
  omega

theorem clauseThree5_blocked_search :
    searchBudget (clauseThreeCycles5.map selectedOptions)
      (clauseThreePorts5.map fun e => [e]) 1 = false := by decide

theorem clauseThree5_blocked_lower (ps : List (List Edge))
    (h : ValidChoices (clauseThreeCycles5.map selectedOptions) ps) :
    2 ≤ cost (ps.reverse ++ clauseThreePorts5.map (fun e => [e])) := by
  have := searchBudget_excludes _ _ ps 1 clauseThree5_blocked_search h
  omega

def clauseThreeWitness5 (port : Fin 3) : List Nat :=
  match port.val with
  | 0 => [2, 4, 3, 0, 0, 3, 2]
  | 1 => [0, 3, 2, 1, 2, 3, 2]
  | _ => [0, 3, 0, 0, 0, 3, 2]

def choosePaths (cs : List Cycle) (cuts : List Nat) : List (List Edge) :=
  (cs.zip cuts).map fun ci => selected ci.1 ci.2

theorem clauseThree5_witness_valid : ∀ p : Fin 3,
    ValidChoices (clauseThreeCycles5.map selectedOptions)
      (choosePaths clauseThreeCycles5 (clauseThreeWitness5 p)) := by decide

theorem clauseThree5_witness_cost : ∀ p : Fin 3,
    cost (choosePaths clauseThreeCycles5 (clauseThreeWitness5 p)) = 1 := by decide

end STACS2027
