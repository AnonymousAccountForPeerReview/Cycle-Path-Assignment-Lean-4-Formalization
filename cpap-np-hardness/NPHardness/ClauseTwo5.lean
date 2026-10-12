module

public import NPHardness.Gadgets
public import NPHardness.ClauseThree5

/-! Figure 4(c) at k = 5 (Appendix C, Step 3). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

@[expose] public section
namespace STACS2027

def clauseTwoCycles5 : List Cycle :=
  [[0, 1, 2, 14, 13], [0, 12, 11, 14, 13], [2, 3, 10, 11, 14], [3, 4, 15, 9, 10], [4, 5, 6, 16, 15], [6, 7, 8, 17, 16], [8, 9, 15, 16, 17], [10, 11, 20, 19, 18], [19, 20, 21, 23, 22], [19, 20, 23, 21, 22]]

theorem clauseTwo5_enumeration : cycles (clauseTwoGraph 5) 5 = clauseTwoCycles5 := by decide

theorem clauseTwo5_cycles_valid :
    ∀ c ∈ clauseTwoCycles5, IsCycle (clauseTwoGraph 5) 5 c := by decide

theorem clauseTwo5_distinct :
    clauseTwoCycles5.Pairwise (fun c d => ¬ SameCycle c d) := by decide

theorem clauseTwo5_no_zero :
    searchBudget (clauseTwoCycles5.map selectedOptions) [] 0 = false := by decide

theorem clauseTwo5_cost_positive (ps : List (List Edge))
    (h : ValidChoices (clauseTwoCycles5.map selectedOptions) ps) :
    1 ≤ cost ps := by
  have := searchBudget_excludes_cost _ ps 0 clauseTwo5_no_zero h
  omega

theorem clauseTwo5_blocked_search :
    searchBudget (clauseTwoCycles5.map selectedOptions) [[(0,1)], [(4,5)]] 1 = false := by decide

theorem clauseTwo5_blocked_lower (ps : List (List Edge))
    (h : ValidChoices (clauseTwoCycles5.map selectedOptions) ps) :
    2 ≤ cost (ps.reverse ++ [[(0,1)], [(4,5)]]) := by
  have := searchBudget_excludes _ _ ps 1 clauseTwo5_blocked_search h
  omega

def clauseTwoWitness5 (port : Bool) : List Nat :=
  if port then [0, 3, 2, 1, 2, 3, 2, 2, 0, 2] else [2, 4, 3, 0, 0, 3, 2, 2, 0, 2]

theorem clauseTwo5_witness_valid : ∀ p : Bool,
    ValidChoices (clauseTwoCycles5.map selectedOptions)
      (choosePaths clauseTwoCycles5 (clauseTwoWitness5 p)) := by decide

theorem clauseTwo5_witness_cost : ∀ p : Bool,
    cost (choosePaths clauseTwoCycles5 (clauseTwoWitness5 p)) = 1 := by decide

end STACS2027
