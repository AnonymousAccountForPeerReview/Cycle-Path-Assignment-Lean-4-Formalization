module

public import NPHardness.Gadgets
public import NPHardness.ClauseThree5

/-! Figure 4(c) at k = 6, with the red edge subdivided once (Appendix C, Step 3). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

@[expose] public section
namespace STACS2027

def clauseTwoCycles6 : List Cycle :=
  [[0, 1, 25, 2, 14, 13], [0, 13, 14, 11, 12, 24], [2, 14, 11, 10, 3, 26], [3, 4, 15, 9, 30, 10], [4, 5, 27, 6, 16, 15], [6, 7, 28, 8, 17, 16], [8, 17, 16, 15, 9, 29], [10, 11, 20, 19, 31, 18], [19, 20, 21, 32, 23, 22], [19, 20, 23, 32, 21, 22]]

theorem clauseTwo6_enumeration : cycles (clauseTwoGraph 6) 6 = clauseTwoCycles6 := by decide

theorem clauseTwo6_cycles_valid :
    ∀ c ∈ clauseTwoCycles6, IsCycle (clauseTwoGraph 6) 6 c := by decide

theorem clauseTwo6_distinct :
    clauseTwoCycles6.Pairwise (fun c d => ¬ SameCycle c d) := by decide

theorem clauseTwo6_no_zero :
    searchBudget (clauseTwoCycles6.map selectedOptions) [] 0 = false := by decide

theorem clauseTwo6_cost_positive (ps : List (List Edge))
    (h : ValidChoices (clauseTwoCycles6.map selectedOptions) ps) :
    1 ≤ cost ps := by
  have := searchBudget_excludes_cost _ ps 0 clauseTwo6_no_zero h
  omega

theorem clauseTwo6_blocked_search :
    searchBudget (clauseTwoCycles6.map selectedOptions) [[(0,1)], [(4,5)]] 1 = false := by decide

theorem clauseTwo6_blocked_lower (ps : List (List Edge))
    (h : ValidChoices (clauseTwoCycles6.map selectedOptions) ps) :
    2 ≤ cost (ps.reverse ++ [[(0,1)], [(4,5)]]) := by
  have := searchBudget_excludes _ _ ps 1 clauseTwo6_blocked_search h
  omega

def clauseTwoWitness6 (port : Bool) : List Nat :=
  if port then [0, 2, 3, 1, 3, 4, 3, 2, 0, 3] else [3, 1, 2, 0, 0, 4, 3, 2, 0, 3]

theorem clauseTwo6_witness_valid : ∀ p : Bool,
    ValidChoices (clauseTwoCycles6.map selectedOptions)
      (choosePaths clauseTwoCycles6 (clauseTwoWitness6 p)) := by decide

theorem clauseTwo6_witness_cost : ∀ p : Bool,
    cost (choosePaths clauseTwoCycles6 (clauseTwoWitness6 p)) = 1 := by decide

end STACS2027
