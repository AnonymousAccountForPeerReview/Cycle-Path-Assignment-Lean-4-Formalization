module

public import NPHardness.CPAP
public import NPHardness.Gadgets
public import NPHardness.ClauseThree5
public import NPHardness.LoadCost
public import NPHardness.ClauseTwo5
public import NPHardness.ClauseTwo6

/-! Local gadget optima. These are not the global reduction or NP-hardness theorem. -/

set_option maxRecDepth 100000

@[expose] public section
namespace STACS2027

theorem clauseThreeGraph5_eq : clauseThreeGraph 5 = clauseThree5 := by decide

theorem clauseThree5_assignment_one : HasAssignment (clauseThreeGraph 5) 5 1 := by
  refine ⟨choosePaths clauseThreeCycles5 (clauseThreeWitness5 0), ?_, ?_⟩
  · rw [clauseThreeGraph5_eq, clauseThree5_enumeration]
    exact clauseThree5_witness_valid 0
  · rw [clauseThree5_witness_cost 0]; exact Nat.le_refl 1

theorem clauseThree5_no_assignment_zero : ¬ HasAssignment (clauseThreeGraph 5) 5 0 := by
  rintro ⟨ps, hv, hc⟩
  rw [clauseThreeGraph5_eq, clauseThree5_enumeration] at hv
  have := clauseThree5_cost_positive ps hv
  omega

theorem clauseTwo5_assignment_one : HasAssignment (clauseTwoGraph 5) 5 1 := by
  refine ⟨choosePaths clauseTwoCycles5 (clauseTwoWitness5 false), ?_, ?_⟩
  · rw [clauseTwo5_enumeration]
    exact clauseTwo5_witness_valid false
  · rw [clauseTwo5_witness_cost false]; exact Nat.le_refl 1

theorem clauseTwo5_no_assignment_zero : ¬ HasAssignment (clauseTwoGraph 5) 5 0 := by
  rintro ⟨ps, hv, hc⟩
  rw [clauseTwo5_enumeration] at hv
  have := clauseTwo5_cost_positive ps hv
  omega

theorem clauseTwo6_assignment_one : HasAssignment (clauseTwoGraph 6) 6 1 := by
  refine ⟨choosePaths clauseTwoCycles6 (clauseTwoWitness6 false), ?_, ?_⟩
  · rw [clauseTwo6_enumeration]
    exact clauseTwo6_witness_valid false
  · rw [clauseTwo6_witness_cost false]; exact Nat.le_refl 1

theorem clauseTwo6_no_assignment_zero : ¬ HasAssignment (clauseTwoGraph 6) 6 0 := by
  rintro ⟨ps, hv, hc⟩
  rw [clauseTwo6_enumeration] at hv
  have := clauseTwo6_cost_positive ps hv
  omega

end STACS2027
