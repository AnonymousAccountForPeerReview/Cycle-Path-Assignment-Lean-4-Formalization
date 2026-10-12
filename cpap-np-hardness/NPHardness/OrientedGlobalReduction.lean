module

public import NPHardness.GlobalReduction
public import NPHardness.OrientedGlobalCompleteness

/-! Global correctness on the exact Definition 7 domain, with the original
clause count as the target budget. This file asserts no machine runtime or
planarity theorem. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]
open Complexity.SAT

theorem formulaGraph_assignment_budget_lower {k budget : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f)
    (hassign : HasAssignment (formulaGraph k f) k budget) : f.length ≤ budget := by
  obtain ⟨choose,hchoose,hcost⟩ := (formulaGraph_assignment_iff_family hk hf hd budget).mp hassign
  have hsV : ∀ v, v < variableBound f → ∀ p ∈ variableChosen k hk choose v, p ⊆ placedVariableGraph k v := by
    intro v _ p hp
    exact chosenFamily_supported (placedVariableFamily_valid hk) choose p hp
  have hsC : ∀ j, ∀ hj : j < (placeFormula [] f).length, ∀ p ∈ clauseChosen k hk f choose j,
      p ⊆ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j] := by
    intro j hj p hp
    rw [clauseChosen_at hk f choose j hj] at hp
    exact chosenFamily_supported (placedClauseFamily_valid hk hf ⟨j,hj⟩) choose p hp
  have hbase : ∀ j, j < (placeFormula [] f).length → 1 ≤ cost (clauseChosen k hk f choose j) := by
    intro j hj
    rw [clauseChosen_at hk f choose j hj]
    exact placedClauseFamily_cost_positive hk hf ⟨j,hj⟩ choose
      (fun c hc => hchoose c (formulaFamily_clause_mem hk f ⟨j,hj⟩ hc))
  have hsum := sum_map_le (List.range (placeFormula [] f).length) (fun _ => 1)
    (fun j => cost (clauseChosen k hk f choose j) +
      crossCost (globalVariablePaths f (variableChosen k hk choose)) (clauseChosen k hk f choose j)) (by
        intro j hj
        have h := hbase j (List.mem_range.mp hj)
        omega)
  rw [sum_map_const,List.length_range,Nat.mul_one,placeFormula_length] at hsum
  change cost (chosenFamily (formulaFamily k hk f) choose) ≤ budget at hcost
  rw [formulaFamily_choices,formulaGraph_cost_decomposition hf _ _ hsV hsC] at hcost
  simp only [placeFormula_length] at hcost
  omega

/-- The effective graph map for every Definition 7 input. Simplification
removes repeated literals, tautologies, and units. Fresh satisfiable clauses
restore the original budget. A detected contradiction yields a graph whose
unavoidable baseline exceeds that budget by one. -/
def globalReductionGraph (k : Nat) (f : CNF) : Graph :=
  match cleanFormula f with
  | some g => formulaGraph k (padFormula (f.length-g.length) g)
  | none => formulaGraph k (padFormula (f.length+1) [])

/-- Global SAT/CPAP correctness for exactly Definition 7, including repeated
literals and tautological clauses, for every k >= 5. The budget is the original
number of clauses, not the number remaining after preprocessing. -/
theorem globalReduction_sat_iff_assignment {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) :
    Satisfiable f ↔ HasAssignment (globalReductionGraph k f) k f.length := by
  have hsat := cleanFormula_sat f
  cases hg : cleanFormula f with
  | none =>
    rw [hg] at hsat
    have hbad : ¬ HasAssignment (globalReductionGraph k f) k f.length := by
      intro h
      have hgraph : globalReductionGraph k f = formulaGraph k (padFormula (f.length+1) []) := by
        simp [globalReductionGraph,hg]
      rw [hgraph] at h
      have hbound := formulaGraph_assignment_budget_lower hk
        (padFormula_bounded (f.length+1) emptyFormula_bounded)
        (padFormula_distinct (f.length+1) emptyFormula_distinct) h
      rw [padFormula_length] at hbound
      simp only [List.length_nil,Nat.zero_add] at hbound
      omega
    exact ⟨fun h => False.elim (hsat h),fun h => False.elim (hbad h)⟩
  | some g =>
    rw [hg] at hsat
    obtain ⟨hgb,hgd,hgl⟩ := cleanFormula_bounded hf hg
    have hlen : (padFormula (f.length-g.length) g).length = f.length := by
      rw [padFormula_length]
      omega
    have hclean := formulaGraph_sat_iff_assignment hk
      (padFormula_bounded (f.length-g.length) hgb) (padFormula_distinct (f.length-g.length) hgd)
    rw [hlen] at hclean
    have hgraph : globalReductionGraph k f = formulaGraph k (padFormula (f.length-g.length) g) := by
      simp [globalReductionGraph,hg]
    rw [hgraph]
    exact hsat.symm.trans ((padFormula_sat (f.length-g.length) g).symm.trans hclean)

end STACS2027.Oriented
