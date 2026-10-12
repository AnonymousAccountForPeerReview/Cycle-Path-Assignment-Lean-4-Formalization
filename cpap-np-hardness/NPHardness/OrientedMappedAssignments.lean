module

public import NPHardness.OrientedGlobalFamilyUnique

/-! Exact restriction of a global vertex choice to each gadget. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

theorem placedClauseFamily_cost_positive {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (j : Fin (placeFormula [] f).length) (choose : Cycle → Nat)
    (hv : ∀ c ∈ placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val], choose c ∈ c) :
    1 ≤ cost (chosenFamily (placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val]) choose) := by
  obtain ⟨pick,hpick,_,hcost⟩ := mapped_choice_cost (clauseGraph_below k _) (clauseGraph_normalized k _)
    (clauseFamily_valid hk _) (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val])
    (fun _ ha _ hb he => clauseVertex_injective (by have := gadgetWidth_ge k; omega)
      (hf.placed_clause_nodup (List.getElem_mem j.isLt)) (hf.placed_clause_bounds (List.getElem_mem j.isLt)) ha hb he)
    choose hv
  change 1 ≤ cost (chosenFamily
    ((clauseFamily k hk (placeFormula [] f)[j.val]).map
      (List.map (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val]))) choose)
  rw [hcost]
  exact clauseFamily_cost_positive hk _ pick hpick

noncomputable def clauseChosen (k : Nat) (hk : 5 ≤ k) (f : CNF)
    (choose : Cycle → Nat) (j : Nat) : List (List Edge) :=
  chosenFamily (placedClauseFamily k hk (variableBound f) j ((placeFormula [] f)[j]?.getD [])) choose

theorem clauseChosen_at {k : Nat} (hk : 5 ≤ k) (f : CNF) (choose : Cycle → Nat)
    (j : Nat) (hj : j < (placeFormula [] f).length) :
    clauseChosen k hk f choose j =
      chosenFamily (placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j]) choose := by
  simp [clauseChosen,List.getElem?_eq_getElem hj]

theorem formulaFamily_choices {k : Nat} (hk : 5 ≤ k) (f : CNF) (choose : Cycle → Nat) :
    chosenFamily (formulaFamily k hk f) choose =
      globalVariablePaths f (variableChosen k hk choose) ++
      globalClausePaths f (clauseChosen k hk f choose) := by
  unfold chosenFamily formulaFamily globalVariablePaths globalClausePaths variableChosen clauseChosen
  rw [mapIdx_eq_range _ []]
  simp only [List.map_append,List.map_flatten,List.map_map,List.flatMap]
  rfl

theorem formulaFamily_variable_mem {k : Nat} (hk : 5 ≤ k) (f : CNF) {v : Nat}
    (hv : v < variableBound f) {c : Cycle} (hc : c ∈ placedVariableFamily k hk v) :
    c ∈ formulaFamily k hk f :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨v,List.mem_range.mpr hv,hc⟩)

theorem formulaFamily_clause_mem {k : Nat} (hk : 5 ≤ k) (f : CNF)
    (j : Fin (placeFormula [] f).length) {c : Cycle}
    (hc : c ∈ placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val]) :
    c ∈ formulaFamily k hk f := by
  apply List.mem_append_right
  exact List.mem_flatten.mpr ⟨_,List.mem_mapIdx.mpr ⟨j.val,j.isLt,rfl⟩,hc⟩

theorem formulaFamily_budget {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (choose : Cycle → Nat) (hv : ∀ c ∈ formulaFamily k hk f, choose c ∈ c)
    (hcost : cost (chosenFamily (formulaFamily k hk f) choose) ≤ f.length) :
    (∀ v, v < variableBound f → cost (variableChosen k hk choose v) = 0) ∧
    (∀ j, j < (placeFormula [] f).length → cost (clauseChosen k hk f choose j) = 1 ∧
      crossCost (globalVariablePaths f (variableChosen k hk choose)) (clauseChosen k hk f choose j) = 0) := by
  rw [formulaFamily_choices] at hcost
  apply formulaGraph_budget_forces_zero_interaction (k := k) hf _ _ ?_ ?_ ?_ hcost
  · intro v _ p hp
    exact chosenFamily_supported (placedVariableFamily_valid hk) choose p hp
  · intro j hj p hp
    rw [clauseChosen_at hk f choose j hj] at hp
    exact chosenFamily_supported (placedClauseFamily_valid hk hf ⟨j,hj⟩) choose p hp
  · intro j hj
    rw [clauseChosen_at hk f choose j hj]
    exact placedClauseFamily_cost_positive hk hf ⟨j,hj⟩ choose
      (fun c hc => hv c (formulaFamily_clause_mem hk f ⟨j,hj⟩ hc))

end STACS2027.Oriented
