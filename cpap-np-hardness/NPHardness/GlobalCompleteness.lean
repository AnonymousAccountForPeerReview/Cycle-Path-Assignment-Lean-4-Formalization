module

public import NPHardness.CombineAssignments

/-! Combining a satisfying assignment into a CPAP assignment of exactly the
clause-count cost, and the resulting global equivalence. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem formulaGraph_sat_implies_assignment {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f)
    (hsat : Satisfiable f) : HasAssignment (formulaGraph k f) k f.length := by
  classical
  obtain ⟨a,heval⟩ := hsat
  let Vpick := fun v => Classical.choose (placedVariable_sat_witness hk hf a v)
  have hVspec := fun v => Classical.choose_spec (placedVariable_sat_witness hk hf a v)
  have hclauseSat : ∀ j : Fin (placeFormula [] f).length,
      ∃ p ∈ (placeFormula [] f)[j.val], evalLiteral a p.literal = true := by
    intro j
    have hm : ((placeFormula [] f)[j.val].map PlacedLiteral.literal) ∈ f := by
      have hm' : ((placeFormula [] f)[j.val].map PlacedLiteral.literal) ∈
          (placeFormula [] f).map (List.map PlacedLiteral.literal) :=
        List.mem_map.mpr ⟨_,List.getElem_mem j.isLt,rfl⟩
      rw [placeFormula_forget] at hm'
      exact hm'
    have h := List.all_eq_true.mp heval _ hm
    obtain ⟨l,hl,he⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hl
    exact ⟨p,hp,he⟩
  let Cpick := fun j => if hj : j < (placeFormula [] f).length then
      Classical.choose (placedClause_sat_witness hk hf a ⟨j,hj⟩ (hclauseSat ⟨j,hj⟩)) else fun _ => 0
  have hCspec : ∀ j, ∀ hj : j < (placeFormula [] f).length,
      (∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], Cpick j c ∈ c) ∧
      cost (chosenFamily (placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j]) (Cpick j)) = 1 ∧
      (∀ p ∈ (placeFormula [] f)[j], evalLiteral a p.literal = false →
        load (chosenFamily (placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j]) (Cpick j))
          (literalPortGlobal k p) = 0) := by
    intro j hj
    simpa only [Cpick,dite_eq_left hj] using
      Classical.choose_spec (placedClause_sat_witness hk hf a ⟨j,hj⟩ (hclauseSat ⟨j,hj⟩))
  let pick : Sum Nat Nat → Cycle → Nat := Sum.elim Vpick Cpick
  have hn : ((gadgetIndices f).flatMap (indexedFamily k hk f)).Nodup := by
    rw [formulaFamily_indexed]
    exact distinctCycles_nodup (formulaFamily_distinct hk hf hd)
  obtain ⟨choose,hcombine⟩ := combine_indexed_choices (gadgetIndices f) (indexedFamily k hk f) pick hn
  have hchooseV : ∀ v, v < variableBound f → ∀ c ∈ placedVariableFamily k hk v,
      choose c = Vpick v c := by
    intro v hv c hc
    exact hcombine (.inl v) (gadgetIndex_variable_mem f hv) c hc
  have hchooseC : ∀ j, ∀ hj : j < (placeFormula [] f).length,
      ∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], choose c = Cpick j c := by
    intro j hj c hc
    apply hcombine (.inr j) (gadgetIndex_clause_mem f hj) c
    rw [indexedFamily_clause_at hk f hj]
    exact hc
  have hVeq : ∀ v, v < variableBound f → variableChosen k hk choose v =
      chosenFamily (placedVariableFamily k hk v) (Vpick v) := by
    intro v hv
    exact List.map_congr_left (fun c hc => congrArg (selectedAt c) (hchooseV v hv c hc))
  have hCeq : ∀ j, ∀ hj : j < (placeFormula [] f).length, clauseChosen k hk f choose j =
      chosenFamily (placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j]) (Cpick j) := by
    intro j hj
    rw [clauseChosen_at hk f choose j hj]
    exact List.map_congr_left (fun c hc => congrArg (selectedAt c) (hchooseC j hj c hc))
  have hchoose : ∀ c ∈ formulaFamily k hk f, choose c ∈ c := by
    intro c hc
    rw [← formulaFamily_indexed] at hc
    obtain ⟨id,hid,hc⟩ := List.mem_flatMap.mp hc
    rw [hcombine id hid c hc]
    cases id with
    | inl v => exact (hVspec v).1 c hc
    | inr j =>
      have hj : j < (placeFormula [] f).length := by simpa [gadgetIndices] using hid
      rw [indexedFamily_clause_at hk f hj] at hc
      exact (hCspec j hj).1 c hc
  have hsV : ∀ v, v < variableBound f → ∀ p ∈ variableChosen k hk choose v, p ⊆ placedVariableGraph k v := by
    intro v _ p hp
    exact chosenFamily_supported (placedVariableFamily_valid hk) choose p hp
  have hsC : ∀ j, ∀ hj : j < (placeFormula [] f).length, ∀ p ∈ clauseChosen k hk f choose j,
      p ⊆ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j] := by
    intro j hj p hp
    rw [clauseChosen_at hk f choose j hj] at hp
    exact chosenFamily_supported (placedClauseFamily_valid hk hf ⟨j,hj⟩) choose p hp
  have htrue : ∀ v, v < variableBound f → ∀ p ∈ (placeFormula [] f).flatten,
      p.literal.var = v → evalLiteral a p.literal = true →
      load (variableChosen k hk choose v) (literalPortGlobal k p) = 0 := by
    intro v hv p hp hpv htrue
    rw [hVeq v hv,(hVspec v).2.2 p hp hpv,htrue]
    rfl
  have hfalse : ∀ j, ∀ hj : j < (placeFormula [] f).length, ∀ p ∈ (placeFormula [] f)[j],
      evalLiteral a p.literal = false → load (clauseChosen k hk f choose j) (literalPortGlobal k p) = 0 := by
    intro j hj p hp hfalse
    rw [hCeq j hj]
    exact (hCspec j hj).2.2 p hp hfalse
  have hcross := formulaGraph_satisfied_crossCost_zero hf a (variableChosen k hk choose)
    (clauseChosen k hk f choose) hsV hsC htrue hfalse
  have hvarcost : ((List.range (variableBound f)).map fun v => cost (variableChosen k hk choose v)).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro n hn
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hn
    rw [hVeq v (List.mem_range.mp hv)]
    exact (hVspec v).2.1
  have hclausecost : ((List.range (placeFormula [] f).length).map fun j =>
      cost (clauseChosen k hk f choose j) +
        crossCost (globalVariablePaths f (variableChosen k hk choose)) (clauseChosen k hk f choose j)).sum = f.length := by
    have heq : ((List.range (placeFormula [] f).length).map fun j =>
        cost (clauseChosen k hk f choose j) +
          crossCost (globalVariablePaths f (variableChosen k hk choose)) (clauseChosen k hk f choose j)) =
        (List.range (placeFormula [] f).length).map (fun _ => 1) := by
      apply List.map_congr_left
      intro j hj
      have hj' := List.mem_range.mp hj
      rw [hcross j hj',hCeq j hj',(hCspec j hj').2.1]
    rw [heq,sum_map_const,List.length_range,Nat.mul_one,placeFormula_length]
  apply (formulaGraph_assignment_iff_family hk hf hd f.length).mpr
  refine ⟨choose,hchoose,?_⟩
  change cost (chosenFamily (formulaFamily k hk f) choose) ≤ f.length
  rw [formulaFamily_choices,formulaGraph_cost_decomposition hf _ _ hsV hsC,hvarcost,hclausecost]
  omega

/-- The completed global SAT/CPAP equivalence for bounded-occurrence formulas
whose clauses contain distinct variables. The graph is the explicit glued
construction and the budget is exactly the number of clauses. -/
theorem formulaGraph_sat_iff_assignment {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f) :
    Satisfiable f ↔ HasAssignment (formulaGraph k f) k f.length :=
  ⟨formulaGraph_sat_implies_assignment hk hf hd,formulaGraph_assignment_implies_sat hk hf hd⟩

end STACS2027
