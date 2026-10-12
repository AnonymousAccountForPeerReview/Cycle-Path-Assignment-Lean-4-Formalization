module

public import NPHardness.GlobalPorts

/-! A global CPAP assignment at the clause-count budget yields a satisfying
truth assignment for the original formula. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem formulaGraph_assignment_implies_sat {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f)
    (hassign : HasAssignment (formulaGraph k f) k f.length) : Satisfiable f := by
  classical
  obtain ⟨choose,hchoose,hcost⟩ := (formulaGraph_assignment_iff_family hk hf hd f.length).mp hassign
  obtain ⟨hzero,hclauses⟩ := formulaFamily_budget hk hf choose hchoose hcost
  have hnorm : ∀ v, v < variableBound f → ∃ truth : Bool, ∀ p, p < 3 →
      load (variableExpandedState k hk truth) (variablePortEdge p) ≤
      load (variableChosen k hk choose v) (mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge p)) := by
    intro v hv
    exact variableChosen_normalizes hk v choose
      (fun c hc => hchoose c (formulaFamily_variable_mem hk f hv hc)) (hzero v hv)
  let a : Assignment := fun v => if hv : v < variableBound f then Classical.choose (hnorm v hv) else false
  have ha : ∀ v, ∀ hv : v < variableBound f, ∀ p, p < 3 →
      load (variableExpandedState k hk (a v)) (variablePortEdge p) ≤
      load (variableChosen k hk choose v) (mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge p)) := by
    intro v hv p hp
    simpa only [a,dite_eq_left hv] using Classical.choose_spec (hnorm v hv) p hp
  have hclause : ∀ j : Fin (placeFormula [] f).length,
      ∃ p ∈ (placeFormula [] f)[j.val], evalLiteral a p.literal = true := by
    intro j
    obtain ⟨i,p,hip,hport⟩ := clauseChosen_uses_literal hk hf j choose
      (fun c hc => hchoose c (formulaFamily_clause_mem hk f j hc)) (hclauses j.val j.isLt).1
    have hpm := List.mem_of_getElem? hip
    obtain ⟨hpvar,hpport⟩ := hf.placed_clause_bounds (List.getElem_mem j.isLt) p hpm
    have hflat : p ∈ (placeFormula [] f).flatten :=
      List.mem_flatten.mpr ⟨_,List.getElem_mem j.isLt,hpm⟩
    have hglobalzero := crossCost_zero_load (hclauses j.val j.isLt).2 hport
    have hsub : variableChosen k hk choose p.literal.var ⊆
        globalVariablePaths f (variableChosen k hk choose) := by
      intro q hq
      exact List.mem_flatMap.mpr ⟨p.literal.var,List.mem_range.mpr hpvar,hq⟩
    have hlocalzero := load_zero_of_subset hsub hglobalzero
    have hbound := ha p.literal.var hpvar p.port hpport
    change load (variableChosen k hk choose p.literal.var)
      (mapEdge (blockVertex (gadgetWidth k) p.literal.var) (variablePortEdge p.port)) = 0 at hlocalzero
    rw [hlocalzero,variableState_literal_load hk hf hflat a] at hbound
    refine ⟨p,hpm,?_⟩
    cases he : evalLiteral a p.literal <;> simp_all
  refine ⟨a,?_⟩
  rw [← placeFormula_forget [] f]
  apply List.all_eq_true.mpr
  intro c hc
  obtain ⟨pc,hpc,rfl⟩ := List.mem_map.mp hc
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hpc
  obtain ⟨p,hp,he⟩ := hclause ⟨j,hj⟩
  apply List.any_eq_true.mpr
  exact ⟨p.literal,List.mem_map.mpr ⟨p,hp,rfl⟩,he⟩

end STACS2027
