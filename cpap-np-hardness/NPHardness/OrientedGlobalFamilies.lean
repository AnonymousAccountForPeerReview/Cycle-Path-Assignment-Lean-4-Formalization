module

public import NPHardness.OrientedGlobalCost
public import NPHardness.VariableExpansionCost
public import NPHardness.CPAP
public import NPHardness.ClauseTwo6

/-! A complete, nonduplicated representative family for the global graph. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

noncomputable def placedClauseFamily (k : Nat) (hk : 5 ≤ k) (n j : Nat)
    (c : List PlacedLiteral) : List Cycle :=
  (clauseFamily k hk c).map (List.map (clauseVertex (gadgetWidth k) n j c))

noncomputable def formulaFamily (k : Nat) (hk : 5 ≤ k) (f : CNF) : List Cycle :=
  (List.range (variableBound f)).flatMap (placedVariableFamily k hk) ++
    ((placeFormula [] f).mapIdx (fun j c => placedClauseFamily k hk (variableBound f) j c)).flatten

theorem placedClauseFamily_valid {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (j : Fin (placeFormula [] f).length) :
    ∀ c ∈ placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val],
      IsCycle (placedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]) k c := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have h := clauseFamily_valid hk _ d hd
  exact h.map _ (fun a ha b hb he => clauseVertex_injective
    (by have := gadgetWidth_ge k; omega) (hf.placed_clause_nodup (List.getElem_mem j.isLt))
    (hf.placed_clause_bounds (List.getElem_mem j.isLt))
    (h.vertex_bound (clauseGraph_below k _) a ha) (h.vertex_bound (clauseGraph_below k _) b hb) he)

theorem formulaFamily_valid {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f) :
    ∀ c ∈ formulaFamily k hk f, IsCycle (formulaGraph k f) k c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨v,hv,hc⟩ := List.mem_flatMap.mp hc
    exact (placedVariableFamily_valid hk c hc).graph_mono (formulaGraph_variable_contains k f (List.mem_range.mp hv))
  · obtain ⟨cs,hcs,hc⟩ := List.mem_flatten.mp hc
    obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hcs
    exact (placedClauseFamily_valid hk hf ⟨j,hj⟩ c hc).graph_mono (formulaGraph_clause_contains k f j hj)

theorem formulaFamily_complete {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f) {c : Cycle}
    (hc : IsCycle (formulaGraph k f) k c) :
    ∃ d ∈ formulaFamily k hk f, SameCycle c d := by
  rcases formulaGraph_cycle_local hk hf hd hc with ⟨v,hv,hc⟩ | ⟨j,hc⟩
  · obtain ⟨d,hd,rfl⟩ := IsCycle.unmap (variableGraph_below k)
      (realizeLinks_normalized 7 (variableLinks k)) (blockVertex (gadgetWidth k) v)
      (fun a ha b hb he => (blockVertex_injective ha hb he).2) hc
    obtain ⟨e,he,hs⟩ := variableFamily_complete hk hd
    refine ⟨e.map (blockVertex (gadgetWidth k) v),?_,hs.map _⟩
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨v,List.mem_range.mpr hv,List.mem_map.mpr ⟨e,he,rfl⟩⟩
  · obtain ⟨d,hd,rfl⟩ := IsCycle.unmap (clauseGraph_below k _) (clauseGraph_normalized k _)
      (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val])
      (fun a ha b hb he => clauseVertex_injective (by have := gadgetWidth_ge k; omega)
        (hf.placed_clause_nodup (List.getElem_mem j.isLt))
        (hf.placed_clause_bounds (List.getElem_mem j.isLt)) ha hb he) hc
    obtain ⟨e,he,hs⟩ := clauseFamily_complete hk _ hd
    refine ⟨e.map (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val]),?_,hs.map _⟩
    apply List.mem_append_right
    apply List.mem_flatten.mpr
    exact ⟨_,List.mem_mapIdx.mpr ⟨j.val,j.isLt,rfl⟩,List.mem_map.mpr ⟨e,he,rfl⟩⟩

end STACS2027.Oriented
