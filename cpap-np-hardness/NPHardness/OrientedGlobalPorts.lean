module

public import NPHardness.OrientedMappedAssignments

/-! Loads at the identified ports connect the global budget to literal truth. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

theorem clauseChosen_uses_literal {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (j : Fin (placeFormula [] f).length) (choose : Cycle → Nat)
    (hv : ∀ c ∈ placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val], choose c ∈ c)
    (hc : cost (clauseChosen k hk f choose j.val) = 1) :
    ∃ (i : Nat) (p : PlacedLiteral), (placeFormula [] f)[j.val][i]? = some p ∧
      0 < load (clauseChosen k hk f choose j.val) (literalPortGlobal k p) := by
  have hinj : ∀ a, a < gadgetWidth k → ∀ b, b < gadgetWidth k →
      clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val] a =
      clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val] b → a = b :=
    fun _ ha _ hb he => clauseVertex_injective (width := gadgetWidth k)
    (n := variableBound f) (j := j.val) (c := (placeFormula [] f)[j.val])
    (by have := gadgetWidth_ge k; omega) (hf.placed_clause_nodup (List.getElem_mem j.isLt))
    (hf.placed_clause_bounds (List.getElem_mem j.isLt)) ha hb he
  obtain ⟨pick,hpick,hpaths,hcost⟩ := mapped_choice_cost (clauseGraph_below k _) (clauseGraph_normalized k _)
    (clauseFamily_valid hk _) (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val])
    hinj choose hv
  have hc' : cost (chosenFamily (clauseFamily k hk (placeFormula [] f)[j.val]) pick) = 1 := by
    rw [clauseChosen_at hk f choose j.val j.isLt] at hc
    exact hcost.symm.trans hc
  obtain ⟨e,he,hload⟩ := clauseFamily_cost_one_uses_port hk _ pick hpick hc'
  obtain ⟨i,hi,hi3,rfl⟩ := activeClausePorts_spec (hf.placed_clause_size (List.getElem_mem j.isLt)) he
  let p := (placeFormula [] f)[j.val][i]
  have hip : (placeFormula [] f)[j.val][i]? = some p := List.getElem?_eq_getElem hi
  refine ⟨i,p,hip,?_⟩
  rw [clauseChosen_at hk f choose j.val j.isLt]
  change 0 < load (chosenFamily ((clauseFamily k hk (placeFormula [] f)[j.val]).map
    (List.map (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val]))) choose) _
  have hport : literalPortGlobal k p = mapEdge
      (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val])
      (edge (clauseEndpoint i false) (clauseEndpoint i true)) := (mapped_attachment_edge hi3 hip).symm
  rw [hpaths,hport,load_relabel (clauseGraph_below k _) (clauseGraph_normalized k _)
    (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val]) hinj
    (chosenFamily_supported (clauseFamily_valid hk _) pick) (clauseGraph_ports k _ hi3)]
  exact hload

end STACS2027.Oriented
