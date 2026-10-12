module

public import NPHardness.OrientedGlobalSoundness

/-! Truth-state and satisfied-clause assignments in the concrete vertex blocks. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

theorem placedClause_sat_witness {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (a : Assignment) (j : Fin (placeFormula [] f).length)
    (hsat : ∃ p ∈ (placeFormula [] f)[j.val], evalLiteral a p.literal = true) :
    ∃ choose : Cycle → Nat,
      (∀ c ∈ placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val], choose c ∈ c) ∧
      cost (chosenFamily (placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val]) choose) = 1 ∧
      (∀ p ∈ (placeFormula [] f)[j.val], evalLiteral a p.literal = false →
        load (chosenFamily (placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val]) choose)
          (literalPortGlobal k p) = 0) := by
  obtain ⟨p,hp,heval⟩ := hsat
  obtain ⟨i,hi,hip⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨pick,hpick,hcost,havoid⟩ := clauseFamily_witness hk _ (hf.placed_clause_size (List.getElem_mem j.isLt)) i hi
  have hinj : ∀ u, u < gadgetWidth k → ∀ v, v < gadgetWidth k →
      clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val] u =
      clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val] v → u = v :=
    fun _ hu _ hv he => clauseVertex_injective (by have := gadgetWidth_ge k; omega)
      (hf.placed_clause_nodup (List.getElem_mem j.isLt)) (hf.placed_clause_bounds (List.getElem_mem j.isLt)) hu hv he
  have hsupport := chosenFamily_supported (clauseFamily_valid hk (placeFormula [] f)[j.val]) pick
  obtain ⟨choose,hchoose,hpaths⟩ := mapped_choice_push (clauseGraph_below k _) (clauseFamily_valid hk _)
    (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val]) hinj
    (distinctCycles_nodup (placedClauseFamily_distinct hk hf j)) pick hpick
  refine ⟨choose,hchoose,?_,?_⟩
  · change cost (chosenFamily ((clauseFamily k hk (placeFormula [] f)[j.val]).map
      (List.map (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val]))) choose) = 1
    rw [hpaths,cost_relabel (clauseGraph_below k _) (clauseGraph_normalized k _)
      (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val]) hinj hsupport]
    exact hcost
  · intro q hq hqfalse
    obtain ⟨r,hr,hrq⟩ := List.mem_iff_getElem.mp hq
    have hri : r ≠ i := by
      intro he
      subst r
      have hpq := hip.symm.trans hrq
      rw [hpq,hqfalse] at heval
      cases heval
    have hr3 : r < 3 := by have hlen := hf.placed_clause_size (List.getElem_mem j.isLt); omega
    have hqr : (placeFormula [] f)[j.val][r]? = some q := by rw [List.getElem?_eq_getElem hr,hrq]
    have hport : literalPortGlobal k q = mapEdge
        (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val])
        (edge (clauseEndpoint r false) (clauseEndpoint r true)) := (mapped_attachment_edge hr3 hqr).symm
    change load (chosenFamily ((clauseFamily k hk (placeFormula [] f)[j.val]).map
      (List.map (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val]))) choose) _ = 0
    rw [hpaths,hport,load_relabel (clauseGraph_below k _) (clauseGraph_normalized k _)
      (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val]) hinj hsupport
      (clauseGraph_ports k _ hr3)]
    exact load_zero_of_port_avoided (havoid r hr hri)

end STACS2027.Oriented
