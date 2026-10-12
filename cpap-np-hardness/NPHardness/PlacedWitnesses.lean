module

public import NPHardness.ClauseWitnessInterface

/-! Truth-state and satisfied-clause assignments in the concrete vertex blocks. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem mapped_choice_push {g : Graph} {n k : Nat} {cs : List Cycle}
    (hb : VerticesBelow g n) (hc : ∀ c ∈ cs, IsCycle g k c)
    (t : Nat → Nat) (hi : ∀ a, a < n → ∀ b, b < n → t a = t b → a = b)
    (hn : (cs.map (List.map t)).Nodup) (pick : Cycle → Nat)
    (hv : ∀ c ∈ cs, pick c ∈ c) :
    ∃ choose : Cycle → Nat, (∀ c ∈ cs.map (List.map t), choose c ∈ c) ∧
      chosenFamily (cs.map (List.map t)) choose = (chosenFamily cs pick).map (List.map (mapEdge t)) := by
  obtain ⟨choose,hchoose⟩ := image_choice_for_nodup cs (List.map t) (fun c => t (pick c)) hn
  refine ⟨choose,?_,?_⟩
  · intro c hcm
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hcm
    rw [hchoose d hd]
    exact List.mem_map.mpr ⟨pick d,hv d hd,rfl⟩
  · unfold chosenFamily
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro c hcm
    rw [hchoose c hcm]
    exact selectedAt_map (hc c hcm) t
      (fun a ha b hb' he => hi a ((hc c hcm).vertex_bound hb a ha) b
        ((hc c hcm).vertex_bound hb b hb') he) (hv c hcm)

theorem placedVariable_sat_witness {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (a : Assignment) (v : Nat) :
    ∃ choose : Cycle → Nat, (∀ c ∈ placedVariableFamily k hk v, choose c ∈ c) ∧
      cost (chosenFamily (placedVariableFamily k hk v) choose) = 0 ∧
      (∀ p ∈ (placeFormula [] f).flatten, p.literal.var = v →
        load (chosenFamily (placedVariableFamily k hk v) choose) (literalPortGlobal k p) =
          if evalLiteral a p.literal then 0 else 1) := by
  obtain ⟨pick,hpick,hstate⟩ := variableFamily_state hk (a v)
  have hsupport := chosenFamily_supported (variableFamily_valid hk) pick
  obtain ⟨choose,hchoose,hpaths⟩ := mapped_choice_push (variableGraph_below k) (variableFamily_valid hk)
    (blockVertex (gadgetWidth k) v) (fun _ ha _ hb he => (blockVertex_injective ha hb he).2)
    (distinctCycles_nodup (placedVariableFamily_distinct hk)) pick hpick
  refine ⟨choose,hchoose,?_,?_⟩
  · change cost (chosenFamily ((variableFamily k hk).map (List.map (blockVertex (gadgetWidth k) v))) choose) = 0
    rw [hpaths,cost_relabel (variableGraph_below k) (realizeLinks_normalized 7 (variableLinks k))
      (blockVertex (gadgetWidth k) v) (fun _ ha _ hb he => (blockVertex_injective ha hb he).2) hsupport,hstate]
    exact variableExpandedState_zero hk (a v)
  · intro p hp hpv
    change load (chosenFamily ((variableFamily k hk).map (List.map (blockVertex (gadgetWidth k) v))) choose)
      (literalPortGlobal k p) = _
    have hport : literalPortGlobal k p = mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge p.port) := by
      simp only [literalPortGlobal,hpv]
    rw [hpaths,hport,load_relabel (variableGraph_below k) (realizeLinks_normalized 7 (variableLinks k))
      (blockVertex (gadgetWidth k) v) (fun _ ha _ hb he => (blockVertex_injective ha hb he).2) hsupport
      (show variablePortEdge p.port ∈ variableGraph k from variableGraph_ports k (hf.placement_port_lt hp)),hstate,← hpv]
    exact variableState_literal_load hk hf hp a

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

end STACS2027
