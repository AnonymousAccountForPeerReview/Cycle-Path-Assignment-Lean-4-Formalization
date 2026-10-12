module

public import NPHardness.MappedAssignments

/-! Loads at the identified ports connect the global budget to literal truth. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def variablePortEdge (p : Nat) : Edge := edge (variableEndpoint p false) (variableEndpoint p true)
def literalPortGlobal (k : Nat) (p : PlacedLiteral) : Edge :=
  mapEdge (blockVertex (gadgetWidth k) p.literal.var) (variablePortEdge p.port)

theorem variablePortEdge_mem {p : Nat} (hp : p < 3) : variablePortEdge p ∈ variablePorts :=
  (by decide : ∀ p : Fin 3, variablePortEdge p.val ∈ variablePorts) ⟨p,hp⟩

theorem load_zero_iff (ps : List (List Edge)) (e : Edge) :
    load ps e = 0 ↔ ∀ p ∈ ps, e ∉ p := by
  unfold load
  constructor
  · intro h p hp
    have hz := List.sum_eq_zero_iff_forall_eq_nat.mp h _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
    exact List.count_eq_zero.mp hz
  · intro h
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro n hn
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hn
    exact List.count_eq_zero_of_not_mem (h p hp)

theorem load_pos_iff (ps : List (List Edge)) (e : Edge) :
    0 < load ps e ↔ ∃ p ∈ ps, e ∈ p := by
  classical
  constructor
  · intro h
    by_cases hm : ∃ p ∈ ps, e ∈ p
    · exact hm
    · have hz : load ps e = 0 := (load_zero_iff ps e).mpr (fun p hp he => hm ⟨p,hp,he⟩)
      omega
  · rintro ⟨p,hp,he⟩
    have hne : load ps e ≠ 0 := fun h => (load_zero_iff ps e).mp h p hp he
    omega

theorem crossCost_zero_load {ps qs : List (List Edge)} (hz : crossCost ps qs = 0)
    {e : Edge} (he : 0 < load qs e) : load ps e = 0 := by
  obtain ⟨q,hq,heq⟩ := (load_pos_iff qs e).mp he
  apply (load_zero_iff ps e).mpr
  intro p hp hep
  have h := (crossCost_zero_iff ps qs).mp hz p hp q hq
  have hc := List.sum_eq_zero_iff_forall_eq_nat.mp h _ (List.mem_map.mpr ⟨e,hep,rfl⟩)
  exact List.count_eq_zero.mp hc heq

theorem load_zero_of_subset {ps qs : List (List Edge)} (hs : ps ⊆ qs) {e : Edge}
    (hz : load qs e = 0) : load ps e = 0 :=
  (load_zero_iff ps e).mpr (fun p hp => (load_zero_iff qs e).mp hz p (hs hp))

theorem activeClausePorts_spec {c : List PlacedLiteral} (hc : c.length = 2 ∨ c.length = 3)
    {e : Edge} (he : e ∈ activeClausePorts c) :
    ∃ i, i < c.length ∧ i < 3 ∧ e = edge (clauseEndpoint i false) (clauseEndpoint i true) := by
  rcases hc with hc | hc
  · simp only [activeClausePorts,hc] at he
    obtain ⟨i,hi⟩ := (by decide : ∀ e ∈ ([(0,1),(4,5)] : List Edge), ∃ i : Fin 2,
      e = edge (clauseEndpoint i.val false) (clauseEndpoint i.val true)) e he
    exact ⟨i.val,by omega,by omega,hi⟩
  · simp only [activeClausePorts,hc] at he
    obtain ⟨i,hi⟩ := (by decide : ∀ e ∈ clauseThreePorts5, ∃ i : Fin 3,
      e = edge (clauseEndpoint i.val false) (clauseEndpoint i.val true)) e he
    exact ⟨i.val,by omega,i.isLt,hi⟩

theorem clauseFamily_cost_one_uses_port {k : Nat} (hk : 5 ≤ k) (c : List PlacedLiteral)
    (choose : Cycle → Nat) (hv : ∀ d ∈ clauseFamily k hk c, choose d ∈ d)
    (hc : cost (chosenFamily (clauseFamily k hk c) choose) = 1) :
    ∃ e ∈ activeClausePorts c, 0 < load (chosenFamily (clauseFamily k hk c) choose) e := by
  classical
  have hblocked := clauseFamily_blocked_lower hk c choose hv
  by_cases h : ∃ e ∈ activeClausePorts c, 0 < load (chosenFamily (clauseFamily k hk c) choose) e
  · exact h
  · have hz : ((activeClausePorts c).map (load (chosenFamily (clauseFamily k hk c) choose))).sum = 0 := by
      apply List.sum_eq_zero_iff_forall_eq_nat.mpr
      intro n hn
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hn
      have hn : ¬ 0 < load (chosenFamily (clauseFamily k hk c) choose) e := fun hn => h ⟨e,he,hn⟩
      omega
    unfold costWithPorts at hblocked
    rw [hc,hz] at hblocked
    omega

theorem variableChosen_normalizes {k : Nat} (hk : 5 ≤ k) (v : Nat) (choose : Cycle → Nat)
    (hv : ∀ c ∈ placedVariableFamily k hk v, choose c ∈ c)
    (hz : cost (variableChosen k hk choose v) = 0) :
    ∃ truth : Bool, ∀ p, p < 3 → load (variableExpandedState k hk truth) (variablePortEdge p) ≤
      load (variableChosen k hk choose v) (mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge p)) := by
  obtain ⟨pick,hpick,hpaths,hcost⟩ := mapped_choice_cost (variableGraph_below k)
    (realizeLinks_normalized 7 (variableLinks k)) (variableFamily_valid hk)
    (blockVertex (gadgetWidth k) v) (fun _ ha _ hb he => (blockVertex_injective ha hb he).2) choose hv
  have hz' : cost (chosenFamily (variableFamily k hk) pick) = 0 := hcost.symm.trans hz
  obtain ⟨truth,hnorm⟩ := variableFamily_zero_normalizes hk pick hz'
  refine ⟨truth,?_⟩
  intro p hp
  change load (variableExpandedState k hk truth) (variablePortEdge p) ≤
    load (chosenFamily ((variableFamily k hk).map (List.map (blockVertex (gadgetWidth k) v))) choose)
      (mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge p))
  rw [hpaths]
  have hload := load_relabel (variableGraph_below k) (realizeLinks_normalized 7 (variableLinks k))
    (blockVertex (gadgetWidth k) v) (fun _ ha _ hb he => (blockVertex_injective ha hb he).2)
    (chosenFamily_supported (variableFamily_valid hk) pick)
    (show variablePortEdge p ∈ variableGraph k from variableGraph_ports k hp)
  rw [hload]
  exact hnorm _ (variablePortEdge_mem hp)

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

theorem variableState_literal_load {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    {p : PlacedLiteral} (hp : p ∈ (placeFormula [] f).flatten) (a : Assignment) :
    load (variableExpandedState k hk (a p.literal.var)) (variablePortEdge p.port) =
      if evalLiteral a p.literal then 0 else 1 := by
  have hport := hf.placement_port_lt hp
  have hs := variableExpandedState_loads hk (a p.literal.var)
  cases ht : p.literal.positive
  · have hep : p.port = p.earlier + 1 := by simp [PlacedLiteral.port,ht]
    have he : p.port = 1 ∨ p.port = 2 := by omega
    rcases he with he | he
    · rw [he]
      change load (variableExpandedState k hk (a p.literal.var)) (4,5) = _
      rw [hs.2.2]
      cases ha : a p.literal.var <;> simp [evalLiteral,ht,ha]
    · rw [he]
      change load (variableExpandedState k hk (a p.literal.var)) (0,3) = _
      rw [hs.2.1]
      cases ha : a p.literal.var <;> simp [evalLiteral,ht,ha]
  · have he : p.port = 0 := by simp [PlacedLiteral.port,ht]
    rw [he]
    change load (variableExpandedState k hk (a p.literal.var)) (2,6) = _
    rw [hs.1]
    simp [evalLiteral,ht]

end STACS2027
