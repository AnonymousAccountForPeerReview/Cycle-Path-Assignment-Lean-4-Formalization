module

public import NPHardness.OrientedGlobalExcursions

/-! A clause with distinct variables meets each variable gadget in at most
one attachment edge. The hypothesis is explicit: Definition 7 alone permits
repeated literals, whose preprocessing is a separate obligation. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

theorem clause_single_variable_port {k : Nat} {f : CNF} (hd : ClauseVariablesDistinct f)
    {v a b : Nat} (hv : v < variableBound f) {j : Fin (placeFormula [] f).length}
    (haV : VariableRegion k v a) (hbV : VariableRegion k v b)
    (haC : ClauseRegion k f j a) (hbC : ClauseRegion k f j b) :
    ∃ i p s t, i < 3 ∧ (placeFormula [] f)[j.val][i]? = some p ∧ v = p.literal.var ∧
      a = blockVertex (gadgetWidth k) v (variableEndpoint p.port s) ∧
      b = blockVertex (gadgetWidth k) v (variableEndpoint p.port t) := by
  obtain ⟨i,p,s,hi,hip,hvp,hea⟩ := regions_intersection hv haV haC
  obtain ⟨r,q,t,_,hrq,hvq,heb⟩ := regions_intersection hv hbV hbC
  have he : p = q := nodup_map_injective_on (fun p : PlacedLiteral => p.literal.var)
    (hd.placed (List.getElem_mem j.isLt)) (List.mem_of_getElem? hip) (List.mem_of_getElem? hrq)
    (hvp.symm.trans hvq)
  subst q
  exact ⟨i,p,s,t,hi,hip,hvp,hea,heb⟩

/-- The clause copy is an induced subgraph of the global graph, for distinct
variables within each clause. -/
theorem formulaGraph_clause_induced {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) {j : Fin (placeFormula [] f).length} {a b : Nat}
    (hab : a ≠ b) (he : edge a b ∈ formulaGraph k f)
    (ha : ClauseRegion k f j a) (hb : ClauseRegion k f j b) :
    edge a b ∈ placedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val] := by
  rcases formulaGraph_edge_cases he with ⟨v,hv,hev⟩ | ⟨i,hei⟩
  · have hends := placedVariableGraph_endpoints hev
    obtain ⟨r,p,s,t,hr,hrp,hvp,hea,heb⟩ := clause_single_variable_port hd hv hends.1 hends.2 ha hb
    have hst : s ≠ t := by intro h; exact hab (hea.trans ((congrArg _ (congrArg _ h)).trans heb.symm))
    have heq : edge a b = mapEdge (clauseVertex (gadgetWidth k) (variableBound f) j.val
        (placeFormula [] f)[j.val]) (edge (clauseEndpoint r false) (clauseEndpoint r true)) := by
      rw [mapped_attachment_edge hr hrp,mapEdge_edge,← hvp,hea,heb]
      cases s <;> cases t
      · exact False.elim (hst rfl)
      · rfl
      · exact edge_comm _ _
      · exact False.elim (hst rfl)
    rw [heq]
    exact List.mem_map.mpr ⟨_,clauseGraph_ports k _ hr,rfl⟩
  · have h := ha.unique hf (placedClauseGraph_endpoints hei).1
    exact h ▸ hei

def PrivateClauseVertex (k : Nat) (f : CNF) (j : Fin (placeFormula [] f).length)
    (x : Nat) : Prop :=
  ClauseRegion k f j x ∧ ∀ v, v < variableBound f → ¬ VariableRegion k v x

theorem private_clause_neighbor {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {j : Fin (placeFormula [] f).length} {a b : Nat}
    (ha : PrivateClauseVertex k f j a) (he : edge a b ∈ formulaGraph k f) :
    ClauseRegion k f j b := by
  rcases formulaGraph_edge_cases he with ⟨v,hv,hev⟩ | ⟨i,hei⟩
  · exact False.elim (ha.2 v hv (placedVariableGraph_endpoints hev).1)
  · have h := ha.1.unique hf (placedClauseGraph_endpoints hei).1
    exact h ▸ (placedClauseGraph_endpoints hei).2

theorem clause_excursion_one_variable_bound {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f)
    {j : Fin (placeFormula [] f).length} {v a b : Nat} (hv : v < variableBound f)
    {p : List Nat} (hp : IsSimplePath (formulaGraph k f) a b p) (hl : 3 ≤ p.length)
    (ha : ClauseRegion k f j a) (hb : ClauseRegion k f j b)
    (hs : ∀ x ∈ p, VariableRegion k v x) : k - 1 ≤ (pathEdges p).length := by
  obtain ⟨i,lit,s,t,_,hip,_,hea,heb⟩ := clause_single_variable_port hd hv
    (hs a hp.vertices.1) (hs b hp.vertices.2) ha hb
  have hpl := (hf.placed_clause_bounds (List.getElem_mem j.isLt) lit (List.mem_of_getElem? hip)).2
  have hlocal := variable_path_pullback (formulaGraph_variable_path hf hv hp hs) hs
  have hw : 0 < gadgetWidth k := by have := gadgetWidth_ge k; omega
  have hbound : ∀ q r, variableEndpoint q r < gadgetWidth k := fun q r =>
    Nat.lt_of_lt_of_le (variableEndpoint_bound q r) (by have := gadgetWidth_ge k; omega)
  rw [hea,heb,blockVertex_mod hw v _ (hbound _ _),blockVertex_mod hw v _ (hbound _ _)] at hlocal
  have hlen : 3 ≤ (p.map (· % gadgetWidth k)).length := by simpa using hl
  have hab : variableEndpoint lit.port s ≠ variableEndpoint lit.port t := by
    intro he
    have hm := hlocal.vertices
    have hn := hlocal.1
    have hh := hlocal.2.1
    have ht := hlocal.2.2.1
    have hne : (p.map (· % gadgetWidth k)).head? ≠ (p.map (· % gadgetWidth k)).getLast? := by
      cases h : p.map (· % gadgetWidth k) with
      | nil => simp [h] at hlen
      | cons z zs =>
        rw [h] at hn
        have hzs : zs ≠ [] := by intro he; simp [h,he] at hlen
        intro heq
        have hzlast : zs.getLast? = some z := by
          cases zs with
          | nil => exact False.elim (hzs rfl)
          | cons y ys => simpa using heq.symm
        exact (List.nodup_cons.mp hn).1 (List.mem_of_getLast? hzlast)
    apply hne
    rw [hh,ht,he]
  have hedge : edge (variableEndpoint lit.port s) (variableEndpoint lit.port t) ∈ variableGraph k := by
    cases s <;> cases t
    · exact False.elim (hab rfl)
    · exact variableGraph_ports k hpl
    · simpa only [edge_comm] using variableGraph_ports k hpl
    · exact False.elim (hab rfl)
  have hcycle := hlocal.close_cycle hab hedge (path_endpoint_edge_absent hlocal hlen)
  have h := variableGraph_girth hk hcycle
  simp only [List.length_map] at h
  rw [pathEdges_length]
  omega

end STACS2027.Oriented
