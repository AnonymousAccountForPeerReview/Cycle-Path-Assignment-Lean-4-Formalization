module

public import NPHardness.PathRegions

/-! Quantitative bounds on actual paths leaving a clause through a variable
gadget. These estimates do not assume an abstract reduction certificate. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem clauseRegion_port {k : Nat} {f : CNF}
    {j : Fin (placeFormula [] f).length} {i : Nat} (hi : i < 3)
    {p : PlacedLiteral} (hp : (placeFormula [] f)[j.val][i]? = some p) (s : Bool) :
    ClauseRegion k f j
      (blockVertex (gadgetWidth k) p.literal.var (variableEndpoint p.port s)) := by
  refine ⟨clauseEndpoint i s,?_,(clauseVertex_attachment hi hp s).symm⟩
  have hm := (by decide : ∀ i : Fin 3, ∀ s : Bool, clauseEndpoint i.val s < 12) ⟨i,hi⟩ s
  change clauseEndpoint i s < 12 at hm
  have := gadgetWidth_ge k
  omega

theorem formulaGraph_variable_boundary {k : Nat} {f : CNF} {v a b : Nat}
    (hv : v < variableBound f) (he : edge a b ∈ formulaGraph k f)
    (ha : VariableRegion k v a) (hb : ¬ VariableRegion k v b) :
    ∃ j : Fin (placeFormula [] f).length, ∃ i p s,
      i < 3 ∧ (placeFormula [] f)[j.val][i]? = some p ∧
      v = p.literal.var ∧ a = blockVertex (gadgetWidth k) v (variableEndpoint p.port s) := by
  rcases formulaGraph_edge_cases he with ⟨w,_,hw⟩ | ⟨j,hj⟩
  · have hends := placedVariableGraph_endpoints hw
    have hvw := ha.unique hends.1
    exact False.elim (hb (hvw ▸ hends.2))
  · obtain ⟨i,p,s,hi,hip,hvp,he⟩ := regions_intersection hv ha (placedClauseGraph_endpoints hj).1
    exact ⟨j,i,p,s,hi,hip,hvp,he⟩

theorem formulaGraph_variable_path {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {v a b : Nat} (hv : v < variableBound f) {p : List Nat}
    (hp : IsSimplePath (formulaGraph k f) a b p)
    (hs : ∀ x ∈ p, VariableRegion k v x) :
    IsSimplePath (placedVariableGraph k v) a b p := by
  refine ⟨hp.1,hp.2.1,hp.2.2.1,?_⟩
  intro e he
  have hn := pathEdges_normalized p e he
  have hm := pathEdges_endpoints he
  have hg : edge e.1 e.2 ∈ formulaGraph k f := by rw [hn]; exact hp.2.2.2 e he
  have h := (formulaGraph_between_variables hf hv hv hg (hs _ hm.1) (hs _ hm.2)).2
  simpa only [hn] using h

/-- A path from a clause attachment to a different exit of the same variable
has the separation length prescribed in Figure 4(a). -/
theorem clause_exit_variable_distance {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) {j : Fin (placeFormula [] f).length}
    {v a b z : Nat} (hv : v < variableBound f) {p : List Nat}
    (hp : IsSimplePath (formulaGraph k f) a b p)
    (hs : ∀ x ∈ p, VariableRegion k v x)
    (ha : ClauseRegion k f j a) (hb : ¬ ClauseRegion k f j b)
    (he : edge b z ∈ formulaGraph k f) (hz : ¬ VariableRegion k v z) :
    (k-2)/2 ≤ (pathEdges p).length := by
  obtain ⟨i,lit,s,hi,hip,hvlit,hea⟩ := regions_intersection hv (hs a hp.vertices.1) ha
  obtain ⟨j',i',lit',s',hi',hip',hvlit',heb⟩ :=
    formulaGraph_variable_boundary hv he (hs b hp.vertices.2) hz
  have hpl := (hf.placed_clause_bounds (List.getElem_mem j.isLt) lit (List.mem_of_getElem? hip)).2
  have hpl' := (hf.placed_clause_bounds (List.getElem_mem j'.isLt) lit' (List.mem_of_getElem? hip')).2
  have hne : lit.port ≠ lit'.port := by
    intro h
    apply hb
    rw [heb,← h,hvlit]
    exact clauseRegion_port hi hip s'
  have hlocal := variable_path_pullback (formulaGraph_variable_path hf hv hp hs) hs
  have hw : 0 < gadgetWidth k := by have := gadgetWidth_ge k; omega
  have hb1 : variableEndpoint lit.port s < gadgetWidth k :=
    Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) (by have := gadgetWidth_ge k; omega)
  have hb2 : variableEndpoint lit'.port s' < gadgetWidth k :=
    Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) (by have := gadgetWidth_ge k; omega)
  rw [hea,heb,blockVertex_mod hw v _ hb1,blockVertex_mod hw v _ hb2] at hlocal
  have hd := variableGraph_port_distance hk hpl hpl' hne s s' hlocal
  simpa only [pathEdges_length,List.length_map] using hd

end STACS2027
