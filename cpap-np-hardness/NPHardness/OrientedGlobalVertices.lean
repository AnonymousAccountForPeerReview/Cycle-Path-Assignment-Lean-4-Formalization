module

public import NPHardness.OrientedAttachmentEdges
public import NPHardness.PathProjection
public import NPHardness.VariableGeneral
public import NPHardness.OrientedGlobalGraph

/-! Vertex regions of the concrete glued graph. In particular, two variable
regions cannot be joined directly by a clause edge. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

def ClauseRegion (k : Nat) (f : CNF) (j : Fin (placeFormula [] f).length) (x : Nat) : Prop :=
  ∃ u, u < gadgetWidth k ∧
    x = clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val] u

theorem ClauseRegion.unique {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {i j : Fin (placeFormula [] f).length} {x : Nat}
    (hi : ClauseRegion k f i x) (hj : ClauseRegion k f j x) : i = j := by
  obtain ⟨a,ha,hxa⟩ := hi
  obtain ⟨b,hb,hxb⟩ := hj
  apply Fin.ext
  by_cases he : i.val = j.val
  · exact he
  · exact False.elim (formulaGraph_clause_vertices_disjoint hf i.isLt j.isLt he ha hb
      (hxa.symm.trans hxb))

theorem formulaGraph_edge_cases {k : Nat} {f : CNF} {e : Edge}
    (he : e ∈ formulaGraph k f) :
    (∃ v, v < variableBound f ∧ e ∈ placedVariableGraph k v) ∨
    (∃ j : Fin (placeFormula [] f).length,
      e ∈ placedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]) := by
  rcases List.mem_append.mp he with he | he
  · obtain ⟨v,hv,he⟩ := List.mem_flatMap.mp he
    exact Or.inl ⟨v,List.mem_range.mp hv,he⟩
  · obtain ⟨g,hg,he⟩ := List.mem_flatten.mp he
    obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hg
    exact Or.inr ⟨⟨j,hj⟩,he⟩

theorem placedClauseGraph_endpoints {k : Nat} {f : CNF}
    {j : Fin (placeFormula [] f).length} {a b : Nat}
    (he : edge a b ∈ placedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]) :
    ClauseRegion k f j a ∧ ClauseRegion k f j b :=
  mapGraph_edge_endpoints (clauseGraph_below k _) _ he

theorem regions_intersection {k : Nat} {f : CNF} {v : Nat}
    (hv : v < variableBound f) {j : Fin (placeFormula [] f).length} {x : Nat}
    (hxv : VariableRegion k v x) (hxc : ClauseRegion k f j x) :
    ∃ i p side, i < 3 ∧ (placeFormula [] f)[j.val][i]? = some p ∧
      v = p.literal.var ∧
      x = blockVertex (gadgetWidth k) v (variableEndpoint p.port side) := by
  obtain ⟨a,ha,hxa⟩ := hxv
  obtain ⟨b,hb,hxb⟩ := hxc
  obtain ⟨p,side,hp,hv',ha'⟩ := variable_clause_vertex_intersection
    (by have := gadgetWidth_ge k; omega) hv ha hb (hxa.symm.trans hxb)
  obtain ⟨i,hi,hip,_⟩ := attachmentAt_spec.mp hp
  exact ⟨i,p,orientSide p side,hi,hip,hv',hxa.trans (congrArg _ ha')⟩

theorem clause_edge_between_variable_regions {k : Nat} {f : CNF}
    (hf : BoundedOccurrence f) {v w a b : Nat}
    (hv : v < variableBound f) (hw : w < variableBound f)
    {j : Fin (placeFormula [] f).length}
    (he : edge a b ∈ placedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val])
    (ha : VariableRegion k v a) (hb : VariableRegion k w b) :
    v = w ∧ edge a b ∈ placedVariableGraph k v := by
  obtain ⟨u,hu,hau⟩ := ha
  obtain ⟨t,ht,hbt⟩ := hb
  obtain ⟨ce,hce,heq⟩ := List.mem_map.mp he
  have hcb := clauseGraph_below k _ ce hce
  have hwidth : 7 ≤ gadgetWidth k := by have := gadgetWidth_ge k; omega
  have hboth : (∃ p s, attachmentAt (placeFormula [] f)[j.val] ce.1 = some (p,s)) ∧
      (∃ q s, attachmentAt (placeFormula [] f)[j.val] ce.2 = some (q,s)) := by
    rcases (edge_eq_iff ..).mp heq with ⟨h1,h2⟩ | ⟨h2,h1⟩
    · obtain ⟨p,s,hp,_,_⟩ := variable_clause_vertex_intersection hwidth hv hu hcb.1
        (hau.symm.trans h1.symm)
      obtain ⟨q,r,hq,_,_⟩ := variable_clause_vertex_intersection hwidth hw ht hcb.2
        (hbt.symm.trans h2.symm)
      exact ⟨⟨p,s,hp⟩,⟨q,r,hq⟩⟩
    · obtain ⟨p,s,hp,_,_⟩ := variable_clause_vertex_intersection hwidth hw ht hcb.1
        (hbt.symm.trans h2.symm)
      obtain ⟨q,r,hq,_,_⟩ := variable_clause_vertex_intersection hwidth hv hu hcb.2
        (hau.symm.trans h1.symm)
      exact ⟨⟨p,s,hp⟩,⟨q,r,hq⟩⟩
  obtain ⟨⟨p,s,hp⟩,⟨q,r,hq⟩⟩ := hboth
  have hm := clauseGraph_attachment_edge hce hp hq
  obtain ⟨i,heport,hleft⟩ := (by decide : ∀ e ∈ clausePorts, ∃ i : Fin 3,
    e = edge (clauseEndpoint i.val false) (clauseEndpoint i.val true) ∧
    e.1 = clauseEndpoint i.val false) ce hm
  rw [hleft, attachmentAt_endpoint i.isLt false] at hp
  have hcp : (placeFormula [] f)[j.val][i.val]? = some p := by
    cases h : (placeFormula [] f)[j.val][i.val]? with
    | none => simp [h] at hp
    | some t =>
      have hsame : t = p := by simpa [h] using congrArg (Option.map Prod.fst) hp
      simp [hsame]
  have hport := (hf.placed_clause_bounds (List.getElem_mem j.isLt) p (List.mem_of_getElem? hcp)).2
  have hep : edge a b ∈ placedVariableGraph k p.literal.var := by
    apply List.mem_map.mpr
    refine ⟨_,variableGraph_ports k hport,?_⟩
    rw [← mapped_attachment_edge i.isLt hcp, ← heport]
    exact heq
  have hends := placedVariableGraph_endpoints hep
  have hvp : v = p.literal.var := (show VariableRegion k v a from ⟨u,hu,hau⟩).unique hends.1
  have hwp : w = p.literal.var := (show VariableRegion k w b from ⟨t,ht,hbt⟩).unique hends.2
  exact ⟨hvp.trans hwp.symm,hvp ▸ hep⟩

/-- A global edge whose endpoints are in variable regions stays in a single
variable gadget. There are no one-edge shortcuts between variables. -/
theorem formulaGraph_between_variables {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {v w a b : Nat} (hv : v < variableBound f) (hw : w < variableBound f)
    (he : edge a b ∈ formulaGraph k f)
    (ha : VariableRegion k v a) (hb : VariableRegion k w b) :
    v = w ∧ edge a b ∈ placedVariableGraph k v := by
  rcases formulaGraph_edge_cases he with ⟨z,_,hz⟩ | ⟨j,hj⟩
  · have hends := placedVariableGraph_endpoints hz
    have hvz := ha.unique hends.1
    have hwz := hb.unique hends.2
    exact ⟨hvz.trans hwz.symm,hvz ▸ hz⟩
  · exact clause_edge_between_variable_regions hf hv hw hj ha hb

end STACS2027.Oriented
