module

public import NPHardness.GlobalFamilies

/-! Uniqueness of the global cycle family, including variable/clause pairs. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem cycles_different_of_disjoint_graphs {g h : Graph}
    (hg : ∀ e ∈ g, e ∉ h) {r s : Nat} {c d : Cycle}
    (hc : IsCycle g r c) (hd : IsCycle h s d) : ¬ SameCycle c d := by
  intro hs
  cases c with
  | nil => have h := hc.2.1; have hr := hc.1; simp at h; omega
  | cons a cs =>
    obtain ⟨b,_,he⟩ := hc.vertex_incident (by simp : a ∈ a :: cs)
    exact hg _ (hc.2.2.2 _ he) (hd.2.2.2 _ (hs.1 _ he))

theorem variable_clause_cycles_different {k : Nat} {f : CNF}
    (hd : ClauseVariablesDistinct f) {v : Nat} (hv : v < variableBound f)
    {j : Fin (placeFormula [] f).length} {c d : Cycle}
    (hc : IsCycle (placedVariableGraph k v) k c)
    (hdc : IsCycle (placedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]) k d) :
    ¬ SameCycle c d := by
  intro hs
  have hregions : ∀ x ∈ c, VariableRegion k v x ∧ ClauseRegion k f j x := by
    intro x hx
    obtain ⟨y,_,he⟩ := hc.vertex_incident hx
    exact ⟨(placedVariableGraph_endpoints (hc.2.2.2 _ he)).1,
      (placedClauseGraph_endpoints (hdc.2.2.2 _ (hs.1 _ he))).1⟩
  cases c with
  | nil => have h := hc.2.1; have hk := hc.1; simp at h; omega
  | cons a cs =>
    obtain ⟨i,p,s,_,hip,hvp,_⟩ := regions_intersection hv (hregions a (by simp)).1 (hregions a (by simp)).2
    let ends := [blockVertex (gadgetWidth k) v (variableEndpoint p.port false),
      blockVertex (gadgetWidth k) v (variableEndpoint p.port true)]
    have hsub : a :: cs ⊆ ends := by
      intro x hx
      obtain ⟨r,q,t,_,hrq,hvq,hex⟩ := regions_intersection hv (hregions x hx).1 (hregions x hx).2
      have hpq := nodup_map_injective_on (fun p : PlacedLiteral => p.literal.var)
        (hd.placed (List.getElem_mem j.isLt)) (List.mem_of_getElem? hip) (List.mem_of_getElem? hrq)
        (hvp.symm.trans hvq)
      subst q
      cases t <;> simp [ends,hex]
    have hlen := List.Nodup.length_le_of_subset hc.2.2.1 hsub
    have hk := hc.1
    have he := hc.2.1
    simp only [ends,List.length_cons,List.length_nil] at hlen he
    omega

theorem placedVariableFamily_distinct {k v : Nat} (hk : 5 ≤ k) :
    (placedVariableFamily k hk v).Pairwise (fun c d => ¬ SameCycle c d) :=
  mapped_family_distinct (variableGraph_below k) (realizeLinks_normalized 7 (variableLinks k))
    (variableFamily_valid hk) (variableExpansion_distinct hk) _
    (fun _ ha _ hb he => (blockVertex_injective ha hb he).2)

theorem placedClauseFamily_distinct {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (j : Fin (placeFormula [] f).length) :
    (placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val]).Pairwise
      (fun c d => ¬ SameCycle c d) :=
  mapped_family_distinct (clauseGraph_below k _) (clauseGraph_normalized k _)
    (clauseFamily_valid hk _) (clauseFamily_distinct hk _) _
    (fun _ ha _ hb he => clauseVertex_injective (by have := gadgetWidth_ge k; omega)
      (hf.placed_clause_nodup (List.getElem_mem j.isLt))
      (hf.placed_clause_bounds (List.getElem_mem j.isLt)) ha hb he)

theorem formulaFamily_distinct {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f) :
    (formulaFamily k hk f).Pairwise (fun c d => ¬ SameCycle c d) := by
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · apply List.pairwise_flatMap.mpr
    refine ⟨fun _ _ => placedVariableFamily_distinct hk,?_⟩
    apply (show (List.range (variableBound f)).Nodup from List.nodup_range).imp_of_mem
    intro v w _ _ hne c hc d hd
    exact cycles_different_of_disjoint_graphs (formulaGraph_variable_edges_disjoint k hne)
      (placedVariableFamily_valid hk c hc) (placedVariableFamily_valid hk d hd)
  · apply List.pairwise_flatten.mpr
    constructor
    · intro cs hcs
      obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hcs
      exact placedClauseFamily_distinct hk hf ⟨j,hj⟩
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      have hi' : i < (placeFormula [] f).length := by simpa using hi
      have hj' : j < (placeFormula [] f).length := by simpa using hj
      simp only [List.getElem_mapIdx]
      intro c hc d hd
      exact cycles_different_of_disjoint_graphs
        (formulaGraph_clause_edges_disjoint hf hi' hj' (by omega))
        (placedClauseFamily_valid hk hf ⟨i,hi'⟩ c hc) (placedClauseFamily_valid hk hf ⟨j,hj'⟩ d hd)
  · intro c hc d hd'
    obtain ⟨v,hv,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨cs,hcs,hd'⟩ := List.mem_flatten.mp hd'
    obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hcs
    exact variable_clause_cycles_different hd (List.mem_range.mp hv)
      (placedVariableFamily_valid hk c hc) (placedClauseFamily_valid hk hf ⟨j,hj⟩ d hd')

/-- This is the bridge from the executable CPAP decision predicate to the
complete global gadget family, with completeness and uniqueness proved. -/
theorem formulaGraph_assignment_iff_family {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f) (budget : Nat) :
    HasAssignment (formulaGraph k f) k budget ↔ FamilyAssignment (formulaFamily k hk f) budget :=
  hasAssignment_iff_complete_family (formulaFamily_valid hk hf) (formulaFamily_distinct hk hf hd)
    (fun _ hc => formulaFamily_complete hk hf hd hc)

end STACS2027
