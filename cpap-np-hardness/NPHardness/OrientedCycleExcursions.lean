module

public import NPHardness.OrientedClauseRegions

/-! A cycle containing a private clause vertex cannot leave that clause. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

theorem clause_excursion_start_variable {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {j : Fin (placeFormula [] f).length} {a b : Nat} {p : List Nat}
    (hp : IsSimplePath (formulaGraph k f) a b p) (hl : 3 ≤ p.length)
    (ha : ClauseRegion k f j a)
    (hint : ∀ x ∈ p, ClauseRegion k f j x → x = a ∨ x = b) :
    ∃ v, v < variableBound f ∧ VariableRegion k v a := by
  cases p with
  | nil => simp at hl
  | cons x xs =>
    have hxa : x = a := by simpa using hp.2.1
    subst x
    cases xs with
    | nil => simp at hl
    | cons y ys =>
      have hepath : edge a y ∈ pathEdges (a :: y :: ys) := by simp [pathEdges]
      have he := hp.2.2.2 _ hepath
      have hy : ¬ ClauseRegion k f j y := by
        intro h
        rcases hint y (by simp) h with h | h
        · exact (List.nodup_cons.mp hp.1).1 (by simp [h])
        · exact path_endpoint_edge_absent hp hl (h ▸ hepath)
      rcases formulaGraph_edge_cases he with ⟨v,hv,hev⟩ | ⟨i,hei⟩
      · exact ⟨v,hv,(placedVariableGraph_endpoints hev).1⟩
      · have hends := placedClauseGraph_endpoints hei
        have h := ha.unique hf hends.1
        exact False.elim (hy (h ▸ hends.2))

theorem clause_excursion_length {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f)
    {j : Fin (placeFormula [] f).length} {a b : Nat} {p : List Nat}
    (hp : IsSimplePath (formulaGraph k f) a b p) (hl : 3 ≤ p.length)
    (ha : ClauseRegion k f j a) (hb : ClauseRegion k f j b)
    (hint : ∀ x ∈ p, ClauseRegion k f j x → x = a ∨ x = b) :
    k - 1 ≤ (pathEdges p).length := by
  classical
  obtain ⟨v,hv,hav⟩ := clause_excursion_start_variable hf hp hl ha hint
  obtain ⟨w,hw,hbw⟩ := clause_excursion_start_variable hf hp.reverse (by simpa using hl) hb (by
    intro x hx hc
    exact (hint x (by simpa using hx) hc).symm)
  by_cases hall : ∀ x ∈ p, VariableRegion k v x
  · exact clause_excursion_one_variable_bound hk hf hd hv hp hl ha hb hall
  · have hout : ∃ x ∈ p, ¬ VariableRegion k v x := by
      obtain ⟨x,hx⟩ := Classical.not_forall.mp hall
      exact ⟨x,not_imp.mp hx⟩
    have h := clause_excursion_crossing_bound hk hf hv hw hp ha hb hint hav hbw hout
    omega

theorem formulaGraph_cycle_private_clause {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f)
    {j : Fin (placeFormula [] f).length} {c : Cycle}
    (hc : IsCycle (formulaGraph k f) k c) {z : Nat} (hz : z ∈ c)
    (hprivate : PrivateClauseVertex k f j z) : ∀ x ∈ c, ClauseRegion k f j x := by
  classical
  obtain ⟨rest,hr,_,hperm⟩ := hc.rotate_to_vertex hz
  obtain ⟨a,b,hpath,hea,heb⟩ := hr.tail_path
  have ha := private_clause_neighbor hf hprivate hea
  have hb := private_clause_neighbor hf hprivate heb
  intro x hx
  by_cases h : ClauseRegion k f j x
  · exact h
  · have hxrest : x ∈ rest := by
      have hm := hperm.mem_iff.mp hx
      rcases List.mem_cons.mp hm with rfl | hm
      · exact False.elim (h hprivate.1)
      · exact hm
    obtain ⟨u,v,q,hq,hq3,hql,hu,hv,hint⟩ := hpath.excursion (ClauseRegion k f j) ha hb ⟨x,hxrest,h⟩
    have hbound := clause_excursion_length hk hf hd hq hq3 hu hv hint
    have hlen := hr.2.1
    rw [pathEdges_length] at hbound
    simp only [List.length_cons] at hlen
    omega

end STACS2027.Oriented
