module

public import NPHardness.OrientedExcursionDistances

/-! The long-excursion argument in the glued graph. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

theorem variable_boundary_preserves_clause {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {j : Fin (placeFormula [] f).length} {v a b : Nat}
    (he : edge a b ∈ formulaGraph k f) (ha : VariableRegion k v a)
    (hb : ¬ VariableRegion k v b) (hc : ClauseRegion k f j a) : ClauseRegion k f j b := by
  rcases formulaGraph_edge_cases he with ⟨w,_,hw⟩ | ⟨i,hi⟩
  · have hends := placedVariableGraph_endpoints hw
    have h := ha.unique hends.1
    exact False.elim (hb (h ▸ hends.2))
  · have hends := placedClauseGraph_endpoints hi
    have h := hc.unique hf hends.1
    exact h ▸ hends.2

/-- An excursion out of a clause which leaves its starting variable gadget
has at least 2*floor((k-2)/2)+2 edges. Its internal vertices avoid the clause;
the conclusion concerns the concrete global graph. -/
theorem clause_excursion_crossing_bound {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) {j : Fin (placeFormula [] f).length}
    {v w a b : Nat} (hv : v < variableBound f) (hw : w < variableBound f)
    {p : List Nat} (hp : IsSimplePath (formulaGraph k f) a b p)
    (ha : ClauseRegion k f j a) (hb : ClauseRegion k f j b)
    (hint : ∀ x ∈ p, ClauseRegion k f j x → x = a ∨ x = b)
    (hav : VariableRegion k v a) (hbw : VariableRegion k w b)
    (hout : ∃ x ∈ p, ¬ VariableRegion k v x) :
    2 * ((k-2)/2) + 2 ≤ (pathEdges p).length := by
  cases p with
  | nil => exact False.elim (hp.ne_nil rfl)
  | cons start xs =>
    have hstart : start = a := by simpa using hp.2.1
    subst start
    have hout' : ∃ x ∈ xs, ¬ VariableRegion k v x := by
      obtain ⟨x,hx,hn⟩ := hout
      rcases List.mem_cons.mp hx with rfl | hx
      · exact False.elim (hn hav)
      · exact ⟨x,hx,hn⟩
    obtain ⟨pre,u,z,post,heq,hpre,hz⟩ := list_first_exit (VariableRegion k v) hav hout'
    have hp' : IsSimplePath (formulaGraph k f) a b (pre ++ [u] ++ z :: post) := heq ▸ hp
    have hu : VariableRegion k v u := hpre u (by simp)
    have heuz : edge u z ∈ formulaGraph k f := hp'.2.2.2 _ (by
      simp [List.append_assoc,pathEdges_bridge])
    have hzw : ¬ VariableRegion k w z := by
      intro h
      have hvw := (formulaGraph_between_variables hf hv hw heuz hu h).1
      exact hz (hvw ▸ h)
    have hhead : (pre ++ [u]).head? = some a := by
      have h := hp'.2.1
      cases pre <;> simpa using h
    have ham : a ∈ pre ++ [u] := List.mem_of_head? hhead
    have hzmem : z ∈ a :: xs := by rw [heq]; simp
    have hza : z ≠ a := by intro h; exact hz (h ▸ hav)
    have hzb : z ≠ b := by intro h; exact hzw (h ▸ hbw)
    have hzc : ¬ ClauseRegion k f j z := by
      intro h
      rcases hint z hzmem h with h | h
      · exact hza h
      · exact hzb h
    have huc : ¬ ClauseRegion k f j u :=
      fun h => hzc (variable_boundary_preserves_clause hf heuz hu hz h)
    have hprefix : IsSimplePath (formulaGraph k f) a u (pre ++ [u]) :=
      hp'.infix ⟨[],z :: post,rfl⟩ hhead (by simp)
    have hdleft := clause_exit_variable_distance hk hf hv hprefix hpre ha huc heuz hz
    have htailLast : (z :: post).getLast? = some b := by simpa using hp'.2.2.1
    have htailHead : (z :: post).reverse.head? = some b := by
      simpa only [← List.getLast?_eq_head?_reverse] using htailLast
    have htailNonempty : (z :: post).reverse ≠ [] := by simp
    obtain ⟨q,tail,hq⟩ := List.exists_cons_of_ne_nil htailNonempty
    have hqb : q = b := by simpa [hq] using htailHead
    subst q
    have htailOut : ∃ x ∈ tail, ¬ VariableRegion k w x := by
      have hzm : z ∈ b :: tail := by rw [← hq]; simp
      rcases List.mem_cons.mp hzm with h | h
      · exact False.elim (hzb h)
      · exact ⟨z,h,hzw⟩
    obtain ⟨suf,t,y,middle,hsplit,hsuf,hy⟩ :=
      list_first_exit (VariableRegion k w) hbw htailOut
    have hrev : (z :: post).reverse = suf ++ [t] ++ y :: middle := hq.trans hsplit
    have htrev : z :: post = (suf ++ [t] ++ y :: middle).reverse :=
      List.reverse_eq_iff.mp hrev
    have ht : VariableRegion k w t := hsuf t (by simp)
    have hrevFull : (pre ++ [u] ++ z :: post).reverse =
        (suf ++ [t] ++ y :: middle) ++ (pre ++ [u]).reverse := by
      rw [List.reverse_append,hrev]
    have hrevPath := hp'.reverse
    rw [hrevFull] at hrevPath
    have hety : edge t y ∈ formulaGraph k f := hrevPath.2.2.2 _ (by
      apply pathEdges_subset_append _ _ _
      simp [List.append_assoc,pathEdges_bridge])
    have hymn : y ∈ z :: post := by rw [← List.mem_reverse,hrev]; simp
    have hym : y ∈ a :: xs := by rw [heq]; simp [hymn]
    have hya : y ≠ a := by
      intro h
      have hn := (List.nodup_append.mp hp'.1).2.2
      exact hn a ham y hymn h.symm
    have hyb : y ≠ b := by intro h; exact hy (h ▸ hbw)
    have hyc : ¬ ClauseRegion k f j y := by
      intro h
      rcases hint y hym h with h | h
      · exact hya h
      · exact hyb h
    have htc : ¬ ClauseRegion k f j t :=
      fun h => hyc (variable_boundary_preserves_clause hf hety ht hy h)
    have hsufhead : (suf ++ [t]).head? = some b := by
      have h := hrevPath.2.1
      cases suf <;> simpa using h
    have hsuffix : IsSimplePath (formulaGraph k f) b t (suf ++ [t]) :=
      hrevPath.infix ⟨[],(y :: middle) ++ (pre ++ [u]).reverse,by simp [List.append_assoc]⟩
        hsufhead (by simp)
    have hdright := clause_exit_variable_distance hk hf hw hsuffix hsuf hb htc hety hy
    have hlen1 := congrArg List.length heq
    have hlen2 := congrArg List.length hrev
    simp only [List.length_append,List.length_cons,List.length_nil,List.length_reverse] at hlen1 hlen2
    simp only [pathEdges_length,List.length_append,List.length_cons,List.length_nil] at hdleft hdright ⊢
    omega

end STACS2027.Oriented
