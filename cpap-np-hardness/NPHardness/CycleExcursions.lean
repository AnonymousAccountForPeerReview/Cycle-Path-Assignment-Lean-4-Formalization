module

public import NPHardness.ClauseRegions

/-! A cycle containing a private clause vertex cannot leave that clause. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem IsSimplePath.excursion {g : Graph} {a b : Nat} {p : List Nat}
    (hp : IsSimplePath g a b p) (S : Nat → Prop) (ha : S a) (hb : S b)
    (hout : ∃ x ∈ p, ¬ S x) :
    ∃ u v q, IsSimplePath g u v q ∧ 3 ≤ q.length ∧ q.length ≤ p.length ∧
      S u ∧ S v ∧ (∀ x ∈ q, S x → x = u ∨ x = v) := by
  classical
  cases p with
  | nil => exact False.elim (hp.ne_nil rfl)
  | cons start xs =>
    have hstart : start = a := by simpa using hp.2.1
    subst start
    have hout' : ∃ x ∈ xs, ¬ S x := by
      obtain ⟨x,hx,hn⟩ := hout
      rcases List.mem_cons.mp hx with rfl | hx
      · exact False.elim (hn ha)
      · exact ⟨x,hx,hn⟩
    obtain ⟨pre,u,z,post,heq,hpre,hz⟩ := list_first_exit S ha hout'
    have hlast : (z :: post).getLast? = some b := by
      have h := hp.2.2.1
      rw [heq] at h
      simpa using h
    have hbmem := List.mem_of_getLast? hlast
    have hpost : ∃ x ∈ post, ¬ ¬ S x := by
      rcases List.mem_cons.mp hbmem with h | h
      · exact False.elim (hz (h ▸ hb))
      · exact ⟨b,h,fun hn => hn hb⟩
    obtain ⟨middle,t,v,suf,hmid,hinside,hv⟩ := list_first_exit (fun x => ¬ S x) hz hpost
    have hs : a :: xs = pre ++ (u :: (middle ++ [t]) ++ [v]) ++ suf := by
      rw [heq,hmid]
      simp [List.append_assoc]
    have hinfix : List.IsInfix (u :: (middle ++ [t]) ++ [v]) (a :: xs) := ⟨pre,suf,hs.symm⟩
    refine ⟨u,v,u :: (middle ++ [t]) ++ [v],hp.infix hinfix (by simp)
      (List.getLast?_concat),?_,
      hinfix.sublist.length_le,hpre u (by simp),Classical.not_not.mp hv,?_⟩
    · simp
    · intro x hx hS
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with (h | h) | h
      · exact Or.inl h
      · exact False.elim (hinside x (by simpa using h) hS)
      · exact Or.inr h

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

theorem IsCycle.tail_path {g : Graph} {r z : Nat} {rest : List Nat}
    (hc : IsCycle g r (z :: rest)) :
    ∃ a b, IsSimplePath g a b rest ∧ edge z a ∈ g ∧ edge z b ∈ g := by
  have hlen := hc.2.1
  have hr := hc.1
  cases rest with
  | nil => simp at hlen; omega
  | cons a tail =>
    have htail : tail ≠ [] := by intro h; simp [h] at hlen; omega
    obtain hempty | ⟨middle,b,hb⟩ := List.eq_nil_or_concat tail
    · exact False.elim (htail hempty)
    simp only [List.concat_eq_append] at hb
    refine ⟨a,b,⟨(List.nodup_cons.mp hc.2.2.1).2,rfl,?_,?_⟩,?_,?_⟩
    · rw [hb]
      change ((a :: middle) ++ [b]).getLast? = some b
      exact List.getLast?_concat
    · intro e he
      apply hc.2.2.2 e
      apply pathEdges_subset_append _ _ e
      exact pathEdges_suffix [z] (a :: tail) he
    · exact hc.2.2.2 _ (by simp [cycleEdges,pathEdges])
    · apply hc.2.2.2
      rw [hb]
      change edge z b ∈ cycleEdges (z :: ((a :: middle) ++ [b]))
      rw [cycleEdges_snoc]
      simp [edge_comm]

/-- The central global separation theorem for cycles meeting a private clause
vertex. Every vertex of a k-cycle through such a vertex lies in that clause. -/
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

end STACS2027
