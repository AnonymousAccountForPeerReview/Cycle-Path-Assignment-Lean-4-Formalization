module

public import NPHardness.CycleExcursions

/-! Global classification: gluing creates no additional k-cycles for clauses
with distinct variables. Both sides of the statement refer to the actual
formulaGraph constructor and its concrete embedded gadget copies. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem pathEdges_not_loop {p : List Nat} (hn : p.Nodup) (v : Nat) :
    edge v v ∉ pathEdges p := by
  induction p with
  | nil => simp [pathEdges]
  | cons a p ih =>
    cases p with
    | nil => simp [pathEdges]
    | cons b bs =>
      intro he
      rcases List.mem_cons.mp he with he | he
      · rcases (edge_eq_iff ..).mp he with ⟨ha,hb⟩ | ⟨hb,ha⟩
        all_goals exact (List.nodup_cons.mp hn).1 (by simp [← ha,← hb])
      · exact ih (List.nodup_cons.mp hn).2 he

theorem IsCycle.not_loop {g : Graph} {r : Nat} {c : Cycle}
    (hc : IsCycle g r c) (v : Nat) : edge v v ∉ cycleEdges c := by
  cases c with
  | nil => simp [cycleEdges,pathEdges]
  | cons a tail =>
    have htail : tail ≠ [] := by
      intro h
      have hlen := hc.2.1
      have hr := hc.1
      simp [h] at hlen
      omega
    obtain he | ⟨middle,b,hb⟩ := List.eq_nil_or_concat tail
    · exact False.elim (htail he)
    simp only [List.concat_eq_append] at hb
    intro he
    rw [hb,cycleEdges_snoc] at he
    rcases List.mem_append.mp he with he | he
    · exact pathEdges_not_loop (hb ▸ hc.2.2.1) v he
    · have heq : edge v v = edge b a := by simpa using he
      have hba : b = a := by rcases (edge_eq_iff ..).mp heq with h | h <;> omega
      exact (List.nodup_cons.mp hc.2.2.1).1 (by simp [hb,hba])

theorem IsCycle.edge_endpoints_ne {g : Graph} {r : Nat} {c : Cycle}
    (hc : IsCycle g r c) {e : Edge} (he : e ∈ cycleEdges c) : e.1 ≠ e.2 := by
  have hn := pathEdges_normalized (c ++ c.take 1) e he
  intro h
  apply hc.not_loop e.2
  have he' : edge e.1 e.2 ∈ cycleEdges c := by rw [hn]; exact he
  simpa only [h] using he'

theorem path_variable_region {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {v a : Nat} (hv : v < variableBound f) {xs : List Nat}
    (ha : VariableRegion k v a)
    (hcover : ∀ x ∈ a :: xs, ∃ w, w < variableBound f ∧ VariableRegion k w x)
    (he : ∀ e ∈ pathEdges (a :: xs), e ∈ formulaGraph k f) :
    ∀ x ∈ a :: xs, VariableRegion k v x := by
  induction xs generalizing a with
  | nil => simpa using ha
  | cons b bs ih =>
    obtain ⟨w,hw,hbw⟩ := hcover b (by simp)
    have heab := he (edge a b) (by simp [pathEdges])
    have hvw := (formulaGraph_between_variables hf hv hw heab ha hbw).1
    have hb : VariableRegion k v b := hvw ▸ hbw
    have ht := ih hb (fun x hx => hcover x (by simp [hx]))
      (fun e hem => he e (List.mem_cons_of_mem _ hem))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact ht x hx

/-- Every global k-cycle is wholly contained in one embedded gadget. The
distinct-variable condition is stated rather than silently added to Definition 7. -/
theorem formulaGraph_cycle_local {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f) {c : Cycle}
    (hc : IsCycle (formulaGraph k f) k c) :
    (∃ v, v < variableBound f ∧ IsCycle (placedVariableGraph k v) k c) ∨
    (∃ j : Fin (placeFormula [] f).length,
      IsCycle (placedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]) k c) := by
  classical
  by_cases hprivate : ∃ j : Fin (placeFormula [] f).length, ∃ z ∈ c, PrivateClauseVertex k f j z
  · obtain ⟨j,z,hz,hp⟩ := hprivate
    have hall := formulaGraph_cycle_private_clause hk hf hd hc hz hp
    refine Or.inr ⟨j,hc.1,hc.2.1,hc.2.2.1,?_⟩
    intro e he
    have hn := pathEdges_normalized (c ++ c.take 1) e he
    have hm := cycleEdges_endpoints he
    have heg : edge e.1 e.2 ∈ formulaGraph k f := by rw [hn]; exact hc.2.2.2 e he
    have h := formulaGraph_clause_induced hf hd (hc.edge_endpoints_ne he) heg (hall _ hm.1) (hall _ hm.2)
    simpa only [hn] using h
  · have hcover : ∀ x ∈ c, ∃ v, v < variableBound f ∧ VariableRegion k v x := by
      intro x hx
      obtain ⟨y,_,he⟩ := hc.vertex_incident hx
      rcases formulaGraph_edge_cases (hc.2.2.2 _ he) with ⟨v,hv,hev⟩ | ⟨j,hej⟩
      · exact ⟨v,hv,(placedVariableGraph_endpoints hev).1⟩
      · have hxc := (placedClauseGraph_endpoints hej).1
        by_cases h : ∃ v, v < variableBound f ∧ VariableRegion k v x
        · exact h
        · apply False.elim
          apply hprivate
          exact ⟨j,x,hx,hxc,fun v hv hxv => h ⟨v,hv,hxv⟩⟩
    cases c with
    | nil => have h := hc.2.1; have hk' := hc.1; simp at h; omega
    | cons a xs =>
      obtain ⟨v,hv,hav⟩ := hcover a (by simp)
      have hpath : ∀ e ∈ pathEdges (a :: xs), e ∈ formulaGraph k f :=
        fun e he => hc.2.2.2 e (pathEdges_subset_append _ _ e he)
      have hall := path_variable_region hf hv hav hcover hpath
      refine Or.inl ⟨v,hv,hc.1,hc.2.1,hc.2.2.1,?_⟩
      intro e he
      have hn := pathEdges_normalized ((a :: xs) ++ (a :: xs).take 1) e he
      have hm := cycleEdges_endpoints he
      have heg : edge e.1 e.2 ∈ formulaGraph k f := by rw [hn]; exact hc.2.2.2 e he
      have h := (formulaGraph_between_variables hf hv hv heg (hall _ hm.1) (hall _ hm.2)).2
      simpa only [hn] using h

theorem formulaGraph_cycle_local_iff {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f) (c : Cycle) :
    IsCycle (formulaGraph k f) k c ↔
    (∃ v, v < variableBound f ∧ IsCycle (placedVariableGraph k v) k c) ∨
    (∃ j : Fin (placeFormula [] f).length,
      IsCycle (placedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]) k c) := by
  constructor
  · exact formulaGraph_cycle_local hk hf hd
  · rintro (⟨v,hv,hc⟩ | ⟨j,hc⟩)
    · exact hc.graph_mono (formulaGraph_variable_contains k f hv)
    · exact hc.graph_mono (formulaGraph_clause_contains k f j.val j.isLt)

end STACS2027
