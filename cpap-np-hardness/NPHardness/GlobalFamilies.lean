module

public import NPHardness.AssignmentFamilies
public import NPHardness.ClauseTwo6

/-! A complete, nonduplicated representative family for the global graph. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

noncomputable def variableFamily (k : Nat) (hk : 5 ≤ k) : List Cycle :=
  variableSkeletonInputs.map (variableExpansion k hk)

noncomputable def clauseFamily (k : Nat) (hk : 5 ≤ k) (c : List PlacedLiteral) : List Cycle :=
  if c.length = 2 then
    if k = 6 then clauseTwoCycles6 else clauseTwoCycles5.map (clauseTwoExpansion k hk)
  else clauseThreeCycles5.map (clauseThreeExpansion k hk)

theorem variableFamily_valid {k : Nat} (hk : 5 ≤ k) :
    ∀ c ∈ variableFamily k hk, IsCycle (variableGraph k) k c := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  exact (variableExpansion_spec hk hd).1

theorem variableFamily_complete {k : Nat} (hk : 5 ≤ k) {c : Cycle}
    (hc : IsCycle (variableGraph k) k c) : ∃ d ∈ variableFamily k hk, SameCycle c d := by
  obtain ⟨d,hd,he⟩ := variableExpansion_complete hk hc
  exact ⟨_,List.mem_map.mpr ⟨d,hd,rfl⟩,he⟩

theorem clauseFamily_valid {k : Nat} (hk : 5 ≤ k) (c : List PlacedLiteral) :
    ∀ d ∈ clauseFamily k hk c, IsCycle (clauseGraph k c) k d := by
  unfold clauseFamily clauseGraph
  split
  · split
    · next h6 => subst k; exact clauseTwo6_cycles_valid
    · intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact (clauseTwoExpansion_spec hk he).1
  · intro d hd
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
    exact (clauseThreeExpansion_spec hk he).1

theorem clauseFamily_distinct {k : Nat} (hk : 5 ≤ k) (c : List PlacedLiteral) :
    (clauseFamily k hk c).Pairwise (fun d e => ¬ SameCycle d e) := by
  unfold clauseFamily
  split
  · split
    · exact clauseTwo6_distinct
    · exact clauseTwoExpansion_distinct hk
  · exact clauseThreeExpansion_distinct hk

theorem clauseFamily_complete {k : Nat} (hk : 5 ≤ k) (c : List PlacedLiteral) {d : Cycle}
    (hd : IsCycle (clauseGraph k c) k d) : ∃ e ∈ clauseFamily k hk c, SameCycle d e := by
  unfold clauseGraph at hd
  unfold clauseFamily
  split at hd
  · next hc =>
      rw [ite_eq_left hc]
      split
      · next h6 =>
          subst k
          obtain ⟨e,he,hs⟩ := isCycle_represented hd
          rw [clauseTwo6_enumeration] at he
          exact ⟨e,he,hs⟩
      · obtain ⟨e,he,hs⟩ := clauseTwoExpansion_complete hk hd
        exact ⟨_,List.mem_map.mpr ⟨e,he,rfl⟩,hs⟩
  · next hc =>
      rw [ite_eq_right hc]
      obtain ⟨e,he,hs⟩ := clauseThreeExpansion_complete hk hd
      exact ⟨_,List.mem_map.mpr ⟨e,he,rfl⟩,hs⟩

theorem SameCycle.map {c d : Cycle} (hs : SameCycle c d) (t : Nat → Nat) :
    SameCycle (c.map t) (d.map t) := by
  constructor <;> intro e he <;> rw [cycleEdges_map] at he ⊢
  · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
    exact List.mem_map.mpr ⟨x,hs.1 x hx,rfl⟩
  · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
    exact List.mem_map.mpr ⟨x,hs.2 x hx,rfl⟩

theorem sameCycle_map_reflect {g : Graph} {n r s : Nat} (hb : VerticesBelow g n)
    (hn : ∀ e ∈ g, edge e.1 e.2 = e) (t : Nat → Nat)
    (hi : ∀ a, a < n → ∀ b, b < n → t a = t b → a = b)
    {c d : Cycle} (hc : IsCycle g r c) (hd : IsCycle g s d)
    (hs : SameCycle (c.map t) (d.map t)) : SameCycle c d := by
  have hsub : ∀ {c d : Cycle}, (∀ e ∈ cycleEdges c, e ∈ g) →
      (∀ e ∈ cycleEdges d, e ∈ g) →
      (∀ e ∈ cycleEdges (c.map t), e ∈ cycleEdges (d.map t)) →
      ∀ e ∈ cycleEdges c, e ∈ cycleEdges d := by
    intro c d hc hd h e he
    have hm := h (mapEdge t e) (by rw [cycleEdges_map]; exact List.mem_map.mpr ⟨e,he,rfl⟩)
    rw [cycleEdges_map] at hm
    obtain ⟨e',he',heq⟩ := List.mem_map.mp hm
    have hee := mapEdge_injective_on hb hn t hi (hd e' he') (hc e he) heq
    exact hee ▸ he'
  exact ⟨hsub hc.2.2.2 hd.2.2.2 hs.1,hsub hd.2.2.2 hc.2.2.2 hs.2⟩

theorem mapped_family_distinct {g : Graph} {n k : Nat} {cs : List Cycle}
    (hb : VerticesBelow g n) (hn : ∀ e ∈ g, edge e.1 e.2 = e)
    (hc : ∀ c ∈ cs, IsCycle g k c) (hcs : cs.Pairwise (fun c d => ¬ SameCycle c d))
    (t : Nat → Nat) (hi : ∀ a, a < n → ∀ b, b < n → t a = t b → a = b) :
    (cs.map (List.map t)).Pairwise (fun c d => ¬ SameCycle c d) := by
  rw [List.pairwise_map]
  apply hcs.imp_of_mem
  intro c d hcm hdm hne hs
  exact hne (sameCycle_map_reflect hb hn t hi (hc c hcm) (hc d hdm) hs)

theorem clauseGraph_normalized (k : Nat) (c : List PlacedLiteral) :
    ∀ e ∈ clauseGraph k c, edge e.1 e.2 = e := by
  unfold clauseGraph
  split
  · exact realizeLinks_normalized _ _
  · exact realizeLinks_normalized _ _

noncomputable def placedVariableFamily (k : Nat) (hk : 5 ≤ k) (v : Nat) : List Cycle :=
  (variableFamily k hk).map (List.map (blockVertex (gadgetWidth k) v))

noncomputable def placedClauseFamily (k : Nat) (hk : 5 ≤ k) (n j : Nat)
    (c : List PlacedLiteral) : List Cycle :=
  (clauseFamily k hk c).map (List.map (clauseVertex (gadgetWidth k) n j c))

noncomputable def formulaFamily (k : Nat) (hk : 5 ≤ k) (f : CNF) : List Cycle :=
  (List.range (variableBound f)).flatMap (placedVariableFamily k hk) ++
    ((placeFormula [] f).mapIdx (fun j c => placedClauseFamily k hk (variableBound f) j c)).flatten

theorem placedVariableFamily_valid {k v : Nat} (hk : 5 ≤ k) :
    ∀ c ∈ placedVariableFamily k hk v, IsCycle (placedVariableGraph k v) k c := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have h := variableFamily_valid hk d hd
  exact h.map _ (fun a ha b hb he => (blockVertex_injective
    (h.vertex_bound (variableGraph_below k) a ha) (h.vertex_bound (variableGraph_below k) b hb) he).2)

theorem placedClauseFamily_valid {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (j : Fin (placeFormula [] f).length) :
    ∀ c ∈ placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val],
      IsCycle (placedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]) k c := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have h := clauseFamily_valid hk _ d hd
  exact h.map _ (fun a ha b hb he => clauseVertex_injective
    (by have := gadgetWidth_ge k; omega) (hf.placed_clause_nodup (List.getElem_mem j.isLt))
    (hf.placed_clause_bounds (List.getElem_mem j.isLt))
    (h.vertex_bound (clauseGraph_below k _) a ha) (h.vertex_bound (clauseGraph_below k _) b hb) he)

theorem formulaFamily_valid {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f) :
    ∀ c ∈ formulaFamily k hk f, IsCycle (formulaGraph k f) k c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨v,hv,hc⟩ := List.mem_flatMap.mp hc
    exact (placedVariableFamily_valid hk c hc).graph_mono (formulaGraph_variable_contains k f (List.mem_range.mp hv))
  · obtain ⟨cs,hcs,hc⟩ := List.mem_flatten.mp hc
    obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hcs
    exact (placedClauseFamily_valid hk hf ⟨j,hj⟩ c hc).graph_mono (formulaGraph_clause_contains k f j hj)

theorem formulaFamily_complete {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f) {c : Cycle}
    (hc : IsCycle (formulaGraph k f) k c) :
    ∃ d ∈ formulaFamily k hk f, SameCycle c d := by
  rcases formulaGraph_cycle_local hk hf hd hc with ⟨v,hv,hc⟩ | ⟨j,hc⟩
  · obtain ⟨d,hd,rfl⟩ := IsCycle.unmap (variableGraph_below k)
      (realizeLinks_normalized 7 (variableLinks k)) (blockVertex (gadgetWidth k) v)
      (fun a ha b hb he => (blockVertex_injective ha hb he).2) hc
    obtain ⟨e,he,hs⟩ := variableFamily_complete hk hd
    refine ⟨e.map (blockVertex (gadgetWidth k) v),?_,hs.map _⟩
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨v,List.mem_range.mpr hv,List.mem_map.mpr ⟨e,he,rfl⟩⟩
  · obtain ⟨d,hd,rfl⟩ := IsCycle.unmap (clauseGraph_below k _) (clauseGraph_normalized k _)
      (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val])
      (fun a ha b hb he => clauseVertex_injective (by have := gadgetWidth_ge k; omega)
        (hf.placed_clause_nodup (List.getElem_mem j.isLt))
        (hf.placed_clause_bounds (List.getElem_mem j.isLt)) ha hb he) hc
    obtain ⟨e,he,hs⟩ := clauseFamily_complete hk _ hd
    refine ⟨e.map (clauseVertex (gadgetWidth k) (variableBound f) j.val (placeFormula [] f)[j.val]),?_,hs.map _⟩
    apply List.mem_append_right
    apply List.mem_flatten.mpr
    exact ⟨_,List.mem_mapIdx.mpr ⟨j.val,j.isLt,rfl⟩,List.mem_map.mpr ⟨e,he,rfl⟩⟩

end STACS2027
