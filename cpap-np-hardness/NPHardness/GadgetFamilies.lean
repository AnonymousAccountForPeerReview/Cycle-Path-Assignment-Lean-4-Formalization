module

public import NPHardness.GadgetPrivateEdges
public import NPHardness.FamilyCost

/-! Explicitly specified representative families for every k ≥ 5. Choice
selects a vertex-list orientation; the graph constructors are computable. -/

@[expose] public section
namespace STACS2027

noncomputable def variableExpansion (k : Nat) (hk : 5 ≤ k) (d : Cycle) : Cycle :=
  if hd : d ∈ variableSkeletonInputs then
    Classical.choose (variable_general_cycle_realization hk d hd) else []

noncomputable def clauseThreeExpansion (k : Nat) (hk : 5 ≤ k) (d : Cycle) : Cycle :=
  if hd : d ∈ clauseThreeCycles5 then
    Classical.choose (clauseThree_general_cycle_realization hk d hd) else []

noncomputable def clauseTwoExpansion (k : Nat) (hk : 5 ≤ k) (d : Cycle) : Cycle :=
  if hd : d ∈ clauseTwoCycles5 then
    Classical.choose (clauseTwo_general_cycle_realization hk d hd) else []

theorem variableExpansion_spec {k : Nat} (hk : 5 ≤ k) {d : Cycle} (hd : d ∈ variableSkeletonInputs) :
    IsCycle (variableGraph k) k (variableExpansion k hk d) ∧
      (cycleEdges (variableExpansion k hk d)).Perm
        ((cycleEdges d).flatMap (expandedEdge (linkSteps 7 (variableLinks k)))) := by
  simpa only [variableExpansion, dite_eq_left hd] using
    Classical.choose_spec (variable_general_cycle_realization hk d hd)

theorem clauseThreeExpansion_spec {k : Nat} (hk : 5 ≤ k) {d : Cycle} (hd : d ∈ clauseThreeCycles5) :
    IsCycle (clauseThreeGraph k) k (clauseThreeExpansion k hk d) ∧
      (cycleEdges (clauseThreeExpansion k hk d)).Perm
        ((cycleEdges d).flatMap (expandedEdge (linkSteps 18 (clauseThreeLinks k)))) := by
  simpa only [clauseThreeExpansion, dite_eq_left hd] using
    Classical.choose_spec (clauseThree_general_cycle_realization hk d hd)

theorem clauseTwoExpansion_spec {k : Nat} (hk : 5 ≤ k) {d : Cycle} (hd : d ∈ clauseTwoCycles5) :
    IsCycle (clauseTwoGraph k) k (clauseTwoExpansion k hk d) ∧
      (cycleEdges (clauseTwoExpansion k hk d)).Perm
        ((cycleEdges d).flatMap (expandedEdge (linkSteps 24 (clauseTwoLinks k)))) := by
  simpa only [clauseTwoExpansion, dite_eq_left hd] using
    Classical.choose_spec (clauseTwo_general_cycle_realization hk d hd)

theorem variableExpansion_complete {k : Nat} (hk : 5 ≤ k) {c : Cycle}
    (hc : IsCycle (variableGraph k) k c) :
    ∃ d ∈ variableSkeletonInputs, SameCycle c (variableExpansion k hk d) := by
  obtain ⟨d, hd, hp⟩ := variable_general_cycle_classification hk hc
  have hs := hp.trans (variableExpansion_spec hk hd).2.symm
  exact ⟨d, hd, ⟨fun _ he => hs.mem_iff.mp he, fun _ he => hs.mem_iff.mpr he⟩⟩

theorem clauseThreeExpansion_complete {k : Nat} (hk : 5 ≤ k) {c : Cycle}
    (hc : IsCycle (clauseThreeGraph k) k c) :
    ∃ d ∈ clauseThreeCycles5, SameCycle c (clauseThreeExpansion k hk d) := by
  obtain ⟨d, hd, hp⟩ := clauseThree_general_cycle_classification hk hc
  have hs := hp.trans (clauseThreeExpansion_spec hk hd).2.symm
  exact ⟨d, hd, ⟨fun _ he => hs.mem_iff.mp he, fun _ he => hs.mem_iff.mpr he⟩⟩

theorem clauseTwoExpansion_complete {k : Nat} (hk : 5 ≤ k) {c : Cycle}
    (hc : IsCycle (clauseTwoGraph k) k c) :
    ∃ d ∈ clauseTwoCycles5, SameCycle c (clauseTwoExpansion k hk d) := by
  obtain ⟨d, hd, hp⟩ := clauseTwo_general_cycle_classification hk hc
  have hs := hp.trans (clauseTwoExpansion_spec hk hd).2.symm
  exact ⟨d, hd, ⟨fun _ he => hs.mem_iff.mp he, fun _ he => hs.mem_iff.mpr he⟩⟩

theorem expansion_sameCycle_reflect {g : Graph} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) {r s : Nat} {c d c' d' : Cycle}
    (hc : IsCycle g r c) (hd : IsCycle g s d)
    (hp : (cycleEdges c').Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    (hq : (cycleEdges d').Perm ((cycleEdges d).flatMap (expandedEdge ss)))
    (hs : SameCycle c' d') : SameCycle c d := by
  constructor
  · apply expandedEdges_subset_reflect hv hc.2.2.2 hd.2.2.2
    intro e he
    exact hq.mem_iff.mp (hs.1 e (hp.mem_iff.mpr he))
  · apply expandedEdges_subset_reflect hv hd.2.2.2 hc.2.2.2
    intro e he
    exact hp.mem_iff.mp (hs.2 e (hq.mem_iff.mpr he))

theorem variableExpansion_distinct {k : Nat} (hk : 5 ≤ k) :
    (variableSkeletonInputs.map (variableExpansion k hk)).Pairwise (fun c d => ¬ SameCycle c d) := by
  rw [List.pairwise_map]
  have hn : variableSkeletonInputs.Pairwise (fun c d => ¬ SameCycle c d) := by decide
  apply hn.imp_of_mem
  intro c d hc hd hne hs
  obtain ⟨hb, hn, hnl⟩ := variable_links_wellformed k
  apply hne
  exact expansion_sameCycle_reflect (linkSteps_from_base_valid 7 (variableLinks k) hb hn hnl)
    (variableSkeleton_cycles_valid c (variableSkeletonInputs_subset hc))
    (variableSkeleton_cycles_valid d (variableSkeletonInputs_subset hd))
    (variableExpansion_spec hk hc).2 (variableExpansion_spec hk hd).2 hs

theorem clauseThreeExpansion_distinct {k : Nat} (hk : 5 ≤ k) :
    (clauseThreeCycles5.map (clauseThreeExpansion k hk)).Pairwise (fun c d => ¬ SameCycle c d) := by
  rw [List.pairwise_map]
  apply clauseThree5_distinct.imp_of_mem
  intro c d hc hd hne hs
  obtain ⟨hb, hn, hnl⟩ := clauseThree_links_wellformed k
  apply hne
  exact expansion_sameCycle_reflect (linkSteps_from_base_valid 18 (clauseThreeLinks k) hb hn hnl)
    (clauseThree5_cycles_valid c hc) (clauseThree5_cycles_valid d hd)
    (clauseThreeExpansion_spec hk hc).2 (clauseThreeExpansion_spec hk hd).2 hs

theorem clauseTwoExpansion_distinct {k : Nat} (hk : 5 ≤ k) :
    (clauseTwoCycles5.map (clauseTwoExpansion k hk)).Pairwise (fun c d => ¬ SameCycle c d) := by
  rw [List.pairwise_map]
  apply clauseTwo5_distinct.imp_of_mem
  intro c d hc hd hne hs
  obtain ⟨hb, hn, hnl⟩ := clauseTwo_links_wellformed k
  apply hne
  exact expansion_sameCycle_reflect (linkSteps_from_base_valid 24 (clauseTwoLinks k) hb hn hnl)
    (clauseTwo5_cycles_valid c hc) (clauseTwo5_cycles_valid d hd)
    (clauseTwoExpansion_spec hk hc).2 (clauseTwoExpansion_spec hk hd).2 hs

end STACS2027
