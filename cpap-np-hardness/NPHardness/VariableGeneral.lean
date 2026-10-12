module

public import NPHardness.GadgetProjection

/-! General-k cycle classification of Figure 4(a). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

def variableSkeletonCycles : List Cycle :=
  [[0,1,4,3], [1,2,6,5,4], [0,1,2,6,5,4,3]]

def variableSkeletonInputs : List Cycle := [[0,1,4,3], [1,2,6,5,4]]

theorem variableSkeletonInputs_subset : variableSkeletonInputs ⊆ variableSkeletonCycles := by decide

theorem variableSkeleton_enumeration :
    (List.range 8).flatMap (cycles variableSkeleton) = variableSkeletonCycles := by decide

theorem variableSkeleton_cycles_valid : ∀ c ∈ variableSkeletonCycles,
    IsCycle variableSkeleton c.length c := by decide

theorem variableSkeleton_represents {r : Nat} {c : Cycle} (hc : IsCycle variableSkeleton r c) :
    ∃ d ∈ variableSkeletonCycles, IsCycle variableSkeleton r d ∧ SameCycle c d := by
  have hb : VerticesBelow variableSkeleton 7 := (variable_links_wellformed 0).1
  have hr := hc.length_le_bound hb
  obtain ⟨d, hd, hs⟩ := isCycle_represented hc
  refine ⟨d, ?_, enumerated_isCycle hd, hs⟩
  rw [← variableSkeleton_enumeration]
  exact List.mem_flatMap.mpr ⟨r, List.mem_range.mpr (by omega), hd⟩

def variableWeight (k : Nat) (e : Edge) : Nat :=
  if e = (0,1) then (k-1)/2 else
  if e = (1,2) then (k-3)/2 else
  if e = (3,4) ∨ e = (5,6) then (k-2)/2 else 1

theorem variable_edge_expanded_length {k : Nat} (hk : 5 ≤ k) (e : Edge) (he : e ∈ variableSkeleton) :
    (expandedEdge (linkSteps 7 (variableLinks k)) e).length = variableWeight k e := by
  obtain ⟨hb, hn, hp⟩ := variable_links_wellformed k
  have hmem : e ∈ linkEdges (variableLinks k) := he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem
  have h := linkSteps_edge_length 7 (variableLinks k) hb hn hp l hl
  simp only [variableLinks, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only at h
  all_goals rw [h]
  all_goals simp [variableWeight, edge]
  all_goals omega

theorem variable_expanded_length {k : Nat} (hk : 5 ≤ k) {r : Nat} {c : Cycle}
    (hc : IsCycle variableSkeleton r c) :
    expandedLength (linkSteps 7 (variableLinks k)) c = ((cycleEdges c).map (variableWeight k)).sum := by
  unfold expandedLength
  congr 1
  apply List.map_congr_left
  intro e he
  exact variable_edge_expanded_length hk e (hc.2.2.2 e he)

theorem variable_input_lengths {k : Nat} (hk : 5 ≤ k) :
    ∀ c ∈ variableSkeletonInputs, expandedLength (linkSteps 7 (variableLinks k)) c = k := by
  intro c hc
  have hmem : c ∈ variableSkeletonCycles := variableSkeletonInputs_subset hc
  have hv := variableSkeleton_cycles_valid c hmem
  rw [variable_expanded_length hk hv]
  simp only [variableSkeletonInputs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [cycleEdges, pathEdges, variableWeight, edge] <;> omega

theorem variable_outer_length {k : Nat} (hk : 5 ≤ k) :
    expandedLength (linkSteps 7 (variableLinks k)) [0,1,2,6,5,4,3] = 2*k - 2 := by
  have hv := variableSkeleton_cycles_valid [0,1,2,6,5,4,3] (by simp [variableSkeletonCycles])
  rw [variable_expanded_length hk hv]
  simp [cycleEdges, pathEdges, variableWeight, edge]
  omega

/-- Only the two intended cycles survive at length k. The third skeleton cycle
has expanded length 2k-2, which is strictly larger than k for k ≥ 5. -/
theorem variable_general_cycle_classification {k : Nat} (hk : 5 ≤ k) {c : Cycle}
    (hc : IsCycle (variableGraph k) k c) :
    ∃ d ∈ variableSkeletonInputs,
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 7 (variableLinks k)))) := by
  obtain ⟨r, d, hd, hp⟩ := variable_cycle_projection hc
  obtain ⟨e, he, hec, hs⟩ := variableSkeleton_represents hd
  have hperm := hp.trans ((hs.edge_perm hd hec).flatMap_right (expandedEdge (linkSteps 7 (variableLinks k))))
  have hlen := hperm.length_eq
  simp only [hc.edge_length, List.length_flatMap] at hlen
  change k = expandedLength (linkSteps 7 (variableLinks k)) e at hlen
  simp only [variableSkeletonCycles, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨_, by simp [variableSkeletonInputs], hperm⟩
  · exact ⟨_, by simp [variableSkeletonInputs], hperm⟩
  · rw [variable_outer_length hk] at hlen
    omega

theorem variable_general_cycle_realization {k : Nat} (hk : 5 ≤ k) (d : Cycle)
    (hd : d ∈ variableSkeletonInputs) :
    ∃ c, IsCycle (variableGraph k) k c ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 7 (variableLinks k)))) := by
  obtain ⟨hb, hn, hp⟩ := variable_links_wellformed k
  have hv := linkSteps_from_base_valid 7 (variableLinks k) hb hn hp
  have hmem : d ∈ variableSkeletonCycles := variableSkeletonInputs_subset hd
  have hdc := variableSkeleton_cycles_valid d hmem
  obtain ⟨r, c, hc, hperm⟩ := subdivision_cycle_lift _ _ hv hdc
  have hlen := hperm.length_eq
  simp only [hc.edge_length, List.length_flatMap] at hlen
  change r = expandedLength (linkSteps 7 (variableLinks k)) d at hlen
  rw [variable_input_lengths hk d hd] at hlen
  rw [hlen] at hc
  refine ⟨c, ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩, hperm⟩
  intro e he
  exact (realizeLinks_membership 7 (variableLinks k) hb hn hp e).mp (hc.2.2.2 e he)

end STACS2027
