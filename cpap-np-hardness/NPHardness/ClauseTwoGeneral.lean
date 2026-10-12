module

public import NPHardness.ClauseTwoProfileArithmetic
public import NPHardness.ClauseTwoProfileCertificates

/-! General-k cycle classification of Figure 4(c), including k=6. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

/-- Every k-cycle in the two-literal gadget arises from a base five-cycle. -/
theorem clauseTwo_projects_to_five {k : Nat} (hk : 5 ≤ k) {c : Cycle}
    (hc : IsCycle (clauseTwoGraph k) k c) :
    ∃ d, IsCycle clauseTwoSkeleton 5 d ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 24 (clauseTwoLinks k)))) := by
  obtain ⟨r, d, hd, hp⟩ := clauseTwo_cycle_projection hc
  have hlen := hp.length_eq
  simp only [hc.edge_length, List.length_flatMap] at hlen
  change k = expandedLength (linkSteps 24 (clauseTwoLinks k)) d at hlen
  rw [clauseTwo_expanded_length k hd] at hlen
  have hrle : r ≤ 5 := by
    by_cases h : r ≤ 5
    · exact h
    have hg := clauseTwo_long_cycle_uses_green hd (by omega)
    have hm : k - 5 ≤ colourCount clauseTwoGreen d * (k - 5) := by
      simpa using Nat.mul_le_mul_right (k - 5) hg
    simp only [profileLength, clauseTwoProfile, hd.2.1] at hlen
    omega
  have hr : r = 5 := by
    by_cases h : r = 5
    · exact h
    have hrs : r = 3 ∨ r = 4 := by have := hd.1; omega
    obtain ⟨e, he, hs⟩ := isCycle_represented hd
    have hec := enumerated_isCycle he
    have hmem : e ∈ cycles clauseTwoSkeleton 3 ++ cycles clauseTwoSkeleton 4 := by
      rcases hrs with rfl | rfl
      · exact List.mem_append_left _ he
      · exact List.mem_append_right _ he
    have hprofile := clauseTwo_short_profile_certificate e hmem
    have hperm := hp.trans ((hs.edge_perm hd hec).flatMap_right
      (expandedEdge (linkSteps 24 (clauseTwoLinks k))))
    have he_len := hperm.length_eq
    simp only [hc.edge_length, List.length_flatMap] at he_len
    change k = expandedLength (linkSteps 24 (clauseTwoLinks k)) e at he_len
    rw [clauseTwo_expanded_length k hec] at he_len
    exact False.elim (clauseTwo_profiles_excluded hk _ hprofile he_len.symm)
  rw [hr] at hd
  exact ⟨d, hd, hp⟩

theorem clauseTwo_skeleton_eq_five : clauseTwoSkeleton = clauseTwoGraph 5 := rfl

theorem clauseTwo_general_cycle_classification {k : Nat} (hk : 5 ≤ k) {c : Cycle}
    (hc : IsCycle (clauseTwoGraph k) k c) :
    ∃ d ∈ clauseTwoCycles5,
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 24 (clauseTwoLinks k)))) := by
  obtain ⟨d, hd, hp⟩ := clauseTwo_projects_to_five hk hc
  obtain ⟨e, he, hs⟩ := isCycle_represented hd
  rw [clauseTwo_skeleton_eq_five, clauseTwo5_enumeration] at he
  have hec := clauseTwo5_cycles_valid e he
  exact ⟨e, he, hp.trans ((hs.edge_perm hd hec).flatMap_right _)⟩

theorem clauseTwo_five_profiles : ∀ c ∈ clauseTwoCycles5,
    clauseTwoProfile c = ⟨5,1,0,0,0⟩ ∨ clauseTwoProfile c = ⟨5,0,1,1,1⟩ := by decide

theorem clauseTwo_five_expanded {k : Nat} (hk : 5 ≤ k) (d : Cycle) (hd : d ∈ clauseTwoCycles5) :
    expandedLength (linkSteps 24 (clauseTwoLinks k)) d = k := by
  rw [clauseTwo_expanded_length k (clauseTwo5_cycles_valid d hd)]
  rcases clauseTwo_five_profiles d hd with h | h <;> rw [h]
  · simp [profileLength]; omega
  · by_cases h6 : k = 6
    · subst k; decide
    · simp [profileLength, orangeSubdivisions, blueSubdivisions, redSubdivisions, h6]
      omega

theorem clauseTwo_general_cycle_realization {k : Nat} (hk : 5 ≤ k) (d : Cycle)
    (hd : d ∈ clauseTwoCycles5) :
    ∃ c, IsCycle (clauseTwoGraph k) k c ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 24 (clauseTwoLinks k)))) := by
  obtain ⟨hb, hn, hp⟩ := clauseTwo_links_wellformed k
  have hv := linkSteps_from_base_valid 24 (clauseTwoLinks k) hb hn hp
  have hdc := clauseTwo5_cycles_valid d hd
  obtain ⟨r, c, hc, hperm⟩ := subdivision_cycle_lift _ _ hv hdc
  have hlen := hperm.length_eq
  simp only [hc.edge_length, List.length_flatMap] at hlen
  change r = expandedLength (linkSteps 24 (clauseTwoLinks k)) d at hlen
  rw [clauseTwo_five_expanded hk d hd] at hlen
  rw [hlen] at hc
  refine ⟨c, ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩, hperm⟩
  intro e he
  exact (realizeLinks_membership 24 (clauseTwoLinks k) hb hn hp e).mp (hc.2.2.2 e he)

end STACS2027
