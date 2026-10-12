module

public import NPHardness.ClauseTwoProfiles

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

/-- None of the other skeleton profiles can acquire length k. -/
theorem clauseTwo_profiles_excluded {k : Nat} (hk : 5 ≤ k) (p : CycleProfile)
    (hp : p ∈ clauseTwoExcludedProfiles) : profileLength k p ≠ k := by
  simp only [clauseTwoExcludedProfiles, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals by_cases h6 : k = 6
  all_goals simp [profileLength, orangeSubdivisions, blueSubdivisions, redSubdivisions, h6]
  all_goals omega

def clauseTwoWeight (k : Nat) (e : Edge) : Nat :=
  1 + (if e ∈ clauseTwoGreen then k-5 else 0) +
    (if e ∈ clauseTwoOrange then orangeSubdivisions k else 0) +
    (if e ∈ clauseTwoBlue then blueSubdivisions k else 0) +
    (if e ∈ clauseTwoRed then redSubdivisions k else 0)

theorem clauseTwo_edge_expanded_length (k : Nat) (e : Edge) (he : e ∈ clauseTwoSkeleton) :
    (expandedEdge (linkSteps 24 (clauseTwoLinks k)) e).length = clauseTwoWeight k e := by
  obtain ⟨hb, hn, hp⟩ := clauseTwo_links_wellformed k
  have hmem : e ∈ linkEdges (clauseTwoLinks k) := he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem
  have h := linkSteps_edge_length 24 (clauseTwoLinks k) hb hn hp l hl
  simp only [clauseTwoLinks, clauseThreeLinks, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simpa [clauseTwoWeight, clauseTwoGreen, clauseThreeGreen, clauseTwoOrange,
    clauseTwoBlue, clauseTwoRed, edge, Nat.add_comm] using h

theorem sum_colour_weight (es : List Edge) (p : Edge → Bool) (t : Nat) :
    (es.map fun e => if p e then t else 0).sum = (es.filter p).length * t := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    cases h : p e <;> simp [h, Nat.add_mul] <;> omega

theorem clauseTwo_expanded_length (k : Nat) {r : Nat} {c : Cycle} (hc : IsCycle clauseTwoSkeleton r c) :
    expandedLength (linkSteps 24 (clauseTwoLinks k)) c = profileLength k (clauseTwoProfile c) := by
  unfold expandedLength
  have hm : (cycleEdges c).map (fun e => (expandedEdge (linkSteps 24 (clauseTwoLinks k)) e).length) =
      (cycleEdges c).map (clauseTwoWeight k) := by
    apply List.map_congr_left
    intro e he
    exact clauseTwo_edge_expanded_length k e (hc.2.2.2 e he)
  rw [hm]
  change ((cycleEdges c).map (fun e =>
    1 + (if e ∈ clauseTwoGreen then k-5 else 0) +
      (if e ∈ clauseTwoOrange then orangeSubdivisions k else 0) +
      (if e ∈ clauseTwoBlue then blueSubdivisions k else 0) +
      (if e ∈ clauseTwoRed then redSubdivisions k else 0))).sum = _
  simp only [sum_map_add, sum_map_const, Nat.mul_one]
  have hf : ∀ es : List Edge, ∀ t : Nat,
      ((cycleEdges c).map fun e => if e ∈ es then t else 0).sum = colourCount es c * t := by
    intro es t
    simpa only [List.contains_iff_mem, colourCount] using sum_colour_weight (cycleEdges c) es.contains t
  simp only [hf, hc.edge_length, profileLength, clauseTwoProfile, hc.2.1]

end STACS2027
