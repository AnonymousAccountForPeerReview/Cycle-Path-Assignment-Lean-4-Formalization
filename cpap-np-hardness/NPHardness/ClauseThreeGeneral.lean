module

public import NPHardness.GadgetProjection
public import NPHardness.Acyclic

/-! General-k cycle classification of the 3-literal clause gadget (Step 2, Figure 4(b)). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

def clauseThreeGreen : List Edge :=
  [(0,12), (1,2), (2,3), (5,6), (7,8), (8,9), (9,10)]

def clauseThreeNonGreen : Graph := clauseThree5.filter fun e => !clauseThreeGreen.contains e

def clauseThreeTreeRank (v : Nat) : Nat :=
  [0,1,3,5,6,7,9,10,10,8,4,3,4,1,2,7,8,9][v]!

def greenCount (c : Cycle) : Nat :=
  ((cycleEdges c).filter clauseThreeGreen.contains).length

theorem clauseThree_rank_certificate : ∀ v a b : Fin 18,
    edge v.val a.val ∈ clauseThreeNonGreen → edge v.val b.val ∈ clauseThreeNonGreen →
    clauseThreeTreeRank a.val ≤ clauseThreeTreeRank v.val →
    clauseThreeTreeRank b.val ≤ clauseThreeTreeRank v.val → a = b := by decide

theorem clauseThree_nonGreen_rank : AcyclicRank clauseThreeNonGreen clauseThreeTreeRank := by
  intro v a b ha hb hra hrb
  have hbound := (clauseThree_links_wellformed 5).1
  have hba := (edge_below v a 18).mp (hbound _ (List.mem_filter.mp ha).1)
  have hbb := (edge_below v b 18).mp (hbound _ (List.mem_filter.mp hb).1)
  have h := clauseThree_rank_certificate ⟨v, hba.1⟩ ⟨a, hba.2⟩ ⟨b, hbb.2⟩ ha hb hra hrb
  exact congrArg Fin.val h

theorem clauseThree_nonGreen_acyclic : ∀ r c, ¬ IsCycle clauseThreeNonGreen r c :=
  clauseThree_nonGreen_rank.no_cycle

theorem clauseThree_cycle_uses_green {r : Nat} {c : Cycle} (hc : IsCycle clauseThree5 r c) :
    1 ≤ greenCount c := by
  classical
  have hex : ∃ e ∈ cycleEdges c, e ∈ clauseThreeGreen := by
    by_cases h : ∃ e ∈ cycleEdges c, e ∈ clauseThreeGreen
    · exact h
    apply False.elim
    apply clauseThree_nonGreen_acyclic r c
    refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
    intro e he
    apply List.mem_filter.mpr
    exact ⟨hc.2.2.2 e he, by simpa using (fun hg => h ⟨e, he, hg⟩)⟩
  obtain ⟨e, he, hg⟩ := hex
  have hmem : e ∈ (cycleEdges c).filter clauseThreeGreen.contains := by simp [he, hg]
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)

theorem clauseThree_no_triangles : cycles clauseThree5 3 = [] := by decide
theorem clauseThree_no_quadrangles : cycles clauseThree5 4 = [] := by decide

theorem clauseThree_girth_five {r : Nat} {c : Cycle} (hc : IsCycle clauseThree5 r c) : 5 ≤ r := by
  have hk := hc.1
  by_cases h : 5 ≤ r
  · exact h
  · have hr : r = 3 ∨ r = 4 := by omega
    obtain ⟨d, hd, _⟩ := isCycle_represented hc
    rcases hr with rfl | rfl
    · simp [clauseThree_no_triangles] at hd
    · simp [clauseThree_no_quadrangles] at hd

theorem clauseThree_edge_expanded_length (k : Nat) (e : Edge) (he : e ∈ clauseThree5) :
    (expandedEdge (linkSteps 18 (clauseThreeLinks k)) e).length =
      1 + if e ∈ clauseThreeGreen then k - 5 else 0 := by
  obtain ⟨hb, hn, hp⟩ := clauseThree_links_wellformed k
  have hmem : e ∈ linkEdges (clauseThreeLinks k) := he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem
  have h := linkSteps_edge_length 18 (clauseThreeLinks k) hb hn hp l hl
  simp only [clauseThreeLinks, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simpa [clauseThreeGreen, edge, Nat.add_comm] using h

theorem sum_edge_weights (es : List Edge) (p : Edge → Bool) (t : Nat) :
    (es.map fun e => 1 + if p e then t else 0).sum = es.length + (es.filter p).length * t := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    cases h : p e <;> simp [h, Nat.add_mul] <;> omega

theorem clauseThree_expanded_length (k : Nat) {r : Nat} {c : Cycle} (hc : IsCycle clauseThree5 r c) :
    expandedLength (linkSteps 18 (clauseThreeLinks k)) c = r + greenCount c * (k - 5) := by
  unfold expandedLength
  have hm : (cycleEdges c).map (fun e => (expandedEdge (linkSteps 18 (clauseThreeLinks k)) e).length) =
      (cycleEdges c).map (fun e => 1 + if clauseThreeGreen.contains e then k - 5 else 0) := by
    apply List.map_congr_left
    intro e he
    simpa using clauseThree_edge_expanded_length k e (hc.2.2.2 e he)
  rw [hm, sum_edge_weights, hc.edge_length]
  rfl

/-- Every k-cycle projects to a base five-cycle; no longer base cycle can create
an additional k-cycle under the prescribed green-edge subdivisions. -/
theorem clauseThree_projects_to_five {k : Nat} (hk : 5 ≤ k) {c : Cycle}
    (hc : IsCycle (clauseThreeGraph k) k c) :
    ∃ d, IsCycle clauseThree5 5 d ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 18 (clauseThreeLinks k)))) := by
  obtain ⟨r, d, hd, hp⟩ := clauseThree_cycle_projection hc
  have hlen := hp.length_eq
  simp only [hc.edge_length, List.length_flatMap] at hlen
  change k = expandedLength (linkSteps 18 (clauseThreeLinks k)) d at hlen
  rw [clauseThree_expanded_length k hd] at hlen
  have hgreen := clauseThree_cycle_uses_green hd
  have hmin := clauseThree_girth_five hd
  have hm : k - 5 ≤ greenCount d * (k - 5) := by
    simpa using Nat.mul_le_mul_right (k - 5) hgreen
  have hr : r = 5 := by omega
  subst r
  exact ⟨d, hd, hp⟩

theorem clauseThree_general_cycle_classification {k : Nat} (hk : 5 ≤ k) {c : Cycle}
    (hc : IsCycle (clauseThreeGraph k) k c) :
    ∃ d ∈ clauseThreeCycles5,
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 18 (clauseThreeLinks k)))) := by
  obtain ⟨d, hd, hp⟩ := clauseThree_projects_to_five hk hc
  obtain ⟨e, he, hs⟩ := isCycle_represented hd
  rw [clauseThree5_enumeration] at he
  have hec := clauseThree5_cycles_valid e he
  exact ⟨e, he, hp.trans ((hs.edge_perm hd hec).flatMap_right _)⟩

theorem clauseThree_five_green_count : ∀ c ∈ clauseThreeCycles5, greenCount c = 1 := by decide

/-- Every one of the seven base cycles actually yields a k-cycle. -/
theorem clauseThree_general_cycle_realization {k : Nat} (hk : 5 ≤ k) (d : Cycle)
    (hd : d ∈ clauseThreeCycles5) :
    ∃ c, IsCycle (clauseThreeGraph k) k c ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 18 (clauseThreeLinks k)))) := by
  obtain ⟨hb, hn, hp⟩ := clauseThree_links_wellformed k
  have hv := linkSteps_from_base_valid 18 (clauseThreeLinks k) hb hn hp
  have hdc := clauseThree5_cycles_valid d hd
  obtain ⟨r, c, hc, hperm⟩ := subdivision_cycle_lift _ _ hv hdc
  have hlen := hperm.length_eq
  simp only [hc.edge_length, List.length_flatMap] at hlen
  change r = expandedLength (linkSteps 18 (clauseThreeLinks k)) d at hlen
  rw [clauseThree_expanded_length k hdc, clauseThree_five_green_count d hd, Nat.one_mul] at hlen
  have hr : r = k := by omega
  rw [hr] at hc
  refine ⟨c, ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩, hperm⟩
  intro e he
  exact (realizeLinks_membership 18 (clauseThreeLinks k) hb hn hp e).mp (hc.2.2.2 e he)

end STACS2027
