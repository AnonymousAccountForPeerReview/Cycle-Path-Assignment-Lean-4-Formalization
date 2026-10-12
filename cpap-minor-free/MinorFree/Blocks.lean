module

public import MinorFree.Elimination
public import MinorFree.K4

/-!
Combining assignments over edge-disjoint parts: when every cycle of a graph
lies within one of a list of pairwise edge-disjoint subgraphs (its blocks),
assignments of the parts combine to an assignment of the whole graph of the
summed cost. With Lemma 25 and the `K₄` assignment this gives Theorem 20.
-/

@[expose] public section
namespace STACS2027

theorem cycleEdges_nonempty {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) :
    ∃ e, e ∈ cycleEdges c := by
  have hl := hc.2.1
  have hk := hc.1
  cases c with
  | nil => simp at hl; omega
  | cons a rest =>
    cases rest with
    | nil => simp at hl; omega
    | cons b rest => exact ⟨edge a b, by simp [cycleEdges, pathEdges]⟩

/-- Assignments of two edge-disjoint graphs, every cycle of whose union lies in one of them,
combine to an assignment of the union with the summed budget. -/
theorem hasAssignment_disjoint_union {g₁ g₂ : Graph} {k b₁ b₂ : Nat}
    (hdisj : ∀ e ∈ g₁, e ∉ g₂)
    (hsplit : ∀ c, IsCycle (g₁ ++ g₂) k c →
      (∀ e ∈ cycleEdges c, e ∈ g₁) ∨ (∀ e ∈ cycleEdges c, e ∈ g₂))
    (h₁ : HasAssignment g₁ k b₁) (h₂ : HasAssignment g₂ k b₂) :
    HasAssignment (g₁ ++ g₂) k (b₁ + b₂) := by
  have hc₁ : ∀ c ∈ cycles g₁ k, IsCycle g₁ k c := fun c hc => enumerated_isCycle hc
  have hc₂ : ∀ c ∈ cycles g₂ k, IsCycle g₂ k c := fun c hc => enumerated_isCycle hc
  -- No cycle of `g₁` is a cycle of `g₂`.
  have hcross : ∀ c, IsCycle g₁ k c → ∀ d, IsCycle g₂ k d → ¬ SameCycle c d := by
    intro c hc d hd hs
    obtain ⟨e, he⟩ := cycleEdges_nonempty hc
    exact hdisj e (hc.2.2.2 e he) (hd.2.2.2 e (hs.1 e he))
  have hc : ∀ c ∈ cycles g₁ k ++ cycles g₂ k, IsCycle (g₁ ++ g₂) k c := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact (hc₁ c h).graph_mono (fun e he => List.mem_append_left _ he)
    · exact (hc₂ c h).graph_mono (fun e he => List.mem_append_right _ he)
  have hn : (cycles g₁ k ++ cycles g₂ k).Pairwise (fun c d => ¬ SameCycle c d) := by
    apply List.pairwise_append.mpr
    refine ⟨cycles_pairwise_different g₁ k, cycles_pairwise_different g₂ k, ?_⟩
    intro c hcm d hdm
    exact hcross c (hc₁ c hcm) d (hc₂ d hdm)
  have hcover : ∀ c, IsCycle (g₁ ++ g₂) k c → ∃ d ∈ cycles g₁ k ++ cycles g₂ k, SameCycle c d := by
    intro c hcc
    rcases hsplit c hcc with h | h
    · obtain ⟨d, hd, hs⟩ := isCycle_represented ⟨hcc.1, hcc.2.1, hcc.2.2.1, h⟩
      exact ⟨d, List.mem_append_left _ hd, hs⟩
    · obtain ⟨d, hd, hs⟩ := isCycle_represented ⟨hcc.1, hcc.2.1, hcc.2.2.1, h⟩
      exact ⟨d, List.mem_append_right _ hd, hs⟩
  rw [hasAssignment_iff_complete_family hc hn hcover]
  obtain ⟨choose₁, hchoose₁, hcost₁⟩ := (hasAssignment_iff_enumerated_family g₁ k b₁).mp h₁
  obtain ⟨choose₂, hchoose₂, hcost₂⟩ := (hasAssignment_iff_enumerated_family g₂ k b₂).mp h₂
  refine ⟨fun c => if c ∈ cycles g₁ k then choose₁ c else choose₂ c, ?_, ?_⟩
  · intro c hcm
    by_cases h : c ∈ cycles g₁ k
    · simp only [h, ↓reduceIte]; exact hchoose₁ c h
    · simp only [h, ↓reduceIte]
      rcases List.mem_append.mp hcm with h' | h'
      · exact absurd h' h
      · exact hchoose₂ c h'
  · have hnot : ∀ c ∈ cycles g₂ k, c ∉ cycles g₁ k :=
      fun c hcm h => hcross c (hc₁ c h) c (hc₂ c hcm) (SameCycle.refl c)
    rw [List.map_append, cost_append]
    have e₁ : (cycles g₁ k).map (fun c => selectedAt c (if c ∈ cycles g₁ k then choose₁ c else choose₂ c)) =
        (cycles g₁ k).map (fun c => selectedAt c (choose₁ c)) :=
      List.map_congr_left (fun c hcm => by simp [hcm])
    have e₂ : (cycles g₂ k).map (fun c => selectedAt c (if c ∈ cycles g₁ k then choose₁ c else choose₂ c)) =
        (cycles g₂ k).map (fun c => selectedAt c (choose₂ c)) :=
      List.map_congr_left (fun c hcm => by simp [hnot c hcm])
    rw [e₁, e₂]
    have hzero : crossCost ((cycles g₁ k).map fun c => selectedAt c (choose₁ c))
        ((cycles g₂ k).map fun c => selectedAt c (choose₂ c)) = 0 := by
      apply (crossCost_zero_iff _ _).mpr
      intro p hp q hq
      obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hp
      obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hq
      apply overlap_eq_zero_of_disjoint
      intro e he heq
      exact hdisj e ((hc₁ c hcm).2.2.2 e (selectedAt_mem.mp he).1)
        ((hc₂ d hdm).2.2.2 e (selectedAt_mem.mp heq).1)
    rw [hzero]
    omega

/-- Blocks: a list of pairwise edge-disjoint graphs. -/
def EdgeDisjoint (blocks : List Graph) : Prop :=
  blocks.Pairwise fun g h => ∀ e ∈ g, e ∉ h

/-- Every `k`-cycle of the union of the blocks lies within one block (as every cycle of a
graph lies within one of its 2-connected blocks). -/
def CyclesInBlocks (blocks : List Graph) (k : Nat) : Prop :=
  ∀ c, IsCycle blocks.flatten k c → ∃ b ∈ blocks, ∀ e ∈ cycleEdges c, e ∈ b

theorem mem_flatten_block {blocks : List Graph} {e : Edge} (he : e ∈ blocks.flatten) :
    ∃ b ∈ blocks, e ∈ b := by
  obtain ⟨b, hb, he⟩ := List.mem_flatten.mp he
  exact ⟨b, hb, he⟩

/-- Assignments of the blocks combine to an assignment of the whole graph with the summed
budget. -/
theorem hasAssignment_blocks {blocks : List Graph} {k : Nat} (budget : Graph → Nat)
    (hdisj : EdgeDisjoint blocks) (hsplit : CyclesInBlocks blocks k)
    (hb : ∀ b ∈ blocks, HasAssignment b k (budget b)) :
    HasAssignment blocks.flatten k (blocks.map budget).sum := by
  induction blocks with
  | nil =>
    refine ⟨[], ?_, Nat.le_refl _⟩
    have : cycles ([] : List Graph).flatten k = [] := by
      cases h : cycles ([] : List Graph).flatten k with
      | nil => rfl
      | cons c cs =>
        have hc := enumerated_isCycle (h ▸ List.mem_cons_self : c ∈ cycles ([] : List Graph).flatten k)
        obtain ⟨e, he⟩ := cycleEdges_nonempty hc
        have := hc.2.2.2 e he
        simp at this
    rw [this]; trivial
  | cons b rest ih =>
    obtain ⟨hdb, hdrest⟩ := List.pairwise_cons.mp hdisj
    simp only [List.flatten_cons, List.map_cons, List.sum_cons]
    have hdisj' : ∀ e ∈ b, e ∉ rest.flatten := by
      intro e he hin
      obtain ⟨b', hb', he'⟩ := mem_flatten_block hin
      exact hdb b' hb' e he he'
    apply hasAssignment_disjoint_union hdisj' _ (hb b (by simp))
    · apply ih hdrest _ (fun b' hb' => hb b' (by simp [hb']))
      intro c hc
      have hc' : IsCycle (b ++ rest.flatten) k c :=
        hc.graph_mono (fun e he => List.mem_append_right _ he)
      obtain ⟨b', hb', hin⟩ := hsplit c (by simpa using hc')
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exfalso
        obtain ⟨e, he⟩ := cycleEdges_nonempty hc
        exact hdisj' e (hin e he) (hc.2.2.2 e he)
      · exact ⟨b', hb', hin⟩
    · intro c hc
      obtain ⟨b', hb', hin⟩ := hsplit c (by simpa using hc)
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact Or.inl hin
      · exact Or.inr (fun e he => List.mem_flatten.mpr ⟨b', hb', hin e he⟩)

/-- A block as Lemma 19 describes it: outerplanar — formalized by a degree-two elimination
order and the common-neighbour bound of Lemma 24 — or a copy of `K₄`. -/
def OuterplanarOrK4 (b : Graph) : Prop :=
  ((∃ rank, EliminationOrder b rank) ∧ CommonNeighbourBound b) ∨ IsK4 b

/-- **Theorem 20** (on the block structure): a graph whose four-cycles lie within pairwise
edge-disjoint blocks, each outerplanar (with an elimination order and the common-neighbour
bound) or a copy of `K₄` — as the blocks of every `K_{2,3}`-minor-free graph are, by
Lemma 19 — admits a perfect cycle-path assignment for `k = 4`. -/
theorem perfect_assignment_of_blocks {blocks : List Graph} (hdisj : EdgeDisjoint blocks)
    (hsplit : CyclesInBlocks blocks 4) (hb : ∀ b ∈ blocks, OuterplanarOrK4 b) :
    HasAssignment blocks.flatten 4 0 := by
  have h := hasAssignment_blocks (fun _ => 0) hdisj hsplit (fun b hbm => ?_)
  · simpa using h
  · rcases hb b hbm with ⟨⟨rank, ho⟩, hc⟩ | hk4
    · exact perfect_four_cycle_assignment ho hc
    · exact hk4.perfect

end STACS2027
