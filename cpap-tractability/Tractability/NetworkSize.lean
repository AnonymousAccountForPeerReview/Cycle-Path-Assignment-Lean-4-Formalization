module

public import Tractability.FlowTools

/-!
# The size of the network

With `t` four-cycles, the network has exactly `2t` source arcs, `4t` pair arcs and
`4t` sink arcs, so `10t` arcs in all; its nodes are `s`, `z`, the `2t` pair nodes
and at most `4t` edge nodes; every arc has capacity one and cost less than `t`.
This is the `O(t)` size used in the running-time bound of Theorem 2.
-/

@[expose] public section
namespace STACS2027

theorem pairLayer_length (t : Nat) (C : Nat → Cycle)
    (hlen : ∀ i, i < t → ∀ p, (opposingPair (C i) p).length = 2) :
    (pairLayer t C).length = 4 * t := by
  simp only [pairLayer, List.length_flatMap, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_append, List.length_map]
  have : ((List.range t).map fun i =>
      (opposingPair (C i) false).length + (opposingPair (C i) true).length) =
      (List.range t).map fun _ => 4 := by
    apply List.map_congr_left
    intro i hi
    rw [hlen i (List.mem_range.mp hi) false, hlen i (List.mem_range.mp hi) true]
  rw [this, sum_map_const, List.length_range]
  omega

theorem sinkLayer_length (es : List Edge) (w : Edge → Nat) :
    (sinkLayer es w).length = (es.map w).sum := by
  simp only [sinkLayer, List.length_flatMap, List.length_map, List.length_range]

theorem length_eraseDups_le {α : Type} [BEq α] (l : List α) : l.eraseDups.length ≤ l.length := by
  match l with
  | [] => simp
  | a :: l =>
    rw [List.eraseDups_cons]
    have h₁ : (l.filter fun b => !b == a).length < (a :: l).length :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) (by simp)
    have h₂ := length_eraseDups_le (l.filter fun b => !b == a)
    simp only [List.length_cons] at h₁ ⊢
    omega
termination_by l.length

theorem cycleEdgeList_length_le (g : Graph) : (cycleEdgeList g).length ≤ 4 * (cycles g 4).length := by
  have h := length_eraseDups_le ((cycles g 4).flatMap cycleEdges)
  rw [List.length_flatMap] at h
  have : ((cycles g 4).map fun c => (cycleEdges c).length).sum = 4 * (cycles g 4).length := by
    have hm : ((cycles g 4).map fun c => (cycleEdges c).length) = (cycles g 4).map fun _ => 4 := by
      apply List.map_congr_left
      intro c hc
      obtain ⟨a, b, u, v, rfl, _⟩ := fourCycle_shape (enumerated_isCycle hc)
      simp [cycleEdges_four]
    rw [hm, sum_map_const]
    omega
  rw [this] at h
  exact h

theorem countP_mem_eq_sum_count (L S : List Edge) (hS : S.Nodup) :
    L.countP (fun e => decide (e ∈ S)) = (L.map fun e => S.count e * 1).sum := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]
    by_cases hm : x ∈ S
    · simp only [hm, hS.count_of_mem hm, decide_true, ↓reduceIte]; omega
    · simp [hm, List.count_eq_zero.mpr hm]

/-- Every edge of a cycle is in the cycle-edge list, and a cycle has four distinct edges, so
the list's count of its edges is `4`. -/
theorem countP_cycleEdges_eq_four (g : Graph) {c : Cycle} (hc : c ∈ cycles g 4) :
    (cycleEdgeList g).countP (fun e => decide (e ∈ cycleEdges c)) = 4 := by
  obtain ⟨a, b, u, v, rfl, hab, hau, hav, hbu, hbv, huv⟩ := fourCycle_shape (enumerated_isCycle hc)
  have hnd := cycleEdges_four_nodup hab hau hav hbu hbv huv
  have hsub : ∀ e ∈ cycleEdges [a, b, u, v], e ∈ cycleEdgeList g :=
    fun e he => (mem_cycleEdgeList g e).mpr ⟨_, hc, he⟩
  rw [countP_mem_eq_sum_count _ _ hnd, sum_counts _ _ _ (cycleEdgeList_nodup g) hsub]
  simp [cycleEdges_four]

theorem sum_cycleCount (g : Graph) :
    ((cycleEdgeList g).map (cycleCount g)).sum = 4 * (cycles g 4).length := by
  have hunfold : (cycleEdgeList g).map (cycleCount g) =
      (cycleEdgeList g).map fun e => (cycles g 4).countP fun c => decide (e ∈ cycleEdges c) := by
    apply List.map_congr_left
    intro e _
    exact cycleCount_eq_countP g e
  rw [hunfold]
  have h : ((cycleEdgeList g).map fun e => (cycles g 4).countP fun c => decide (e ∈ cycleEdges c)).sum =
      ((cycles g 4).map fun c => (cycleEdgeList g).countP fun e => decide (e ∈ cycleEdges c)).sum := by
    simp only [List.countP_eq_length_filter]
    have hl : ∀ (l : List Cycle) (q : Cycle → Bool), (l.filter q).length = (l.map fun c => if q c then 1 else 0).sum := by
      intro l q
      induction l with
      | nil => rfl
      | cons c l ih => simp only [List.filter_cons]; split <;> simp_all <;> omega
    have hl' : ∀ (l : List Edge) (q : Edge → Bool), (l.filter q).length = (l.map fun e => if q e then 1 else 0).sum := by
      intro l q
      induction l with
      | nil => rfl
      | cons c l ih => simp only [List.filter_cons]; split <;> simp_all <;> omega
    simp only [hl, hl']
    exact sum_map_swap (cycleEdgeList g) (cycles g 4) fun e c => if decide (e ∈ cycleEdges c) then 1 else 0
  rw [h]
  have : ((cycles g 4).map fun c => (cycleEdgeList g).countP fun e => decide (e ∈ cycleEdges c)) =
      (cycles g 4).map fun _ => 4 := by
    apply List.map_congr_left
    intro c hc
    exact countP_cycleEdges_eq_four g hc
  rw [this, sum_map_const]
  omega

/-- The network has exactly `10t` arcs: `2t` from the source, `4t` pair arcs and `4t` sink arcs. -/
theorem fourCycleNetwork_length (g : Graph) :
    (fourCycleNetwork g).length = 10 * (cycles g 4).length := by
  rw [fourCycleNetwork, sourceArcs_eq, pairArcs_eq, sinkArcs_eq, List.length_append,
    List.length_append, sourceLayer_length, sinkLayer_length, sum_cycleCount, pairLayer_length]
  · omega
  · intro i hi p
    obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (fourCycle_isCycle g hi)
    rw [hc]
    exact opposingPair_length_four a b u v p

theorem pairNodes_length (t : Nat) :
    ((List.range t).flatMap fun i => [FlowNode.pair i false, FlowNode.pair i true]).length = 2 * t := by
  rw [List.length_flatMap]
  have : ((List.range t).map fun i => ([FlowNode.pair i false, FlowNode.pair i true]).length) =
      (List.range t).map fun _ => 2 := by
    apply List.map_congr_left; intro i _; rfl
  rw [this, sum_map_const, List.length_range]
  omega

theorem networkNodes_length (g : Graph) :
    (networkNodes g).length = 2 + 2 * (cycles g 4).length + (cycleEdgeList g).length := by
  rw [networkNodes, List.length_append, List.length_cons, List.length_cons, pairNodes_length,
    List.length_map]
  omega

/-- The network has at most `6t + 2` nodes. -/
theorem networkNodes_length_le (g : Graph) :
    (networkNodes g).length ≤ 6 * (cycles g 4).length + 2 := by
  rw [networkNodes_length]
  have := cycleEdgeList_length_le g
  omega

/-- Every arc joins two nodes of the network. -/
theorem arc_nodes_mem (g : Graph) (a : Arc) (ha : a ∈ fourCycleNetwork g) :
    a.tail ∈ networkNodes g ∧ a.head ∈ networkNodes g := by
  have hpair : ∀ i p, i < (cycles g 4).length → FlowNode.pair i p ∈ networkNodes g := by
    intro i p hi
    unfold networkNodes
    apply List.mem_append_left
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    exact ⟨i, List.mem_range.mpr hi, by cases p <;> simp⟩
  have hedge : ∀ e, e ∈ cycleEdgeList g → FlowNode.edgeNode e ∈ networkNodes g := by
    intro e he
    unfold networkNodes
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have hsource : FlowNode.source ∈ networkNodes g := by
    unfold networkNodes
    apply List.mem_append_left
    exact List.mem_cons_self
  have hsink : FlowNode.sink ∈ networkNodes g := by
    unfold networkNodes
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ List.mem_cons_self
  rw [fourCycleNetwork, sourceArcs_eq, pairArcs_eq, sinkArcs_eq] at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, p, hi, rfl⟩ := (mem_sourceLayer _ a).mp ha
      exact ⟨hsource, hpair i p hi⟩
    · obtain ⟨i, p, e, hi, he, rfl⟩ := (mem_pairLayer _ _ a).mp ha
      refine ⟨hpair i p hi, hedge e ?_⟩
      exact (mem_cycleEdgeList g e).mpr ⟨_, fourCycle_mem g hi, opposingPair_sub_cycleEdges _ p e he⟩
  · obtain ⟨e, j, he, _, rfl⟩ := (mem_sinkLayer _ _ a).mp ha
    exact ⟨hedge e he, hsink⟩

theorem cycleCount_le (g : Graph) (e : Edge) : cycleCount g e ≤ (cycles g 4).length := by
  rw [cycleCount]; exact List.countP_le_length

/-- Every arc costs less than `t`: the sink arcs of `y_e` cost `0, …, ϖ(e) - 1` with
`ϖ(e) ≤ t`, and the other arcs cost `0` (and exist only when `t ≥ 1`). -/
theorem arc_cost_lt (g : Graph) (a : Arc) (ha : a ∈ fourCycleNetwork g) :
    a.cost < (cycles g 4).length := by
  rw [fourCycleNetwork, sourceArcs_eq, pairArcs_eq, sinkArcs_eq] at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, p, hi, rfl⟩ := (mem_sourceLayer _ a).mp ha
      exact Nat.lt_of_le_of_lt (Nat.zero_le i) hi
    · obtain ⟨i, p, e, hi, _, rfl⟩ := (mem_pairLayer _ _ a).mp ha
      exact Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  · obtain ⟨e, j, _, hj, rfl⟩ := (mem_sinkLayer _ _ a).mp ha
    exact Nat.lt_of_lt_of_le hj (cycleCount_le g e)

/-- The size of the network of Theorem 2: `10t` arcs and at most `6t + 2` nodes, every arc
joining two nodes with cost less than `t` (and capacity one, by construction). -/
theorem fourCycleNetwork_size (g : Graph) :
    (fourCycleNetwork g).length = 10 * (cycles g 4).length ∧
    (networkNodes g).length ≤ 6 * (cycles g 4).length + 2 ∧
    (∀ a ∈ fourCycleNetwork g, a.tail ∈ networkNodes g ∧ a.head ∈ networkNodes g) ∧
    ∀ a ∈ fourCycleNetwork g, a.cost < (cycles g 4).length :=
  ⟨fourCycleNetwork_length g, networkNodes_length_le g, fun a ha => arc_nodes_mem g a ha,
    fun a ha => arc_cost_lt g a ha⟩

end STACS2027
