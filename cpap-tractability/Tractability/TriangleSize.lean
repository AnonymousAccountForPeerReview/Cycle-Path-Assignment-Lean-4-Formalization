module

public import Tractability.TriangleEquivalence
public import Tractability.NetworkSize

/-!
# The size of the triangle network

With `t` triangles, the network has exactly `t` source arcs, `3t` edge arcs and `3t`
sink arcs, so `7t` arcs in all; its nodes are `s`, `z`, the `t` triangle nodes and at
most `3t` edge nodes; every arc has capacity one and cost less than `t`. "The network
has `O(t)` vertices and arcs."
-/

@[expose] public section
namespace STACS2027

theorem triangleLayer_length (t : Nat) (C : Nat → Cycle)
    (hlen : ∀ i, i < t → (cycleEdges (C i)).length = 3) :
    (triangleLayer t C).length = 3 * t := by
  simp only [triangleLayer, List.length_flatMap, List.length_map]
  have : ((List.range t).map fun i => (cycleEdges (C i)).length) = (List.range t).map fun _ => 3 := by
    apply List.map_congr_left
    intro i hi
    exact hlen i (List.mem_range.mp hi)
  rw [this, sum_map_const, List.length_range]
  omega

theorem triangleEdgeList_length_le (g : Graph) :
    (triangleEdgeList g).length ≤ 3 * (cycles g 3).length := by
  have h := length_eraseDups_le ((cycles g 3).flatMap cycleEdges)
  rw [List.length_flatMap] at h
  have : ((cycles g 3).map fun c => (cycleEdges c).length).sum = 3 * (cycles g 3).length := by
    have hm : ((cycles g 3).map fun c => (cycleEdges c).length) = (cycles g 3).map fun _ => 3 := by
      apply List.map_congr_left
      intro c hc
      obtain ⟨a, b, u, rfl, _⟩ := triangle_shape (enumerated_isCycle hc)
      simp [cycleEdges_three]
    rw [hm, sum_map_const]
    omega
  rw [this] at h
  exact h

/-- Every edge of a triangle is in the triangle-edge list, and a triangle has three distinct
edges, so the list's count of its edges is `3`. -/
theorem countP_cycleEdges_eq_three (g : Graph) {c : Cycle} (hc : c ∈ cycles g 3) :
    (triangleEdgeList g).countP (fun e => decide (e ∈ cycleEdges c)) = 3 := by
  obtain ⟨a, b, u, rfl, hab, hau, hbu⟩ := triangle_shape (enumerated_isCycle hc)
  have hnd := cycleEdges_three_nodup hab hau hbu
  have hsub : ∀ e ∈ cycleEdges [a, b, u], e ∈ triangleEdgeList g :=
    fun e he => (mem_triangleEdgeList g e).mpr ⟨_, hc, he⟩
  rw [countP_mem_eq_sum_count _ _ hnd, sum_counts _ _ _ (triangleEdgeList_nodup g) hsub]
  simp [cycleEdges_three]

theorem sum_triangleCount (g : Graph) :
    ((triangleEdgeList g).map (triangleCount g)).sum = 3 * (cycles g 3).length := by
  have hunfold : (triangleEdgeList g).map (triangleCount g) =
      (triangleEdgeList g).map fun e => (cycles g 3).countP fun c => decide (e ∈ cycleEdges c) := by
    apply List.map_congr_left
    intro e _
    exact triangleCount_eq_countP g e
  rw [hunfold]
  have h : ((triangleEdgeList g).map fun e => (cycles g 3).countP fun c => decide (e ∈ cycleEdges c)).sum =
      ((cycles g 3).map fun c => (triangleEdgeList g).countP fun e => decide (e ∈ cycleEdges c)).sum := by
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
    exact sum_map_swap (triangleEdgeList g) (cycles g 3) fun e c => if decide (e ∈ cycleEdges c) then 1 else 0
  rw [h]
  have : ((cycles g 3).map fun c => (triangleEdgeList g).countP fun e => decide (e ∈ cycleEdges c)) =
      (cycles g 3).map fun _ => 3 := by
    apply List.map_congr_left
    intro c hc
    exact countP_cycleEdges_eq_three g hc
  rw [this, sum_map_const]
  omega

/-- The triangle network has exactly `7t` arcs: `t` from the source, `3t` edge arcs and `3t`
sink arcs. -/
theorem triangleNetwork_length (g : Graph) :
    (triangleNetwork g).length = 7 * (cycles g 3).length := by
  rw [triangleNetwork, triangleSourceArcs_eq, triangleEdgeArcs_eq, triangleSinkArcs_eq,
    List.length_append, List.length_append, triangleSourceLayer_length, sinkLayer_length,
    sum_triangleCount, triangleLayer_length]
  · omega
  · intro i hi
    exact triangleAt_edges_length g hi

theorem triangleNodes_length (g : Graph) :
    (triangleNodes g).length = 2 + (cycles g 3).length + (triangleEdgeList g).length := by
  rw [triangleNodes, List.length_append, List.length_cons, List.length_cons, List.length_map,
    List.length_map, List.length_range]
  omega

/-- The triangle network has at most `4t + 2` nodes. -/
theorem triangleNodes_length_le (g : Graph) :
    (triangleNodes g).length ≤ 4 * (cycles g 3).length + 2 := by
  rw [triangleNodes_length]
  have := triangleEdgeList_length_le g
  omega

/-- Every arc joins two nodes of the triangle network. -/
theorem triangle_arc_nodes_mem (g : Graph) (a : Arc) (ha : a ∈ triangleNetwork g) :
    a.tail ∈ triangleNodes g ∧ a.head ∈ triangleNodes g := by
  have htri : ∀ i, i < (cycles g 3).length → FlowNode.triangle i ∈ triangleNodes g := by
    intro i hi
    unfold triangleNodes
    apply List.mem_append_left
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hedge : ∀ e, e ∈ triangleEdgeList g → FlowNode.edgeNode e ∈ triangleNodes g := by
    intro e he
    unfold triangleNodes
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have hsource : FlowNode.source ∈ triangleNodes g := by
    unfold triangleNodes
    apply List.mem_append_left
    exact List.mem_cons_self
  have hsink : FlowNode.sink ∈ triangleNodes g := by
    unfold triangleNodes
    apply List.mem_append_left
    exact List.mem_cons_of_mem _ List.mem_cons_self
  rw [triangleNetwork, triangleSourceArcs_eq, triangleEdgeArcs_eq, triangleSinkArcs_eq] at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, hi, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha
      exact ⟨hsource, htri i hi⟩
    · obtain ⟨i, e, hi, he, rfl⟩ := (mem_triangleLayer _ _ a).mp ha
      exact ⟨htri i hi, hedge e (triangle_edge_mem_list g hi he)⟩
  · obtain ⟨e, j, he, _, rfl⟩ := (mem_sinkLayer _ _ a).mp ha
    exact ⟨hedge e he, hsink⟩

theorem triangleCount_le (g : Graph) (e : Edge) : triangleCount g e ≤ (cycles g 3).length := by
  rw [triangleCount]; exact List.countP_le_length

/-- Every arc costs less than `t`. -/
theorem triangle_arc_cost_lt (g : Graph) (a : Arc) (ha : a ∈ triangleNetwork g) :
    a.cost < (cycles g 3).length := by
  rw [triangleNetwork, triangleSourceArcs_eq, triangleEdgeArcs_eq, triangleSinkArcs_eq] at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, hi, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha
      exact Nat.lt_of_le_of_lt (Nat.zero_le i) hi
    · obtain ⟨i, e, hi, _, rfl⟩ := (mem_triangleLayer _ _ a).mp ha
      exact Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  · obtain ⟨e, j, _, hj, rfl⟩ := (mem_sinkLayer _ _ a).mp ha
    exact Nat.lt_of_lt_of_le hj (triangleCount_le g e)

/-- The size of the triangle network: `7t` arcs and at most `4t + 2` nodes, every arc joining
two nodes with cost less than `t` (and capacity one, by construction). -/
theorem triangleNetwork_size (g : Graph) :
    (triangleNetwork g).length = 7 * (cycles g 3).length ∧
    (triangleNodes g).length ≤ 4 * (cycles g 3).length + 2 ∧
    (∀ a ∈ triangleNetwork g, a.tail ∈ triangleNodes g ∧ a.head ∈ triangleNodes g) ∧
    ∀ a ∈ triangleNetwork g, a.cost < (cycles g 3).length :=
  ⟨triangleNetwork_length g, triangleNodes_length_le g, fun a ha => triangle_arc_nodes_mem g a ha,
    fun a ha => triangle_arc_cost_lt g a ha⟩

end STACS2027
