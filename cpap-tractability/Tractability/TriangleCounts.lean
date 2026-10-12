module

public import Tractability.TriangleNetwork

/-!
# Counting arcs of a flow at each node of the triangle network

As for the four-cycle network: the triangle node `x_{C_i}` is entered only by its
source arc and left only by its three edge arcs; the edge node `y_e` is entered by the
edge arcs of the triangles containing `e` and left by its `ϖ(e)` sink arcs. The counts
are proved for the layers with the triangle list abstracted.
-/

@[expose] public section
namespace STACS2027

/-! ## The two new layers, abstractly -/

/-- The source arcs for `t` triangles. -/
def triangleSourceLayer (t : Nat) : List Arc :=
  (List.range t).map fun i => ⟨.source, .triangle i, 0⟩

/-- The edge arcs for `t` triangles `C 0, …, C (t - 1)`. -/
def triangleLayer (t : Nat) (C : Nat → Cycle) : List Arc :=
  (List.range t).flatMap fun i => (cycleEdges (C i)).map fun e => ⟨.triangle i, .edgeNode e, 0⟩

theorem triangleSourceArcs_eq (g : Graph) :
    triangleSourceArcs g = triangleSourceLayer (cycles g 3).length := rfl

theorem triangleEdgeArcs_eq (g : Graph) :
    triangleEdgeArcs g = triangleLayer (cycles g 3).length (triangleAt g) := rfl

theorem triangleSinkArcs_eq (g : Graph) :
    triangleSinkArcs g = sinkLayer (triangleEdgeList g) (triangleCount g) := rfl

/-! ### Source layer -/

theorem triangleSourceLayer_countP (t : Nat) (q : Arc → Bool) :
    (triangleSourceLayer t).countP q =
      ((List.range t).map fun i => if q ⟨.source, .triangle i, 0⟩ then 1 else 0).sum := by
  rw [triangleSourceLayer, List.countP_map, countP_eq_sum_range _ 0]
  simp only [List.length_range, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_range (List.mem_range.mp hi)]
  rfl

theorem mem_triangleSourceLayer (t : Nat) (a : Arc) :
    a ∈ triangleSourceLayer t ↔ ∃ i, i < t ∧ a = ⟨.source, .triangle i, 0⟩ := by
  simp only [triangleSourceLayer, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem triangleSourceLayer_head_triangle (t : Nat) (P : Arc → Bool) (i₀ : Nat) :
    (triangleSourceLayer t).countP (fun a => a.head.beq (.triangle i₀) && P a) =
      if i₀ < t then (if P ⟨.source, .triangle i₀, 0⟩ then 1 else 0) else 0 := by
  rw [triangleSourceLayer_countP, sum_map_range_single _ i₀]
  · split
    · simp [FlowNode.beq]
    · rfl
  · intro i hi
    simp [FlowNode.beq, hi]

theorem triangleSourceLayer_head_other (t : Nat) (P : Arc → Bool) (v : FlowNode)
    (hv : ∀ i, v ≠ .triangle i) :
    (triangleSourceLayer t).countP (fun a => a.head.beq v && P a) = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer t a).mp ha
  have := hv i
  cases v <;> simp_all [FlowNode.beq]

theorem triangleSourceLayer_tail_source (t : Nat) (P : Arc → Bool) :
    (triangleSourceLayer t).countP (fun a => a.tail.beq .source && P a) =
      (triangleSourceLayer t).countP P := by
  apply List.countP_congr
  intro a ha
  obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer t a).mp ha
  simp [FlowNode.beq]

theorem triangleSourceLayer_tail_other (t : Nat) (P : Arc → Bool) (v : FlowNode)
    (hv : v ≠ .source) :
    (triangleSourceLayer t).countP (fun a => a.tail.beq v && P a) = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer t a).mp ha
  cases v <;> simp_all [FlowNode.beq]

theorem triangleSourceLayer_length (t : Nat) : (triangleSourceLayer t).length = t := by
  simp [triangleSourceLayer]

/-! ### Triangle layer -/

theorem triangleLayer_countP (t : Nat) (C : Nat → Cycle) (q : Arc → Bool) :
    (triangleLayer t C).countP q = ((List.range t).map fun i =>
      (cycleEdges (C i)).countP (fun e => q ⟨.triangle i, .edgeNode e, 0⟩)).sum := by
  rw [triangleLayer, countP_flatMap']
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [List.countP_map, Function.comp_def]

theorem mem_triangleLayer (t : Nat) (C : Nat → Cycle) (a : Arc) :
    a ∈ triangleLayer t C ↔
      ∃ i e, i < t ∧ e ∈ cycleEdges (C i) ∧ a = ⟨.triangle i, .edgeNode e, 0⟩ := by
  simp only [triangleLayer, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨i, hi, e, he, rfl⟩
    exact ⟨i, e, hi, he, rfl⟩
  · rintro ⟨i, e, hi, he, rfl⟩
    exact ⟨i, hi, e, he, rfl⟩

theorem triangleLayer_tail_triangle (t : Nat) (C : Nat → Cycle) (P : Arc → Bool) (i₀ : Nat) :
    (triangleLayer t C).countP (fun a => a.tail.beq (.triangle i₀) && P a) =
      if i₀ < t then (cycleEdges (C i₀)).countP (fun e => P ⟨.triangle i₀, .edgeNode e, 0⟩)
      else 0 := by
  rw [triangleLayer_countP, sum_map_range_single _ i₀]
  · split
    · simp [FlowNode.beq]
    · rfl
  · intro i hi
    simp [FlowNode.beq, hi]

theorem triangleLayer_tail_other (t : Nat) (C : Nat → Cycle) (P : Arc → Bool) (v : FlowNode)
    (hv : ∀ i, v ≠ .triangle i) :
    (triangleLayer t C).countP (fun a => a.tail.beq v && P a) = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  obtain ⟨i, e, _, _, rfl⟩ := (mem_triangleLayer t C a).mp ha
  have := hv i
  cases v <;> simp_all [FlowNode.beq]

theorem triangleLayer_head_other (t : Nat) (C : Nat → Cycle) (P : Arc → Bool) (v : FlowNode)
    (hv : ∀ e, v ≠ .edgeNode e) :
    (triangleLayer t C).countP (fun a => a.head.beq v && P a) = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  obtain ⟨i, e, _, _, rfl⟩ := (mem_triangleLayer t C a).mp ha
  have := hv e
  cases v <;> simp_all [FlowNode.beq]

/-- The edge arcs entering `y_e`: one for each triangle containing `e`, when the triangles have
no repeated edge. -/
theorem triangleLayer_head_edge (t : Nat) (C : Nat → Cycle) (P : Arc → Bool) (e₀ : Edge)
    (hn : ∀ i, i < t → (cycleEdges (C i)).Nodup) :
    (triangleLayer t C).countP (fun a => a.head.beq (.edgeNode e₀) && P a) =
      ((List.range t).map fun i =>
        if e₀ ∈ cycleEdges (C i) ∧ P ⟨.triangle i, .edgeNode e₀, 0⟩ = true then 1 else 0).sum := by
  rw [triangleLayer_countP]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [← countP_eq_mem_indicator _ (hn i hi')]
  apply List.countP_congr
  intro e _
  simp only [FlowNode.beq, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩

/-! ## The network has no repeated arc -/

theorem triangleSourceLayer_nodup (t : Nat) : (triangleSourceLayer t).Nodup := by
  rw [triangleSourceLayer, List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp (fun h he => h (by
    have := congrArg Arc.head he
    simpa using this))

theorem triangleLayer_nodup (t : Nat) (C : Nat → Cycle) (hn : ∀ i, i < t → (cycleEdges (C i)).Nodup) :
    (triangleLayer t C).Nodup := by
  rw [triangleLayer]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.range_succ, List.flatMap_append, List.nodup_append]
    refine ⟨ih (fun i hi => hn i (by omega)), ?_, ?_⟩
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact (List.nodup_iff_pairwise_ne.mp (hn t (by omega))).imp (fun h he => h (by
        have := congrArg Arc.head he
        simpa using this))
    · intro a ha b hb hab
      subst hab
      obtain ⟨i, e, hi, _, rfl⟩ := (mem_triangleLayer t C a).mp ha
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map] at hb
      obtain ⟨e', _, he'⟩ := hb
      have := congrArg Arc.tail he'
      simp at this
      omega

theorem triangleNetwork_nodup (g : Graph) : (triangleNetwork g).Nodup := by
  rw [triangleNetwork, triangleSourceArcs_eq, triangleEdgeArcs_eq, triangleSinkArcs_eq,
    List.nodup_append, List.nodup_append]
  refine ⟨⟨triangleSourceLayer_nodup _, triangleLayer_nodup _ _ (fun i hi => triangleAt_edges_nodup g hi), ?_⟩,
    sinkLayer_nodup _ (triangleEdgeList_nodup g) _, ?_⟩
  · intro a ha b hb
    obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha
    obtain ⟨i', e, _, _, rfl⟩ := (mem_triangleLayer _ _ b).mp hb
    simp
  · intro a ha b hb
    obtain ⟨e, j, _, _, rfl⟩ := (mem_sinkLayer _ _ b).mp hb
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer _ a).mp ha
      simp
    · obtain ⟨i', e', _, _, rfl⟩ := (mem_triangleLayer _ _ a).mp ha
      simp

/-! ## Flows given by a predicate -/

/-- The flow consisting of the arcs of the triangle network satisfying `P`. -/
def triangleFlowOf (g : Graph) (P : Arc → Bool) : List Arc := (triangleNetwork g).filter P

theorem triangleFlowOf_sublist (g : Graph) (P : Arc → Bool) :
    (triangleFlowOf g P).Sublist (triangleNetwork g) :=
  List.filter_sublist

theorem inflow_triangleFlowOf (g : Graph) (P : Arc → Bool) (v : FlowNode) :
    inflow (triangleFlowOf g P) v =
      (triangleSourceLayer (cycles g 3).length).countP (fun a => a.head.beq v && P a) +
      (triangleLayer (cycles g 3).length (triangleAt g)).countP (fun a => a.head.beq v && P a) +
      (sinkLayer (triangleEdgeList g) (triangleCount g)).countP (fun a => a.head.beq v && P a) := by
  simp only [inflow, triangleFlowOf, triangleNetwork, List.countP_filter, List.countP_append,
    triangleSourceArcs_eq, triangleEdgeArcs_eq, triangleSinkArcs_eq]

theorem outflow_triangleFlowOf (g : Graph) (P : Arc → Bool) (v : FlowNode) :
    outflow (triangleFlowOf g P) v =
      (triangleSourceLayer (cycles g 3).length).countP (fun a => a.tail.beq v && P a) +
      (triangleLayer (cycles g 3).length (triangleAt g)).countP (fun a => a.tail.beq v && P a) +
      (sinkLayer (triangleEdgeList g) (triangleCount g)).countP (fun a => a.tail.beq v && P a) := by
  simp only [outflow, triangleFlowOf, triangleNetwork, List.countP_filter, List.countP_append,
    triangleSourceArcs_eq, triangleEdgeArcs_eq, triangleSinkArcs_eq]

theorem flowCost_triangleFlowOf (g : Graph) (P : Arc → Bool) :
    flowCost (triangleFlowOf g P) =
      flowCost ((sinkLayer (triangleEdgeList g) (triangleCount g)).filter P) := by
  simp only [triangleFlowOf, triangleNetwork, List.filter_append, flowCost, List.map_append,
    List.sum_append, triangleSourceArcs_eq, triangleEdgeArcs_eq, triangleSinkArcs_eq]
  have h₁ : (((triangleSourceLayer (cycles g 3).length).filter P).map Arc.cost).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, _, rfl⟩ := (mem_triangleSourceLayer _ a).mp (List.mem_filter.mp ha).1
    rfl
  have h₂ : (((triangleLayer (cycles g 3).length (triangleAt g)).filter P).map Arc.cost).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, e, _, _, rfl⟩ := (mem_triangleLayer _ _ a).mp (List.mem_filter.mp ha).1
    rfl
  omega

theorem flowValue_triangleFlowOf (g : Graph) (P : Arc → Bool) :
    flowValue (triangleFlowOf g P) = (triangleSourceLayer (cycles g 3).length).countP P := by
  rw [flowValue, outflow_triangleFlowOf, triangleSourceLayer_tail_source,
    triangleLayer_tail_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]
  omega

theorem inflow_triangleFlowOf_triangle (g : Graph) (P : Arc → Bool) (i : Nat) :
    inflow (triangleFlowOf g P) (.triangle i) =
      if i < (cycles g 3).length then (if P ⟨.source, .triangle i, 0⟩ then 1 else 0) else 0 := by
  rw [inflow_triangleFlowOf, triangleSourceLayer_head_triangle,
    triangleLayer_head_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]
  omega

theorem outflow_triangleFlowOf_triangle (g : Graph) (P : Arc → Bool) (i : Nat) :
    outflow (triangleFlowOf g P) (.triangle i) =
      if i < (cycles g 3).length then
        (cycleEdges (triangleAt g i)).countP (fun e => P ⟨.triangle i, .edgeNode e, 0⟩)
      else 0 := by
  rw [outflow_triangleFlowOf, triangleSourceLayer_tail_other _ P _ (by intro h; cases h),
    triangleLayer_tail_triangle, sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]
  omega

theorem inflow_triangleFlowOf_edge (g : Graph) (P : Arc → Bool) (e₀ : Edge) :
    inflow (triangleFlowOf g P) (.edgeNode e₀) =
      ((List.range (cycles g 3).length).map fun i =>
        if e₀ ∈ cycleEdges (triangleAt g i) ∧ P ⟨.triangle i, .edgeNode e₀, 0⟩ = true then 1
        else 0).sum := by
  rw [inflow_triangleFlowOf, triangleSourceLayer_head_other _ P _ (fun _ h => by cases h),
    triangleLayer_head_edge _ _ P e₀ (fun i hi => triangleAt_edges_nodup g hi),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]
  omega

theorem outflow_triangleFlowOf_edge (g : Graph) (P : Arc → Bool) (e₀ : Edge) :
    outflow (triangleFlowOf g P) (.edgeNode e₀) =
      if e₀ ∈ triangleEdgeList g then
        (List.range (triangleCount g e₀)).countP (fun j => P ⟨.edgeNode e₀, .sink, j⟩)
      else 0 := by
  rw [outflow_triangleFlowOf, triangleSourceLayer_tail_other _ P _ (by intro h; cases h),
    triangleLayer_tail_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_tail_edge _ (triangleEdgeList_nodup g)]
  omega

theorem inflow_triangleFlowOf_pair (g : Graph) (P : Arc → Bool) (i : Nat) (p : Bool) :
    inflow (triangleFlowOf g P) (.pair i p) = 0 := by
  rw [inflow_triangleFlowOf, triangleSourceLayer_head_other _ P _ (fun _ h => by cases h),
    triangleLayer_head_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_head_other _ _ P _ (by intro h; cases h)]

theorem outflow_triangleFlowOf_pair (g : Graph) (P : Arc → Bool) (i : Nat) (p : Bool) :
    outflow (triangleFlowOf g P) (.pair i p) = 0 := by
  rw [outflow_triangleFlowOf, triangleSourceLayer_tail_other _ P _ (by intro h; cases h),
    triangleLayer_tail_other _ _ P _ (fun _ h => by cases h),
    sinkLayer_tail_other _ _ P _ (fun _ h => by cases h)]

end STACS2027
