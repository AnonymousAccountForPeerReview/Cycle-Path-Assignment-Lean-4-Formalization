module

public import Tractability.FlowEquivalence
public import Tractability.NetworkSize
public import Tractability.TriangleSize

/-!
# Paper interface: Section 3 and Appendix A of the accompanying paper

This module restates the development in the manuscript's terms. It adds no
construction; each theorem is proved from the development.

Theorem 2 states that `CPAP(G, 4)` can be solved in time `O(t^{1+o(1)} + Υ_4)`, `t` being
the number of simple four-cycles and `Υ_4` the time to enumerate them. Its proof
(Appendix A) is a reduction to minimum-cost flow: the network `𝓕` below, the exact
correspondence between integral flows of value `2t` and cycle-path assignments, and
the size of `𝓕`, after which the running time is that of the cited minimum-cost flow
algorithm of ANONYMIZED et al. The reduction and the size bound are what is
formalized here. The companion package `cpap-runtimes` proves the network construction
and extraction programs (`STACS2027.Runtimes.Flow.cpap4_flow_ram_semantic`) and a
four-cycle enumerator (`STACS2027.Runtimes.C4.fourCycles_ram_semantic`). Its
`STACS2027.Runtimes.cpap4_enum_ram_semantic` combines these with the cited min-cost flow
solver; the almost-linear-time solver bound remains a hypothesis.

The additional triangle result (`cor:K3TimeComplexity`
) modifies the network: one node `x_C` per triangle `C`, a
unit arc `s → x_C` and arcs `x_C → y_e` for the three edges of `C`, the same sink bundles;
"an integral flow of value `t` selects one edge per triangle and has minimum cost exactly
when the corresponding assignment is optimal", and "the network has `O(t)` vertices and arcs".
Both are formalized the same way (`cpap3_iff_flow`, `triangleNetwork_size`).
-/

@[expose] public section
namespace STACS2027.Paper

/-! ## The observation behind the network -/

/-- "The choice of a length-2 edge subpath of a simple 4-cycle with sequential edges
`(e₁, e₂, e₃, e₄)` can be understood as independently choosing a single edge from the sets
`{e₁, e₃}` and `{e₂, e₄}`": the four paths of a four-cycle are exactly the four such choices. -/
theorem opposing_pair_choices {g : Graph} {c : Cycle} (hc : IsCycle g 4 c) (q : List Edge) :
    q ∈ selectedOptions c ↔
      ∃ j, j < 4 ∧ q = selected c j ∧
        (∀ p, chosenEdge c j p ∈ opposingPair c p) ∧
        (∀ e, e ∈ q ↔ e = chosenEdge c j false ∨ e = chosenEdge c j true) := by
  obtain ⟨a, b, u, v, rfl, _⟩ := fourCycle_shape hc
  rw [mem_selectedOptions_four]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl, fun p => chosenEdge_mem_pair a b u v j p,
      fun e => mem_selected_four_iff a b u v hj e⟩
  · rintro ⟨j, hj, rfl, _⟩
    exact ⟨j, hj, rfl⟩

/-- Every choice of one edge from each opposing pair is one of the four paths. -/
theorem opposing_pair_choices_complete {g : Graph} {c : Cycle} (hc : IsCycle g 4 c)
    (q₀ q₁ : Bool) :
    ∃ j, j < 4 ∧ ∀ e, e ∈ selected c j ↔
      e = chosenEdge c (optionIndex q₀ q₁) false ∨ e = chosenEdge c (optionIndex q₀ q₁) true := by
  obtain ⟨a, b, u, v, rfl, _⟩ := fourCycle_shape hc
  exact ⟨optionIndex q₀ q₁, optionIndex_lt q₀ q₁,
    fun e => mem_selected_four_iff a b u v (optionIndex_lt q₀ q₁) e⟩

/-! ## Appendix A: the network `𝓕` -/

/-- `|X| = 2t`: two opposing-pair nodes per cycle, and `|Y| ≤ 4t` edge nodes. -/
theorem network_node_counts (g : Graph) :
    (networkNodes g).length = 2 + 2 * (cycles g 4).length + (cycleEdgeList g).length ∧
      (cycleEdgeList g).length ≤ 4 * (cycles g 4).length :=
  ⟨networkNodes_length g, cycleEdgeList_length_le g⟩

/-- `|E_𝓕| = O(t)`: exactly `10t` arcs. -/
theorem network_arc_count (g : Graph) : (fourCycleNetwork g).length = 10 * (cycles g 4).length :=
  fourCycleNetwork_length g

/-- The arcs from `y_e` to the sink are exactly `ϖ(e)` parallel arcs with costs
`0, 1, …, ϖ(e) - 1`, for each edge `e` on a four-cycle, and `ϖ(e) ≤ t`; so `Q ≤ t - 1`. -/
theorem sink_arc_costs (g : Graph) :
    (∀ a ∈ sinkArcs g, ∃ e j, e ∈ cycleEdgeList g ∧ j < cycleCount g e ∧
      a = ⟨.edgeNode e, .sink, j⟩) ∧
    (∀ e ∈ cycleEdgeList g, ∀ j, j < cycleCount g e → (⟨.edgeNode e, .sink, j⟩ : Arc) ∈ sinkArcs g) ∧
    (sinkArcs g).Nodup ∧
    ∀ e, cycleCount g e ≤ (cycles g 4).length := by
  refine ⟨fun a ha => (mem_sinkLayer _ _ a).mp ha, fun e he j hj => (mem_sinkLayer _ _ _).mpr ⟨e, j, he, hj, rfl⟩,
    sinkLayer_nodup _ (cycleEdgeList_nodup g) _, cycleCount_le g⟩

/-- Every cycle-path assignment induces an integral flow of value `2t` and the same cost
(proof sketch of Theorem 2, "every cycle-path assignment induces an integral flow with this same cost"). -/
theorem assignment_to_flow (g : Graph) (ps : List (List Edge))
    (hv : ValidChoices ((cycles g 4).map selectedOptions) ps) :
    ∃ flow, IsFlow (fourCycleNetwork g) flow ∧ flowValue flow = 2 * (cycles g 4).length ∧
      flowCost flow = cost ps :=
  ⟨_, flow_of_assignment g ps hv⟩

/-- Every integral flow of value `2t` yields an assignment of no greater cost; "an optimal
integral flow therefore yields an optimal assignment". -/
theorem flow_to_assignment (g : Graph) (flow : List Arc) (hF : IsFlow (fourCycleNetwork g) flow)
    (hval : flowValue flow = 2 * (cycles g 4).length) :
    ∃ ps, ValidChoices ((cycles g 4).map selectedOptions) ps ∧ cost ps ≤ flowCost flow :=
  assignment_of_flow g flow hF hval

/-- "No bottlenecks exist for this flow": a flow of value `2t` always exists. -/
theorem flow_exists (g : Graph) :
    ∃ flow, IsFlow (fourCycleNetwork g) flow ∧ flowValue flow = 2 * (cycles g 4).length := by
  have hv : ValidChoices ((cycles g 4).map selectedOptions)
      ((List.range (cycles g 4).length).map fun i => selected (fourCycle g i) 0) := by
    apply validChoices_of_getD
    · simp
    · intro i hi
      rw [getD_map_range _ _ [] hi]
      change selected (fourCycle g i) 0 ∈ selectedOptions (fourCycle g i)
      obtain ⟨a, b, u, v, hc, _⟩ := fourCycle_shape (fourCycle_isCycle g hi)
      rw [hc, mem_selectedOptions_four]
      exact ⟨0, by omega, rfl⟩
  obtain ⟨hflow, hval, _⟩ := flow_of_assignment g _ hv
  exact ⟨_, hflow, hval⟩

/-! ## Theorem 2 -/

/-- **Theorem 2**, the reduction: `CPAP(G, 4)` has an assignment of cost at most `B` iff `𝓕`
has an integral flow of value `2t` and cost at most `B`. The minimum cost of such a flow is
therefore `OPT`. -/
theorem fourCycle_flow_reduction (g : Graph) (budget : Nat) :
    HasAssignment g 4 budget ↔
      ∃ flow, IsFlow (fourCycleNetwork g) flow ∧
        flowValue flow = 2 * (cycles g 4).length ∧ flowCost flow ≤ budget :=
  cpap4_iff_flow g budget

/-- Theorem 2, the size of `𝓕`: `10t` arcs, at most `6t + 2` nodes, every arc of capacity one
(by construction) between two nodes, with cost less than `t`. -/
theorem fourCycle_network_size (g : Graph) :
    (fourCycleNetwork g).length = 10 * (cycles g 4).length ∧
    (networkNodes g).length ≤ 6 * (cycles g 4).length + 2 ∧
    (∀ a ∈ fourCycleNetwork g, a.tail ∈ networkNodes g ∧ a.head ∈ networkNodes g) ∧
    ∀ a ∈ fourCycleNetwork g, a.cost < (cycles g 4).length :=
  fourCycleNetwork_size g

/-! ## The corollary for triangles (`cor:K3TimeComplexity`) -/

/-- The modified network: "one node `x_C` for each triangle `C`", "a unit-capacity, zero-cost
arc from the source to `x_C` and from `x_C` to each of the three edge nodes `y_e` with
`e ∈ E(C)`", and "the same bundles of unit-capacity arcs from each `y_e` to the sink, with costs
`0, …, ϖ(e) − 1`". -/
theorem triangle_network_arcs (g : Graph) :
    (∀ a ∈ triangleSourceArcs g, ∃ i, i < (cycles g 3).length ∧ a = ⟨.source, .triangle i, 0⟩) ∧
    (∀ a ∈ triangleEdgeArcs g, ∃ i e, i < (cycles g 3).length ∧ e ∈ cycleEdges (triangleAt g i) ∧
      a = ⟨.triangle i, .edgeNode e, 0⟩) ∧
    (∀ a ∈ triangleSinkArcs g, ∃ e j, e ∈ triangleEdgeList g ∧ j < triangleCount g e ∧
      a = ⟨.edgeNode e, .sink, j⟩) ∧
    ∀ e, triangleCount g e ≤ (cycles g 3).length :=
  ⟨fun a ha => (mem_triangleSourceLayer _ a).mp ha, fun a ha => (mem_triangleLayer _ _ a).mp ha,
    fun a ha => (mem_sinkLayer _ _ a).mp ha, triangleCount_le g⟩

/-- A triangle's paths of `k − 2 = 1` edge are its three edges. -/
theorem triangle_paths {g : Graph} {c : Cycle} (hc : IsCycle g 3 c) (q : List Edge) :
    q ∈ selectedOptions c ↔ ∃ e ∈ cycleEdges c, q = [e] := by
  obtain ⟨a, b, u, rfl, _⟩ := triangle_shape hc
  exact mem_selectedOptions_three a b u q

/-- "An integral flow of value `t` selects one edge per triangle and has minimum cost exactly
when the corresponding assignment is optimal": every assignment induces a flow of value `t` and
the same cost, and every flow of value `t` yields an assignment of no greater cost. -/
theorem triangle_correspondence (g : Graph) :
    (∀ ps, ValidChoices ((cycles g 3).map selectedOptions) ps →
      ∃ flow, IsFlow (triangleNetwork g) flow ∧ flowValue flow = (cycles g 3).length ∧
        flowCost flow = cost ps) ∧
    ∀ flow, IsFlow (triangleNetwork g) flow → flowValue flow = (cycles g 3).length →
      ∃ ps, ValidChoices ((cycles g 3).map selectedOptions) ps ∧ cost ps ≤ flowCost flow :=
  ⟨fun ps hv => ⟨_, triangle_flow_of_assignment g ps hv⟩,
    fun flow hF hval => triangle_assignment_of_flow g flow hF hval⟩

/-- **Corollary `K3TimeComplexity`**, the reduction: `CPAP(G, 3)` has an assignment of cost at
most `B` iff the triangle network has an integral flow of value `t` and cost at most `B`. -/
theorem corollary_k3 (g : Graph) (budget : Nat) :
    HasAssignment g 3 budget ↔
      ∃ flow, IsFlow (triangleNetwork g) flow ∧
        flowValue flow = (cycles g 3).length ∧ flowCost flow ≤ budget :=
  cpap3_iff_flow g budget

/-- "The network has `O(t)` vertices and arcs": `7t` arcs and at most `4t + 2` nodes, every arc
of capacity one between two nodes, with cost less than `t`. -/
theorem corollary_k3_size (g : Graph) :
    (triangleNetwork g).length = 7 * (cycles g 3).length ∧
    (triangleNodes g).length ≤ 4 * (cycles g 3).length + 2 ∧
    (∀ a ∈ triangleNetwork g, a.tail ∈ triangleNodes g ∧ a.head ∈ triangleNodes g) ∧
    ∀ a ∈ triangleNetwork g, a.cost < (cycles g 3).length :=
  triangleNetwork_size g

end STACS2027.Paper
