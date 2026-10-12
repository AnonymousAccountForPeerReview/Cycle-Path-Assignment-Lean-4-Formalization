# How the proof works

The compared theorem `cpap4_iff_flow` is `hasAssignment_iff_flow` in
`Tractability/FlowEquivalence.lean`, proved from the two directions below. A flow is
handled as `flowOf g P = (fourCycleNetwork g).filter P` for a predicate `P` on
arcs; `Tractability/NetworkCounts.lean` computes, for such a flow, the inflow and
outflow at each kind of node from the three layers of the network
(`sourceLayer`, `pairLayer`, `sinkLayer`, with the cycle list, edge list and
multiplicities abstracted so that no proof unfolds the enumeration
`cycles g 4`).

## Assignment to flow (`flow_of_assignment`)

Given paths `ps` indexed like `cycles g 4`, `assignmentPredicate ps` keeps every
source arc, the pair arc `x_{C_i,p} → y_e` exactly when `e` is on the path of
`C_i`, and the sink arc `y_e → z` of cost `j` exactly when `j < l(e)`.

* At `x_{C_i,p}`: one unit in; one unit out, because a path of a four-cycle
  contains exactly one edge of each opposing pair
  (`opposingPair_countP_selected`, from the explicit description of the four
  paths in `Tractability/FourCycles.lean`).
* At `y_e`: the inflow is `l(e)` (`inflow_edge_eq_load`: each cycle through
  `e` on its path sends one unit, through the one pair containing `e`); the
  outflow is `min(ϖ(e), l(e)) = l(e)`, since `l(e) ≤ ϖ(e)`
  (`load_le_cycleCount`) and `l(e) = 0` for edges on no cycle.
* The value is `2t`, and the cost is `∑_e (0 + 1 + ⋯ + (l(e) − 1))
  = ∑_e binom(l(e), 2) = cost ps` (`sum_range_if_lt`, `cost_eq_load_sum`).

## Flow to assignment (`assignment_of_flow`)

Given a flow `F` of value `2t`, `F = flowOf g (· ∈ F)` because the arc list has
no repetition (`fourCycleNetwork_nodup`, `Sublist.filter_mem_eq`).

* The `2t` source arcs all carry flow (value `2t`, `countP_eq_length`), so
  every `x_{C_i,p}` receives one unit and sends it along exactly one of its two
  arcs; the two chosen edges determine one of the four paths of `C_i`
  (`optionIndex`, `chosenEdge_optionIndex`), and the pair arcs with flow are
  exactly those naming an edge of that path.
* Hence the inflow of `y_e` is `l(e)` of the constructed paths
  (`inflow_edge_eq_load` again), so `l(e)` sink arcs of `y_e` carry flow, and
  their costs, distinct among `0, …, ϖ(e) − 1`, sum to at least
  `binom(l(e), 2)` (`sum_range_if_ge_pairCount`). Summing over the edges,
  `cost ps ≤ flowCost F`.

## Size (`Tractability/NetworkSize.lean`)

The source layer has `2t` arcs, the pair layer `4t` (two edges per pair, two
pairs per cycle), and the sink layer `∑_e ϖ(e) = 4t` by double counting
(`sum_cycleCount`: each cycle has four distinct edges, all in
`cycleEdgeList`). The node list has `2 + 2t + |cycleEdgeList| ≤ 6t + 2` entries,
and every arc's cost is below `ϖ(e) ≤ t`.

## The Section 3 triangle reduction (`Tractability/Triangle*.lean`)

The triangle network replaces the two pair nodes of a cycle by one node
`x_{C_i}` (`FlowNode.triangle i`) with a source arc and three edge arcs, one for
each edge of the triangle `C_i = [a, b, u]` (its edges `ab, bu, ua` are distinct,
`cycleEdges_three_nodup`); the sink layer is the same `sinkLayer`, on the edges
lying on triangles with multiplicities `ϖ(e)` (`triangleCount`). The counts at
each node are proved on the abstract layers as before (`TriangleCounts.lean`):
`x_{C_i}` is entered by its source arc and left by the edge arcs carrying flow,
`y_e` is entered by one arc per triangle containing `e` whose arc carries flow
and left by its sink arcs.

The paths of a triangle are its three edges as singleton lists
(`selectedOptions_three`). From an assignment, the flow uses every source arc,
the edge arc of the chosen edge of each triangle, and the `l(e)` cheapest sink
arcs of each edge (`triangleAssignmentPredicate`): conservation at `x_{C_i}`
is that exactly one of its three edges is the chosen one, at `y_e` that the
inflow, which is the load of `e`, equals the number of chosen sink arcs
(`triangle_flow_of_assignment`). From a flow of value `t`, every source arc
carries flow, so each triangle node sends its unit along exactly one edge arc
(`countP = 1`); `triangleChoice` picks that edge with `List.find?`, and the
uniqueness (`countP_one_unique`) identifies the edge arcs carrying flow with the
chosen edges; the sink arcs of `y_e` then cost at least `binom(l(e), 2)`
(`triangle_assignment_of_flow`). The sizes are `t + 3t + ∑_e ϖ(e) = 7t` arcs,
since `∑_e ϖ(e) = 3t` (`sum_triangleCount`), and `2 + t + |edge nodes| ≤ 4t + 2`
nodes (`TriangleSize.lean`).

## Executed companion boundary

The mathematical reductions and sizes above have dependency A: only `propext`, `Classical.choice`, and `Quot.sound`. The companion `cpap-runtimes` package proves actual construction, extraction and enumeration. Composing a flow solver requires `Flow.MinCostFlowSolver F T` (F); almost-linear runtime conclusions also require `Flow.AlmostLinear T` (F+). These explicit premises retain the sole excluded almost-linear flow algorithm without adding an axiom.
