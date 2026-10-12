# Paper map: Section 3 and Appendix A in Lean

Result numbers and appendix letters follow the accompanying paper. Names without a namespace are in `STACS2027`; `Paper.x` is
`STACS2027.Paper.x` in `Tractability/Paper.lean`. Every row is a proved theorem or a definition.
The four compared theorems are marked **(Challenge)**.

## Definitions

| Manuscript | Lean | Notes |
|---|---|---|
| Definition 1 (CPAP, objective `∑_e binom(l(e),2)`), `t`, `ϖ(e)` | `HasAssignment g 4 B`, `cost` (`cpap-np-hardness` formalization, copied); `(cycles g 4).length`; `cycleCount` | The `cpap-np-hardness` formalization proves `cost` is the load objective. `ϖ(e)` counts the enumerated four-cycles containing `e`. |
| "cyclically ordered edges `(e₁,e₂,e₃,e₄)`", "opposing pairs `{e₁,e₃}` and `{e₂,e₄}`" | `cycleEdges c`, `opposingPair c false`, `opposingPair c true` | `cycleEdges [a,b,u,v] = [ab, bu, uv, va]` (`cycleEdges_four`). |
| "a source `s`, a sink `z`, two opposing-pair nodes `x_{C,{e₁,e₃}}` and `x_{C,{e₂,e₄}}` for each `C ∈ 𝒞_4`, and one edge node `y_e` for each edge occurring in at least one four-cycle" | `FlowNode`: `source`, `sink`, `pair i p` (`x_{C_i, pair p}`), `edgeNode e` (`y_e`); `networkNodes` | Two opposing-pair nodes per enumerated cycle, one edge node per edge in `cycleEdgeList`. |
| "All arcs have unit capacity", arc families 1–3 and their costs | `Arc` (tail, head, cost); `sourceArcs`, `pairArcs`, `sinkArcs`; `fourCycleNetwork` **(Challenge)** | Capacity one is built in: a flow uses each arc at most once. The `ϖ(e)` parallel arcs `y_e → z` have costs `0, …, ϖ(e) − 1`. |
| integral flow of value `2t`, its cost | `IsFlow`, `flowValue`, `flowCost` **(Challenge)** | A flow is a sublist of the arc list conserving flow at all nodes but `s` and `z`. |

## Appendix A, proof of Theorem 2

| Manuscript | Lean |
|---|---|
| "choosing a length-two subpath is equivalent to choosing one edge from each of the opposing pairs" | `Paper.opposing_pair_choices`, `Paper.opposing_pair_choices_complete`; `chosenEdge`, `optionIndex`, `mem_selected_four_iff`, `pair_mem_selected_unique` |
| "There are `2t` opposing-pair nodes and at most `4t` edge nodes", "at most `6t + 2` vertices and exactly `10t` arcs" | `Paper.network_node_counts`, `Paper.network_arc_count` (exactly `10t`) |
| costs `0, 1, …, ϖ(e) − 1`, "all costs lie between zero and `t − 1`" | `Paper.sink_arc_costs`, `arc_cost_lt` |
| "From assignments to flows": "`τ` induces a feasible integral flow of value `2t` and cost `c(τ)`. In particular, a feasible flow always exists" | `flow_of_assignment`, `Paper.assignment_to_flow`, `Paper.flow_exists` |
| "The inflow at `y_e` is then exactly `l(e)`", "`∑_{j=0}^{l(e)−1} j = binom(l(e), 2)`" | `inflow_edge_eq_load`, `sum_range_if_lt`, `sum_range_if_ge_pairCount` |
| "From flows to assignments": "each opposing-pair node receives one unit and sends it along exactly one of its two outgoing arcs", "the two selected edges ... form a valid length-two subpath" | `assignment_of_flow`: `hsource`, `hpair`, the `optionIndex` construction; `Paper.flow_to_assignment` |
| "Optimality forces the flow to use the `l(e)` cheapest arcs", "the minimum flow cost is `OPT`" | `assignment_of_flow` (cost at most the flow's), `cpap4_iff_flow` |
| Theorem 2, the reduction | `cpap4_iff_flow` **(Challenge)**, `Paper.fourCycle_flow_reduction` |
| Theorem 2, size of the network | `fourCycleNetwork_size` **(Challenge)**, `Paper.fourCycle_network_size` |

## Section 3: the triangle flow reduction

| Manuscript | Lean |
|---|---|
| "replacing the opposing-pair nodes with one node `x_C` for each triangle `C`" | `FlowNode.triangle`, `triangleAt`, `triangleNodes` **(Challenge)** |
| "a unit-capacity, zero-cost arc from the source to `x_C` and from `x_C` to each of the three edge nodes `y_e` with `e ∈ E(C)`" | `triangleSourceArcs`, `triangleEdgeArcs` **(Challenge)**, `Paper.triangle_network_arcs` |
| "the same bundles of unit-capacity arcs from each `y_e` to the sink, with costs `0, …, ϖ(e) − 1`" | `triangleEdgeList`, `triangleCount`, `triangleSinkArcs`, `triangleNetwork` **(Challenge)** |
| a triangle's paths of one edge | `selectedOptions_three`, `mem_selectedOptions_three`, `Paper.triangle_paths` |
| "An integral flow of value `t` selects one edge per triangle" | `triangle_assignment_of_flow` (every source arc is used, each triangle node sends its unit along exactly one edge arc, `triangleChoice`), `inflow_triangle_edge_eq_load` |
| "and has minimum cost exactly when the corresponding assignment is optimal" | `triangle_flow_of_assignment` (same cost), `triangle_assignment_of_flow` (no greater cost), `Paper.triangle_correspondence`, `cpap3_iff_flow` **(Challenge)**, `Paper.corollary_k3` |
| "The network has `O(t)` vertices and arcs" | `triangleNetwork_length` (`7t`), `triangleNodes_length_le` (`≤ 4t + 2`), `triangleNetwork_size` **(Challenge)**, `Paper.corollary_k3_size` |

## Runtime boundary and companion proofs

This package proves the flow correspondence and network sizes. The companion
`cpap-runtimes` package proves the executed four-cycle listing
(`STACS2027.Runtimes.C4.fourCycles_ram_semantic`), construction and extraction
(`STACS2027.Runtimes.Flow.cpap4_flow_ram_semantic`), and Corollary 3's pipeline
(`STACS2027.Runtimes.cpap4_enum_ram_semantic`). Its
`STACS2027.Runtimes.fourCycleAssignment_single` also executes listing, packing
and assignment solving in one RAM program. The sorted construction theorem
`STACS2027.Runtimes.Flow.sortedNetworkConstruction` handles every valid cycle
permutation with memory independent of the vertex labels.

The running-time statements use the explicit cited almost-linear min-cost-flow
contract. Its implementation remains the sole external algorithmic contract.
The four-cycle enumeration citations stay in the manuscript; the companion
package supplies a verified listing procedure meeting the required bound.

## Differences from the manuscript

* The cycles are those enumerated by `cycles g 4` of the `cpap-np-hardness` formalization, each
  edge set once, and `t` is the length of that list.
* Parallel arcs are told apart by their costs; a flow is a sublist of the arc
  list, so "the cheapest available sink arcs" are a choice the proof makes
  (`assignmentPredicate`) rather than a property of every flow, and the
  converse direction bounds the cost of any choice from below.
