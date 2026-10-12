module

import Tractability

/-!
Exact-message axiom guards for every explicitly named Tractability declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.sum_map_le_sum_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_le_sum_map

/-- info: 'STACS2027.opposingPair_countP_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.opposingPair_countP_selected

/-- info: 'STACS2027.inflow_edge_eq_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_edge_eq_load

/-- info: 'STACS2027.path_edges_mem_cycleEdgeList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.path_edges_mem_cycleEdgeList

/-- info: 'STACS2027.load_le_cycleCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_le_cycleCount

/-- info: 'STACS2027.load_eq_zero_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_eq_zero_of_not_mem

/-- info: 'STACS2027.cost_paths_eq_load_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_paths_eq_load_sum

/-- info: 'STACS2027.assignmentPredicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assignmentPredicate

/-- info: 'STACS2027.flow_of_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.flow_of_assignment

/-- info: 'STACS2027.assignment_of_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assignment_of_flow

/-- info: 'STACS2027.cpap4_iff_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap4_iff_flow

/-- info: 'STACS2027.FlowNode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.FlowNode

/-- info: 'STACS2027.FlowNode.beq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.FlowNode.beq

/-- info: 'STACS2027.Arc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Arc

/-- info: 'STACS2027.opposingPair' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.opposingPair

/-- info: 'STACS2027.cycleEdgeList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdgeList

/-- info: 'STACS2027.cycleCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleCount

/-- info: 'STACS2027.sourceArcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceArcs

/-- info: 'STACS2027.fourCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fourCycle

/-- info: 'STACS2027.pairArcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairArcs

/-- info: 'STACS2027.sinkArcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sinkArcs

/-- info: 'STACS2027.fourCycleNetwork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fourCycleNetwork

/-- info: 'STACS2027.networkNodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.networkNodes

/-- info: 'STACS2027.inflow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.inflow

/-- info: 'STACS2027.outflow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.outflow

/-- info: 'STACS2027.IsFlow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsFlow

/-- info: 'STACS2027.flowValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.flowValue

/-- info: 'STACS2027.flowCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.flowCost

/-- info: 'STACS2027.getD_map_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.getD_map_range

/-- info: 'STACS2027.map_getD_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.map_getD_range

/-- info: 'STACS2027.fourCycle_isCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fourCycle_isCycle

/-- info: 'STACS2027.fourCycle_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fourCycle_mem

/-- info: 'STACS2027.opposingPair_fourCycle_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.opposingPair_fourCycle_nodup

/-- info: 'STACS2027.countP_eq_sum_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_eq_sum_range

/-- info: 'STACS2027.cycleCount_eq_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleCount_eq_countP

/-- info: 'STACS2027.cycleCount_eq_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleCount_eq_sum

/-- info: 'STACS2027.validChoices_getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.validChoices_getD

/-- info: 'STACS2027.validChoices_of_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.validChoices_of_getD

/-- info: 'STACS2027.load_eq_sum_indicator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_eq_sum_indicator

/-- info: 'STACS2027.sourceLayer_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceLayer_nodup

/-- info: 'STACS2027.pairLayer_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairLayer_nodup

/-- info: 'STACS2027.sinkLayer_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sinkLayer_nodup

/-- info: 'STACS2027.fourCycleNetwork_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fourCycleNetwork_nodup

/-- info: 'STACS2027.Sublist.filter_mem_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Sublist.filter_mem_eq

/-- info: 'STACS2027.countP_lt_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_lt_range

/-- info: 'STACS2027.sum_range_if_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_range_if_lt

/-- info: 'STACS2027.sum_range_if_ge_pairCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_range_if_ge_pairCount

/-- info: 'STACS2027.edge_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_eq_iff

/-- info: 'STACS2027.edge_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_comm

/-- info: 'STACS2027.fourCycle_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fourCycle_shape

/-- info: 'STACS2027.cycleEdges_four' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_four

/-- info: 'STACS2027.opposingPair_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.opposingPair_four

/-- info: 'STACS2027.selected_four' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.selected_four

/-- info: 'STACS2027.selectedOptions_four' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.selectedOptions_four

/-- info: 'STACS2027.fourCycle_edges_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fourCycle_edges_distinct

/-- info: 'STACS2027.chosenEdge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.chosenEdge

/-- info: 'STACS2027.optionIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.optionIndex

/-- info: 'STACS2027.optionIndex_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.optionIndex_lt

/-- info: 'STACS2027.chosenEdge_four' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.chosenEdge_four

/-- info: 'STACS2027.chosenEdge_optionIndex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.chosenEdge_optionIndex

/-- info: 'STACS2027.mem_selected_four_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.mem_selected_four_iff

/-- info: 'STACS2027.chosenEdge_mem_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chosenEdge_mem_pair

/-- info: 'STACS2027.chosenEdge_mem_selected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.chosenEdge_mem_selected

/-- info: 'STACS2027.pair_mem_selected_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pair_mem_selected_unique

/-- info: 'STACS2027.mem_opposingPair_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_opposingPair_four

/-- info: 'STACS2027.opposingPair_sub_cycleEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.opposingPair_sub_cycleEdges

/-- info: 'STACS2027.opposingPair_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.opposingPair_nodup

/-- info: 'STACS2027.opposingPair_length_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.opposingPair_length_four

/-- info: 'STACS2027.cycleEdges_four_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_four_nodup

/-- info: 'STACS2027.mem_selectedOptions_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_selectedOptions_four

/-- info: 'STACS2027.FlowNode.beq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.FlowNode.beq_iff

/-- info: 'STACS2027.FlowNode.beq_eq_decide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.FlowNode.beq_eq_decide

/-- info: 'STACS2027.Arc.ext_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Arc.ext_iff

/-- info: 'STACS2027.sum_map_range_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_range_single

/-- info: 'STACS2027.sum_map_single' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sum_map_single

/-- info: 'STACS2027.sum_flatMap_nat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sum_flatMap_nat

/-- info: 'STACS2027.countP_flatMap'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_flatMap'

/-- info: 'STACS2027.sourceLayer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sourceLayer

/-- info: 'STACS2027.pairLayer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pairLayer

/-- info: 'STACS2027.sinkLayer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sinkLayer

/-- info: 'STACS2027.sourceArcs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceArcs_eq

/-- info: 'STACS2027.pairArcs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairArcs_eq

/-- info: 'STACS2027.sinkArcs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sinkArcs_eq

/-- info: 'STACS2027.sourceLayer_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceLayer_countP

/-- info: 'STACS2027.sourceLayer_head_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceLayer_head_pair

/-- info: 'STACS2027.sourceLayer_head_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceLayer_head_other

/-- info: 'STACS2027.mem_sourceLayer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_sourceLayer

/-- info: 'STACS2027.sourceLayer_tail_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceLayer_tail_source

/-- info: 'STACS2027.sourceLayer_tail_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceLayer_tail_other

/-- info: 'STACS2027.sourceLayer_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceLayer_length

/-- info: 'STACS2027.pairLayer_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairLayer_countP

/-- info: 'STACS2027.mem_pairLayer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_pairLayer

/-- info: 'STACS2027.pairLayer_tail_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairLayer_tail_pair

/-- info: 'STACS2027.pairLayer_tail_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairLayer_tail_other

/-- info: 'STACS2027.pairLayer_head_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairLayer_head_other

/-- info: 'STACS2027.countP_eq_mem_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_eq_mem_indicator

/-- info: 'STACS2027.pairLayer_head_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairLayer_head_edge

/-- info: 'STACS2027.mem_sinkLayer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_sinkLayer

/-- info: 'STACS2027.sinkLayer_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sinkLayer_countP

/-- info: 'STACS2027.sinkLayer_head_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sinkLayer_head_other

/-- info: 'STACS2027.sinkLayer_tail_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sinkLayer_tail_other

/-- info: 'STACS2027.sinkLayer_tail_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sinkLayer_tail_edge

/-- info: 'STACS2027.sinkLayer_cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sinkLayer_cost

/-- info: 'STACS2027.nodup_eraseDups' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.nodup_eraseDups

/-- info: 'STACS2027.cycleEdgeList_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdgeList_nodup

/-- info: 'STACS2027.mem_cycleEdgeList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_cycleEdgeList

/-- info: 'STACS2027.flowOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.flowOf

/-- info: 'STACS2027.flowOf_sublist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.flowOf_sublist

/-- info: 'STACS2027.inflow_flowOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_flowOf

/-- info: 'STACS2027.outflow_flowOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outflow_flowOf

/-- info: 'STACS2027.flowCost_flowOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.flowCost_flowOf

/-- info: 'STACS2027.flowValue_flowOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.flowValue_flowOf

/-- info: 'STACS2027.inflow_flowOf_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_flowOf_pair

/-- info: 'STACS2027.outflow_flowOf_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outflow_flowOf_pair

/-- info: 'STACS2027.inflow_flowOf_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_flowOf_edge

/-- info: 'STACS2027.outflow_flowOf_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outflow_flowOf_edge

/-- info: 'STACS2027.inflow_flowOf_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_flowOf_triangle

/-- info: 'STACS2027.outflow_flowOf_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outflow_flowOf_triangle

/-- info: 'STACS2027.inflow_flowOf_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_flowOf_source

/-- info: 'STACS2027.outflow_flowOf_sink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outflow_flowOf_sink

/-- info: 'STACS2027.pairLayer_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairLayer_length

/-- info: 'STACS2027.sinkLayer_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sinkLayer_length

/-- info: 'STACS2027.length_eraseDups_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.length_eraseDups_le

/-- info: 'STACS2027.cycleEdgeList_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdgeList_length_le

/-- info: 'STACS2027.countP_mem_eq_sum_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_mem_eq_sum_count

/-- info: 'STACS2027.countP_cycleEdges_eq_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_cycleEdges_eq_four

/-- info: 'STACS2027.sum_cycleCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_cycleCount

/-- info: 'STACS2027.fourCycleNetwork_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fourCycleNetwork_length

/-- info: 'STACS2027.pairNodes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairNodes_length

/-- info: 'STACS2027.networkNodes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.networkNodes_length

/-- info: 'STACS2027.networkNodes_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.networkNodes_length_le

/-- info: 'STACS2027.arc_nodes_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.arc_nodes_mem

/-- info: 'STACS2027.cycleCount_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleCount_le

/-- info: 'STACS2027.arc_cost_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.arc_cost_lt

/-- info: 'STACS2027.fourCycleNetwork_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fourCycleNetwork_size

/-- info: 'STACS2027.Paper.opposing_pair_choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.opposing_pair_choices

/-- info: 'STACS2027.Paper.opposing_pair_choices_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.opposing_pair_choices_complete

/-- info: 'STACS2027.Paper.network_node_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.network_node_counts

/-- info: 'STACS2027.Paper.network_arc_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.network_arc_count

/-- info: 'STACS2027.Paper.sink_arc_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.sink_arc_costs

/-- info: 'STACS2027.Paper.assignment_to_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.assignment_to_flow

/-- info: 'STACS2027.Paper.flow_to_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.flow_to_assignment

/-- info: 'STACS2027.Paper.flow_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.flow_exists

/-- info: 'STACS2027.Paper.fourCycle_flow_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.fourCycle_flow_reduction

/-- info: 'STACS2027.Paper.fourCycle_network_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.fourCycle_network_size

/-- info: 'STACS2027.Paper.triangle_network_arcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.triangle_network_arcs

/-- info: 'STACS2027.Paper.triangle_paths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.triangle_paths

/-- info: 'STACS2027.Paper.triangle_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.triangle_correspondence

/-- info: 'STACS2027.Paper.corollary_k3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.corollary_k3

/-- info: 'STACS2027.Paper.corollary_k3_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.corollary_k3_size

/-- info: 'STACS2027.triangleSourceLayer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.triangleSourceLayer

/-- info: 'STACS2027.triangleLayer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.triangleLayer

/-- info: 'STACS2027.triangleSourceArcs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleSourceArcs_eq

/-- info: 'STACS2027.triangleEdgeArcs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleEdgeArcs_eq

/-- info: 'STACS2027.triangleSinkArcs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleSinkArcs_eq

/-- info: 'STACS2027.triangleSourceLayer_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleSourceLayer_countP

/-- info: 'STACS2027.mem_triangleSourceLayer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_triangleSourceLayer

/-- info: 'STACS2027.triangleSourceLayer_head_triangle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleSourceLayer_head_triangle

/-- info: 'STACS2027.triangleSourceLayer_head_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleSourceLayer_head_other

/-- info: 'STACS2027.triangleSourceLayer_tail_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleSourceLayer_tail_source

/-- info: 'STACS2027.triangleSourceLayer_tail_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleSourceLayer_tail_other

/-- info: 'STACS2027.triangleSourceLayer_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.triangleSourceLayer_length

/-- info: 'STACS2027.triangleLayer_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleLayer_countP

/-- info: 'STACS2027.mem_triangleLayer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_triangleLayer

/-- info: 'STACS2027.triangleLayer_tail_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleLayer_tail_triangle

/-- info: 'STACS2027.triangleLayer_tail_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleLayer_tail_other

/-- info: 'STACS2027.triangleLayer_head_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleLayer_head_other

/-- info: 'STACS2027.triangleLayer_head_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleLayer_head_edge

/-- info: 'STACS2027.triangleSourceLayer_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleSourceLayer_nodup

/-- info: 'STACS2027.triangleLayer_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleLayer_nodup

/-- info: 'STACS2027.triangleNetwork_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleNetwork_nodup

/-- info: 'STACS2027.triangleFlowOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleFlowOf

/-- info: 'STACS2027.triangleFlowOf_sublist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleFlowOf_sublist

/-- info: 'STACS2027.inflow_triangleFlowOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_triangleFlowOf

/-- info: 'STACS2027.outflow_triangleFlowOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outflow_triangleFlowOf

/-- info: 'STACS2027.flowCost_triangleFlowOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.flowCost_triangleFlowOf

/-- info: 'STACS2027.flowValue_triangleFlowOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.flowValue_triangleFlowOf

/-- info: 'STACS2027.inflow_triangleFlowOf_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_triangleFlowOf_triangle

/-- info: 'STACS2027.outflow_triangleFlowOf_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outflow_triangleFlowOf_triangle

/-- info: 'STACS2027.inflow_triangleFlowOf_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_triangleFlowOf_edge

/-- info: 'STACS2027.outflow_triangleFlowOf_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outflow_triangleFlowOf_edge

/-- info: 'STACS2027.inflow_triangleFlowOf_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_triangleFlowOf_pair

/-- info: 'STACS2027.outflow_triangleFlowOf_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outflow_triangleFlowOf_pair

/-- info: 'STACS2027.triangle_path_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangle_path_edge

/-- info: 'STACS2027.triangle_edge_mem_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangle_edge_mem_list

/-- info: 'STACS2027.inflow_triangle_edge_eq_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inflow_triangle_edge_eq_load

/-- info: 'STACS2027.load_le_triangleCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_le_triangleCount

/-- info: 'STACS2027.triangle_load_eq_zero_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangle_load_eq_zero_of_not_mem

/-- info: 'STACS2027.triangle_cost_eq_load_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangle_cost_eq_load_sum

/-- info: 'STACS2027.triangleAssignmentPredicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleAssignmentPredicate

/-- info: 'STACS2027.triangle_flow_of_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangle_flow_of_assignment

/-- info: 'STACS2027.countP_one_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_one_unique

/-- info: 'STACS2027.triangleChoice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleChoice

/-- info: 'STACS2027.triangle_assignment_of_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangle_assignment_of_flow

/-- info: 'STACS2027.cpap3_iff_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap3_iff_flow

/-- info: 'STACS2027.triangleAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleAt

/-- info: 'STACS2027.triangleEdgeList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleEdgeList

/-- info: 'STACS2027.triangleCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleCount

/-- info: 'STACS2027.triangleSourceArcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleSourceArcs

/-- info: 'STACS2027.triangleEdgeArcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleEdgeArcs

/-- info: 'STACS2027.triangleSinkArcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleSinkArcs

/-- info: 'STACS2027.triangleNetwork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleNetwork

/-- info: 'STACS2027.triangleNodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleNodes

/-- info: 'STACS2027.triangle_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangle_shape

/-- info: 'STACS2027.cycleEdges_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_three

/-- info: 'STACS2027.triangle_edges_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangle_edges_distinct

/-- info: 'STACS2027.cycleEdges_three_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_three_nodup

/-- info: 'STACS2027.selectedOptions_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.selectedOptions_three

/-- info: 'STACS2027.mem_selectedOptions_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_selectedOptions_three

/-- info: 'STACS2027.triangleAt_isCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleAt_isCycle

/-- info: 'STACS2027.triangleAt_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleAt_mem

/-- info: 'STACS2027.triangleAt_edges_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleAt_edges_nodup

/-- info: 'STACS2027.triangleAt_edges_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleAt_edges_length

/-- info: 'STACS2027.triangleEdgeList_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleEdgeList_nodup

/-- info: 'STACS2027.mem_triangleEdgeList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_triangleEdgeList

/-- info: 'STACS2027.triangleCount_eq_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleCount_eq_countP

/-- info: 'STACS2027.triangleCount_eq_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleCount_eq_sum

/-- info: 'STACS2027.triangleLayer_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleLayer_length

/-- info: 'STACS2027.triangleEdgeList_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleEdgeList_length_le

/-- info: 'STACS2027.countP_cycleEdges_eq_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_cycleEdges_eq_three

/-- info: 'STACS2027.sum_triangleCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_triangleCount

/-- info: 'STACS2027.triangleNetwork_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleNetwork_length

/-- info: 'STACS2027.triangleNodes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleNodes_length

/-- info: 'STACS2027.triangleNodes_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleNodes_length_le

/-- info: 'STACS2027.triangle_arc_nodes_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangle_arc_nodes_mem

/-- info: 'STACS2027.triangleCount_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleCount_le

/-- info: 'STACS2027.triangle_arc_cost_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangle_arc_cost_lt

/-- info: 'STACS2027.triangleNetwork_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.triangleNetwork_size
