module

import all ApproximationHardness

/-!
Exact-message axiom guards for every explicitly named ApproximationHardness declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.flipAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.flipAt

/-- info: 'STACS2027.evalLiteral_flipAt_self' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalLiteral_flipAt_self

/-- info: 'STACS2027.evalLiteral_flipAt_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalLiteral_flipAt_other

/-- info: 'STACS2027.placedClause_unsat_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedClause_unsat_witness

/-- info: 'STACS2027.formulaGraph_cost_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_cost_upper_bound

/-- info: 'STACS2027.formulaGraph_hasAssignment_of_satisfiedCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_hasAssignment_of_satisfiedCount

/-- info: 'STACS2027.LReductionSat.comp_cpap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LReductionSat.comp_cpap

/-- info: 'STACS2027.leOneLeTwo_lreduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.leOneLeTwo_lreduction

/-- info: 'STACS2027.threeOccurrence_cpap_lreduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.threeOccurrence_cpap_lreduction

/-- info: 'STACS2027.approximation_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.approximation_transfer

/-- info: 'STACS2027.crossCost_append_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.crossCost_append_left

/-- info: 'STACS2027.crossCost_flatMap_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.crossCost_flatMap_left

/-- info: 'STACS2027.sum_map_filter_of_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sum_map_filter_of_zero

/-- info: 'STACS2027.overlap_sum_eq_ports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_sum_eq_ports

/-- info: 'STACS2027.crossCost_eq_ports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.crossCost_eq_ports

/-- info: 'STACS2027.nodup_of_length_le_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.nodup_of_length_le_one

/-- info: 'STACS2027.placed_clause_filter_var_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placed_clause_filter_var_length

/-- info: 'STACS2027.sharedPorts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sharedPorts

/-- info: 'STACS2027.sharedPorts_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sharedPorts_nodup

/-- info: 'STACS2027.shared_edge_mem_sharedPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.shared_edge_mem_sharedPorts

/-- info: 'STACS2027.crossCost_variable_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.crossCost_variable_clause

/-- info: 'STACS2027.crossCost_global_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.crossCost_global_eq

/-- info: 'STACS2027.sum_flatMap_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sum_flatMap_range

/-- info: 'STACS2027.clauseLoad_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseLoad_family

/-- info: 'STACS2027.weightedLoad_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.weightedLoad_state

/-- info: 'STACS2027.decode_error_bound_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.decode_error_bound_explicit

/-- info: 'STACS2027.cpap_lreduction_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap_lreduction_decoder

/-- info: 'STACS2027.blockOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.blockOf

/-- info: 'STACS2027.outsideBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.outsideBlock

/-- info: 'STACS2027.portEdgeG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.portEdgeG

/-- info: 'STACS2027.clauseLoad' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseLoad

/-- info: 'STACS2027.decodeAssign' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.decodeAssign

/-- info: 'STACS2027.outsideBlock_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outsideBlock_perm

/-- info: 'STACS2027.blockOf_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.blockOf_block

/-- info: 'STACS2027.variableRegion_of_blockOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableRegion_of_blockOf

/-- info: 'STACS2027.blockOf_of_variableRegion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.blockOf_of_variableRegion

/-- info: 'STACS2027.edge_normal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_normal

/-- info: 'STACS2027.mem_mapGraph_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_mapGraph_edge

/-- info: 'STACS2027.portEdgeG_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.portEdgeG_eq

/-- info: 'STACS2027.variablePortEdge_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.variablePortEdge_lt

/-- info: 'STACS2027.portEdgeG_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.portEdgeG_blocks

/-- info: 'STACS2027.portEdgeG_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.portEdgeG_mem

/-- info: 'STACS2027.variablePortEdge_inj3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variablePortEdge_inj3

/-- info: 'STACS2027.variablePortEdge_swap3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variablePortEdge_swap3

/-- info: 'STACS2027.portEdgeG_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.portEdgeG_inj

/-- info: 'STACS2027.selectedAt_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selectedAt_length

/-- info: 'STACS2027.loadTerm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.loadTerm

/-- info: 'STACS2027.clauseLoad_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseLoad_eq

/-- info: 'STACS2027.loadTerm_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.loadTerm_perm

/-- info: 'STACS2027.loadTerm_variable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.loadTerm_variable

/-- info: 'STACS2027.placed_var_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placed_var_unique

/-- info: 'STACS2027.clause_edge_in_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_edge_in_block

/-- info: 'STACS2027.loadTerm_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.loadTerm_clause

/-- info: 'STACS2027.PathsPerm.sum_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PathsPerm.sum_map

/-- info: 'STACS2027.decoder_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.decoder_transport

/-- info: 'STACS2027.Embed.ForestData.consumptionIds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.consumptionIds

/-- info: 'STACS2027.Embed.ForestData.consAt_ids_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.consAt_ids_nodup

/-- info: 'STACS2027.Embed.ForestData.consumptionIds_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.consumptionIds_nodup

/-- info: 'STACS2027.Embed.ForestData.consumptionIds_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.consumptionIds_lt

/-- info: 'STACS2027.Embed.ForestData.consumptionIds_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.consumptionIds_length_le

/-- info: 'STACS2027.Embed.ForestData.solver_events_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.solver_events_le

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyPrefix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyPrefix

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyPrefix_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyPrefix_succ

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyPrefix_full' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyPrefix_full

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyPrefix_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyPrefix_length

/-- info: 'STACS2027.Embed.DFSRAM.getD_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.getD_snoc

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyStep

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyLoop

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyStep_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyStep_loopFree

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyStep_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyStep_size

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyStep_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyStep_mem

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyStep_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyStep_out

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyStep_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyStep_reg

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyStep_advance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyStep_advance

/-- info: 'STACS2027.Embed.DFSRAM.adjacency_cell_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacency_cell_eq_iff

/-- info: 'STACS2027.Embed.DFSRAM.AdjacencyState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.AdjacencyState

/-- info: 'STACS2027.Embed.DFSRAM.AdjacencyState.smallReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.AdjacencyState.smallReg

/-- info: 'STACS2027.Embed.DFSRAM.AdjacencyState.bases_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.AdjacencyState.bases_step

/-- info: 'STACS2027.Embed.DFSRAM.AdjacencyState.step_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.AdjacencyState.step_cells

/-- info: 'STACS2027.Embed.DFSRAM.AdjacencyState.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.AdjacencyState.step

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyStep_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyStep_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.AdjacencyState.addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.AdjacencyState.addrOK

/-- info: 'STACS2027.Embed.DFSRAM.adjacencyLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.adjacencyLoop_spec

/-- info: 'STACS2027.Embed.DFSRAM.AdjacencyState.tables' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.AdjacencyState.tables

/-- info: 'STACS2027.Embed.cyc_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_congr

/-- info: 'STACS2027.Embed.ForestData.pairF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.pairF

/-- info: 'STACS2027.Embed.ForestData.hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.hyp

/-- info: 'STACS2027.Embed.ForestData.rotN_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotN_inj

/-- info: 'STACS2027.Embed.ForestData.alphaT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.alphaT

/-- info: 'STACS2027.Embed.ForestData.alphaT_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.alphaT_lt

/-- info: 'STACS2027.Embed.ForestData.alphaT_alphaT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.alphaT_alphaT

/-- info: 'STACS2027.Embed.ForestData.sigN_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.sigN_lt

/-- info: 'STACS2027.Embed.ForestData.sigF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.sigF

/-- info: 'STACS2027.Embed.ForestData.sigF_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.sigF_inj

/-- info: 'STACS2027.Embed.ForestData.natp_sigF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.natp_sigF

/-- info: 'STACS2027.Embed.ForestData.backS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.backS

/-- info: 'STACS2027.Embed.ForestData.natS_backS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.natS_backS

/-- info: 'STACS2027.Embed.ForestData.backS_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.backS_pair

/-- info: 'STACS2027.Embed.ForestData.rootOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rootOf

/-- info: 'STACS2027.Embed.ForestData.rootOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rootOf_spec

/-- info: 'STACS2027.Embed.ForestData.mem_W_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mem_W_top

/-- info: 'STACS2027.Embed.ForestData.lt_of_Ftour_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.lt_of_Ftour_top

/-- info: 'STACS2027.Embed.ForestData.tau_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.tau_cyc

/-- info: 'STACS2027.Embed.ForestData.pair_same_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.pair_same_tree

/-- info: 'STACS2027.Embed.ForestData.diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.diag

/-- info: 'STACS2027.Embed.ForestData.roots' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.roots

/-- info: 'STACS2027.Embed.ForestData.mem_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mem_roots

/-- info: 'STACS2027.Embed.ForestData.diag_noncrossing_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.diag_noncrossing_iff

/-- info: 'STACS2027.Embed.countP_le_of_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.countP_le_of_inj

/-- info: 'STACS2027.Embed.ForestData.rotInv_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotInv_cyc

/-- info: 'STACS2027.Embed.ForestData.rotN_rotInvN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotN_rotInvN

/-- info: 'STACS2027.Embed.ForestData.node_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.node_reaches

/-- info: 'STACS2027.Embed.ForestData.numV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.numV

/-- info: 'STACS2027.Embed.ForestData.node_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.node_count

/-- info: 'STACS2027.Embed.ForestData.rootOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rootOf_eq

/-- info: 'STACS2027.Embed.ForestData.rootOf_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rootOf_root

/-- info: 'STACS2027.Embed.ForestData.rootOf_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rootOf_pair

/-- info: 'STACS2027.Embed.ForestData.numC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.numC

/-- info: 'STACS2027.Embed.ForestData.sig_reaches_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.sig_reaches_root

/-- info: 'STACS2027.Embed.ForestData.sig_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.sig_count

/-- info: 'STACS2027.Embed.ForestData.numT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.numT

/-- info: 'STACS2027.Embed.ForestData.tree_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.tree_count

/-- info: 'STACS2027.Embed.ForestData.back_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.back_count

/-- info: 'STACS2027.Embed.ForestData.connected_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.connected_sig

/-- info: 'STACS2027.Embed.ForestData.connected_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.connected_iterate

/-- info: 'STACS2027.Embed.ForestData.component_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.component_count

/-- info: 'STACS2027.Embed.ForestData.face_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.face_eq

/-- info: 'STACS2027.Embed.ForestData.face_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.face_inj

/-- info: 'STACS2027.Embed.ForestData.face_firstReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.face_firstReturn

/-- info: 'STACS2027.Embed.ForestData.pairF_graphEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.pairF_graphEdge

/-- info: 'STACS2027.Embed.ForestData.hyp_planar_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.hyp_planar_iff

/-- info: 'STACS2027.Embed.hypermap_ext' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.hypermap_ext

/-- info: 'STACS2027.Embed.cyc_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_unique

/-- info: 'STACS2027.Embed.iterate_two_cycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.iterate_two_cycle

/-- info: 'STACS2027.Embed.orbit_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.orbit_three

/-- info: 'STACS2027.Embed.orbit_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.orbit_two

/-- info: 'STACS2027.Embed.orbit_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.orbit_one

/-- info: 'STACS2027.Embed.cyc_small' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_small

/-- info: 'STACS2027.Embed.ForestData.graphEdge_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.graphEdge_eq

/-- info: 'STACS2027.Embed.ForestData.anchor' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.anchor

/-- info: 'STACS2027.Embed.ForestData.bitsOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.bitsOf

/-- info: 'STACS2027.Embed.ForestData.cyc_bitsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.cyc_bitsOf

/-- info: 'STACS2027.Embed.ForestData.exists_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.exists_bits

/-- info: 'STACS2027.Embed.ForestData.hyp_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.hyp_valid

/-- info: 'STACS2027.Embed.ForestData.below_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.below_top

/-- info: 'STACS2027.Embed.ForestData.fork_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.fork_below

/-- info: 'STACS2027.Embed.ForestData.top_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.top_closed

/-- info: 'STACS2027.Embed.ForestData.exists_planar_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.exists_planar_iff

/-- info: 'STACS2027.Embed.RAMSolver.orientationBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationBase

/-- info: 'STACS2027.Embed.RAMSolver.keyBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyBase

/-- info: 'STACS2027.Embed.RAMSolver.nextBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nextBase

/-- info: 'STACS2027.Embed.RAMSolver.predBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.predBase

/-- info: 'STACS2027.Embed.RAMSolver.bufferLimit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.bufferLimit

/-- info: 'STACS2027.Embed.RAMSolver.bufferHeaders' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.bufferHeaders

/-- info: 'STACS2027.Embed.RAMSolver.orientationLayout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationLayout

/-- info: 'STACS2027.Embed.RAMSolver.bufferHeaders_values' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.bufferHeaders_values

/-- info: 'STACS2027.Embed.RAMSolver.bufferHeaders_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.bufferHeaders_frame

/-- info: 'STACS2027.Embed.RAMSolver.bufferHeaders_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.bufferHeaders_spec

/-- info: 'STACS2027.Embed.RAMSolver.readoutHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readoutHeader

/-- info: 'STACS2027.Embed.RAMSolver.readoutHeader_values' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readoutHeader_values

/-- info: 'STACS2027.Embed.RAMSolver.readoutHeader_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readoutHeader_frame

/-- info: 'STACS2027.Embed.RAMSolver.readoutHeader_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readoutHeader_spec

/-- info: 'STACS2027.Embed.countP_congr'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.countP_congr'

/-- info: 'STACS2027.Embed.countP_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.countP_one

/-- info: 'STACS2027.Embed.countP_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.countP_two

/-- info: 'STACS2027.Embed.countP_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.countP_split

/-- info: 'STACS2027.Embed.countP_add_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.countP_add_not

/-- info: 'STACS2027.Embed.cycleMin_of_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cycleMin_of_fixed

/-- info: 'STACS2027.Embed.iterate_of_fixed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.iterate_of_fixed

/-- info: 'STACS2027.Embed.meetsB_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.meetsB_false

/-- info: 'STACS2027.Embed.meetsB_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.meetsB_true

/-- info: 'STACS2027.Embed.hitTime0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.hitTime0_le

/-- info: 'STACS2027.Embed.hitTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.hitTime_le

/-- info: 'STACS2027.Embed.pairSet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.pairSet

/-- info: 'STACS2027.Embed.nextIn_pair_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.nextIn_pair_iff

/-- info: 'STACS2027.Embed.Diagram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram

/-- info: 'STACS2027.Embed.Diagram.faces' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.faces

/-- info: 'STACS2027.Embed.Diagram.chord_inj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.chord_inj

/-- info: 'STACS2027.Embed.Diagram.chord_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.chord_mem

/-- info: 'STACS2027.Embed.Diagram.tour_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.tour_mem

/-- info: 'STACS2027.Embed.Diagram.iterate_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.iterate_mem

/-- info: 'STACS2027.Embed.Diagram.faces_inj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.faces_inj

/-- info: 'STACS2027.Embed.Diagram.faces_fix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.faces_fix

/-- info: 'STACS2027.Embed.Diagram.faces_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.faces_mem

/-- info: 'STACS2027.Embed.Diagram.tour_ne_self' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.tour_ne_self

/-- info: 'STACS2027.Embed.Diagram.reach_chord_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.reach_chord_pos

/-- info: 'STACS2027.Embed.Diagram.InArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.InArc

/-- info: 'STACS2027.Embed.Diagram.NonCrossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.NonCrossing

/-- info: 'STACS2027.Embed.Diagram.meetsFrom_pair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.meetsFrom_pair

/-- info: 'STACS2027.Embed.Diagram.inArc_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.inArc_iff

/-- info: 'STACS2027.Embed.Diagram.inArc_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.inArc_adjacent

/-- info: 'STACS2027.Embed.Diagram.Short' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.Short

/-- info: 'STACS2027.Embed.Diagram.span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.span

/-- info: 'STACS2027.Embed.Diagram.span_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.span_spec

/-- info: 'STACS2027.Embed.Diagram.exists_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.exists_short

/-- info: 'STACS2027.Embed.Diagram.exists_short_of_faces_invol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.exists_short_of_faces_invol

/-- info: 'STACS2027.Embed.Diagram.keepS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.keepS

/-- info: 'STACS2027.Embed.Diagram.keepS_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.keepS_iff

/-- info: 'STACS2027.Embed.Diagram.keepS_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.keepS_false

/-- info: 'STACS2027.Embed.Diagram.keepS_chord' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.keepS_chord

/-- info: 'STACS2027.Embed.Diagram.keepS_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.keepS_sub

/-- info: 'STACS2027.Embed.Diagram.remove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.remove

/-- info: 'STACS2027.Embed.Diagram.remove_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.remove_S

/-- info: 'STACS2027.Embed.Diagram.remove_tour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.remove_tour

/-- info: 'STACS2027.Embed.Diagram.remove_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.remove_chord

/-- info: 'STACS2027.Embed.Diagram.delta' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.delta

/-- info: 'STACS2027.Embed.Diagram.short_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.short_ne

/-- info: 'STACS2027.Embed.Diagram.short_tour_chord_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.short_tour_chord_ne

/-- info: 'STACS2027.Embed.Diagram.countP_not_keepS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.countP_not_keepS

/-- info: 'STACS2027.Embed.Diagram.countP_keepS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.countP_keepS

/-- info: 'STACS2027.Embed.Diagram.avoid_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.avoid_generic

/-- info: 'STACS2027.Embed.Diagram.avoid_tour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.avoid_tour

/-- info: 'STACS2027.Embed.Diagram.avoid_faces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.avoid_faces

/-- info: 'STACS2027.Embed.Diagram.remove_faces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.remove_faces

/-- info: 'STACS2027.Embed.Diagram.remove_tour_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.remove_tour_count

/-- info: 'STACS2027.Embed.Diagram.remove_faces_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.remove_faces_count

/-- info: 'STACS2027.Embed.Diagram.nextIn_firstReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.nextIn_firstReturn

/-- info: 'STACS2027.Embed.Diagram.remove_inArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.remove_inArc

/-- info: 'STACS2027.Embed.Diagram.inArc_short_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.inArc_short_false

/-- info: 'STACS2027.Embed.Diagram.inArc_short_partner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.inArc_short_partner

/-- info: 'STACS2027.Embed.Diagram.noncrossing_remove_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.noncrossing_remove_iff

/-- info: 'STACS2027.Embed.Diagram.preserves_S' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.preserves_S

/-- info: 'STACS2027.Embed.Diagram.iterate_preserves_S' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.iterate_preserves_S

/-- info: 'STACS2027.Embed.Diagram.cmin_preserves_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.cmin_preserves_S

/-- info: 'STACS2027.Embed.Diagram.cycleCount_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.cycleCount_split

/-- info: 'STACS2027.Embed.Diagram.minima_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.minima_bound

/-- info: 'STACS2027.Embed.Diagram.cycleCount_tour_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.cycleCount_tour_pos

/-- info: 'STACS2027.Embed.Diagram.excess_no_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.excess_no_short

/-- info: 'STACS2027.Embed.Diagram.chord_excess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Diagram.chord_excess

/-- info: 'STACS2027.Embed.MergeEntry' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.MergeEntry

/-- info: 'STACS2027.Embed.selectMerge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.selectMerge

/-- info: 'STACS2027.Embed.selectMerge_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.selectMerge_mem

/-- info: 'STACS2027.Embed.selectMerge_of_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.selectMerge_of_mem

/-- info: 'STACS2027.Embed.ForestData.mergeLog' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mergeLog

/-- info: 'STACS2027.Embed.ForestData.mem_mergeLog' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mem_mergeLog

/-- info: 'STACS2027.Embed.ForestData.mergeParents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mergeParents

/-- info: 'STACS2027.Embed.ForestData.mergeFlips' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mergeFlips

/-- info: 'STACS2027.Embed.ForestData.merge_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.merge_records

/-- info: 'STACS2027.Embed.computedOrientation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.computedOrientation

/-- info: 'STACS2027.Embed.computedOrientation_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.computedOrientation_consistent

/-- info: 'STACS2027.Embed.computedRotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.computedRotation

/-- info: 'STACS2027.Embed.computedRotation_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.computedRotation_planar

/-- info: 'STACS2027.Embed.computedChoices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.computedChoices

/-- info: 'STACS2027.Embed.computedChoices_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.computedChoices_planar

/-- info: 'STACS2027.Embed.computed_reduction_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.computed_reduction_planar

/-- info: 'STACS2027.Embed.PlanarEmbeddingLinearRAM' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanarEmbeddingLinearRAM

/-- info: 'STACS2027.Embed.cycleMin_iff_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cycleMin_iff_reach

/-- info: 'STACS2027.Embed.nextIn_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.nextIn_congr

/-- info: 'STACS2027.Embed.iterate_congr_avoid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.iterate_congr_avoid

/-- info: 'STACS2027.Embed.avoidCount_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.avoidCount_congr

/-- info: 'STACS2027.Embed.Chain' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Chain

/-- info: 'STACS2027.Embed.chain_cons_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.chain_cons_iff

/-- info: 'STACS2027.Embed.chain_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.chain_append

/-- info: 'STACS2027.Embed.chain_iterate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.chain_iterate

/-- info: 'STACS2027.Embed.chain_maps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.chain_maps

/-- info: 'STACS2027.Embed.Cyc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Cyc

/-- info: 'STACS2027.Embed.cyc_maps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_maps

/-- info: 'STACS2027.Embed.cyc_rot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_rot

/-- info: 'STACS2027.Embed.chain_sublist_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.chain_sublist_mem

/-- info: 'STACS2027.Embed.getLast?_append_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.getLast?_append_cons

/-- info: 'STACS2027.Embed.cyc_one' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_one

/-- info: 'STACS2027.Embed.cyc_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_two

/-- info: 'STACS2027.Embed.cyc_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_three

/-- info: 'STACS2027.Embed.cyc_append_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_append_comm

/-- info: 'STACS2027.Embed.chain_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.chain_join

/-- info: 'STACS2027.Embed.head?_append_of_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.head?_append_of_some

/-- info: 'STACS2027.Embed.getLast?_append_of_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.getLast?_append_of_some

/-- info: 'STACS2027.Embed.getLast?_of_head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.getLast?_of_head

/-- info: 'STACS2027.Embed.natp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.natp

/-- info: 'STACS2027.Embed.natp_val' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.natp_val

/-- info: 'STACS2027.Embed.iterate_natp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.iterate_natp

/-- info: 'STACS2027.Embed.natS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.natS

/-- info: 'STACS2027.Embed.natS_val' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.natS_val

/-- info: 'STACS2027.Embed.reaches_iff_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.reaches_iff_mem

/-- info: 'STACS2027.Embed.nextIn_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.nextIn_chain

/-- info: 'STACS2027.Embed.filter_eq_append_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.filter_eq_append_cons

/-- info: 'STACS2027.Embed.cyc_of_rot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_of_rot

/-- info: 'STACS2027.Embed.cyc_firstReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_firstReturn

/-- info: 'STACS2027.Embed.before_iff_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_iff_idx

/-- info: 'STACS2027.Embed.nodup_rot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.nodup_rot

/-- info: 'STACS2027.Embed.mem_rot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.mem_rot

/-- info: 'STACS2027.Embed.before_at_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_at_iff

/-- info: 'STACS2027.Embed.before_in_B_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_in_B_iff

/-- info: 'STACS2027.Embed.before_rot_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_rot_iff

/-- info: 'STACS2027.Embed.rot_between_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.rot_between_iff

/-- info: 'STACS2027.Embed.wn_of_rot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.wn_of_rot

/-- info: 'STACS2027.Embed.natp_invol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.natp_invol

/-- info: 'STACS2027.Embed.inArc_iff_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.inArc_iff_before

/-- info: 'STACS2027.Embed.noncrossing_iff_wn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.noncrossing_iff_wn

/-- info: 'STACS2027.Embed.upd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.upd

/-- info: 'STACS2027.Embed.upd_same' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.upd_same

/-- info: 'STACS2027.Embed.upd_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.upd_ne

/-- info: 'STACS2027.Embed.upd_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.upd_apply

/-- info: 'STACS2027.Embed.DG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DG

/-- info: 'STACS2027.Embed.DS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DS

/-- info: 'STACS2027.Embed.DG.darts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.darts

/-- info: 'STACS2027.Embed.DG.fd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.fd

/-- info: 'STACS2027.Embed.DG.darts_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.darts_eq

/-- info: 'STACS2027.Embed.DG.nd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.nd

/-- info: 'STACS2027.Embed.DG.nw' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.nw

/-- info: 'STACS2027.Embed.DG.step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.step

/-- info: 'STACS2027.Embed.DG.init' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.init

/-- info: 'STACS2027.Embed.DG.Halted' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.Halted

/-- info: 'STACS2027.Embed.DG.Ok' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.Ok

/-- info: 'STACS2027.Embed.DFSRAM.startRoot_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.startRoot_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.exploreNew_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.exploreNew_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.insideRead_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.insideRead_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.outsideRead_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.outsideRead_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.readNext_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.readNext_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.outsideStep_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.outsideStep_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.finishPrefixProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.finishPrefixProgram

/-- info: 'STACS2027.Embed.DFSRAM.finishPrefix_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.finishPrefix_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.finishStep_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.finishStep_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.exploreRead_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.exploreRead_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.explorePrefix_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.explorePrefix_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.exploreStep_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.exploreStep_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.insideStep_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.insideStep_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.stepProgram_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.stepProgram_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.program_spec

/-- info: 'STACS2027.Embed.IncidenceRAM.prepareForest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.prepareForest

/-- info: 'STACS2027.Embed.IncidenceRAM.prepareForest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.prepareForest_spec

/-- info: 'STACS2027.Embed.DFSRAM.CacheFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.CacheFrame

/-- info: 'STACS2027.Embed.DFSRAM.CacheFrame.noStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.CacheFrame.noStore

/-- info: 'STACS2027.Embed.DFSRAM.CacheFrame.store_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.CacheFrame.store_cell

/-- info: 'STACS2027.Embed.DFSRAM.CacheFrame.seq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.CacheFrame.seq

/-- info: 'STACS2027.Embed.DFSRAM.CacheFrame.ifz' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.CacheFrame.ifz

/-- info: 'STACS2027.Embed.DFSRAM.stepProgram_cacheFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.stepProgram_cacheFrame

/-- info: 'STACS2027.Embed.DFSRAM.Tables.run_cacheFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Tables.run_cacheFrame

/-- info: 'STACS2027.Embed.DFSRAM.Tables.run_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Tables.run_step

/-- info: 'STACS2027.Embed.DG.Inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.Inv

/-- info: 'STACS2027.Embed.DG.mem_darts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.mem_darts

/-- info: 'STACS2027.Embed.DG.darts_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.darts_nodup

/-- info: 'STACS2027.Embed.DG.getD_of_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.getD_of_lt

/-- info: 'STACS2027.Embed.DG.getD_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.getD_mem

/-- info: 'STACS2027.Embed.DG.exists_getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.exists_getD

/-- info: 'STACS2027.Embed.DG.getD_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.getD_inj

/-- info: 'STACS2027.Embed.DG.before_snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.before_snoc

/-- info: 'STACS2027.Embed.DG.nd_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.nd_mem

/-- info: 'STACS2027.Embed.DG.nw_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.nw_facts

/-- info: 'STACS2027.Embed.DG.inv_exploreNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.inv_exploreNew

/-- info: 'STACS2027.Embed.DG.inv_exploreOld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.inv_exploreOld

/-- info: 'STACS2027.Embed.DG.treeOn_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.treeOn_congr

/-- info: 'STACS2027.Embed.DG.fin_neighbours' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.fin_neighbours

/-- info: 'STACS2027.Embed.DG.inv_finishRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.inv_finishRoot

/-- info: 'STACS2027.Embed.DG.inv_finishNonroot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.inv_finishNonroot

/-- info: 'STACS2027.Embed.DG.inv_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.inv_start

/-- info: 'STACS2027.Embed.DG.inv_skip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.inv_skip

/-- info: 'STACS2027.Embed.DG.inv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.inv_step

/-- info: 'STACS2027.Embed.DG.inv_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.inv_init

/-- info: 'STACS2027.Embed.DG.inv_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.inv_iterate

/-- info: 'STACS2027.Embed.DFSRAM.Rep.setCounter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Rep.setCounter

/-- info: 'STACS2027.Embed.DFSRAM.stepProgram_high' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.stepProgram_high

/-- info: 'STACS2027.Embed.DFSRAM.boundedRun_memAbove' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.boundedRun_memAbove

/-- info: 'STACS2027.Embed.DFSRAM.program_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.program_refines

/-- info: 'STACS2027.Embed.DFSRAM.dsArray' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.dsArray

/-- info: 'STACS2027.Embed.DFSRAM.setArray' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.setArray

/-- info: 'STACS2027.Embed.DFSRAM.MemoryRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.MemoryRep

/-- info: 'STACS2027.Embed.DFSRAM.Rep.memory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Rep.memory

/-- info: 'STACS2027.Embed.DFSRAM.array_set' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.array_set

/-- info: 'STACS2027.Embed.DFSRAM.MemoryRep.update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.MemoryRep.update

/-- info: 'STACS2027.Embed.DFSRAM.MemoryRep.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.MemoryRep.push

/-- info: 'STACS2027.Embed.DFSRAM.MemoryRep.of_regs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.MemoryRep.of_regs

/-- info: 'STACS2027.Embed.DFSRAM.Tables.update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Tables.update

/-- info: 'STACS2027.Embed.DFSRAM.Layout' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Layout

/-- info: 'STACS2027.Embed.DFSRAM.Layout.block' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Layout.block

/-- info: 'STACS2027.Embed.DFSRAM.Layout.cell' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Layout.cell

/-- info: 'STACS2027.Embed.DFSRAM.Layout.limit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Layout.limit

/-- info: 'STACS2027.Embed.DFSRAM.dartCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.dartCount

/-- info: 'STACS2027.Embed.DFSRAM.scan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.scan

/-- info: 'STACS2027.Embed.DFSRAM.current' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.current

/-- info: 'STACS2027.Embed.DFSRAM.inner' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.inner

/-- info: 'STACS2027.Embed.DFSRAM.height' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.height

/-- info: 'STACS2027.Embed.DFSRAM.postLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.postLength

/-- info: 'STACS2027.Embed.DFSRAM.remaining' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.remaining

/-- info: 'STACS2027.Embed.DFSRAM.baseRegister' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.baseRegister

/-- info: 'STACS2027.Embed.DFSRAM.widthRegister' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.widthRegister

/-- info: 'STACS2027.Embed.DFSRAM.address' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.address

/-- info: 'STACS2027.Embed.DFSRAM.pointer' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.pointer

/-- info: 'STACS2027.Embed.DFSRAM.degree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.degree

/-- info: 'STACS2027.Embed.DFSRAM.nextDart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.nextDart

/-- info: 'STACS2027.Embed.DFSRAM.opposite' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.opposite

/-- info: 'STACS2027.Embed.DFSRAM.nextVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.nextVertex

/-- info: 'STACS2027.Embed.DFSRAM.parent' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.parent

/-- info: 'STACS2027.Embed.DFSRAM.value' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.value

/-- info: 'STACS2027.Embed.DFSRAM.needHeight' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.needHeight

/-- info: 'STACS2027.Embed.DFSRAM.test' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.test

/-- info: 'STACS2027.Embed.DFSRAM.otherTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.otherTest

/-- info: 'STACS2027.Embed.DFSRAM.repValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.repValue

/-- info: 'STACS2027.Embed.DFSRAM.Bases' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Bases

/-- info: 'STACS2027.Embed.DFSRAM.Tables' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Tables

/-- info: 'STACS2027.Embed.DFSRAM.Rep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Rep

/-- info: 'STACS2027.Embed.DFSRAM.loadCell' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.loadCell

/-- info: 'STACS2027.Embed.DFSRAM.storeCell' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.storeCell

/-- info: 'STACS2027.Embed.DFSRAM.pushPost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.pushPost

/-- info: 'STACS2027.Embed.DFSRAM.advanceScan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.advanceScan

/-- info: 'STACS2027.Embed.DFSRAM.startRoot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.startRoot

/-- info: 'STACS2027.Embed.DFSRAM.outsideRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.outsideRead

/-- info: 'STACS2027.Embed.DFSRAM.outsideStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.outsideStep

/-- info: 'STACS2027.Embed.DFSRAM.readNext' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.readNext

/-- info: 'STACS2027.Embed.DFSRAM.exploreNew' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.exploreNew

/-- info: 'STACS2027.Embed.DFSRAM.exploreRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.exploreRead

/-- info: 'STACS2027.Embed.DFSRAM.explorePrefix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.explorePrefix

/-- info: 'STACS2027.Embed.DFSRAM.exploreStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.exploreStep

/-- info: 'STACS2027.Embed.DFSRAM.finishRoot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.finishRoot

/-- info: 'STACS2027.Embed.DFSRAM.finishChild' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.finishChild

/-- info: 'STACS2027.Embed.DFSRAM.finishStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.finishStep

/-- info: 'STACS2027.Embed.DFSRAM.insideRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.insideRead

/-- info: 'STACS2027.Embed.DFSRAM.insideStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.insideStep

/-- info: 'STACS2027.Embed.DFSRAM.stepProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.stepProgram

/-- info: 'STACS2027.Embed.DFSRAM.loopBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.loopBody

/-- info: 'STACS2027.Embed.DFSRAM.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.program

/-- info: 'STACS2027.Embed.DFSRAM.stepProgram_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.stepProgram_loopFree

/-- info: 'STACS2027.Embed.DFSRAM.stepProgram_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.stepProgram_size

/-- info: 'STACS2027.Embed.DFSRAM.Layout.cell_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Layout.cell_lt

/-- info: 'STACS2027.Embed.DFSRAM.Layout.cell_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Layout.cell_injective

/-- info: 'STACS2027.Embed.DFSRAM.update_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.update_cell

/-- info: 'STACS2027.Embed.DFSRAM.Bases.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Bases.frame

/-- info: 'STACS2027.Embed.DFSRAM.Bases.run_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Bases.run_step

/-- info: 'STACS2027.Embed.DFSRAM.stepProgram_remaining' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.stepProgram_remaining

/-- info: 'STACS2027.Embed.DFSRAM.stepProgram_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.stepProgram_out

/-- info: 'STACS2027.Embed.DFSRAM.startRoot_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.startRoot_raw

/-- info: 'STACS2027.Embed.DFSRAM.finishStep_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.finishStep_raw

/-- info: 'STACS2027.Embed.length_le_of_nodup_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.length_le_of_nodup_lt

/-- info: 'STACS2027.Embed.DG.mu' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.mu

/-- info: 'STACS2027.Embed.DG.step_halted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.step_halted

/-- info: 'STACS2027.Embed.DG.iterate_halted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.iterate_halted

/-- info: 'STACS2027.Embed.DG.bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.bounds

/-- info: 'STACS2027.Embed.DG.mu_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.mu_step

/-- info: 'STACS2027.Embed.DG.halted_of_mu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.halted_of_mu

/-- info: 'STACS2027.Embed.DG.final' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.final

/-- info: 'STACS2027.Embed.DG.mu_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.mu_init

/-- info: 'STACS2027.Embed.DG.halted_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.halted_final

/-- info: 'STACS2027.Embed.DG.inv_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.inv_final

/-- info: 'STACS2027.Embed.DG.final_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.final_fin

/-- info: 'STACS2027.Embed.DG.valid_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.valid_final

/-- info: 'STACS2027.Embed.DG.post_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.post_final

/-- info: 'STACS2027.Embed.IncidenceRAM.dfsPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.dfsPre

/-- info: 'STACS2027.Embed.IncidenceRAM.dfsPre_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.dfsPre_loopFree

/-- info: 'STACS2027.Embed.IncidenceRAM.dfsPre_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.dfsPre_size

/-- info: 'STACS2027.Embed.IncidenceRAM.dfsPre_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.dfsPre_mem

/-- info: 'STACS2027.Embed.IncidenceRAM.dfsPre_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.dfsPre_out

/-- info: 'STACS2027.Embed.IncidenceRAM.dfsPre_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.dfsPre_reg

/-- info: 'STACS2027.Embed.IncidenceRAM.dfsPre_bases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.dfsPre_bases

/-- info: 'STACS2027.Embed.IncidenceRAM.dfsPre_tables' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.dfsPre_tables

/-- info: 'STACS2027.Embed.IncidenceRAM.dfsPre_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.dfsPre_rep

/-- info: 'STACS2027.Embed.DFSRAM.Bases.run_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Bases.run_aux

/-- info: 'STACS2027.Embed.DFSRAM.Tables.mem_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Tables.mem_congr

/-- info: 'STACS2027.Embed.DFSRAM.MemoryRep.congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.MemoryRep.congr

/-- info: 'STACS2027.Embed.DFSRAM.Rep.setGhosts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Rep.setGhosts

/-- info: 'STACS2027.Embed.DFSRAM.Rep.run_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Rep.run_readOnly

/-- info: 'STACS2027.Embed.DFSRAM.Tables.run_readOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Tables.run_readOnly

/-- info: 'STACS2027.Embed.DFSRAM.loadCell_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.loadCell_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.storeCell_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.storeCell_addrOK

/-- info: 'STACS2027.Embed.DFSRAM.insideRead_values' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.insideRead_values

/-- info: 'STACS2027.Embed.DFSRAM.outsideRead_values' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.outsideRead_values

/-- info: 'STACS2027.Embed.DFSRAM.readNext_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.readNext_value

/-- info: 'STACS2027.Embed.DFSRAM.exploreRead_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.exploreRead_values

/-- info: 'STACS2027.Embed.DFSRAM.explorePrefix_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.explorePrefix_refines

/-- info: 'STACS2027.Embed.DFSRAM.startRoot_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.startRoot_refines

/-- info: 'STACS2027.Embed.DFSRAM.exploreNew_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.exploreNew_raw

/-- info: 'STACS2027.Embed.DFSRAM.exploreNew_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.exploreNew_refines

/-- info: 'STACS2027.Embed.DFSRAM.finishStep_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.finishStep_refines

/-- info: 'STACS2027.Embed.DFSRAM.exploreStep_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.exploreStep_refines

/-- info: 'STACS2027.Embed.DFSRAM.insideStep_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.insideStep_refines

/-- info: 'STACS2027.Embed.DFSRAM.advanceScan_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.advanceScan_refines

/-- info: 'STACS2027.Embed.DFSRAM.outsideStep_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.outsideStep_refines

/-- info: 'STACS2027.Embed.DFSRAM.stepProgram_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.stepProgram_refines

/-- info: 'STACS2027.Embed.missingDart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.missingDart

/-- info: 'STACS2027.Embed.filter_missing_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.filter_missing_erase

/-- info: 'STACS2027.Embed.ForestData.defaultCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.defaultCycle

/-- info: 'STACS2027.Embed.ForestData.defaultCycle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.defaultCycle_eq

/-- info: 'STACS2027.Embed.ForestData.distinguished_mem_of_degree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.distinguished_mem_of_degree

/-- info: 'STACS2027.Embed.ForestData.real_parts_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.real_parts_bound

/-- info: 'STACS2027.Embed.ForestData.real_child_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.real_child_bound

/-- info: 'STACS2027.Embed.RAMSolver.bufferHeaders_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.bufferHeaders_context

/-- info: 'STACS2027.Embed.RAMSolver.bufferHeaders_solverRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.bufferHeaders_solverRep

/-- info: 'STACS2027.Embed.RAMSolver.bufferHeaders_solverTables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.bufferHeaders_solverTables

/-- info: 'STACS2027.Embed.RAMSolver.defaultReadyMaterialization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultReadyMaterialization

/-- info: 'STACS2027.Embed.RAMSolver.DefaultFrame.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.DefaultFrame.step

/-- info: 'STACS2027.Embed.RAMSolver.DefaultCacheState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.DefaultCacheState

/-- info: 'STACS2027.Embed.RAMSolver.DefaultCacheState.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.DefaultCacheState.step

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationLoop_spec

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationPre

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationProgram

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationProgram_spec

/-- info: 'STACS2027.Embed.RAMSolver.slotCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.slotCycle

/-- info: 'STACS2027.Embed.RAMSolver.slotCycle_labels' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.slotCycle_labels

/-- info: 'STACS2027.Embed.RAMSolver.slotCycle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.slotCycle_eq

/-- info: 'STACS2027.Embed.RAMSolver.cycleSlots_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.cycleSlots_labels

/-- info: 'STACS2027.Embed.RAMSolver.decodePart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.decodePart

/-- info: 'STACS2027.Embed.RAMSolver.readLeftPart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readLeftPart

/-- info: 'STACS2027.Embed.RAMSolver.readRightPart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readRightPart

/-- info: 'STACS2027.Embed.RAMSolver.decodePart_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.decodePart_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.readLeftPart_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readLeftPart_size

/-- info: 'STACS2027.Embed.RAMSolver.readRightPart_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readRightPart_size

/-- info: 'STACS2027.Embed.RAMSolver.decodePart_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.decodePart_mem

/-- info: 'STACS2027.Embed.RAMSolver.decodePart_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.decodePart_out

/-- info: 'STACS2027.Embed.RAMSolver.readLeftPart_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readLeftPart_value

/-- info: 'STACS2027.Embed.RAMSolver.readRightPart_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readRightPart_value

/-- info: 'STACS2027.Embed.RAMSolver.rotationIfEq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationIfEq

/-- info: 'STACS2027.Embed.RAMSolver.nextPredValues' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nextPredValues

/-- info: 'STACS2027.Embed.RAMSolver.nextPredCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nextPredCode

/-- info: 'STACS2027.Embed.RAMSolver.nextLabel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nextLabel

/-- info: 'STACS2027.Embed.RAMSolver.predLabel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.predLabel

/-- info: 'STACS2027.Embed.RAMSolver.nextPredCode_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nextPredCode_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.nextPredCode_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nextPredCode_mem

/-- info: 'STACS2027.Embed.RAMSolver.nextPredCode_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nextPredCode_out

/-- info: 'STACS2027.Embed.RAMSolver.nextPredCode_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nextPredCode_size

/-- info: 'STACS2027.Embed.RAMSolver.both_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.both_zero_iff

/-- info: 'STACS2027.Embed.RAMSolver.run_rotationIfEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.run_rotationIfEq

/-- info: 'STACS2027.Embed.RAMSolver.nextPredCode_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nextPredCode_values

/-- info: 'STACS2027.Embed.RAMSolver.readBothParts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readBothParts

/-- info: 'STACS2027.Embed.RAMSolver.rotationRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationRead

/-- info: 'STACS2027.Embed.RAMSolver.cycleSlots' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.cycleSlots

/-- info: 'STACS2027.Embed.RAMSolver.rotationRead_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationRead_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.rotationRead_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationRead_size

/-- info: 'STACS2027.Embed.RAMSolver.rotationRead_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationRead_mem

/-- info: 'STACS2027.Embed.RAMSolver.rotationRead_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationRead_out

/-- info: 'STACS2027.Embed.RAMSolver.rotationRead_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationRead_reg

/-- info: 'STACS2027.Embed.RAMSolver.rotationRead_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationRead_values

/-- info: 'STACS2027.Embed.RAMSolver.rotationRead_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationRead_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.defaultSourceRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultSourceRegisters

/-- info: 'STACS2027.Embed.RAMSolver.defaultFixedRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultFixedRegisters

/-- info: 'STACS2027.Embed.RAMSolver.DefaultReady' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.DefaultReady

/-- info: 'STACS2027.Embed.RAMSolver.DefaultFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.DefaultFrame

/-- info: 'STACS2027.Embed.RAMSolver.DefaultFrame.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.DefaultFrame.refl

/-- info: 'STACS2027.Embed.RAMSolver.DefaultFrame.read' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.DefaultFrame.read

/-- info: 'STACS2027.Embed.RAMSolver.DefaultReady.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.DefaultReady.frame

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationStep_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationStep_correct

/-- info: 'STACS2027.Embed.RAMSolver.rotationStore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationStore

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationStep

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationLoop

/-- info: 'STACS2027.Embed.RAMSolver.nextPredCode_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nextPredCode_reg

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationStep_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationStep_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationStep_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationStep_size

/-- info: 'STACS2027.Embed.RAMSolver.rotationStore_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationStore_mem

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationStep_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationStep_out

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationStep_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationStep_reg

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationStep_advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationStep_advance

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationStep_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationStep_mem

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationStep_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationStep_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.defaultSolverProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultSolverProgram

/-- info: 'STACS2027.Embed.RAMSolver.defaultSolverProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultSolverProgram_spec

/-- info: 'STACS2027.Embed.ForestData.below_desc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.below_desc

/-- info: 'STACS2027.Embed.DG.postOrder_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DG.postOrder_final

/-- info: 'STACS2027.Embed.incF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.incF

/-- info: 'STACS2027.Embed.incF_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incF_valid

/-- info: 'STACS2027.Embed.incBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incBits

/-- info: 'STACS2027.Embed.rotOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.rotOut

/-- info: 'STACS2027.Embed.nonempty_of_bounded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.nonempty_of_bounded

/-- info: 'STACS2027.Embed.incidence_reaches_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incidence_reaches_iff

/-- info: 'STACS2027.Embed.rotOut_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.rotOut_planar

/-- info: 'STACS2027.Embed.incidence_forkWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incidence_forkWitness

/-- info: 'STACS2027.Embed.RAMSolver.readoutProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readoutProgram

/-- info: 'STACS2027.Embed.RAMSolver.readoutProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readoutProgram_spec

/-- info: 'STACS2027.Embed.RAMSolver.completedSolver' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.completedSolver

/-- info: 'STACS2027.Embed.RAMSolver.EmbeddingRuntime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.EmbeddingRuntime

/-- info: 'STACS2027.Embed.RAMSolver.EmbeddingRuntime.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.EmbeddingRuntime.frame

/-- info: 'STACS2027.Embed.SMem.evalBit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.SMem.evalBit

/-- info: 'STACS2027.Embed.SMem.evalBit_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.SMem.evalBit_zero

/-- info: 'STACS2027.Embed.SMem.evalBit_target' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.SMem.evalBit_target

/-- info: 'STACS2027.Embed.SMem.evalBit_fork' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.SMem.evalBit_fork

/-- info: 'STACS2027.Embed.cnext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.cnext

/-- info: 'STACS2027.Embed.dropWhile_ne_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.dropWhile_ne_append

/-- info: 'STACS2027.Embed.cnext_rot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cnext_rot

/-- info: 'STACS2027.Embed.cyc_cnext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cyc_cnext

/-- info: 'STACS2027.Embed.cnext_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cnext_mem

/-- info: 'STACS2027.Embed.cnext_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cnext_reverse

/-- info: 'STACS2027.Embed.ForestData.itemDart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.itemDart

/-- info: 'STACS2027.Embed.ForestData.itemDart_item' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.itemDart_item

/-- info: 'STACS2027.Embed.ForestData.cycOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.cycOf

/-- info: 'STACS2027.Embed.ForestData.rotN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotN

/-- info: 'STACS2027.Embed.ForestData.ord_map_itemDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.ord_map_itemDart

/-- info: 'STACS2027.Embed.ForestData.cycOf_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.cycOf_perm

/-- info: 'STACS2027.Embed.ForestData.cycOf_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.cycOf_nodup

/-- info: 'STACS2027.Embed.ForestData.mem_cycOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mem_cycOf

/-- info: 'STACS2027.Embed.ForestData.rotN_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotN_lt

/-- info: 'STACS2027.Embed.ForestData.rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rot

/-- info: 'STACS2027.Embed.ForestData.rotInvN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotInvN

/-- info: 'STACS2027.Embed.ForestData.rotInvN_rotN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotInvN_rotN

/-- info: 'STACS2027.Embed.ForestData.rotInvN_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotInvN_lt

/-- info: 'STACS2027.Embed.ForestData.rotInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotInv

/-- info: 'STACS2027.Embed.ForestData.rot_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rot_inj

/-- info: 'STACS2027.Embed.ForestData.rotN_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotN_cyc

/-- info: 'STACS2027.Embed.ForestData.upL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.upL

/-- info: 'STACS2027.Embed.ForestData.downL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.downL

/-- info: 'STACS2027.Embed.ForestData.Ftour' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.Ftour

/-- info: 'STACS2027.Embed.ForestData.expandT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.expandT

/-- info: 'STACS2027.Embed.ForestData.Ftour_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.Ftour_eq

/-- info: 'STACS2027.Embed.ForestData.upL_root' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.upL_root

/-- info: 'STACS2027.Embed.ForestData.upL_nonroot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.upL_nonroot

/-- info: 'STACS2027.Embed.ForestData.downL_root' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.downL_root

/-- info: 'STACS2027.Embed.ForestData.downL_nonroot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.downL_nonroot

/-- info: 'STACS2027.Embed.ForestData.expandT_item' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.expandT_item

/-- info: 'STACS2027.Embed.ForestData.mem_Ftour_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mem_Ftour_vertex

/-- info: 'STACS2027.Embed.ForestData.Ftour_top' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.Ftour_top

/-- info: 'STACS2027.Embed.ForestData.expandT_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.expandT_root

/-- info: 'STACS2027.Embed.ForestData.mem_Ftour_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mem_Ftour_top

/-- info: 'STACS2027.Embed.ForestData.nodup_flatMap'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.nodup_flatMap'

/-- info: 'STACS2027.Embed.ForestData.ord_vertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.ord_vertex

/-- info: 'STACS2027.Embed.ForestData.Ftour_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.Ftour_nodup

/-- info: 'STACS2027.Embed.ForestData.sigN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.sigN

/-- info: 'STACS2027.Embed.ForestData.part_facts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.part_facts

/-- info: 'STACS2027.Embed.ForestData.euler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.euler

/-- info: 'STACS2027.Embed.ForestData.part_facts_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.part_facts_at

/-- info: 'STACS2027.Embed.ForestData.top_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.top_cyc

/-- info: 'STACS2027.Embed.ForestData.top_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.top_nodup

/-- info: 'STACS2027.Embed.ForestData.dart_part_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.dart_part_back

/-- info: 'STACS2027.Embed.ForestData.filter_flatMap'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.filter_flatMap'

/-- info: 'STACS2027.Embed.ForestData.Ftour_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.Ftour_filter

/-- info: 'STACS2027.Embed.firstLookup' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup

/-- info: 'STACS2027.Embed.firstLookup_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup_loopFree

/-- info: 'STACS2027.Embed.firstLookup_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup_size

/-- info: 'STACS2027.Embed.firstLookup_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup_mem

/-- info: 'STACS2027.Embed.firstLookup_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup_value

/-- info: 'STACS2027.Embed.firstLookup_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup_out

/-- info: 'STACS2027.Embed.firstLookup_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup_reg

/-- info: 'STACS2027.Embed.firstLookup_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup_addrOK

/-- info: 'STACS2027.Embed.firstLookup_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup_exec

/-- info: 'STACS2027.Embed.firstLookup_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup_dictionary

/-- info: 'STACS2027.Embed.firstLookup_dictionary_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstLookup_dictionary_bounded

/-- info: 'STACS2027.Embed.firstCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.firstCode

/-- info: 'STACS2027.Embed.firstCode_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstCode_snoc

/-- info: 'STACS2027.Embed.firstCode_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstCode_positive

/-- info: 'STACS2027.Embed.firstCode_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstCode_prefix

/-- info: 'STACS2027.Embed.firstCode_firstOcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstCode_firstOcc

/-- info: 'STACS2027.Embed.Meets' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Meets

/-- info: 'STACS2027.Embed.hitTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.hitTime

/-- info: 'STACS2027.Embed.hitTime_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.hitTime_spec

/-- info: 'STACS2027.Embed.firstReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstReturn

/-- info: 'STACS2027.Embed.meets_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.meets_of_perm

/-- info: 'STACS2027.Embed.firstReturn_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstReturn_mem

/-- info: 'STACS2027.Embed.firstReturn_of_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstReturn_of_not

/-- info: 'STACS2027.Embed.firstReturn_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstReturn_of_mem

/-- info: 'STACS2027.Embed.reaches_firstReturn_of_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.reaches_firstReturn_of_iterate

/-- info: 'STACS2027.Embed.reaches_firstReturn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.reaches_firstReturn_iff

/-- info: 'STACS2027.Embed.firstReturn_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstReturn_injective

/-- info: 'STACS2027.Embed.MeetsB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.MeetsB

/-- info: 'STACS2027.Embed.meetsB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.meetsB_iff

/-- info: 'STACS2027.Embed.meetsB_of_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.meetsB_of_reaches

/-- info: 'STACS2027.Embed.avoidCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.avoidCount

/-- info: 'STACS2027.Embed.exists_smin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.exists_smin

/-- info: 'STACS2027.Embed.smin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.smin

/-- info: 'STACS2027.Embed.smin_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.smin_spec

/-- info: 'STACS2027.Embed.smin_eq_of_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.smin_eq_of_reaches

/-- info: 'STACS2027.Embed.cycleCount_firstReturn_avoid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cycleCount_firstReturn_avoid

/-- info: 'STACS2027.Embed.AllMeet' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.AllMeet

/-- info: 'STACS2027.Embed.avoidCount_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.avoidCount_eq_zero

/-- info: 'STACS2027.Embed.cycleCount_firstReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cycleCount_firstReturn

/-- info: 'STACS2027.Embed.pair' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.pair

/-- info: 'STACS2027.Embed.pair_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.pair_pair

/-- info: 'STACS2027.Embed.pair_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.pair_ne

/-- info: 'STACS2027.Embed.pair_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.pair_lt

/-- info: 'STACS2027.Embed.pair_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.pair_inj

/-- info: 'STACS2027.Embed.ForestData' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData

/-- info: 'STACS2027.Embed.ForestData.IsVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.IsVertex

/-- info: 'STACS2027.Embed.ForestData.dartsAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.dartsAt

/-- info: 'STACS2027.Embed.ForestData.IsRoot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.IsRoot

/-- info: 'STACS2027.Embed.ForestData.up' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.up

/-- info: 'STACS2027.Embed.ForestData.Desc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.Desc

/-- info: 'STACS2027.Embed.ForestData.IsUp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.IsUp

/-- info: 'STACS2027.Embed.ForestData.IsDown' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.IsDown

/-- info: 'STACS2027.Embed.ForestData.IsTree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.IsTree

/-- info: 'STACS2027.Embed.ForestData.Valid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.Valid

/-- info: 'STACS2027.Embed.ForestData.mem_dartsAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mem_dartsAt

/-- info: 'STACS2027.Embed.ForestData.dartsAt_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.dartsAt_nodup

/-- info: 'STACS2027.Embed.ForestData.desc_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_refl

/-- info: 'STACS2027.Embed.ForestData.desc_trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_trans

/-- info: 'STACS2027.Embed.ForestData.desc_up' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_up

/-- info: 'STACS2027.Embed.ForestData.isVertex_rep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.isVertex_rep

/-- info: 'STACS2027.Embed.ForestData.up_vertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.up_vertex

/-- info: 'STACS2027.Embed.ForestData.iterate_up_vertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.iterate_up_vertex

/-- info: 'STACS2027.Embed.ForestData.up_root' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.up_root

/-- info: 'STACS2027.Embed.ForestData.depth_iterate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.depth_iterate

/-- info: 'STACS2027.Embed.ForestData.iterate_up_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.iterate_up_depth

/-- info: 'STACS2027.Embed.ForestData.desc_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_depth

/-- info: 'STACS2027.Embed.ForestData.desc_eq_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_eq_iterate

/-- info: 'STACS2027.Embed.ForestData.desc_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_unique

/-- info: 'STACS2027.Embed.ForestData.desc_of_desc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_of_desc

/-- info: 'STACS2027.Embed.ForestData.desc_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_antisymm

/-- info: 'STACS2027.Embed.ForestData.desc_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_child

/-- info: 'STACS2027.Embed.ForestData.up_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.up_ne

/-- info: 'STACS2027.Embed.ForestData.depth_up_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.depth_up_lt

/-- info: 'STACS2027.Embed.ForestData.INF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.INF

/-- info: 'STACS2027.Embed.ForestData.gid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.gid

/-- info: 'STACS2027.Embed.ForestData.isIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.isIn

/-- info: 'STACS2027.Embed.ForestData.sol' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.sol

/-- info: 'STACS2027.Embed.ForestData.top_of_isTop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.top_of_isTop

/-- info: 'STACS2027.Embed.ForestData.parts_other' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.parts_other

/-- info: 'STACS2027.Embed.ForestData.dart_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.dart_part

/-- info: 'STACS2027.Embed.ForestData.node_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.node_part

/-- info: 'STACS2027.Embed.ForestData.lt_of_mem_D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.lt_of_mem_D

/-- info: 'STACS2027.Embed.ForestData.depth_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.depth_child

/-- info: 'STACS2027.Embed.ForestData.isIn_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.isIn_target

/-- info: 'STACS2027.Embed.ForestData.isIn_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.isIn_fork

/-- info: 'STACS2027.Embed.ForestData.key_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.key_lt

/-- info: 'STACS2027.Embed.ForestData.good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.good

/-- info: 'STACS2027.Embed.ForestData.item_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.item_inj

/-- info: 'STACS2027.Embed.ForestData.tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.tree

/-- info: 'STACS2027.Embed.ForestData.planar_of_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.planar_of_consistent

/-- info: 'STACS2027.Embed.Sol.popStep_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popStep_classes

/-- info: 'STACS2027.Embed.Sol.consStep_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consStep_class

/-- info: 'STACS2027.Embed.Sol.consStep_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consStep_finish

/-- info: 'STACS2027.Embed.Sol.forkTicks' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkTicks

/-- info: 'STACS2027.Embed.Sol.forkFinish' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkFinish

/-- info: 'STACS2027.Embed.Sol.forkFinish_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkFinish_refines

/-- info: 'STACS2027.Embed.Sol.forkTicks_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkTicks_le

/-- info: 'STACS2027.Embed.Sol.completeFork' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeFork

/-- info: 'STACS2027.Embed.Sol.forkNodeTicks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkNodeTicks

/-- info: 'STACS2027.Embed.Sol.completeFork_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeFork_refines

/-- info: 'STACS2027.Embed.Sol.forkNodeTicks_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkNodeTicks_le

/-- info: 'STACS2027.Embed.Sol.prepare_fork_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.prepare_fork_parts

/-- info: 'STACS2027.Embed.Sol.Good.tgtOf_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.tgtOf_fork

/-- info: 'STACS2027.Embed.before_take_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_take_mem

/-- info: 'STACS2027.Embed.Sol.Live' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Live

/-- info: 'STACS2027.Embed.Sol.PostOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.PostOrder

/-- info: 'STACS2027.Embed.Sol.PostOrder.below_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.PostOrder.below_done

/-- info: 'STACS2027.Embed.Sol.PostOrder.live_incomparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.PostOrder.live_incomparable

/-- info: 'STACS2027.Embed.Sol.Tree.own_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.own_disjoint

/-- info: 'STACS2027.Embed.Sol.Tree.live_groups_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.live_groups_disjoint

/-- info: 'STACS2027.Embed.Sol.Tree.live_ends_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.live_ends_disjoint

/-- info: 'STACS2027.Embed.Sol.live_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.live_append

/-- info: 'STACS2027.Embed.Sol.Ready' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Ready

/-- info: 'STACS2027.Embed.Sol.PostOrder.ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.PostOrder.ready

/-- info: 'STACS2027.Embed.Sol.Frontier' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Frontier

/-- info: 'STACS2027.Embed.Sol.frontier_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.frontier_nil

/-- info: 'STACS2027.Embed.ForestData.PostOrder.solver' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.PostOrder.solver

/-- info: 'STACS2027.Embed.varAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.varAt

/-- info: 'STACS2027.Embed.firstOcc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.firstOcc

/-- info: 'STACS2027.Embed.incRep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.incRep

/-- info: 'STACS2027.Embed.incDG' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.incDG

/-- info: 'STACS2027.Embed.flatten_length_nM' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.flatten_length_nM

/-- info: 'STACS2027.Embed.incidence_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incidence_length

/-- info: 'STACS2027.Embed.incidence_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incidence_getElem?

/-- info: 'STACS2027.Embed.halfEdgeEnd_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.halfEdgeEnd_even

/-- info: 'STACS2027.Embed.halfEdgeEnd_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.halfEdgeEnd_odd

/-- info: 'STACS2027.Embed.varAt_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.varAt_eq

/-- info: 'STACS2027.Embed.firstOcc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstOcc_spec

/-- info: 'STACS2027.Embed.firstOcc_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstOcc_inj

/-- info: 'STACS2027.Embed.NonemptyClauses' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.NonemptyClauses

/-- info: 'STACS2027.Embed.kl_pos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.kl_pos

/-- info: 'STACS2027.Embed.off_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.off_strict

/-- info: 'STACS2027.Embed.off_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.off_inj

/-- info: 'STACS2027.Embed.oj_off' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.oj_off

/-- info: 'STACS2027.Embed.occ_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.occ_lt

/-- info: 'STACS2027.Embed.incRep_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incRep_even

/-- info: 'STACS2027.Embed.incRep_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incRep_odd

/-- info: 'STACS2027.Embed.dart_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.dart_cases

/-- info: 'STACS2027.Embed.incRep_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incRep_eq_iff

/-- info: 'STACS2027.Embed.length_le_of_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.length_le_of_sub

/-- info: 'STACS2027.Embed.countP_range_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.countP_range_getD

/-- info: 'STACS2027.Embed.countP_var' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.countP_var

/-- info: 'STACS2027.Embed.filter_length_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.filter_length_map

/-- info: 'STACS2027.Embed.incDeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incDeg

/-- info: 'STACS2027.Embed.incOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incOk

/-- info: 'STACS2027.Embed.varAt_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.varAt_prefix

/-- info: 'STACS2027.Embed.incRep_odd_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incRep_odd_prefix

/-- info: 'STACS2027.Embed.incRep_even_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.incRep_even_prefix

/-- info: 'STACS2027.Embed.IncidenceRAM.adjacencyPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.adjacencyPre

/-- info: 'STACS2027.Embed.IncidenceRAM.incidenceCache' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.incidenceCache

/-- info: 'STACS2027.Embed.IncidenceRAM.adjacencyPre_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.adjacencyPre_loopFree

/-- info: 'STACS2027.Embed.IncidenceRAM.adjacencyPre_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.adjacencyPre_size

/-- info: 'STACS2027.Embed.IncidenceRAM.adjacencyPre_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.adjacencyPre_mem

/-- info: 'STACS2027.Embed.IncidenceRAM.adjacencyPre_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.adjacencyPre_out

/-- info: 'STACS2027.Embed.IncidenceRAM.adjacencyPre_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.adjacencyPre_reg

/-- info: 'STACS2027.Embed.IncidenceRAM.zero_input_memory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.zero_input_memory

/-- info: 'STACS2027.Embed.IncidenceRAM.adjacencyPre_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.adjacencyPre_start

/-- info: 'STACS2027.Embed.IncidenceRAM.incidenceCache_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.incidenceCache_spec

/-- info: 'STACS2027.Embed.IncidenceRAM.ClauseState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.ClauseState

/-- info: 'STACS2027.Embed.IncidenceRAM.CacheState.clausePre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.CacheState.clausePre

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheClause_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheClause_step

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheFormula_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheFormula_spec

/-- info: 'STACS2027.Embed.IncidenceRAM.CacheAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.CacheAt

/-- info: 'STACS2027.Embed.IncidenceRAM.CacheAt.head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.CacheAt.head

/-- info: 'STACS2027.Embed.IncidenceRAM.CacheAt.of_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.CacheAt.of_mem

/-- info: 'STACS2027.Embed.IncidenceRAM.CacheAt.drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.CacheAt.drop

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheLiteral' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheLiteral

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheClausePre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheClausePre

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheClause

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheFormula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheFormula

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheLiteral_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheLiteral_loopFree

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheLiteral_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheLiteral_size

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheLiteral_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheLiteral_out

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheLiteral_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheLiteral_reg

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheLiteral_advance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheLiteral_advance

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheLiteral_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheLiteral_mem

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheLiteral_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheLiteral_addrOK

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheClausePre_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheClausePre_loopFree

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheClausePre_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheClausePre_size

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheClausePre_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheClausePre_mem

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheClausePre_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheClausePre_out

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheClausePre_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheClausePre_reg

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheClausePre_read' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheClausePre_read

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheClausePre_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheClausePre_addrOK

/-- info: 'STACS2027.Embed.IncidenceRAM.cacheLayout' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cacheLayout

/-- info: 'STACS2027.Embed.IncidenceRAM.cachePre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cachePre

/-- info: 'STACS2027.Embed.IncidenceRAM.cachePre_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cachePre_loopFree

/-- info: 'STACS2027.Embed.IncidenceRAM.cachePre_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cachePre_size

/-- info: 'STACS2027.Embed.IncidenceRAM.cachePre_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cachePre_mem

/-- info: 'STACS2027.Embed.IncidenceRAM.cachePre_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cachePre_out

/-- info: 'STACS2027.Embed.IncidenceRAM.cachePre_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cachePre_addrOK

/-- info: 'STACS2027.Embed.IncidenceRAM.cachePre_bases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cachePre_bases

/-- info: 'STACS2027.Embed.IncidenceRAM.cachePre_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cachePre_start

/-- info: 'STACS2027.Embed.IncidenceRAM.CacheState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.CacheState

/-- info: 'STACS2027.Embed.IncidenceRAM.CacheState.literal_bases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.CacheState.literal_bases

/-- info: 'STACS2027.Embed.IncidenceRAM.CacheState.literal_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.CacheState.literal_mem

/-- info: 'STACS2027.Embed.IncidenceRAM.CacheState.literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.CacheState.literal

/-- info: 'STACS2027.Embed.IncidenceRAM.CacheState.literal_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.CacheState.literal_addrOK

/-- info: 'STACS2027.Embed.IncidenceRAM.cache_listPass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.cache_listPass

/-- info: 'STACS2027.Embed.IncidenceRAM.prepareDFS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.prepareDFS

/-- info: 'STACS2027.Embed.IncidenceRAM.prepareDFS_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.prepareDFS_spec

/-- info: 'STACS2027.Embed.IncidenceRAM.prepareDFS_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.prepareDFS_linear

/-- info: 'STACS2027.Embed.Sol.up_lo_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.up_lo_perm

/-- info: 'STACS2027.Embed.Sol.pop_ends_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.pop_ends_perm

/-- info: 'STACS2027.Embed.Sol.popStep_cell_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popStep_cell_frame

/-- info: 'STACS2027.Embed.Sol.popStep_stack_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popStep_stack_frame

/-- info: 'STACS2027.Embed.Sol.popGroups' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popGroups

/-- info: 'STACS2027.Embed.Sol.popGroups_iterate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popGroups_iterate

/-- info: 'STACS2027.Embed.Sol.popStep_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popStep_stop

/-- info: 'STACS2027.Embed.Sol.popGroups_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popGroups_refines

/-- info: 'STACS2027.Embed.Sol.popGroups_arrays' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popGroups_arrays

/-- info: 'STACS2027.Embed.Sol.popGroups_cell_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popGroups_cell_frame

/-- info: 'STACS2027.Embed.Sol.popGroups_stack_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popGroups_stack_frame

/-- info: 'STACS2027.Embed.Sol.consStep_cell_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consStep_cell_frame

/-- info: 'STACS2027.Embed.Sol.consStep_stack_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consStep_stack_frame

/-- info: 'STACS2027.Embed.Sol.consGroups' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups

/-- info: 'STACS2027.Embed.Sol.consStep_index' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consStep_index

/-- info: 'STACS2027.Embed.Sol.consGroups_index' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups_index

/-- info: 'STACS2027.Embed.Sol.consGroups_iterate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups_iterate

/-- info: 'STACS2027.Embed.Sol.consGroups_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups_refines

/-- info: 'STACS2027.Embed.Sol.consGroups_arrays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups_arrays

/-- info: 'STACS2027.Embed.Sol.consGroups_cell_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups_cell_frame

/-- info: 'STACS2027.Embed.Sol.consGroups_linked_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups_linked_frame

/-- info: 'STACS2027.Embed.Sol.consGroups_stack_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups_stack_frame

/-- info: 'STACS2027.Embed.Linked' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked

/-- info: 'STACS2027.Embed.Linked.nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.nil

/-- info: 'STACS2027.Embed.Linked.singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.singleton

/-- info: 'STACS2027.Embed.Linked.head_zero_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.head_zero_iff

/-- info: 'STACS2027.Embed.Linked.head_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.head_some_iff

/-- info: 'STACS2027.Embed.Linked.pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.pop

/-- info: 'STACS2027.Embed.Linked.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.frame

/-- info: 'STACS2027.Embed.Linked.update_tail_links' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.update_tail_links

/-- info: 'STACS2027.Embed.Linked.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.append

/-- info: 'STACS2027.Embed.Linked.append_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.append_frame

/-- info: 'STACS2027.Embed.Linked.append_cell_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.append_cell_frame

/-- info: 'STACS2027.Embed.Linked.double_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Linked.double_append

/-- info: 'STACS2027.Embed.Sol.khM_linked' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.khM_linked

/-- info: 'STACS2027.Embed.Sol.GroupRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.GroupRep

/-- info: 'STACS2027.Embed.Sol.gtopM_group' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.gtopM_group

/-- info: 'STACS2027.Embed.appendClassProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.appendClassProgram

/-- info: 'STACS2027.Embed.appendClassProgram_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.appendClassProgram_loopFree

/-- info: 'STACS2027.Embed.appendClassProgram_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.appendClassProgram_size

/-- info: 'STACS2027.Embed.AppendAddressOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.AppendAddressOK

/-- info: 'STACS2027.Embed.appendClassProgram_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.appendClassProgram_addrOK

/-- info: 'STACS2027.Embed.appendClassProgram_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.appendClassProgram_exec

/-- info: 'STACS2027.Embed.appendClassProgram_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.appendClassProgram_spec

/-- info: 'STACS2027.Embed.appendClassProgram_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.appendClassProgram_linked

/-- info: 'STACS2027.Embed.Sol.flatMap_up_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.flatMap_up_sub

/-- info: 'STACS2027.Embed.Sol.flatMap_lo_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.flatMap_lo_sub

/-- info: 'STACS2027.Embed.Sol.els_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.els_sub

/-- info: 'STACS2027.Embed.Sol.mergeState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeState

/-- info: 'STACS2027.Embed.Sol.mergeState_index' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeState_index

/-- info: 'STACS2027.Embed.Sol.mergeState_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeState_refines

/-- info: 'STACS2027.Embed.Sol.popGroups_protected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popGroups_protected

/-- info: 'STACS2027.Embed.Sol.consGroups_instruction_frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups_instruction_frame

/-- info: 'STACS2027.Embed.Sol.mergeState_instruction_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeState_instruction_frame

/-- info: 'STACS2027.Embed.Sol.forkFinish_instruction' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkFinish_instruction

/-- info: 'STACS2027.Embed.Sol.consGroups_protected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups_protected

/-- info: 'STACS2027.Embed.Sol.consStep_finish_foreign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consStep_finish_foreign

/-- info: 'STACS2027.Embed.Sol.mergeState_foreign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeState_foreign

/-- info: 'STACS2027.Embed.Sol.forkFinish_foreign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkFinish_foreign

/-- info: 'STACS2027.Embed.MeetsFrom' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.MeetsFrom

/-- info: 'STACS2027.Embed.hitTime0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.hitTime0

/-- info: 'STACS2027.Embed.hitTime0_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.hitTime0_spec

/-- info: 'STACS2027.Embed.nextIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.nextIn

/-- info: 'STACS2027.Embed.nextIn_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.nextIn_mem

/-- info: 'STACS2027.Embed.hitTime0_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.hitTime0_of_mem

/-- info: 'STACS2027.Embed.nextIn_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.nextIn_of_mem

/-- info: 'STACS2027.Embed.meetsFrom_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.meetsFrom_step

/-- info: 'STACS2027.Embed.iterate_succ_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.iterate_succ_apply

/-- info: 'STACS2027.Embed.hitTime0_of_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.hitTime0_of_not

/-- info: 'STACS2027.Embed.nextIn_of_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.nextIn_of_not

/-- info: 'STACS2027.Embed.meetsFrom_of_perm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.meetsFrom_of_perm

/-- info: 'STACS2027.Embed.meetsFrom_of_meets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.meetsFrom_of_meets

/-- info: 'STACS2027.Embed.hitTime_eq_hitTime0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.hitTime_eq_hitTime0

/-- info: 'STACS2027.Embed.firstReturn_eq_nextIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.firstReturn_eq_nextIn

/-- info: 'STACS2027.Embed.reaches_nextIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.reaches_nextIn

/-- info: 'STACS2027.Embed.nextIn_nextIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.nextIn_nextIn

/-- info: 'STACS2027.Embed.Sol.Stored' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Stored

/-- info: 'STACS2027.Embed.Sol.StackRep.store_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.StackRep.store_frame

/-- info: 'STACS2027.Embed.Sol.StackRep.inf_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.StackRep.inf_frame

/-- info: 'STACS2027.Embed.Sol.stored_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.stored_store

/-- info: 'STACS2027.Embed.Sol.Inv.deepest_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Inv.deepest_head

/-- info: 'STACS2027.Embed.Sol.Good.target_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.target_head

/-- info: 'STACS2027.Embed.Sol.itRes_foreign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.itRes_foreign

/-- info: 'STACS2027.Embed.Sol.itRes_stored_foreign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.itRes_stored_foreign

/-- info: 'STACS2027.Embed.Sol.itRes_rep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.itRes_rep

/-- info: 'STACS2027.Embed.Sol.nodeStep_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.nodeStep_leaf

/-- info: 'STACS2027.Embed.Sol.nodeStep_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.nodeStep_single

/-- info: 'STACS2027.Embed.Sol.closeM_foreign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.closeM_foreign

/-- info: 'STACS2027.Embed.Sol.twoStep_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.twoStep_target

/-- info: 'STACS2027.Embed.Sol.completeFork_instruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeFork_instruction

/-- info: 'STACS2027.Embed.Sol.completeNode_instruction_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeNode_instruction_other

/-- info: 'STACS2027.Embed.Sol.completeNode_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeNode_bit

/-- info: 'STACS2027.Embed.Sol.completeNode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeNode

/-- info: 'STACS2027.Embed.Sol.nodeTicks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.nodeTicks

/-- info: 'STACS2027.Embed.Sol.Good.target_tgtOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.target_tgtOf

/-- info: 'STACS2027.Embed.Sol.completeNode_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeNode_refines

/-- info: 'STACS2027.Embed.Sol.itRes_instruction_frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.itRes_instruction_frame

/-- info: 'STACS2027.Embed.Sol.completeFork_foreign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeFork_foreign

/-- info: 'STACS2027.Embed.Sol.closeM_protected' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.closeM_protected

/-- info: 'STACS2027.Embed.Sol.nodeStep_single_foreign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.nodeStep_single_foreign

/-- info: 'STACS2027.Embed.Sol.completeNode_foreign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeNode_foreign

/-- info: 'STACS2027.Embed.foldl_upd_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.foldl_upd_other

/-- info: 'STACS2027.Embed.foldl_upd_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.foldl_upd_spec

/-- info: 'STACS2027.Embed.ForestData.oval' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.oval

/-- info: 'STACS2027.Embed.ForestData.okey' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.okey

/-- info: 'STACS2027.Embed.ForestData.oitems' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.oitems

/-- info: 'STACS2027.Embed.ForestData.orient' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.orient

/-- info: 'STACS2027.Embed.ForestData.Records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.Records

/-- info: 'STACS2027.Embed.ForestData.PostOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.PostOrder

/-- info: 'STACS2027.Embed.ForestData.oitems_getElem_inl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.oitems_getElem_inl

/-- info: 'STACS2027.Embed.ForestData.idx_lt_of_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.idx_lt_of_before

/-- info: 'STACS2027.Embed.ForestData.consumed_gid_or_dart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.consumed_gid_or_dart

/-- info: 'STACS2027.Embed.ForestData.orient_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.orient_consistent

/-- info: 'STACS2027.Embed.RAMSolver.orientationProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationProgram

/-- info: 'STACS2027.Embed.RAMSolver.orientationProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationProgram_spec

/-- info: 'STACS2027.Embed.RAMSolver.orientationBody_mem_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationBody_mem_frame

/-- info: 'STACS2027.Embed.RAMSolver.orientationLoop_framed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationLoop_framed_spec

/-- info: 'STACS2027.Embed.RAMSolver.orientationLoop_mem_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationLoop_mem_frame

/-- info: 'STACS2027.Embed.RAMSolver.keyPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyPre

/-- info: 'STACS2027.Embed.RAMSolver.keyMid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyMid

/-- info: 'STACS2027.Embed.RAMSolver.keyFinish' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyFinish

/-- info: 'STACS2027.Embed.RAMSolver.keyProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyProgram

/-- info: 'STACS2027.Embed.RAMSolver.orientationKeys_explicit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationKeys_explicit

/-- info: 'STACS2027.Embed.RAMSolver.keyPre_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyPre_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.keyMid_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyMid_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.keyFinish_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyFinish_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.keyPre_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyPre_size

/-- info: 'STACS2027.Embed.RAMSolver.keyMid_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyMid_size

/-- info: 'STACS2027.Embed.RAMSolver.keyFinish_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyFinish_size

/-- info: 'STACS2027.Embed.RAMSolver.keyPre_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyPre_mem

/-- info: 'STACS2027.Embed.RAMSolver.keyMid_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyMid_mem

/-- info: 'STACS2027.Embed.RAMSolver.keyFinish_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyFinish_mem

/-- info: 'STACS2027.Embed.RAMSolver.keyPre_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyPre_out

/-- info: 'STACS2027.Embed.RAMSolver.keyMid_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyMid_out

/-- info: 'STACS2027.Embed.RAMSolver.keyFinish_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyFinish_out

/-- info: 'STACS2027.Embed.RAMSolver.keyProgram_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyProgram_regs

/-- info: 'STACS2027.Embed.RAMSolver.getD_map_add' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.getD_map_add

/-- info: 'STACS2027.Embed.RAMSolver.keyProgram_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyProgram_spec

/-- info: 'STACS2027.Embed.RAMSolver.reverseKeyStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.reverseKeyStep

/-- info: 'STACS2027.Embed.RAMSolver.reverseKeyLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.reverseKeyLoop

/-- info: 'STACS2027.Embed.RAMSolver.reverseKeyStep_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.reverseKeyStep_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.reverseKeyStep_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.reverseKeyStep_size

/-- info: 'STACS2027.Embed.RAMSolver.reverseKeyStep_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.reverseKeyStep_reg

/-- info: 'STACS2027.Embed.RAMSolver.reverseKeyStep_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.reverseKeyStep_mem

/-- info: 'STACS2027.Embed.RAMSolver.reverseKeyStep_advance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.reverseKeyStep_advance

/-- info: 'STACS2027.Embed.RAMSolver.reverseKeyStep_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.reverseKeyStep_out

/-- info: 'STACS2027.Embed.RAMSolver.reverseKeyStep_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.reverseKeyStep_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.getD_reverse_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.getD_reverse_nat

/-- info: 'STACS2027.Embed.RAMSolver.KeyCopyState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.KeyCopyState

/-- info: 'STACS2027.Embed.RAMSolver.KeyCopyState.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.KeyCopyState.step

/-- info: 'STACS2027.Embed.RAMSolver.reverseKeyLoop_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.reverseKeyLoop_spec

/-- info: 'STACS2027.Embed.RAMSolver.forwardKeyStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forwardKeyStep

/-- info: 'STACS2027.Embed.RAMSolver.forwardKeyLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forwardKeyLoop

/-- info: 'STACS2027.Embed.RAMSolver.forwardKeyStep_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forwardKeyStep_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.forwardKeyStep_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forwardKeyStep_size

/-- info: 'STACS2027.Embed.RAMSolver.forwardKeyStep_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forwardKeyStep_reg

/-- info: 'STACS2027.Embed.RAMSolver.forwardKeyStep_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forwardKeyStep_mem

/-- info: 'STACS2027.Embed.RAMSolver.forwardKeyStep_advance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forwardKeyStep_advance

/-- info: 'STACS2027.Embed.RAMSolver.forwardKeyStep_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forwardKeyStep_out

/-- info: 'STACS2027.Embed.RAMSolver.ForwardKeyState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ForwardKeyState

/-- info: 'STACS2027.Embed.RAMSolver.ForwardKeyState.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ForwardKeyState.step

/-- info: 'STACS2027.Embed.RAMSolver.forwardKeyLoop_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forwardKeyLoop_spec

/-- info: 'STACS2027.Embed.RAMSolver.boolWord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.boolWord

/-- info: 'STACS2027.Embed.RAMSolver.ORam.base' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ORam.base

/-- info: 'STACS2027.Embed.RAMSolver.ORam.group' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ORam.group

/-- info: 'STACS2027.Embed.RAMSolver.ORam.parent' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ORam.parent

/-- info: 'STACS2027.Embed.RAMSolver.ORam.flip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ORam.flip

/-- info: 'STACS2027.Embed.RAMSolver.ORam.address' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ORam.address

/-- info: 'STACS2027.Embed.RAMSolver.ORam.value' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ORam.value

/-- info: 'STACS2027.Embed.RAMSolver.ORam.diff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ORam.diff

/-- info: 'STACS2027.Embed.RAMSolver.ORam.otherDiff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ORam.otherDiff

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup_size

/-- info: 'STACS2027.Embed.RAMSolver.groupOrientation' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.groupOrientation

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup_value

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup_frame

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup_reg

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup_store' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup_store

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup_exec

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup_array

/-- info: 'STACS2027.Embed.RAMSolver.orientGroup_boundedArray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientGroup_boundedArray

/-- info: 'STACS2027.Embed.RAMSolver.records_parentBound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.records_parentBound

/-- info: 'STACS2027.Embed.RAMSolver.orientationKeys' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationKeys

/-- info: 'STACS2027.Embed.RAMSolver.orientationKeys_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationKeys_bound

/-- info: 'STACS2027.Embed.RAMSolver.orientationKeys_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationKeys_length

/-- info: 'STACS2027.Embed.RAMSolver.orientationKeys_fold' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationKeys_fold

/-- info: 'STACS2027.Embed.RAMSolver.keyProgram_orientationState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.keyProgram_orientationState

/-- info: 'STACS2027.Embed.RAMSolver.OrientationLayout' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.OrientationLayout

/-- info: 'STACS2027.Embed.RAMSolver.OrientationState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.OrientationState

/-- info: 'STACS2027.Embed.RAMSolver.sequenceRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.sequenceRead

/-- info: 'STACS2027.Embed.RAMSolver.sequenceAdvance' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.sequenceAdvance

/-- info: 'STACS2027.Embed.RAMSolver.orientationBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationBody

/-- info: 'STACS2027.Embed.RAMSolver.orientationLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationLoop

/-- info: 'STACS2027.Embed.RAMSolver.sequenceRead_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.sequenceRead_reg

/-- info: 'STACS2027.Embed.RAMSolver.sequenceRead_group' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.sequenceRead_group

/-- info: 'STACS2027.Embed.RAMSolver.sequenceRead_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.sequenceRead_mem

/-- info: 'STACS2027.Embed.RAMSolver.sequenceRead_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.sequenceRead_out

/-- info: 'STACS2027.Embed.RAMSolver.sequenceAdvance_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.sequenceAdvance_reg

/-- info: 'STACS2027.Embed.RAMSolver.sequenceAdvance_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.sequenceAdvance_mem

/-- info: 'STACS2027.Embed.RAMSolver.sequenceAdvance_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.sequenceAdvance_out

/-- info: 'STACS2027.Embed.RAMSolver.OrientationState.read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.OrientationState.read

/-- info: 'STACS2027.Embed.RAMSolver.OrientationState.orient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.OrientationState.orient

/-- info: 'STACS2027.Embed.RAMSolver.OrientationState.advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.OrientationState.advance

/-- info: 'STACS2027.Embed.RAMSolver.orientationBody_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationBody_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.orientationBody_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationBody_size

/-- info: 'STACS2027.Embed.RAMSolver.orientationBody_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationBody_state

/-- info: 'STACS2027.Embed.RAMSolver.orientationBody_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationBody_out

/-- info: 'STACS2027.Embed.RAMSolver.orientationBody_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationBody_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.orientationLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationLoop_spec

/-- info: 'STACS2027.Embed.RAMSolver.orientationLoop_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationLoop_consistent

/-- info: 'STACS2027.Embed.PlanRAM.readForest_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.readForest_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.planStore_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.planStore_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.zStore_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.zStore_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem_plan_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem_plan_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedSlot_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedSlot_addrOK

/-- info: 'STACS2027.Embed.PlanCache.threeDarts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanCache.threeDarts

/-- info: 'STACS2027.Embed.PlanCache.threeDarts_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanCache.threeDarts_eq

/-- info: 'STACS2027.Embed.PlanCache.distinguished' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanCache.distinguished

/-- info: 'STACS2027.Embed.PlanCache.zOf_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanCache.zOf_three

/-- info: 'STACS2027.Embed.PlanCache.zOf_from_slots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanCache.zOf_from_slots

/-- info: 'STACS2027.Embed.PlanCache.parts_vertex_slots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanCache.parts_vertex_slots

/-- info: 'STACS2027.Embed.PlanCache.item_cached' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanCache.item_cached

/-- info: 'STACS2027.Embed.PlanRAM.DartFrame.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.DartFrame.refl

/-- info: 'STACS2027.Embed.PlanRAM.DartFrame.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.DartFrame.trans

/-- info: 'STACS2027.Embed.PlanRAM.DartFrame.above' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.DartFrame.above

/-- info: 'STACS2027.Embed.PlanRAM.DartFrame.cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.DartFrame.cell

/-- info: 'STACS2027.Embed.PlanRAM.dartBody_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartBody_context

/-- info: 'STACS2027.Embed.PlanRAM.dartBody_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartBody_mem

/-- info: 'STACS2027.Embed.PlanRAM.dartBody_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartBody_out

/-- info: 'STACS2027.Embed.PlanRAM.dartBody_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartBody_reg

/-- info: 'STACS2027.Embed.PlanRAM.dartBody_advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartBody_advance

/-- info: 'STACS2027.Embed.PlanRAM.dartTablesProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTablesProgram_spec

/-- info: 'STACS2027.Embed.PlanRAM.scanDart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.scanDart

/-- info: 'STACS2027.Embed.PlanRAM.otherDart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.otherDart

/-- info: 'STACS2027.Embed.PlanRAM.thisVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.thisVertex

/-- info: 'STACS2027.Embed.PlanRAM.otherVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.otherVertex

/-- info: 'STACS2027.Embed.PlanRAM.thisDepth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.thisDepth

/-- info: 'STACS2027.Embed.PlanRAM.otherDepth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.otherDepth

/-- info: 'STACS2027.Embed.PlanRAM.otherParent' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.otherParent

/-- info: 'STACS2027.Embed.PlanRAM.otherDistinguished' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.otherDistinguished

/-- info: 'STACS2027.Embed.PlanRAM.targetValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.targetValue

/-- info: 'STACS2027.Embed.PlanRAM.keyValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.keyValue

/-- info: 'STACS2027.Embed.PlanRAM.comparison' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.comparison

/-- info: 'STACS2027.Embed.PlanRAM.dartRemaining' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartRemaining

/-- info: 'STACS2027.Embed.PlanRAM.secondComparison' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.secondComparison

/-- info: 'STACS2027.Embed.PlanRAM.dartProbe' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartProbe

/-- info: 'STACS2027.Embed.PlanRAM.dartValues' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartValues

/-- info: 'STACS2027.Embed.PlanRAM.dartCommits' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartCommits

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep

/-- info: 'STACS2027.Embed.PlanRAM.dartTableBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableBody

/-- info: 'STACS2027.Embed.PlanRAM.dartTablesProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTablesProgram

/-- info: 'STACS2027.Embed.PlanRAM.Context.dartProbe_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.dartProbe_context

/-- info: 'STACS2027.Embed.PlanRAM.Context.dartValues_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.dartValues_context

/-- info: 'STACS2027.Embed.PlanRAM.dartProbe_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartProbe_raw

/-- info: 'STACS2027.Embed.PlanRAM.dartValues_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartValues_raw

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_context

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_reg

/-- info: 'STACS2027.Embed.PlanRAM.dartCommits_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartCommits_raw

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_memory

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_out

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_loopFree

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_size

/-- info: 'STACS2027.Embed.PlanRAM.dartProbe_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartProbe_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.dartCommits_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartCommits_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_exec

/-- info: 'STACS2027.Embed.PlanRAM.DartPrefix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.DartPrefix

/-- info: 'STACS2027.Embed.PlanRAM.DartFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.DartFrame

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_frame

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_cell

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_prefix

/-- info: 'STACS2027.Embed.PlanRAM.dartTableStep_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dartTableStep_zero

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedBounds_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedBounds_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedBounds_addr_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedBounds_addr_append

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedScan_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedScan_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedRead_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedRead_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedProgram_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedProgram_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedProgram_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedProgram_exec

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedRAM_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedRAM_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.tree_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.tree_cached

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedSlot_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedSlot_value

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedSlot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedSlot_frame

/-- info: 'STACS2027.Embed.PlanRAM.Context.distinguishedSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.distinguishedSlot

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedScan_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedScan_value

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedRead

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedProgram_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedProgram_run

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedRead_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedRead_frame

/-- info: 'STACS2027.Embed.PlanRAM.Context.distinguishedRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.distinguishedRead

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedRead_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedRead_value

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedProgram_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedProgram_mem

/-- info: 'STACS2027.Embed.PlanRAM.Context.distinguishedProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.distinguishedProgram

/-- info: 'STACS2027.Embed.PlanRAM.MutableZero.distinguishedProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.MutableZero.distinguishedProgram

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedValues_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedValues_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedProgram_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedProgram_inputs

/-- info: 'STACS2027.Embed.IncidenceRAM.prepareForestPlan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.prepareForestPlan

/-- info: 'STACS2027.Embed.IncidenceRAM.prepareForestPlan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.prepareForestPlan_spec

/-- info: 'STACS2027.Embed.ForestData.IsBack' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.IsBack

/-- info: 'STACS2027.Embed.ForestData.zOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.zOf

/-- info: 'STACS2027.Embed.ForestData.item' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.item

/-- info: 'STACS2027.Embed.ForestData.top' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.top

/-- info: 'STACS2027.Embed.ForestData.IsTop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.IsTop

/-- info: 'STACS2027.Embed.ForestData.parts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.parts

/-- info: 'STACS2027.Embed.ForestData.ht' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.ht

/-- info: 'STACS2027.Embed.ForestData.tgt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.tgt

/-- info: 'STACS2027.Embed.ForestData.key' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.key

/-- info: 'STACS2027.Embed.ForestData.isDown_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.isDown_iff

/-- info: 'STACS2027.Embed.ForestData.down_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.down_child

/-- info: 'STACS2027.Embed.ForestData.ht_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.ht_lt

/-- info: 'STACS2027.Embed.ForestData.plan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.plan

/-- info: 'STACS2027.Embed.ForestData.isUp_pair' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.isUp_pair

/-- info: 'STACS2027.Embed.ForestData.isDown_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.isDown_pair

/-- info: 'STACS2027.Embed.ForestData.isTree_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.isTree_pair

/-- info: 'STACS2027.Embed.ForestData.InEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.InEnd

/-- info: 'STACS2027.Embed.ForestData.OutEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.OutEnd

/-- info: 'STACS2027.Embed.ForestData.not_up_and_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.not_up_and_down

/-- info: 'STACS2027.Embed.ForestData.isBack_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.isBack_pair

/-- info: 'STACS2027.Embed.ForestData.back_in_or_out' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.back_in_or_out

/-- info: 'STACS2027.Embed.ForestData.not_in_and_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.not_in_and_out

/-- info: 'STACS2027.Embed.ForestData.outEnd_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.outEnd_pair

/-- info: 'STACS2027.Embed.ForestData.rep_ne_pair' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rep_ne_pair

/-- info: 'STACS2027.Embed.ForestData.child_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.child_down

/-- info: 'STACS2027.Embed.ForestData.four_darts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.four_darts

/-- info: 'STACS2027.Embed.ForestData.only_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.only_three

/-- info: 'STACS2027.Embed.ForestData.inEnd_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.inEnd_child

/-- info: 'STACS2027.Embed.ForestData.tree_not_back' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.tree_not_back

/-- info: 'STACS2027.Embed.ForestData.par_isUp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.par_isUp

/-- info: 'STACS2027.Embed.ForestData.inEnd_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.inEnd_unique

/-- info: 'STACS2027.Embed.ForestData.zOf_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.zOf_mem

/-- info: 'STACS2027.Embed.ForestData.zOf_ge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.zOf_ge

/-- info: 'STACS2027.Embed.ForestData.zOf_back' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.zOf_back

/-- info: 'STACS2027.Embed.ForestData.inEnd_unique_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.inEnd_unique_root

/-- info: 'STACS2027.Embed.ForestData.ZExcl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.ZExcl

/-- info: 'STACS2027.Embed.ForestData.parts_vertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.parts_vertex

/-- info: 'STACS2027.Embed.ForestData.id_item' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.id_item

/-- info: 'STACS2027.Embed.ForestData.not_up_root' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.not_up_root

/-- info: 'STACS2027.Embed.ForestData.back_of_not_tree_part' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.back_of_not_tree_part

/-- info: 'STACS2027.Embed.ForestData.mem_D_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mem_D_vertex

/-- info: 'STACS2027.Embed.ForestData.top_isTop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.top_isTop

/-- info: 'STACS2027.Embed.ForestData.parts_top' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.parts_top

/-- info: 'STACS2027.Embed.ForestData.back_root_inEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.back_root_inEnd

/-- info: 'STACS2027.Embed.ForestData.desc_root_of_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_root_of_rel

/-- info: 'STACS2027.Embed.ForestData.mem_D_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mem_D_top

/-- info: 'STACS2027.Embed.ForestData.part_in_D' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.part_in_D

/-- info: 'STACS2027.Embed.ForestData.open_partner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.open_partner

/-- info: 'STACS2027.Embed.ForestData.open_partner_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.open_partner_root

/-- info: 'STACS2027.Embed.ForestData.key_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.key_of_open

/-- info: 'STACS2027.Embed.ForestData.open_key_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.open_key_inj

/-- info: 'STACS2027.Embed.PlanRAM.solverLayout' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverLayout

/-- info: 'STACS2027.Embed.PlanRAM.zLimit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.zLimit

/-- info: 'STACS2027.Embed.PlanRAM.solverHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverHeader

/-- info: 'STACS2027.Embed.PlanRAM.solverHeader_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverHeader_loopFree

/-- info: 'STACS2027.Embed.PlanRAM.solverHeader_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverHeader_size

/-- info: 'STACS2027.Embed.PlanRAM.solverHeader_bases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverHeader_bases

/-- info: 'STACS2027.Embed.PlanRAM.solverHeader_metadata' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverHeader_metadata

/-- info: 'STACS2027.Embed.PlanRAM.solverHeader_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverHeader_frame

/-- info: 'STACS2027.Embed.PlanRAM.solverHeader_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverHeader_spec

/-- info: 'STACS2027.Embed.PlanRAM.solverSetup' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverSetup

/-- info: 'STACS2027.Embed.PlanRAM.solverSetup_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverSetup_loopFree

/-- info: 'STACS2027.Embed.PlanRAM.solverSetup_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverSetup_size

/-- info: 'STACS2027.Embed.PlanRAM.solverSetup_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverSetup_frame

/-- info: 'STACS2027.Embed.PlanRAM.solverSetup_forest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverSetup_forest

/-- info: 'STACS2027.Embed.PlanRAM.solverSetup_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverSetup_context

/-- info: 'STACS2027.Embed.PlanRAM.solverSetup_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverSetup_rep

/-- info: 'STACS2027.Embed.PlanRAM.solverSetup_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.solverSetup_spec

/-- info: 'STACS2027.Embed.IncidenceRAM.preparePlanContext' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.preparePlanContext

/-- info: 'STACS2027.Embed.IncidenceRAM.preparePlanContext_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.IncidenceRAM.preparePlanContext_spec

/-- info: 'STACS2027.Embed.PlanRAM.zBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.zBase

/-- info: 'STACS2027.Embed.PlanRAM.vertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertex

/-- info: 'STACS2027.Embed.PlanRAM.degree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.degree

/-- info: 'STACS2027.Embed.PlanRAM.vertexParent' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexParent

/-- info: 'STACS2027.Embed.PlanRAM.dart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.dart

/-- info: 'STACS2027.Embed.PlanRAM.opposite' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.opposite

/-- info: 'STACS2027.Embed.PlanRAM.child' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.child

/-- info: 'STACS2027.Embed.PlanRAM.childParent' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.childParent

/-- info: 'STACS2027.Embed.PlanRAM.itemType' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.itemType

/-- info: 'STACS2027.Embed.PlanRAM.itemValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.itemValue

/-- info: 'STACS2027.Embed.PlanRAM.distinguished' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguished

/-- info: 'STACS2027.Embed.PlanRAM.vertexBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexBound

/-- info: 'STACS2027.Embed.PlanRAM.partCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.partCount

/-- info: 'STACS2027.Embed.PlanRAM.topVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topVertex

/-- info: 'STACS2027.Embed.PlanRAM.remaining' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.remaining

/-- info: 'STACS2027.Embed.PlanRAM.slot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.slot

/-- info: 'STACS2027.Embed.PlanRAM.address' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.address

/-- info: 'STACS2027.Embed.PlanRAM.test' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.test

/-- info: 'STACS2027.Embed.PlanRAM.otherTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.otherTest

/-- info: 'STACS2027.Embed.PlanRAM.readForest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.readForest
