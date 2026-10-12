module

import BoundedCost

/-!
Exact-message axiom guards for every explicitly named BoundedCost declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.algorithm3_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.algorithm3_correct

/-- info: 'STACS2027.kCycleCore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.kCycleCore

/-- info: 'STACS2027.mem_kCycleCore_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_kCycleCore_iff

/-- info: 'STACS2027.mem_of_mem_kCycleCore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_of_mem_kCycleCore

/-- info: 'STACS2027.mem_vertices_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_vertices_iff

/-- info: 'STACS2027.mem_vertices_kCycleCore_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_vertices_kCycleCore_iff

/-- info: 'STACS2027.isCycle_kCycleCore_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isCycle_kCycleCore_iff

/-- info: 'STACS2027.range_filter_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.range_filter_extend

/-- info: 'STACS2027.range_filter_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.range_filter_eq

/-- info: 'STACS2027.vertices_filter_of_subgraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.vertices_filter_of_subgraph

/-- info: 'STACS2027.vertices_of_subgraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.vertices_of_subgraph

/-- info: 'STACS2027.neighbors_of_subgraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.neighbors_of_subgraph

/-- info: 'STACS2027.walksFrom_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.walksFrom_zero

/-- info: 'STACS2027.walksFrom_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.walksFrom_succ

/-- info: 'STACS2027.walksFrom_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.walksFrom_head

/-- info: 'STACS2027.flatMap_filter_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.flatMap_filter_eq

/-- info: 'STACS2027.flatMap_congr_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.flatMap_congr_mem

/-- info: 'STACS2027.walksFrom_of_subgraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.walksFrom_of_subgraph

/-- info: 'STACS2027.isCycle_pathEdges_core' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isCycle_pathEdges_core

/-- info: 'STACS2027.rawCycles_kCycleCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rawCycles_kCycleCore

/-- info: 'STACS2027.cycles_kCycleCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycles_kCycleCore

/-- info: 'STACS2027.hasAssignment_kCycleCore_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_kCycleCore_iff

/-- info: 'STACS2027.encodings_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.encodings_congr

/-- info: 'STACS2027.encodings_kCycleCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.encodings_kCycleCore

/-- info: 'STACS2027.markedEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.markedEdges

/-- info: 'STACS2027.incident' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.incident

/-- info: 'STACS2027.omittedPosition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.omittedPosition

/-- info: 'STACS2027.omittedVertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.omittedVertex

/-- info: 'STACS2027.recoveredPath' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.recoveredPath

/-- info: 'STACS2027.recoverAssignment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.recoverAssignment

/-- info: 'STACS2027.deletedOverlaps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.deletedOverlaps

/-- info: 'STACS2027.omittedPosition_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.omittedPosition_lt

/-- info: 'STACS2027.recoveredPath_pathsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.recoveredPath_pathsOf

/-- info: 'STACS2027.incident_eq_false_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.incident_eq_false_iff

/-- info: 'STACS2027.mem_selected_iff_incident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_selected_iff_incident

/-- info: 'STACS2027.mem_markedEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_markedEdges

/-- info: 'STACS2027.omittedVertex_incident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.omittedVertex_incident

/-- info: 'STACS2027.recoveredPath_omits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.recoveredPath_omits

/-- info: 'STACS2027.recoveredPath_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.recoveredPath_spec

/-- info: 'STACS2027.recoveredPath_permitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.recoveredPath_permitted

/-- info: 'STACS2027.recoverAssignment_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.recoverAssignment_correct

/-- info: 'STACS2027.deletedOverlaps_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.deletedOverlaps_spec

/-- info: 'STACS2027.IsOptimalCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsOptimalCost

/-- info: 'STACS2027.firstOptionCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.firstOptionCost

/-- info: 'STACS2027.searchOptimum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.searchOptimum

/-- info: 'STACS2027.almostFormula_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.almostFormula_zero

/-- info: 'STACS2027.almostSatisfiable_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.almostSatisfiable_zero_iff

/-- info: 'STACS2027.permittedFormula_nil_satisfiable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.permittedFormula_nil_satisfiable_iff

/-- info: 'STACS2027.hasAssignment_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_mono

/-- info: 'STACS2027.validChoices_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.validChoices_first

/-- info: 'STACS2027.hasAssignment_firstOptionCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_firstOptionCost

/-- info: 'STACS2027.exists_least_of_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_least_of_exists

/-- info: 'STACS2027.exists_isOptimalCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_isOptimalCost

/-- info: 'STACS2027.isOptimalCost_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isOptimalCost_unique

/-- info: 'STACS2027.almostSatisfiable_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.almostSatisfiable_mono

/-- info: 'STACS2027.exists_almostSatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_almostSatisfiable

/-- info: 'STACS2027.isOptimalCost_iff_least_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isOptimalCost_iff_least_accepted

/-- info: 'STACS2027.find?_range_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.find?_range_eq_some_iff

/-- info: 'STACS2027.searchOptimum_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.searchOptimum_correct

/-- info: 'STACS2027.next' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.next

/-- info: 'STACS2027.next_lt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.next_lt

/-- info: 'STACS2027.next_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.next_eq_iff

/-- info: 'STACS2027.next_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.next_inj

/-- info: 'STACS2027.next_ne_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.next_ne_self

/-- info: 'STACS2027.getD_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.getD_inj

/-- info: 'STACS2027.getD_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.getD_mem

/-- info: 'STACS2027.mem_iff_getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.mem_iff_getD

/-- info: 'STACS2027.pathEdges_getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_getD

/-- info: 'STACS2027.cycleEdges_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_getD

/-- info: 'STACS2027.edge_fst_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_fst_snd

/-- info: 'STACS2027.vertex_on_edgeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.vertex_on_edgeAt

/-- info: 'STACS2027.disjointEdges_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointEdges_edge

/-- info: 'STACS2027.disjointEdges_edgeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointEdges_edgeAt

/-- info: 'STACS2027.mem_selected_iff_position' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_selected_iff_position

/-- info: 'STACS2027.edgeAt_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgeAt_inj

/-- info: 'STACS2027.exists_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_position

/-- info: 'STACS2027.next_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.next_spec

/-- info: 'STACS2027.common_vertex_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.common_vertex_positions

/-- info: 'STACS2027.pathVariable_div' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathVariable_div

/-- info: 'STACS2027.pathVariable_mod' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pathVariable_mod

/-- info: 'STACS2027.pathVariable_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathVariable_inj

/-- info: 'STACS2027.pathVariable_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathVariable_lt

/-- info: 'STACS2027.kCycle_isCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.kCycle_isCycle

/-- info: 'STACS2027.kCycle_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.kCycle_mem

/-- info: 'STACS2027.edgePosition_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgePosition_lt

/-- info: 'STACS2027.cycleEdgeAt_edgePosition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdgeAt_edgePosition

/-- info: 'STACS2027.edgePosition_cycleEdgeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgePosition_cycleEdgeAt

/-- info: 'STACS2027.cycleEdgeAt_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdgeAt_mem

/-- info: 'STACS2027.edgeVariable_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgeVariable_eq

/-- info: 'STACS2027.kCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.kCycle

/-- info: 'STACS2027.pathVariable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pathVariable

/-- info: 'STACS2027.cycleEdgeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdgeAt

/-- info: 'STACS2027.edgePosition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgePosition

/-- info: 'STACS2027.edgeVariable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgeVariable

/-- info: 'STACS2027.disjointEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.disjointEdges

/-- info: 'STACS2027.pathConstraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathConstraints

/-- info: 'STACS2027.candidateOverlaps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.candidateOverlaps

/-- info: 'STACS2027.overlapClause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlapClause

/-- info: 'STACS2027.permittedFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.permittedFormula

/-- info: 'STACS2027.almostFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.almostFormula

/-- info: 'STACS2027.AlmostSatisfiable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.AlmostSatisfiable

/-- info: 'STACS2027.edgesOnCycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgesOnCycles

/-- info: 'STACS2027.cyclesThrough' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cyclesThrough

/-- info: 'STACS2027.prefixOffset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixOffset

/-- info: 'STACS2027.prefixVariable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixVariable

/-- info: 'STACS2027.prefixClauses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixClauses

/-- info: 'STACS2027.zeroCostFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.zeroCostFormula

/-- info: 'STACS2027.omittedIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.omittedIndex

/-- info: 'STACS2027.omittedIndex_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.omittedIndex_spec

/-- info: 'STACS2027.evalClause_overlapClause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.evalClause_overlapClause

/-- info: 'STACS2027.permittedFormula_satisfiable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.permittedFormula_satisfiable_iff

/-- info: 'STACS2027.almostFormula_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.almostFormula_length

/-- info: 'STACS2027.mem_almostFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_almostFormula

/-- info: 'STACS2027.almostSatisfiable_iff_hasAssignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.almostSatisfiable_iff_hasAssignment

/-- info: 'STACS2027.PrefixEncodingClauseCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PrefixEncodingClauseCount

/-- info: 'STACS2027.prefixEncodingClauseCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixEncodingClauseCount

/-- info: 'STACS2027.violatedBy' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.violatedBy

/-- info: 'STACS2027.mem_candidateOverlaps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_candidateOverlaps

/-- info: 'STACS2027.overlap_row_components' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_row_components

/-- info: 'STACS2027.candidateOverlaps_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.candidateOverlaps_nodup

/-- info: 'STACS2027.double_sum_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.double_sum_succ

/-- info: 'STACS2027.cost_map_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_map_range

/-- info: 'STACS2027.overlap_eq_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_eq_countP

/-- info: 'STACS2027.countP_candidateOverlaps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_candidateOverlaps

/-- info: 'STACS2027.PathsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PathsOf

/-- info: 'STACS2027.PathsOf.nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PathsOf.nodup

/-- info: 'STACS2027.PathsOf.subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PathsOf.subset

/-- info: 'STACS2027.countP_path_of_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_path_of_cycle

/-- info: 'STACS2027.cost_eq_countP_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_eq_countP_violated

/-- info: 'STACS2027.Paper.path_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.path_variables

/-- info: 'STACS2027.Paper.path_constraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.path_constraints

/-- info: 'STACS2027.Paper.candidate_overlaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.candidate_overlaps

/-- info: 'STACS2027.Paper.overlap_constraint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.overlap_constraint

/-- info: 'STACS2027.Paper.permitted_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.permitted_formula

/-- info: 'STACS2027.Paper.replicated_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.replicated_formula

/-- info: 'STACS2027.Paper.encoding_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.encoding_correct

/-- info: 'STACS2027.Paper.clause_deletion_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.clause_deletion_correct

/-- info: 'STACS2027.Paper.boundedCost_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.boundedCost_encoding

/-- info: 'STACS2027.Paper.boundedCost_encoding_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.boundedCost_encoding_size

/-- info: 'STACS2027.Paper.prefix_clauses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.prefix_clauses

/-- info: 'STACS2027.Paper.prefix_variables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.prefix_variables

/-- info: 'STACS2027.Paper.prefix_encoding_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.prefix_encoding_count

/-- info: 'STACS2027.Paper.zeroCost_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.zeroCost_encoding

/-- info: 'STACS2027.Paper.zeroCost_encoding_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.zeroCost_encoding_size

/-- info: 'STACS2027.assignmentOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assignmentOf

/-- info: 'STACS2027.assignmentOf_pathVariable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assignmentOf_pathVariable

/-- info: 'STACS2027.assignmentOf_pathVariable_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assignmentOf_pathVariable_iff

/-- info: 'STACS2027.mem_pathConstraints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_pathConstraints

/-- info: 'STACS2027.evalClause_two_neg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalClause_two_neg

/-- info: 'STACS2027.evalClause_two_pos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalClause_two_pos

/-- info: 'STACS2027.pathConstraints_satisfied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathConstraints_satisfied

/-- info: 'STACS2027.decode_of_satisfied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.decode_of_satisfied

/-- info: 'STACS2027.nodup_eraseDups' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.nodup_eraseDups

/-- info: 'STACS2027.edgesOnCycles_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgesOnCycles_nodup

/-- info: 'STACS2027.mem_edgesOnCycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_edgesOnCycles

/-- info: 'STACS2027.mem_cyclesThrough' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_cyclesThrough

/-- info: 'STACS2027.cyclesThrough_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cyclesThrough_nodup

/-- info: 'STACS2027.cyclesThrough_getD_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cyclesThrough_getD_lt

/-- info: 'STACS2027.cyclesThrough_getD_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cyclesThrough_getD_mem

/-- info: 'STACS2027.cyclesThrough_getD_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cyclesThrough_getD_inj

/-- info: 'STACS2027.countP_contains_eq_sum_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_contains_eq_sum_count

/-- info: 'STACS2027.countP_edgesOnCycles_eq_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_edgesOnCycles_eq_k

/-- info: 'STACS2027.sum_cyclesThrough_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_cyclesThrough_length

/-- info: 'STACS2027.sum_sub_one_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_sub_one_le

/-- info: 'STACS2027.Sublist.sum_le_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Sublist.sum_le_sum

/-- info: 'STACS2027.dropWhile_ne_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.dropWhile_ne_of_mem

/-- info: 'STACS2027.split_at_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.split_at_mem

/-- info: 'STACS2027.prefixSum_le_of_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixSum_le_of_after

/-- info: 'STACS2027.prefixSum_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixSum_add_le

/-- info: 'STACS2027.mem_dropWhile_of_mem_takeWhile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_dropWhile_of_mem_takeWhile

/-- info: 'STACS2027.prefixOffset_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixOffset_ge

/-- info: 'STACS2027.prefixVariable_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixVariable_lt

/-- info: 'STACS2027.prefixVariable_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixVariable_inj

/-- info: 'STACS2027.pathConstraints_two_literals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathConstraints_two_literals

/-- info: 'STACS2027.overlapClause_two_literals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlapClause_two_literals

/-- info: 'STACS2027.almostFormula_two_cnf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.almostFormula_two_cnf

/-- info: 'STACS2027.countP_gt_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_gt_range

/-- info: 'STACS2027.countP_point' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_point

/-- info: 'STACS2027.countP_and_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_and_or

/-- info: 'STACS2027.disjoint_pairs_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjoint_pairs_count

/-- info: 'STACS2027.per_cycle_pathConstraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.per_cycle_pathConstraints

/-- info: 'STACS2027.two_mul_pathConstraints_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.two_mul_pathConstraints_length

/-- info: 'STACS2027.two_mul_candidateOverlaps_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.two_mul_candidateOverlaps_length_le

/-- info: 'STACS2027.prefixClauses_two_literals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixClauses_two_literals

/-- info: 'STACS2027.zeroCostFormula_two_cnf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.zeroCostFormula_two_cnf

/-- info: 'STACS2027.prefixClauses_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixClauses_length_le

/-- info: 'STACS2027.filterMap_positive_range_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.filterMap_positive_range_length

/-- info: 'STACS2027.prefixClauses_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixClauses_length

/-- info: 'STACS2027.prefixAuxiliaryVariables_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixAuxiliaryVariables_count

/-- info: 'STACS2027.zeroCostFormula_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.zeroCostFormula_length_le

/-- info: 'STACS2027.almostFormula_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.almostFormula_size

/-- info: 'STACS2027.zeroCostFormula_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.zeroCostFormula_size

/-- info: 'STACS2027.getD_map_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.getD_map_range

/-- info: 'STACS2027.map_getD_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.map_getD_range

/-- info: 'STACS2027.validChoices_getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.validChoices_getD

/-- info: 'STACS2027.validChoices_of_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.validChoices_of_getD

/-- info: 'STACS2027.mem_selectedOptions_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_selectedOptions_iff

/-- info: 'STACS2027.pathsOf_of_validChoices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathsOf_of_validChoices

/-- info: 'STACS2027.validChoices_of_pathsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.validChoices_of_pathsOf

/-- info: 'STACS2027.contains_eq_false_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.contains_eq_false_iff

/-- info: 'STACS2027.Sublist.count_add_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Sublist.count_add_le

/-- info: 'STACS2027.Sublist.length_le_countP_contains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Sublist.length_le_countP_contains

/-- info: 'STACS2027.sum_map_le_sum_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_le_sum_map

/-- info: 'STACS2027.countP_lt_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_lt_range

/-- info: 'STACS2027.sum_map_range_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_range_single

/-- info: 'STACS2027.countP_eq_sum_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_eq_sum_range

/-- info: 'STACS2027.evalCNF_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.evalCNF_iff

/-- info: 'STACS2027.mem_flatten_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_flatten_replicate

/-- info: 'STACS2027.count_flatten_replicate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.count_flatten_replicate

/-- info: 'STACS2027.length_flatten_replicate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.length_flatten_replicate

/-- info: 'STACS2027.mem_prefixClauses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_prefixClauses

/-- info: 'STACS2027.mem_zeroCostFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_zeroCostFormula

/-- info: 'STACS2027.assignmentOf_edgeVariable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assignmentOf_edgeVariable

/-- info: 'STACS2027.edgeVariable_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgeVariable_lt

/-- info: 'STACS2027.evalClause_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalClause_congr

/-- info: 'STACS2027.evalClause_pos_neg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalClause_pos_neg

/-- info: 'STACS2027.evalClause_neg_pos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalClause_neg_pos

/-- info: 'STACS2027.allPrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allPrefix

/-- info: 'STACS2027.mem_allPrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_allPrefix

/-- info: 'STACS2027.prefixValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixValue

/-- info: 'STACS2027.zeroAssignment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.zeroAssignment

/-- info: 'STACS2027.find?_key_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.find?_key_injective

/-- info: 'STACS2027.zeroAssignment_pathVariable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.zeroAssignment_pathVariable

/-- info: 'STACS2027.zeroAssignment_prefixVariable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.zeroAssignment_prefixVariable

/-- info: 'STACS2027.prefixValue_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixValue_succ

/-- info: 'STACS2027.prefixValue_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.prefixValue_iff

/-- info: 'STACS2027.zeroCostFormula_satisfiable_of_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.zeroCostFormula_satisfiable_of_assignment

/-- info: 'STACS2027.no_overlap_of_satisfied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.no_overlap_of_satisfied

/-- info: 'STACS2027.recoverAssignment_zeroCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.recoverAssignment_zeroCost

/-- info: 'STACS2027.zeroCostFormula_satisfiable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.zeroCostFormula_satisfiable_iff
