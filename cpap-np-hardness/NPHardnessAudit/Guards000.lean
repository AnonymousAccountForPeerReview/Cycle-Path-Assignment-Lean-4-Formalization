module

import NPHardness

/-!
Exact-message axiom guards for every explicitly named NPHardness declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.IsCycle.two_neighbors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.two_neighbors

/-- info: 'STACS2027.exists_rank_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_rank_max

/-- info: 'STACS2027.AcyclicRank' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.AcyclicRank

/-- info: 'STACS2027.AcyclicRank.no_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.AcyclicRank.no_cycle

/-- info: 'STACS2027.CycleCoreRank' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.CycleCoreRank

/-- info: 'STACS2027.CycleCoreRank.cycle_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.CycleCoreRank.cycle_zero

/-- info: 'STACS2027.cost_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_perm

/-- info: 'STACS2027.SameCycle.vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SameCycle.vertices

/-- info: 'STACS2027.distinctCycles_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.distinctCycles_eq

/-- info: 'STACS2027.distinctCycles_nodup' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.distinctCycles_nodup

/-- info: 'STACS2027.FamilyAssignment' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.FamilyAssignment

/-- info: 'STACS2027.validChoices_vertex_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.validChoices_vertex_function

/-- info: 'STACS2027.hasAssignment_iff_enumerated_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_iff_enumerated_family

/-- info: 'STACS2027.representativeIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.representativeIn

/-- info: 'STACS2027.representativeIn_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.representativeIn_spec

/-- info: 'STACS2027.representatives_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.representatives_perm

/-- info: 'STACS2027.familyAssignment_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.familyAssignment_transport

/-- info: 'STACS2027.hasAssignment_iff_complete_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_iff_complete_family

/-- info: 'STACS2027.hasAssignment_graph_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_graph_equiv

/-- info: 'STACS2027.hasAssignment_graph_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_graph_perm

/-- info: 'STACS2027.familyAssignment_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.familyAssignment_relabel

/-- info: 'STACS2027.hasAssignment_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_relabel

/-- info: 'STACS2027.subdividedEdge_fresh_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdividedEdge_fresh_source

/-- info: 'STACS2027.subdividedEdge_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdividedEdge_old

/-- info: 'STACS2027.realizeLinks_old_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_old_edge

/-- info: 'STACS2027.clausePortVertices' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clausePortVertices

/-- info: 'STACS2027.attachmentAt_vertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.attachmentAt_vertex

/-- info: 'STACS2027.clausePortVertices_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clausePortVertices_bound

/-- info: 'STACS2027.clauseSkeleton_port_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseSkeleton_port_edges

/-- info: 'STACS2027.clauseGraph_attachment_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseGraph_attachment_edge

/-- info: 'STACS2027.variable_clause_vertex_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_clause_vertex_intersection

/-- info: 'STACS2027.attachmentAt_endpoint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.attachmentAt_endpoint

/-- info: 'STACS2027.clauseGraph_ports' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseGraph_ports

/-- info: 'STACS2027.formulaGraph_shared_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_shared_edge

/-- info: 'STACS2027.gridCopyTemplate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridCopyTemplate

/-- info: 'STACS2027.gridCopyTemplate_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridCopyTemplate_emit

/-- info: 'STACS2027.boundedOccurrence_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.boundedOccurrence_perm

/-- info: 'STACS2027.satisfiable_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.satisfiable_perm

/-- info: 'STACS2027.occurrences' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.occurrences

/-- info: 'STACS2027.BoundedOccurrence' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence

/-- info: 'STACS2027.BoundedOccurrence.isThreeCNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.isThreeCNF

/-- info: 'STACS2027.HasAssignment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HasAssignment

/-- info: 'STACS2027.hasAssignment_iff_load_cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_iff_load_cost

/-- info: 'STACS2027.graphEmitter_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.graphEmitter_correct

/-- info: 'STACS2027.graphEmitter_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.graphEmitter_polyTime

/-- info: 'STACS2027.cpap_np_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap_np_hard

/-- info: 'STACS2027.paddingClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.paddingClause

/-- info: 'STACS2027.addPaddingClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.addPaddingClause

/-- info: 'STACS2027.occurrences_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.occurrences_append

/-- info: 'STACS2027.occurrences_ge_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_ge_bound

/-- info: 'STACS2027.paddingClause_positive_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.paddingClause_positive_bound

/-- info: 'STACS2027.paddingClause_negative_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.paddingClause_negative_zero

/-- info: 'STACS2027.paddingClause_below_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.paddingClause_below_zero

/-- info: 'STACS2027.addPaddingClause_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.addPaddingClause_bounded

/-- info: 'STACS2027.addPaddingClause_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.addPaddingClause_distinct

/-- info: 'STACS2027.addPaddingClause_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.addPaddingClause_sat

/-- info: 'STACS2027.padFormula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.padFormula

/-- info: 'STACS2027.padFormula_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.padFormula_length

/-- info: 'STACS2027.padFormula_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.padFormula_sat

/-- info: 'STACS2027.padFormula_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.padFormula_bounded

/-- info: 'STACS2027.padFormula_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.padFormula_distinct

/-- info: 'STACS2027.emptyFormula_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.emptyFormula_bounded

/-- info: 'STACS2027.emptyFormula_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.emptyFormula_distinct

/-- info: 'STACS2027.ClauseVariablesDistinct' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ClauseVariablesDistinct

/-- info: 'STACS2027.ClauseVariablesDistinct.placed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.ClauseVariablesDistinct.placed

/-- info: 'STACS2027.nodup_map_injective_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.nodup_map_injective_on

/-- info: 'STACS2027.clause_single_variable_port' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_single_variable_port

/-- info: 'STACS2027.formulaGraph_clause_induced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_clause_induced

/-- info: 'STACS2027.PrivateClauseVertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PrivateClauseVertex

/-- info: 'STACS2027.private_clause_neighbor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.private_clause_neighbor

/-- info: 'STACS2027.path_endpoint_edge_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.path_endpoint_edge_absent

/-- info: 'STACS2027.clause_excursion_one_variable_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_excursion_one_variable_bound

/-- info: 'STACS2027.clauseThree5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThree5

/-- info: 'STACS2027.clauseThreeCycles5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThreeCycles5

/-- info: 'STACS2027.clauseThreePorts5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThreePorts5

/-- info: 'STACS2027.clauseThree5_enumeration' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_enumeration

/-- info: 'STACS2027.clauseThree5_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_distinct

/-- info: 'STACS2027.clauseThree5_cycles_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_cycles_valid

/-- info: 'STACS2027.clauseThree5_no_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_no_zero

/-- info: 'STACS2027.clauseThree5_cost_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_cost_positive

/-- info: 'STACS2027.clauseThree5_blocked_search' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_blocked_search

/-- info: 'STACS2027.clauseThree5_blocked_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_blocked_lower

/-- info: 'STACS2027.clauseThreeWitness5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThreeWitness5

/-- info: 'STACS2027.choosePaths' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.choosePaths

/-- info: 'STACS2027.clauseThree5_witness_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_witness_valid

/-- info: 'STACS2027.clauseThree5_witness_cost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_witness_cost

/-- info: 'STACS2027.clauseThreeGreen' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThreeGreen

/-- info: 'STACS2027.clauseThreeNonGreen' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThreeNonGreen

/-- info: 'STACS2027.clauseThreeTreeRank' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeTreeRank

/-- info: 'STACS2027.greenCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.greenCount

/-- info: 'STACS2027.clauseThree_rank_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_rank_certificate

/-- info: 'STACS2027.clauseThree_nonGreen_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_nonGreen_rank

/-- info: 'STACS2027.clauseThree_nonGreen_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_nonGreen_acyclic

/-- info: 'STACS2027.clauseThree_cycle_uses_green' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_cycle_uses_green

/-- info: 'STACS2027.clauseThree_no_triangles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_no_triangles

/-- info: 'STACS2027.clauseThree_no_quadrangles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_no_quadrangles

/-- info: 'STACS2027.clauseThree_girth_five' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_girth_five

/-- info: 'STACS2027.clauseThree_edge_expanded_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_edge_expanded_length

/-- info: 'STACS2027.sum_edge_weights' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_edge_weights

/-- info: 'STACS2027.clauseThree_expanded_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_expanded_length

/-- info: 'STACS2027.clauseThree_projects_to_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_projects_to_five

/-- info: 'STACS2027.clauseThree_general_cycle_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_general_cycle_classification

/-- info: 'STACS2027.clauseThree_five_green_count' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThree_five_green_count

/-- info: 'STACS2027.clauseThree_general_cycle_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_general_cycle_realization

/-- info: 'STACS2027.clauseTwoCycles5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoCycles5

/-- info: 'STACS2027.clauseTwo5_enumeration' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_enumeration

/-- info: 'STACS2027.clauseTwo5_cycles_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_cycles_valid

/-- info: 'STACS2027.clauseTwo5_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_distinct

/-- info: 'STACS2027.clauseTwo5_no_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_no_zero

/-- info: 'STACS2027.clauseTwo5_cost_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_cost_positive

/-- info: 'STACS2027.clauseTwo5_blocked_search' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_blocked_search

/-- info: 'STACS2027.clauseTwo5_blocked_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_blocked_lower

/-- info: 'STACS2027.clauseTwoWitness5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWitness5

/-- info: 'STACS2027.clauseTwo5_witness_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_witness_valid

/-- info: 'STACS2027.clauseTwo5_witness_cost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_witness_cost

/-- info: 'STACS2027.clauseTwoCycles6' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoCycles6

/-- info: 'STACS2027.clauseTwo6_enumeration' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_enumeration

/-- info: 'STACS2027.clauseTwo6_cycles_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_cycles_valid

/-- info: 'STACS2027.clauseTwo6_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_distinct

/-- info: 'STACS2027.clauseTwo6_no_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_no_zero

/-- info: 'STACS2027.clauseTwo6_cost_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_cost_positive

/-- info: 'STACS2027.clauseTwo6_blocked_search' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_blocked_search

/-- info: 'STACS2027.clauseTwo6_blocked_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_blocked_lower

/-- info: 'STACS2027.clauseTwoWitness6' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWitness6

/-- info: 'STACS2027.clauseTwo6_witness_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_witness_valid

/-- info: 'STACS2027.clauseTwo6_witness_cost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_witness_cost

/-- info: 'STACS2027.clauseTwo_projects_to_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_projects_to_five

/-- info: 'STACS2027.clauseTwo_skeleton_eq_five' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_skeleton_eq_five

/-- info: 'STACS2027.clauseTwo_general_cycle_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_general_cycle_classification

/-- info: 'STACS2027.clauseTwo_five_profiles' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_five_profiles

/-- info: 'STACS2027.clauseTwo_five_expanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_five_expanded

/-- info: 'STACS2027.clauseTwo_general_cycle_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_general_cycle_realization

/-- info: 'STACS2027.clauseTwo_profiles_excluded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_profiles_excluded

/-- info: 'STACS2027.clauseTwoWeight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWeight

/-- info: 'STACS2027.clauseTwo_edge_expanded_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_edge_expanded_length

/-- info: 'STACS2027.sum_colour_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_colour_weight

/-- info: 'STACS2027.clauseTwo_expanded_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_expanded_length

/-- info: 'STACS2027.clauseTwoNonGreen' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoNonGreen

/-- info: 'STACS2027.clauseTwoCore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoCore

/-- info: 'STACS2027.clauseTwoCoreRank' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoCoreRank

/-- info: 'STACS2027.clauseTwo_core_rank_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_core_rank_certificate

/-- info: 'STACS2027.clauseTwo_core_zero_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_core_zero_certificate

/-- info: 'STACS2027.clauseTwo_nonGreen_core_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_nonGreen_core_rank

/-- info: 'STACS2027.clauseTwo_nonGreen_cycle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_nonGreen_cycle_bound

/-- info: 'STACS2027.clauseTwo_long_cycle_uses_green' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_long_cycle_uses_green

/-- info: 'STACS2027.clauseTwo_short_profile_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_short_profile_certificate

/-- info: 'STACS2027.clauseTwoGreen' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoGreen

/-- info: 'STACS2027.clauseTwoOrange' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoOrange

/-- info: 'STACS2027.clauseTwoBlue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoBlue

/-- info: 'STACS2027.clauseTwoRed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoRed

/-- info: 'STACS2027.colourCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.colourCount

/-- info: 'STACS2027.CycleProfile' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.CycleProfile

/-- info: 'STACS2027.clauseTwoProfile' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoProfile

/-- info: 'STACS2027.profileLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.profileLength

/-- info: 'STACS2027.clauseTwoExcludedProfiles' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoExcludedProfiles

/-- info: 'STACS2027.clauseFamily_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseFamily_witness

/-- info: 'STACS2027.load_zero_of_port_avoided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_zero_of_port_avoided

/-- info: 'STACS2027.combine_indexed_choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.combine_indexed_choices

/-- info: 'STACS2027.gadgetIndices' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gadgetIndices

/-- info: 'STACS2027.indexedFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.indexedFamily

/-- info: 'STACS2027.formulaFamily_indexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaFamily_indexed

/-- info: 'STACS2027.gadgetIndex_variable_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gadgetIndex_variable_mem

/-- info: 'STACS2027.gadgetIndex_clause_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gadgetIndex_clause_mem

/-- info: 'STACS2027.indexedFamily_clause_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.indexedFamily_clause_at

/-- info: 'STACS2027.formulaGraph_satisfied_crossCost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_satisfied_crossCost_zero

/-- info: 'STACS2027.selectedOptions' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.selectedOptions

/-- info: 'STACS2027.searchBudget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.searchBudget

/-- info: 'STACS2027.cost_tail_le' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.cost_tail_le

/-- info: 'STACS2027.ValidChoices' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ValidChoices

/-- info: 'STACS2027.validChoicesDecidable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.validChoicesDecidable

/-- info: 'STACS2027.searchBudget_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.searchBudget_complete

/-- info: 'STACS2027.searchBudget_excludes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.searchBudget_excludes

/-- info: 'STACS2027.searchBudget_excludes_cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.searchBudget_excludes_cost

/-- info: 'STACS2027.IsSimplePath.excursion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsSimplePath.excursion

/-- info: 'STACS2027.clause_excursion_start_variable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_excursion_start_variable

/-- info: 'STACS2027.clause_excursion_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_excursion_length

/-- info: 'STACS2027.IsCycle.tail_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.tail_path

/-- info: 'STACS2027.formulaGraph_cycle_private_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_cycle_private_clause

/-- info: 'STACS2027.SameCycle.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SameCycle.refl

/-- info: 'STACS2027.SameCycle.symm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SameCycle.symm

/-- info: 'STACS2027.SameCycle.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SameCycle.trans

/-- info: 'STACS2027.cycleRepresentatives' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleRepresentatives

/-- info: 'STACS2027.cycleRepresentatives_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleRepresentatives_cons

/-- info: 'STACS2027.cycleRepresentatives_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleRepresentatives_subset

/-- info: 'STACS2027.cycleRepresentatives_pairwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleRepresentatives_pairwise

/-- info: 'STACS2027.cycleRepresentatives_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleRepresentatives_cover

/-- info: 'STACS2027.cycleRepresentatives_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleRepresentatives_nodup

/-- info: 'STACS2027.edge_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.edge_comm

/-- info: 'STACS2027.edge_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_eq_iff

/-- info: 'STACS2027.edge_left_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_left_inj

/-- info: 'STACS2027.IsCycle.of_perm_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.of_perm_edges

/-- info: 'STACS2027.sameCycle_append_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sameCycle_append_swap

/-- info: 'STACS2027.IsCycle.append_swap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.append_swap

/-- info: 'STACS2027.IsCycle.rotate_to_vertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.rotate_to_vertex

/-- info: 'STACS2027.pathEdges_append_last' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_append_last

/-- info: 'STACS2027.cycleEdges_snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_snoc

/-- info: 'STACS2027.pathEdges_reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_reverse

/-- info: 'STACS2027.cycleEdges_reverse_tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_reverse_tail

/-- info: 'STACS2027.sameCycle_reverse_tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sameCycle_reverse_tail

/-- info: 'STACS2027.IsCycle.reverse_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.reverse_tail

/-- info: 'STACS2027.pathEdge_vertices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdge_vertices

/-- info: 'STACS2027.IsCycle.edges_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.edges_nodup

/-- info: 'STACS2027.IsCycle.vertex_incident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.vertex_incident

/-- info: 'STACS2027.distinctLiterals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.distinctLiterals

/-- info: 'STACS2027.distinctLiterals_sublist' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.distinctLiterals_sublist

/-- info: 'STACS2027.distinctLiterals_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.distinctLiterals_mem

/-- info: 'STACS2027.distinctLiterals_nodup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.distinctLiterals_nodup

/-- info: 'STACS2027.distinctLiterals_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.distinctLiterals_eval

/-- info: 'STACS2027.normalizeClauses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.normalizeClauses

/-- info: 'STACS2027.normalizeClauses_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.normalizeClauses_eval

/-- info: 'STACS2027.FormulaDeletion' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.FormulaDeletion

/-- info: 'STACS2027.FormulaDeletion.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.FormulaDeletion.refl

/-- info: 'STACS2027.FormulaDeletion.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.FormulaDeletion.trans

/-- info: 'STACS2027.FormulaDeletion.filter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.FormulaDeletion.filter

/-- info: 'STACS2027.distinctLiterals_deletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.distinctLiterals_deletion

/-- info: 'STACS2027.normalizeClauses_deletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.normalizeClauses_deletion

/-- info: 'STACS2027.distinct_variables_of_nodup_nontaut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.distinct_variables_of_nodup_nontaut

/-- info: 'STACS2027.normalizeClauses_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.normalizeClauses_distinct

/-- info: 'STACS2027.FormulaDeletion.occurrences_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.FormulaDeletion.occurrences_le

/-- info: 'STACS2027.FormulaDeletion.threeCNF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.FormulaDeletion.threeCNF

/-- info: 'STACS2027.FormulaDeletion.distinct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.FormulaDeletion.distinct

/-- info: 'STACS2027.emitterSlots' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.emitterSlots

/-- info: 'STACS2027.emitterSlotsExpr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.emitterSlotsExpr

/-- info: 'STACS2027.emitterSlotsExpr_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.emitterSlotsExpr_eval

/-- info: 'STACS2027.allocatedEmit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.allocatedEmit

/-- info: 'STACS2027.allocatedEmit_forget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocatedEmit_forget

/-- info: 'STACS2027.allocatedEmit_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocatedEmit_bounds

/-- info: 'STACS2027.allocatedEmit_descending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocatedEmit_descending

/-- info: 'STACS2027.allocatedEmit_literals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocatedEmit_literals

/-- info: 'STACS2027.sourceChainChunk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sourceChainChunk

/-- info: 'STACS2027.sourceChainChunk_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sourceChainChunk_eval

/-- info: 'STACS2027.chainEnd_clause_sizes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.chainEnd_clause_sizes

/-- info: 'STACS2027.sourceChainChunk_sizes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceChainChunk_sizes

/-- info: 'STACS2027.expandSourceUnit_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.expandSourceUnit_mem

/-- info: 'STACS2027.sourceChainChunk_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceChainChunk_below

/-- info: 'STACS2027.allocatedThree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.allocatedThree

/-- info: 'STACS2027.allocatedThree_sizes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocatedThree_sizes

/-- info: 'STACS2027.allocatedThree_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocatedThree_sound

/-- info: 'STACS2027.allocatedThree_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocatedThree_below

/-- info: 'STACS2027.allocatedThree_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocatedThree_complete

/-- info: 'STACS2027.allocatedThree_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.allocatedThree_satisfiable

/-- info: 'STACS2027.transformAllocated' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.transformAllocated

/-- info: 'STACS2027.transformAllocated_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.transformAllocated_emit

/-- info: 'STACS2027.chainEndExpr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.chainEndExpr

/-- info: 'STACS2027.chainChunkExpr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.chainChunkExpr

/-- info: 'STACS2027.chainEndExpr_emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.chainEndExpr_emit

/-- info: 'STACS2027.chainChunkExpr_emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.chainChunkExpr_emit

/-- info: 'STACS2027.normalizeTemplate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.normalizeTemplate

/-- info: 'STACS2027.normalizedEmitter' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.normalizedEmitter

/-- info: 'STACS2027.normalizedEmitter_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.normalizedEmitter_emit

/-- info: 'STACS2027.normalizedEmitter_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.normalizedEmitter_correct

/-- info: 'STACS2027.normalizedEmitter_sizes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.normalizedEmitter_sizes

/-- info: 'STACS2027.inNP_twoThreeEmitter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.inNP_twoThreeEmitter

/-- info: 'STACS2027.vertices' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.vertices

/-- info: 'STACS2027.neighbors' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.neighbors

/-- info: 'STACS2027.walksFrom' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.walksFrom

/-- info: 'STACS2027.rawCycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rawCycles

/-- info: 'STACS2027.cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycles

/-- info: 'STACS2027.raw_enumerated_isCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.raw_enumerated_isCycle

/-- info: 'STACS2027.enumerated_isCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.enumerated_isCycle

/-- info: 'STACS2027.le_foldr_max_of_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.le_foldr_max_of_mem

/-- info: 'STACS2027.mem_vertices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_vertices

/-- info: 'STACS2027.endpoints_mem_vertices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.endpoints_mem_vertices

/-- info: 'STACS2027.mem_walksFrom_of_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_walksFrom_of_path

/-- info: 'STACS2027.pathEdges_subset_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_subset_append

/-- info: 'STACS2027.isCycle_raw_enumerated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isCycle_raw_enumerated

/-- info: 'STACS2027.isCycle_represented' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isCycle_represented

/-- info: 'STACS2027.cycles_pairwise_different' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycles_pairwise_different

/-- info: 'STACS2027.cycles_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycles_nodup

/-- info: 'STACS2027.clauseRegion_port' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseRegion_port

/-- info: 'STACS2027.formulaGraph_variable_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_variable_boundary

/-- info: 'STACS2027.formulaGraph_variable_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_variable_path

/-- info: 'STACS2027.clause_exit_variable_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_exit_variable_distance

/-- info: 'STACS2027.overlap_eq_intersection_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_eq_intersection_length

/-- info: 'STACS2027.overlap_le_of_intersection_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_le_of_intersection_subset

/-- info: 'STACS2027.overlap_eq_of_intersection_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_eq_of_intersection_iff

/-- info: 'STACS2027.originalChoice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.originalChoice

/-- info: 'STACS2027.originalChoice_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.originalChoice_mem

/-- info: 'STACS2027.originalChoice_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.originalChoice_avoids

/-- info: 'STACS2027.expanded_cycle_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_cycle_intersection

/-- info: 'STACS2027.expanded_overlap_same_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_overlap_same_vertices

/-- info: 'STACS2027.expanded_overlap_normalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_overlap_normalizes

/-- info: 'STACS2027.liftEdges_subset_subdivideOnce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.liftEdges_subset_subdivideOnce

/-- info: 'STACS2027.expandedEdges_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expandedEdges_nodup

/-- info: 'STACS2027.expandedEdge_nonempty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.expandedEdge_nonempty

/-- info: 'STACS2027.expandedEdge_preserves_endpoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expandedEdge_preserves_endpoint

/-- info: 'STACS2027.expanded_cycle_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_cycle_vertices

/-- info: 'STACS2027.expandedEdge_unique_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expandedEdge_unique_parent

/-- info: 'STACS2027.expandedEdges_subset_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expandedEdges_subset_reflect

/-- info: 'STACS2027.expandedEdge_shared_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expandedEdge_shared_unchanged

/-- info: 'STACS2027.linkSteps_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.linkSteps_zero

/-- info: 'STACS2027.expandedEdges_unchanged_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expandedEdges_unchanged_mem

/-- info: 'STACS2027.expanded_selectedAt_port_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_selectedAt_port_mem

/-- info: 'STACS2027.expanded_selectedAt_port_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_selectedAt_port_count

/-- info: 'STACS2027.expanded_selectedAt_port_normalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_selectedAt_port_normalizes

/-- info: 'STACS2027.expanded_family_port_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_family_port_eq

/-- info: 'STACS2027.expanded_family_port_normalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_family_port_normalizes

/-- info: 'STACS2027.overlap_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_singleton

/-- info: 'STACS2027.cost_append_ports' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_append_ports

/-- info: 'STACS2027.load_reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.load_reverse

/-- info: 'STACS2027.costWithPorts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.costWithPorts

/-- info: 'STACS2027.costWithPorts_eq_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.costWithPorts_eq_append

/-- info: 'STACS2027.PathsPerm.costWithPorts_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PathsPerm.costWithPorts_eq

/-- info: 'STACS2027.expanded_family_costWithPorts_normalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_family_costWithPorts_normalizes

/-- info: 'STACS2027.sum_map_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sum_map_le

/-- info: 'STACS2027.cost_map_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.cost_map_le

/-- info: 'STACS2027.cost_map_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.cost_map_eq

/-- info: 'STACS2027.overlap_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_perm

/-- info: 'STACS2027.PathsPerm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PathsPerm

/-- info: 'STACS2027.PathsPerm.overlap_sums' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PathsPerm.overlap_sums

/-- info: 'STACS2027.PathsPerm.cost_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PathsPerm.cost_eq

/-- info: 'STACS2027.PathsPerm.load_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PathsPerm.load_eq

/-- info: 'STACS2027.vertex_choices_have_options' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.vertex_choices_have_options

/-- info: 'STACS2027.expanded_family_normalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_family_normalizes

/-- info: 'STACS2027.expanded_family_cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expanded_family_cost_eq

/-- info: 'STACS2027.Edge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Edge

/-- info: 'STACS2027.Graph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Graph

/-- info: 'STACS2027.Cycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Cycle

/-- info: 'STACS2027.edge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.edge

/-- info: 'STACS2027.pathEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pathEdges

/-- info: 'STACS2027.cycleEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.cycleEdges

/-- info: 'STACS2027.IsCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsCycle

/-- info: 'STACS2027.SameCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.SameCycle

/-- info: 'STACS2027.selected' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.selected

/-- info: 'STACS2027.pathEdges_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_length

/-- info: 'STACS2027.selected_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selected_length

/-- info: 'STACS2027.overlap' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.overlap

/-- info: 'STACS2027.overlap_nil_left' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.overlap_nil_left

/-- info: 'STACS2027.overlap_cons_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.overlap_cons_left

/-- info: 'STACS2027.overlap_nil_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.overlap_nil_right

/-- info: 'STACS2027.overlap_cons_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_cons_right

/-- info: 'STACS2027.overlap_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_comm

/-- info: 'STACS2027.cost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.cost

/-- info: 'STACS2027.cost_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_snoc

/-- info: 'STACS2027.cost_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_reverse

/-- info: 'STACS2027.variable_expansion_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_expansion_shared

/-- info: 'STACS2027.clauseThree_expansion_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_expansion_shared

/-- info: 'STACS2027.clauseTwo_expansion_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_expansion_shared

/-- info: 'STACS2027.clauseThree5_cycles_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_cycles_self

/-- info: 'STACS2027.clauseTwo5_cycles_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_cycles_self

/-- info: 'STACS2027.clauseThreeExpansion_cost_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeExpansion_cost_positive

/-- info: 'STACS2027.clauseTwoExpansion_cost_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoExpansion_cost_positive

/-- info: 'STACS2027.clauseThreeWitnessVertex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeWitnessVertex

/-- info: 'STACS2027.clauseTwoWitnessVertex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWitnessVertex

/-- info: 'STACS2027.clauseThreeWitnessVertex_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeWitnessVertex_valid

/-- info: 'STACS2027.clauseTwoWitnessVertex_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWitnessVertex_valid

/-- info: 'STACS2027.clauseThreeWitnessVertex_cost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeWitnessVertex_cost

/-- info: 'STACS2027.clauseTwoWitnessVertex_cost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWitnessVertex_cost

/-- info: 'STACS2027.clauseThreeExpansion_witness_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeExpansion_witness_valid

/-- info: 'STACS2027.clauseTwoExpansion_witness_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoExpansion_witness_valid

/-- info: 'STACS2027.clauseThreeExpansion_witness_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeExpansion_witness_cost

/-- info: 'STACS2027.clauseTwoExpansion_witness_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoExpansion_witness_cost

/-- info: 'STACS2027.variableExpansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpansion

/-- info: 'STACS2027.clauseThreeExpansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeExpansion

/-- info: 'STACS2027.clauseTwoExpansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoExpansion

/-- info: 'STACS2027.variableExpansion_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpansion_spec

/-- info: 'STACS2027.clauseThreeExpansion_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeExpansion_spec

/-- info: 'STACS2027.clauseTwoExpansion_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoExpansion_spec

/-- info: 'STACS2027.variableExpansion_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpansion_complete

/-- info: 'STACS2027.clauseThreeExpansion_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeExpansion_complete

/-- info: 'STACS2027.clauseTwoExpansion_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoExpansion_complete

/-- info: 'STACS2027.expansion_sameCycle_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expansion_sameCycle_reflect

/-- info: 'STACS2027.variableExpansion_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpansion_distinct

/-- info: 'STACS2027.clauseThreeExpansion_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeExpansion_distinct

/-- info: 'STACS2027.clauseTwoExpansion_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoExpansion_distinct

/-- info: 'STACS2027.clauseThreeExpansion_blocked_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeExpansion_blocked_lower

/-- info: 'STACS2027.clauseTwoExpansion_blocked_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoExpansion_blocked_lower

/-- info: 'STACS2027.clauseThreeWitnessVertex_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeWitnessVertex_avoids

/-- info: 'STACS2027.clauseTwoWitnessVertex_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWitnessVertex_avoids

/-- info: 'STACS2027.clauseThreeExpansion_witness_avoids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeExpansion_witness_avoids

/-- info: 'STACS2027.clauseTwoExpansion_witness_avoids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoExpansion_witness_avoids

/-- info: 'STACS2027.variablePrivate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variablePrivate

/-- info: 'STACS2027.clauseTwoPrivate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoPrivate

/-- info: 'STACS2027.variable_private_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_private_certificate

/-- info: 'STACS2027.clauseThree_private_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_private_certificate

/-- info: 'STACS2027.clauseTwo_private_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_private_certificate

/-- info: 'STACS2027.variable_uncoloured_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_uncoloured_unchanged

/-- info: 'STACS2027.clauseThree_uncoloured_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_uncoloured_unchanged

/-- info: 'STACS2027.clauseTwo_uncoloured_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_uncoloured_unchanged

/-- info: 'STACS2027.variable_shared_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_shared_unchanged

/-- info: 'STACS2027.clauseThree_shared_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_shared_unchanged

/-- info: 'STACS2027.clauseTwo_shared_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_shared_unchanged

/-- info: 'STACS2027.variable_ports_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_ports_unchanged

/-- info: 'STACS2027.clauseThree_ports_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_ports_unchanged

/-- info: 'STACS2027.clauseTwo_ports_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_ports_unchanged

/-- info: 'STACS2027.IsCycle.length_le_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.length_le_bound

/-- info: 'STACS2027.variableSkeleton' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableSkeleton

/-- info: 'STACS2027.clauseTwoSkeleton' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoSkeleton

/-- info: 'STACS2027.variable_links_wellformed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_links_wellformed

/-- info: 'STACS2027.clauseThree_links_wellformed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_links_wellformed

/-- info: 'STACS2027.clauseTwo_links_wellformed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_links_wellformed

/-- info: 'STACS2027.variable_cycle_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_cycle_projection

/-- info: 'STACS2027.clauseThree_cycle_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree_cycle_projection

/-- info: 'STACS2027.clauseTwo_cycle_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo_cycle_projection

/-- info: 'STACS2027.mapEdge_injective_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapEdge_injective_on

/-- info: 'STACS2027.count_map_on' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.count_map_on

/-- info: 'STACS2027.overlap_map_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_map_on

/-- info: 'STACS2027.cost_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_relabel

/-- info: 'STACS2027.boundedInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.boundedInverse

/-- info: 'STACS2027.boundedInverse_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.boundedInverse_left

/-- info: 'STACS2027.boundedInverse_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.boundedInverse_right

/-- info: 'STACS2027.mapGraph_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapGraph_inverse

/-- info: 'STACS2027.IsCycle.unmap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.unmap

/-- info: 'STACS2027.selectedAt_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selectedAt_map

/-- info: 'STACS2027.Link' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Link

/-- info: 'STACS2027.subdividedEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.subdividedEdge

/-- info: 'STACS2027.realizeLinks' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.realizeLinks

/-- info: 'STACS2027.subdividedEdge_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.subdividedEdge_length

/-- info: 'STACS2027.realizeLinks_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_length

/-- info: 'STACS2027.variableLinks' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableLinks

/-- info: 'STACS2027.variableGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variableGraph

/-- info: 'STACS2027.variablePorts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variablePorts

/-- info: 'STACS2027.clauseThreeLinks' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThreeLinks

/-- info: 'STACS2027.clauseThreeGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThreeGraph

/-- info: 'STACS2027.clausePorts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clausePorts

/-- info: 'STACS2027.orangeSubdivisions' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.orangeSubdivisions

/-- info: 'STACS2027.blueSubdivisions' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.blueSubdivisions

/-- info: 'STACS2027.redSubdivisions' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.redSubdivisions

/-- info: 'STACS2027.clauseTwoLinks' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoLinks

/-- info: 'STACS2027.clauseTwoGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseTwoGraph

/-- info: 'STACS2027.variableGraph_edge_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableGraph_edge_count

/-- info: 'STACS2027.clauseThreeGraph_edge_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeGraph_edge_count

/-- info: 'STACS2027.clauseTwoGraph_edge_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoGraph_edge_count

/-- info: 'STACS2027.formulaGraph_sat_implies_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_sat_implies_assignment

/-- info: 'STACS2027.formulaGraph_sat_iff_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_sat_iff_assignment

/-- info: 'STACS2027.crossCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.crossCost

/-- info: 'STACS2027.crossCost_nil_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.crossCost_nil_right

/-- info: 'STACS2027.crossCost_append_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.crossCost_append_right

/-- info: 'STACS2027.cost_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_append

/-- info: 'STACS2027.crossCost_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.crossCost_zero_iff

/-- info: 'STACS2027.crossCost_flatMap_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.crossCost_flatMap_right

/-- info: 'STACS2027.cost_flatMap_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_flatMap_disjoint

/-- info: 'STACS2027.globalVariablePaths' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.globalVariablePaths

/-- info: 'STACS2027.globalClausePaths' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.globalClausePaths

/-- info: 'STACS2027.formulaGraph_cost_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_cost_decomposition

/-- info: 'STACS2027.sum_map_eq_length_of_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_eq_length_of_positive

/-- info: 'STACS2027.formulaGraph_budget_forces_zero_interaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_budget_forces_zero_interaction

/-- info: 'STACS2027.pathEdges_not_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_not_loop

/-- info: 'STACS2027.IsCycle.not_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.not_loop

/-- info: 'STACS2027.IsCycle.edge_endpoints_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.edge_endpoints_ne

/-- info: 'STACS2027.path_variable_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.path_variable_region

/-- info: 'STACS2027.formulaGraph_cycle_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_cycle_local

/-- info: 'STACS2027.formulaGraph_cycle_local_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_cycle_local_iff

/-- info: 'STACS2027.variable_boundary_preserves_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_boundary_preserves_clause

/-- info: 'STACS2027.clause_excursion_crossing_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_excursion_crossing_bound

/-- info: 'STACS2027.variableFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableFamily

/-- info: 'STACS2027.clauseFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseFamily

/-- info: 'STACS2027.variableFamily_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableFamily_valid

/-- info: 'STACS2027.variableFamily_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableFamily_complete

/-- info: 'STACS2027.clauseFamily_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseFamily_valid

/-- info: 'STACS2027.clauseFamily_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseFamily_distinct

/-- info: 'STACS2027.clauseFamily_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseFamily_complete

/-- info: 'STACS2027.SameCycle.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SameCycle.map

/-- info: 'STACS2027.sameCycle_map_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sameCycle_map_reflect

/-- info: 'STACS2027.mapped_family_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapped_family_distinct

/-- info: 'STACS2027.clauseGraph_normalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseGraph_normalized

/-- info: 'STACS2027.placedVariableFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedVariableFamily

/-- info: 'STACS2027.placedClauseFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedClauseFamily

/-- info: 'STACS2027.formulaFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaFamily

/-- info: 'STACS2027.placedVariableFamily_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedVariableFamily_valid

/-- info: 'STACS2027.placedClauseFamily_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedClauseFamily_valid

/-- info: 'STACS2027.formulaFamily_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaFamily_valid

/-- info: 'STACS2027.formulaFamily_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaFamily_complete

/-- info: 'STACS2027.cycles_different_of_disjoint_graphs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycles_different_of_disjoint_graphs

/-- info: 'STACS2027.variable_clause_cycles_different' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_clause_cycles_different

/-- info: 'STACS2027.placedVariableFamily_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedVariableFamily_distinct

/-- info: 'STACS2027.placedClauseFamily_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedClauseFamily_distinct

/-- info: 'STACS2027.formulaFamily_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaFamily_distinct

/-- info: 'STACS2027.formulaGraph_assignment_iff_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_assignment_iff_family

/-- info: 'STACS2027.gadgetWidth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gadgetWidth

/-- info: 'STACS2027.clauseGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseGraph

/-- info: 'STACS2027.placedVariableGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.placedVariableGraph

/-- info: 'STACS2027.placedClauseGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.placedClauseGraph

/-- info: 'STACS2027.formulaGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph

/-- info: 'STACS2027.gadgetWidth_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gadgetWidth_ge

/-- info: 'STACS2027.variableGraph_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableGraph_below

/-- info: 'STACS2027.clauseThreeGraph_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeGraph_below

/-- info: 'STACS2027.clauseTwoGraph_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoGraph_below

/-- info: 'STACS2027.clauseGraph_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseGraph_below

/-- info: 'STACS2027.placeFormula_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.placeFormula_length

/-- info: 'STACS2027.placement_literal_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placement_literal_mem

/-- info: 'STACS2027.BoundedOccurrence.placed_clause_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.placed_clause_bounds

/-- info: 'STACS2027.BoundedOccurrence.placed_clause_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.placed_clause_nodup

/-- info: 'STACS2027.BoundedOccurrence.placed_clause_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.placed_clause_size

/-- info: 'STACS2027.formulaGraph_variable_contains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_variable_contains

/-- info: 'STACS2027.formulaGraph_clause_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_clause_contains

/-- info: 'STACS2027.mapped_attachment_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapped_attachment_edge

/-- info: 'STACS2027.realizeLinks_contains_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_contains_zero

/-- info: 'STACS2027.variableGraph_ports' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableGraph_ports

/-- info: 'STACS2027.variablePortEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variablePortEdge

/-- info: 'STACS2027.literalPortGlobal' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.literalPortGlobal

/-- info: 'STACS2027.variablePortEdge_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variablePortEdge_mem

/-- info: 'STACS2027.load_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_zero_iff

/-- info: 'STACS2027.load_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_pos_iff

/-- info: 'STACS2027.crossCost_zero_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.crossCost_zero_load

/-- info: 'STACS2027.load_zero_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_zero_of_subset

/-- info: 'STACS2027.activeClausePorts_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.activeClausePorts_spec

/-- info: 'STACS2027.clauseFamily_cost_one_uses_port' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseFamily_cost_one_uses_port

/-- info: 'STACS2027.variableChosen_normalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableChosen_normalizes

/-- info: 'STACS2027.clauseChosen_uses_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseChosen_uses_literal

/-- info: 'STACS2027.variableState_literal_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableState_literal_load

/-- info: 'STACS2027.formulaGraph_assignment_budget_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_assignment_budget_lower

/-- info: 'STACS2027.globalReductionGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.globalReductionGraph

/-- info: 'STACS2027.globalReduction_sat_iff_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.globalReduction_sat_iff_assignment

/-- info: 'STACS2027.BoundedOccurrence.placed_clauses_keys_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.placed_clauses_keys_disjoint

/-- info: 'STACS2027.formulaGraph_variable_vertices_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_variable_vertices_disjoint

/-- info: 'STACS2027.formulaGraph_clause_vertices_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_clause_vertices_disjoint

/-- info: 'STACS2027.mapGraph_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapGraph_disjoint

/-- info: 'STACS2027.formulaGraph_variable_edges_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_variable_edges_disjoint

/-- info: 'STACS2027.formulaGraph_clause_edges_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_clause_edges_disjoint

/-- info: 'STACS2027.overlap_zero_of_graph_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_zero_of_graph_disjoint

/-- info: 'STACS2027.clauseGraph_edge_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseGraph_edge_bound

/-- info: 'STACS2027.formulaGraph_edge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_edge_bound

/-- info: 'STACS2027.clauseBound_le_of_literals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseBound_le_of_literals

/-- info: 'STACS2027.variableBound_le_of_literals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableBound_le_of_literals

/-- info: 'STACS2027.FormulaDeletion.variableBound_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.FormulaDeletion.variableBound_le

/-- info: 'STACS2027.variableBound_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.variableBound_append

/-- info: 'STACS2027.addPaddingClause_variableBound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.addPaddingClause_variableBound

/-- info: 'STACS2027.padFormula_variableBound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.padFormula_variableBound

/-- info: 'STACS2027.globalReductionGraph_edge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.globalReductionGraph_edge_bound

/-- info: 'STACS2027.formulaGraph_assignment_implies_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_assignment_implies_sat

/-- info: 'STACS2027.VariableRegion' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.VariableRegion

/-- info: 'STACS2027.ClauseRegion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.ClauseRegion

/-- info: 'STACS2027.VariableRegion.unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.VariableRegion.unique

/-- info: 'STACS2027.ClauseRegion.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.ClauseRegion.unique

/-- info: 'STACS2027.formulaGraph_edge_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_edge_cases

/-- info: 'STACS2027.mapGraph_edge_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapGraph_edge_endpoints

/-- info: 'STACS2027.placedVariableGraph_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedVariableGraph_endpoints

/-- info: 'STACS2027.placedClauseGraph_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedClauseGraph_endpoints

/-- info: 'STACS2027.regions_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.regions_intersection

/-- info: 'STACS2027.clause_edge_between_variable_regions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_edge_between_variable_regions

/-- info: 'STACS2027.formulaGraph_between_variables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_between_variables

/-- info: 'STACS2027.gluingObstructionFormula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gluingObstructionFormula

/-- info: 'STACS2027.gluingObstruction_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gluingObstruction_bounded

/-- info: 'STACS2027.gluingObstruction_distinct' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gluingObstruction_distinct

/-- info: 'STACS2027.gluingRepairFlips' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gluingRepairFlips

/-- info: 'STACS2027.gluingObstruction_incidenceEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gluingObstruction_incidenceEmbedding

/-- info: 'STACS2027.gluingObstruction_incidenceEmbedding_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gluingObstruction_incidenceEmbedding_valid

/-- info: 'STACS2027.gluingObstruction_incidenceEmbedding_ends' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gluingObstruction_incidenceEmbedding_ends

/-- info: 'STACS2027.gluingObstruction_incidence_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gluingObstruction_incidence_planar

/-- info: 'STACS2027.K33Subdivision' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.K33Subdivision

/-- info: 'STACS2027.gluingObstructionPaths' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gluingObstructionPaths

/-- info: 'STACS2027.fixedGluingK33Subdivision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fixedGluingK33Subdivision

/-- info: 'STACS2027.fixed_gluing_contains_K33_subdivision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fixed_gluing_contains_K33_subdivision

/-- info: 'STACS2027.gluingRepairEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gluingRepairEmbedding

/-- info: 'STACS2027.gluingRepairEmbedding_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gluingRepairEmbedding_valid

/-- info: 'STACS2027.gluingRepairEmbedding_ends' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gluingRepairEmbedding_ends

/-- info: 'STACS2027.gluingRepair_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gluingRepair_planar

/-- info: 'STACS2027.gridVariablesExpr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridVariablesExpr

/-- info: 'STACS2027.gridVariablesExpr_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gridVariablesExpr_eval

/-- info: 'STACS2027.gridCopyExprs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridCopyExprs

/-- info: 'STACS2027.gridCopyExprs_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridCopyExprs_eval

/-- info: 'STACS2027.copyGraphTemplate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.copyGraphTemplate

/-- info: 'STACS2027.copyGraphTemplate_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.copyGraphTemplate_emit

/-- info: 'STACS2027.sourceWheelEmitter' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sourceWheelEmitter

/-- info: 'STACS2027.sourceWheelEmitter_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceWheelEmitter_emit

/-- info: 'STACS2027.graphEmitter' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.graphEmitter

/-- info: 'STACS2027.graphEmitter_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.graphEmitter_output

/-- info: 'STACS2027.graphRecord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.graphRecord

/-- info: 'STACS2027.validGraphRecord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.validGraphRecord

/-- info: 'STACS2027.recordEdge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.recordEdge

/-- info: 'STACS2027.instructionGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.instructionGraph

/-- info: 'STACS2027.instructionBudget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.instructionBudget

/-- info: 'STACS2027.ValidGraphInstructions' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ValidGraphInstructions

/-- info: 'STACS2027.GraphOutput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.GraphOutput

/-- info: 'STACS2027.CPAP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.CPAP

/-- info: 'STACS2027.cpapLanguage_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpapLanguage_encode

/-- info: 'STACS2027.cpap_iff_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap_iff_decode

/-- info: 'STACS2027.GraphOutput.encode_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.GraphOutput.encode_iff

/-- info: 'STACS2027.GraphOutput.nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.GraphOutput.nil

/-- info: 'STACS2027.GraphOutput.tick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.GraphOutput.tick

/-- info: 'STACS2027.GraphOutput.edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.GraphOutput.edge

/-- info: 'STACS2027.GraphOutput.append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.GraphOutput.append

/-- info: 'STACS2027.GraphOutput.flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.GraphOutput.flatMap

/-- info: 'STACS2027.graphRecords' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.graphRecords

/-- info: 'STACS2027.graphRecords_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.graphRecords_output

/-- info: 'STACS2027.clauseGraphRecords' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseGraphRecords

/-- info: 'STACS2027.clauseGraphRecords_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseGraphRecords_output

/-- info: 'STACS2027.edgeProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.edgeProgram

/-- info: 'STACS2027.edgeProgram_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgeProgram_emit

/-- info: 'STACS2027.graphProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.graphProgram

/-- info: 'STACS2027.graphProgram_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.graphProgram_emit

/-- info: 'STACS2027.variableGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.variableGraphProgram

/-- info: 'STACS2027.variableGraphProgram_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableGraphProgram_emit

/-- info: 'STACS2027.clauseVertexExpr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseVertexExpr

/-- info: 'STACS2027.clauseVertexExpr_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseVertexExpr_eval

/-- info: 'STACS2027.clauseGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseGraphProgram

/-- info: 'STACS2027.clauseGraphProgram_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseGraphProgram_emit

/-- info: 'STACS2027.transformParameterized' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.transformParameterized

/-- info: 'STACS2027.transformParameterized_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.transformParameterized_emit

/-- info: 'STACS2027.mapEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.mapEdge

/-- info: 'STACS2027.mapGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.mapGraph

/-- info: 'STACS2027.mapEdge_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapEdge_edge

/-- info: 'STACS2027.pathEdges_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_map

/-- info: 'STACS2027.cycleEdges_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_map

/-- info: 'STACS2027.IsCycle.vertex_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.vertex_bound

/-- info: 'STACS2027.IsCycle.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.map

/-- info: 'STACS2027.IsCycle.graph_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsCycle.graph_mono

/-- info: 'STACS2027.realizeLinks_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_below

/-- info: 'STACS2027.placeFormula_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.placeFormula_append

/-- info: 'STACS2027.placeLiterals_uniform' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.placeLiterals_uniform

/-- info: 'STACS2027.placeFormula_uniform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placeFormula_uniform

/-- info: 'STACS2027.gridWheelFamily_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridWheelFamily_count

/-- info: 'STACS2027.gridWheelFamily_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridWheelFamily_nodup

/-- info: 'STACS2027.gridWheelFamily_placement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridWheelFamily_placement

/-- info: 'STACS2027.sourceCopies_flatten_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceCopies_flatten_nodup

/-- info: 'STACS2027.sourceCopies_placement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceCopies_placement

/-- info: 'STACS2027.gridCopyFormula_indices_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridCopyFormula_indices_below

/-- info: 'STACS2027.gridBoundedFormula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridBoundedFormula

/-- info: 'STACS2027.gridBoundedFormula_placement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridBoundedFormula_placement

/-- info: 'STACS2027.gridWheelFamily_literal_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridWheelFamily_literal_bound

/-- info: 'STACS2027.gridWheelFamily_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridWheelFamily_contains

/-- info: 'STACS2027.gridWheelFamily_variableBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridWheelFamily_variableBound

/-- info: 'STACS2027.gridBoundedFormula_variableBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridBoundedFormula_variableBound

/-- info: 'STACS2027.gridWheelFamily_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridWheelFamily_distinct

/-- info: 'STACS2027.sourceCopies_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceCopies_distinct

/-- info: 'STACS2027.gridBoundedFormula_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridBoundedFormula_distinct

/-- info: 'STACS2027.gridBoundedFormula_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridBoundedFormula_perm

/-- info: 'STACS2027.gridBoundedFormula_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridBoundedFormula_bounded

/-- info: 'STACS2027.gridBoundedFormula_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridBoundedFormula_satisfiable

/-- info: 'STACS2027.gridPair' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridPair

/-- info: 'STACS2027.gridSegment' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridSegment

/-- info: 'STACS2027.sourceGrid_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceGrid_chain

/-- info: 'STACS2027.sourceWheel_gridFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sourceWheel_gridFrom

/-- info: 'STACS2027.gridAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridAt

/-- info: 'STACS2027.gridSegment_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridSegment_range

/-- info: 'STACS2027.gridWheelRows' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridWheelRows

/-- info: 'STACS2027.gridWheelRows_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridWheelRows_perm

/-- info: 'STACS2027.gridWheelFamily' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridWheelFamily

/-- info: 'STACS2027.gridWheelFamily_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridWheelFamily_perm

/-- info: 'STACS2027.gridPairExpr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridPairExpr

/-- info: 'STACS2027.gridPairExpr_emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gridPairExpr_emit

/-- info: 'STACS2027.gridWheelProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.gridWheelProgram

/-- info: 'STACS2027.gridWheelProgram_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridWheelProgram_emit

/-- info: 'STACS2027.LinearPreprocessExtract.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessExtract.State

/-- info: 'STACS2027.LinearPreprocessExtract.step' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessExtract.step

/-- info: 'STACS2027.LinearPreprocessExtract.Executes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessExtract.Executes

/-- info: 'STACS2027.LinearPreprocessExtract.Executes.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessExtract.Executes.trans

/-- info: 'STACS2027.LinearPreprocessExtract.run_scan' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessExtract.run_scan

/-- info: 'STACS2027.LinearPreprocessExtract.run_reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessExtract.run_reverse

/-- info: 'STACS2027.LinearPreprocessExtract.executes_contents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessExtract.executes_contents

/-- info: 'STACS2027.LinearPreprocessExtract.extraction_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessExtract.extraction_linear

/-- info: 'STACS2027.LinearPreprocessInit.push' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.push

/-- info: 'STACS2027.LinearPreprocessInit.addClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.addClause

/-- info: 'STACS2027.LinearPreprocessInit.addClause_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.addClause_length

/-- info: 'STACS2027.LinearPreprocessInit.addClause_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.addClause_mem

/-- info: 'STACS2027.LinearPreprocessInit.buildTables' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.buildTables

/-- info: 'STACS2027.LinearPreprocessInit.initialize_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.initialize_memory

/-- info: 'STACS2027.LinearPreprocessInit.initialize_adj_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.initialize_adj_mono

/-- info: 'STACS2027.LinearPreprocessInit.initialize_adj_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.initialize_adj_length

/-- info: 'STACS2027.LinearPreprocessInit.initialize_adj_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.initialize_adj_ids

/-- info: 'STACS2027.LinearPreprocessInit.initialize_adj_occurrence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.initialize_adj_occurrence

/-- info: 'STACS2027.LinearPreprocessInit.initialMemory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.initialMemory

/-- info: 'STACS2027.LinearPreprocessInit.initialAdj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.initialAdj

/-- info: 'STACS2027.LinearPreprocessInit.initialMemory_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.initialMemory_eq

/-- info: 'STACS2027.LinearPreprocessInit.contents_initialMemory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.contents_initialMemory

/-- info: 'STACS2027.LinearPreprocessInit.initial_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.initial_valid

/-- info: 'STACS2027.LinearPreprocessInit.initialAdj_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.initialAdj_valid

/-- info: 'STACS2027.LinearPreprocessInit.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.State

/-- info: 'STACS2027.LinearPreprocessInit.step' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.step

/-- info: 'STACS2027.LinearPreprocessInit.Executes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.Executes

/-- info: 'STACS2027.LinearPreprocessInit.Executes.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.Executes.trans

/-- info: 'STACS2027.LinearPreprocessInit.run_clause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.run_clause

/-- info: 'STACS2027.LinearPreprocessInit.run_scan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.run_scan

/-- info: 'STACS2027.LinearPreprocessInit.run_queue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.run_queue

/-- info: 'STACS2027.LinearPreprocessInit.executes_initialize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.executes_initialize

/-- info: 'STACS2027.LinearPreprocessInit.normalized_degree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.normalized_degree

/-- info: 'STACS2027.LinearPreprocessInit.normalized_initial_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessInit.normalized_initial_valid

/-- info: 'STACS2027.LinearPreprocessNormalize.opposite' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.opposite

/-- info: 'STACS2027.LinearPreprocessNormalize.opposite_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.opposite_self

/-- info: 'STACS2027.LinearPreprocessNormalize.opposite_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.opposite_comm

/-- info: 'STACS2027.LinearPreprocessNormalize.opposite_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.opposite_eq

/-- info: 'STACS2027.LinearPreprocessNormalize.smallTaut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.smallTaut

/-- info: 'STACS2027.LinearPreprocessNormalize.smallTaut_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.smallTaut_eq

/-- info: 'STACS2027.LinearPreprocessNormalize.pairDistinct' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.pairDistinct

/-- info: 'STACS2027.LinearPreprocessNormalize.smallDistinct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.smallDistinct

/-- info: 'STACS2027.LinearPreprocessNormalize.smallDistinct_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.smallDistinct_eq

/-- info: 'STACS2027.LinearPreprocessNormalize.normalizeOne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.normalizeOne

/-- info: 'STACS2027.LinearPreprocessNormalize.normalizeOne_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.normalizeOne_eq

/-- info: 'STACS2027.LinearPreprocessNormalize.normalizeClauses_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.normalizeClauses_cons

/-- info: 'STACS2027.LinearPreprocessNormalize.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.State

/-- info: 'STACS2027.LinearPreprocessNormalize.step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.step

/-- info: 'STACS2027.LinearPreprocessNormalize.Executes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.Executes

/-- info: 'STACS2027.LinearPreprocessNormalize.Executes.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.Executes.trans

/-- info: 'STACS2027.LinearPreprocessNormalize.run_scan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.run_scan

/-- info: 'STACS2027.LinearPreprocessNormalize.run_reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.run_reverse

/-- info: 'STACS2027.LinearPreprocessNormalize.executes_normalizeClauses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessNormalize.executes_normalizeClauses

/-- info: 'STACS2027.LinearPreprocessPadding.freshClauses' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.freshClauses

/-- info: 'STACS2027.LinearPreprocessPadding.freshClauses_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.freshClauses_length

/-- info: 'STACS2027.LinearPreprocessPadding.freshClauses_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.freshClauses_snoc

/-- info: 'STACS2027.LinearPreprocessPadding.padFormula_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.padFormula_eq

/-- info: 'STACS2027.LinearPreprocessPadding.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.State

/-- info: 'STACS2027.LinearPreprocessPadding.step' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.step

/-- info: 'STACS2027.LinearPreprocessPadding.Executes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.Executes

/-- info: 'STACS2027.LinearPreprocessPadding.Executes.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.Executes.trans

/-- info: 'STACS2027.LinearPreprocessPadding.run_clause' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.run_clause

/-- info: 'STACS2027.LinearPreprocessPadding.run_scan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.run_scan

/-- info: 'STACS2027.LinearPreprocessPadding.run_pad' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.run_pad

/-- info: 'STACS2027.LinearPreprocessPadding.run_reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.run_reverse

/-- info: 'STACS2027.LinearPreprocessPadding.transitionCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.transitionCount

/-- info: 'STACS2027.LinearPreprocessPadding.executes_padFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPadding.executes_padFormula

/-- info: 'STACS2027.LinearPreprocessPayload.ClauseBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.ClauseBound

/-- info: 'STACS2027.LinearPreprocessPayload.FormulaBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.FormulaBound

/-- info: 'STACS2027.LinearPreprocessPayload.IdsBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.IdsBound

/-- info: 'STACS2027.LinearPreprocessPayload.MemoryBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.MemoryBound

/-- info: 'STACS2027.LinearPreprocessPayload.AdjacencyBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.AdjacencyBound

/-- info: 'STACS2027.LinearPreprocessPayload.ClauseBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.ClauseBound.mono

/-- info: 'STACS2027.LinearPreprocessPayload.FormulaBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.FormulaBound.mono

/-- info: 'STACS2027.LinearPreprocessPayload.IdsBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.IdsBound.mono

/-- info: 'STACS2027.LinearPreprocessPayload.MemoryBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.MemoryBound.mono

/-- info: 'STACS2027.LinearPreprocessPayload.AdjacencyBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.AdjacencyBound.mono

/-- info: 'STACS2027.LinearPreprocessPayload.memory_write' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.memory_write

/-- info: 'STACS2027.LinearPreprocessPayload.updateAt_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.updateAt_bound

/-- info: 'STACS2027.LinearPreprocessPayload.updateIds_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.updateIds_bound

/-- info: 'STACS2027.LinearPreprocessPayload.UnitsStateBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.UnitsStateBound

/-- info: 'STACS2027.LinearPreprocessPayload.UnitsStateBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.UnitsStateBound.mono

/-- info: 'STACS2027.LinearPreprocessPayload.units_step_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.units_step_bound

/-- info: 'STACS2027.LinearPreprocessPayload.push_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.push_bound

/-- info: 'STACS2027.LinearPreprocessPayload.InitStateBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.InitStateBound

/-- info: 'STACS2027.LinearPreprocessPayload.InitStateBound.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.InitStateBound.mono

/-- info: 'STACS2027.LinearPreprocessPayload.init_step_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.init_step_bound

/-- info: 'STACS2027.LinearPreprocessPayload.init_start_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessPayload.init_start_bound

/-- info: 'STACS2027.LinearPreprocessResult.ResultSpec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessResult.ResultSpec

/-- info: 'STACS2027.LinearPreprocessResult.result_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessResult.result_correct

/-- info: 'STACS2027.LinearPreprocessResult.normalized_kernel_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessResult.normalized_kernel_correct

/-- info: 'STACS2027.LinearPreprocessUnitWork.CellsSmall' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.CellsSmall

/-- info: 'STACS2027.LinearPreprocessUnitWork.updateAt_small' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.updateAt_small

/-- info: 'STACS2027.LinearPreprocessUnitWork.cellLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.cellLength

/-- info: 'STACS2027.LinearPreprocessUnitWork.literalInspectionBound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.literalInspectionBound

/-- info: 'STACS2027.LinearPreprocessUnitWork.inspection_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.inspection_bound

/-- info: 'STACS2027.LinearPreprocessUnitWork.unit_work_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.unit_work_bounded

/-- info: 'STACS2027.LinearPreprocessUnitWork.Invariant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.Invariant

/-- info: 'STACS2027.LinearPreprocessUnitWork.step_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.step_invariant

/-- info: 'STACS2027.LinearPreprocessUnitWork.executes_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.executes_invariant

/-- info: 'STACS2027.LinearPreprocessUnitWork.reachable_unit_work' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.reachable_unit_work

/-- info: 'STACS2027.LinearPreprocessUnitWork.statePotential' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.statePotential

/-- info: 'STACS2027.LinearPreprocessUnitWork.step_potential_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.step_potential_le

/-- info: 'STACS2027.LinearPreprocessUnitWork.executes_potential_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.executes_potential_le

/-- info: 'STACS2027.LinearPreprocessUnitWork.normalized_reachable_queue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnitWork.normalized_reachable_queue

/-- info: 'STACS2027.LinearPreprocessUnits.Memory' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.Memory

/-- info: 'STACS2027.LinearPreprocessUnits.Incidences' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.Incidences

/-- info: 'STACS2027.LinearPreprocessUnits.write' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.write

/-- info: 'STACS2027.LinearPreprocessUnits.write_same' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.write_same

/-- info: 'STACS2027.LinearPreprocessUnits.write_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.write_other

/-- info: 'STACS2027.LinearPreprocessUnits.contents' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.contents

/-- info: 'STACS2027.LinearPreprocessUnits.mem_contents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.mem_contents

/-- info: 'STACS2027.LinearPreprocessUnits.simplifyCell' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.simplifyCell

/-- info: 'STACS2027.LinearPreprocessUnits.simplifyCell_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.simplifyCell_avoids

/-- info: 'STACS2027.LinearPreprocessUnits.simplifyCell_unchanged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.simplifyCell_unchanged

/-- info: 'STACS2027.LinearPreprocessUnits.simplifyCell_idempotent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.simplifyCell_idempotent

/-- info: 'STACS2027.LinearPreprocessUnits.simplifyCell_deletion' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.simplifyCell_deletion

/-- info: 'STACS2027.LinearPreprocessUnits.short' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.short

/-- info: 'STACS2027.LinearPreprocessUnits.updateAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.updateAt

/-- info: 'STACS2027.LinearPreprocessUnits.updateIds' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.updateIds

/-- info: 'STACS2027.LinearPreprocessUnits.updateIds_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.updateIds_memory

/-- info: 'STACS2027.LinearPreprocessUnits.updateIds_queue_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.updateIds_queue_bound

/-- info: 'STACS2027.LinearPreprocessUnits.Covers' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.Covers

/-- info: 'STACS2027.LinearPreprocessUnits.updateIds_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.updateIds_all

/-- info: 'STACS2027.LinearPreprocessUnits.contents_simplify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.contents_simplify

/-- info: 'STACS2027.LinearPreprocessUnits.contents_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.contents_update

/-- info: 'STACS2027.LinearPreprocessUnits.update_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.update_cover

/-- info: 'STACS2027.LinearPreprocessUnits.Complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.Complete

/-- info: 'STACS2027.LinearPreprocessUnits.CompleteExcept' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.CompleteExcept

/-- info: 'STACS2027.LinearPreprocessUnits.updateAt_completeExcept' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.updateAt_completeExcept

/-- info: 'STACS2027.LinearPreprocessUnits.updateIds_completeExcept' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.updateIds_completeExcept

/-- info: 'STACS2027.LinearPreprocessUnits.updateIds_ids_below' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.updateIds_ids_below

/-- info: 'STACS2027.LinearPreprocessUnits.Valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.Valid

/-- info: 'STACS2027.LinearPreprocessUnits.AdjacencyValid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.AdjacencyValid

/-- info: 'STACS2027.LinearPreprocessUnits.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.State

/-- info: 'STACS2027.LinearPreprocessUnits.step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.step

/-- info: 'STACS2027.LinearPreprocessUnits.Executes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.Executes

/-- info: 'STACS2027.LinearPreprocessUnits.potential' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.potential

/-- info: 'STACS2027.LinearPreprocessUnits.Valid.pop_inactive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.Valid.pop_inactive

/-- info: 'STACS2027.LinearPreprocessUnits.Valid.pop_unit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.Valid.pop_unit

/-- info: 'STACS2027.LinearPreprocessUnits.unit_potential_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.unit_potential_decreases

/-- info: 'STACS2027.LinearPreprocessUnits.completed_clause_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.completed_clause_lower

/-- info: 'STACS2027.LinearPreprocessUnits.TerminalSpec' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.TerminalSpec

/-- info: 'STACS2027.LinearPreprocessUnits.terminalSpec_deletion' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.terminalSpec_deletion

/-- info: 'STACS2027.LinearPreprocessUnits.executes_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.executes_terminal

/-- info: 'STACS2027.LinearPreprocessUnits.kernel_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LinearPreprocessUnits.kernel_linear

/-- info: 'STACS2027.load' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.load

/-- info: 'STACS2027.pairCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pairCount

/-- info: 'STACS2027.two_mul_pairCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.two_mul_pairCount

/-- info: 'STACS2027.pairCount_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairCount_eq

/-- info: 'STACS2027.sum_map_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_add

/-- info: 'STACS2027.sum_map_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sum_map_zero

/-- info: 'STACS2027.sum_map_const' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sum_map_const

/-- info: 'STACS2027.sum_map_swap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_swap

/-- info: 'STACS2027.load_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.load_cons

/-- info: 'STACS2027.overlap_family' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_family

/-- info: 'STACS2027.sum_indicator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_indicator

/-- info: 'STACS2027.sum_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_counts

/-- info: 'STACS2027.pairCount_add_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairCount_add_bit

/-- info: 'STACS2027.cost_eq_load_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_eq_load_sum

/-- info: 'STACS2027.cost_eq_binomial_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_eq_binomial_sum

/-- info: 'STACS2027.chosenFamily' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.chosenFamily

/-- info: 'STACS2027.activeClausePorts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.activeClausePorts

/-- info: 'STACS2027.chosenFamily_supported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chosenFamily_supported

/-- info: 'STACS2027.clauseFamily_cost_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseFamily_cost_positive

/-- info: 'STACS2027.clauseFamily_blocked_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseFamily_blocked_lower

/-- info: 'STACS2027.image_choice_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.image_choice_function

/-- info: 'STACS2027.image_choice_for_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.image_choice_for_nodup

/-- info: 'STACS2027.variableFamily_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableFamily_state

/-- info: 'STACS2027.variableFamily_zero_normalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableFamily_zero_normalizes

/-- info: 'STACS2027.clauseTwoWitnessVertex6' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWitnessVertex6

/-- info: 'STACS2027.clauseTwoWitnessVertex6_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWitnessVertex6_valid

/-- info: 'STACS2027.clauseTwoWitnessVertex6_cost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWitnessVertex6_cost

/-- info: 'STACS2027.clauseTwoWitnessVertex6_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoWitnessVertex6_avoids

/-- info: 'STACS2027.clauseThreeFamily_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeFamily_witness

/-- info: 'STACS2027.clauseTwoFamily_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoFamily_witness

/-- info: 'STACS2027.clauseThreeGraph5_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.clauseThreeGraph5_eq

/-- info: 'STACS2027.clauseThree5_assignment_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_assignment_one

/-- info: 'STACS2027.clauseThree5_no_assignment_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_no_assignment_zero

/-- info: 'STACS2027.clauseTwo5_assignment_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_assignment_one

/-- info: 'STACS2027.clauseTwo5_no_assignment_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_no_assignment_zero

/-- info: 'STACS2027.clauseTwo6_assignment_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_assignment_one

/-- info: 'STACS2027.clauseTwo6_no_assignment_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_no_assignment_zero

/-- info: 'STACS2027.LocatedClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LocatedClause

/-- info: 'STACS2027.locatedGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.locatedGraph

/-- info: 'STACS2027.locatedTag' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.locatedTag

/-- info: 'STACS2027.locatedTag_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.locatedTag_injective

/-- info: 'STACS2027.locatedGraph_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.locatedGraph_perm

/-- info: 'STACS2027.locatedGraph_sat_iff_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.locatedGraph_sat_iff_assignment

/-- info: 'STACS2027.locateClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.locateClause

/-- info: 'STACS2027.locateCopyClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.locateCopyClause

/-- info: 'STACS2027.gridLocated' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.gridLocated

/-- info: 'STACS2027.gridLocated_placement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridLocated_placement

/-- info: 'STACS2027.gridLocated_tags_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gridLocated_tags_nodup

/-- info: 'STACS2027.mapped_choice_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapped_choice_pullback

/-- info: 'STACS2027.mapped_choice_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapped_choice_cost

/-- info: 'STACS2027.load_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_relabel

/-- info: 'STACS2027.placedClauseFamily_cost_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedClauseFamily_cost_positive

/-- info: 'STACS2027.mapIdx_eq_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapIdx_eq_range

/-- info: 'STACS2027.variableChosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableChosen

/-- info: 'STACS2027.clauseChosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseChosen

/-- info: 'STACS2027.clauseChosen_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseChosen_at

/-- info: 'STACS2027.formulaFamily_choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaFamily_choices

/-- info: 'STACS2027.formulaFamily_variable_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaFamily_variable_mem

/-- info: 'STACS2027.formulaFamily_clause_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaFamily_clause_mem

/-- info: 'STACS2027.formulaFamily_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaFamily_budget

/-- info: 'STACS2027.PlacedLiteral' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlacedLiteral

/-- info: 'STACS2027.placeLiterals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.placeLiterals

/-- info: 'STACS2027.placeFormula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.placeFormula

/-- info: 'STACS2027.PlacedLiteral.port' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlacedLiteral.port

/-- info: 'STACS2027.PlacedLiteral.key' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlacedLiteral.key

/-- info: 'STACS2027.placeLiterals_forget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.placeLiterals_forget

/-- info: 'STACS2027.placeLiterals_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.placeLiterals_append

/-- info: 'STACS2027.placeFormula_flatten' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.placeFormula_flatten

/-- info: 'STACS2027.placeFormula_forget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.placeFormula_forget

/-- info: 'STACS2027.placeLiterals_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placeLiterals_bounds

/-- info: 'STACS2027.placeLiterals_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placeLiterals_nodup

/-- info: 'STACS2027.occurrences_eq_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_eq_count

/-- info: 'STACS2027.BoundedOccurrence.placement_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.placement_bounds

/-- info: 'STACS2027.BoundedOccurrence.placement_port_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.placement_port_lt

/-- info: 'STACS2027.BoundedOccurrence.placement_key_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.placement_key_injective

/-- info: 'STACS2027.BoundedOccurrence.placement_keys_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedOccurrence.placement_keys_nodup

/-- info: 'STACS2027.avoidsVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.avoidsVertex

/-- info: 'STACS2027.selectedAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.selectedAt

/-- info: 'STACS2027.avoidsVertex_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.avoidsVertex_edge

/-- info: 'STACS2027.pathEdges_avoid_vertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_avoid_vertex

/-- info: 'STACS2027.selectedAt_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selectedAt_head

/-- info: 'STACS2027.SameCycle.selectedAt_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SameCycle.selectedAt_perm

/-- info: 'STACS2027.selected_at_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selected_at_split

/-- info: 'STACS2027.selected_perm_selectedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selected_perm_selectedAt

/-- info: 'STACS2027.selectedAt_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selectedAt_nodup

/-- info: 'STACS2027.selectedAt_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selectedAt_mem

/-- info: 'STACS2027.selectedAt_has_option' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selectedAt_has_option

/-- info: 'STACS2027.selected_option_has_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.selected_option_has_vertex

/-- info: 'STACS2027.Oriented.variable_clause_vertex_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.variable_clause_vertex_intersection

/-- info: 'STACS2027.Oriented.formulaGraph_shared_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_shared_edge

/-- info: 'STACS2027.Oriented.clause_single_variable_port' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clause_single_variable_port

/-- info: 'STACS2027.Oriented.formulaGraph_clause_induced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_clause_induced

/-- info: 'STACS2027.Oriented.PrivateClauseVertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.PrivateClauseVertex

/-- info: 'STACS2027.Oriented.private_clause_neighbor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.private_clause_neighbor

/-- info: 'STACS2027.Oriented.clause_excursion_one_variable_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clause_excursion_one_variable_bound

/-- info: 'STACS2027.Oriented.indexedFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.indexedFamily

/-- info: 'STACS2027.Oriented.formulaFamily_indexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaFamily_indexed

/-- info: 'STACS2027.Oriented.indexedFamily_clause_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.indexedFamily_clause_at

/-- info: 'STACS2027.Oriented.formulaGraph_satisfied_crossCost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_satisfied_crossCost_zero

/-- info: 'STACS2027.Oriented.clause_excursion_start_variable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clause_excursion_start_variable

/-- info: 'STACS2027.Oriented.clause_excursion_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clause_excursion_length

/-- info: 'STACS2027.Oriented.formulaGraph_cycle_private_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_cycle_private_clause

/-- info: 'STACS2027.Oriented.clauseRegion_port' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clauseRegion_port

/-- info: 'STACS2027.Oriented.formulaGraph_variable_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_variable_boundary

/-- info: 'STACS2027.Oriented.formulaGraph_variable_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_variable_path

/-- info: 'STACS2027.Oriented.clause_exit_variable_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clause_exit_variable_distance

/-- info: 'STACS2027.Oriented.formulaGraph_sat_implies_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_sat_implies_assignment

/-- info: 'STACS2027.Oriented.formulaGraph_sat_iff_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_sat_iff_assignment

/-- info: 'STACS2027.Oriented.formulaGraph_cost_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_cost_decomposition

/-- info: 'STACS2027.Oriented.formulaGraph_budget_forces_zero_interaction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_budget_forces_zero_interaction

/-- info: 'STACS2027.Oriented.path_variable_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.path_variable_region

/-- info: 'STACS2027.Oriented.formulaGraph_cycle_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_cycle_local

/-- info: 'STACS2027.Oriented.variable_boundary_preserves_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.variable_boundary_preserves_clause

/-- info: 'STACS2027.Oriented.clause_excursion_crossing_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clause_excursion_crossing_bound

/-- info: 'STACS2027.Oriented.placedClauseFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.placedClauseFamily

/-- info: 'STACS2027.Oriented.formulaFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaFamily

/-- info: 'STACS2027.Oriented.placedClauseFamily_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.placedClauseFamily_valid

/-- info: 'STACS2027.Oriented.formulaFamily_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaFamily_valid

/-- info: 'STACS2027.Oriented.formulaFamily_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaFamily_complete

/-- info: 'STACS2027.Oriented.variable_clause_cycles_different' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.variable_clause_cycles_different

/-- info: 'STACS2027.Oriented.placedClauseFamily_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.placedClauseFamily_distinct

/-- info: 'STACS2027.Oriented.formulaFamily_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaFamily_distinct

/-- info: 'STACS2027.Oriented.formulaGraph_assignment_iff_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_assignment_iff_family

/-- info: 'STACS2027.Oriented.placedClauseGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Oriented.placedClauseGraph

/-- info: 'STACS2027.Oriented.formulaGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph

/-- info: 'STACS2027.Oriented.formulaGraph_variable_contains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_variable_contains

/-- info: 'STACS2027.Oriented.formulaGraph_clause_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_clause_contains

/-- info: 'STACS2027.Oriented.mapped_attachment_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.mapped_attachment_edge

/-- info: 'STACS2027.Oriented.clauseChosen_uses_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clauseChosen_uses_literal

/-- info: 'STACS2027.Oriented.formulaGraph_assignment_budget_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_assignment_budget_lower

/-- info: 'STACS2027.Oriented.globalReductionGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Oriented.globalReductionGraph

/-- info: 'STACS2027.Oriented.globalReduction_sat_iff_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.globalReduction_sat_iff_assignment

/-- info: 'STACS2027.Oriented.formulaGraph_clause_vertices_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_clause_vertices_disjoint

/-- info: 'STACS2027.Oriented.formulaGraph_clause_edges_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_clause_edges_disjoint

/-- info: 'STACS2027.Oriented.formulaGraph_assignment_implies_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_assignment_implies_sat

/-- info: 'STACS2027.Oriented.ClauseRegion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.ClauseRegion

/-- info: 'STACS2027.Oriented.ClauseRegion.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.ClauseRegion.unique

/-- info: 'STACS2027.Oriented.formulaGraph_edge_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_edge_cases

/-- info: 'STACS2027.Oriented.placedClauseGraph_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.placedClauseGraph_endpoints

/-- info: 'STACS2027.Oriented.regions_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.regions_intersection

/-- info: 'STACS2027.Oriented.clause_edge_between_variable_regions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clause_edge_between_variable_regions

/-- info: 'STACS2027.Oriented.formulaGraph_between_variables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaGraph_between_variables

/-- info: 'STACS2027.EndpointChoices' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.EndpointChoices

/-- info: 'STACS2027.orientedClauseVertex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseVertex

/-- info: 'STACS2027.orientedPlacedClauseGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedPlacedClauseGraph

/-- info: 'STACS2027.orientedFormulaGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedFormulaGraph

/-- info: 'STACS2027.orientedGlobalReductionGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedGlobalReductionGraph

/-- info: 'STACS2027.orientedClauseVertex_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseVertex_injective

/-- info: 'STACS2027.orientedFormulaGraph_cycle_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedFormulaGraph_cycle_local

/-- info: 'STACS2027.orientedFormulaGraph_sat_iff_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedFormulaGraph_sat_iff_assignment

/-- info: 'STACS2027.orientedGlobalReduction_sat_iff_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedGlobalReduction_sat_iff_assignment

/-- info: 'STACS2027.ChoiceNum' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ChoiceNum

/-- info: 'STACS2027.ChoiceNum.eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.ChoiceNum.eval

/-- info: 'STACS2027.ChoiceNum.plain' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ChoiceNum.plain

/-- info: 'STACS2027.edgeChoiceProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.edgeChoiceProgram

/-- info: 'STACS2027.edgeChoiceProgram_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edgeChoiceProgram_emit

/-- info: 'STACS2027.graphChoiceProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.graphChoiceProgram

/-- info: 'STACS2027.graphChoiceProgram_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.graphChoiceProgram_emit

/-- info: 'STACS2027.GraphLiteralExpr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.GraphLiteralExpr

/-- info: 'STACS2027.GraphLiteralExpr.eval' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.GraphLiteralExpr.eval

/-- info: 'STACS2027.clauseVertexChoice' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.clauseVertexChoice

/-- info: 'STACS2027.clauseVertexChoice_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseVertexChoice_eval

/-- info: 'STACS2027.orientedClauseGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseGraphProgram

/-- info: 'STACS2027.orientedClauseGraphProgram_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseGraphProgram_emit

/-- info: 'STACS2027.orientedClauseGraphRecords' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseGraphRecords

/-- info: 'STACS2027.orientedClauseGraphRecords_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseGraphRecords_output

/-- info: 'STACS2027.orientedClauseRecordsAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseRecordsAt

/-- info: 'STACS2027.orientedClauseGraphsAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseGraphsAt

/-- info: 'STACS2027.orientedClauseRecordsAt_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseRecordsAt_output

/-- info: 'STACS2027.orientedClauseRecordsAt_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseRecordsAt_append

/-- info: 'STACS2027.orientedClauseGraphsAt_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseGraphsAt_zero

/-- info: 'STACS2027.variableGraphRecords_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableGraphRecords_output

/-- info: 'STACS2027.orientedFormulaGraphRecords' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedFormulaGraphRecords

/-- info: 'STACS2027.orientedFormulaGraphRecords_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedFormulaGraphRecords_output

/-- info: 'STACS2027.Oriented.placedClauseFamily_cost_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.placedClauseFamily_cost_positive

/-- info: 'STACS2027.Oriented.clauseChosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clauseChosen

/-- info: 'STACS2027.Oriented.clauseChosen_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clauseChosen_at

/-- info: 'STACS2027.Oriented.formulaFamily_choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaFamily_choices

/-- info: 'STACS2027.Oriented.formulaFamily_variable_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaFamily_variable_mem

/-- info: 'STACS2027.Oriented.formulaFamily_clause_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaFamily_clause_mem

/-- info: 'STACS2027.Oriented.formulaFamily_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.formulaFamily_budget

/-- info: 'STACS2027.Oriented.placedClause_sat_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.placedClause_sat_witness

/-- info: 'STACS2027.Oriented.orientSide' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Oriented.orientSide

/-- info: 'STACS2027.Oriented.orientSide_involutive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Oriented.orientSide_involutive

/-- info: 'STACS2027.Oriented.orientSide_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Oriented.orientSide_injective

/-- info: 'STACS2027.Oriented.clauseVertex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clauseVertex

/-- info: 'STACS2027.Oriented.clauseVertex_attachment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clauseVertex_attachment

/-- info: 'STACS2027.Oriented.clauseVertex_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Oriented.clauseVertex_injective

/-- info: 'STACS2027.Paper.trueEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.trueEdge

/-- info: 'STACS2027.Paper.falseEdge1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.falseEdge1

/-- info: 'STACS2027.Paper.falseEdge2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.falseEdge2

/-- info: 'STACS2027.Paper.sharedEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.sharedEdge

/-- info: 'STACS2027.Paper.alphaCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.alphaCycle

/-- info: 'STACS2027.Paper.betaCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.betaCycle

/-- info: 'STACS2027.Paper.outerCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.outerCycle

/-- info: 'STACS2027.Paper.variablePathLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.variablePathLength

/-- info: 'STACS2027.Paper.variablePorts_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.variablePorts_eq

/-- info: 'STACS2027.Paper.step1_skeleton_cycles' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step1_skeleton_cycles

/-- info: 'STACS2027.Paper.step1_incidences' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step1_incidences

/-- info: 'STACS2027.Paper.step1_lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step1_lengths

/-- info: 'STACS2027.Paper.step1_cycle_lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step1_cycle_lengths

/-- info: 'STACS2027.Paper.step1_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step1_cycles

/-- info: 'STACS2027.Paper.step1_k_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step1_k_cycles

/-- info: 'STACS2027.Paper.observation_o1_2_variable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.observation_o1_2_variable

/-- info: 'STACS2027.Paper.step1_truth_states' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step1_truth_states

/-- info: 'STACS2027.Paper.step2Edges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step2Edges

/-- info: 'STACS2027.Paper.step2LiteralEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step2LiteralEdges

/-- info: 'STACS2027.Paper.step2Green' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step2Green

/-- info: 'STACS2027.Paper.step3Edges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step3Edges

/-- info: 'STACS2027.Paper.step3Green' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step3Green

/-- info: 'STACS2027.Paper.step3Orange' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step3Orange

/-- info: 'STACS2027.Paper.step3Blue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step3Blue

/-- info: 'STACS2027.Paper.step3Red' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step3Red

/-- info: 'STACS2027.Paper.step2Subdivisions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step2Subdivisions

/-- info: 'STACS2027.Paper.step3Subdivisions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step3Subdivisions

/-- info: 'STACS2027.Paper.step2_k5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step2_k5

/-- info: 'STACS2027.Paper.step3_k5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step3_k5

/-- info: 'STACS2027.Paper.step2_links' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step2_links

/-- info: 'STACS2027.Paper.step3_links' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step3_links

/-- info: 'STACS2027.Paper.step2_literal_edges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step2_literal_edges

/-- info: 'STACS2027.Paper.clause_slot_edges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Paper.clause_slot_edges

/-- info: 'STACS2027.Paper.clause_gadget_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.clause_gadget_observations

/-- info: 'STACS2027.Paper.clause_gadget_optima' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.clause_gadget_optima

/-- info: 'STACS2027.Paper.gadgets_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadgets_planar

/-- info: 'STACS2027.Paper.step4_port_edges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step4_port_edges

/-- info: 'STACS2027.Paper.step4_variable_port' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.step4_variable_port

/-- info: 'STACS2027.Paper.step4_identification' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.step4_identification

/-- info: 'STACS2027.Paper.cpap_objective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.cpap_objective

/-- info: 'STACS2027.Paper.LeOneLeTwoCNF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.LeOneLeTwoCNF

/-- info: 'STACS2027.Paper.PlanarLeOneLeTwoCNF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Paper.PlanarLeOneLeTwoCNF

/-- info: 'STACS2027.Paper.leOneLeTwoCNF_iff_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.leOneLeTwoCNF_iff_registered

/-- info: 'STACS2027.Paper.PlanarLeOneLeTwoLanguage' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Paper.PlanarLeOneLeTwoLanguage

/-- info: 'STACS2027.Paper.planarLeOneLeTwoLanguage_encode_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.planarLeOneLeTwoLanguage_encode_iff

/-- info: 'STACS2027.Paper.planarLeOneLeTwoCNF_np_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.planarLeOneLeTwoCNF_np_hard

/-- info: 'STACS2027.Paper.gadget_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction

/-- info: 'STACS2027.Paper.gadget_reduction_any_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction_any_endpoints

/-- info: 'STACS2027.Paper.gadget_reduction_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction_planar

/-- info: 'STACS2027.Paper.gadget_reduction_full_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction_full_domain

/-- info: 'STACS2027.Paper.gadget_reduction_full_domain_any_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction_full_domain_any_endpoints

/-- info: 'STACS2027.Paper.gadget_reduction_full_domain_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction_full_domain_size

/-- info: 'STACS2027.Paper.gadget_reduction_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction_size

/-- info: 'STACS2027.Paper.gadget_reduction_linear_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction_linear_time

/-- info: 'STACS2027.Paper.gadget_reduction_unit_steps_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction_unit_steps_bounded

/-- info: 'STACS2027.Paper.gadget_reduction_planar_linear_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction_planar_linear_time

/-- info: 'STACS2027.Paper.observation_o1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.observation_o1

/-- info: 'STACS2027.Paper.observation_o1_any_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.observation_o1_any_endpoints

/-- info: 'STACS2027.Paper.fixed_endpoints_K33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.fixed_endpoints_K33

/-- info: 'STACS2027.Paper.planar_np_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.planar_np_hard

/-- info: 'STACS2027.Paper.general_np_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.general_np_hard

/-- info: 'STACS2027.Paper.planar_source_np_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.planar_source_np_complete

/-- info: 'STACS2027.subdivideOnce_path_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_path_projection

/-- info: 'STACS2027.subdivision_path_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivision_path_projection

/-- info: 'STACS2027.chainSteps_fresh_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chainSteps_fresh_bound

/-- info: 'STACS2027.linkSteps_fresh_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.linkSteps_fresh_bound

/-- info: 'STACS2027.realizeLinks_path_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_path_projection

/-- info: 'STACS2027.pathWeight' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pathWeight

/-- info: 'STACS2027.pathWeight_endpoint_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathWeight_endpoint_bound

/-- info: 'STACS2027.edge_normalized' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.edge_normalized

/-- info: 'STACS2027.subdividedEdge_normalized' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.subdividedEdge_normalized

/-- info: 'STACS2027.realizeLinks_normalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_normalized

/-- info: 'STACS2027.mapGraph_pullback_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapGraph_pullback_edge

/-- info: 'STACS2027.pathEdges_normalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_normalized

/-- info: 'STACS2027.IsSimplePath.map_into' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsSimplePath.map_into

/-- info: 'STACS2027.blockVertex_mod' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.blockVertex_mod

/-- info: 'STACS2027.variable_path_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_path_pullback

/-- info: 'STACS2027.pathEdges_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_suffix

/-- info: 'STACS2027.pathEdges_infix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_infix

/-- info: 'STACS2027.IsSimplePath.infix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsSimplePath.infix

/-- info: 'STACS2027.IsSimplePath.reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsSimplePath.reverse

/-- info: 'STACS2027.list_first_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.list_first_exit

/-- info: 'STACS2027.mapped_choice_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapped_choice_push

/-- info: 'STACS2027.placedVariable_sat_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedVariable_sat_witness

/-- info: 'STACS2027.placedClause_sat_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.placedClause_sat_witness

/-- info: 'STACS2027.PlanarAssembly.BoundaryRouting' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.BoundaryRouting

/-- info: 'STACS2027.PlanarAssembly.BoundaryRouting.interiorRoot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.BoundaryRouting.interiorRoot

/-- info: 'STACS2027.PlanarAssembly.BoundaryRouting.interiorFaceCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.BoundaryRouting.interiorFaceCount

/-- info: 'STACS2027.PlanarAssembly.BoundaryRouting.faceLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.BoundaryRouting.faceLabel

/-- info: 'STACS2027.PlanarAssembly.BoundaryRouting.faceLabel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.BoundaryRouting.faceLabel_step

/-- info: 'STACS2027.PlanarAssembly.BoundaryRouting.tagged_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.BoundaryRouting.tagged_nodup

/-- info: 'STACS2027.PlanarAssembly.BoundaryRouting.tags_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.BoundaryRouting.tags_disjoint

/-- info: 'STACS2027.PlanarAssembly.BoundaryRouting.face_count_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.BoundaryRouting.face_count_lower_bound

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.HasSourceOrders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.HasSourceOrders

/-- info: 'STACS2027.PlanarAssembly.chosenPieces_with_source_orders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.chosenPieces_with_source_orders

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.pieceSourceOrders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.pieceSourceOrders

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.orderedPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.orderedPorts

/-- info: 'STACS2027.PlanarAssembly.EmbeddingPorts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.EmbeddingPorts

/-- info: 'STACS2027.PlanarAssembly.clauseIndexOfPiece' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseIndexOfPiece

/-- info: 'STACS2027.PlanarAssembly.piecePorts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecePorts

/-- info: 'STACS2027.PlanarAssembly.piecePorts_variable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecePorts_variable

/-- info: 'STACS2027.PlanarAssembly.piecePorts_clause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecePorts_clause

/-- info: 'STACS2027.PlanarAssembly.piece_variable_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_variable_eq

/-- info: 'STACS2027.PlanarAssembly.piece_clause_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_clause_eq

/-- info: 'STACS2027.PlanarAssembly.piecePorts_spherical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecePorts_spherical

/-- info: 'STACS2027.PlanarAssembly.piecePorts_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecePorts_nodup

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.maps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.maps

/-- info: 'STACS2027.PlanarAssembly.variablePortIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variablePortIndex

/-- info: 'STACS2027.PlanarAssembly.clausePortIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clausePortIndex

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.choices

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.variable_global_port' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.variable_global_port

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.clause_global_port' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.clause_global_port

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.spherical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.spherical

/-- info: 'STACS2027.PlanarAssembly.blockGraph_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.blockGraph_end

/-- info: 'STACS2027.PlanarAssembly.piece_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_end

/-- info: 'STACS2027.PlanarAssembly.formulaPieces_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.formulaPieces_disjoint

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.embedding

/-- info: 'STACS2027.PlanarAssembly.piecePortIndex_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecePortIndex_injective

/-- info: 'STACS2027.PlanarAssembly.orientedFormulaGraph_planar_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.orientedFormulaGraph_planar_exists

/-- info: 'STACS2027.PlanarAssembly.Connected' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.Connected

/-- info: 'STACS2027.PlanarAssembly.Connected.refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.Connected.refl

/-- info: 'STACS2027.PlanarAssembly.Connected.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.Connected.trans

/-- info: 'STACS2027.PlanarAssembly.Connected.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.Connected.symm

/-- info: 'STACS2027.PlanarAssembly.Connected.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.Connected.step

/-- info: 'STACS2027.PlanarAssembly.Connected.of_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.Connected.of_node

/-- info: 'STACS2027.PlanarAssembly.Connected.of_face' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.Connected.of_face

/-- info: 'STACS2027.PlanarAssembly.connected_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.connected_simulation

/-- info: 'STACS2027.PlanarAssembly.componentCount_le_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.componentCount_le_cover

/-- info: 'STACS2027.PlanarAssembly.PortPairing.connected_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.connected_transfer

/-- info: 'STACS2027.PlanarAssembly.PortPairing.connected_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.connected_pair

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.local_node_connected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.local_node_connected

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.source_connected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.source_connected

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.component_count_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.component_count_bound

/-- info: 'STACS2027.PlanarAssembly.faceInverse' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.faceInverse

/-- info: 'STACS2027.PlanarAssembly.face_faceInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.face_faceInverse

/-- info: 'STACS2027.PlanarAssembly.faceInverse_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.faceInverse_face

/-- info: 'STACS2027.PlanarAssembly.PortPairing' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing

/-- info: 'STACS2027.PlanarAssembly.PortPairing.switch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.switch

/-- info: 'STACS2027.PlanarAssembly.PortPairing.switch_marked' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.switch_marked

/-- info: 'STACS2027.PlanarAssembly.PortPairing.switch_face_marked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.switch_face_marked

/-- info: 'STACS2027.PlanarAssembly.PortPairing.switch_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.switch_involutive

/-- info: 'STACS2027.PlanarAssembly.PortPairing.assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.assembled

/-- info: 'STACS2027.PlanarAssembly.PortPairing.assembled_face_marked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.assembled_face_marked

/-- info: 'STACS2027.PlanarAssembly.PortPairing.assembled_face_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.assembled_face_unmarked

/-- info: 'STACS2027.PlanarAssembly.PortPairing.assembled_face_preserves_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.assembled_face_preserves_marked

/-- info: 'STACS2027.PlanarAssembly.PortPairing.node_face_eq_edge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.node_face_eq_edge

/-- info: 'STACS2027.PlanarAssembly.PortPairing.switch_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.switch_end

/-- info: 'STACS2027.PlanarAssembly.PortPairing.assembled_node_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.assembled_node_end

/-- info: 'STACS2027.PlanarAssembly.portEndpoint' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.portEndpoint

/-- info: 'STACS2027.PlanarAssembly.DisjointPortEndpoints' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.DisjointPortEndpoints

/-- info: 'STACS2027.PlanarAssembly.face_endpoint' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.face_endpoint

/-- info: 'STACS2027.PlanarAssembly.face_marked_false' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.face_marked_false

/-- info: 'STACS2027.PlanarAssembly.PortPairing.active_dart_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.active_dart_rep

/-- info: 'STACS2027.PlanarAssembly.PortPairing.disjoint_node_switches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.disjoint_node_switches

/-- info: 'STACS2027.PlanarAssembly.PortPairing.MatchedEndpointFibers' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.MatchedEndpointFibers

/-- info: 'STACS2027.PlanarAssembly.PortPairing.endpoint_fibers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.endpoint_fibers

/-- info: 'STACS2027.PlanarAssembly.involution_cycles_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.involution_cycles_twice

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.marked_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.marked_count

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.source_edge_no_fixed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.source_edge_no_fixed

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.digon_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.digon_count

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.assembled_planar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.assembled_planar

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.source_node_step_face' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.source_node_step_face

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.source_node_face' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.source_node_face

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.noninterior_has_port' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.noninterior_has_port

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.consumed_faces_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.consumed_faces_le

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.interior_face_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.interior_face_loss

/-- info: 'STACS2027.PlanarAssembly.PortPairing.pair_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.pair_injective

/-- info: 'STACS2027.PlanarAssembly.PortPairing.iterate_marked_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.iterate_marked_cases

/-- info: 'STACS2027.PlanarAssembly.PortPairing.marked_cycleMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.marked_cycleMin

/-- info: 'STACS2027.PlanarAssembly.PortPairing.digonRoot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.digonRoot

/-- info: 'STACS2027.PlanarAssembly.PortPairing.digonCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.digonCount

/-- info: 'STACS2027.PlanarAssembly.PortPairing.marked_cycleMin_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.marked_cycleMin_eq

/-- info: 'STACS2027.PlanarAssembly.PortPairing.countP_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.countP_split

/-- info: 'STACS2027.PlanarAssembly.PortPairing.digonCount_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.digonCount_twice

/-- info: 'STACS2027.PlanarAssembly.planar_mapGraph_of_rotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.planar_mapGraph_of_rotation

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.orientedFormulaGraph_planar_of_orderedPorts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.orientedFormulaGraph_planar_of_orderedPorts

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.Inactive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.Inactive

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.inactiveRoots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.inactiveRoots

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.mem_inactiveRoots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.mem_inactiveRoots

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.inactiveRoots_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.inactiveRoots_nodup

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.inactiveRoots_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.inactiveRoots_cover

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.SourceNodesSeparate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.SourceNodesSeparate

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.inactiveRoots_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.inactiveRoots_count

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.assembled_planar_of_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.assembled_planar_of_separation

/-- info: 'STACS2027.PlanarAssembly.placed_clause_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placed_clause_lengths

/-- info: 'STACS2027.PlanarAssembly.placed_occurrence_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placed_occurrence_count

/-- info: 'STACS2027.PlanarAssembly.occurrencePosition_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrencePosition_offset

/-- info: 'STACS2027.PlanarAssembly.occurrence_incidence_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrence_incidence_lookup

/-- info: 'STACS2027.PlanarAssembly.occurrenceVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrenceVertex

/-- info: 'STACS2027.PlanarAssembly.occurrence_incidence_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrence_incidence_end

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_connected_vertex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_connected_vertex

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_source_nodes_separate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_source_nodes_separate

/-- info: 'STACS2027.ungluedClauseGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ungluedClauseGraph

/-- info: 'STACS2027.ungluedFormulaGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ungluedFormulaGraph

/-- info: 'STACS2027.assemblyVertex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.assemblyVertex

/-- info: 'STACS2027.assemblyVertex_variable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assemblyVertex_variable

/-- info: 'STACS2027.assemblyVertex_clause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assemblyVertex_clause

/-- info: 'STACS2027.assemblyVertex_variableGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assemblyVertex_variableGraph

/-- info: 'STACS2027.assemblyVertex_clauseGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assemblyVertex_clauseGraph

/-- info: 'STACS2027.assemblyVertex_formulaGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assemblyVertex_formulaGraph

/-- info: 'STACS2027.AssemblyAttachment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.AssemblyAttachment

/-- info: 'STACS2027.assemblyVertex_variable_clause_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assemblyVertex_variable_clause_fiber

/-- info: 'STACS2027.assemblyVertex_clause_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assemblyVertex_clause_injective

/-- info: 'STACS2027.AssemblyAttachment.identified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.AssemblyAttachment.identified

/-- info: 'STACS2027.assemblyVertex_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assemblyVertex_fiber

/-- info: 'STACS2027.assembly_side_alignment' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.assembly_side_alignment

/-- info: 'STACS2027.clauseEndpoint_lt_gadgetWidth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseEndpoint_lt_gadgetWidth

/-- info: 'STACS2027.AssemblyAttachment.target_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.AssemblyAttachment.target_unique

/-- info: 'STACS2027.ungluedFormulaGraph_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.ungluedFormulaGraph_below

/-- info: 'STACS2027.ungluedFormulaPieces' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ungluedFormulaPieces

/-- info: 'STACS2027.ungluedFormulaPieces_flatten' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.ungluedFormulaPieces_flatten

/-- info: 'STACS2027.PlanarAssembly.pieceOffset' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceOffset

/-- info: 'STACS2027.PlanarAssembly.flatten_piece' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.flatten_piece

/-- info: 'STACS2027.PlanarAssembly.pieceOffset_end_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceOffset_end_le

/-- info: 'STACS2027.PlanarAssembly.pieceOffset_mono_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceOffset_mono_end

/-- info: 'STACS2027.PlanarAssembly.blockDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.blockDart

/-- info: 'STACS2027.PlanarAssembly.blockDart_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.blockDart_index

/-- info: 'STACS2027.PlanarAssembly.blockDart_side' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.blockDart_side

/-- info: 'STACS2027.PlanarAssembly.flatten_piece_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.flatten_piece_getElem?

/-- info: 'STACS2027.PlanarAssembly.blockDart_edge_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.blockDart_edge_lookup

/-- info: 'STACS2027.PlanarAssembly.blockDart_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.blockDart_end

/-- info: 'STACS2027.PlanarAssembly.blockDart_graphEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.blockDart_graphEdge

/-- info: 'STACS2027.PlanarAssembly.blockDart_block_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.blockDart_block_injective

/-- info: 'STACS2027.PlanarAssembly.blockDart_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.blockDart_injective

/-- info: 'STACS2027.PlanarAssembly.variablePieceIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variablePieceIndex

/-- info: 'STACS2027.PlanarAssembly.clausePieceIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clausePieceIndex

/-- info: 'STACS2027.PlanarAssembly.variablePiece_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variablePiece_eq

/-- info: 'STACS2027.PlanarAssembly.clausePiece_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clausePiece_eq

/-- info: 'STACS2027.PlanarAssembly.variableGlobalDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableGlobalDart

/-- info: 'STACS2027.PlanarAssembly.clauseGlobalDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseGlobalDart

/-- info: 'STACS2027.PlanarAssembly.variableGlobalDart_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableGlobalDart_lookup
