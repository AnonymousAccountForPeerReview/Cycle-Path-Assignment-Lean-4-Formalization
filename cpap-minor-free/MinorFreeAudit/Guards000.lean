module

public import MinorFree

/-!
Exact-message axiom guards for every explicitly named MinorFree declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

@[expose] public section

set_option maxRecDepth 100000

/-- info: 'STACS2027.biclique' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.biclique

/-- info: 'STACS2027.pairs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pairs

/-- info: 'STACS2027.canonicalCycles' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.canonicalCycles

/-- info: 'STACS2027.mem_biclique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_biclique

/-- info: 'STACS2027.biclique_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.biclique_length

/-- info: 'STACS2027.biclique_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.biclique_nodup

/-- info: 'STACS2027.edge_mem_biclique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_mem_biclique

/-- info: 'STACS2027.edge_zero_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_zero_mem

/-- info: 'STACS2027.edge_one_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_one_mem

/-- info: 'STACS2027.canonical_isCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.canonical_isCycle

/-- info: 'STACS2027.sameCycle_shapes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sameCycle_shapes

/-- info: 'STACS2027.biclique_cycle_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.biclique_cycle_shape

/-- info: 'STACS2027.mem_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_pairs

/-- info: 'STACS2027.pairs_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pairs_succ

/-- info: 'STACS2027.pairs_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pairs_length

/-- info: 'STACS2027.pairs_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairs_nodup

/-- info: 'STACS2027.canonical_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.canonical_injective

/-- info: 'STACS2027.canonical_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.canonical_pairwise

/-- info: 'STACS2027.canonical_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.canonical_cover

/-- info: 'STACS2027.canonical_isCycle'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.canonical_isCycle'

/-- info: 'STACS2027.biclique_cycles_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.biclique_cycles_perm

/-- info: 'STACS2027.biclique_cycle_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.biclique_cycle_count

/-- info: 'STACS2027.biclique_cost_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.biclique_cost_lower

/-- info: 'STACS2027.biclique_edge_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.biclique_edge_cycles

/-- info: 'STACS2027.biclique_cost_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.biclique_cost_upper

/-- info: 'STACS2027.BicliqueEmbedding.ed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.ed

/-- info: 'STACS2027.BicliqueEmbedding.nd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.nd

/-- info: 'STACS2027.BicliqueEmbedding.fc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.fc

/-- info: 'STACS2027.BicliqueEmbedding.ed_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.ed_eq

/-- info: 'STACS2027.BicliqueEmbedding.ed_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.ed_lt

/-- info: 'STACS2027.BicliqueEmbedding.nd_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.nd_lt

/-- info: 'STACS2027.BicliqueEmbedding.fc_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.fc_lt

/-- info: 'STACS2027.BicliqueEmbedding.nd_fc_ed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.nd_fc_ed

/-- info: 'STACS2027.BicliqueEmbedding.bicliqueMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.bicliqueMap

/-- info: 'STACS2027.BicliqueEmbedding.biclique_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.biclique_succ

/-- info: 'STACS2027.BicliqueEmbedding.biclique_getElem?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.biclique_getElem?

/-- info: 'STACS2027.BicliqueEmbedding.vert' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.vert

/-- info: 'STACS2027.BicliqueEmbedding.halfEdgeEnd_biclique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.halfEdgeEnd_biclique

/-- info: 'STACS2027.BicliqueEmbedding.vert_nd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.vert_nd

/-- info: 'STACS2027.BicliqueEmbedding.iterate_nd_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.iterate_nd_zero

/-- info: 'STACS2027.BicliqueEmbedding.iterate_nd_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.iterate_nd_one

/-- info: 'STACS2027.BicliqueEmbedding.reach_trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.reach_trans

/-- info: 'STACS2027.BicliqueEmbedding.reach_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.reach_zero

/-- info: 'STACS2027.BicliqueEmbedding.reach_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.reach_one

/-- info: 'STACS2027.BicliqueEmbedding.nd_reach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.nd_reach

/-- info: 'STACS2027.BicliqueEmbedding.iterate_node_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.iterate_node_val

/-- info: 'STACS2027.BicliqueEmbedding.iterate_nd_vert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.iterate_nd_vert

/-- info: 'STACS2027.BicliqueEmbedding.dartOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.dartOf

/-- info: 'STACS2027.BicliqueEmbedding.faceOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.faceOf

/-- info: 'STACS2027.BicliqueEmbedding.faceOf_fc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.faceOf_fc

/-- info: 'STACS2027.BicliqueEmbedding.countP_range_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.countP_range_eq_zero

/-- info: 'STACS2027.BicliqueEmbedding.bicliqueMap_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BicliqueEmbedding.bicliqueMap_planar

/-- info: 'STACS2027.biclique_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.biclique_planar

/-- info: 'STACS2027.biclique_planar_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.biclique_planar_family

/-- info: 'STACS2027.cycleEdges_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_nonempty

/-- info: 'STACS2027.hasAssignment_disjoint_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_disjoint_union

/-- info: 'STACS2027.EdgeDisjoint' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.EdgeDisjoint

/-- info: 'STACS2027.CyclesInBlocks' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.CyclesInBlocks

/-- info: 'STACS2027.mem_flatten_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_flatten_block

/-- info: 'STACS2027.hasAssignment_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_blocks

/-- info: 'STACS2027.OuterplanarOrK4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterplanarOrK4

/-- info: 'STACS2027.perfect_assignment_of_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.perfect_assignment_of_blocks

/-- info: 'STACS2027.EliminationOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.EliminationOrder

/-- info: 'STACS2027.CommonNeighbourBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.CommonNeighbourBound

/-- info: 'STACS2027.earliestIndex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.earliestIndex

/-- info: 'STACS2027.algorithm4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.algorithm4

/-- info: 'STACS2027.earliestIndex_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.earliestIndex_spec

/-- info: 'STACS2027.EarliestView' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.EarliestView

/-- info: 'STACS2027.earliestView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.earliestView

/-- info: 'STACS2027.algorithm4_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.algorithm4_disjoint

/-- info: 'STACS2027.algorithm4_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.algorithm4_valid

/-- info: 'STACS2027.algorithm4_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.algorithm4_cost

/-- info: 'STACS2027.algorithm4_perfect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.algorithm4_perfect

/-- info: 'STACS2027.perfect_four_cycle_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.perfect_four_cycle_assignment

/-- info: 'STACS2027.cost_eq_zero_of_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_eq_zero_of_pairwise

/-- info: 'STACS2027.overlap_eq_zero_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_eq_zero_of_disjoint

/-- info: 'STACS2027.overlap_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.overlap_eq_zero_iff

/-- info: 'STACS2027.four_cycle_rotation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.four_cycle_rotation

/-- info: 'STACS2027.cycleEdges_four' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_four

/-- info: 'STACS2027.mem_cycleEdges_four' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.mem_cycleEdges_four

/-- info: 'STACS2027.edge_has_endpoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_has_endpoint

/-- info: 'STACS2027.edge_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_avoids

/-- info: 'STACS2027.mem_selectedAt_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_selectedAt_four

/-- info: 'STACS2027.sameCycle_rotation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sameCycle_rotation

/-- info: 'STACS2027.IsCycle.rotation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.rotation

/-- info: 'STACS2027.nodup_four' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.nodup_four

/-- info: 'STACS2027.k4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.k4

/-- info: 'STACS2027.k4Assignment' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.k4Assignment

/-- info: 'STACS2027.k4Assignment_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k4Assignment_valid

/-- info: 'STACS2027.k4Assignment_cost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.k4Assignment_cost

/-- info: 'STACS2027.k4_perfect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k4_perfect

/-- info: 'STACS2027.k4_verticesBelow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.k4_verticesBelow

/-- info: 'STACS2027.k4_normalized' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.k4_normalized

/-- info: 'STACS2027.IsCycle.length_le_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.length_le_vertices

/-- info: 'STACS2027.k4_cycles_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k4_cycles_nil

/-- info: 'STACS2027.k4_perfect_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k4_perfect_large

/-- info: 'STACS2027.k4_cycle_assignments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k4_cycle_assignments

/-- info: 'STACS2027.IsK4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsK4

/-- info: 'STACS2027.IsK4.perfect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsK4.perfect

/-- info: 'STACS2027.IsK4.perfect_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsK4.perfect_large

/-- info: 'STACS2027.sum_map_add'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_add'

/-- info: 'STACS2027.sum_map_scale' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sum_map_scale

/-- info: 'STACS2027.sum_map_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_ext

/-- info: 'STACS2027.schwarz_two_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.schwarz_two_term

/-- info: 'STACS2027.schwarz_four_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.schwarz_four_term

/-- info: 'STACS2027.schwarz_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.schwarz_inequality

/-- info: 'STACS2027.sq_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sq_sum_le

/-- info: 'STACS2027.two_pairCount_add_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.two_pairCount_add_self

/-- info: 'STACS2027.sq_load_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sq_load_sum

/-- info: 'STACS2027.load_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_total

/-- info: 'STACS2027.assignment_total_load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.assignment_total_load

/-- info: 'STACS2027.cost_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_lower_bound

/-- info: 'STACS2027.load_le_cycle_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_le_cycle_count

/-- info: 'STACS2027.pairCount_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pairCount_mono

/-- info: 'STACS2027.cost_le_of_load_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_le_of_load_le

/-- info: 'STACS2027.Paper.algorithm4_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.algorithm4_path

/-- info: 'STACS2027.Paper.common_neighbours_hypothesis' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.common_neighbours_hypothesis

/-- info: 'STACS2027.Paper.outerplanar_algorithm4_perfect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.outerplanar_algorithm4_perfect

/-- info: 'STACS2027.Paper.outerplanar_algorithm4_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.outerplanar_algorithm4_disjoint

/-- info: 'STACS2027.Paper.k4_assignment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.k4_assignment

/-- info: 'STACS2027.Paper.k4_no_long_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.k4_no_long_cycles

/-- info: 'STACS2027.Paper.blockwise_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.blockwise_combination

/-- info: 'STACS2027.Paper.k23_perfect_of_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.k23_perfect_of_blocks

/-- info: 'STACS2027.Paper.total_load_general' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.total_load_general

/-- info: 'STACS2027.Paper.cauchy_schwarz_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.cauchy_schwarz_lower_bound

/-- info: 'STACS2027.Paper.biclique_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.biclique_counts

/-- info: 'STACS2027.Paper.biclique_edge_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.biclique_edge_count

/-- info: 'STACS2027.Paper.biclique_planar'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.biclique_planar'

/-- info: 'STACS2027.Paper.biclique_planar_family'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.biclique_planar_family'
