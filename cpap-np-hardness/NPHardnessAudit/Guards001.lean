module

import NPHardness

/-!
Exact-message axiom guards for every explicitly named NPHardness declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.PlanarAssembly.clauseGlobalDart_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseGlobalDart_lookup

/-- info: 'STACS2027.PlanarAssembly.variableGlobalDart_piece_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableGlobalDart_piece_injective

/-- info: 'STACS2027.PlanarAssembly.clauseGlobalDart_piece_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseGlobalDart_piece_injective

/-- info: 'STACS2027.PlanarAssembly.variableGlobalDart_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableGlobalDart_injective

/-- info: 'STACS2027.PlanarAssembly.clauseGlobalDart_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseGlobalDart_injective

/-- info: 'STACS2027.PlanarAssembly.variableGlobalDart_ne_clauseGlobalDart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableGlobalDart_ne_clauseGlobalDart

/-- info: 'STACS2027.PlanarAssembly.OccurrencePosition' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OccurrencePosition

/-- info: 'STACS2027.PlanarAssembly.occurrencePosition_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrencePosition_exists

/-- info: 'STACS2027.PlanarAssembly.occurrencePosition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrencePosition

/-- info: 'STACS2027.PlanarAssembly.placedOccurrences_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placedOccurrences_nodup

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices

/-- info: 'STACS2027.PlanarAssembly.NextSelected' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextSelected

/-- info: 'STACS2027.PlanarAssembly.nextSelected_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.nextSelected_exists

/-- info: 'STACS2027.PlanarAssembly.nextSelected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.nextSelected

/-- info: 'STACS2027.PlanarAssembly.nextSelected_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.nextSelected_spec

/-- info: 'STACS2027.PlanarAssembly.NextSelected.source_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextSelected.source_unique

/-- info: 'STACS2027.PlanarAssembly.nextSelected_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.nextSelected_injective

/-- info: 'STACS2027.PlanarAssembly.iterate_mod_return' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.iterate_mod_return

/-- info: 'STACS2027.PlanarAssembly.NextSelected.ne_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextSelected.ne_self

/-- info: 'STACS2027.PlanarAssembly.nextSelected_ne_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.nextSelected_ne_self

/-- info: 'STACS2027.PlanarAssembly.NextSelected.mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextSelected.mirror

/-- info: 'STACS2027.PlanarAssembly.cyclic_order_no_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.cyclic_order_no_fixed

/-- info: 'STACS2027.PlanarAssembly.nextSelected_small_order_or_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.nextSelected_small_order_or_mirror

/-- info: 'STACS2027.PlanarAssembly.spherical_cofacial_subset_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.spherical_cofacial_subset_ordered

/-- info: 'STACS2027.PlanarAssembly.NextSelected.to_nextPort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextSelected.to_nextPort

/-- info: 'STACS2027.PlanarAssembly.PortPairing.MarkedNode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.MarkedNode

/-- info: 'STACS2027.PlanarAssembly.PortPairing.marked_active' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.marked_active

/-- info: 'STACS2027.PlanarAssembly.PortPairing.switch_opposite_mark' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.switch_opposite_mark

/-- info: 'STACS2027.PlanarAssembly.PortPairing.markedNode_of_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.markedNode_of_reaches

/-- info: 'STACS2027.PlanarAssembly.PortPairing.markedNode_active_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.markedNode_active_iff

/-- info: 'STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel

/-- info: 'STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel_marked

/-- info: 'STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel_unmarked

/-- info: 'STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel_old_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel_old_step

/-- info: 'STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel_switch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel_switch

/-- info: 'STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.retainedNodeLabel_step

/-- info: 'STACS2027.PlanarAssembly.PortPairing.retainedNodeRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.retainedNodeRoot

/-- info: 'STACS2027.PlanarAssembly.PortPairing.retained_nodes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.retained_nodes_le

/-- info: 'STACS2027.PlanarAssembly.PortPairing.marked_nodes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.marked_nodes_le

/-- info: 'STACS2027.PlanarAssembly.PortPairing.node_count_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.node_count_loss

/-- info: 'STACS2027.PlanarAssembly.reaches_until_on_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.reaches_until_on_orbit

/-- info: 'STACS2027.PlanarAssembly.PortPairing.DisjointNodeSwitches' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.DisjointNodeSwitches

/-- info: 'STACS2027.PlanarAssembly.PortPairing.switch_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.switch_active

/-- info: 'STACS2027.PlanarAssembly.PortPairing.node_step_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.node_step_transfer

/-- info: 'STACS2027.PlanarAssembly.PortPairing.node_orbit_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.node_orbit_transfer

/-- info: 'STACS2027.PlanarAssembly.PortPairing.switch_node_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.switch_node_orbit

/-- info: 'STACS2027.PlanarAssembly.PortPairing.EndpointFibers' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.EndpointFibers

/-- info: 'STACS2027.PlanarAssembly.PortPairing.assembled_node_orbit_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PortPairing.assembled_node_orbit_iff

/-- info: 'STACS2027.PlanarAssembly.placed_clause_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placed_clause_length

/-- info: 'STACS2027.PlanarAssembly.occurrencePosition_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrencePosition_decode

/-- info: 'STACS2027.PlanarAssembly.occurrencePosition_at_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrencePosition_at_offset

/-- info: 'STACS2027.PlanarAssembly.odd_offset_port_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.odd_offset_port_data

/-- info: 'STACS2027.PlanarAssembly.OccurrenceIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OccurrenceIndex

/-- info: 'STACS2027.PlanarAssembly.occurrence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrence

/-- info: 'STACS2027.PlanarAssembly.occurrence_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrence_mem

/-- info: 'STACS2027.PlanarAssembly.occurrence_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrence_injective

/-- info: 'STACS2027.PlanarAssembly.occurrence_variable_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrence_variable_lt

/-- info: 'STACS2027.PlanarAssembly.occurrenceVariable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrenceVariable

/-- info: 'STACS2027.PlanarAssembly.occurrenceLocalPort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrenceLocalPort

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.variableOccurrencePort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.variableOccurrencePort

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.clauseOccurrencePort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.clauseOccurrencePort

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.variableOccurrencePort_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.variableOccurrencePort_injective

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.clause_global_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.clause_global_injective

/-- info: 'STACS2027.PlanarAssembly.occurrencePosition_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrencePosition_get

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.clauseOccurrencePort_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.clauseOccurrencePort_injective

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.variableOccurrencePort_ne_clauseOccurrencePort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.variableOccurrencePort_ne_clauseOccurrencePort

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.sourcePort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.sourcePort

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_injective

/-- info: 'STACS2027.PlanarAssembly.occurrenceDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrenceDart

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_even

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_odd

/-- info: 'STACS2027.PlanarAssembly.occurrenceDart_graphEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrenceDart_graphEdge

/-- info: 'STACS2027.PlanarAssembly.PieceSourceOrders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PieceSourceOrders

/-- info: 'STACS2027.PlanarAssembly.PieceSourceOrders.nextSelected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PieceSourceOrders.nextSelected

/-- info: 'STACS2027.PlanarAssembly.PieceSourceOrders.source_nextSelected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PieceSourceOrders.source_nextSelected

/-- info: 'STACS2027.PlanarAssembly.PieceSourceOrders.nextPort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PieceSourceOrders.nextPort

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.orderedFromPieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.orderedFromPieces

/-- info: 'STACS2027.PlanarAssembly.LocalMaps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalMaps

/-- info: 'STACS2027.PlanarAssembly.emptyMap' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.emptyMap

/-- info: 'STACS2027.PlanarAssembly.tailMaps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.tailMaps

/-- info: 'STACS2027.PlanarAssembly.sumCast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sumCast

/-- info: 'STACS2027.PlanarAssembly.piecesMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecesMap

/-- info: 'STACS2027.PlanarAssembly.sumCast_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sumCast_left

/-- info: 'STACS2027.PlanarAssembly.sumCast_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sumCast_right

/-- info: 'STACS2027.PlanarAssembly.MapField' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.MapField

/-- info: 'STACS2027.PlanarAssembly.MapField.read' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.MapField.read

/-- info: 'STACS2027.PlanarAssembly.field_transport' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.field_transport

/-- info: 'STACS2027.PlanarAssembly.field_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.field_left

/-- info: 'STACS2027.PlanarAssembly.field_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.field_right

/-- info: 'STACS2027.PlanarAssembly.piecesMap_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecesMap_field

/-- info: 'STACS2027.PlanarAssembly.piecesMap_iterate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecesMap_iterate

/-- info: 'STACS2027.PlanarAssembly.blockDart_surjective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.blockDart_surjective

/-- info: 'STACS2027.PlanarAssembly.piecesMap_spherical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecesMap_spherical

/-- info: 'STACS2027.PlanarAssembly.piecesMap_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecesMap_nodes

/-- info: 'STACS2027.PlanarAssembly.piecesMap_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecesMap_edges

/-- info: 'STACS2027.PlanarAssembly.piecesMap_embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecesMap_embedding

/-- info: 'STACS2027.PlanarAssembly.piecesMap_step_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecesMap_step_project

/-- info: 'STACS2027.PlanarAssembly.piecesMap_path_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecesMap_path_project

/-- info: 'STACS2027.PlanarAssembly.piecesMap_path_same_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecesMap_path_same_piece

/-- info: 'STACS2027.PlanarAssembly.variableOccurrenceEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableOccurrenceEnd

/-- info: 'STACS2027.PlanarAssembly.clauseOccurrenceEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseOccurrenceEnd

/-- info: 'STACS2027.PlanarAssembly.variableOccurrenceEnd_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableOccurrenceEnd_injective

/-- info: 'STACS2027.PlanarAssembly.occurrence_slot_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrence_slot_lt

/-- info: 'STACS2027.PlanarAssembly.clauseEndpoint_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseEndpoint_injective

/-- info: 'STACS2027.PlanarAssembly.occurrencePosition_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrencePosition_injective

/-- info: 'STACS2027.PlanarAssembly.clauseOccurrenceEnd_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseOccurrenceEnd_injective

/-- info: 'STACS2027.PlanarAssembly.variableOccurrenceEnd_ne_clauseOccurrenceEnd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableOccurrenceEnd_ne_clauseOccurrenceEnd

/-- info: 'STACS2027.PlanarAssembly.dartSide' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.dartSide

/-- info: 'STACS2027.PlanarAssembly.dartSide_graphEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.dartSide_graphEdge

/-- info: 'STACS2027.PlanarAssembly.graphEdge_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.graphEdge_index

/-- info: 'STACS2027.PlanarAssembly.halfEdgeEnd_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.halfEdgeEnd_lookup

/-- info: 'STACS2027.PlanarAssembly.mapEdge_variablePort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.mapEdge_variablePort

/-- info: 'STACS2027.PlanarAssembly.mapEdge_clausePort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.mapEdge_clausePort

/-- info: 'STACS2027.PlanarAssembly.atSide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.atSide

/-- info: 'STACS2027.PlanarAssembly.endpointSide' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.endpointSide

/-- info: 'STACS2027.PlanarAssembly.endpointSide_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.endpointSide_injective

/-- info: 'STACS2027.PlanarAssembly.halfEdgeEnd_atSide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.halfEdgeEnd_atSide

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.variableOccurrencePort_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.variableOccurrencePort_lookup

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.clauseOccurrencePort_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.clauseOccurrencePort_lookup

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.variableOccurrencePort_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.variableOccurrencePort_end

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.clauseOccurrencePort_end' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.clauseOccurrencePort_end

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.variablePort_end_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.variablePort_end_injective

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.clausePort_end_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.clausePort_end_injective

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.variablePort_end_ne_clausePort_end' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.variablePort_end_ne_clausePort_end

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_end_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_end_injective

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.disjointPortEndpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.disjointPortEndpoints

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_face_separated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_face_separated

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.geometricPairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.geometricPairing

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.geometricPairing_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.geometricPairing_disjoint

/-- info: 'STACS2027.PlanarAssembly.three_port_orders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.three_port_orders

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile.mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile.mirror

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile.relabel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile.relabel

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile.block

/-- info: 'STACS2027.PlanarAssembly.variableSignedNext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableSignedNext

/-- info: 'STACS2027.PlanarAssembly.variableSignedSide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableSignedSide

/-- info: 'STACS2027.PlanarAssembly.variableGraph_signed_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableGraph_signed_profile

/-- info: 'STACS2027.PlanarAssembly.placedVariableGraph_signed_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placedVariableGraph_signed_profile

/-- info: 'STACS2027.PlanarAssembly.placedClauseThreeGraph_port_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placedClauseThreeGraph_port_profile

/-- info: 'STACS2027.PlanarAssembly.placedClauseTwoGraph_port_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placedClauseTwoGraph_port_profile

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile.subdivideOnce_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile.subdivideOnce_bounded

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile.chainSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile.chainSteps

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile.linkSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile.linkSteps

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile.realizeLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile.realizeLinks

/-- info: 'STACS2027.PlanarAssembly.variableGraph_port_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableGraph_port_profile

/-- info: 'STACS2027.PlanarAssembly.clauseThreeGraph_port_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseThreeGraph_port_profile

/-- info: 'STACS2027.PlanarAssembly.clauseTwoGraph_port_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseTwoGraph_port_profile

/-- info: 'STACS2027.PlanarAssembly.NextSelected.conjugate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextSelected.conjugate

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile.mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile.mem

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile.perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile.perm

/-- info: 'STACS2027.PlanarAssembly.ProfileSubdivision.subdivide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ProfileSubdivision.subdivide

/-- info: 'STACS2027.PlanarAssembly.turn3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.turn3

/-- info: 'STACS2027.PlanarAssembly.three_port_order_cube' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.three_port_order_cube

/-- info: 'STACS2027.PlanarAssembly.common_face_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.common_face_reaches

/-- info: 'STACS2027.PlanarAssembly.two_port_orders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.two_port_orders

/-- info: 'STACS2027.PlanarAssembly.lift_avoiding_walk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.lift_avoiding_walk

/-- info: 'STACS2027.PlanarAssembly.NextSelected.lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextSelected.lift

/-- info: 'STACS2027.PlanarOperations.Subdivision.iotaF_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.iotaF_injective

/-- info: 'STACS2027.PlanarOperations.Subdivision.face_step_new_interior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.face_step_new_interior

/-- info: 'STACS2027.PlanarOperations.Subdivision.nextSelected_subdivide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nextSelected_subdivide

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile

/-- info: 'STACS2027.PlanarAssembly.sphericalPortProfile_of_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sphericalPortProfile_of_tables

/-- info: 'STACS2027.PlanarAssembly.variablePortNext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variablePortNext

/-- info: 'STACS2027.PlanarAssembly.variablePortPrev' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variablePortPrev

/-- info: 'STACS2027.PlanarAssembly.clauseThreePortNext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseThreePortNext

/-- info: 'STACS2027.PlanarAssembly.clauseTwoPortNext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseTwoPortNext

/-- info: 'STACS2027.PlanarAssembly.variablePortSide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variablePortSide

/-- info: 'STACS2027.PlanarAssembly.variableTablePort' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableTablePort

/-- info: 'STACS2027.PlanarAssembly.clauseThreeTablePort' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseThreeTablePort

/-- info: 'STACS2027.PlanarAssembly.clauseTwoTablePort' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseTwoTablePort

/-- info: 'STACS2027.PlanarAssembly.variablePortEdgeAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variablePortEdgeAt

/-- info: 'STACS2027.PlanarAssembly.clauseThreePortEdgeAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseThreePortEdgeAt

/-- info: 'STACS2027.PlanarAssembly.clauseTwoPortEdgeAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseTwoPortEdgeAt

/-- info: 'STACS2027.PlanarAssembly.variable_skeleton_port_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variable_skeleton_port_profile

/-- info: 'STACS2027.PlanarAssembly.clauseThree_skeleton_port_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseThree_skeleton_port_profile

/-- info: 'STACS2027.PlanarAssembly.clauseTwo_skeleton_port_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseTwo_skeleton_port_profile

/-- info: 'STACS2027.orientedClauseVertex_congr_choices' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseVertex_congr_choices

/-- info: 'STACS2027.orientedPlacedClauseGraph_congr_choices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedPlacedClauseGraph_congr_choices

/-- info: 'STACS2027.orientedFormulaGraph_congr_choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedFormulaGraph_congr_choices

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.formulaGraph_prescribed_choices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.formulaGraph_prescribed_choices

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.orientedFormulaGraph_planar_prescribed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.orientedFormulaGraph_planar_prescribed

/-- info: 'STACS2027.PlanarAssembly.NextSelected.restrict' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextSelected.restrict

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.HasProfiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.HasProfiles

/-- info: 'STACS2027.PlanarAssembly.chosenPieces_with_profiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.chosenPieces_with_profiles

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.HasProfiles.source_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.HasProfiles.source_orders

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.variableOccurrence_side' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.variableOccurrence_side

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.clauseOccurrence_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.clauseOccurrence_side

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.HasProfiles.occurrence_sides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.HasProfiles.occurrence_sides

/-- info: 'STACS2027.PlanarAssembly.SphericalPortProfile.reindex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SphericalPortProfile.reindex

/-- info: 'STACS2027.PlanarAssembly.pieceProfileNext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceProfileNext

/-- info: 'STACS2027.PlanarAssembly.pieceProfileSide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceProfileSide

/-- info: 'STACS2027.PlanarAssembly.variableSignedNext_val' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableSignedNext_val

/-- info: 'STACS2027.PlanarAssembly.clauseThreePortNext_val' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseThreePortNext_val

/-- info: 'STACS2027.PlanarAssembly.clauseTwoPortNext_val' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseTwoPortNext_val

/-- info: 'STACS2027.PlanarAssembly.piece_signed_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_signed_profile

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.assemblyFlips' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.assemblyFlips

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.assemblyFlips_occurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.assemblyFlips_occurrence

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.assemblyVertex_opposite_clause' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.assemblyVertex_opposite_clause

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.assemblyVertex_marked_clause' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.assemblyVertex_marked_clause

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.assemblyVertex_port_sides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.assemblyVertex_port_sides

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.attachment_port_endpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.attachment_port_endpoints

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.geometricPairing_glue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.geometricPairing_glue

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.geometricPairing_fibers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.geometricPairing_fibers

/-- info: 'STACS2027.PlanarAssembly.NextPort' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextPort

/-- info: 'STACS2027.PlanarAssembly.NextPort.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextPort.unique

/-- info: 'STACS2027.PlanarAssembly.NextPort.unshift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextPort.unshift

/-- info: 'STACS2027.PlanarAssembly.NextPort.shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextPort.shift

/-- info: 'STACS2027.PlanarAssembly.NextPort.predecessor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextPort.predecessor

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.boundary

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.boundary_of_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.boundary_of_next

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.boundary_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.boundary_after

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.boundary_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.boundary_before

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.boundary_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.boundary_step

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.routing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.routing

/-- info: 'STACS2027.PlanarAssembly.OrderedIncidencePorts.face_count_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.OrderedIncidencePorts.face_count_lower_bound

/-- info: 'STACS2027.PlanarAssembly.SelectedPairing.marked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SelectedPairing.marked

/-- info: 'STACS2027.PlanarAssembly.SelectedPairing.pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SelectedPairing.pair

/-- info: 'STACS2027.PlanarAssembly.SelectedPairing.marked_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SelectedPairing.marked_iff

/-- info: 'STACS2027.PlanarAssembly.SelectedPairing.pair_port' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SelectedPairing.pair_port

/-- info: 'STACS2027.PlanarAssembly.SelectedPairing.pair_unmarked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SelectedPairing.pair_unmarked

/-- info: 'STACS2027.PlanarAssembly.SelectedPairing.toPortPairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.SelectedPairing.toPortPairing

/-- info: 'STACS2027.PlanarAssembly.graphEdge_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.graphEdge_ne

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.pairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.pairing

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.pairing_marked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.pairing_marked

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.pairing_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.pairing_pair

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.pairing_variable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.pairing_variable

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.pairing_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.pairing_clause

/-- info: 'STACS2027.PlanarAssembly.piecePorts_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecePorts_length

/-- info: 'STACS2027.PlanarAssembly.piecePortIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecePortIndex

/-- info: 'STACS2027.PlanarAssembly.pieceNodeIndex_variable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceNodeIndex_variable

/-- info: 'STACS2027.PlanarAssembly.pieceNodeIndex_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceNodeIndex_clause

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.block_port_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.block_port_congr

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.sourcePort_piece_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.sourcePort_piece_match

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.transport' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.transport

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.predecessor_vertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.predecessor_vertex

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.order' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.order

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.order_spec' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.order_spec

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.order_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.order_injective

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.order_iterate' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.order_iterate

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.order_cyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.order_cyclic

/-- info: 'STACS2027.PlanarAssembly.PieceIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.PieceIndex

/-- info: 'STACS2027.PlanarAssembly.pieceClauseIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceClauseIndex

/-- info: 'STACS2027.PlanarAssembly.pieceVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceVertex

/-- info: 'STACS2027.PlanarAssembly.pieceUsedCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceUsedCount

/-- info: 'STACS2027.PlanarAssembly.pieceFullCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceFullCount

/-- info: 'STACS2027.PlanarAssembly.pieceNodeIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceNodeIndex

/-- info: 'STACS2027.PlanarAssembly.pieceUsedPort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceUsedPort

/-- info: 'STACS2027.PlanarAssembly.pieceUsedPort_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceUsedPort_injective

/-- info: 'STACS2027.PlanarAssembly.pieceUsedCount_le_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceUsedCount_le_three

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_piece_vertex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_piece_vertex

/-- info: 'STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_piece_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.LocalPortChoices.sourcePort_piece_complete

/-- info: 'STACS2027.PlanarAssembly.pieceNodeIndex_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceNodeIndex_complete

/-- info: 'STACS2027.PlanarAssembly.sourcePortNumber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sourcePortNumber

/-- info: 'STACS2027.PlanarAssembly.sourcePortNumber_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sourcePortNumber_even

/-- info: 'STACS2027.PlanarAssembly.sourcePortNumber_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sourcePortNumber_odd

/-- info: 'STACS2027.PlanarAssembly.piecePortIndex_number' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piecePortIndex_number

/-- info: 'STACS2027.PlanarAssembly.sourcePortCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sourcePortCount

/-- info: 'STACS2027.PlanarAssembly.sourceForward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sourceForward

/-- info: 'STACS2027.PlanarAssembly.sourcePortCount_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sourcePortCount_piece

/-- info: 'STACS2027.PlanarAssembly.sourceForward_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.sourceForward_piece

/-- info: 'STACS2027.PlanarAssembly.piece_profile_source_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_profile_source_order

/-- info: 'STACS2027.PlanarAssembly.occurrenceVertex_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrenceVertex_even

/-- info: 'STACS2027.PlanarAssembly.occurrenceVertex_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrenceVertex_odd

/-- info: 'STACS2027.PlanarAssembly.occurrenceDart_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrenceDart_injective

/-- info: 'STACS2027.PlanarAssembly.occurrenceDart_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrenceDart_cases

/-- info: 'STACS2027.PlanarAssembly.variableOccurrences' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableOccurrences

/-- info: 'STACS2027.PlanarAssembly.clauseOccurrences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseOccurrences

/-- info: 'STACS2027.PlanarAssembly.variableOccurrenceIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableOccurrenceIndex

/-- info: 'STACS2027.PlanarAssembly.clauseOccurrenceIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseOccurrenceIndex

/-- info: 'STACS2027.PlanarAssembly.variableOccurrenceIndex_vertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableOccurrenceIndex_vertex

/-- info: 'STACS2027.PlanarAssembly.clauseOccurrenceIndex_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseOccurrenceIndex_vertex

/-- info: 'STACS2027.PlanarAssembly.variableOccurrenceIndex_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableOccurrenceIndex_injective

/-- info: 'STACS2027.PlanarAssembly.clauseOccurrenceIndex_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseOccurrenceIndex_injective

/-- info: 'STACS2027.PlanarAssembly.variableNodeIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableNodeIndex

/-- info: 'STACS2027.PlanarAssembly.clauseNodeIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseNodeIndex

/-- info: 'STACS2027.PlanarAssembly.variableUsedPort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableUsedPort

/-- info: 'STACS2027.PlanarAssembly.variableUsedPort_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableUsedPort_injective

/-- info: 'STACS2027.PlanarAssembly.clauseUsedPort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseUsedPort

/-- info: 'STACS2027.PlanarAssembly.clauseUsedPort_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseUsedPort_injective

/-- info: 'STACS2027.PlanarAssembly.finite_injection_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.finite_injection_card

/-- info: 'STACS2027.PlanarAssembly.variableOccurrences_le_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableOccurrences_le_three

/-- info: 'STACS2027.PlanarAssembly.clauseOccurrences_le_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseOccurrences_le_three

/-- info: 'STACS2027.PlanarAssembly.occurrence_node_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrence_node_semantics

/-- info: 'STACS2027.PlanarAssembly.placedLiteral_port_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placedLiteral_port_zero

/-- info: 'STACS2027.PlanarAssembly.ChosenPieces.HasProfiles.source_rule_sides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ChosenPieces.HasProfiles.source_rule_sides

/-- info: 'STACS2027.PlanarAssembly.orientedFormulaGraph_planar_source_rule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.orientedFormulaGraph_planar_source_rule

/-- info: 'STACS2027.HasSphericalCofacialPorts.relabel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HasSphericalCofacialPorts.relabel

/-- info: 'STACS2027.EdgesOrdered' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.EdgesOrdered

/-- info: 'STACS2027.subdividedEdge_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdividedEdge_ordered

/-- info: 'STACS2027.realizeLinks_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_ordered

/-- info: 'STACS2027.mapEdge_block_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapEdge_block_eq

/-- info: 'STACS2027.mapGraph_block_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapGraph_block_eq

/-- info: 'STACS2027.HasSphericalCofacialPorts.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HasSphericalCofacialPorts.block

/-- info: 'STACS2027.mapGraph_block_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mapGraph_block_nodup

/-- info: 'STACS2027.PlanarAssembly.placedVariablePorts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placedVariablePorts

/-- info: 'STACS2027.PlanarAssembly.ungluedClausePorts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ungluedClausePorts

/-- info: 'STACS2027.PlanarAssembly.placedVariableGraph_sphericalPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placedVariableGraph_sphericalPorts

/-- info: 'STACS2027.PlanarAssembly.clauseGraph_sphericalPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseGraph_sphericalPorts

/-- info: 'STACS2027.PlanarAssembly.clauseGraph_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseGraph_ordered

/-- info: 'STACS2027.PlanarAssembly.ungluedClauseGraph_sphericalPorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ungluedClauseGraph_sphericalPorts

/-- info: 'STACS2027.PlanarAssembly.placedVariablePorts_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placedVariablePorts_nodup

/-- info: 'STACS2027.PlanarAssembly.ungluedClausePorts_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ungluedClausePorts_nodup

/-- info: 'STACS2027.PlanarAssembly.placedVariablePorts_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placedVariablePorts_length

/-- info: 'STACS2027.PlanarAssembly.ungluedClausePorts_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ungluedClausePorts_length

/-- info: 'STACS2027.PlanarAssembly.variablePorts_getElem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variablePorts_getElem

/-- info: 'STACS2027.PlanarAssembly.clausePorts_getElem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clausePorts_getElem

/-- info: 'STACS2027.PlanarAssembly.placedVariablePorts_getElem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.placedVariablePorts_getElem

/-- info: 'STACS2027.PlanarAssembly.ungluedClausePorts_getElem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.ungluedClausePorts_getElem

/-- info: 'STACS2027.PlanarBoundedMembership.boundedVerifier' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.boundedVerifier

/-- info: 'STACS2027.PlanarBoundedMembership.boundedProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.boundedProgram

/-- info: 'STACS2027.PlanarBoundedMembership.boundedProgram_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.boundedProgram_accepts

/-- info: 'STACS2027.PlanarBoundedMembership.boundedProgram_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.boundedProgram_sound

/-- info: 'STACS2027.PlanarBoundedMembership.boundedProgram_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.boundedProgram_complete

/-- info: 'STACS2027.planarBoundedSAT_inNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planarBoundedSAT_inNP

/-- info: 'STACS2027.PlanarBoundedMembership.TableCaps' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.TableCaps

/-- info: 'STACS2027.PlanarBoundedMembership.cTwo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.cTwo

/-- info: 'STACS2027.PlanarBoundedMembership.cPositive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.cPositive

/-- info: 'STACS2027.PlanarBoundedMembership.cNegative' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.cNegative

/-- info: 'STACS2027.PlanarBoundedMembership.extraCheck' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.extraCheck

/-- info: 'STACS2027.PlanarBoundedMembership.s_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.s_two

/-- info: 'STACS2027.PlanarBoundedMembership.s_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.s_positive

/-- info: 'STACS2027.PlanarBoundedMembership.s_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.s_negative

/-- info: 'STACS2027.PlanarBoundedMembership.s_extra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.s_extra

/-- info: 'STACS2027.PlanarBoundedMembership.count_le_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.count_le_one_iff

/-- info: 'STACS2027.PlanarBoundedMembership.count_le_two_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.count_le_two_iff

/-- info: 'STACS2027.PlanarBoundedMembership.parse_flatten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.parse_flatten

/-- info: 'STACS2027.PlanarBoundedMembership.checkedProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.checkedProgram

/-- info: 'STACS2027.PlanarBoundedMembership.checkedProgram_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.checkedProgram_emit

/-- info: 'STACS2027.PlanarBoundedMembership.lit_eq_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.lit_eq_pos

/-- info: 'STACS2027.PlanarBoundedMembership.lit_eq_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.lit_eq_neg

/-- info: 'STACS2027.PlanarBoundedMembership.tableCaps_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedMembership.tableCaps_iff

/-- info: 'STACS2027.PlanarBoundedSATLanguage' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarBoundedSATLanguage

/-- info: 'STACS2027.planarBoundedSAT_encode_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planarBoundedSAT_encode_iff

/-- info: 'STACS2027.PlanarCPAP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarCPAP

/-- info: 'STACS2027.planarCPAP_encode_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planarCPAP_encode_iff

/-- info: 'STACS2027.IsPlanarLeOneLeTwoCNF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsPlanarLeOneLeTwoCNF

/-- info: 'STACS2027.PlanarLeOneLeTwoSAT' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarLeOneLeTwoSAT

/-- info: 'STACS2027.planarLeOneLeTwoSAT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planarLeOneLeTwoSAT_eq

/-- info: 'STACS2027.GraphOutput.planar_encode_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.GraphOutput.planar_encode_iff

/-- info: 'STACS2027.WordPipeline.Runs.fixed_start' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Runs.fixed_start

/-- info: 'STACS2027.WordPipeline.Runs.terminal_unique' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.Runs.terminal_unique

/-- info: 'STACS2027.WordPipeline.reaches_units' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.reaches_units

/-- info: 'STACS2027.WordPipeline.planar_prepared_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.planar_prepared_execution

/-- info: 'STACS2027.WordPipeline.prepared_execution_linear_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.WordPipeline.prepared_execution_linear_words

/-- info: 'STACS2027.graphWithBudget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.graphWithBudget

/-- info: 'STACS2027.budgetTicks_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.budgetTicks_output

/-- info: 'STACS2027.graphWithBudget_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.graphWithBudget_output

/-- info: 'STACS2027.orientedFormulaGraph_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedFormulaGraph_normalized

/-- info: 'STACS2027.orientedGraphWithBudget_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedGraphWithBudget_output

/-- info: 'STACS2027.PlanarWordOutput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarWordOutput

/-- info: 'STACS2027.PlanarWordOutput.encoded_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarWordOutput.encoded_correct

/-- info: 'STACS2027.planar_full_domain_supplied_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planar_full_domain_supplied_table

/-- info: 'STACS2027.planar_full_domain_graphOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planar_full_domain_graphOutput

/-- info: 'STACS2027.PlanarGluing.cut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cut

/-- info: 'STACS2027.PlanarGluing.linked_label_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.linked_label_invariant

/-- info: 'STACS2027.PlanarGluing.componentCount_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.componentCount_ge

/-- info: 'STACS2027.PlanarGluing.componentRep_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.componentRep_step

/-- info: 'STACS2027.PlanarGluing.mergedComponentLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.mergedComponentLabel

/-- info: 'STACS2027.PlanarGluing.mergedComponentLabel_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.mergedComponentLabel_a

/-- info: 'STACS2027.PlanarGluing.mergedComponentLabel_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.mergedComponentLabel_b

/-- info: 'STACS2027.PlanarGluing.mergedComponentLabel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.mergedComponentLabel_step

/-- info: 'STACS2027.PlanarGluing.cut_mergedLabel_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cut_mergedLabel_invariant

/-- info: 'STACS2027.PlanarGluing.cut_components_le_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cut_components_le_add_one

/-- info: 'STACS2027.PlanarGluing.cut_step_transfer_of_faces_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cut_step_transfer_of_faces_ne

/-- info: 'STACS2027.PlanarGluing.cut_path_transfer_of_faces_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cut_path_transfer_of_faces_ne

/-- info: 'STACS2027.PlanarGluing.cut_components_le_of_faces_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cut_components_le_of_faces_ne

/-- info: 'STACS2027.PlanarGluing.cut_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cut_planar

/-- info: 'STACS2027.PlanarGluing.left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.left

/-- info: 'STACS2027.PlanarGluing.right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.right

/-- info: 'STACS2027.PlanarGluing.split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.split

/-- info: 'STACS2027.PlanarGluing.split_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.split_left

/-- info: 'STACS2027.PlanarGluing.split_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.split_right

/-- info: 'STACS2027.PlanarGluing.cases_dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cases_dart

/-- info: 'STACS2027.PlanarGluing.left_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.left_injective

/-- info: 'STACS2027.PlanarGluing.right_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.right_injective

/-- info: 'STACS2027.PlanarGluing.left_ne_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.left_ne_right

/-- info: 'STACS2027.PlanarGluing.sumPerm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.sumPerm

/-- info: 'STACS2027.PlanarGluing.sumPerm_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.sumPerm_left

/-- info: 'STACS2027.PlanarGluing.sumPerm_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.sumPerm_right

/-- info: 'STACS2027.PlanarGluing.swap' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.swap

/-- info: 'STACS2027.PlanarGluing.swap_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.swap_swap

/-- info: 'STACS2027.PlanarGluing.swap_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.swap_injective

/-- info: 'STACS2027.PlanarGluing.cycleRoots' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cycleRoots

/-- info: 'STACS2027.PlanarGluing.cycleRoots_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cycleRoots_nodup

/-- info: 'STACS2027.PlanarGluing.mem_cycleRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.mem_cycleRoots

/-- info: 'STACS2027.PlanarGluing.cmin_mem_cycleRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cmin_mem_cycleRoots

/-- info: 'STACS2027.PlanarGluing.cycleRoots_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cycleRoots_length

/-- info: 'STACS2027.PlanarGluing.Reaches' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reaches

/-- info: 'STACS2027.PlanarGluing.Reaches.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reaches.refl

/-- info: 'STACS2027.PlanarGluing.Reaches.step' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reaches.step

/-- info: 'STACS2027.PlanarGluing.Reaches.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reaches.trans

/-- info: 'STACS2027.PlanarGluing.Reaches.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reaches.symm

/-- info: 'STACS2027.PlanarGluing.reaches_cmin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.reaches_cmin

/-- info: 'STACS2027.PlanarGluing.cycleRoots_eq_of_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cycleRoots_eq_of_reaches

/-- info: 'STACS2027.PlanarGluing.sumPerm_cycles_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.sumPerm_cycles_ge

/-- info: 'STACS2027.PlanarGluing.SphericalEmbedding.of_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.SphericalEmbedding.of_data

/-- info: 'STACS2027.PlanarGluing.nodePredecessor_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.nodePredecessor_node

/-- info: 'STACS2027.PlanarGluing.LinkedPath' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.LinkedPath

/-- info: 'STACS2027.PlanarGluing.LinkedPath.refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.LinkedPath.refl

/-- info: 'STACS2027.PlanarGluing.LinkedPath.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.LinkedPath.step

/-- info: 'STACS2027.PlanarGluing.LinkedPath.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.LinkedPath.trans

/-- info: 'STACS2027.PlanarGluing.LinkedPath.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.LinkedPath.symm

/-- info: 'STACS2027.PlanarGluing.nodeOrbit_linked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.nodeOrbit_linked

/-- info: 'STACS2027.PlanarGluing.faceOrbit_linked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.faceOrbit_linked

/-- info: 'STACS2027.PlanarGluing.liftIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.liftIndex

/-- info: 'STACS2027.PlanarGluing.liftIndex_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.liftIndex_inverse

/-- info: 'STACS2027.PlanarGluing.DartEquiv.cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.cons

/-- info: 'STACS2027.PlanarGluing.IndexEquiv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.IndexEquiv

/-- info: 'STACS2027.PlanarGluing.IndexEquiv.refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.IndexEquiv.refl

/-- info: 'STACS2027.PlanarGluing.IndexEquiv.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.IndexEquiv.trans

/-- info: 'STACS2027.PlanarGluing.IndexEquiv.cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.IndexEquiv.cons

/-- info: 'STACS2027.PlanarGluing.IndexEquiv.swapHead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.IndexEquiv.swapHead

/-- info: 'STACS2027.PlanarGluing.IndexEquiv.of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.IndexEquiv.of_perm

/-- info: 'STACS2027.PlanarGluing.edgeIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.edgeIndex

/-- info: 'STACS2027.PlanarGluing.liftDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.liftDart

/-- info: 'STACS2027.PlanarGluing.edgeIndex_liftDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.edgeIndex_liftDart

/-- info: 'STACS2027.PlanarGluing.liftDart_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.liftDart_mod

/-- info: 'STACS2027.PlanarGluing.liftDart_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.liftDart_inverse

/-- info: 'STACS2027.PlanarGluing.DartEquiv.darts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.darts

/-- info: 'STACS2027.PlanarGluing.edgeIndex_graphEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.edgeIndex_graphEdge

/-- info: 'STACS2027.PlanarGluing.liftDart_graphEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.liftDart_graphEdge

/-- info: 'STACS2027.PlanarGluing.IndexEquiv.graphDarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.IndexEquiv.graphDarts

/-- info: 'STACS2027.PlanarGluing.planarGraph_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.planarGraph_perm

/-- info: 'STACS2027.PlanarGluing.flipEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipEdge

/-- info: 'STACS2027.PlanarGluing.flipEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipEdges

/-- info: 'STACS2027.PlanarGluing.flipEdges_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipEdges_length

/-- info: 'STACS2027.PlanarGluing.flipEdges_getElem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipEdges_getElem

/-- info: 'STACS2027.PlanarGluing.flipEdge_twice' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipEdge_twice

/-- info: 'STACS2027.PlanarGluing.flipEdges_twice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipEdges_twice

/-- info: 'STACS2027.PlanarGluing.graphEdge_twice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.graphEdge_twice

/-- info: 'STACS2027.PlanarGluing.flipDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipDart

/-- info: 'STACS2027.PlanarGluing.flipDart_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipDart_index

/-- info: 'STACS2027.PlanarGluing.flipDart_twice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipDart_twice

/-- info: 'STACS2027.PlanarGluing.flipDart_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipDart_edge

/-- info: 'STACS2027.PlanarGluing.flipDartEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipDartEquiv

/-- info: 'STACS2027.PlanarGluing.flipDart_ends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.flipDart_ends

/-- info: 'STACS2027.PlanarGluing.planarGraph_flipEdges_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.planarGraph_flipEdges_forward

/-- info: 'STACS2027.PlanarGluing.planarGraph_flipEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.planarGraph_flipEdges

/-- info: 'STACS2027.PlanarGluing.canonicalEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.canonicalEdge

/-- info: 'STACS2027.PlanarGluing.canonicalEdges_eq_flipEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.canonicalEdges_eq_flipEdges

/-- info: 'STACS2027.PlanarGluing.planarGraph_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.planarGraph_canonical

/-- info: 'STACS2027.incidenceVertexBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.incidenceVertexBound

/-- info: 'STACS2027.incidence_edge_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.incidence_edge_bounds

/-- info: 'STACS2027.incidence_halfEdgeEnd_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.incidence_halfEdgeEnd_bound

/-- info: 'STACS2027.incidence_addPaddingClause' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.incidence_addPaddingClause

/-- info: 'STACS2027.planar_incidence_addPaddingClause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planar_incidence_addPaddingClause

/-- info: 'STACS2027.planar_incidence_padFormula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planar_incidence_padFormula

/-- info: 'STACS2027.PlanarGluing.pathEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.pathEdges

/-- info: 'STACS2027.PlanarGluing.pathEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.pathEmbedding

/-- info: 'STACS2027.PlanarGluing.pathEmbedding_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.pathEmbedding_valid

/-- info: 'STACS2027.PlanarGluing.pathEmbedding_ends' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.pathEmbedding_ends

/-- info: 'STACS2027.PlanarGluing.sphericalOfTables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.sphericalOfTables

/-- info: 'STACS2027.PlanarGluing.pathSpherical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.pathSpherical

/-- info: 'STACS2027.PlanarGluing.sphericalTwoEdgePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.sphericalTwoEdgePath

/-- info: 'STACS2027.PlanarGluing.Reflection.inverse_iterate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.inverse_iterate

/-- info: 'STACS2027.PlanarGluing.Reflection.inverse_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.inverse_reaches

/-- info: 'STACS2027.PlanarGluing.Reflection.cycles_of_same_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.cycles_of_same_orbits

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_node_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_node_inverse

/-- info: 'STACS2027.PlanarGluing.Reflection.node_mirror_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.node_mirror_inverse

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_node_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_node_orbits

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_face_edge_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_face_edge_step

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_face_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_face_reverse

/-- info: 'STACS2027.PlanarGluing.Reflection.edgeEquiv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.edgeEquiv

/-- info: 'STACS2027.PlanarGluing.Reflection.faceInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.faceInv

/-- info: 'STACS2027.PlanarGluing.Reflection.face_faceInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.face_faceInv

/-- info: 'STACS2027.PlanarGluing.Reflection.faceInv_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.faceInv_face

/-- info: 'STACS2027.PlanarGluing.Reflection.faceInv_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.faceInv_injective

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_cycles_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_cycles_node

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_cycles_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_cycles_face

/-- info: 'STACS2027.PlanarGluing.Reflection.path_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.path_simulation

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_path

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_linked

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_components

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_euler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_euler

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_planar

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_spherical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_spherical

/-- info: 'STACS2027.PlanarGluing.Reflection.mirror_embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.mirror_embedding

/-- info: 'STACS2027.PlanarGluing.Reflection.embedding_edge_twice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.Reflection.embedding_edge_twice

/-- info: 'STACS2027.PlanarGluing.DartEquiv.spherical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.spherical

/-- info: 'STACS2027.PlanarGluing.DartEquiv.cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.cast

/-- info: 'STACS2027.PlanarGluing.SphericalEmbedding.relabel_ends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.SphericalEmbedding.relabel_ends

/-- info: 'STACS2027.PlanarGluing.DartEquiv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv

/-- info: 'STACS2027.PlanarGluing.DartEquiv.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.refl

/-- info: 'STACS2027.PlanarGluing.DartEquiv.symm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.symm

/-- info: 'STACS2027.PlanarGluing.DartEquiv.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.trans

/-- info: 'STACS2027.PlanarGluing.DartEquiv.injective' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.injective

/-- info: 'STACS2027.PlanarGluing.DartEquiv.card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.card_le

/-- info: 'STACS2027.PlanarGluing.DartEquiv.card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.card_eq

/-- info: 'STACS2027.PlanarGluing.DartEquiv.conjugate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.conjugate

/-- info: 'STACS2027.PlanarGluing.DartEquiv.conjugate_toFun' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.conjugate_toFun

/-- info: 'STACS2027.PlanarGluing.DartEquiv.inv_conjugate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.inv_conjugate

/-- info: 'STACS2027.PlanarGluing.DartEquiv.iterate_conjugate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.iterate_conjugate

/-- info: 'STACS2027.PlanarGluing.DartEquiv.conjugate_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.conjugate_injective

/-- info: 'STACS2027.PlanarGluing.DartEquiv.cycles_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.cycles_le

/-- info: 'STACS2027.PlanarGluing.DartEquiv.cycles_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.cycles_eq

/-- info: 'STACS2027.PlanarGluing.DartEquiv.hypermap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.hypermap

/-- info: 'STACS2027.PlanarGluing.DartEquiv.linked_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.linked_map

/-- info: 'STACS2027.PlanarGluing.ComponentRoot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.ComponentRoot

/-- info: 'STACS2027.PlanarGluing.componentRoot_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.componentRoot_iff

/-- info: 'STACS2027.PlanarGluing.componentRoot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.componentRoot_le

/-- info: 'STACS2027.PlanarGluing.componentRoot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.componentRoot_eq

/-- info: 'STACS2027.PlanarGluing.compMin_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.compMin_linked

/-- info: 'STACS2027.PlanarGluing.componentRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.componentRep

/-- info: 'STACS2027.PlanarGluing.componentRep_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.componentRep_linked

/-- info: 'STACS2027.PlanarGluing.componentRep_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.componentRep_root

/-- info: 'STACS2027.PlanarGluing.linked_of_componentRep_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.linked_of_componentRep_eq

/-- info: 'STACS2027.PlanarGluing.DartEquiv.components_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.components_le

/-- info: 'STACS2027.PlanarGluing.DartEquiv.planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.DartEquiv.planar

/-- info: 'STACS2027.PlanarGluing.graphEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.graphEdge

/-- info: 'STACS2027.PlanarGluing.GraphDartEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.GraphDartEquiv

/-- info: 'STACS2027.PlanarGluing.GraphDartEquiv.planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.GraphDartEquiv.planar

/-- info: 'STACS2027.PlanarGluing.transpose' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose

/-- info: 'STACS2027.PlanarGluing.transpose_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_injective

/-- info: 'STACS2027.PlanarGluing.transpose_twice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_twice

/-- info: 'STACS2027.PlanarGluing.transpose_a' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_a

/-- info: 'STACS2027.PlanarGluing.transpose_b' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_b

/-- info: 'STACS2027.PlanarGluing.transpose_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_other

/-- info: 'STACS2027.PlanarGluing.reaches_until_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.reaches_until_invariant

/-- info: 'STACS2027.PlanarGluing.transpose_merge_markers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_merge_markers

/-- info: 'STACS2027.PlanarGluing.transpose_merge_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_merge_step

/-- info: 'STACS2027.PlanarGluing.transpose_merge_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_merge_orbit

/-- info: 'STACS2027.PlanarGluing.mergeRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.mergeRep

/-- info: 'STACS2027.PlanarGluing.mergeRep_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.mergeRep_step

/-- info: 'STACS2027.PlanarGluing.transpose_reaches_mergeRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_reaches_mergeRep

/-- info: 'STACS2027.PlanarGluing.transpose_merge_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_merge_cycles

/-- info: 'STACS2027.PlanarGluing.cmin_eq_iff_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cmin_eq_iff_reaches

/-- info: 'STACS2027.PlanarGluing.crank_cycle_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.crank_cycle_injective

/-- info: 'STACS2027.PlanarGluing.crank_max_of_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.crank_max_of_wrap

/-- info: 'STACS2027.PlanarGluing.crank_step_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.crank_step_of_lt

/-- info: 'STACS2027.PlanarGluing.cutLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cutLabel

/-- info: 'STACS2027.PlanarGluing.cutLabel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.cutLabel_step

/-- info: 'STACS2027.PlanarGluing.transpose_split_separate_of_rank_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_split_separate_of_rank_lt

/-- info: 'STACS2027.PlanarGluing.swap_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.swap_comm

/-- info: 'STACS2027.PlanarGluing.transpose_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_comm

/-- info: 'STACS2027.PlanarGluing.transpose_split_separate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_split_separate

/-- info: 'STACS2027.PlanarGluing.transpose_split_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.transpose_split_cycles

/-- info: 'STACS2027.PlanarGluing.sumPerm_iterate_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.sumPerm_iterate_left

/-- info: 'STACS2027.PlanarGluing.sumPerm_iterate_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.sumPerm_iterate_right

/-- info: 'STACS2027.PlanarGluing.disjointSum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.disjointSum

/-- info: 'STACS2027.PlanarGluing.disjointSum_left_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.disjointSum_left_path

/-- info: 'STACS2027.PlanarGluing.disjointSum_right_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.disjointSum_right_path

/-- info: 'STACS2027.PlanarGluing.componentRoots' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.componentRoots

/-- info: 'STACS2027.PlanarGluing.componentRoots_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.componentRoots_length

/-- info: 'STACS2027.PlanarGluing.disjointSum_components_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.disjointSum_components_le

/-- info: 'STACS2027.PlanarGluing.disjointSum_euler_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.disjointSum_euler_ge

/-- info: 'STACS2027.PlanarGluing.disjointSum_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.disjointSum_planar

/-- info: 'STACS2027.PlanarGluing.tables_spherical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.tables_spherical

/-- info: 'STACS2027.PlanarGluing.SphericalEmbedding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.SphericalEmbedding

/-- info: 'STACS2027.PlanarGluing.disjointSum_graphEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.disjointSum_graphEdge

/-- info: 'STACS2027.PlanarGluing.disjointSum_nodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.disjointSum_nodes

/-- info: 'STACS2027.PlanarGluing.planarGraph_append_spherical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarGluing.planarGraph_append_spherical

/-- info: 'STACS2027.PlanarOperations.Subdivision.iota' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.iota

/-- info: 'STACS2027.PlanarOperations.Subdivision.sig' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.sig

/-- info: 'STACS2027.PlanarOperations.Subdivision.IsOld' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.IsOld

/-- info: 'STACS2027.PlanarOperations.Subdivision.sig_iota' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.sig_iota

/-- info: 'STACS2027.PlanarOperations.Subdivision.isOld_iota' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.isOld_iota

/-- info: 'STACS2027.PlanarOperations.Subdivision.iota_sig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.iota_sig

/-- info: 'STACS2027.PlanarOperations.Subdivision.iota_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.iota_lt

/-- info: 'STACS2027.PlanarOperations.Subdivision.sig_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.sig_lt

/-- info: 'STACS2027.PlanarOperations.Subdivision.iota_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.iota_mono

/-- info: 'STACS2027.PlanarOperations.Subdivision.nd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nd

/-- info: 'STACS2027.PlanarOperations.Subdivision.ndi' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.ndi

/-- info: 'STACS2027.PlanarOperations.Subdivision.fc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.fc

/-- info: 'STACS2027.PlanarOperations.Subdivision.tau' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.tau

/-- info: 'STACS2027.PlanarOperations.Subdivision.nd_old' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nd_old

/-- info: 'STACS2027.PlanarOperations.Subdivision.nd_r1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nd_r1

/-- info: 'STACS2027.PlanarOperations.Subdivision.nd_r3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nd_r3

/-- info: 'STACS2027.PlanarOperations.Subdivision.ndi_old' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.ndi_old

/-- info: 'STACS2027.PlanarOperations.Subdivision.ndi_r1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.ndi_r1

/-- info: 'STACS2027.PlanarOperations.Subdivision.ndi_r3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.ndi_r3

/-- info: 'STACS2027.PlanarOperations.Subdivision.dart_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.dart_cases

/-- info: 'STACS2027.PlanarOperations.Subdivision.sig_new' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.sig_new

/-- info: 'STACS2027.PlanarOperations.Subdivision.nd_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nd_lt

/-- info: 'STACS2027.PlanarOperations.Subdivision.ndi_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.ndi_lt

/-- info: 'STACS2027.PlanarOperations.Subdivision.nd_ndi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nd_ndi

/-- info: 'STACS2027.PlanarOperations.Subdivision.ed_lt'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.ed_lt'

/-- info: 'STACS2027.PlanarOperations.Subdivision.newMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.newMap

/-- info: 'STACS2027.PlanarOperations.Subdivision.G'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.G'

/-- info: 'STACS2027.PlanarOperations.Subdivision.nodeLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nodeLabel

/-- info: 'STACS2027.PlanarOperations.Subdivision.graphEdge_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.graphEdge_new

/-- info: 'STACS2027.PlanarOperations.Subdivision.nodeLabel_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nodeLabel_old

/-- info: 'STACS2027.PlanarOperations.Subdivision.nodeLabel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nodeLabel_step

/-- info: 'STACS2027.PlanarOperations.Subdivision.nodes_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.nodes_ge

/-- info: 'STACS2027.PlanarOperations.Subdivision.fc_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.fc_low

/-- info: 'STACS2027.PlanarOperations.Subdivision.fc_r0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.fc_r0

/-- info: 'STACS2027.PlanarOperations.Subdivision.fc_r1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.fc_r1

/-- info: 'STACS2027.PlanarOperations.Subdivision.fc_r2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.fc_r2

/-- info: 'STACS2027.PlanarOperations.Subdivision.fc_r3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.fc_r3

/-- info: 'STACS2027.PlanarOperations.Subdivision.tau_old' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.tau_old

/-- info: 'STACS2027.PlanarOperations.Subdivision.tau_new' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.tau_new

/-- info: 'STACS2027.PlanarOperations.Subdivision.tau_r3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.tau_r3

/-- info: 'STACS2027.PlanarOperations.Subdivision.tau_r0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.tau_r0

/-- info: 'STACS2027.PlanarOperations.Subdivision.tau_r2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.tau_r2

/-- info: 'STACS2027.PlanarOperations.Subdivision.tau_iota' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.tau_iota

/-- info: 'STACS2027.PlanarOperations.Subdivision.tau_fc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.tau_fc

/-- info: 'STACS2027.PlanarOperations.Subdivision.tau_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.tau_lt

/-- info: 'STACS2027.PlanarOperations.Subdivision.iotaF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.iotaF

/-- info: 'STACS2027.PlanarOperations.Subdivision.sigF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.sigF

/-- info: 'STACS2027.PlanarOperations.Subdivision.faces_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.faces_ge

/-- info: 'STACS2027.PlanarOperations.Subdivision.iota_r' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.iota_r

/-- info: 'STACS2027.PlanarOperations.Subdivision.step_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.step_transfer

/-- info: 'STACS2027.PlanarOperations.Subdivision.linked_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.linked_transfer

/-- info: 'STACS2027.PlanarOperations.Subdivision.components_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.components_le

/-- info: 'STACS2027.PlanarOperations.Subdivision.newMap_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.newMap_planar

/-- info: 'STACS2027.PlanarOperations.Subdivision.splitEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.splitEdges

/-- info: 'STACS2027.PlanarOperations.Subdivision.flatMap_two_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.flatMap_two_length

/-- info: 'STACS2027.PlanarOperations.Subdivision.getElem?_flatMap_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.getElem?_flatMap_two

/-- info: 'STACS2027.PlanarOperations.Subdivision.splitEdges_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.splitEdges_length

/-- info: 'STACS2027.PlanarOperations.Subdivision.splitEdges_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.splitEdges_get

/-- info: 'STACS2027.PlanarOperations.Subdivision.end_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.end_split

/-- info: 'STACS2027.PlanarOperations.Subdivision.end_c' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.end_c

/-- info: 'STACS2027.PlanarOperations.Subdivision.end_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.end_old

/-- info: 'STACS2027.PlanarOperations.Subdivision.iterate_node_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.iterate_node_val

/-- info: 'STACS2027.PlanarOperations.Subdivision.iterate_nd_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.iterate_nd_old

/-- info: 'STACS2027.PlanarOperations.Subdivision.reach_c' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.reach_c

/-- info: 'STACS2027.PlanarOperations.Subdivision.planar_subdivide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.planar_subdivide

/-- info: 'STACS2027.PlanarOperations.Subdivision.iterate_face_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.iterate_face_val

/-- info: 'STACS2027.PlanarOperations.Subdivision.face_step_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.face_step_transfer

/-- info: 'STACS2027.PlanarOperations.Subdivision.face_orbit_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Subdivision.face_orbit_transfer

/-- info: 'STACS2027.planar_subdivideOnce_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planar_subdivideOnce_bounded

/-- info: 'STACS2027.planar_chainSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planar_chainSteps

/-- info: 'STACS2027.planar_linkSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planar_linkSteps

/-- info: 'STACS2027.planar_realizeLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planar_realizeLinks

/-- info: 'STACS2027.variableGraph_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableGraph_planar

/-- info: 'STACS2027.clauseThreeGraph_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeGraph_planar

/-- info: 'STACS2027.clauseTwoGraph_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoGraph_planar

/-- info: 'STACS2027.IsGraphEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsGraphEmbedding

/-- info: 'STACS2027.HasCofacialPorts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HasCofacialPorts

/-- info: 'STACS2027.HasCofacialPorts.mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HasCofacialPorts.mem

/-- info: 'STACS2027.PlanarOperations.Ports.embedding_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Ports.embedding_transport

/-- info: 'STACS2027.variableLinks_ports_unsubdivided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableLinks_ports_unsubdivided

/-- info: 'STACS2027.clauseThreeLinks_ports_unsubdivided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThreeLinks_ports_unsubdivided

/-- info: 'STACS2027.clauseTwoLinks_ports_unsubdivided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwoLinks_ports_unsubdivided

/-- info: 'STACS2027.PlanarOperations.Ports.splitMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Ports.splitMap

/-- info: 'STACS2027.PlanarOperations.Ports.embedding_subdivide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarOperations.Ports.embedding_subdivide

/-- info: 'STACS2027.subdivideOnce_perm_liftEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_perm_liftEdges

/-- info: 'STACS2027.subdivideOnce_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivideOnce_nodup

/-- info: 'STACS2027.subdivisionGraph_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivisionGraph_nodup

/-- info: 'STACS2027.subdivisionGraph_perm_expanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.subdivisionGraph_perm_expanded

/-- info: 'STACS2027.realizeLinks_perm_subdivisionGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.realizeLinks_perm_subdivisionGraph

/-- info: 'STACS2027.splitEdges_singleton_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.splitEdges_singleton_perm

/-- info: 'STACS2027.PlanarPreprocess.cutThenShrink_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.cutThenShrink_planar

/-- info: 'STACS2027.PlanarPreprocess.planarGraph_dropLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.planarGraph_dropLast

/-- info: 'STACS2027.PlanarPreprocess.planarGraph_sublist_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.planarGraph_sublist_prefix

/-- info: 'STACS2027.PlanarPreprocess.planarGraph_sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.planarGraph_sublist

/-- info: 'STACS2027.PlanarPreprocess.Prunes.planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Prunes.planar

/-- info: 'STACS2027.PlanarPreprocess.normalized_output_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.normalized_output_planar

/-- info: 'STACS2027.PlanarPreprocess.normalized_output_padded_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.normalized_output_padded_planar

/-- info: 'STACS2027.PlanarPreprocess.contradiction_padded_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.contradiction_padded_planar

/-- info: 'STACS2027.PlanarPreprocess.Deletion.old_dart_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.old_dart_cases

/-- info: 'STACS2027.PlanarPreprocess.Deletion.project' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.project

/-- info: 'STACS2027.PlanarPreprocess.Deletion.project_embed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.project_embed

/-- info: 'STACS2027.PlanarPreprocess.Deletion.project_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.project_last

/-- info: 'STACS2027.PlanarPreprocess.Deletion.embed_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.embed_project

/-- info: 'STACS2027.PlanarPreprocess.Deletion.project_removeLast_of_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.project_removeLast_of_ne

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removeLast_of_hits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removeLast_of_hits

/-- info: 'STACS2027.PlanarPreprocess.Deletion.edgeOrbit_linked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.edgeOrbit_linked

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrink_step_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrink_step_lift

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrink_path_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrink_path_lift

/-- info: 'STACS2027.PlanarPreprocess.Deletion.project_fixed_perm_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.project_fixed_perm_step

/-- info: 'STACS2027.PlanarPreprocess.Deletion.project_shrink_step_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.project_shrink_step_fixed

/-- info: 'STACS2027.PlanarPreprocess.Deletion.project_shrink_node_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.project_shrink_node_step

/-- info: 'STACS2027.PlanarPreprocess.Deletion.project_shrink_face_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.project_shrink_face_step

/-- info: 'STACS2027.PlanarPreprocess.Deletion.project_shrink_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.project_shrink_step

/-- info: 'STACS2027.PlanarPreprocess.Deletion.project_shrink_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.project_shrink_path

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_linked

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_componentRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_componentRoot

/-- info: 'STACS2027.PlanarPreprocess.Deletion.linked_from_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.linked_from_fixed

/-- info: 'STACS2027.PlanarPreprocess.Deletion.componentRoot_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.componentRoot_last

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_components

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_planar

/-- info: 'STACS2027.PlanarPreprocess.Deletion.cutLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.cutLast

/-- info: 'STACS2027.PlanarPreprocess.Deletion.cutLast_last_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.cutLast_last_fixed

/-- info: 'STACS2027.PlanarPreprocess.Deletion.cutLast_penultimate_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.cutLast_penultimate_fixed

/-- info: 'STACS2027.PlanarPreprocess.Deletion.cutLast_shrink_last_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.cutLast_shrink_last_fixed

/-- info: 'STACS2027.PlanarPreprocess.Deletion.cutThenShrink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.cutThenShrink

/-- info: 'STACS2027.PlanarPreprocess.Deletion.cutThenShrink_edge_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.cutThenShrink_edge_lift

/-- info: 'STACS2027.PlanarPreprocess.Deletion.cutThenShrink_node_orbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.cutThenShrink_node_orbit

/-- info: 'STACS2027.PlanarPreprocess.Deletion.graphEdge_last_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.graphEdge_last_pair

/-- info: 'STACS2027.PlanarPreprocess.Deletion.cutThenShrink_graphEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.cutThenShrink_graphEdge

/-- info: 'STACS2027.PlanarPreprocess.Deletion.cutThenShrink_graphNodes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.cutThenShrink_graphNodes

/-- info: 'STACS2027.PlanarPreprocess.Deletion.penultimate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.penultimate

/-- info: 'STACS2027.PlanarPreprocess.Deletion.penultimate_ne_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.penultimate_ne_last

/-- info: 'STACS2027.PlanarPreprocess.Deletion.embedPair_ne_penultimate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.embedPair_ne_penultimate

/-- info: 'STACS2027.PlanarPreprocess.Deletion.embedPair_ne_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.embedPair_ne_last

/-- info: 'STACS2027.PlanarPreprocess.Deletion.embed_removePair_of_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.embed_removePair_of_avoids

/-- info: 'STACS2027.PlanarPreprocess.Deletion.nodeInverse' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.nodeInverse

/-- info: 'STACS2027.PlanarPreprocess.Deletion.nodeInverse_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.nodeInverse_injective

/-- info: 'STACS2027.PlanarPreprocess.Deletion.node_nodeInverse' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.node_nodeInverse

/-- info: 'STACS2027.PlanarPreprocess.Deletion.embed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.embed

/-- info: 'STACS2027.PlanarPreprocess.Deletion.last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.last

/-- info: 'STACS2027.PlanarPreprocess.Deletion.embed_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.embed_injective

/-- info: 'STACS2027.PlanarPreprocess.Deletion.embed_ne_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.embed_ne_last

/-- info: 'STACS2027.PlanarPreprocess.Deletion.skipLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.skipLast

/-- info: 'STACS2027.PlanarPreprocess.Deletion.skipLast_ne_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.skipLast_ne_last

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removeLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removeLast

/-- info: 'STACS2027.PlanarPreprocess.Deletion.embed_removeLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.embed_removeLast

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removeLast_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removeLast_injective

/-- info: 'STACS2027.PlanarPreprocess.Deletion.lift_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.lift_step

/-- info: 'STACS2027.PlanarPreprocess.Deletion.lift_reaches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.lift_reaches

/-- info: 'STACS2027.PlanarPreprocess.Deletion.retract_iterate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.retract_iterate

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removeLast_orbit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removeLast_orbit

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removeLast_cmin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removeLast_cmin

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removeLast_cycleMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removeLast_cycleMin

/-- info: 'STACS2027.PlanarPreprocess.Deletion.last_cycleMin_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.last_cycleMin_iff

/-- info: 'STACS2027.PlanarPreprocess.Deletion.finRange_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.finRange_snoc

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removeLast_cycleCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removeLast_cycleCount

/-- info: 'STACS2027.PlanarPreprocess.Deletion.comp_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.comp_injective

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removeLast_comp_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removeLast_comp_fixed

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removeLast_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removeLast_inverse

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removePair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removePair

/-- info: 'STACS2027.PlanarPreprocess.Deletion.embedPair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.embedPair

/-- info: 'STACS2027.PlanarPreprocess.Deletion.rnext_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.rnext_split

/-- info: 'STACS2027.PlanarPreprocess.Deletion.rnext_filter_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.rnext_filter_ne

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removeLast_rnext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removeLast_rnext

/-- info: 'STACS2027.PlanarPreprocess.Deletion.filter_lt_filter_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.filter_lt_filter_lt

/-- info: 'STACS2027.PlanarPreprocess.Deletion.removePair_rnext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.removePair_rnext

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_node_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_node_orbit

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_face_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_face_orbit

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_edge_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_edge_orbit

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_edge_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_edge_lift

/-- info: 'STACS2027.PlanarPreprocess.Deletion.edge_fixed_face_node_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.edge_fixed_face_node_fixed

/-- info: 'STACS2027.PlanarPreprocess.Deletion.singletonLoss' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.singletonLoss

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_edge_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_edge_cycles

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_node_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_node_cycles

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_face_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_face_cycles

/-- info: 'STACS2027.PlanarPreprocess.Deletion.shrinkLast_eulerRhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Deletion.shrinkLast_eulerRhs

/-- info: 'STACS2027.PlanarPreprocess.IncidenceVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.IncidenceVertex

/-- info: 'STACS2027.PlanarPreprocess.IncidenceEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.IncidenceEdge

/-- info: 'STACS2027.PlanarPreprocess.renameClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.renameClause

/-- info: 'STACS2027.PlanarPreprocess.mapEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.mapEdge

/-- info: 'STACS2027.PlanarPreprocess.labelledIncidence' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.labelledIncidence

/-- info: 'STACS2027.PlanarPreprocess.labelledIncidence_offset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.labelledIncidence_offset

/-- info: 'STACS2027.PlanarPreprocess.incidenceGraph_labelled' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.incidenceGraph_labelled

/-- info: 'STACS2027.PlanarPreprocess.labelledIncidence_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.labelledIncidence_map

/-- info: 'STACS2027.PlanarPreprocess.keepLabel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.keepLabel

/-- info: 'STACS2027.PlanarPreprocess.keepLabel_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.keepLabel_injective

/-- info: 'STACS2027.PlanarPreprocess.Prunes.incidence_sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Prunes.incidence_sublist

/-- info: 'STACS2027.PlanarPreprocess.renameClause_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.renameClause_injective

/-- info: 'STACS2027.PlanarPreprocess.planarGraph_map_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.planarGraph_map_injective

/-- info: 'STACS2027.PlanarPreprocess.Prunes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Prunes

/-- info: 'STACS2027.PlanarPreprocess.Prunes.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.Prunes.trans

/-- info: 'STACS2027.PlanarPreprocess.normalize_prunes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.normalize_prunes

/-- info: 'STACS2027.PlanarPreprocess.CellsPrune' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.CellsPrune

/-- info: 'STACS2027.PlanarPreprocess.CellsPrune.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.CellsPrune.refl

/-- info: 'STACS2027.PlanarPreprocess.updateAt_prunes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.updateAt_prunes

/-- info: 'STACS2027.PlanarPreprocess.updateIds_prunes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.updateIds_prunes

/-- info: 'STACS2027.PlanarPreprocess.CellsPrune.contents' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.CellsPrune.contents

/-- info: 'STACS2027.PlanarPreprocess.StatePrunes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.StatePrunes

/-- info: 'STACS2027.PlanarPreprocess.step_prunes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.step_prunes

/-- info: 'STACS2027.PlanarPreprocess.executes_prunes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.executes_prunes

/-- info: 'STACS2027.PlanarPreprocess.normalized_output_prunes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarPreprocess.normalized_output_prunes

/-- info: 'STACS2027.halfEdgeEnd_relabel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.halfEdgeEnd_relabel

/-- info: 'STACS2027.planarGraph_relabel_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planarGraph_relabel_iff

/-- info: 'STACS2027.planarGraph_relabel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planarGraph_relabel

/-- info: 'STACS2027.halfEdgeEnd_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.halfEdgeEnd_bound

/-- info: 'STACS2027.PlanarSource.Formula.CanonicalClauseRotation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.CanonicalClauseRotation

/-- info: 'STACS2027.PlanarSource.Formula.copiedClause_port_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copiedClause_port_data

/-- info: 'STACS2027.PlanarSource.Formula.copiedClause_port_predecessor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copiedClause_port_predecessor

/-- info: 'STACS2027.PlanarSource.Formula.clauseRole_port_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.clauseRole_port_data

/-- info: 'STACS2027.PlanarSource.Formula.clauseRole_port_predecessor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.clauseRole_port_predecessor

/-- info: 'STACS2027.PlanarSource.Formula.odd_expanded_role' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.odd_expanded_role

/-- info: 'STACS2027.PlanarSource.Formula.placedRingMap_odd_predecessor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.placedRingMap_odd_predecessor

/-- info: 'STACS2027.PlanarSource.ComputableComb.GraphEmbedding.dropLast_node_of_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.GraphEmbedding.dropLast_node_of_lt

/-- info: 'STACS2027.PlanarSource.ComputableComb.GraphEmbedding.prefix_node_of_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.GraphEmbedding.prefix_node_of_lt

/-- info: 'STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_clause_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_clause_node

/-- info: 'STACS2027.PlanarSource.ComputableComb.edgeData_clause_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.edgeData_clause_next

/-- info: 'STACS2027.PlanarSource.ComputableComb.rotationData_cast_clause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.rotationData_cast_clause

/-- info: 'STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_formulaData_clause' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_formulaData_clause

/-- info: 'STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_formulaData_clause_prev' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_formulaData_clause_prev

/-- info: 'STACS2027.PlanarSource.ComputableComb.gridIncidenceEmbedding_formulaData_clause_prev' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.gridIncidenceEmbedding_formulaData_clause_prev

/-- info: 'STACS2027.PlanarSource.cellPositions_count' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.cellPositions_count

/-- info: 'STACS2027.PlanarSource.RotationTable.GridBlock.variable_twice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.RotationTable.GridBlock.variable_twice

/-- info: 'STACS2027.PlanarSource.grid_variable_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.grid_variable_twice

/-- info: 'STACS2027.PlanarSource.count_le_one_of_unique_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.count_le_one_of_unique_index

/-- info: 'STACS2027.PlanarSource.rotation_no_fixed_of_twice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.rotation_no_fixed_of_twice

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_distinct

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_distinct

/-- info: 'STACS2027.PlanarSource.Formula.grid_ringFormula_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.grid_ringFormula_distinct

/-- info: 'STACS2027.PlanarSource.ComputableComb.rnext_map_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.rnext_map_injective

/-- info: 'STACS2027.PlanarSource.ComputableComb.incidence_length_nM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.incidence_length_nM

/-- info: 'STACS2027.PlanarSource.ComputableComb.rot_filter_incidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.rot_filter_incidence

/-- info: 'STACS2027.PlanarSource.ComputableComb.variableAt_eq_vr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.variableAt_eq_vr

/-- info: 'STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_node

/-- info: 'STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_edgeData_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_edgeData_next

/-- info: 'STACS2027.PlanarSource.ComputableComb.rotationData_cast_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.rotationData_cast_next

/-- info: 'STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_formulaData_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.incidenceEmbedding_formulaData_next

/-- info: 'STACS2027.PlanarSource.ComputableComb.gridIncidenceEmbedding_formulaData_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.gridIncidenceEmbedding_formulaData_next

/-- info: 'STACS2027.PlanarSource.Embedding.Reaches' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.Reaches

/-- info: 'STACS2027.PlanarSource.Embedding.Reaches.refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.Reaches.refl

/-- info: 'STACS2027.PlanarSource.Embedding.Reaches.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.Reaches.trans

/-- info: 'STACS2027.PlanarSource.Embedding.Reaches.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.Reaches.step

/-- info: 'STACS2027.PlanarSource.Embedding.Reaches.edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.Reaches.edge

/-- info: 'STACS2027.PlanarSource.Embedding.Reaches.node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.Reaches.node

/-- info: 'STACS2027.PlanarSource.Embedding.Reaches.face' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.Reaches.face

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.liftOriginal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.liftOriginal

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.liftOriginal_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.liftOriginal_zero

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_ring_reaches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_ring_reaches

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_to_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_to_block

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.lift_original_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.lift_original_edge

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.lift_original_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.lift_original_node

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.lift_original_face' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.lift_original_face

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.lift_original_linked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.lift_original_linked

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.componentMinimum' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.componentMinimum

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.componentMinimum_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.componentMinimum_spec

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_minimum_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_minimum_block

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_minimum_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_minimum_original

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.componentBack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.componentBack

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.componentBack_minimum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.componentBack_minimum

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.componentBack_injective_on_minima' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.componentBack_injective_on_minima

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_componentCount_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_componentCount_le

/-- info: 'STACS2027.PlanarSource.ComputableComb.GraphEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.GraphEmbedding

/-- info: 'STACS2027.PlanarSource.ComputableComb.next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.next

/-- info: 'STACS2027.PlanarSource.ComputableComb.prev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.prev

/-- info: 'STACS2027.PlanarSource.ComputableComb.next_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.next_eq

/-- info: 'STACS2027.PlanarSource.ComputableComb.prev_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.prev_eq

/-- info: 'STACS2027.PlanarSource.ComputableComb.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.map

/-- info: 'STACS2027.PlanarSource.ComputableComb.map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.map_eq

/-- info: 'STACS2027.PlanarSource.ComputableComb.registered_node_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.registered_node_orbit

/-- info: 'STACS2027.PlanarSource.ComputableComb.registered_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.registered_planar

/-- info: 'STACS2027.PlanarSource.ComputableComb.embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.embedding

/-- info: 'STACS2027.PlanarSource.ComputableComb.embedding_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.embedding_node

/-- info: 'STACS2027.PlanarSource.ComputableComb.gridEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.gridEmbedding

/-- info: 'STACS2027.PlanarSource.ComputableComb.finalEdgeCast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.finalEdgeCast

/-- info: 'STACS2027.PlanarSource.ComputableComb.finalEdgeCast_nodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.finalEdgeCast_nodes

/-- info: 'STACS2027.PlanarSource.ComputableComb.GraphEmbedding.dropLast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.GraphEmbedding.dropLast

/-- info: 'STACS2027.PlanarSource.ComputableComb.GraphEmbedding.reindex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.GraphEmbedding.reindex

/-- info: 'STACS2027.PlanarSource.ComputableComb.GraphEmbedding.prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.GraphEmbedding.prefix

/-- info: 'STACS2027.PlanarSource.ComputableComb.gridIncidenceEmbedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.gridIncidenceEmbedding

/-- info: 'STACS2027.PlanarSource.ComputableComb.gridRingOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.gridRingOutput

/-- info: 'STACS2027.PlanarSource.ComputableComb.gridRingOutput_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.gridRingOutput_correct

/-- info: 'STACS2027.PlanarSource.ComputableFormula.RotationData' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableFormula.RotationData

/-- info: 'STACS2027.PlanarSource.ComputableFormula.edgeData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableFormula.edgeData

/-- info: 'STACS2027.PlanarSource.ComputableFormula.edgeData_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableFormula.edgeData_next

/-- info: 'STACS2027.PlanarSource.ComputableFormula.formulaData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableFormula.formulaData

/-- info: 'STACS2027.PlanarSource.ComputableFormula.output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableFormula.output

/-- info: 'STACS2027.PlanarSource.ComputableFormula.formulaData_variable_orbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableFormula.formulaData_variable_orbit

/-- info: 'STACS2027.PlanarSource.ComputableFormula.output_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableFormula.output_planar

/-- info: 'STACS2027.PlanarSource.ComputableFormula.output_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableFormula.output_bounded

/-- info: 'STACS2027.PlanarSource.ComputableFormula.output_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableFormula.output_satisfiable

/-- info: 'STACS2027.PlanarSource.ComputableFormula.output_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableFormula.output_correct

/-- info: 'STACS2027.PlanarSource.negate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.negate

/-- info: 'STACS2027.PlanarSource.opposite_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.opposite_counts

/-- info: 'STACS2027.PlanarSource.ComputableComb.GraphEmbedding.dropLast_rnext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.GraphEmbedding.dropLast_rnext

/-- info: 'STACS2027.PlanarSource.ComputableComb.GraphEmbedding.prefix_rnext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ComputableComb.GraphEmbedding.prefix_rnext

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_length

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_flatten' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_flatten

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_variables' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_variables

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_flatten_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_flatten_length

/-- info: 'STACS2027.PlanarSource.Formula.ringClauses_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauses_length

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_length

/-- info: 'STACS2027.PlanarSource.Formula.ringClauses_flatten_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauses_flatten_length

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_flatten_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_flatten_length

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_variableBound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_variableBound

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_variableBound_of_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_variableBound_of_bounded

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_variableBound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_variableBound

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation

/-- info: 'STACS2027.PlanarSource.Embedding.dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.dart

/-- info: 'STACS2027.PlanarSource.Embedding.index' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.index

/-- info: 'STACS2027.PlanarSource.Embedding.index_dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.index_dart

/-- info: 'STACS2027.PlanarSource.Embedding.dart_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.dart_mod

/-- info: 'STACS2027.PlanarSource.Embedding.dart_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.dart_index

/-- info: 'STACS2027.PlanarSource.Embedding.d2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.d2

/-- info: 'STACS2027.PlanarSource.Embedding.d6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.d6

/-- info: 'STACS2027.PlanarSource.Embedding.two_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.two_cases

/-- info: 'STACS2027.PlanarSource.Embedding.six_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.six_cases

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.oldEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.oldEdge

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.oldNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.oldNode

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.oldFace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.oldFace

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.original' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.original

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newEdge

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newNode

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newFace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newFace

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded

/-- info: 'STACS2027.PlanarSource.Embedding.fin6_val_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.fin6_val_three

/-- info: 'STACS2027.PlanarSource.Embedding.fin6_val_four' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.fin6_val_four

/-- info: 'STACS2027.PlanarSource.Embedding.fin6_val_five' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.fin6_val_five

/-- info: 'STACS2027.PlanarSource.Embedding.dart_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.dart_injective

/-- info: 'STACS2027.PlanarSource.Embedding.dart_tags_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.dart_tags_ne

/-- info: 'STACS2027.PlanarSource.Embedding.dart_map_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.dart_map_nodup

/-- info: 'STACS2027.PlanarSource.Embedding.dart_maps_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.dart_maps_disjoint

/-- info: 'STACS2027.PlanarSource.Embedding.reaches_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.reaches_map

/-- info: 'STACS2027.PlanarSource.Embedding.cycleCount_le_representatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.cycleCount_le_representatives

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.oldNodeRep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.oldNodeRep

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.oldNodeReps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.oldNodeReps

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.oldNode_reaches_rep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.oldNode_reaches_rep

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.oldNodeRep_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.oldNodeRep_mem

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.original_node_count_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.original_node_count_le

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newNodeRep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newNodeRep

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newNodeReps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newNodeReps

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newNodeRep_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newNodeRep_step

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newNodeReps_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newNodeReps_nodup

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newNodeReps_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newNodeReps_fixed

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_node_count_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_node_count_ge

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.liftOriginalFace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.liftOriginalFace

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newFaceLabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newFaceLabel

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newFaceLabel_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newFaceLabel_lift

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newFaceLabel_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newFaceLabel_step

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newFaceReps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newFaceReps

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newFaceReps_labels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newFaceReps_labels

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_face_count_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_face_count_ge

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.original_edge_count_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.original_edge_count_le

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_edge_pairing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_edge_pairing

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_edge_count_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_edge_count_ge

/-- info: 'STACS2027.PlanarSource.Embedding.nodePred' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.nodePred

/-- info: 'STACS2027.PlanarSource.Embedding.node_nodePred' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.node_nodePred

/-- info: 'STACS2027.PlanarSource.Embedding.nodePred_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.nodePred_node

/-- info: 'STACS2027.PlanarSource.Embedding.node_dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.node_dart

/-- info: 'STACS2027.PlanarSource.Embedding.nodePred_dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.nodePred_dart

/-- info: 'STACS2027.PlanarSource.Embedding.blockRotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.blockRotation

/-- info: 'STACS2027.PlanarSource.Embedding.fromHypermap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.fromHypermap

/-- info: 'STACS2027.PlanarSource.Embedding.blockRotation_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.blockRotation_iterate

/-- info: 'STACS2027.PlanarSource.Embedding.blockRotation_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.blockRotation_orbit

/-- info: 'STACS2027.PlanarSource.Embedding.fromHypermap_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.fromHypermap_node

/-- info: 'STACS2027.PlanarSource.Embedding.fromHypermap_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.fromHypermap_edge

/-- info: 'STACS2027.PlanarSource.Embedding.hypermap_eq_of_edge_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.hypermap_eq_of_edge_node

/-- info: 'STACS2027.PlanarSource.Embedding.fromHypermap_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.fromHypermap_original

/-- info: 'STACS2027.PlanarSource.Embedding.halfEdgeEnd_d2_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.halfEdgeEnd_d2_zero

/-- info: 'STACS2027.PlanarSource.Embedding.halfEdgeEnd_d2_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.halfEdgeEnd_d2_one

/-- info: 'STACS2027.PlanarSource.Embedding.bipartiteSide' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.bipartiteSide

/-- info: 'STACS2027.PlanarSource.Embedding.halfEdgeEnd_side' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.halfEdgeEnd_side

/-- info: 'STACS2027.PlanarSource.Embedding.incidence_node_parity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.incidence_node_parity

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.ExpandedVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.ExpandedVertex

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedVertex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedVertex

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedEdges

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedEdges_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedEdges_length

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedEdges_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedEdges_end

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.Anchor' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.Anchor

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.anchor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.anchor

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.anchorDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.anchorDart

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.anchorVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.anchorVertex

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedVertex_anchor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedVertex_anchor

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.newNode_reaches_anchor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.newNode_reaches_anchor

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedVertex_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedVertex_step

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.anchors_reach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.anchors_reach

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_node_orbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_node_orbit

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedEdges_planar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expandedEdges_planar

/-- info: 'STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_planar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Embedding.BipartiteRotation.expanded_planar

/-- info: 'STACS2027.PlanarSource.gridCNF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.gridCNF_zero

/-- info: 'STACS2027.PlanarSource.ringFormula_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.ringFormula_nil

/-- info: 'STACS2027.PlanarSource.empty_source_properties' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.empty_source_properties

/-- info: 'STACS2027.PlanarSource.sourceEndpointChoices' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.sourceEndpointChoices

/-- info: 'STACS2027.PlanarSource.sourceEndpointChoices_negative' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.sourceEndpointChoices_negative

/-- info: 'STACS2027.PlanarSource.sourceEndpointChoices_first' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.sourceEndpointChoices_first

/-- info: 'STACS2027.PlanarSource.sourceEndpointChoices_second' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.sourceEndpointChoices_second

/-- info: 'STACS2027.PlanarSource.Formula.IncidenceEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.IncidenceEdge

/-- info: 'STACS2027.PlanarSource.Formula.incidenceAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.incidenceAt

/-- info: 'STACS2027.PlanarSource.Formula.incidenceAt_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.incidenceAt_zero

/-- info: 'STACS2027.PlanarSource.Formula.incidenceAt_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.incidenceAt_cons

/-- info: 'STACS2027.PlanarSource.Formula.incidenceAt_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.incidenceAt_length

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula

/-- info: 'STACS2027.PlanarSource.Formula.tagCopies_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.tagCopies_length

/-- info: 'STACS2027.PlanarSource.Formula.tagCopies_incidenceAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.tagCopies_incidenceAt

/-- info: 'STACS2027.PlanarSource.Formula.copyFormula_incidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyFormula_incidence

/-- info: 'STACS2027.PlanarSource.Formula.ringClauses' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauses

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula

/-- info: 'STACS2027.PlanarSource.Formula.implicationEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.implicationEdges

/-- info: 'STACS2027.PlanarSource.Formula.ringClauses_incidenceAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauses_incidenceAt

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_incidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_incidence

/-- info: 'STACS2027.PlanarSource.Formula.map_range_triples' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.map_range_triples

/-- info: 'STACS2027.PlanarSource.Formula.map_flatMap_interleave' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.map_flatMap_interleave

/-- info: 'STACS2027.PlanarSource.Formula.encodeExpanded' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.encodeExpanded

/-- info: 'STACS2027.PlanarSource.Formula.encodeExpanded_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.encodeExpanded_injective

/-- info: 'STACS2027.PlanarSource.Formula.nextIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.nextIndex

/-- info: 'STACS2027.PlanarSource.Formula.clauseIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.clauseIndex

/-- info: 'STACS2027.PlanarSource.Formula.expandedPair' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.expandedPair

/-- info: 'STACS2027.PlanarSource.Formula.expandedPair_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.expandedPair_at

/-- info: 'STACS2027.PlanarSource.Formula.expandedEdges_encoded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.expandedEdges_encoded

/-- info: 'STACS2027.PlanarSource.Formula.correctedTriples' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.correctedTriples

/-- info: 'STACS2027.PlanarSource.Formula.expandedEdges_corrected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.expandedEdges_corrected

/-- info: 'STACS2027.PlanarSource.Formula.incidenceGraph_length_flatten' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.incidenceGraph_length_flatten

/-- info: 'STACS2027.PlanarSource.Formula.copyIncidence_eq_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyIncidence_eq_range

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_incidence_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_incidence_perm

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_planar_of_expanded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_planar_of_expanded

/-- info: 'STACS2027.PlanarSource.Formula.occurrence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.occurrence

/-- info: 'STACS2027.PlanarSource.Formula.occurrence_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.occurrence_mem

/-- info: 'STACS2027.PlanarSource.Formula.occurrence_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.occurrence_of_mem

/-- info: 'STACS2027.PlanarSource.Formula.successor_range_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.successor_range_perm

/-- info: 'STACS2027.PlanarSource.Formula.pairClause_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.pairClause_count

/-- info: 'STACS2027.PlanarSource.Formula.ringClauses_occurrences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauses_occurrences

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_occurrences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_occurrences

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_bounded

/-- info: 'STACS2027.PlanarSource.Formula.ring_clause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ring_clause

/-- info: 'STACS2027.PlanarSource.Formula.ring_propagates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ring_propagates

/-- info: 'STACS2027.PlanarSource.Formula.ring_constant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ring_constant

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_satisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_satisfiable

/-- info: 'STACS2027.PlanarSource.Formula.sourceSigns' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.sourceSigns

/-- info: 'STACS2027.PlanarSource.Formula.sourceSigns_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.sourceSigns_at

/-- info: 'STACS2027.PlanarSource.Formula.nextIndex_at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.nextIndex_at

/-- info: 'STACS2027.PlanarSource.Formula.embeddedRingFormula' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.embeddedRingFormula

/-- info: 'STACS2027.PlanarSource.Formula.embeddedRingFormula_satisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.embeddedRingFormula_satisfiable

/-- info: 'STACS2027.PlanarSource.Formula.embeddedRingFormula_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.embeddedRingFormula_bounded

/-- info: 'STACS2027.PlanarSource.Formula.embeddedRingFormula_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.embeddedRingFormula_planar

/-- info: 'STACS2027.PlanarSource.FromFormula.variableAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.FromFormula.variableAt

/-- info: 'STACS2027.PlanarSource.FromFormula.clauseAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.FromFormula.clauseAt

/-- info: 'STACS2027.PlanarSource.FromFormula.variableAt_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.FromFormula.variableAt_get

/-- info: 'STACS2027.PlanarSource.FromFormula.incidenceAt_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.FromFormula.incidenceAt_first

/-- info: 'STACS2027.PlanarSource.FromFormula.incidence_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.FromFormula.incidence_first

/-- info: 'STACS2027.PlanarSource.FromFormula.incidence_second' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.FromFormula.incidence_second

/-- info: 'STACS2027.PlanarSource.FromFormula.incidence_labels' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.FromFormula.incidence_labels

/-- info: 'STACS2027.PlanarSource.Packed.ringRecords' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringRecords

/-- info: 'STACS2027.PlanarSource.Packed.successorGraphProgram_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.successorGraphProgram_refines

/-- info: 'STACS2027.PlanarSource.Packed.successorGraphProgram_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.successorGraphProgram_source

/-- info: 'STACS2027.PlanarSource.Packed.ringGraphBlock_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringGraphBlock_exact

/-- info: 'STACS2027.PlanarSource.Packed.ringGraphBlock_copies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringGraphBlock_copies

/-- info: 'STACS2027.PlanarSource.Packed.copyGraphLiterals' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyGraphLiterals

/-- info: 'STACS2027.PlanarSource.Packed.copyGraphLiterals_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyGraphLiterals_eval

/-- info: 'STACS2027.PlanarSource.Packed.copyGraphBlock' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyGraphBlock

/-- info: 'STACS2027.PlanarSource.Packed.copiedAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copiedAt

/-- info: 'STACS2027.PlanarSource.Packed.copyGraphBlock_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyGraphBlock_emit

/-- info: 'STACS2027.PlanarSource.Packed.pairGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.pairGraphProgram

/-- info: 'STACS2027.PlanarSource.Packed.pairGraphProgram_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.pairGraphProgram_emit

/-- info: 'STACS2027.PlanarSource.Packed.successorGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.successorGraphProgram

/-- info: 'STACS2027.PlanarSource.Packed.ringGraphBlock' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringGraphBlock

/-- info: 'STACS2027.PlanarSource.Packed.Layout.startGraphProgram_copies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.startGraphProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endGraphProgram_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endGraphProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellGraphProgram_copies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellGraphProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowGraphProgram_copies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowGraphProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.Layout.columnGraphProgram_copies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.columnGraphProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.clauseRowBaseValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.clauseRowBaseValue

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowRowGraphProgram_copies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowRowGraphProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.Layout.graphPhase_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.graphPhase_copies

/-- info: 'STACS2027.PlanarSource.Packed.orientedFormulaGraph_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.orientedFormulaGraph_nil

/-- info: 'STACS2027.PlanarSource.Packed.ringGrid_graph_planar_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringGrid_graph_planar_empty

/-- info: 'STACS2027.PlanarSource.Packed.incidenceNext_grid_permutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.incidenceNext_grid_permutation

/-- info: 'STACS2027.PlanarSource.Packed.ringGrid_records_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringGrid_records_output

/-- info: 'STACS2027.PlanarSource.Packed.graphOutput_ringGraphRecords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphOutput_ringGraphRecords

/-- info: 'STACS2027.PlanarSource.Packed.graphOutput_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphOutput_spec

/-- info: 'STACS2027.PlanarSource.Packed.graphOutput_assignment_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphOutput_assignment_iff

/-- info: 'STACS2027.PlanarSource.Formula.ringFormulaGraph_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormulaGraph_planar

/-- info: 'STACS2027.PlanarSource.Packed.ringGrid_graph_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringGrid_graph_planar

/-- info: 'STACS2027.PlanarSource.Packed.Layout.occurrenceCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.occurrenceCount

/-- info: 'STACS2027.PlanarSource.Packed.Layout.occurrenceCount_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.occurrenceCount_eval

/-- info: 'STACS2027.PlanarSource.Packed.Layout.occurrenceCount_lift_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.occurrenceCount_lift_eval

/-- info: 'STACS2027.PlanarSource.Packed.ascendingVariableGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ascendingVariableGraphProgram

/-- info: 'STACS2027.PlanarSource.Packed.ascendingVariableGraphProgram_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ascendingVariableGraphProgram_emit

/-- info: 'STACS2027.PlanarSource.Packed.Layout.startGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.startGraphProgram

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellGraphProgram

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endGraphProgram

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowGraphProgram

/-- info: 'STACS2027.PlanarSource.Packed.Layout.columnGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.columnGraphProgram

/-- info: 'STACS2027.PlanarSource.Packed.Layout.graphPhase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.graphPhase

/-- info: 'STACS2027.PlanarSource.Packed.Layout.graphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.graphProgram

/-- info: 'STACS2027.PlanarSource.Packed.gridGraphProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.gridGraphProgram

/-- info: 'STACS2027.PlanarSource.Packed.gridGraphProgram_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.gridGraphProgram_emit

/-- info: 'STACS2027.PlanarSource.Packed.Layout.graphProgram_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.graphProgram_emit

/-- info: 'STACS2027.PlanarSource.Packed.graphBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphBody

/-- info: 'STACS2027.PlanarSource.Packed.graphSourceProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphSourceProgram

/-- info: 'STACS2027.PlanarSource.Packed.graphOutput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphOutput

/-- info: 'STACS2027.PlanarSource.Packed.graphOutput_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphOutput_polyTime

/-- info: 'STACS2027.PlanarSource.Packed.graphOutput_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphOutput_eq

/-- info: 'STACS2027.PlanarSource.Packed.Layout.sourceRingRecords' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.sourceRingRecords

/-- info: 'STACS2027.PlanarSource.Packed.Layout.startGraphProgram_rings' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.startGraphProgram_rings

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellGraphProgram_rings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellGraphProgram_rings

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endGraphProgram_rings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endGraphProgram_rings

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowGraphProgram_rings' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowGraphProgram_rings

/-- info: 'STACS2027.PlanarSource.Packed.GraphRingBlocks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.GraphRingBlocks

/-- info: 'STACS2027.PlanarSource.Packed.GraphRingBlocks.column' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.GraphRingBlocks.column

/-- info: 'STACS2027.PlanarSource.Packed.GraphRingBlocks.row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.GraphRingBlocks.row

/-- info: 'STACS2027.PlanarSource.Packed.graphPhase_rings_of_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.graphPhase_rings_of_blocks

/-- info: 'STACS2027.PlanarSource.Packed.Layout.sourceRingRecords_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.sourceRingRecords_lift

/-- info: 'STACS2027.PlanarSource.Packed.Layout.graphRingBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.graphRingBlocks

/-- info: 'STACS2027.PlanarSource.Packed.Layout.graphPhase_rings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.graphPhase_rings

/-- info: 'STACS2027.PlanarSource.Formula.copyPlaced' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyPlaced

/-- info: 'STACS2027.PlanarSource.Formula.ringPlaced' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringPlaced

/-- info: 'STACS2027.PlanarSource.Formula.ringGraphRecords' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringGraphRecords

/-- info: 'STACS2027.PlanarSource.Formula.copyPlaced_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.copyPlaced_length

/-- info: 'STACS2027.PlanarSource.Formula.ringGraphRecords_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringGraphRecords_eq

/-- info: 'STACS2027.PlanarSource.Formula.ringGraphRecords_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringGraphRecords_output

/-- info: 'STACS2027.PlanarSource.Formula.ringClauseRecordsAt_explicit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringClauseRecordsAt_explicit

/-- info: 'STACS2027.planarBoundedSAT_np_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planarBoundedSAT_np_hard

/-- info: 'STACS2027.planarBoundedSAT_np_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planarBoundedSAT_np_complete

/-- info: 'STACS2027.planarLeOneLeTwoSAT_np_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.planarLeOneLeTwoSAT_np_complete

/-- info: 'STACS2027.PlanarSource.Packed.Layout.columnSize_eval' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.columnSize_eval

/-- info: 'STACS2027.PlanarSource.Packed.Layout.columnBase_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.columnBase_eval

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellBase_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellBase_eval

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endBase_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endBase_eval

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowBase_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowBase_eval

/-- info: 'STACS2027.PlanarSource.Packed.Layout.formulaLength_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.formulaLength_eval

/-- info: 'STACS2027.PlanarSource.Packed.Layout.columnLive_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.columnLive_eval

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellLive_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellLive_eval

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowLive_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowLive_eval

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cell_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cell_block

/-- info: 'STACS2027.PlanarSource.Packed.Layout.start_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.start_block

/-- info: 'STACS2027.PlanarSource.Packed.Layout.end_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.end_block

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbow_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbow_block

/-- info: 'STACS2027.PlanarSource.Packed.addN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.addN

/-- info: 'STACS2027.PlanarSource.Packed.mulN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.mulN

/-- info: 'STACS2027.PlanarSource.Packed.subN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.subN

/-- info: 'STACS2027.PlanarSource.Packed.Template' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Template

/-- info: 'STACS2027.PlanarSource.Packed.Template.eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Template.eval

/-- info: 'STACS2027.PlanarSource.Packed.orientExpr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.orientExpr

/-- info: 'STACS2027.PlanarSource.Packed.keyExpr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.keyExpr

/-- info: 'STACS2027.PlanarSource.Packed.templateOccurrences' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.templateOccurrences

/-- info: 'STACS2027.PlanarSource.Packed.blockOccurrences' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.blockOccurrences

/-- info: 'STACS2027.PlanarSource.Packed.copyBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyBlock

/-- info: 'STACS2027.PlanarSource.Packed.copiesAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copiesAt

/-- info: 'STACS2027.PlanarSource.Packed.copyBlock_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyBlock_emit

/-- info: 'STACS2027.PlanarSource.Packed.signChoice' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.signChoice

/-- info: 'STACS2027.PlanarSource.Packed.signChoice_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.signChoice_eval

/-- info: 'STACS2027.PlanarSource.Packed.templateSign' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.templateSign

/-- info: 'STACS2027.PlanarSource.Packed.cellTemplates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.cellTemplates

/-- info: 'STACS2027.PlanarSource.Packed.startTemplates' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.startTemplates

/-- info: 'STACS2027.PlanarSource.Packed.cellTemplates_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.cellTemplates_eval

/-- info: 'STACS2027.PlanarSource.Packed.endTemplates' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.endTemplates

/-- info: 'STACS2027.PlanarSource.Packed.rainbowTemplates' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.rainbowTemplates

/-- info: 'STACS2027.PlanarSource.Packed.startTemplates_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.startTemplates_eval

/-- info: 'STACS2027.PlanarSource.Packed.endTemplates_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.endTemplates_eval

/-- info: 'STACS2027.PlanarSource.Packed.rainbowTemplates_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.rainbowTemplates_eval

/-- info: 'STACS2027.PlanarSource.Packed.ringGrid_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringGrid_distinct

/-- info: 'STACS2027.PlanarSource.Packed.output_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.output_distinct

/-- info: 'STACS2027.PlanarSource.Packed.cell_literals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.cell_literals

/-- info: 'STACS2027.PlanarSource.Packed.reverse_blocks_literals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.reverse_blocks_literals

/-- info: 'STACS2027.PlanarSource.Packed.column_literals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.column_literals

/-- info: 'STACS2027.PlanarSource.Packed.startProgram_copies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.startProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.endProgram_copies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.endProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.rainbowProgram_copies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.rainbowProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.columnProgram_copies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.columnProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.rowBaseValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.rowBaseValue

/-- info: 'STACS2027.PlanarSource.Packed.forDown_guard_emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.forDown_guard_emit

/-- info: 'STACS2027.PlanarSource.Packed.rainbowRowProgram_copies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.rainbowRowProgram_copies

/-- info: 'STACS2027.PlanarSource.Packed.gridPhase_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.gridPhase_copies

/-- info: 'STACS2027.PlanarSource.Formula.ringFormula_next_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Formula.ringFormula_next_congr

/-- info: 'STACS2027.PlanarSource.Packed.incidenceNext_grid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.incidenceNext_grid

/-- info: 'STACS2027.PlanarSource.Packed.ringFormula_eq_gridRingOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringFormula_eq_gridRingOutput

/-- info: 'STACS2027.PlanarSource.Packed.ringGrid_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringGrid_correct

/-- info: 'STACS2027.PlanarSource.Packed.output_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.output_correct

/-- info: 'STACS2027.PlanarSource.Packed.copyGraphAt_column' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyGraphAt_column

/-- info: 'STACS2027.PlanarSource.Packed.copyGraphAt_rainbowRow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyGraphAt_rainbowRow

/-- info: 'STACS2027.PlanarSource.Packed.copiesAt_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copiesAt_length

/-- info: 'STACS2027.PlanarSource.Packed.copyGraphAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyGraphAt

/-- info: 'STACS2027.PlanarSource.Packed.copyGraphAt_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyGraphAt_append

/-- info: 'STACS2027.PlanarSource.Packed.copyGraphAt_reverse_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.copyGraphAt_reverse_blocks

/-- info: 'STACS2027.PlanarSource.Packed.expandCopyRecords' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.expandCopyRecords

/-- info: 'STACS2027.PlanarSource.Packed.expandCopyRecords_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.expandCopyRecords_append

/-- info: 'STACS2027.PlanarSource.Packed.expandCopyRecords_flatMap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.expandCopyRecords_flatMap

/-- info: 'STACS2027.PlanarSource.Packed.expandCopyRecords_copiesAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.expandCopyRecords_copiesAt

/-- info: 'STACS2027.PlanarSource.Packed.ringGraphRecords_expandCopies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.ringGraphRecords_expandCopies

/-- info: 'STACS2027.PlanarSource.Packed.Index.size' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.size

/-- info: 'STACS2027.PlanarSource.Packed.Index.size_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.size_nil

/-- info: 'STACS2027.PlanarSource.Packed.Index.size_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.size_append

/-- info: 'STACS2027.PlanarSource.Packed.Index.size_flatMap_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.size_flatMap_const

/-- info: 'STACS2027.PlanarSource.Packed.Index.inst_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.inst_length

/-- info: 'STACS2027.PlanarSource.Packed.Index.cell_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.cell_size

/-- info: 'STACS2027.PlanarSource.Packed.Index.start_size' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.start_size

/-- info: 'STACS2027.PlanarSource.Packed.Index.end_size' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.end_size

/-- info: 'STACS2027.PlanarSource.Packed.Index.evenRainbow_size' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.evenRainbow_size

/-- info: 'STACS2027.PlanarSource.Packed.Index.oddRainbow_size' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.oddRainbow_size

/-- info: 'STACS2027.PlanarSource.Packed.Index.columnSize' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.columnSize

/-- info: 'STACS2027.PlanarSource.Packed.Index.column_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.column_size

/-- info: 'STACS2027.PlanarSource.Packed.Index.truncate_reverse_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.truncate_reverse_flatMap

/-- info: 'STACS2027.PlanarSource.Packed.Index.grid_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.grid_blocks

/-- info: 'STACS2027.PlanarSource.Packed.Index.rainbow_row_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.rainbow_row_size

/-- info: 'STACS2027.PlanarSource.Packed.Index.grid_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.grid_size

/-- info: 'STACS2027.PlanarSource.Packed.Layout' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout

/-- info: 'STACS2027.PlanarSource.Packed.Layout.lift' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.lift

/-- info: 'STACS2027.PlanarSource.Packed.Layout.columnSize' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.columnSize

/-- info: 'STACS2027.PlanarSource.Packed.Layout.formulaLength' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.formulaLength

/-- info: 'STACS2027.PlanarSource.Packed.Layout.variableCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.variableCount

/-- info: 'STACS2027.PlanarSource.Packed.Layout.columnBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.columnBase

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellBase

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endBase

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowBase

/-- info: 'STACS2027.PlanarSource.Packed.Layout.columnLive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.columnLive

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellLive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellLive

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowLive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowLive

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellTemplates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellTemplates

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellOccurrences' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellOccurrences

/-- info: 'STACS2027.PlanarSource.Packed.Layout.startOccurrences' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.startOccurrences

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endOccurrences' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endOccurrences

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowOccurrences' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowOccurrences

/-- info: 'STACS2027.PlanarSource.Packed.gate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.gate

/-- info: 'STACS2027.PlanarSource.Packed.Layout.chainCandidates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.chainCandidates

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellCandidates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellCandidates

/-- info: 'STACS2027.PlanarSource.Packed.Layout.startCandidates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.startCandidates

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endCandidates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endCandidates

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowCandidates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowCandidates

/-- info: 'STACS2027.PlanarSource.Packed.successorProgram_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.successorProgram_registered

/-- info: 'STACS2027.PlanarSource.Packed.output_ringFormula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.output_ringFormula

/-- info: 'STACS2027.PlanarSource.Packed.blockOccurrences_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.blockOccurrences_variables

/-- info: 'STACS2027.PlanarSource.Packed.map_eq_of_mem_zip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.map_eq_of_mem_zip

/-- info: 'STACS2027.PlanarSource.Packed.cellPositions_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.cellPositions_eq

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cellOccurrences_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cellOccurrences_variables

/-- info: 'STACS2027.PlanarSource.Packed.Layout.cell_zip_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.cell_zip_position

/-- info: 'STACS2027.PlanarSource.Packed.Layout.startOccurrences_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.startOccurrences_variables

/-- info: 'STACS2027.PlanarSource.Packed.Layout.start_zip_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.start_zip_position

/-- info: 'STACS2027.PlanarSource.Packed.Layout.endOccurrences_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.endOccurrences_variables

/-- info: 'STACS2027.PlanarSource.Packed.Layout.end_zip_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.end_zip_position

/-- info: 'STACS2027.PlanarSource.Packed.rainbowEndpoint' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.rainbowEndpoint

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbowOccurrences_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbowOccurrences_variables

/-- info: 'STACS2027.PlanarSource.Packed.Layout.rainbow_zip_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Layout.rainbow_zip_position

/-- info: 'STACS2027.PlanarSource.Packed.Index.BlockAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.BlockAt

/-- info: 'STACS2027.PlanarSource.Packed.Index.BlockAt.append_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.BlockAt.append_left

/-- info: 'STACS2027.PlanarSource.Packed.Index.BlockAt.append_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.BlockAt.append_right

/-- info: 'STACS2027.PlanarSource.Packed.Index.BlockAt.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.BlockAt.trans

/-- info: 'STACS2027.PlanarSource.Packed.Index.reverse_range_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.reverse_range_split

/-- info: 'STACS2027.PlanarSource.Packed.Index.reverse_range_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarSource.Packed.Index.reverse_range_block
