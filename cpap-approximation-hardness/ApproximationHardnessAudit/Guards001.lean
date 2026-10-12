module

import all ApproximationHardness

/-!
Exact-message axiom guards for every explicitly named ApproximationHardness declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem_loopFree

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem_size

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem_values

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem_spec

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem_frame

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem_rep

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem_tables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem_tables

/-- info: 'STACS2027.Embed.ForestData.mk_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mk_fork

/-- info: 'STACS2027.Embed.ForestData.open_in_D' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.open_in_D

/-- info: 'STACS2027.Embed.ForestData.keys_of_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.keys_of_vertex

/-- info: 'STACS2027.Embed.ForestData.zOf_mem_of_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.zOf_mem_of_three

/-- info: 'STACS2027.Embed.ForestData.item_down' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.item_down

/-- info: 'STACS2027.Embed.ForestData.item_back' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.item_back

/-- info: 'STACS2027.Embed.ForestData.id_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.id_node

/-- info: 'STACS2027.Embed.ForestData.id_dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.id_dart

/-- info: 'STACS2027.Embed.ForestData.child_depth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.child_depth

/-- info: 'STACS2027.Embed.ForestData.not_desc_child_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.not_desc_child_parent

/-- info: 'STACS2027.Embed.ForestData.sibling_no_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.sibling_no_chord

/-- info: 'STACS2027.Embed.ForestData.down_child_par' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.down_child_par

/-- info: 'STACS2027.Embed.ForestData.mk_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.mk_target

/-- info: 'STACS2027.Embed.ForestData.kind_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.kind_vertex

/-- info: 'STACS2027.Embed.ForestData.kind_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.kind_top

/-- info: 'STACS2027.Embed.ForestData.kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.kind

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryBounds_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryBounds_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryBounds_addr_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryBounds_addr_append

/-- info: 'STACS2027.Embed.PlanRAM.retainItem_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.retainItem_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.Context.slotHeader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.slotHeader

/-- info: 'STACS2027.Embed.PlanRAM.Context.slotCompare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.slotCompare

/-- info: 'STACS2027.Embed.PlanRAM.Context.partSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.partSlot

/-- info: 'STACS2027.Embed.PlanRAM.partSlot_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.partSlot_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryPrefix_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryPrefix_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.Context.ordinaryPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.ordinaryPrefix

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryPrefix_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryPrefix_reg

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryParts_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryParts_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryParts_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryParts_exec

/-- info: 'STACS2027.Embed.PlanRAM.PartSlots' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PartSlots

/-- info: 'STACS2027.Embed.PlanRAM.update_part_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.update_part_cell

/-- info: 'STACS2027.Embed.PlanRAM.clearParts_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.clearParts_mem

/-- info: 'STACS2027.Embed.PlanRAM.clearParts_slots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.clearParts_slots

/-- info: 'STACS2027.Embed.PlanRAM.retainItem_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.retainItem_mem

/-- info: 'STACS2027.Embed.PlanRAM.retainItem_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.retainItem_count

/-- info: 'STACS2027.Embed.PlanRAM.retainItem_slots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.retainItem_slots

/-- info: 'STACS2027.Embed.PlanRAM.part_cell_after_forest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.part_cell_after_forest

/-- info: 'STACS2027.Embed.PlanRAM.clearParts_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.clearParts_context

/-- info: 'STACS2027.Embed.PlanRAM.retainItem_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.retainItem_context

/-- info: 'STACS2027.Embed.PlanRAM.clearParts_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.clearParts_reg

/-- info: 'STACS2027.Embed.PlanRAM.retainItem_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.retainItem_reg

/-- info: 'STACS2027.Embed.PlanRAM.clearParts_mutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.clearParts_mutable

/-- info: 'STACS2027.Embed.PlanRAM.retainItem_mutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.retainItem_mutable

/-- info: 'STACS2027.Embed.PlanRAM.PartsState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PartsState

/-- info: 'STACS2027.Embed.PlanRAM.PartsState.readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PartsState.readOnly

/-- info: 'STACS2027.Embed.PlanRAM.PartsState.retain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PartsState.retain

/-- info: 'STACS2027.Embed.PlanRAM.slotHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.slotHeader

/-- info: 'STACS2027.Embed.PlanRAM.slotCompare' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.slotCompare

/-- info: 'STACS2027.Embed.PlanRAM.run_partSlot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.run_partSlot

/-- info: 'STACS2027.Embed.PlanRAM.slotHeader_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.slotHeader_state

/-- info: 'STACS2027.Embed.PlanRAM.slotCompare_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.slotCompare_state

/-- info: 'STACS2027.Embed.PlanRAM.slotCompare_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.slotCompare_values

/-- info: 'STACS2027.Embed.PlanRAM.cachedItem_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.cachedItem_state

/-- info: 'STACS2027.Embed.PlanRAM.partSlot_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.partSlot_state

/-- info: 'STACS2027.Embed.PlanRAM.scanPrefix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.scanPrefix

/-- info: 'STACS2027.Embed.PlanRAM.scanPrefix_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.scanPrefix_next

/-- info: 'STACS2027.Embed.PlanRAM.scanPrefix_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.scanPrefix_bound

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryPrefix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryPrefix

/-- info: 'STACS2027.Embed.PlanRAM.run_ordinaryParts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.run_ordinaryParts

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryPrefix_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryPrefix_state

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryParts_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryParts_scan

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryParts_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryParts_values

/-- info: 'STACS2027.Embed.PlanRAM.PartMemFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PartMemFrame

/-- info: 'STACS2027.Embed.PlanRAM.PartMemFrame.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PartMemFrame.trans

/-- info: 'STACS2027.Embed.PlanRAM.clearParts_memFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.clearParts_memFrame

/-- info: 'STACS2027.Embed.PlanRAM.retainItem_memFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.retainItem_memFrame

/-- info: 'STACS2027.Embed.PlanRAM.partSlot_memFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.partSlot_memFrame

/-- info: 'STACS2027.Embed.PlanRAM.partSlot_mutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.partSlot_mutable

/-- info: 'STACS2027.Embed.PlanRAM.partSlot_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.partSlot_context

/-- info: 'STACS2027.Embed.PlanRAM.partSlot_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.partSlot_reg

/-- info: 'STACS2027.Embed.PlanRAM.partSlot_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.partSlot_frame

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryParts_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryParts_reg

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryParts_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryParts_frame

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryParts_mutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryParts_mutable

/-- info: 'STACS2027.Embed.PlanRAM.postCopyPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyPre

/-- info: 'STACS2027.Embed.PlanRAM.postCopyBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyBody

/-- info: 'STACS2027.Embed.PlanRAM.postCopyLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyLoop

/-- info: 'STACS2027.Embed.PlanRAM.postCopyProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyProgram

/-- info: 'STACS2027.Embed.PlanRAM.postCopyBody_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyBody_loopFree

/-- info: 'STACS2027.Embed.PlanRAM.postCopyBody_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyBody_size

/-- info: 'STACS2027.Embed.PlanRAM.postCopyBody_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyBody_reg

/-- info: 'STACS2027.Embed.PlanRAM.postCopyBody_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyBody_mem

/-- info: 'STACS2027.Embed.PlanRAM.postCopyBody_advance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyBody_advance

/-- info: 'STACS2027.Embed.PlanRAM.postCopyBody_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyBody_out

/-- info: 'STACS2027.Embed.PlanRAM.postCopyBody_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyBody_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.PostCopyState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PostCopyState

/-- info: 'STACS2027.Embed.PlanRAM.PostCopyState.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PostCopyState.step

/-- info: 'STACS2027.Embed.PlanRAM.postCopyLoop_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyLoop_spec

/-- info: 'STACS2027.Embed.PlanRAM.postCopyProgram_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyProgram_reg

/-- info: 'STACS2027.Embed.PlanRAM.postCopyProgram_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopyProgram_spec

/-- info: 'STACS2027.Embed.PlanRAM.postCopy_context_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopy_context_spec

/-- info: 'STACS2027.Embed.PlanRAM.postCopy_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopy_compiled

/-- info: 'STACS2027.Embed.PlanRAM.postCopy_prefix_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.postCopy_prefix_frame

/-- info: 'STACS2027.Embed.PlanRAM.planStore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.planStore

/-- info: 'STACS2027.Embed.PlanRAM.zStore' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.zStore

/-- info: 'STACS2027.Embed.PlanRAM.planStore_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.planStore_raw

/-- info: 'STACS2027.Embed.PlanRAM.zStore_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.zStore_raw

/-- info: 'STACS2027.Embed.PlanRAM.Context' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context

/-- info: 'STACS2027.Embed.PlanRAM.Context.temp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.temp

/-- info: 'STACS2027.Embed.PlanRAM.Context.readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.readOnly

/-- info: 'STACS2027.Embed.PlanRAM.Context.memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.memory

/-- info: 'STACS2027.Embed.PlanRAM.Context.planStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.planStore

/-- info: 'STACS2027.Embed.PlanRAM.Context.zStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.zStore

/-- info: 'STACS2027.Embed.PlanRAM.planStore_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.planStore_exec

/-- info: 'STACS2027.Embed.PlanRAM.zStore_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.zStore_exec

/-- info: 'STACS2027.Embed.PlanRAM.MutableZero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.MutableZero

/-- info: 'STACS2027.Embed.PlanRAM.MutableZero.planStore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.MutableZero.planStore

/-- info: 'STACS2027.Embed.PlanRAM.MutableZero.zStore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.MutableZero.zStore

/-- info: 'STACS2027.Embed.PlanRAM.Context.readForest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.readForest

/-- info: 'STACS2027.Embed.PlanRAM.Context.cachedItem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.cachedItem

/-- info: 'STACS2027.Embed.PlanRAM.forest_parts_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.forest_parts_bound

/-- info: 'STACS2027.Embed.PlanRAM.forest_item_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.forest_item_bound

/-- info: 'STACS2027.Embed.PlanRAM.forest_post_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.forest_post_bound

/-- info: 'STACS2027.Embed.PlanRAM.initial_mutable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.initial_mutable

/-- info: 'STACS2027.Embed.PlanRAM.initial_rep_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.initial_rep_frame

/-- info: 'STACS2027.Embed.PlanRAM.compiled_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.compiled_tables

/-- info: 'STACS2027.Embed.PlanRAM.planTablesProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.planTablesProgram

/-- info: 'STACS2027.Embed.PlanRAM.planTablesProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.planTablesProgram_spec

/-- info: 'STACS2027.Embed.PlanRAM.topPrepare' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topPrepare

/-- info: 'STACS2027.Embed.PlanRAM.topHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topHead

/-- info: 'STACS2027.Embed.PlanRAM.topExtra' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topExtra

/-- info: 'STACS2027.Embed.PlanRAM.run_topParts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.run_topParts

/-- info: 'STACS2027.Embed.PlanRAM.topPrepare_regs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topPrepare_regs

/-- info: 'STACS2027.Embed.PlanRAM.topPrepare_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topPrepare_mem

/-- info: 'STACS2027.Embed.PlanRAM.topPrepare_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topPrepare_context

/-- info: 'STACS2027.Embed.PlanRAM.topHead_regs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topHead_regs

/-- info: 'STACS2027.Embed.PlanRAM.topHead_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topHead_mem

/-- info: 'STACS2027.Embed.PlanRAM.topHead_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topHead_context

/-- info: 'STACS2027.Embed.PlanRAM.topExtra_regs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topExtra_regs

/-- info: 'STACS2027.Embed.PlanRAM.topExtra_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topExtra_mem

/-- info: 'STACS2027.Embed.PlanRAM.topExtra_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topExtra_context

/-- info: 'STACS2027.Embed.PlanRAM.topHead_slots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topHead_slots

/-- info: 'STACS2027.Embed.PlanRAM.topExtra_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topExtra_slots

/-- info: 'STACS2027.Embed.PlanRAM.topCompletion_slots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topCompletion_slots

/-- info: 'STACS2027.Embed.PlanRAM.topParts_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts_reg

/-- info: 'STACS2027.Embed.PlanRAM.topParts_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts_context

/-- info: 'STACS2027.Embed.PlanRAM.ForestData.parts_top_nonroot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ForestData.parts_top_nonroot

/-- info: 'STACS2027.Embed.PlanRAM.topParts_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts_values

/-- info: 'STACS2027.Embed.PlanRAM.planStore_partFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.planStore_partFrame

/-- info: 'STACS2027.Embed.PlanRAM.topPrepare_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topPrepare_frame

/-- info: 'STACS2027.Embed.PlanRAM.topHead_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topHead_frame

/-- info: 'STACS2027.Embed.PlanRAM.topExtra_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topExtra_frame

/-- info: 'STACS2027.Embed.PlanRAM.topParts_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts_frame

/-- info: 'STACS2027.Embed.PlanRAM.topParts_mutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts_mutable

/-- info: 'STACS2027.Embed.PlanRAM.topParts_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts_out

/-- info: 'STACS2027.Embed.PlanRAM.clearTop_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.clearTop_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.topPrepare_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topPrepare_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.topHead_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topHead_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.topExtra_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topExtra_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.topParts_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts_loopFree

/-- info: 'STACS2027.Embed.PlanRAM.topParts_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts_size

/-- info: 'STACS2027.Embed.PlanRAM.topParts_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.topParts_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts_spec

/-- info: 'STACS2027.Embed.PlanRAM.vertexBounds_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexBounds_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep_addr_split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep_addr_split

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep_exec

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep_prefix

/-- info: 'STACS2027.Embed.PlanRAM.vertexTablesProgram_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTablesProgram_complete

/-- info: 'STACS2027.Embed.PlanRAM.VertexPrefix.nodeValues' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.VertexPrefix.nodeValues

/-- info: 'STACS2027.Embed.PlanRAM.vertexFrame_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexFrame_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.vertexFinish' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexFinish

/-- info: 'STACS2027.Embed.PlanRAM.run_vertexTableStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.run_vertexTableStep

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader_test

/-- info: 'STACS2027.Embed.PlanRAM.parts_nonrepresentative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.parts_nonrepresentative

/-- info: 'STACS2027.Embed.PlanRAM.VertexMemFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.VertexMemFrame

/-- info: 'STACS2027.Embed.PlanRAM.VertexEntry.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.VertexEntry.frame

/-- info: 'STACS2027.Embed.PlanRAM.storeVertexGroups' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.storeVertexGroups

/-- info: 'STACS2027.Embed.PlanRAM.vertexLookup' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexLookup

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.storeVertexGroups_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.storeVertexGroups_mem

/-- info: 'STACS2027.Embed.PlanRAM.storeVertexGroups_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.storeVertexGroups_reg

/-- info: 'STACS2027.Embed.PlanRAM.storeVertexGroups_top' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.storeVertexGroups_top

/-- info: 'STACS2027.Embed.PlanRAM.Context.storeVertexGroups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.storeVertexGroups

/-- info: 'STACS2027.Embed.PlanRAM.MutableZero.storeVertexGroups' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.MutableZero.storeVertexGroups

/-- info: 'STACS2027.Embed.PlanRAM.Context.vertexLookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.vertexLookup

/-- info: 'STACS2027.Embed.PlanRAM.vertexLookup_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexLookup_reg

/-- info: 'STACS2027.Embed.PlanRAM.vertexLookup_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexLookup_test

/-- info: 'STACS2027.Embed.PlanRAM.Context.vertexHeader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.Context.vertexHeader

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader_reg

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader_top' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader_top

/-- info: 'STACS2027.Embed.PlanRAM.clearParts_mem_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.clearParts_mem_frame

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader_mem_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader_mem_frame

/-- info: 'STACS2027.Embed.PlanRAM.MutableZero.vertexHeader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.MutableZero.vertexHeader

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeaderBounds_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeaderBounds_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.clearParts_plan_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.clearParts_plan_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.storeVertexGroups_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.storeVertexGroups_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.vertexLookup_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexLookup_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader_addrOK

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader_exec

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeaderValues_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeaderValues_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader_mem

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader_groups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader_groups

/-- info: 'STACS2027.Embed.PlanRAM.vertexHeader_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexHeader_empty

/-- info: 'STACS2027.Embed.PlanRAM.vertexLoop_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexLoop_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.VertexEntry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.VertexEntry

/-- info: 'STACS2027.Embed.PlanRAM.VertexEntry.mem_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.VertexEntry.mem_congr

/-- info: 'STACS2027.Embed.PlanRAM.VertexPrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.VertexPrefix

/-- info: 'STACS2027.Embed.PlanRAM.VertexPrefix.temp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.VertexPrefix.temp

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep_counters' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep_counters

/-- info: 'STACS2027.Embed.PlanRAM.vertexTablesProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTablesProgram_spec

/-- info: 'STACS2027.Embed.PlanRAM.exclusion' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.exclusion

/-- info: 'STACS2027.Embed.PlanRAM.representative' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.representative

/-- info: 'STACS2027.Embed.PlanRAM.constant' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.constant

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedSlot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedSlot

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedProgram

/-- info: 'STACS2027.Embed.PlanRAM.clearParts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.clearParts

/-- info: 'STACS2027.Embed.PlanRAM.retainItem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.retainItem

/-- info: 'STACS2027.Embed.PlanRAM.partSlot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.partSlot

/-- info: 'STACS2027.Embed.PlanRAM.ordinaryParts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.ordinaryParts

/-- info: 'STACS2027.Embed.PlanRAM.topParts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.topParts

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableBody

/-- info: 'STACS2027.Embed.PlanRAM.vertexTablesProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTablesProgram

/-- info: 'STACS2027.Embed.PlanRAM.distinguishedSlot_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.distinguishedSlot_loopFree

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep_loopFree

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep_size

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep_out

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep_reg_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep_reg_frame

/-- info: 'STACS2027.Embed.PlanRAM.vertexRefine_run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexRefine_run_skip

/-- info: 'STACS2027.Embed.PlanRAM.PartMemFrame.groupCell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PartMemFrame.groupCell

/-- info: 'STACS2027.Embed.PlanRAM.PartMemFrame.cacheCell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PartMemFrame.cacheCell

/-- info: 'STACS2027.Embed.PlanRAM.PartMemFrame.otherCell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PartMemFrame.otherCell

/-- info: 'STACS2027.Embed.PlanRAM.PartMemFrame.otherSlots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.PartMemFrame.otherSlots

/-- info: 'STACS2027.Embed.PlanRAM.vertexTableStep_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.PlanRAM.vertexTableStep_values

/-- info: 'STACS2027.Embed.Item' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Item

/-- info: 'STACS2027.Embed.Plan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan

/-- info: 'STACS2027.Embed.nodup_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.nodup_one

/-- info: 'STACS2027.Embed.flatMap_congr'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.flatMap_congr'

/-- info: 'STACS2027.Embed.Plan.ord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.ord

/-- info: 'STACS2027.Embed.Plan.W' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.W

/-- info: 'STACS2027.Embed.Plan.partW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.partW

/-- info: 'STACS2027.Embed.Plan.mem_ord' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.mem_ord

/-- info: 'STACS2027.Embed.Plan.W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.W_eq

/-- info: 'STACS2027.Embed.Plan.W_of_ord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.W_of_ord

/-- info: 'STACS2027.Embed.Plan.mem_W' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.mem_W

/-- info: 'STACS2027.Embed.Plan.D' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.D

/-- info: 'STACS2027.Embed.Plan.ID' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.ID

/-- info: 'STACS2027.Embed.Plan.mem_W_D' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.mem_W_D

/-- info: 'STACS2027.Embed.Plan.mem_partW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.mem_partW

/-- info: 'STACS2027.Embed.Plan.mem_D' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.mem_D

/-- info: 'STACS2027.Embed.Plan.IsTarget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.IsTarget

/-- info: 'STACS2027.Embed.Plan.IsFork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.IsFork

/-- info: 'STACS2027.Embed.Plan.Kind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.Kind

/-- info: 'STACS2027.Embed.Plan.Placed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.Placed

/-- info: 'STACS2027.Embed.Plan.ForkOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.ForkOK

/-- info: 'STACS2027.Embed.Plan.ord_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.ord_nil

/-- info: 'STACS2027.Embed.Plan.ord_one' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.ord_one

/-- info: 'STACS2027.Embed.Plan.ord_two' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.ord_two

/-- info: 'STACS2027.Embed.Plan.W_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.W_pair

/-- info: 'STACS2027.Embed.Plan.W_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.W_single

/-- info: 'STACS2027.Embed.Plan.mem_openEnds_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.mem_openEnds_congr

/-- info: 'STACS2027.Embed.Plan.openEnds_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.openEnds_singleton

/-- info: 'STACS2027.Embed.Plan.eq_cons_of_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.eq_cons_of_first

/-- info: 'STACS2027.Embed.Plan.eq_snoc_of_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.eq_snoc_of_last

/-- info: 'STACS2027.Embed.Plan.dart_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.dart_good

/-- info: 'STACS2027.Embed.Plan.W_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.W_nodup

/-- info: 'STACS2027.Embed.Plan.suff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.suff

/-- info: 'STACS2027.Embed.Plan.sides0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.sides0

/-- info: 'STACS2027.Embed.Plan.Below' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.Below

/-- info: 'STACS2027.Embed.Plan.nec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.nec

/-- info: 'STACS2027.Embed.Plan.forkOK_of_valley' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.forkOK_of_valley

/-- info: 'STACS2027.Embed.Plan.nec_forkOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.nec_forkOK

/-- info: 'STACS2027.Embed.Plan.not_target_and_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.not_target_and_fork

/-- info: 'STACS2027.Embed.Plan.exists_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.exists_placed

/-- info: 'STACS2027.Embed.planarEmbeddingProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.planarEmbeddingProgram

/-- info: 'STACS2027.Embed.planarEmbeddingProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.planarEmbeddingProgram_spec

/-- info: 'STACS2027.Embed.planarEmbeddingProgram_space' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.planarEmbeddingProgram_space

/-- info: 'STACS2027.Embed.planarEmbedding_linear_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.planarEmbedding_linear_ram

/-- info: 'STACS2027.Embed.RAMSolver.readoutHeader_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readoutHeader_ready

/-- info: 'STACS2027.Embed.RAMSolver.encodedBit_evalBit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.encodedBit_evalBit

/-- info: 'STACS2027.Embed.RAMSolver.readoutHeader_rotationValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readoutHeader_rotationValue

/-- info: 'STACS2027.Embed.cnext_append_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.cnext_append_comm

/-- info: 'STACS2027.Embed.ForestData.rotInvN_choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.rotInvN_choice

/-- info: 'STACS2027.Embed.RAMSolver.readoutRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readoutRegisters

/-- info: 'STACS2027.Embed.RAMSolver.ReadoutFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ReadoutFrame

/-- info: 'STACS2027.Embed.RAMSolver.ReadoutFrame.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ReadoutFrame.refl

/-- info: 'STACS2027.Embed.RAMSolver.ReadoutFrame.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ReadoutFrame.step

/-- info: 'STACS2027.Embed.RAMSolver.rotationValue_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationValue_frame

/-- info: 'STACS2027.Embed.RAMSolver.ReadoutReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ReadoutReady

/-- info: 'STACS2027.Embed.RAMSolver.ReadoutReady.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ReadoutReady.frame

/-- info: 'STACS2027.Embed.RAMSolver.rotationStep_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationStep_ready

/-- info: 'STACS2027.Embed.RAMSolver.rotationLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationLoop_spec

/-- info: 'STACS2027.Embed.RAMSolver.rotationValue_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationValue_correct

/-- info: 'STACS2027.Embed.RAMSolver.rotationLoop_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationLoop_planar

/-- info: 'STACS2027.Embed.RAMSolver.codeCase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.codeCase

/-- info: 'STACS2027.Embed.RAMSolver.difference_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.difference_zero

/-- info: 'STACS2027.Embed.RAMSolver.both_differences_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.both_differences_zero

/-- info: 'STACS2027.Embed.RAMSolver.loadOrientation' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.loadOrientation

/-- info: 'STACS2027.Embed.RAMSolver.negateOrientation' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.negateOrientation

/-- info: 'STACS2027.Embed.RAMSolver.encodedBit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.encodedBit

/-- info: 'STACS2027.Embed.RAMSolver.codeBit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.codeBit

/-- info: 'STACS2027.Embed.RAMSolver.codeBit_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.codeBit_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.codeBit_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.codeBit_value

/-- info: 'STACS2027.Embed.RAMSolver.codeBit_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.codeBit_mem

/-- info: 'STACS2027.Embed.RAMSolver.codeBit_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.codeBit_out

/-- info: 'STACS2027.Embed.RAMSolver.codeBit_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.codeBit_reg

/-- info: 'STACS2027.Embed.RAMSolver.codeBit_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.codeBit_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.readVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readVertex

/-- info: 'STACS2027.Embed.RAMSolver.writeRotation' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.writeRotation

/-- info: 'STACS2027.Embed.RAMSolver.rotationStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationStep

/-- info: 'STACS2027.Embed.RAMSolver.rotationLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationLoop

/-- info: 'STACS2027.Embed.RAMSolver.readVertex_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readVertex_value

/-- info: 'STACS2027.Embed.RAMSolver.readVertex_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readVertex_mem

/-- info: 'STACS2027.Embed.RAMSolver.readVertex_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readVertex_out

/-- info: 'STACS2027.Embed.RAMSolver.readVertex_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.readVertex_reg

/-- info: 'STACS2027.Embed.RAMSolver.writeRotation_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.writeRotation_out

/-- info: 'STACS2027.Embed.RAMSolver.writeRotation_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.writeRotation_mem

/-- info: 'STACS2027.Embed.RAMSolver.writeRotation_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.writeRotation_reg

/-- info: 'STACS2027.Embed.RAMSolver.writeRotation_advance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.writeRotation_advance

/-- info: 'STACS2027.Embed.RAMSolver.rotationStep_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationStep_mem

/-- info: 'STACS2027.Embed.RAMSolver.rotationStep_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationStep_reg

/-- info: 'STACS2027.Embed.RAMSolver.rotationStep_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationStep_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.rotationValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationValue

/-- info: 'STACS2027.Embed.RAMSolver.rotationStep_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationStep_out

/-- info: 'STACS2027.Embed.RAMSolver.rotationStep_advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationStep_advance

/-- info: 'STACS2027.Embed.RAMSolver.rotationStep_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rotationStep_addrOK

/-- info: 'STACS2027.Embed.SMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.SMem

/-- info: 'STACS2027.Embed.SMS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.SMS

/-- info: 'STACS2027.Embed.SMem.store' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.SMem.store

/-- info: 'STACS2027.Embed.appL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.appL

/-- info: 'STACS2027.Embed.Sol.khM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.khM

/-- info: 'STACS2027.Embed.Sol.gtopM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.gtopM

/-- info: 'STACS2027.Embed.Sol.itRes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.itRes

/-- info: 'STACS2027.Embed.Sol.tgtOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.tgtOf

/-- info: 'STACS2027.Embed.Sol.tcode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.tcode

/-- info: 'STACS2027.Embed.Sol.closeM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.closeM

/-- info: 'STACS2027.Embed.Sol.forkStart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkStart

/-- info: 'STACS2027.Embed.Sol.twoStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.twoStep

/-- info: 'STACS2027.Embed.Sol.nodeStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.nodeStep

/-- info: 'STACS2027.Embed.Sol.popStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popStep

/-- info: 'STACS2027.Embed.Sol.consStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consStep

/-- info: 'STACS2027.Embed.Sol.mstep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mstep

/-- info: 'STACS2027.Embed.Grp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Grp

/-- info: 'STACS2027.Embed.Res' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Res

/-- info: 'STACS2027.Embed.Grp.els' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Grp.els

/-- info: 'STACS2027.Embed.els' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.els

/-- info: 'STACS2027.Embed.Sol' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol

/-- info: 'STACS2027.Embed.Sol.kh' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.kh

/-- info: 'STACS2027.Embed.Sol.gtop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.gtop

/-- info: 'STACS2027.Embed.Sol.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.empty

/-- info: 'STACS2027.Embed.Sol.dartRes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.dartRes

/-- info: 'STACS2027.Embed.Sol.closeRes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.closeRes

/-- info: 'STACS2027.Embed.Sol.upC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.upC

/-- info: 'STACS2027.Embed.Sol.loC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.loC

/-- info: 'STACS2027.Embed.Sol.popped' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popped

/-- info: 'STACS2027.Embed.Sol.rest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.rest

/-- info: 'STACS2027.Embed.Sol.mergeRes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeRes

/-- info: 'STACS2027.Embed.Sol.forkRes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkRes

/-- info: 'STACS2027.Embed.Sol.twoRes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.twoRes

/-- info: 'STACS2027.Embed.Sol.solve' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.solve

/-- info: 'STACS2027.Embed.Sol.rpart' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.rpart

/-- info: 'STACS2027.Embed.Sol.rpart_guard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.rpart_guard

/-- info: 'STACS2027.Embed.Sol.solve_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.solve_eq

/-- info: 'STACS2027.Embed.Sol.solve_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.solve_nil

/-- info: 'STACS2027.Embed.Sol.solve_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.solve_one

/-- info: 'STACS2027.Embed.Sol.solve_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.solve_two

/-- info: 'STACS2027.Embed.Sol.mergeCons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeCons

/-- info: 'STACS2027.Embed.Sol.forkCons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkCons

/-- info: 'STACS2027.Embed.Sol.twoCons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.twoCons

/-- info: 'STACS2027.Embed.Sol.consAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consAt

/-- info: 'STACS2027.Embed.Sol.Consistent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Consistent

/-- info: 'STACS2027.Embed.Sol.forkBit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkBit

/-- info: 'STACS2027.Embed.Sol.twoBit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.twoBit

/-- info: 'STACS2027.Embed.Sol.bit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.bit

/-- info: 'STACS2027.Embed.Sol.runPrefix_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.runPrefix_bits

/-- info: 'STACS2027.Embed.RAMSolver.MemoryBounds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.MemoryBounds

/-- info: 'STACS2027.Embed.RAMSolver.StateBounds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.StateBounds

/-- info: 'STACS2027.Embed.RAMSolver.StateBounds.stepBounds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.StateBounds.stepBounds

/-- info: 'STACS2027.Embed.RAMSolver.appL_bounded' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appL_bounded

/-- info: 'STACS2027.Embed.RAMSolver.popStep_bounded' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStep_bounded

/-- info: 'STACS2027.Embed.RAMSolver.consStep_bounded' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consStep_bounded

/-- info: 'STACS2027.Embed.RAMSolver.CloseAddressOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.CloseAddressOK

/-- info: 'STACS2027.Embed.RAMSolver.closeResultProgram_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.closeResultProgram_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.CloseAddressOK.ofRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.CloseAddressOK.ofRep

/-- info: 'STACS2027.Embed.RAMSolver.closeResultProgram_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.closeResultProgram_size

/-- info: 'STACS2027.Embed.RAMSolver.closeResultProgram_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.closeResultProgram_exec

/-- info: 'STACS2027.Embed.RAMSolver.difference_pair_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.difference_pair_zero

/-- info: 'STACS2027.Embed.RAMSolver.symmetric_difference_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.symmetric_difference_zero

/-- info: 'STACS2027.Embed.RAMSolver.closeResultProgram_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.closeResultProgram_raw

/-- info: 'STACS2027.Embed.RAMSolver.closeResultProgram_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.closeResultProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.solverBudgetProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverBudgetProgram

/-- info: 'STACS2027.Embed.RAMSolver.solverProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverProgram

/-- info: 'STACS2027.Embed.RAMSolver.solverBudgetProgram_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverBudgetProgram_raw

/-- info: 'STACS2027.Embed.RAMSolver.solverBudgetProgram_rep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverBudgetProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.solverBudgetProgram_exec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverBudgetProgram_exec

/-- info: 'STACS2027.Embed.RAMSolver.solverProgram_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverProgram_refines

/-- info: 'STACS2027.Embed.RAMSolver.orderForkProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orderForkProgram

/-- info: 'STACS2027.Embed.RAMSolver.itemResultInto_reg_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itemResultInto_reg_frame

/-- info: 'STACS2027.Embed.RAMSolver.orderForkProgram_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orderForkProgram_raw

/-- info: 'STACS2027.Embed.RAMSolver.orderForkProgram_rep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orderForkProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.orderForkProgram_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orderForkProgram_exec

/-- info: 'STACS2027.Embed.RAMSolver.run_forkNodeProgram' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.run_forkNodeProgram

/-- info: 'STACS2027.Embed.RAMSolver.forkResultProgram_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forkResultProgram_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.storeNodeResult_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.storeNodeResult_rep

/-- info: 'STACS2027.Embed.RAMSolver.storeNodeResult_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.storeNodeResult_size

/-- info: 'STACS2027.Embed.RAMSolver.storeNodeResult_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.storeNodeResult_exec

/-- info: 'STACS2027.Embed.RAMSolver.beginForkProgram_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.beginForkProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.beginForkProgram_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.beginForkProgram_exec

/-- info: 'STACS2027.Embed.RAMSolver.forkResultProgram_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forkResultProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.forkResultProgram_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forkResultProgram_exec

/-- info: 'STACS2027.Embed.RAMSolver.forkNodeProgram_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forkNodeProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.forkNodeProgram_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forkNodeProgram_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.forkNodeProgram_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forkNodeProgram_exec

/-- info: 'STACS2027.Embed.RAMSolver.TableMemEq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.TableMemEq

/-- info: 'STACS2027.Embed.RAMSolver.TableMemEq.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.TableMemEq.refl

/-- info: 'STACS2027.Embed.RAMSolver.TableMemEq.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.TableMemEq.trans

/-- info: 'STACS2027.Embed.RAMSolver.TableMemEq.update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.TableMemEq.update

/-- info: 'STACS2027.Embed.RAMSolver.TableMemEq.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.TableMemEq.append

/-- info: 'STACS2027.Embed.RAMSolver.Tables.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Tables.frame

/-- info: 'STACS2027.Embed.Plan.Below.ht_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.Below.ht_le

/-- info: 'STACS2027.Embed.Plan.Below.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.Below.trans

/-- info: 'STACS2027.Embed.Plan.below_child' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.below_child

/-- info: 'STACS2027.Embed.Plan.Below.first' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.Below.first

/-- info: 'STACS2027.Embed.Plan.below_cases' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.below_cases

/-- info: 'STACS2027.Embed.Plan.mem_D_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.mem_D_below

/-- info: 'STACS2027.Embed.Plan.D_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.D_mono

/-- info: 'STACS2027.Embed.Sol.Tree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree

/-- info: 'STACS2027.Embed.Sol.Own' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Own

/-- info: 'STACS2027.Embed.Sol.OwnIt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.OwnIt

/-- info: 'STACS2027.Embed.Sol.gids' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.gids

/-- info: 'STACS2027.Embed.Sol.own_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.own_below

/-- info: 'STACS2027.Embed.Sol.ownIt_own' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.ownIt_own

/-- info: 'STACS2027.Embed.Sol.Tree.chain' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.chain

/-- info: 'STACS2027.Embed.Sol.Tree.own_cmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.own_cmp

/-- info: 'STACS2027.Embed.Sol.Tree.not_below_sibling' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.not_below_sibling

/-- info: 'STACS2027.Embed.Sol.Tree.gid_not_ownIt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.gid_not_ownIt

/-- info: 'STACS2027.Embed.Sol.Tree.fork_disj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.fork_disj

/-- info: 'STACS2027.Embed.Sol.gids_close_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.gids_close_sub

/-- info: 'STACS2027.Embed.Sol.gids_merge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.gids_merge

/-- info: 'STACS2027.Embed.Sol.gids_rest_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.gids_rest_sub

/-- info: 'STACS2027.Embed.Sol.gids_popped_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.gids_popped_sub

/-- info: 'STACS2027.Embed.Sol.mergeCons_ids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeCons_ids

/-- info: 'STACS2027.Embed.Sol.Tree.rpart_own' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.rpart_own

/-- info: 'STACS2027.Embed.Sol.Tree.gids_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.gids_ok

/-- info: 'STACS2027.Embed.Sol.Tree.rpart_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.rpart_ok

/-- info: 'STACS2027.Embed.Sol.Good.fork_of_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.fork_of_cons

/-- info: 'STACS2027.Embed.Sol.Tree.cons_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.cons_ok

/-- info: 'STACS2027.Embed.Sol.Tree.ids_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.ids_sub

/-- info: 'STACS2027.Embed.Sol.Tree.parts_disj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.parts_disj

/-- info: 'STACS2027.Embed.Sol.Tree.cons_own' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.cons_own

/-- info: 'STACS2027.Embed.Sol.Tree.gone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.gone

/-- info: 'STACS2027.Embed.Sol.eq_of_mem_nodup_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.eq_of_mem_nodup_map

/-- info: 'STACS2027.Embed.Sol.Tree.consumed_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.consumed_unique

/-- info: 'STACS2027.Embed.Sol.Tree.consumed_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.consumed_below

/-- info: 'STACS2027.Embed.RAMSolver.itRes_ia' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itRes_ia

/-- info: 'STACS2027.Embed.RAMSolver.closeM_ia' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.closeM_ia

/-- info: 'STACS2027.Embed.RAMSolver.forkStart_ia' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forkStart_ia

/-- info: 'STACS2027.Embed.RAMSolver.tgtOf_dart_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.tgtOf_dart_mem

/-- info: 'STACS2027.Embed.RAMSolver.twoStep_ia_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.twoStep_ia_bound

/-- info: 'STACS2027.Embed.RAMSolver.nodeStep_ia_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nodeStep_ia_bound

/-- info: 'STACS2027.Embed.RAMSolver.mstep_ia_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstep_ia_bound

/-- info: 'STACS2027.Embed.RAMSolver.iterate_ia_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.iterate_ia_bound

/-- info: 'STACS2027.Embed.RAMSolver.solver_final_ia_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solver_final_ia_bound

/-- info: 'STACS2027.Embed.RAMSolver.initialMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.initialMem

/-- info: 'STACS2027.Embed.RAMSolver.initialState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.initialState

/-- info: 'STACS2027.Embed.RAMSolver.solverInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverInit

/-- info: 'STACS2027.Embed.RAMSolver.solverInit_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverInit_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.solverInit_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverInit_size

/-- info: 'STACS2027.Embed.RAMSolver.solverInit_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverInit_frame

/-- info: 'STACS2027.Embed.RAMSolver.solverInit_bases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverInit_bases

/-- info: 'STACS2027.Embed.RAMSolver.solverInit_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverInit_rep

/-- info: 'STACS2027.Embed.RAMSolver.solverInit_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverInit_tables

/-- info: 'STACS2027.Embed.RAMSolver.initialState_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.initialState_bounds

/-- info: 'STACS2027.Embed.RAMSolver.solverInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverInit_spec

/-- info: 'STACS2027.Embed.mem_els' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.mem_els

/-- info: 'STACS2027.Embed.els_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.els_nil

/-- info: 'STACS2027.Embed.els_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.els_cons

/-- info: 'STACS2027.Embed.els_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.els_append

/-- info: 'STACS2027.Embed.mem_gels' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.mem_gels

/-- info: 'STACS2027.Embed.Sol.Desc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Desc

/-- info: 'STACS2027.Embed.Sol.Core' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Core

/-- info: 'STACS2027.Embed.Sol.Inv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Inv

/-- info: 'STACS2027.Embed.Sol.Desc.nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Desc.nodup

/-- info: 'STACS2027.Embed.Sol.Desc.sub' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Desc.sub

/-- info: 'STACS2027.Embed.Sol.desc_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.desc_append

/-- info: 'STACS2027.Embed.Sol.desc_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.desc_flatMap

/-- info: 'STACS2027.Embed.Sol.kh_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.kh_ge

/-- info: 'STACS2027.Embed.Sol.kh_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.kh_mem

/-- info: 'STACS2027.Embed.Sol.kh_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.kh_nil

/-- info: 'STACS2027.Embed.Sol.le_gtop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.le_gtop

/-- info: 'STACS2027.Embed.Sol.gtop_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.gtop_mem

/-- info: 'STACS2027.Embed.Sol.head_of_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.head_of_max

/-- info: 'STACS2027.Embed.Sol.core_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.core_nil

/-- info: 'STACS2027.Embed.Sol.Core.tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Core.tail

/-- info: 'STACS2027.Embed.Sol.Core.suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Core.suffix

/-- info: 'STACS2027.Embed.Sol.Core.prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Core.prefix

/-- info: 'STACS2027.Embed.Sol.core_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.core_cons

/-- info: 'STACS2027.Embed.Sol.grp_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.grp_nodup

/-- info: 'STACS2027.Embed.Sol.Core.nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Core.nodup

/-- info: 'STACS2027.Embed.Sol.Core.gtop_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Core.gtop_lt

/-- info: 'STACS2027.Embed.Sol.Core.lt_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Core.lt_of_mem

/-- info: 'STACS2027.Embed.Sol.inv_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.inv_empty

/-- info: 'STACS2027.Embed.Sol.inv_dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.inv_dart

/-- info: 'STACS2027.Embed.Sol.closeRes_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.closeRes_cons

/-- info: 'STACS2027.Embed.Sol.mem_tail_of_nodup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mem_tail_of_nodup

/-- info: 'STACS2027.Embed.Sol.inv_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.inv_close

/-- info: 'STACS2027.Embed.Sol.LRC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.LRC

/-- info: 'STACS2027.Embed.Sol.mem_takeWhile_imp'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mem_takeWhile_imp'

/-- info: 'STACS2027.Embed.Sol.popped_append_rest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popped_append_rest

/-- info: 'STACS2027.Embed.Sol.lt_gtop_of_popped' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.lt_gtop_of_popped

/-- info: 'STACS2027.Embed.Sol.gtop_le_of_rest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.gtop_le_of_rest

/-- info: 'STACS2027.Embed.Sol.mem_upC_loC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mem_upC_loC

/-- info: 'STACS2027.Embed.Sol.upC_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.upC_sub

/-- info: 'STACS2027.Embed.Sol.loC_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.loC_sub

/-- info: 'STACS2027.Embed.Sol.desc_upC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.desc_upC

/-- info: 'STACS2027.Embed.Sol.desc_loC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.desc_loC

/-- info: 'STACS2027.Embed.Sol.side_upC_loC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.side_upC_loC

/-- info: 'STACS2027.Embed.Sol.upC_reaches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.upC_reaches

/-- info: 'STACS2027.Embed.Sol.els_merge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.els_merge

/-- info: 'STACS2027.Embed.Sol.low_merge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.low_merge

/-- info: 'STACS2027.Embed.Sol.MergeFacts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.MergeFacts

/-- info: 'STACS2027.Embed.Sol.merge_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.merge_facts

/-- info: 'STACS2027.Embed.Sol.inv_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.inv_merge

/-- info: 'STACS2027.Embed.Sol.lrc_of_vr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.lrc_of_vr

/-- info: 'STACS2027.Embed.Sol.vr_of_lrc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.vr_of_lrc

/-- info: 'STACS2027.Embed.Sol.Inv.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Inv.congr

/-- info: 'STACS2027.Embed.Sol.Inv.low_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Inv.low_le

/-- info: 'STACS2027.Embed.Sol.Inv.low_lt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Inv.low_lt

/-- info: 'STACS2027.Embed.Sol.Inv.empty_of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Inv.empty_of

/-- info: 'STACS2027.Embed.Sol.Inv.low_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Inv.low_eq

/-- info: 'STACS2027.Embed.Sol.inv_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.inv_fork

/-- info: 'STACS2027.Embed.Sol.OInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.OInv

/-- info: 'STACS2027.Embed.Sol.oinv_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.oinv_nil

/-- info: 'STACS2027.Embed.Sol.oinv_dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.oinv_dart

/-- info: 'STACS2027.Embed.Sol.oinv_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.oinv_close

/-- info: 'STACS2027.Embed.Sol.oinv_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.oinv_merge

/-- info: 'STACS2027.Embed.RAMSolver.ItemAddressOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ItemAddressOK

/-- info: 'STACS2027.Embed.RAMSolver.itemResultInto_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itemResultInto_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.itemResultInto_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itemResultInto_size

/-- info: 'STACS2027.Embed.RAMSolver.ItemAddressOK.ofRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ItemAddressOK.ofRep

/-- info: 'STACS2027.Embed.RAMSolver.itemResultInto_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itemResultInto_exec

/-- info: 'STACS2027.Embed.RAMSolver.Rep.transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Rep.transfer

/-- info: 'STACS2027.Embed.RAMSolver.itemResultInto_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itemResultInto_rep

/-- info: 'STACS2027.Embed.RAMSolver.solverBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverBody

/-- info: 'STACS2027.Embed.RAMSolver.solverLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverLoop

/-- info: 'STACS2027.Embed.RAMSolver.Rep.high' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Rep.high

/-- info: 'STACS2027.Embed.RAMSolver.mstepProgram_reg_high' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstepProgram_reg_high

/-- info: 'STACS2027.Embed.RAMSolver.mstepProgram_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstepProgram_out

/-- info: 'STACS2027.Embed.RAMSolver.boundedRun_memAbove' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.boundedRun_memAbove

/-- info: 'STACS2027.Embed.RAMSolver.solverLoop_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverLoop_refines

/-- info: 'STACS2027.Embed.Plan.mem_ID_dart' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.mem_ID_dart

/-- info: 'STACS2027.Embed.Plan.mem_ID_node' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.mem_ID_node

/-- info: 'STACS2027.Embed.Plan.openEnds_dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.openEnds_dart

/-- info: 'STACS2027.Embed.Plan.openEnds_D_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.openEnds_D_nil

/-- info: 'STACS2027.Embed.Plan.openEnds_D_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.openEnds_D_one

/-- info: 'STACS2027.Embed.Plan.openEnds_D_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.openEnds_D_target

/-- info: 'STACS2027.Embed.Plan.openEnds_D_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Plan.openEnds_D_fork

/-- info: 'STACS2027.Embed.Sol.Good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good

/-- info: 'STACS2027.Embed.Sol.forkOK_ab' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkOK_ab

/-- info: 'STACS2027.Embed.Sol.Good.twoRes_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.twoRes_fork

/-- info: 'STACS2027.Embed.Sol.Good.twoCons_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.twoCons_fork

/-- info: 'STACS2027.Embed.Sol.Good.twoBit_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.twoBit_fork

/-- info: 'STACS2027.Embed.Sol.Good.solve_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.solve_target

/-- info: 'STACS2027.Embed.Sol.Good.consAt_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.consAt_target

/-- info: 'STACS2027.Embed.Sol.Good.rpart_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.rpart_inv

/-- info: 'STACS2027.Embed.Sol.Good.solve_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.solve_inv

/-- info: 'STACS2027.Embed.Sol.lrc_of_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.lrc_of_fork

/-- info: 'STACS2027.Embed.Sol.Good.rpart_oinv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.rpart_oinv

/-- info: 'STACS2027.Embed.Sol.Good.solve_oinv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.solve_oinv

/-- info: 'STACS2027.Embed.Sol.Good.ord_bit_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.ord_bit_two

/-- info: 'STACS2027.Embed.Sol.Good.placed_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.placed_all

/-- info: 'STACS2027.Embed.Sol.Good.wn_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Good.wn_all

/-- info: 'STACS2027.Embed.RAMSolver.FloorReady' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.FloorReady

/-- info: 'STACS2027.Embed.RAMSolver.floorPlan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.floorPlan

/-- info: 'STACS2027.Embed.RAMSolver.floorReady_setReg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.floorReady_setReg

/-- info: 'STACS2027.Embed.RAMSolver.floorReady_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.floorReady_add

/-- info: 'STACS2027.Embed.RAMSolver.floorPlan_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.floorPlan_exec

/-- info: 'STACS2027.Embed.RAMSolver.solverFloorRegisters' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverFloorRegisters

/-- info: 'STACS2027.Embed.RAMSolver.solverProgram_floor_certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverProgram_floor_certificate

/-- info: 'STACS2027.Embed.RAMSolver.solverFloorReady' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverFloorReady

/-- info: 'STACS2027.Embed.RAMSolver.solverProgram_memBelow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.solverProgram_memBelow

/-- info: 'STACS2027.Embed.Sol.mergeRows' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeRows

/-- info: 'STACS2027.Embed.Sol.mergeState_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeState_records

/-- info: 'STACS2027.Embed.Sol.mergeRows_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.mergeRows_perm

/-- info: 'STACS2027.Embed.Sol.writeParents_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.writeParents_other

/-- info: 'STACS2027.Embed.Sol.writeFlips_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.writeFlips_other

/-- info: 'STACS2027.Embed.Sol.writeParents_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.writeParents_mem

/-- info: 'STACS2027.Embed.Sol.writeFlips_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.writeFlips_mem

/-- info: 'STACS2027.Embed.Sol.finishRows' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.finishRows

/-- info: 'STACS2027.Embed.Sol.finishRows_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.finishRows_perm

/-- info: 'STACS2027.Embed.Sol.forkFinish_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkFinish_records

/-- info: 'STACS2027.Embed.RAMSolver.mstepProgram_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstepProgram_simulation

/-- info: 'STACS2027.Embed.RAMSolver.MemoryBounds.store' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.MemoryBounds.store

/-- info: 'STACS2027.Embed.RAMSolver.MemoryBounds.inf_frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.MemoryBounds.inf_frame

/-- info: 'STACS2027.Embed.RAMSolver.MemoryBounds.ia_frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.MemoryBounds.ia_frame

/-- info: 'STACS2027.Embed.RAMSolver.MemoryBounds.itRes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.MemoryBounds.itRes

/-- info: 'STACS2027.Embed.RAMSolver.MemoryBounds.closeM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.MemoryBounds.closeM

/-- info: 'STACS2027.Embed.RAMSolver.StateBounds.forkStart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.StateBounds.forkStart

/-- info: 'STACS2027.Embed.RAMSolver.StateBounds.twoStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.StateBounds.twoStep

/-- info: 'STACS2027.Embed.RAMSolver.StateBounds.nodeStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.StateBounds.nodeStep

/-- info: 'STACS2027.Embed.RAMSolver.mstep_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstep_bounded

/-- info: 'STACS2027.Embed.RAMSolver.nodeStep_index' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nodeStep_index

/-- info: 'STACS2027.Embed.RAMSolver.mstep_index_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstep_index_le

/-- info: 'STACS2027.Embed.RAMSolver.mstep_iterate_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstep_iterate_bounded

/-- info: 'STACS2027.Embed.RAMSolver.mstep_iterate_index_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstep_iterate_index_le

/-- info: 'STACS2027.Embed.RAMSolver.itemResultInto' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itemResultInto

/-- info: 'STACS2027.Embed.RAMSolver.storeNodeResult' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.storeNodeResult

/-- info: 'STACS2027.Embed.RAMSolver.leafNodeProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.leafNodeProgram

/-- info: 'STACS2027.Embed.RAMSolver.singleNodeProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.singleNodeProgram

/-- info: 'STACS2027.Embed.RAMSolver.beginForkProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.beginForkProgram

/-- info: 'STACS2027.Embed.RAMSolver.forkResultProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forkResultProgram

/-- info: 'STACS2027.Embed.RAMSolver.forkNodeProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forkNodeProgram

/-- info: 'STACS2027.Embed.RAMSolver.closePositiveProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.closePositiveProgram

/-- info: 'STACS2027.Embed.RAMSolver.closeNegativeProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.closeNegativeProgram

/-- info: 'STACS2027.Embed.RAMSolver.closeResultProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.closeResultProgram

/-- info: 'STACS2027.Embed.RAMSolver.targetNodeProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.targetNodeProgram

/-- info: 'STACS2027.Embed.RAMSolver.twoNodeProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.twoNodeProgram

/-- info: 'STACS2027.Embed.RAMSolver.nodeStepProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nodeStepProgram

/-- info: 'STACS2027.Embed.RAMSolver.mstepProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstepProgram

/-- info: 'STACS2027.Embed.RAMSolver.itemResultInto_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itemResultInto_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.nodeStepProgram_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nodeStepProgram_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.nodeStepProgram_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nodeStepProgram_size

/-- info: 'STACS2027.Embed.RAMSolver.mstepProgram_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstepProgram_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.mstepProgram_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.mstepProgram_size

/-- info: 'STACS2027.Embed.RAMSolver.itemResultInto_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itemResultInto_raw

/-- info: 'STACS2027.Embed.RAMSolver.storeNodeResult_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.storeNodeResult_raw

/-- info: 'STACS2027.Embed.RAMSolver.beginForkProgram_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.beginForkProgram_raw

/-- info: 'STACS2027.Embed.Sol.forkRows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.forkRows

/-- info: 'STACS2027.Embed.Sol.nodeRows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.nodeRows

/-- info: 'STACS2027.Embed.Sol.itRes_records_frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.itRes_records_frame

/-- info: 'STACS2027.Embed.Sol.completeFork_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeFork_records

/-- info: 'STACS2027.Embed.Sol.closeM_records_frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.closeM_records_frame

/-- info: 'STACS2027.Embed.Sol.nodeRows_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.nodeRows_perm

/-- info: 'STACS2027.Embed.Sol.completeNode_recordArrays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeNode_recordArrays

/-- info: 'STACS2027.Embed.Sol.Tree.consAt_ids_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.Tree.consAt_ids_nodup

/-- info: 'STACS2027.Embed.Sol.completeNode_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeNode_records

/-- info: 'STACS2027.Embed.RAMSolver.nodeStepProgram_rep_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nodeStepProgram_rep_addr

/-- info: 'STACS2027.Embed.RAMSolver.nodeStepProgram_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.nodeStepProgram_simulation

/-- info: 'STACS2027.Embed.RAMSolver.leafNodeProgram_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.leafNodeProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.leafNodeProgram_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.leafNodeProgram_exec

/-- info: 'STACS2027.Embed.RAMSolver.singleItem_node_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.singleItem_node_frame

/-- info: 'STACS2027.Embed.RAMSolver.singleNodeProgram_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.singleNodeProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.singleNodeProgram_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.singleNodeProgram_exec

/-- info: 'STACS2027.Embed.RAMSolver.Bases.finiteFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Bases.finiteFrame

/-- info: 'STACS2027.Embed.RAMSolver.Rep.finiteFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Rep.finiteFrame

/-- info: 'STACS2027.Embed.RAMSolver.Tables.prefixFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Tables.prefixFrame

/-- info: 'STACS2027.Embed.RAMSolver.defaultRotationProgram_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.defaultRotationProgram_regs

/-- info: 'STACS2027.Embed.RAMSolver.orientationLoop_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.orientationLoop_regs

/-- info: 'STACS2027.Embed.DFSRAM.Bases.phaseFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Bases.phaseFrame

/-- info: 'STACS2027.Embed.DFSRAM.Bases.solverFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Bases.solverFrame

/-- info: 'STACS2027.Embed.DFSRAM.Tables.prefixFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.DFSRAM.Tables.prefixFrame

/-- info: 'STACS2027.Embed.RAMSolver.PopAddressOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.PopAddressOK

/-- info: 'STACS2027.Embed.RAMSolver.popStepProgram_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStepProgram_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.PopAddressOK.ofRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.PopAddressOK.ofRep

/-- info: 'STACS2027.Embed.RAMSolver.popStepProgram_exec_ofRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStepProgram_exec_ofRep

/-- info: 'STACS2027.Embed.RAMSolver.popClasses_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popClasses_raw

/-- info: 'STACS2027.Embed.RAMSolver.popProbe' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popProbe

/-- info: 'STACS2027.Embed.RAMSolver.popProbe_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popProbe_raw

/-- info: 'STACS2027.Embed.RAMSolver.consumeRecord_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consumeRecord_raw

/-- info: 'STACS2027.Embed.RAMSolver.popExecute_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popExecute_raw

/-- info: 'STACS2027.Embed.RAMSolver.Rep.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Rep.frame

/-- info: 'STACS2027.Embed.RAMSolver.Rep.setMode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Rep.setMode

/-- info: 'STACS2027.Embed.RAMSolver.rawHeadKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rawHeadKey_eq

/-- info: 'STACS2027.Embed.RAMSolver.popProbe_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popProbe_rep

/-- info: 'STACS2027.Embed.RAMSolver.popStepProgram_run_probe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStepProgram_run_probe

/-- info: 'STACS2027.Embed.RAMSolver.popStepProgram_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStepProgram_active

/-- info: 'STACS2027.Embed.RAMSolver.popStepProgram_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStepProgram_inactive

/-- info: 'STACS2027.Embed.RAMSolver.popStepProgram_rep_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStepProgram_rep_tables

/-- info: 'STACS2027.Embed.RAMSolver.popStepProgram_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStepProgram_simulation

/-- info: 'STACS2027.Embed.RAMSolver.Layout' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Layout

/-- info: 'STACS2027.Embed.RAMSolver.Layout.block' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Layout.block

/-- info: 'STACS2027.Embed.RAMSolver.Layout.cell' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Layout.cell

/-- info: 'STACS2027.Embed.RAMSolver.Layout.limit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Layout.limit

/-- info: 'STACS2027.Embed.RAMSolver.Layout.cell_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Layout.cell_lt

/-- info: 'STACS2027.Embed.RAMSolver.Layout.cell_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Layout.cell_injective

/-- info: 'STACS2027.Embed.RAMSolver.memField' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.memField

/-- info: 'STACS2027.Embed.RAMSolver.Bases' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Bases

/-- info: 'STACS2027.Embed.RAMSolver.Rep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Rep

/-- info: 'STACS2027.Embed.RAMSolver.itemType' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itemType

/-- info: 'STACS2027.Embed.RAMSolver.itemValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.itemValue

/-- info: 'STACS2027.Embed.RAMSolver.Tables' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Tables

/-- info: 'STACS2027.Embed.RAMSolver.loadCell' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.loadCell

/-- info: 'STACS2027.Embed.RAMSolver.storeCell' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.storeCell

/-- info: 'STACS2027.Embed.RAMSolver.appendInto' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendInto

/-- info: 'STACS2027.Embed.RAMSolver.appendInto_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendInto_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.appendInto_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendInto_size

/-- info: 'STACS2027.Embed.RAMSolver.appendInto_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendInto_spec

/-- info: 'STACS2027.Embed.Sol.writeParents' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.writeParents

/-- info: 'STACS2027.Embed.Sol.writeFlips' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.writeFlips

/-- info: 'STACS2027.Embed.Sol.upperRows' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.upperRows

/-- info: 'STACS2027.Embed.Sol.lowerRows' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.lowerRows

/-- info: 'STACS2027.Embed.Sol.popStep_records' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popStep_records

/-- info: 'STACS2027.Embed.Sol.consStep_records' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consStep_records

/-- info: 'STACS2027.Embed.Sol.popGroups_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.popGroups_records

/-- info: 'STACS2027.Embed.Sol.consGroups_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.consGroups_records

/-- info: 'STACS2027.Embed.Sol.RecordPrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.RecordPrefix

/-- info: 'STACS2027.Embed.Sol.recordPrefix_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.recordPrefix_empty

/-- info: 'STACS2027.Embed.Sol.recordPrefix_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.recordPrefix_append

/-- info: 'STACS2027.Embed.Sol.runPrefix_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.runPrefix_records

/-- info: 'STACS2027.Embed.ForestData.solver_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.solver_records

/-- info: 'STACS2027.Embed.Sol.runPrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.runPrefix

/-- info: 'STACS2027.Embed.Sol.prefixCharge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.prefixCharge

/-- info: 'STACS2027.Embed.Sol.completeNode_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.completeNode_frontier

/-- info: 'STACS2027.Embed.Sol.runPrefix_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.runPrefix_spec

/-- info: 'STACS2027.Embed.Sol.prefixCharge_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.prefixCharge_eq

/-- info: 'STACS2027.Embed.ForestData.iterate_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.iterate_fixed

/-- info: 'STACS2027.Embed.ForestData.solver_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.solver_linear

/-- info: 'STACS2027.Embed.ForestData.solver_fixedBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.solver_fixedBudget

/-- info: 'STACS2027.Embed.RAMSolver.ConsumeAddressOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ConsumeAddressOK

/-- info: 'STACS2027.Embed.RAMSolver.consumeGroupProgram_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consumeGroupProgram_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.FinishAddressOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.FinishAddressOK

/-- info: 'STACS2027.Embed.RAMSolver.finishMergeProgram_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.finishMergeProgram_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.consStepProgram_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consStepProgram_exec

/-- info: 'STACS2027.Embed.RAMSolver.ConsumeAddressOK.ofRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.ConsumeAddressOK.ofRep

/-- info: 'STACS2027.Embed.RAMSolver.FinishAddressOK.ofRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.FinishAddressOK.ofRep

/-- info: 'STACS2027.Embed.RAMSolver.consStepProgram_exec_ofRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consStepProgram_exec_ofRep

/-- info: 'STACS2027.Embed.RAMSolver.headKey' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.headKey

/-- info: 'STACS2027.Embed.RAMSolver.groupRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.groupRead

/-- info: 'STACS2027.Embed.RAMSolver.consumeRecord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consumeRecord

/-- info: 'STACS2027.Embed.RAMSolver.popClasses' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popClasses

/-- info: 'STACS2027.Embed.RAMSolver.popStepProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStepProgram

/-- info: 'STACS2027.Embed.RAMSolver.consumeGroupProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consumeGroupProgram

/-- info: 'STACS2027.Embed.RAMSolver.finishMergeProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.finishMergeProgram

/-- info: 'STACS2027.Embed.RAMSolver.consStepProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consStepProgram

/-- info: 'STACS2027.Embed.RAMSolver.headKey_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.headKey_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.popStepProgram_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStepProgram_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.consStepProgram_loopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consStepProgram_loopFree

/-- info: 'STACS2027.Embed.RAMSolver.popStepProgram_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.popStepProgram_size

/-- info: 'STACS2027.Embed.RAMSolver.consStepProgram_size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consStepProgram_size

/-- info: 'STACS2027.Embed.RAMSolver.appendInto_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendInto_memory

/-- info: 'STACS2027.Embed.RAMSolver.appendInto_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendInto_frame

/-- info: 'STACS2027.Embed.RAMSolver.appendInto_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendInto_addrOK

/-- info: 'STACS2027.Embed.RAMSolver.appendMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendMem

/-- info: 'STACS2027.Embed.RAMSolver.rawHeadKey' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rawHeadKey

/-- info: 'STACS2027.Embed.RAMSolver.appendMem_slice' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendMem_slice

/-- info: 'STACS2027.Embed.RAMSolver.loadCell_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.loadCell_frame

/-- info: 'STACS2027.Embed.RAMSolver.storeCell_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.storeCell_memory

/-- info: 'STACS2027.Embed.RAMSolver.consumeGroupProgram_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consumeGroupProgram_raw

/-- info: 'STACS2027.Embed.RAMSolver.finishMergeProgram_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.finishMergeProgram_raw

/-- info: 'STACS2027.Embed.RAMSolver.Layout.cell_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Layout.cell_eq_iff

/-- info: 'STACS2027.Embed.RAMSolver.update_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.update_cell

/-- info: 'STACS2027.Embed.RAMSolver.StepBounds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.StepBounds

/-- info: 'STACS2027.Embed.RAMSolver.appendMem_foreign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendMem_foreign

/-- info: 'STACS2027.Embed.RAMSolver.appendMem_linked' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendMem_linked

/-- info: 'STACS2027.Embed.RAMSolver.appL_head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appL_head

/-- info: 'STACS2027.Embed.RAMSolver.appL_tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appL_tail

/-- info: 'STACS2027.Embed.RAMSolver.appendMem_rep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.appendMem_rep

/-- info: 'STACS2027.Embed.RAMSolver.consumeGroupProgram_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consumeGroupProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.finishMergeProgram_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.finishMergeProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.consStepProgram_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consStepProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.consumeGroupProgram_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consumeGroupProgram_tables

/-- info: 'STACS2027.Embed.RAMSolver.finishMergeProgram_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.finishMergeProgram_tables

/-- info: 'STACS2027.Embed.RAMSolver.consStepProgram_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consStepProgram_tables

/-- info: 'STACS2027.Embed.RAMSolver.consStepProgram_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.consStepProgram_simulation

/-- info: 'STACS2027.Embed.RAMSolver.targetReadProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.targetReadProgram

/-- info: 'STACS2027.Embed.RAMSolver.targetStoreProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.targetStoreProgram

/-- info: 'STACS2027.Embed.RAMSolver.targetReadProgram_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.targetReadProgram_raw

/-- info: 'STACS2027.Embed.RAMSolver.targetStoreProgram_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.targetStoreProgram_raw

/-- info: 'STACS2027.Embed.RAMSolver.targetStoreProgram_rep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.targetStoreProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.targetNodeProgram_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.targetNodeProgram_run

/-- info: 'STACS2027.Embed.RAMSolver.targetNodeProgram_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.targetNodeProgram_rep

/-- info: 'STACS2027.Embed.RAMSolver.targetNodeProgram_addr_decomp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.targetNodeProgram_addr_decomp

/-- info: 'STACS2027.Embed.RAMSolver.targetNodeProgram_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.targetNodeProgram_exec

/-- info: 'STACS2027.Embed.RAMSolver.Rep.temp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Rep.temp

/-- info: 'STACS2027.Embed.RAMSolver.Tables.temp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Tables.temp

/-- info: 'STACS2027.Embed.RAMSolver.Rep.loadTemp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Rep.loadTemp

/-- info: 'STACS2027.Embed.RAMSolver.Tables.loadTemp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.Tables.loadTemp

/-- info: 'STACS2027.Embed.RAMSolver.boundedRun_addr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.boundedRun_addr

/-- info: 'STACS2027.Embed.RAMSolver.twoReadProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.twoReadProgram

/-- info: 'STACS2027.Embed.RAMSolver.twoBranchProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.twoBranchProgram

/-- info: 'STACS2027.Embed.RAMSolver.forkBranch_rep_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.forkBranch_rep_addr

/-- info: 'STACS2027.Embed.RAMSolver.leftTarget_rep_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.leftTarget_rep_addr

/-- info: 'STACS2027.Embed.RAMSolver.rightTarget_rep_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.rightTarget_rep_addr

/-- info: 'STACS2027.Embed.RAMSolver.twoBranchProgram_rep_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.twoBranchProgram_rep_addr

/-- info: 'STACS2027.Embed.RAMSolver.twoReadProgram_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.twoReadProgram_raw

/-- info: 'STACS2027.Embed.RAMSolver.twoNodeProgram_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.twoNodeProgram_run

/-- info: 'STACS2027.Embed.RAMSolver.twoNodeProgram_addr_decomp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.twoNodeProgram_addr_decomp

/-- info: 'STACS2027.Embed.RAMSolver.twoNodeProgram_rep_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.RAMSolver.twoNodeProgram_rep_addr

/-- info: 'STACS2027.Embed.Sol.StackRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.StackRep

/-- info: 'STACS2027.Embed.Sol.StackRep.cons_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.StackRep.cons_iff

/-- info: 'STACS2027.Embed.Sol.StackRep.head_zero_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.StackRep.head_zero_iff

/-- info: 'STACS2027.Embed.Sol.StackRep.group' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.StackRep.group

/-- info: 'STACS2027.Embed.Sol.StackRep.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.StackRep.frame

/-- info: 'STACS2027.Embed.Sol.StackRep.array_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.StackRep.array_frame

/-- info: 'STACS2027.Embed.Sol.GroupRep.other_positive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.GroupRep.other_positive

/-- info: 'STACS2027.Embed.Sol.GroupRep.other_negative' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.GroupRep.other_negative

/-- info: 'STACS2027.Embed.Sol.GroupRep.pop_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.GroupRep.pop_positive

/-- info: 'STACS2027.Embed.Sol.GroupRep.pop_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.GroupRep.pop_negative

/-- info: 'STACS2027.Embed.Sol.itRes_dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.itRes_dart

/-- info: 'STACS2027.Embed.Sol.closeM_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.closeM_positive

/-- info: 'STACS2027.Embed.Sol.closeM_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.closeM_negative

/-- info: 'STACS2027.Embed.Sol.closeM_group_next' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.closeM_group_next

/-- info: 'STACS2027.Embed.Sol.closeM_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.Sol.closeM_stack

/-- info: 'STACS2027.Embed.ForestData.TreeOn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.TreeOn

/-- info: 'STACS2027.Embed.ForestData.treeOn_up' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.treeOn_up

/-- info: 'STACS2027.Embed.ForestData.treeOn_iter' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.treeOn_iter

/-- info: 'STACS2027.Embed.ForestData.depth_iterate'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.depth_iterate'

/-- info: 'STACS2027.Embed.ForestData.iterate_up_depth'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.iterate_up_depth'

/-- info: 'STACS2027.Embed.ForestData.desc_depth'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_depth'

/-- info: 'STACS2027.Embed.ForestData.desc_eq_iterate'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_eq_iterate'

/-- info: 'STACS2027.Embed.ForestData.desc_unique'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_unique'

/-- info: 'STACS2027.Embed.ForestData.desc_P' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_P

/-- info: 'STACS2027.Embed.ForestData.desc_antisymm'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_antisymm'

/-- info: 'STACS2027.Embed.ForestData.desc_up_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_up_not

/-- info: 'STACS2027.Embed.ForestData.desc_nonroot_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_nonroot_iff

/-- info: 'STACS2027.Embed.ForestData.desc_root_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_root_iff

/-- info: 'STACS2027.Embed.ForestData.iterate_up_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.iterate_up_congr

/-- info: 'STACS2027.Embed.ForestData.desc_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.ForestData.desc_congr

/-- info: 'STACS2027.Embed.Before' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Before

/-- info: 'STACS2027.Embed.before_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_mem

/-- info: 'STACS2027.Embed.before_cons_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_cons_iff

/-- info: 'STACS2027.Embed.before_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_nil

/-- info: 'STACS2027.Embed.before_append_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_append_iff

/-- info: 'STACS2027.Embed.before_append_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_append_left

/-- info: 'STACS2027.Embed.before_append_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_append_right

/-- info: 'STACS2027.Embed.before_append_mid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_append_mid

/-- info: 'STACS2027.Embed.before_irrefl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_irrefl

/-- info: 'STACS2027.Embed.before_asymm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_asymm

/-- info: 'STACS2027.Embed.before_total' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_total

/-- info: 'STACS2027.Embed.before_trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_trans

/-- info: 'STACS2027.Embed.before_filter_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_filter_iff

/-- info: 'STACS2027.Embed.before_reverse_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_reverse_iff

/-- info: 'STACS2027.Embed.before_of_append_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_of_append_left

/-- info: 'STACS2027.Embed.before_of_append_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_of_append_right

/-- info: 'STACS2027.Embed.WN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.WN

/-- info: 'STACS2027.Embed.wn_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.wn_nil

/-- info: 'STACS2027.Embed.wn_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.wn_singleton

/-- info: 'STACS2027.Embed.wn_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.wn_append

/-- info: 'STACS2027.Embed.wn_reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.wn_reverse

/-- info: 'STACS2027.Embed.wn_cons_close' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.wn_cons_close

/-- info: 'STACS2027.Embed.wn_snoc_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.wn_snoc_close

/-- info: 'STACS2027.Embed.mem_of_between' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.mem_of_between

/-- info: 'STACS2027.Embed.before_of_infix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_of_infix

/-- info: 'STACS2027.Embed.before_infix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.before_infix

/-- info: 'STACS2027.Embed.wn_infix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.wn_infix

/-- info: 'STACS2027.Embed.wn_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Embed.wn_congr

/-- info: 'STACS2027.Embed.openEnds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.openEnds

/-- info: 'STACS2027.Embed.mem_openEnds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.mem_openEnds

/-- info: 'STACS2027.Embed.openEnds_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.openEnds_append

/-- info: 'STACS2027.Embed.openEnds_cons_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.openEnds_cons_close

/-- info: 'STACS2027.Embed.openEnds_snoc_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.openEnds_snoc_close

/-- info: 'STACS2027.Embed.openEnds_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.openEnds_reverse

/-- info: 'STACS2027.Embed.VR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.VR

/-- info: 'STACS2027.Embed.Valley' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.Valley

/-- info: 'STACS2027.Embed.valley_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.valley_first

/-- info: 'STACS2027.Embed.valley_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.valley_last

/-- info: 'STACS2027.Embed.valley_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Embed.valley_cons

/-- info: 'STACS2027.Embed.valley_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Embed.valley_snoc

/-- info: 'STACS2027.max3SAT3_lReducible_cpap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.max3SAT3_lReducible_cpap

/-- info: 'STACS2027.cpap_maxSNPHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap_maxSNPHard

/-- info: 'STACS2027.cpap_apxHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap_apxHard

/-- info: 'STACS2027.cpap_no_ptas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap_no_ptas

/-- info: 'STACS2027.cpap_not_approximable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap_not_approximable

/-- info: 'STACS2027.Hardness.eraseDups_sublist_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.eraseDups_sublist_nodup

/-- info: 'STACS2027.Hardness.eraseDups_sublist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.eraseDups_sublist

/-- info: 'STACS2027.Hardness.eraseDups_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.eraseDups_nodup

/-- info: 'STACS2027.Hardness.eraseDups_eq_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.eraseDups_eq_nil

/-- info: 'STACS2027.Hardness.evalClause_eraseDups' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.evalClause_eraseDups

/-- info: 'STACS2027.Hardness.unitGadget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Hardness.unitGadget

/-- info: 'STACS2027.Hardness.normClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Hardness.normClause

/-- info: 'STACS2027.Hardness.normFrom' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Hardness.normFrom

/-- info: 'STACS2027.Hardness.normalize' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Hardness.normalize

/-- info: 'STACS2027.Hardness.isUnit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Hardness.isUnit

/-- info: 'STACS2027.Hardness.unitCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Hardness.unitCount

/-- info: 'STACS2027.Hardness.normFrom_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Hardness.normFrom_nil

/-- info: 'STACS2027.Hardness.normFrom_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Hardness.normFrom_cons

/-- info: 'STACS2027.Hardness.mem_normClause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.mem_normClause

/-- info: 'STACS2027.Hardness.mem_normFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.mem_normFrom

/-- info: 'STACS2027.Hardness.length_eraseDups_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.length_eraseDups_le

/-- info: 'STACS2027.Hardness.normalize_clauses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.normalize_clauses

/-- info: 'STACS2027.Hardness.filter_and_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.filter_and_add

/-- info: 'STACS2027.Hardness.occurrences_true_add_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.occurrences_true_add_false

/-- info: 'STACS2027.Hardness.occurrences_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.occurrences_add

/-- info: 'STACS2027.Hardness.normFrom_filter_sublist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.normFrom_filter_sublist

/-- info: 'STACS2027.Hardness.occurrences_gadget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.occurrences_gadget

/-- info: 'STACS2027.Hardness.occurrences_normFrom_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.occurrences_normFrom_fresh

/-- info: 'STACS2027.Hardness.normalize_threeOccurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.normalize_threeOccurrence

/-- info: 'STACS2027.Hardness.satisfiedCount_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.satisfiedCount_cons

/-- info: 'STACS2027.Hardness.unitCount_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.unitCount_cons

/-- info: 'STACS2027.Hardness.satisfiedCount_gadget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Hardness.satisfiedCount_gadget

/-- info: 'STACS2027.Hardness.satisfiedCount_gadget_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Hardness.satisfiedCount_gadget_le

/-- info: 'STACS2027.Hardness.satisfiedCount_gadget_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Hardness.satisfiedCount_gadget_eq

/-- info: 'STACS2027.Hardness.eraseDups_eq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.eraseDups_eq_singleton

/-- info: 'STACS2027.Hardness.evalClause_of_eraseDups' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.evalClause_of_eraseDups

/-- info: 'STACS2027.Hardness.satisfiedCount_normClause_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.satisfiedCount_normClause_le

/-- info: 'STACS2027.Hardness.freshFalse' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Hardness.freshFalse

/-- info: 'STACS2027.Hardness.evalClause_freshFalse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Hardness.evalClause_freshFalse

/-- info: 'STACS2027.Hardness.satisfiedCount_normClause_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.satisfiedCount_normClause_eq

/-- info: 'STACS2027.Hardness.satisfiedCount_normFrom_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.satisfiedCount_normFrom_le

/-- info: 'STACS2027.Hardness.satisfiedCount_normFrom_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.satisfiedCount_normFrom_eq

/-- info: 'STACS2027.Hardness.satisfiedCount_normalize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.satisfiedCount_normalize_le

/-- info: 'STACS2027.Hardness.isMaxSat_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.isMaxSat_normalize

/-- info: 'STACS2027.Hardness.unitCount_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.unitCount_le

/-- info: 'STACS2027.Hardness.two_mul_unitCount_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.two_mul_unitCount_le

/-- info: 'STACS2027.Hardness.pt_unitGadget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_unitGadget

/-- info: 'STACS2027.Hardness.PT.unitGadget'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.PT.unitGadget'

/-- info: 'STACS2027.Hardness.pt_normClause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_normClause

/-- info: 'STACS2027.Hardness.PT.normClause'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.PT.normClause'

/-- info: 'STACS2027.Hardness.pt_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_normalize

/-- info: 'STACS2027.cpapProblem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpapProblem

/-- info: 'STACS2027.cpapProblem_sol_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpapProblem_sol_encode

/-- info: 'STACS2027.cpapProblem_isOpt_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpapProblem_isOpt_iff

/-- info: 'STACS2027.cpapProblem_isOpt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpapProblem_isOpt

/-- info: 'STACS2027.Hardness.pt_occurrences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_occurrences

/-- info: 'STACS2027.Hardness.PT.occurrences'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.PT.occurrences'

/-- info: 'STACS2027.Hardness.pt_pureThree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_pureThree

/-- info: 'STACS2027.Hardness.PT.pureThree'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.PT.pureThree'

/-- info: 'STACS2027.Hardness.pt_pureValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_pureValue

/-- info: 'STACS2027.Hardness.PT.pureValue'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.PT.pureValue'

/-- info: 'STACS2027.Hardness.pt_tautological' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_tautological

/-- info: 'STACS2027.Hardness.PT.tautological'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.PT.tautological'

/-- info: 'STACS2027.Hardness.pt_deleted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_deleted

/-- info: 'STACS2027.Hardness.PT.deleted'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.PT.deleted'

/-- info: 'STACS2027.Hardness.pt_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_kept

/-- info: 'STACS2027.Hardness.PT.kept'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.PT.kept'

/-- info: 'STACS2027.Hardness.pt_complemented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_complemented

/-- info: 'STACS2027.Hardness.PT.complemented'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.PT.complemented'

/-- info: 'STACS2027.Hardness.PT.recover'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.PT.recover'

/-- info: 'STACS2027.Hardness.satisfiedCount_eq_satCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Hardness.satisfiedCount_eq_satCount

/-- info: 'STACS2027.Hardness.max3SAT3_sol_encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Hardness.max3SAT3_sol_encode

/-- info: 'STACS2027.Hardness.isMaxSat_of_isOpt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.isMaxSat_of_isOpt

/-- info: 'STACS2027.Hardness.solMap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Hardness.solMap

/-- info: 'STACS2027.Hardness.pt_solMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.pt_solMap

/-- info: 'STACS2027.Hardness.lReducible_max3SAT3_cpap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Hardness.lReducible_max3SAT3_cpap

/-- info: 'STACS2027.distinctLiterals_of_nodup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.distinctLiterals_of_nodup

/-- info: 'STACS2027.clause_distinct_vars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_distinct_vars

/-- info: 'STACS2027.normalizeClauses_leOneLeTwo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.normalizeClauses_leOneLeTwo

/-- info: 'STACS2027.firstUnit_eq_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.firstUnit_eq_none

/-- info: 'STACS2027.unitReduce_leOneLeTwo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.unitReduce_leOneLeTwo

/-- info: 'STACS2027.cleanFormula_leOneLeTwo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cleanFormula_leOneLeTwo

/-- info: 'STACS2027.globalReductionGraph_leOneLeTwo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.globalReductionGraph_leOneLeTwo

/-- info: 'STACS2027.orientedClauseVertex_trivial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedClauseVertex_trivial

/-- info: 'STACS2027.orientedPlacedClauseGraph_trivial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedPlacedClauseGraph_trivial

/-- info: 'STACS2027.orientedFormulaGraph_trivial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.orientedFormulaGraph_trivial

/-- info: 'STACS2027.kernel_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.kernel_trivial

/-- info: 'STACS2027.instance_map_linear_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.instance_map_linear_time

/-- info: 'STACS2027.IsMinCost.of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsMinCost.of_perm

/-- info: 'STACS2027.LReductionToCPAP.of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LReductionToCPAP.of_perm

/-- info: 'STACS2027.cpap_lreduction_computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap_lreduction_computed

/-- info: 'STACS2027.LeOneLeTwoCNF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LeOneLeTwoCNF

/-- info: 'STACS2027.formulaGraph_hasAssignment_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.formulaGraph_hasAssignment_exists

/-- info: 'STACS2027.minCost_add_maxSat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.minCost_add_maxSat

/-- info: 'STACS2027.four_mul_maxSat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.four_mul_maxSat

/-- info: 'STACS2027.three_mul_minCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.three_mul_minCost_le

/-- info: 'STACS2027.decode_error_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.decode_error_bound

/-- info: 'STACS2027.cpap_optimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap_optimum

/-- info: 'STACS2027.cpap_lreduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cpap_lreduction

/-- info: 'STACS2027.gadget_reduction_linear_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.gadget_reduction_linear_ram

/-- info: 'STACS2027.weightedLoad' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.weightedLoad

/-- info: 'STACS2027.weightedLoad_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.weightedLoad_eq

/-- info: 'STACS2027.variablePortEdge_values' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.variablePortEdge_values

/-- info: 'STACS2027.variableSkeleton_weighted_normalizes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.variableSkeleton_weighted_normalizes

/-- info: 'STACS2027.weight_eq_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.weight_eq_toNat

/-- info: 'STACS2027.variableExpansion_weighted_normalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableExpansion_weighted_normalizes

/-- info: 'STACS2027.variableChosen_weighted_normalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variableChosen_weighted_normalizes

/-- info: 'STACS2027.exists_greatest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_greatest

/-- info: 'STACS2027.exists_least' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_least

/-- info: 'STACS2027.satisfiedCount_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_le

/-- info: 'STACS2027.maxSat_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.maxSat_exists

/-- info: 'STACS2027.minCost_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.minCost_exists

/-- info: 'STACS2027.IsMaxSat.unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsMaxSat.unique

/-- info: 'STACS2027.IsMinCost.unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsMinCost.unique

/-- info: 'STACS2027.satisfiedCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount

/-- info: 'STACS2027.IsMaxSat' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsMaxSat

/-- info: 'STACS2027.IsMinCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsMinCost

/-- info: 'STACS2027.LReductionToCPAP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.LReductionToCPAP

/-- info: 'STACS2027.LReductionSat' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LReductionSat

/-- info: 'STACS2027.Paper.leOneLeTwoCNF_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.leOneLeTwoCNF_iff

/-- info: 'STACS2027.Paper.threeOccurrence_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.threeOccurrence_iff

/-- info: 'STACS2027.Paper.optima_exist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.optima_exist

/-- info: 'STACS2027.Paper.assignment_from_truth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.assignment_from_truth

/-- info: 'STACS2027.Paper.truth_from_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.truth_from_assignment

/-- info: 'STACS2027.Paper.optimum_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.optimum_relation

/-- info: 'STACS2027.Paper.random_assignment_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.random_assignment_bound

/-- info: 'STACS2027.Paper.alpha_condition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.alpha_condition

/-- info: 'STACS2027.Paper.beta_condition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.beta_condition

/-- info: 'STACS2027.Paper.gadget_lreduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_lreduction

/-- info: 'STACS2027.Paper.polarize_construction' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.polarize_construction

/-- info: 'STACS2027.Paper.polarize_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.polarize_target

/-- info: 'STACS2027.Paper.polarize_optimum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.polarize_optimum

/-- info: 'STACS2027.Paper.polarize_recovery' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.polarize_recovery

/-- info: 'STACS2027.Paper.leOneLeTwo_lreduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.leOneLeTwo_lreduction

/-- info: 'STACS2027.Paper.gadget_lreduction_from_threeOccurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_lreduction_from_threeOccurrence

/-- info: 'STACS2027.Paper.cpapProblem_optimum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.cpapProblem_optimum

/-- info: 'STACS2027.Paper.cpap_lReducible_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.cpap_lReducible_paper

/-- info: 'STACS2027.Paper.maxSNP_hardness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.maxSNP_hardness

/-- info: 'STACS2027.Paper.apx_hardness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.apx_hardness

/-- info: 'STACS2027.Paper.no_ptas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.no_ptas

/-- info: 'STACS2027.Paper.no_ptas_nonuniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.no_ptas_nonuniform

/-- info: 'STACS2027.Paper.ptas_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.ptas_transfer

/-- info: 'STACS2027.Paper.instance_map_computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.instance_map_computed

/-- info: 'STACS2027.Paper.full_domain_is_gadget_graph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.full_domain_is_gadget_graph

/-- info: 'STACS2027.Paper.gadget_polyTime_instance_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_polyTime_instance_map

/-- info: 'STACS2027.Paper.gadget_reduction_linear_time_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.gadget_reduction_linear_time_ram

/-- info: 'STACS2027.PlanarAssembly.occList' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occList

/-- info: 'STACS2027.PlanarAssembly.occPort' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occPort

/-- info: 'STACS2027.PlanarAssembly.occVar' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occVar

/-- info: 'STACS2027.PlanarAssembly.positiveIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.positiveIndex

/-- info: 'STACS2027.PlanarAssembly.variableSign' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableSign

/-- info: 'STACS2027.PlanarAssembly.clauseSign' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseSign

/-- info: 'STACS2027.PlanarAssembly.flipBit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.flipBit

/-- info: 'STACS2027.PlanarAssembly.orientationBits' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.orientationBits

/-- info: 'STACS2027.PlanarAssembly.orientationChoices' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.orientationChoices

/-- info: 'STACS2027.PlanarAssembly.orientationChoices_occurrence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.orientationChoices_occurrence

/-- info: 'STACS2027.PlanarAssembly.orientationBits_getElem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.orientationBits_getElem

/-- info: 'STACS2027.PlanarAssembly.occPort_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occPort_eq

/-- info: 'STACS2027.PlanarAssembly.occVar_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occVar_eq

/-- info: 'STACS2027.PlanarAssembly.positiveIndex_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.positiveIndex_eq

/-- info: 'STACS2027.PlanarAssembly.occurrenceDart_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.occurrenceDart_val

/-- info: 'STACS2027.PlanarAssembly.variableSign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.variableSign_spec

/-- info: 'STACS2027.PlanarAssembly.clauseSign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseSign_spec

/-- info: 'STACS2027.PlanarAssembly.pieceForward' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceForward

/-- info: 'STACS2027.PlanarAssembly.pieceNextX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceNextX

/-- info: 'STACS2027.PlanarAssembly.pieceSideX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceSideX

/-- info: 'STACS2027.PlanarAssembly.pieceNextX_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.pieceNextX_val

/-- info: 'STACS2027.PlanarAssembly.piece_length_variable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_length_variable

/-- info: 'STACS2027.PlanarAssembly.piece_clause_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_clause_lt

/-- info: 'STACS2027.PlanarAssembly.piece_length_clause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_length_clause

/-- info: 'STACS2027.PlanarAssembly.piece_length_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_length_bounds

/-- info: 'STACS2027.PlanarAssembly.piece_explicit_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_explicit_profile

/-- info: 'STACS2027.PlanarAssembly.clauseSign_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.clauseSign_three

/-- info: 'STACS2027.PlanarAssembly.piece_sign_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.piece_sign_witness

/-- info: 'STACS2027.PlanarAssembly.explicit_source_orders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.explicit_source_orders

/-- info: 'STACS2027.PlanarAssembly.explicit_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.explicit_sides

/-- info: 'STACS2027.PlanarAssembly.orientationChoices_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.orientationChoices_planar

/-- info: 'STACS2027.PlanarAssembly.IsPlanarRotation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.IsPlanarRotation

/-- info: 'STACS2027.PlanarAssembly.planarGraph_iff_rotation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.planarGraph_iff_rotation

/-- info: 'STACS2027.PlanarAssembly.choicesOfBits' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.choicesOfBits

/-- info: 'STACS2027.PlanarAssembly.choicesOfBits_orientationBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.choicesOfBits_orientationBits

/-- info: 'STACS2027.PlanarAssembly.orientationBits_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.orientationBits_planar

/-- info: 'STACS2027.PlanarAssembly.NextSelected.chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextSelected.chain

/-- info: 'STACS2027.PlanarAssembly.NextSelected.skip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NextSelected.skip

/-- info: 'STACS2027.PlanarAssembly.cyclic_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.cyclic_values

/-- info: 'STACS2027.PlanarAssembly.cyclic_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.cyclic_skip

/-- info: 'STACS2027.PlanarAssembly.three_cycle_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.three_cycle_sign

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.iterate_fixed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.iterate_fixed

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.order_fixed' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.order_fixed

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.face_edge_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.face_edge_node

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.order_of_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.order_of_node

/-- info: 'STACS2027.PlanarAssembly.NodeDartIndex.node_vertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarAssembly.NodeDartIndex.node_vertex

/-- info: 'STACS2027.ThreeOccurrence' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ThreeOccurrence

/-- info: 'STACS2027.pureThree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pureThree

/-- info: 'STACS2027.pureValue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pureValue

/-- info: 'STACS2027.deleted' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.deleted

/-- info: 'STACS2027.kept' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.kept

/-- info: 'STACS2027.deletedCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.deletedCount

/-- info: 'STACS2027.complemented' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.complemented

/-- info: 'STACS2027.flipLiteral' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.flipLiteral

/-- info: 'STACS2027.flipFormula' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.flipFormula

/-- info: 'STACS2027.padding' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.padding

/-- info: 'STACS2027.polarize' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.polarize

/-- info: 'STACS2027.sublist_flatten_of_sublist' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.sublist_flatten_of_sublist

/-- info: 'STACS2027.occurrences_kept_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_kept_le

/-- info: 'STACS2027.occurrences_flipFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_flipFormula

/-- info: 'STACS2027.occurrences_eq_zero_of_forall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_eq_zero_of_forall

/-- info: 'STACS2027.occurrences_padding_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_padding_lt

/-- info: 'STACS2027.occurrences_padding_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_padding_false

/-- info: 'STACS2027.occurrences_padding_true_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_padding_true_le

/-- info: 'STACS2027.occurrences_kept_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_kept_pure

/-- info: 'STACS2027.variable_lt_of_mem_flipFormula_kept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variable_lt_of_mem_flipFormula_kept

/-- info: 'STACS2027.polarize_boundedOccurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.polarize_boundedOccurrence

/-- info: 'STACS2027.polarize_clauseVariablesDistinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.polarize_clauseVariablesDistinct

/-- info: 'STACS2027.polarize_leOneLeTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.polarize_leOneLeTwo

/-- info: 'STACS2027.satisfiedCount_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_append

/-- info: 'STACS2027.deletedClauses' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.deletedClauses

/-- info: 'STACS2027.countP_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_split

/-- info: 'STACS2027.satisfiedCount_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_split

/-- info: 'STACS2027.satisfiedCount_deleted_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_deleted_le

/-- info: 'STACS2027.evalClause_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalClause_congr

/-- info: 'STACS2027.extendPure' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.extendPure

/-- info: 'STACS2027.occurrences_pos_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.occurrences_pos_of_mem

/-- info: 'STACS2027.pureValue_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pureValue_of_mem

/-- info: 'STACS2027.evalClause_extendPure_kept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.evalClause_extendPure_kept

/-- info: 'STACS2027.evalClause_extendPure_deleted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.evalClause_extendPure_deleted

/-- info: 'STACS2027.satisfiedCount_extendPure_deleted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_extendPure_deleted

/-- info: 'STACS2027.satisfiedCount_extendPure_kept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_extendPure_kept

/-- info: 'STACS2027.flipAssign' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.flipAssign

/-- info: 'STACS2027.evalLiteral_flip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalLiteral_flip

/-- info: 'STACS2027.evalClause_flip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.evalClause_flip

/-- info: 'STACS2027.satisfiedCount_flipFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_flipFormula

/-- info: 'STACS2027.flipAssign_flipAssign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.flipAssign_flipAssign

/-- info: 'STACS2027.satisfiedCount_padding_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_padding_le

/-- info: 'STACS2027.padTrue' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.padTrue

/-- info: 'STACS2027.satisfiedCount_padTrue_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_padTrue_padding

/-- info: 'STACS2027.evalClause_padTrue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.evalClause_padTrue

/-- info: 'STACS2027.satisfiedCount_padTrue_kept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_padTrue_kept

/-- info: 'STACS2027.recover' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.recover

/-- info: 'STACS2027.satisfiedCount_recover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_recover

/-- info: 'STACS2027.satisfiedCount_polarize_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.satisfiedCount_polarize_ge

/-- info: 'STACS2027.polarize_maxSat_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.polarize_maxSat_eq

/-- info: 'STACS2027.polarize_lreduction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.polarize_lreduction

/-- info: 'STACS2027.count_selectedAt_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.count_selectedAt_le

/-- info: 'STACS2027.load_chosen_le_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.load_chosen_le_countP

/-- info: 'STACS2027.clauseThree5_ports_once' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseThree5_ports_once

/-- info: 'STACS2027.clauseTwo5_ports_once' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo5_ports_once

/-- info: 'STACS2027.clauseTwo6_ports_once' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseTwo6_ports_once

/-- info: 'STACS2027.clauseFamily_port_load_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseFamily_port_load_le_one

/-- info: 'STACS2027.defaultPlaced' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.defaultPlaced

/-- info: 'STACS2027.slotEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.slotEdge

/-- info: 'STACS2027.slotEdge_values' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.slotEdge_values

/-- info: 'STACS2027.slotEdge_mem_activeClausePorts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.slotEdge_mem_activeClausePorts

/-- info: 'STACS2027.sum_slots_eq_sum_activePorts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_slots_eq_sum_activePorts

/-- info: 'STACS2027.clauseChosen_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseChosen_local

/-- info: 'STACS2027.clauseChosen_port_load_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseChosen_port_load_le_one

/-- info: 'STACS2027.clauseChosen_blocked_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseChosen_blocked_lower

/-- info: 'STACS2027.clauseChosen_cost_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clauseChosen_cost_positive

/-- info: 'STACS2027.RAM.ExecB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB

/-- info: 'STACS2027.RAM.ComputesIn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ComputesIn

/-- info: 'STACS2027.RAM.ExecB.exec' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.exec

/-- info: 'STACS2027.RAM.ExecB.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.mono

/-- info: 'STACS2027.RAM.ExecB.det' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.det

/-- info: 'STACS2027.RAM.ExecB.det_exec' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.det_exec

/-- info: 'STACS2027.RAM.EqBelow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EqBelow

/-- info: 'STACS2027.RAM.EqBelow.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EqBelow.refl

/-- info: 'STACS2027.RAM.EqBelow.symm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EqBelow.symm

/-- info: 'STACS2027.RAM.EqBelow.setReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EqBelow.setReg

/-- info: 'STACS2027.RAM.EqBelow.setMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EqBelow.setMem

/-- info: 'STACS2027.RAM.EqBelow.emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EqBelow.emit

/-- info: 'STACS2027.RAM.ExecB.congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.congr

/-- info: 'STACS2027.RAM.ComputesIn.computes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ComputesIn.computes

/-- info: 'STACS2027.RAM.ComputesIn.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ComputesIn.mono

/-- info: 'STACS2027.RAM.ComputesIn.unique' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ComputesIn.unique

/-- info: 'STACS2027.RAM.ComputesIn.of_eqBelow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ComputesIn.of_eqBelow

/-- info: 'STACS2027.RAM.ComputesIn.of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ComputesIn.of_mem

/-- info: 'STACS2027.RAM.memFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree

/-- info: 'STACS2027.RAM.memFree_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_seq

/-- info: 'STACS2027.RAM.memFree_ifz' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_ifz

/-- info: 'STACS2027.RAM.memFree_loop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_loop

/-- info: 'STACS2027.RAM.Exec.toExecB_of_memFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Exec.toExecB_of_memFree

/-- info: 'STACS2027.RAM.loopFree_endpointCode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_endpointCode

/-- info: 'STACS2027.RAM.loopFree_clauseEmit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_clauseEmit

/-- info: 'STACS2027.RAM.loopFree_readLit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_readLit

/-- info: 'STACS2027.RAM.loopFree_clauseB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_clauseB

/-- info: 'STACS2027.RAM.passBpre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passBpre

/-- info: 'STACS2027.RAM.passB_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passB_eq

/-- info: 'STACS2027.RAM.InvB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvB

/-- info: 'STACS2027.RAM.AfterV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AfterV

/-- info: 'STACS2027.RAM.InvB.start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvB.start

/-- info: 'STACS2027.RAM.passBModel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passBModel

/-- info: 'STACS2027.RAM.passBCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.passBCost

/-- info: 'STACS2027.RAM.sat_passB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.sat_passB

/-- info: 'STACS2027.RAM.passBModel_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.passBModel_out

/-- info: 'STACS2027.RAM.ramConst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ramConst

/-- info: 'STACS2027.RAM.ram_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ram_computes

/-- info: 'STACS2027.RAM.mul_le_three_mul' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.mul_le_three_mul

/-- info: 'STACS2027.RAM.ramLinConst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ramLinConst

/-- info: 'STACS2027.RAM.ram_linear_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ram_linear_time

/-- info: 'STACS2027.RAM.decCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.decCost

/-- info: 'STACS2027.RAM.decSpace' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.decSpace

/-- info: 'STACS2027.RAM.PathsBelow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PathsBelow

/-- info: 'STACS2027.RAM.decInput_getD_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.decInput_getD_left

/-- info: 'STACS2027.RAM.decInput_getD_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.decInput_getD_right

/-- info: 'STACS2027.RAM.OutInvD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OutInvD

/-- info: 'STACS2027.RAM.outBodyD_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.outBodyD_step

/-- info: 'STACS2027.RAM.tabMem_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.tabMem_at

/-- info: 'STACS2027.RAM.tabMem_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.tabMem_out

/-- info: 'STACS2027.RAM.decInput_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.decInput_length

/-- info: 'STACS2027.RAM.decInput_paths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.decInput_paths

/-- info: 'STACS2027.RAM.dec_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.dec_computes

/-- info: 'STACS2027.RAM.TablesAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.TablesAt

/-- info: 'STACS2027.RAM.EdgeScratch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EdgeScratch

/-- info: 'STACS2027.RAM.readEdge_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.readEdge_run

/-- info: 'STACS2027.RAM.readEdge_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.readEdge_addrOK

/-- info: 'STACS2027.RAM.flagIfNe_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.flagIfNe_run

/-- info: 'STACS2027.RAM.flagEdge_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.flagEdge_run

/-- info: 'STACS2027.RAM.flagEdge_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.flagEdge_addrOK

/-- info: 'STACS2027.RAM.portInc_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.portInc_mem

/-- info: 'STACS2027.RAM.portInc_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.portInc_frame

/-- info: 'STACS2027.RAM.portEdgeG_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.portEdgeG_iff

/-- info: 'STACS2027.RAM.portInc_mem'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.portInc_mem'

/-- info: 'STACS2027.RAM.offOf_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.offOf_run

/-- info: 'STACS2027.RAM.offOf_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.offOf_frame

/-- info: 'STACS2027.RAM.variablePortEdge_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.variablePortEdge_cases

/-- info: 'STACS2027.RAM.CountFixed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.CountFixed

/-- info: 'STACS2027.RAM.countEdge_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.countEdge_run

/-- info: 'STACS2027.RAM.portInc_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.portInc_addrOK

/-- info: 'STACS2027.RAM.portIncs_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.portIncs_addrOK

/-- info: 'STACS2027.RAM.countTail_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.countTail_addrOK

/-- info: 'STACS2027.RAM.countEdge_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.countEdge_addrOK

/-- info: 'STACS2027.RAM.decConst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.decConst

/-- info: 'STACS2027.RAM.pathLoop_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.pathLoop_sum

/-- info: 'STACS2027.RAM.decCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.decCost_le

/-- info: 'STACS2027.RAM.flatMap_pathCode_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.flatMap_pathCode_length

/-- info: 'STACS2027.RAM.ramInput_length_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ramInput_length_ge

/-- info: 'STACS2027.RAM.dec_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.dec_linear

/-- info: 'STACS2027.RAM.clauseFamily_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseFamily_length_le

/-- info: 'STACS2027.RAM.formulaFamily_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.formulaFamily_length_le

/-- info: 'STACS2027.RAM.validChoices_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.validChoices_shape

/-- info: 'STACS2027.RAM.decLinConst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.decLinConst

/-- info: 'STACS2027.RAM.decSpaceConst' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.decSpaceConst

/-- info: 'STACS2027.RAM.decSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.decSpace_le

/-- info: 'STACS2027.RAM.decoder_linear_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.decoder_linear_time

/-- info: 'STACS2027.RAM.decoder_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.decoder_ram

/-- info: 'STACS2027.RAM.wMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.wMem

/-- info: 'STACS2027.RAM.wMemE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.wMemE

/-- info: 'STACS2027.RAM.wMem_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.wMem_below

/-- info: 'STACS2027.RAM.wMemE_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.wMemE_below

/-- info: 'STACS2027.RAM.wMemE_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.wMemE_nil

/-- info: 'STACS2027.RAM.wMemE_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.wMemE_snoc

/-- info: 'STACS2027.RAM.clauseLoad_snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseLoad_snoc
