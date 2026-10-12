module

import Outerplanar

/-!
Exact-message axiom guards for every explicitly named Outerplanar declaration.
The supplemental shared deletion modules listed in scripts/lean_declarations.py
are covered by the same exact guards.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.Algo.Comb.headD_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.headD_mem

/-- info: 'STACS2027.Algo.Comb.selected_zero_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.selected_zero_perm

/-- info: 'STACS2027.Algo.Comb.selected_zero_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.selected_zero_sub

/-- info: 'STACS2027.Algo.Comb.cost_selected_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.cost_selected_zero

/-- info: 'STACS2027.Algo.Comb.isMinCost_family_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.isMinCost_family_iff

/-- info: 'STACS2027.Algo.Comb.optimalAssignmentOutput_of_cost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.optimalAssignmentOutput_of_cost_zero

/-- info: 'STACS2027.Algo.Comb.cost_flatMap_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.cost_flatMap_disjoint

/-- info: 'STACS2027.Algo.Comb.flatMap_flatten_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.flatMap_flatten_eq

/-- info: 'STACS2027.Algo.Comb.overlap_zero_of_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.overlap_zero_of_blocks

/-- info: 'STACS2027.Algo.Comb.cycle_in_head_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.cycle_in_head_block

/-- info: 'STACS2027.Algo.Comb.cost_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.cost_blocks

/-- info: 'STACS2027.Algo.optimalAssignmentOutput_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.optimalAssignmentOutput_blocks

/-- info: 'STACS2027.Algo.Comb.selected_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.selected_map

/-- info: 'STACS2027.Algo.Comb.isCycle_of_edge_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.isCycle_of_edge_iff

/-- info: 'STACS2027.Algo.optimalAssignmentOutput_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.optimalAssignmentOutput_relabel

/-- info: 'STACS2027.Algo.Comb.eraseDups_nodup'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.eraseDups_nodup'

/-- info: 'STACS2027.Algo.Comb.labels_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.labels_nodup

/-- info: 'STACS2027.Algo.Comb.mem_proper' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.mem_proper

/-- info: 'STACS2027.Algo.Comb.mem_labels_of_proper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.mem_labels_of_proper

/-- info: 'STACS2027.Algo.Comb.labelOf_idOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.labelOf_idOf

/-- info: 'STACS2027.Algo.Comb.idOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.idOf_lt

/-- info: 'STACS2027.Algo.Comb.labelOf_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.labelOf_mem

/-- info: 'STACS2027.Algo.Comb.labelOf_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.labelOf_inj

/-- info: 'STACS2027.Algo.Comb.mem_idEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.mem_idEdges

/-- info: 'STACS2027.Algo.Comb.edge_edge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.edge_edge

/-- info: 'STACS2027.Algo.Comb.idEdges_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.idEdges_below

/-- info: 'STACS2027.Algo.Comb.idEdges_normalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.idEdges_normalized

/-- info: 'STACS2027.Algo.Comb.mapEdge_labelOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.mapEdge_labelOf

/-- info: 'STACS2027.Algo.Comb.edge_iff_idEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.edge_iff_idEdges

/-- info: 'STACS2027.Algo.optimalAssignmentOutput_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.optimalAssignmentOutput_labels

/-- info: 'STACS2027.Algo.solveWith_eq_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.solveWith_eq_map

/-- info: 'STACS2027.Algo.Comb.walkWithin_map' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.walkWithin_map

/-- info: 'STACS2027.Algo.Comb.HasMinor.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.HasMinor.map

/-- info: 'STACS2027.Algo.Comb.labelExt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.labelExt

/-- info: 'STACS2027.Algo.Comb.labelExt_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.labelExt_injective

/-- info: 'STACS2027.Algo.Comb.adj_labelExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.adj_labelExt

/-- info: 'STACS2027.Algo.hasMinor_of_idEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.hasMinor_of_idEdges

/-- info: 'STACS2027.Algo.k23MinorFree_idEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.k23MinorFree_idEdges

/-- info: 'STACS2027.Algo.not_hasMinor_k4_idEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.not_hasMinor_k4_idEdges

/-- info: 'STACS2027.Algo.outerplanar_idEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.outerplanar_idEdges

/-- info: 'STACS2027.Poly.length_cfg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.length_cfg

/-- info: 'STACS2027.Poly.getElem_cfg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.getElem_cfg

/-- info: 'STACS2027.Poly.getD_cfg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.getD_cfg

/-- info: 'STACS2027.Poly.cfg_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.cfg_lt

/-- info: 'STACS2027.Poly.cfg_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.cfg_zero

/-- info: 'STACS2027.Poly.cfg_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.cfg_succ

/-- info: 'STACS2027.Poly.enc_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.enc_lt

/-- info: 'STACS2027.Poly.cfg_enc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.cfg_enc

/-- info: 'STACS2027.Poly.enc_cfg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.enc_cfg

/-- info: 'STACS2027.Poly.foldl_min' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.foldl_min

/-- info: 'STACS2027.Poly.argmin_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.argmin_fold

/-- info: 'STACS2027.Ear.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.State

/-- info: 'STACS2027.Ear.update2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.update2

/-- info: 'STACS2027.Ear.initAdj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.initAdj

/-- info: 'STACS2027.Ear.init' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.init

/-- info: 'STACS2027.Ear.pushIf2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pushIf2

/-- info: 'STACS2027.Ear.decDeg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.decDeg

/-- info: 'STACS2027.Ear.elim' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.elim

/-- info: 'STACS2027.Ear.step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.step

/-- info: 'STACS2027.Ear.loop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.loop

/-- info: 'STACS2027.Ear.reinsert' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.reinsert

/-- info: 'STACS2027.Ear.walk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.walk

/-- info: 'STACS2027.Ear.earHam' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.earHam

/-- info: 'STACS2027.Ear.adjEntry' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.adjEntry

/-- info: 'STACS2027.Ear.adjEntry_eq_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.adjEntry_eq_some

/-- info: 'STACS2027.Ear.initAdj_foldl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.initAdj_foldl

/-- info: 'STACS2027.Ear.initAdj_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.initAdj_eq

/-- info: 'STACS2027.Ear.mem_initAdj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.mem_initAdj

/-- info: 'STACS2027.Ear.nodup_filterMap_adjEntry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.nodup_filterMap_adjEntry

/-- info: 'STACS2027.Ear.nodup_initAdj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.nodup_initAdj

/-- info: 'STACS2027.Ear.foldl_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.foldl_mat

/-- info: 'STACS2027.Ear.adj_iff_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.adj_iff_mem

/-- info: 'STACS2027.Ear.init_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.init_mat

/-- info: 'STACS2027.Ear.nbrs_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.nbrs_init

/-- info: 'STACS2027.Ear.inv_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.inv_init

/-- info: 'STACS2027.Ear.getD_rotate_idxOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.getD_rotate_idxOf

/-- info: 'STACS2027.Ear.outerplanarHam_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.outerplanarHam_walk

/-- info: 'STACS2027.Ear.recon' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.recon

/-- info: 'STACS2027.Ear.earHam_eq_recon' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.earHam_eq_recon

/-- info: 'STACS2027.Ear.recon_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.recon_correct

/-- info: 'STACS2027.Ear.earHam_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.earHam_correct

/-- info: 'STACS2027.Ear.Fwd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.Fwd

/-- info: 'STACS2027.Ear.Rep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.Rep

/-- info: 'STACS2027.Ear.Fwd.isRotated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Fwd.isRotated

/-- info: 'STACS2027.Ear.Rep.isRotated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Rep.isRotated

/-- info: 'STACS2027.Ear.reinsert_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.reinsert_eq

/-- info: 'STACS2027.Ear.fwd_reinsert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.fwd_reinsert

/-- info: 'STACS2027.Ear.rep_reinsert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.rep_reinsert

/-- info: 'STACS2027.Ear.walk_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.walk_fwd

/-- info: 'STACS2027.Ear.walk_fwd_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.walk_fwd_length

/-- info: 'STACS2027.Ear.fwd_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.fwd_three

/-- info: 'STACS2027.Ear.rep_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.rep_three

/-- info: 'STACS2027.Ear.nbrs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.nbrs

/-- info: 'STACS2027.Ear.Inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.Inv

/-- info: 'STACS2027.Ear.two_le_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.two_le_length

/-- info: 'STACS2027.Ear.eq_pair_of_length_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.eq_pair_of_length_two

/-- info: 'STACS2027.Ear.matGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.matGraph

/-- info: 'STACS2027.Ear.adj_matGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.adj_matGraph

/-- info: 'STACS2027.Ear.Inv.matSymm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.Inv.matSymm

/-- info: 'STACS2027.Ear.Inv.two_le_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Inv.two_le_deg

/-- info: 'STACS2027.Ear.Inv.exists_deg_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Inv.exists_deg_two

/-- info: 'STACS2027.Ear.Inv.stack_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Inv.stack_ne_nil

/-- info: 'STACS2027.Ear.filter_kill' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.filter_kill

/-- info: 'STACS2027.Ear.length_filter_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.length_filter_ne

/-- info: 'STACS2027.Ear.filter_ne_of_not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.filter_ne_of_not_mem

/-- info: 'STACS2027.Ear.ElimCtx' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx

/-- info: 'STACS2027.Ear.ElimCtx.nodupC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.nodupC

/-- info: 'STACS2027.Ear.ElimCtx.v_notMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.v_notMem

/-- info: 'STACS2027.Ear.ElimCtx.memH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.memH

/-- info: 'STACS2027.Ear.ElimCtx.memC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.memC

/-- info: 'STACS2027.Ear.ElimCtx.uw_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.uw_mem

/-- info: 'STACS2027.Ear.ElimCtx.u_ne_w' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.u_ne_w

/-- info: 'STACS2027.Ear.ElimCtx.mat_vu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.mat_vu

/-- info: 'STACS2027.Ear.ElimCtx.mat_av' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.mat_av

/-- info: 'STACS2027.Ear.ElimCtx.mat_new' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.mat_new

/-- info: 'STACS2027.Ear.ElimCtx.nbrs_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.nbrs_new

/-- info: 'STACS2027.Ear.ElimCtx.inv_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.inv_elim

/-- info: 'STACS2027.Ear.Inv.elimCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Inv.elimCtx

/-- info: 'STACS2027.Ear.Inv.skip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.Inv.skip

/-- info: 'STACS2027.Ear.Inv.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Inv.step

/-- info: 'STACS2027.Ear.Inv.loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Inv.loop

/-- info: 'STACS2027.Ear.PState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.PState

/-- info: 'STACS2027.Ear.palive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.palive

/-- info: 'STACS2027.Ear.pdec' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pdec

/-- info: 'STACS2027.Ear.premove' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.premove

/-- info: 'STACS2027.Ear.pstep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.pstep

/-- info: 'STACS2027.Ear.pstackPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pstackPre

/-- info: 'STACS2027.Ear.pinit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pinit

/-- info: 'STACS2027.Ear.foldl_pdec_rm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.foldl_pdec_rm

/-- info: 'STACS2027.Ear.foldl_pdec_o1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.foldl_pdec_o1

/-- info: 'STACS2027.Ear.foldl_pdec_o2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.foldl_pdec_o2

/-- info: 'STACS2027.Ear.foldl_pdec_pd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.foldl_pdec_pd

/-- info: 'STACS2027.Ear.foldl_pdec_stack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.foldl_pdec_stack

/-- info: 'STACS2027.Ear.AdjOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.AdjOK

/-- info: 'STACS2027.Ear.PInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.PInv

/-- info: 'STACS2027.Ear.pinv_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.pinv_init

/-- info: 'STACS2027.Ear.PInv.length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.PInv.length_le

/-- info: 'STACS2027.Ear.mem_getD_of_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.mem_getD_of_le_two

/-- info: 'STACS2027.Ear.getD_mem_or' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.getD_mem_or

/-- info: 'STACS2027.Ear.PInv.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.PInv.step

/-- info: 'STACS2027.Ear.PInv.pstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.PInv.pstep

/-- info: 'STACS2027.Ear.ppot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ppot

/-- info: 'STACS2027.Ear.ppot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ppot_step

/-- info: 'STACS2027.Ear.ppot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ppot_le

/-- info: 'STACS2027.Ear.PInv.all_removed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.PInv.all_removed

/-- info: 'STACS2027.Ear.PInv.orientation' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.PInv.orientation

/-- info: 'STACS2027.Ear.adjOK_initAdj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.adjOK_initAdj

/-- info: 'STACS2027.Ear.peel_orient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.peel_orient

/-- info: 'STACS2027.Ear.pushIf2_adj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pushIf2_adj

/-- info: 'STACS2027.Ear.pushIf2_mat' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pushIf2_mat

/-- info: 'STACS2027.Ear.pushIf2_deg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pushIf2_deg

/-- info: 'STACS2027.Ear.pushIf2_dead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pushIf2_dead

/-- info: 'STACS2027.Ear.pushIf2_log' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pushIf2_log

/-- info: 'STACS2027.Ear.pushIf2_cnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pushIf2_cnt

/-- info: 'STACS2027.Ear.pushIf2_stack' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pushIf2_stack

/-- info: 'STACS2027.Ear.decDeg_adj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.decDeg_adj

/-- info: 'STACS2027.Ear.decDeg_mat' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.decDeg_mat

/-- info: 'STACS2027.Ear.decDeg_dead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.decDeg_dead

/-- info: 'STACS2027.Ear.decDeg_log' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.decDeg_log

/-- info: 'STACS2027.Ear.decDeg_cnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.decDeg_cnt

/-- info: 'STACS2027.Ear.decDeg_deg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.decDeg_deg

/-- info: 'STACS2027.Ear.decDeg_stack' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.decDeg_stack

/-- info: 'STACS2027.Ear.elim_dead' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_dead

/-- info: 'STACS2027.Ear.elim_cnt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_cnt

/-- info: 'STACS2027.Ear.elim_log' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_log

/-- info: 'STACS2027.Ear.elim_mat_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_mat_true

/-- info: 'STACS2027.Ear.elim_adj_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_adj_true

/-- info: 'STACS2027.Ear.elim_deg_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_deg_true

/-- info: 'STACS2027.Ear.elim_mat_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_mat_false

/-- info: 'STACS2027.Ear.elim_adj_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_adj_false

/-- info: 'STACS2027.Ear.elim_deg_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_deg_false

/-- info: 'STACS2027.Ear.elim_stack_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_stack_false

/-- info: 'STACS2027.Ear.elim_stack_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_stack_true

/-- info: 'STACS2027.Ear.mem_elim_stack' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.mem_elim_stack

/-- info: 'STACS2027.Ear.elim_stack_u' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_stack_u

/-- info: 'STACS2027.Ear.elim_stack_w' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_stack_w

/-- info: 'STACS2027.Ear.elim_stack_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_stack_sub

/-- info: 'STACS2027.Ear.elim_stack_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.elim_stack_length

/-- info: 'STACS2027.Ear.step_skip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.step_skip

/-- info: 'STACS2027.Ear.step_elim' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.step_elim

/-- info: 'STACS2027.Ear.pot' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Ear.pot

/-- info: 'STACS2027.Ear.pot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.pot_step

/-- info: 'STACS2027.Ear.pot_init_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.pot_init_le

/-- info: 'STACS2027.Ear.loop_stopped_of_pot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.loop_stopped_of_pot

/-- info: 'STACS2027.Ear.loop_stopped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.loop_stopped

/-- info: 'STACS2027.Ear.Consec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.Consec

/-- info: 'STACS2027.Ear.Consec.symm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.Consec.symm

/-- info: 'STACS2027.Ear.Consec.isRotated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Consec.isRotated

/-- info: 'STACS2027.Ear.consec_ends' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.consec_ends

/-- info: 'STACS2027.Ear.Consec.drop_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Consec.drop_head

/-- info: 'STACS2027.Ear.not_consec_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.not_consec_ends

/-- info: 'STACS2027.Ear.Static' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Ear.Static

/-- info: 'STACS2027.Ear.static_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.static_init

/-- info: 'STACS2027.Ear.inv_static_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.inv_static_init

/-- info: 'STACS2027.Ear.ElimCtx.static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.ElimCtx.static

/-- info: 'STACS2027.Ear.Inv.step_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.Inv.step_static

/-- info: 'STACS2027.Ear.query_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Ear.query_static

/-- info: 'STACS2027.Poly.lastNb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.lastNb

/-- info: 'STACS2027.Poly.predNb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.predNb

/-- info: 'STACS2027.Poly.walkTo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.walkTo

/-- info: 'STACS2027.Poly.faceWalk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.faceWalk

/-- info: 'STACS2027.Poly.mem_nbP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_nbP

/-- info: 'STACS2027.Poly.mem_nbP_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_nbP_iff

/-- info: 'STACS2027.Poly.nbP_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.nbP_pairwise

/-- info: 'STACS2027.Poly.getLastD_eq_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.getLastD_eq_of_le

/-- info: 'STACS2027.Poly.predNb_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.predNb_eq

/-- info: 'STACS2027.Poly.lastNb_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.lastNb_eq

/-- info: 'STACS2027.Poly.walkTo_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.walkTo_eq

/-- info: 'STACS2027.Poly.faceWalk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.faceWalk_eq

/-- info: 'STACS2027.Algo.proper' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.proper

/-- info: 'STACS2027.Algo.labels' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.labels

/-- info: 'STACS2027.Algo.numV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.numV

/-- info: 'STACS2027.Algo.idOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.idOf

/-- info: 'STACS2027.Algo.labelOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.labelOf

/-- info: 'STACS2027.Algo.idEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.idEdges

/-- info: 'STACS2027.Algo.nbOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.nbOf

/-- info: 'STACS2027.Algo.dfsOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.dfsOf

/-- info: 'STACS2027.Algo.lowStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.lowStep

/-- info: 'STACS2027.Algo.lowOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.lowOf

/-- info: 'STACS2027.Algo.headOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.headOf

/-- info: 'STACS2027.Algo.lowerOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.lowerOf

/-- info: 'STACS2027.Algo.blocksOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.blocksOf

/-- info: 'STACS2027.Algo.solveWith' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.solveWith

/-- info: 'STACS2027.Algo.k4Base' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.k4Base

/-- info: 'STACS2027.Algo.k4Out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.k4Out

/-- info: 'STACS2027.Algo.k4Out_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.k4Out_three

/-- info: 'STACS2027.Algo.k4Out_four' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.k4Out_four

/-- info: 'STACS2027.Algo.k4Out_large' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.k4Out_large

/-- info: 'STACS2027.Algo.Comb.k4Base_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.k4Base_three

/-- info: 'STACS2027.Algo.Comb.k4Base_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.k4Base_four

/-- info: 'STACS2027.Algo.Comb.k4Base_output_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.k4Base_output_of

/-- info: 'STACS2027.Algo.Comb.k4Base_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.Comb.k4Base_output

/-- info: 'STACS2027.Algo.optimalAssignmentOutput_k4Out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.optimalAssignmentOutput_k4Out

/-- info: 'STACS2027.Algo.nodup_eraseDups_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.nodup_eraseDups_aux

/-- info: 'STACS2027.Algo.nodup_eraseDups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.nodup_eraseDups

/-- info: 'STACS2027.Algo.mem_proper' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.mem_proper

/-- info: 'STACS2027.Algo.mem_labels' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.mem_labels

/-- info: 'STACS2027.Algo.idOf_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.idOf_lt

/-- info: 'STACS2027.Algo.idOf_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.idOf_inj

/-- info: 'STACS2027.Algo.mem_idEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.mem_idEdges

/-- info: 'STACS2027.Algo.idEdges_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.idEdges_lt

/-- info: 'STACS2027.Algo.idEdges_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.idEdges_nodup

/-- info: 'STACS2027.Algo.mem_nbOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.mem_nbOf

/-- info: 'STACS2027.Algo.adj_iff_mem_nbOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.adj_iff_mem_nbOf

/-- info: 'STACS2027.Algo.lt_of_isVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.lt_of_isVertex

/-- info: 'STACS2027.Algo.mem_range_of_isVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.mem_range_of_isVertex

/-- info: 'STACS2027.Algo.ok_idEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.ok_idEdges

/-- info: 'STACS2027.Algo.foldr_update_apply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.foldr_update_apply

/-- info: 'STACS2027.Algo.foldl_update_apply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.foldl_update_apply

/-- info: 'STACS2027.Algo.foldl_min_le_init' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.foldl_min_le_init

/-- info: 'STACS2027.Algo.foldl_min_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.foldl_min_le

/-- info: 'STACS2027.Algo.foldl_min_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.foldl_min_cases

/-- info: 'STACS2027.Algo.foldl_min_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.foldl_min_congr

/-- info: 'STACS2027.Algo.lowStep_le_pre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.lowStep_le_pre

/-- info: 'STACS2027.Algo.lowStep_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.lowStep_le

/-- info: 'STACS2027.Algo.lowStep_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.lowStep_cases

/-- info: 'STACS2027.Algo.lowStep_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.lowStep_congr

/-- info: 'STACS2027.Algo.mem_right_of_pre_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.mem_right_of_pre_lt

/-- info: 'STACS2027.Algo.mem_left_of_pre_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.mem_left_of_pre_lt

/-- info: 'STACS2027.Algo.lowOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.lowOf_eq

/-- info: 'STACS2027.Algo.headOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.headOf_eq

/-- info: 'STACS2027.Algo.exists_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.exists_child

/-- info: 'STACS2027.Algo.head_of_isHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.head_of_isHead

/-- info: 'STACS2027.Algo.IsLow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.IsLow

/-- info: 'STACS2027.Algo.lowerOf_eq_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.lowerOf_eq_lower

/-- info: 'STACS2027.Algo.vis_of_isVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.vis_of_isVertex

/-- info: 'STACS2027.Algo.isLow_lowOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.isLow_lowOf

/-- info: 'STACS2027.Algo.isHead_iff_lowOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.isHead_iff_lowOf

/-- info: 'STACS2027.Algo.headOf_lowOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.headOf_lowOf

/-- info: 'STACS2027.Algo.nb_iff_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.nb_iff_adj

/-- info: 'STACS2027.Algo.palm_dfsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.palm_dfsOf

/-- info: 'STACS2027.Algo.isHead_iff_dfsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.isHead_iff_dfsOf

/-- info: 'STACS2027.Algo.isLow_dfsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.isLow_dfsOf

/-- info: 'STACS2027.Algo.headOf_dfsOf_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.headOf_dfsOf_root

/-- info: 'STACS2027.Algo.headOf_dfsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.headOf_dfsOf

/-- info: 'STACS2027.Algo.adj_of_mem_idEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.adj_of_mem_idEdges

/-- info: 'STACS2027.Algo.lowerOf_dfsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.lowerOf_dfsOf

/-- info: 'STACS2027.Algo.blocksOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.blocksOf_eq

/-- info: 'STACS2027.Poly.nbP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.nbP

/-- info: 'STACS2027.Poly.segEnum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.segEnum

/-- info: 'STACS2027.Poly.segOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.segOrder

/-- info: 'STACS2027.Poly.pairs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.pairs

/-- info: 'STACS2027.Poly.slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.slots

/-- info: 'STACS2027.Poly.childSegs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.childSegs

/-- info: 'STACS2027.Poly.extendParts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Poly.extendParts

/-- info: 'STACS2027.Poly.rpF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.rpF

/-- info: 'STACS2027.Poly.pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.pool

/-- info: 'STACS2027.Poly.topOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Poly.topOf

/-- info: 'STACS2027.Poly.cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.cyc

/-- info: 'STACS2027.Poly.bnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.bnd

/-- info: 'STACS2027.Poly.topIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.topIdx

/-- info: 'STACS2027.Poly.rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.rel

/-- info: 'STACS2027.Poly.owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.owned

/-- info: 'STACS2027.Poly.cfg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.cfg

/-- info: 'STACS2027.Poly.enc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Poly.enc

/-- info: 'STACS2027.Poly.loadAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.loadAt

/-- info: 'STACS2027.Poly.localCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.localCost

/-- info: 'STACS2027.Poly.childIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.childIdx

/-- info: 'STACS2027.Poly.tabArg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.tabArg

/-- info: 'STACS2027.Poly.table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.table

/-- info: 'STACS2027.Poly.argTab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.argTab

/-- info: 'STACS2027.Poly.backtrack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.backtrack

/-- info: 'STACS2027.Poly.valOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.valOf

/-- info: 'STACS2027.Poly.rotateTo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Poly.rotateTo

/-- info: 'STACS2027.Poly.polyOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.polyOut

/-- info: 'STACS2027.Poly.btStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.btStep

/-- info: 'STACS2027.Poly.backtrack_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.backtrack_eq

/-- info: 'STACS2027.Poly.foldl_update_apply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.foldl_update_apply

/-- info: 'STACS2027.Poly.BtInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.BtInv

/-- info: 'STACS2027.Poly.childSegs_size_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.childSegs_size_lt

/-- info: 'STACS2027.Poly.childSegs_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.childSegs_unique

/-- info: 'STACS2027.Poly.foldr_btInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.foldr_btInv

/-- info: 'STACS2027.Poly.backtrack_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.backtrack_inv

/-- info: 'STACS2027.Poly.chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.chosen

/-- info: 'STACS2027.Poly.vOf_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.vOf_chosen

/-- info: 'STACS2027.Poly.map_topIdx_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.map_topIdx_chosen

/-- info: 'STACS2027.Poly.bnd_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.bnd_root

/-- info: 'STACS2027.Poly.map_bnd_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.map_bnd_chosen

/-- info: 'STACS2027.Poly.chosen_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.chosen_local

/-- info: 'STACS2027.Poly.total_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.total_chosen

/-- info: 'STACS2027.Poly.isMinCost_total_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.isMinCost_total_chosen

/-- info: 'STACS2027.Poly.getD_append_left'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.getD_append_left'

/-- info: 'STACS2027.Poly.getD_append_right'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.getD_append_right'

/-- info: 'STACS2027.Poly.getD_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.getD_mem

/-- info: 'STACS2027.Poly.filter_range_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.filter_range_append

/-- info: 'STACS2027.Poly.length_filter_range_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.length_filter_range_getD

/-- info: 'STACS2027.Poly.filter_range_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.filter_range_flatMap

/-- info: 'STACS2027.Poly.getD_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.getD_flatMap

/-- info: 'STACS2027.Poly.topIdx_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.topIdx_eq

/-- info: 'STACS2027.Poly.cyc_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.cyc_eq

/-- info: 'STACS2027.Poly.length_topIdx_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.length_topIdx_le

/-- info: 'STACS2027.Poly.sum_map_le_filter_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.sum_map_le_filter_mul

/-- info: 'STACS2027.Poly.countP_interval_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.countP_interval_lt

/-- info: 'STACS2027.Poly.length_tops_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.length_tops_le

/-- info: 'STACS2027.Poly.length_bnd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.length_bnd_le

/-- info: 'STACS2027.Poly.vOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.vOf

/-- info: 'STACS2027.Poly.idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.idx

/-- info: 'STACS2027.Poly.vOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.vOf_lt

/-- info: 'STACS2027.Poly.vOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.vOf_eq

/-- info: 'STACS2027.Poly.cyc_eq_getElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.cyc_eq_getElem

/-- info: 'STACS2027.Poly.mem_pool_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_pool_iff

/-- info: 'STACS2027.Poly.cyc_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.cyc_mem

/-- info: 'STACS2027.Poly.idx_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.idx_lt

/-- info: 'STACS2027.Poly.cyc_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.cyc_idx

/-- info: 'STACS2027.Poly.idx_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.idx_cyc

/-- info: 'STACS2027.Poly.idx_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.idx_injective

/-- info: 'STACS2027.Poly.vOf_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.vOf_idx

/-- info: 'STACS2027.Poly.topOf_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.topOf_eq_top

/-- info: 'STACS2027.Poly.top_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.top_eq_iff

/-- info: 'STACS2027.Poly.mem_topIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_topIdx

/-- info: 'STACS2027.Poly.mem_bnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_bnd

/-- info: 'STACS2027.Poly.nodup_topIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.nodup_topIdx

/-- info: 'STACS2027.Poly.nodup_bnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.nodup_bnd

/-- info: 'STACS2027.Poly.nodup_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.nodup_rel

/-- info: 'STACS2027.Poly.lt_of_mem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.lt_of_mem_rel

/-- info: 'STACS2027.Poly.idx_mem_topIdx_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.idx_mem_topIdx_iff

/-- info: 'STACS2027.Poly.idx_mem_bnd_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.idx_mem_bnd_iff

/-- info: 'STACS2027.Poly.vOf_upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.vOf_upd

/-- info: 'STACS2027.Poly.map_bnd_upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.map_bnd_upd

/-- info: 'STACS2027.Poly.map_topIdx_upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.map_topIdx_upd

/-- info: 'STACS2027.Poly.exists_map_topIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.exists_map_topIdx

/-- info: 'STACS2027.Poly.card_filter_eq_countP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.card_filter_eq_countP

/-- info: 'STACS2027.Poly.countP_zip_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.countP_zip_map

/-- info: 'STACS2027.Poly.idx_mem_rel_of_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.idx_mem_rel_of_owned

/-- info: 'STACS2027.Poly.loadAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.loadAt_eq

/-- info: 'STACS2027.Poly.localCost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.localCost_eq

/-- info: 'STACS2027.Poly.sum_childSegs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.sum_childSegs

/-- info: 'STACS2027.Poly.bnd_child_mem_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.bnd_child_mem_rel

/-- info: 'STACS2027.Poly.childIdx_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.childIdx_eq

/-- info: 'STACS2027.Poly.cfg_enc_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.cfg_enc_map

/-- info: 'STACS2027.Poly.enc_map_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.enc_map_lt

/-- info: 'STACS2027.Poly.stepTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.stepTotal

/-- info: 'STACS2027.Poly.tabArg_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.tabArg_succ

/-- info: 'STACS2027.Poly.tabArg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.tabArg_spec

/-- info: 'STACS2027.Poly.mem_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_pairs

/-- info: 'STACS2027.Poly.map_fst_pairs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.map_fst_pairs

/-- info: 'STACS2027.Poly.pairs_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.pairs_nodup

/-- info: 'STACS2027.Poly.mem_segEnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_segEnum

/-- info: 'STACS2027.Poly.segEnum_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.segEnum_nodup

/-- info: 'STACS2027.Poly.mem_segOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_segOrder

/-- info: 'STACS2027.Poly.segOrder_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.segOrder_nodup

/-- info: 'STACS2027.Poly.segOrder_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.segOrder_size

/-- info: 'STACS2027.Poly.mem_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_slots

/-- info: 'STACS2027.Poly.slots_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.slots_nodup

/-- info: 'STACS2027.Poly.childSegs_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.childSegs_nodup

/-- info: 'STACS2027.Poly.mem_childSegs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_childSegs

/-- info: 'STACS2027.Poly.owned_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.owned_nodup

/-- info: 'STACS2027.Poly.mem_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_owned

/-- info: 'STACS2027.Poly.PolyFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.PolyFacts

/-- info: 'STACS2027.Poly.rotateTo_isCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.rotateTo_isCycle

/-- info: 'STACS2027.Poly.headD_rotateTo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.headD_rotateTo

/-- info: 'STACS2027.Poly.polyOut_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.polyOut_eq

/-- info: 'STACS2027.Poly.optimalAssignmentOutput_polyOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.optimalAssignmentOutput_polyOut

/-- info: 'STACS2027.Poly.topOf_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.topOf_eq

/-- info: 'STACS2027.Poly.topOf_of_isRPath' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.topOf_of_isRPath

/-- info: 'STACS2027.Poly.topOf_of_mem_rpF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.topOf_of_mem_rpF

/-- info: 'STACS2027.Poly.isRPath_of_convexCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.isRPath_of_convexCycle

/-- info: 'STACS2027.Poly.straddle_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.straddle_gap

/-- info: 'STACS2027.Poly.ends_mem_of_inside_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.ends_mem_of_inside_outside

/-- info: 'STACS2027.Poly.mem_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_pool

/-- info: 'STACS2027.Poly.pool_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.pool_nodup

/-- info: 'STACS2027.Poly.mem_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_boundary

/-- info: 'STACS2027.Poly.polyFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.polyFacts

/-- info: 'STACS2027.Poly.mem_extendParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_extendParts

/-- info: 'STACS2027.Poly.joins_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.joins_ne_nil

/-- info: 'STACS2027.Poly.mem_foldl_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_foldl_sound

/-- info: 'STACS2027.Poly.mem_foldl_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_foldl_complete

/-- info: 'STACS2027.Poly.nodup_extendParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.nodup_extendParts

/-- info: 'STACS2027.Poly.nodup_foldl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.nodup_foldl

/-- info: 'STACS2027.Poly.rpF_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.rpF_two

/-- info: 'STACS2027.Poly.rpF_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.rpF_zero

/-- info: 'STACS2027.Poly.rpF_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.rpF_succ

/-- info: 'STACS2027.Poly.faceVerts_eq_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.faceVerts_eq_cons

/-- info: 'STACS2027.Poly.sound_rpF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.sound_rpF

/-- info: 'STACS2027.Poly.mem_rpF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.mem_rpF

/-- info: 'STACS2027.Poly.rpF_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.rpF_nodup

/-- info: 'STACS2027.Poly.foldl_extendParts_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.foldl_extendParts_congr

/-- info: 'STACS2027.Poly.rpF_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.rpF_fuel

/-- info: 'STACS2027.Poly.rpF_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.rpF_eq_nil

/-- info: 'STACS2027.Poly.length_rpF_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.length_rpF_le

/-- info: 'STACS2027.Poly.partsBound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Poly.partsBound

/-- info: 'STACS2027.Poly.length_extendParts_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.length_extendParts_le

/-- info: 'STACS2027.Poly.foldl_extendParts_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.foldl_extendParts_inv

/-- info: 'STACS2027.Poly.foldl_rpF_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Poly.foldl_rpF_bound

/-- info: 'STACS2027.Algo.blockVerts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.blockVerts

/-- info: 'STACS2027.Algo.localEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.localEdges

/-- info: 'STACS2027.Algo.solveBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.solveBlock

/-- info: 'STACS2027.Algo.solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.solve

/-- info: 'STACS2027.Algo.SolveAux.edge_of_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.SolveAux.edge_of_lt

/-- info: 'STACS2027.Algo.SolveAux.adj_of_mem_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.SolveAux.adj_of_mem_lt

/-- info: 'STACS2027.Algo.SolveAux.edge_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.SolveAux.edge_cases

/-- info: 'STACS2027.Algo.SolveAux.isVertex_of_mem_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.SolveAux.isVertex_of_mem_cycle

/-- info: 'STACS2027.Algo.SolveAux.getD_eq_getElem'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.SolveAux.getD_eq_getElem'

/-- info: 'STACS2027.Algo.SolveAux.getD_idxOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.SolveAux.getD_idxOf

/-- info: 'STACS2027.Algo.SolveAux.idxOf_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.SolveAux.idxOf_getD

/-- info: 'STACS2027.Algo.SolveAux.getD_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.SolveAux.getD_mem

/-- info: 'STACS2027.Algo.SolveAux.getD_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.SolveAux.getD_inj

/-- info: 'STACS2027.Algo.mem_blockVerts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.mem_blockVerts

/-- info: 'STACS2027.Algo.blockVerts_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.blockVerts_nodup

/-- info: 'STACS2027.Algo.ends_mem_blockVerts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.ends_mem_blockVerts

/-- info: 'STACS2027.Algo.isVertex_iff_mem_blockVerts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.isVertex_iff_mem_blockVerts

/-- info: 'STACS2027.Algo.mem_localEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.mem_localEdges

/-- info: 'STACS2027.Algo.localEdges_normalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.localEdges_normalized

/-- info: 'STACS2027.Algo.localEdges_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.localEdges_below

/-- info: 'STACS2027.Algo.localEdges_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.localEdges_lt

/-- info: 'STACS2027.Algo.localEdges_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.localEdges_nodup

/-- info: 'STACS2027.Algo.adj_localEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.adj_localEdges

/-- info: 'STACS2027.Algo.adj_localEdges_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.adj_localEdges_cases

/-- info: 'STACS2027.Algo.mapGraph_localEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.mapGraph_localEdges

/-- info: 'STACS2027.Algo.optimalAssignmentOutput_ofLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.optimalAssignmentOutput_ofLocal

/-- info: 'STACS2027.Algo.OuterplanarHam.relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.OuterplanarHam.relabel

/-- info: 'STACS2027.Algo.OuterplanarHam.of_adj_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.OuterplanarHam.of_adj_iff

/-- info: 'STACS2027.Algo.length_of_outerplanarHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.length_of_outerplanarHam

/-- info: 'STACS2027.Algo.ends_mem_ham' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Algo.ends_mem_ham

/-- info: 'STACS2027.Algo.isPolygon_localEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.isPolygon_localEdges

/-- info: 'STACS2027.Algo.optimalAssignmentOutput_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.optimalAssignmentOutput_small

/-- info: 'STACS2027.Algo.k4Edges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Algo.k4Edges

/-- info: 'STACS2027.Algo.edge_mem_k4Edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.edge_mem_k4Edges

/-- info: 'STACS2027.Algo.k4Edges_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.k4Edges_nodup

/-- info: 'STACS2027.Algo.k4Edges_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.k4Edges_sub

/-- info: 'STACS2027.Algo.IsK4Graph.counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.IsK4Graph.counts

/-- info: 'STACS2027.Algo.optimalAssignmentOutput_k4Block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.optimalAssignmentOutput_k4Block

/-- info: 'STACS2027.Algo.isVertex_localEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.isVertex_localEdges

/-- info: 'STACS2027.Algo.optimalAssignmentOutput_outerBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.optimalAssignmentOutput_outerBlock

/-- info: 'STACS2027.Algo.optimalAssignmentOutput_solveBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.optimalAssignmentOutput_solveBlock

/-- info: 'STACS2027.Algo.idBlock_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.idBlock_lt

/-- info: 'STACS2027.Algo.idBlock_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.idBlock_nodup

/-- info: 'STACS2027.Algo.idBlock_twoConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.idBlock_twoConnected

/-- info: 'STACS2027.Algo.solve_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.solve_correct

/-- info: 'STACS2027.Algo.solve_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.solve_optimal

/-- info: 'STACS2027.Algo.solve_optimal_outerplanar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Algo.solve_optimal_outerplanar

/-- info: 'STACS2027.TreeDP.Tree.induction_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Tree.induction_sub

/-- info: 'STACS2027.TreeDP.Problem.upd_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.upd_self

/-- info: 'STACS2027.TreeDP.Problem.tot_eq_dp_of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.tot_eq_dp_of_local

/-- info: 'STACS2027.TreeDP.Problem.total_eq_dp_of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.total_eq_dp_of_local

/-- info: 'STACS2027.Palm.InBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.InBlock

/-- info: 'STACS2027.Palm.head_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.head_self

/-- info: 'STACS2027.Palm.par_not_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.par_not_below

/-- info: 'STACS2027.Palm.tree_edge_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.tree_edge_block

/-- info: 'STACS2027.Palm.isVertex_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.isVertex_block

/-- info: 'STACS2027.Palm.inBlock_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.inBlock_between

/-- info: 'STACS2027.Palm.reach_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.reach_up

/-- info: 'STACS2027.Palm.twoConnected_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.twoConnected_block

/-- info: 'STACS2027.walk_of_pathEdges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.walk_of_pathEdges

/-- info: 'STACS2027.IsCycle.walk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.walk

/-- info: 'STACS2027.IsCycle.adj_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.adj_wrap

/-- info: 'STACS2027.WalkWithin.of_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WalkWithin.of_mem

/-- info: 'STACS2027.WalkWithin.left' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WalkWithin.left

/-- info: 'STACS2027.WalkWithin.right' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WalkWithin.right

/-- info: 'STACS2027.Palm.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.lower

/-- info: 'STACS2027.Palm.lower_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.lower_cases

/-- info: 'STACS2027.Palm.lower_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.lower_comm

/-- info: 'STACS2027.Palm.block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.block

/-- info: 'STACS2027.Palm.adj_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.adj_block

/-- info: 'STACS2027.Palm.block_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.block_sub

/-- info: 'STACS2027.Palm.walk_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.walk_sep

/-- info: 'STACS2027.Palm.cycle_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.cycle_sep

/-- info: 'STACS2027.Palm.lower_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.lower_facts

/-- info: 'STACS2027.Palm.cycle_in_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.cycle_in_block

/-- info: 'STACS2027.ConvexCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ConvexCycle

/-- info: 'STACS2027.ConvexCycle.isCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ConvexCycle.isCycle

/-- info: 'STACS2027.IsPolygon.step_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.step_side

/-- info: 'STACS2027.IsPolygon.walk_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.walk_side

/-- info: 'STACS2027.IsPolygon.cycle_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.cycle_side

/-- info: 'STACS2027.edge_mem_pathEdges_of_gap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_mem_pathEdges_of_gap

/-- info: 'STACS2027.edge_last_head_mem_cycleEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_last_head_mem_cycleEdges

/-- info: 'STACS2027.pathEdges_subset_cycleEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathEdges_subset_cycleEdges

/-- info: 'STACS2027.head_eq_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.head_eq_of_le

/-- info: 'STACS2027.getLast_eq_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.getLast_eq_of_le

/-- info: 'STACS2027.edge_max_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_max_min

/-- info: 'STACS2027.edge_min_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_min_max

/-- info: 'STACS2027.mem_of_mem_cycleEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_of_mem_cycleEdges

/-- info: 'STACS2027.IsPolygon.convex_of_isCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.convex_of_isCycle

/-- info: 'STACS2027.ConvexCycle.eq_of_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.ConvexCycle.eq_of_sameCycle

/-- info: 'STACS2027.DFS.State' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.State

/-- info: 'STACS2027.DFS.step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.step

/-- info: 'STACS2027.DFS.init' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.init

/-- info: 'STACS2027.DFS.Halted' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.Halted

/-- info: 'STACS2027.DFS.run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.run

/-- info: 'STACS2027.DFS.Anc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.Anc

/-- info: 'STACS2027.DFS.Rel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.Rel

/-- info: 'STACS2027.DFS.StackPath' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.StackPath

/-- info: 'STACS2027.DFS.Ok' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.Ok

/-- info: 'STACS2027.DFS.Inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.Inv

/-- info: 'STACS2027.DFS.rel_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.rel_symm

/-- info: 'STACS2027.DFS.stack_anc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.stack_anc

/-- info: 'STACS2027.DFS.iterate_vis' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.iterate_vis

/-- info: 'STACS2027.DFS.iterate_update' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.iterate_update

/-- info: 'STACS2027.DFS.anc_update_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.anc_update_iff

/-- info: 'STACS2027.DFS.rel_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.rel_update

/-- info: 'STACS2027.DFS.stackPath_update' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.stackPath_update

/-- info: 'STACS2027.DFS.getD_mem_nb' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.getD_mem_nb

/-- info: 'STACS2027.DFS.inv_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.inv_init

/-- info: 'STACS2027.DFS.inv_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.inv_root

/-- info: 'STACS2027.DFS.inv_skip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.inv_skip

/-- info: 'STACS2027.DFS.inv_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.inv_push

/-- info: 'STACS2027.DFS.inv_exam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.inv_exam

/-- info: 'STACS2027.DFS.inv_pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.inv_pop

/-- info: 'STACS2027.DFS.inv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.inv_step

/-- info: 'STACS2027.DFS.OrdInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.OrdInv

/-- info: 'STACS2027.DFS.ordInv_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.ordInv_init

/-- info: 'STACS2027.DFS.ordInv_visit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.ordInv_visit

/-- info: 'STACS2027.DFS.ordInv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.ordInv_step

/-- info: 'STACS2027.DFS.ordInv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.ordInv_run

/-- info: 'STACS2027.DFS.mu' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.DFS.mu

/-- info: 'STACS2027.DFS.sum_map_le_aux' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.sum_map_le_aux

/-- info: 'STACS2027.DFS.sum_map_lt_aux' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.sum_map_lt_aux

/-- info: 'STACS2027.DFS.length_filter_eq_sum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.length_filter_eq_sum

/-- info: 'STACS2027.DFS.unvisited_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.unvisited_lt

/-- info: 'STACS2027.DFS.unvisited_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.unvisited_le

/-- info: 'STACS2027.DFS.ptrsum_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.ptrsum_lt

/-- info: 'STACS2027.DFS.mu_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.mu_step

/-- info: 'STACS2027.DFS.step_halted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.step_halted

/-- info: 'STACS2027.DFS.run_halted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.run_halted

/-- info: 'STACS2027.DFS.inv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.inv_run

/-- info: 'STACS2027.DFS.halted_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.halted_run

/-- info: 'STACS2027.DFS.final' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.DFS.final

/-- info: 'STACS2027.DFS.final_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.final_inv

/-- info: 'STACS2027.DFS.final_halted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.final_halted

/-- info: 'STACS2027.DFS.final_ordInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.final_ordInv

/-- info: 'STACS2027.DFS.palm_of_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DFS.palm_of_final

/-- info: 'STACS2027.exists_palm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_palm

/-- info: 'STACS2027.convexList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.convexList

/-- info: 'STACS2027.convexCycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.convexCycles

/-- info: 'STACS2027.polyEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.polyEdges

/-- info: 'STACS2027.IsPolygon.mem_convexList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_convexList

/-- info: 'STACS2027.IsPolygon.mem_convexCycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_convexCycles

/-- info: 'STACS2027.IsPolygon.convexList_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.convexList_nodup

/-- info: 'STACS2027.IsPolygon.mem_polyEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_polyEdges

/-- info: 'STACS2027.IsPolygon.ne_nil_of_mem_convexCycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.ne_nil_of_mem_convexCycles

/-- info: 'STACS2027.CycVar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.CycVar

/-- info: 'STACS2027.omitted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.omitted

/-- info: 'STACS2027.cycLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycLoad

/-- info: 'STACS2027.polygonProblem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.polygonProblem

/-- info: 'STACS2027.IsPolygon.load_map_eq_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.load_map_eq_length

/-- info: 'STACS2027.IsPolygon.cost_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.cost_family

/-- info: 'STACS2027.IsPolygon.convexList_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.convexList_complete

/-- info: 'STACS2027.IsPolygon.hasAssignment_iff_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.hasAssignment_iff_family

/-- info: 'STACS2027.IsPolygon.chooseOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.chooseOf

/-- info: 'STACS2027.IsPolygon.chooseOf_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.chooseOf_mem

/-- info: 'STACS2027.IsPolygon.card_filter_cycVar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.card_filter_cycVar

/-- info: 'STACS2027.IsPolygon.total_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.total_eq

/-- info: 'STACS2027.IsPolygon.dp_root_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.dp_root_optimal

/-- info: 'STACS2027.IsPolygon.dp_table_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.dp_table_correct

/-- info: 'STACS2027.Adj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Adj

/-- info: 'STACS2027.IsVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsVertex

/-- info: 'STACS2027.WalkWithin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WalkWithin

/-- info: 'STACS2027.ConnectedWithin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ConnectedWithin

/-- info: 'STACS2027.TwoConnected' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.TwoConnected

/-- info: 'STACS2027.HasMinor' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.HasMinor

/-- info: 'STACS2027.k23' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.k23

/-- info: 'STACS2027.K23MinorFree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.K23MinorFree

/-- info: 'STACS2027.Outerplanar' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Outerplanar

/-- info: 'STACS2027.IsK4Graph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsK4Graph

/-- info: 'STACS2027.OuterplanarHam' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam

/-- info: 'STACS2027.TwoConnectedK23Structure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.TwoConnectedK23Structure

/-- info: 'STACS2027.IsMinCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsMinCost

/-- info: 'STACS2027.OptimalAssignmentOutput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OptimalAssignmentOutput

/-- info: 'STACS2027.AtMostTwo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.AtMostTwo

/-- info: 'STACS2027.Gap' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Gap

/-- info: 'STACS2027.atMostTwo_of_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.atMostTwo_of_gaps

/-- info: 'STACS2027.IsPolygon.polygon_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.polygon_degenerate

/-- info: 'STACS2027.outerplanarHam_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanarHam_degenerate

/-- info: 'STACS2027.ElimList' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ElimList

/-- info: 'STACS2027.exists_elimList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_elimList

/-- info: 'STACS2027.elimList_suffix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.elimList_suffix

/-- info: 'STACS2027.eliminationOrder_of_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.eliminationOrder_of_degenerate

/-- info: 'STACS2027.IsPolygon.ear_away_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.ear_away_first

/-- info: 'STACS2027.LowDegree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.LowDegree

/-- info: 'STACS2027.OuterplanarHam.position_isVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.position_isVertex

/-- info: 'STACS2027.OuterplanarHam.ear_away_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.ear_away_head

/-- info: 'STACS2027.OuterplanarHam.ear_away_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.ear_away_vertex

/-- info: 'STACS2027.joinPaths' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.joinPaths

/-- info: 'STACS2027.rpathsAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rpathsAux

/-- info: 'STACS2027.rpaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rpaths

/-- info: 'STACS2027.rpathBound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.rpathBound

/-- info: 'STACS2027.infix_pair_head' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.infix_pair_head

/-- info: 'STACS2027.sound_joinPaths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sound_joinPaths

/-- info: 'STACS2027.complete_joinPaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.complete_joinPaths

/-- info: 'STACS2027.idxOf_append_of_isRPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.idxOf_append_of_isRPath

/-- info: 'STACS2027.nodup_joinPaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.nodup_joinPaths

/-- info: 'STACS2027.sum_map_le_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_le_mul

/-- info: 'STACS2027.length_joinPaths_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.length_joinPaths_le

/-- info: 'STACS2027.rpathBound_le_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rpathBound_le_succ

/-- info: 'STACS2027.rpathBound_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rpathBound_mono

/-- info: 'STACS2027.sound_rpathsAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sound_rpathsAux

/-- info: 'STACS2027.IsPolygon.mem_rpathsAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_rpathsAux

/-- info: 'STACS2027.IsPolygon.nodup_rpathsAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.nodup_rpathsAux

/-- info: 'STACS2027.IsPolygon.length_rpathsAux_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.length_rpathsAux_le

/-- info: 'STACS2027.IsPolygon.mem_rpaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_rpaths

/-- info: 'STACS2027.IsPolygon.nodup_rpaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.nodup_rpaths

/-- info: 'STACS2027.IsPolygon.length_rpaths_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.length_rpaths_le

/-- info: 'STACS2027.IsPolygon.mem_rpaths_iff_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_rpaths_iff_convex

/-- info: 'STACS2027.ChordlessCycle' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ChordlessCycle

/-- info: 'STACS2027.IsPolygon.face_chordless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.face_chordless

/-- info: 'STACS2027.IsPolygon.chordless_convex_iff_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.chordless_convex_iff_face

/-- info: 'STACS2027.IsPolygon.chordless_cycle_iff_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.chordless_cycle_iff_face

/-- info: 'STACS2027.ChordlessCycle.of_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.ChordlessCycle.of_sameCycle

/-- info: 'STACS2027.BoundedFaceBoundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundedFaceBoundary

/-- info: 'STACS2027.IsPolygon.bounded_face_boundary_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.bounded_face_boundary_iff

/-- info: 'STACS2027.OuterplanarHam.chordless_posGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.chordless_posGraph

/-- info: 'STACS2027.OuterplanarHam.bounded_face_boundary_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.bounded_face_boundary_iff

/-- info: 'STACS2027.inducedGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.inducedGraph

/-- info: 'STACS2027.adj_inducedGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.adj_inducedGraph

/-- info: 'STACS2027.isCycle_inducedGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isCycle_inducedGraph

/-- info: 'STACS2027.chordless_inducedGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chordless_inducedGraph

/-- info: 'STACS2027.bounded_face_inducedGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.bounded_face_inducedGraph

/-- info: 'STACS2027.IsPolygon.faceEdges_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.faceEdges_injective

/-- info: 'STACS2027.IsPolygon.leaf_delete_faces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_delete_faces

/-- info: 'STACS2027.BoundaryDualAdj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.BoundaryDualAdj

/-- info: 'STACS2027.IsPolygon.boundary_dual_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.boundary_dual_iff

/-- info: 'STACS2027.IsPolygon.leaf_delete_face_bijection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_delete_face_bijection

/-- info: 'STACS2027.IsPolygon.leaf_delete_weakDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_delete_weakDual

/-- info: 'STACS2027.IsFaceVert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsFaceVert

/-- info: 'STACS2027.faceVerts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.faceVerts

/-- info: 'STACS2027.head?_eq_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.head?_eq_of_le

/-- info: 'STACS2027.getLast?_eq_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.getLast?_eq_of_le

/-- info: 'STACS2027.infix_pair_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.infix_pair_iff

/-- info: 'STACS2027.mem_faceVerts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_faceVerts

/-- info: 'STACS2027.faceVerts_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.faceVerts_pairwise

/-- info: 'STACS2027.isFaceVert_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isFaceVert_left

/-- info: 'STACS2027.isFaceVert_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isFaceVert_right

/-- info: 'STACS2027.left_mem_faceVerts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.left_mem_faceVerts

/-- info: 'STACS2027.right_mem_faceVerts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.right_mem_faceVerts

/-- info: 'STACS2027.faceVerts_head?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.faceVerts_head?

/-- info: 'STACS2027.faceVerts_getLast?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.faceVerts_getLast?

/-- info: 'STACS2027.of_mem_segs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.of_mem_segs

/-- info: 'STACS2027.IsPolygon.face_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.face_gap

/-- info: 'STACS2027.IsPolygon.infix_faceVerts_of_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.infix_faceVerts_of_child

/-- info: 'STACS2027.IsPolygon.child_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.child_iff

/-- info: 'STACS2027.IsPolygon.adj_of_infix_faceVerts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.adj_of_infix_faceVerts

/-- info: 'STACS2027.IsPolygon.infix_faceVerts_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.infix_faceVerts_lt

/-- info: 'STACS2027.IsPolygon.three_le_length_faceVerts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.three_le_length_faceVerts

/-- info: 'STACS2027.outerplanar_algorithm_perfect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanar_algorithm_perfect

/-- info: 'STACS2027.outerplanar_algorithm_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanar_algorithm_assignment

/-- info: 'STACS2027.lowDegree_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.lowDegree_split

/-- info: 'STACS2027.lowDegree_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.lowDegree_small

/-- info: 'STACS2027.outerplanar_lowDegree_away' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanar_lowDegree_away

/-- info: 'STACS2027.outerplanar_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanar_degenerate

/-- info: 'STACS2027.outerplanarDrawing_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanarDrawing_degenerate

/-- info: 'STACS2027.outerplanar_eliminationOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanar_eliminationOrder

/-- info: 'STACS2027.outerplanarDrawing_subgraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanarDrawing_subgraph

/-- info: 'STACS2027.HypEuler.EulerOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.HypEuler.EulerOK

/-- info: 'STACS2027.HypEuler.eulerOK_of_moveE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.eulerOK_of_moveE

/-- info: 'STACS2027.HypEuler.eulerOK_induct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.eulerOK_induct

/-- info: 'STACS2027.HypEuler.iterate_of_forall_fixed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.iterate_of_forall_fixed

/-- info: 'STACS2027.HypEuler.cycleCount_of_forall_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.cycleCount_of_forall_fixed

/-- info: 'STACS2027.HypEuler.linked_of_forall_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.linked_of_forall_fixed

/-- info: 'STACS2027.HypEuler.eulerOK_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.eulerOK_of_fixed

/-- info: 'STACS2027.HypEuler.rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.rot

/-- info: 'STACS2027.HypEuler.rot_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.rot_linked

/-- info: 'STACS2027.HypEuler.rot_eulerOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.rot_eulerOK

/-- info: 'STACS2027.HypEuler.eulerOK_of_node_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.eulerOK_of_node_fixed

/-- info: 'STACS2027.HypEuler.eulerOK_of_edge_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.eulerOK_of_edge_fixed

/-- info: 'STACS2027.HypEuler.eulerOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.eulerOK

/-- info: 'STACS2027.hypermapEuler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hypermapEuler

/-- info: 'Complexity.Hypermap.planar_iff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.Hypermap.planar_iff_eq

/-- info: 'Complexity.Hypermap.planar_iff_euler_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.Hypermap.planar_iff_euler_eq

/-- info: 'STACS2027.HypEuler.orbitPrefix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.HypEuler.orbitPrefix

/-- info: 'STACS2027.HypEuler.orbitPrefix_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.orbitPrefix_length

/-- info: 'STACS2027.HypEuler.orbitPrefix_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.orbitPrefix_nodup

/-- info: 'STACS2027.HypEuler.orbitPrefix_cmin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.orbitPrefix_cmin

/-- info: 'STACS2027.HypEuler.flatMap_orbit_lists_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.flatMap_orbit_lists_nodup

/-- info: 'STACS2027.HypEuler.sum_orbit_lists_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.sum_orbit_lists_le

/-- info: 'STACS2027.HypEuler.sum_map_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.sum_map_ge

/-- info: 'STACS2027.HypEuler.sum_map_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.sum_map_ge_one

/-- info: 'STACS2027.HypEuler.cycleCount_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.cycleCount_mul_le

/-- info: 'STACS2027.HypEuler.orbit_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.orbit_count

/-- info: 'STACS2027.HypEuler.cycleLen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.cycleLen

/-- info: 'STACS2027.HypEuler.cycleLen_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.cycleLen_spec

/-- info: 'STACS2027.HypEuler.le_cycleLen_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.le_cycleLen_iff

/-- info: 'STACS2027.HypEuler.mem_orbitPrefix_cycleLen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.mem_orbitPrefix_cycleLen

/-- info: 'STACS2027.HypEuler.sum_cycleLen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.sum_cycleLen

/-- info: 'STACS2027.HypEuler.dartEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.dartEnd

/-- info: 'STACS2027.HypEuler.dartOther' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.dartOther

/-- info: 'STACS2027.HypEuler.halfEdgeEnd_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.halfEdgeEnd_eq

/-- info: 'STACS2027.HypEuler.IsGraphEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.IsGraphEmbedding

/-- info: 'STACS2027.HypEuler.edge_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.edge_edge

/-- info: 'STACS2027.HypEuler.same_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.same_entry

/-- info: 'STACS2027.HypEuler.dartEnd_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.dartEnd_edge

/-- info: 'STACS2027.HypEuler.dartOther_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.dartOther_edge

/-- info: 'STACS2027.HypEuler.dartEnd_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.dartEnd_eq_iff

/-- info: 'STACS2027.HypEuler.dartEnd_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.dartEnd_node

/-- info: 'STACS2027.HypEuler.dartEnd_iterate_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.dartEnd_iterate_node

/-- info: 'STACS2027.HypEuler.node_face' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.node_face

/-- info: 'STACS2027.HypEuler.dartEnd_face' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.dartEnd_face

/-- info: 'STACS2027.HypEuler.node_ne_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.node_ne_self

/-- info: 'STACS2027.HypEuler.linkedPath_of_dartEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.linkedPath_of_dartEnd

/-- info: 'STACS2027.HypEuler.linkedPath_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.linkedPath_edge

/-- info: 'STACS2027.HypEuler.face_ne_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.face_ne_self

/-- info: 'STACS2027.HypEuler.face_face_ne_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.face_face_ne_self

/-- info: 'STACS2027.HypEuler.face_return_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.face_return_even

/-- info: 'STACS2027.HypEuler.SimpleEdgeList' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.HypEuler.SimpleEdgeList

/-- info: 'STACS2027.HypEuler.SimpleEdgeList.loopless' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.SimpleEdgeList.loopless

/-- info: 'STACS2027.HypEuler.dart_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.dart_pair

/-- info: 'STACS2027.HypEuler.SimpleEdgeList.simple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.SimpleEdgeList.simple

/-- info: 'STACS2027.HypEuler.face_girth_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.face_girth_three

/-- info: 'STACS2027.HypEuler.face_girth_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.face_girth_four

/-- info: 'STACS2027.HypEuler.edge_cycleCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.edge_cycleCount

/-- info: 'STACS2027.HypEuler.node_cycleCount_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.node_cycleCount_le

/-- info: 'STACS2027.HypEuler.euler_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.euler_graph

/-- info: 'STACS2027.HypEuler.three_mul_faces_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.three_mul_faces_le

/-- info: 'STACS2027.HypEuler.four_mul_faces_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.four_mul_faces_le

/-- info: 'STACS2027.HypEuler.componentCount_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.componentCount_pos

/-- info: 'STACS2027.HypEuler.swap_b' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.swap_b

/-- info: 'STACS2027.HypEuler.transpose_b'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.transpose_b'

/-- info: 'STACS2027.HypEuler.moveE' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE

/-- info: 'STACS2027.HypEuler.moveE_edge_a' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_edge_a

/-- info: 'STACS2027.HypEuler.moveE_edge_b' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_edge_b

/-- info: 'STACS2027.HypEuler.moveE_edge_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_edge_other

/-- info: 'STACS2027.HypEuler.moveE_face_a' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_face_a

/-- info: 'STACS2027.HypEuler.moveE_face_ea' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_face_ea

/-- info: 'STACS2027.HypEuler.moveE_face_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_face_other

/-- info: 'STACS2027.HypEuler.moveE_node' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_node

/-- info: 'STACS2027.HypEuler.moveE_edge_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_edge_cycles

/-- info: 'STACS2027.HypEuler.edge_edge_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.HypEuler.edge_edge_ne

/-- info: 'STACS2027.HypEuler.moveE_face_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_face_split

/-- info: 'STACS2027.HypEuler.moveE_face_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_face_merge

/-- info: 'STACS2027.HypEuler.moveE_mergedLabel_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_mergedLabel_invariant

/-- info: 'STACS2027.HypEuler.moveE_components_le_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_components_le_add_one

/-- info: 'STACS2027.HypEuler.moveE_step_transfer_of_faces_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_step_transfer_of_faces_ne

/-- info: 'STACS2027.HypEuler.moveE_path_transfer_of_faces_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_path_transfer_of_faces_ne

/-- info: 'STACS2027.HypEuler.moveE_components_le_of_faces_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_components_le_of_faces_ne

/-- info: 'STACS2027.HypEuler.nonFixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.nonFixed

/-- info: 'STACS2027.HypEuler.moveE_nonFixed_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.moveE_nonFixed_lt

/-- info: 'STACS2027.WalkWithin.reach_all' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WalkWithin.reach_all

/-- info: 'STACS2027.hamiltonian_cycle_twoConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hamiltonian_cycle_twoConnected

/-- info: 'STACS2027.leafDelete' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.leafDelete

/-- info: 'STACS2027.adj_leafDelete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.adj_leafDelete

/-- info: 'STACS2027.IsPolygon.leaf_delete_outerplanar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_delete_outerplanar

/-- info: 'STACS2027.IsPolygon.leaf_delete_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_delete_edges

/-- info: 'STACS2027.IsPolygon.side_vertices_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.side_vertices_retained

/-- info: 'STACS2027.IsPolygon.leaf_delete_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_delete_hamiltonian

/-- info: 'STACS2027.IsPolygon.leaf_delete_twoConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_delete_twoConnected

/-- info: 'STACS2027.IsDualLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsDualLeaf

/-- info: 'STACS2027.leafInterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.leafInterior

/-- info: 'STACS2027.IsPolygon.face_path_of_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.face_path_of_edge

/-- info: 'STACS2027.IsPolygon.dual_leaf_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.dual_leaf_cases

/-- info: 'STACS2027.IsPolygon.leaf_delete_face_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_delete_face_edges

/-- info: 'STACS2027.IsPolygon.leaf_delete_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_delete_interior

/-- info: 'STACS2027.IsPolygon.root_leaf_delete_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_delete_interior

/-- info: 'STACS2027.IsPolygon.leaf_face_deletion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_face_deletion

/-- info: 'STACS2027.k23_linear_ram_solve_of_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k23_linear_ram_solve_of_structure

/-- info: 'STACS2027.k23_linear_ram_of_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k23_linear_ram_of_structure

/-- info: 'STACS2027.solve_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.solve_optimal

/-- info: 'STACS2027.k23_linear_ram_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k23_linear_ram_solve

/-- info: 'STACS2027.k23_linear_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k23_linear_ram

/-- info: 'STACS2027.outerplanar_linear_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanar_linear_ram

/-- info: 'STACS2027.CommonNeighbours2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.CommonNeighbours2

/-- info: 'STACS2027.WalkWithin.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WalkWithin.mono

/-- info: 'STACS2027.ConnectedWithin.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.ConnectedWithin.mono

/-- info: 'STACS2027.HasMinor.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.HasMinor.mono

/-- info: 'STACS2027.connectedWithin_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.connectedWithin_singleton

/-- info: 'STACS2027.hasMinor_of_embedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.hasMinor_of_embedding

/-- info: 'STACS2027.common_neighbours_le_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.common_neighbours_le_two

/-- info: 'STACS2027.commonNeighbourBound_of_k23MinorFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.commonNeighbourBound_of_k23MinorFree

/-- info: 'STACS2027.IsK4Graph.hasMinor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsK4Graph.hasMinor

/-- info: 'STACS2027.Outerplanar.k23MinorFree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Outerplanar.k23MinorFree

/-- info: 'STACS2027.EnclosingCycleCountBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.EnclosingCycleCountBound

/-- info: 'STACS2027.EnclosedFacesBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.EnclosedFacesBound

/-- info: 'STACS2027.IsPolygon.enclosed_faces_child_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.enclosed_faces_child_dichotomy

/-- info: 'STACS2027.IsPolygon.top_face_iff_parent_not_enclosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.top_face_iff_parent_not_enclosed

/-- info: 'STACS2027.IsPolygon.boundary_iff_parent_enclosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.boundary_iff_parent_enclosed

/-- info: 'STACS2027.IsPolygon.cycle_child_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.cycle_child_dichotomy

/-- info: 'STACS2027.IsPolygon.enclosed_length_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.enclosed_length_identity

/-- info: 'STACS2027.IsPolygon.enclosed_faces_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.enclosed_faces_bound

/-- info: 'STACS2027.IsPolygon.triangle_eq_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.triangle_eq_face

/-- info: 'STACS2027.IsPolygon.triangle_face_count_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.triangle_face_count_bound

/-- info: 'STACS2027.IsPolygon.neighborhood_exponent_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.neighborhood_exponent_bound

/-- info: 'STACS2027.IsPolygon.enclosing_cycle_count_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.enclosing_cycle_count_bound

/-- info: 'STACS2027.enclosedFacesBound_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.enclosedFacesBound_proved

/-- info: 'STACS2027.enclosingCycleCountBound_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.enclosingCycleCountBound_proved

/-- info: 'STACS2027.PlanarTriangleGeometry.neighbourGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.neighbourGraph

/-- info: 'STACS2027.PlanarTriangleGeometry.adj_neighbourGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.adj_neighbourGraph

/-- info: 'STACS2027.PlanarTriangleGeometry.cone' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.cone

/-- info: 'STACS2027.PlanarTriangleGeometry.neighbour_walk_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.neighbour_walk_head

/-- info: 'STACS2027.PlanarTriangleGeometry.neighbour_minor_cone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.neighbour_minor_cone

/-- info: 'STACS2027.OuterFaceCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterFaceCond

/-- info: 'STACS2027.outerplanarEmbedding_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.outerplanarEmbedding_iff

/-- info: 'STACS2027.linked_of_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.linked_of_commute

/-- info: 'STACS2027.iterate_commute' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.iterate_commute

/-- info: 'STACS2027.OuterFaceCond.dartEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterFaceCond.dartEquiv

/-- info: 'STACS2027.graphDartEquiv_embedding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.graphDartEquiv_embedding

/-- info: 'STACS2027.OuterplanarEmbedding.of_graphDartEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.of_graphDartEquiv

/-- info: 'STACS2027.OuterplanarEmbedding.perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.perm

/-- info: 'STACS2027.outerplanarEmbedding_perm_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanarEmbedding_perm_iff

/-- info: 'STACS2027.halfEdgeEnd_isEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.halfEdgeEnd_isEnd

/-- info: 'STACS2027.outerplanarEmbedding_map_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanarEmbedding_map_iff

/-- info: 'STACS2027.OuterplanarEmbedding.map_injOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.map_injOn

/-- info: 'STACS2027.RepEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RepEdges

/-- info: 'STACS2027.RepEdges.perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RepEdges.perm

/-- info: 'STACS2027.RepEdges.outerplanarEmbedding_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RepEdges.outerplanarEmbedding_iff

/-- info: 'STACS2027.eraseDups_nodup_of_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.eraseDups_nodup_of_length

/-- info: 'STACS2027.nodup_simpleEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.nodup_simpleEdges

/-- info: 'STACS2027.mem_simpleEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_simpleEdges

/-- info: 'STACS2027.simpleEdges_rep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.simpleEdges_rep

/-- info: 'STACS2027.OuterplanarDrawing.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarDrawing.congr

/-- info: 'STACS2027.outerplanarDrawing_iff_minorFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanarDrawing_iff_minorFree

/-- info: 'STACS2027.outerplanarDrawing_iff_outerplanar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanarDrawing_iff_outerplanar

/-- info: 'STACS2027.outerplanar_block_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanar_block_structure

/-- info: 'STACS2027.outerplanarEmbedding_of_minorFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanarEmbedding_of_minorFree

/-- info: 'STACS2027.OuterplanarHam.outerplanarEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.outerplanarEmbedding

/-- info: 'STACS2027.twoConnected_outerplanar_or_k4_of_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.twoConnected_outerplanar_or_k4_of_rep

/-- info: 'STACS2027.outerplanarDrawing_of_minorFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outerplanarDrawing_of_minorFree

/-- info: 'STACS2027.OuterplanarHam.outerplanarDrawing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.outerplanarDrawing

/-- info: 'STACS2027.twoConnected_outerplanar_or_k4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.twoConnected_outerplanar_or_k4

/-- info: 'STACS2027.swap_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.swap_left

/-- info: 'STACS2027.swap_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.swap_right

/-- info: 'STACS2027.swap_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.swap_other

/-- info: 'STACS2027.iterate_swapComp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.iterate_swapComp

/-- info: 'STACS2027.swapComp_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.swapComp_reaches

/-- info: 'STACS2027.swapComp_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.swapComp_cycles

/-- info: 'STACS2027.transpose_reaches_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.transpose_reaches_iff

/-- info: 'STACS2027.glueMap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.glueMap

/-- info: 'STACS2027.glueMap_node' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.glueMap_node

/-- info: 'STACS2027.glueMap_face' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.glueMap_face

/-- info: 'STACS2027.glue_label_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.glue_label_step

/-- info: 'STACS2027.glue_label_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.glue_label_path

/-- info: 'STACS2027.glue_linked_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.glue_linked_cases

/-- info: 'STACS2027.glue_path_of_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.glue_path_of_path

/-- info: 'STACS2027.glue_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.glue_components

/-- info: 'STACS2027.iterate_eq_of_closed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.iterate_eq_of_closed

/-- info: 'STACS2027.disjointSum_node_reaches_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_node_reaches_left

/-- info: 'STACS2027.disjointSum_node_reaches_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_node_reaches_right

/-- info: 'STACS2027.disjointSum_node_not_lr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_node_not_lr

/-- info: 'STACS2027.disjointSum_node_not_rl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_node_not_rl

/-- info: 'STACS2027.disjointSum_node_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_node_sep

/-- info: 'STACS2027.disjointSum_face_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_face_sep

/-- info: 'STACS2027.outer_dart_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outer_dart_at

/-- info: 'STACS2027.outer_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.outer_linked

/-- info: 'STACS2027.SphOuter.append_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SphOuter.append_glue

/-- info: 'STACS2027.exists_dart_of_isEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_dart_of_isEnd

/-- info: 'STACS2027.SphOuter.append_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SphOuter.append_cut

/-- info: 'STACS2027.RepEdges.lt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RepEdges.lt

/-- info: 'STACS2027.RepEdges.adj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RepEdges.adj

/-- info: 'STACS2027.RepEdges.mem_of_adj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RepEdges.mem_of_adj

/-- info: 'STACS2027.RepEdges.isEnd_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RepEdges.isEnd_iff

/-- info: 'STACS2027.OuterplanarHam.sphOuter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.sphOuter

/-- info: 'STACS2027.polyHyp_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.polyHyp_single

/-- info: 'STACS2027.sphOuter_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sphOuter_single

/-- info: 'STACS2027.vset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.vset

/-- info: 'STACS2027.edge_fst_snd_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_fst_snd_of_lt

/-- info: 'STACS2027.edge_snd_fst_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_snd_fst_of_lt

/-- info: 'STACS2027.mem_vset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_vset

/-- info: 'STACS2027.adj_filter' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.adj_filter

/-- info: 'STACS2027.split_sphOuter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.split_sphOuter

/-- info: 'STACS2027.small_sphOuter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.small_sphOuter

/-- info: 'STACS2027.sphOuter_of_minorFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sphOuter_of_minorFree

/-- info: 'STACS2027.chordLabel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.chordLabel

/-- info: 'STACS2027.PolyOuter' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PolyOuter

/-- info: 'STACS2027.polyLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.polyLabel

/-- info: 'STACS2027.isLong' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.isLong

/-- info: 'STACS2027.downDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.downDart

/-- info: 'STACS2027.downDart_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.downDart_ends

/-- info: 'STACS2027.PolyHyp.chordLabel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.chordLabel_step

/-- info: 'STACS2027.PolyHyp.pkey_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.pkey_succ

/-- info: 'STACS2027.PolyHyp.polyOuter_of_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.polyOuter_of_key

/-- info: 'STACS2027.PolyHyp.key_of_polyOuter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.key_of_polyOuter

/-- info: 'STACS2027.PolyHyp.polyLabel_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.polyLabel_face

/-- info: 'STACS2027.PolyHyp.short_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.short_count

/-- info: 'STACS2027.PolyHyp.long_add_short' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.long_add_short

/-- info: 'STACS2027.PolyHyp.downDart_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.downDart_label

/-- info: 'STACS2027.PolyHyp.faces_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.faces_ge

/-- info: 'STACS2027.PolyHyp.succDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.succDart

/-- info: 'STACS2027.PolyHyp.nodes_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.nodes_ge

/-- info: 'STACS2027.PolyHyp.predDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.predDart

/-- info: 'STACS2027.PolyHyp.linked_predDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.linked_predDart

/-- info: 'STACS2027.PolyHyp.components_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.components_le

/-- info: 'STACS2027.PolyHyp.sphOuter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.sphOuter

/-- info: 'STACS2027.pkey' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pkey

/-- info: 'STACS2027.pdec' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pdec

/-- info: 'STACS2027.pdec_pkey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pdec_pkey

/-- info: 'STACS2027.pkey_pdec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pkey_pdec

/-- info: 'STACS2027.pkey_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pkey_pos

/-- info: 'STACS2027.pkey_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pkey_lt

/-- info: 'STACS2027.pdec_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pdec_lt

/-- info: 'STACS2027.PolyHyp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp

/-- info: 'STACS2027.nbrKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.nbrKeys

/-- info: 'STACS2027.polySucc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.polySucc

/-- info: 'STACS2027.polyPred' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.polyPred

/-- info: 'STACS2027.mem_nbrKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_nbrKeys

/-- info: 'STACS2027.nbrKeys_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.nbrKeys_sorted

/-- info: 'STACS2027.nbrKeys_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.nbrKeys_nodup

/-- info: 'STACS2027.pdec_adjs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pdec_adjs

/-- info: 'STACS2027.pkey_pdec_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pkey_pdec_mem

/-- info: 'STACS2027.key_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.key_bounds

/-- info: 'STACS2027.sorted_index_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sorted_index_lt

/-- info: 'STACS2027.PolyHyp.adjs_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.adjs_bounds

/-- info: 'STACS2027.PolyHyp.pkey_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.pkey_mem

/-- info: 'STACS2027.PolyHyp.one_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.one_mem

/-- info: 'STACS2027.PolyHyp.last_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.last_mem

/-- info: 'STACS2027.PolyHyp.nbrKeys_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.nbrKeys_pos

/-- info: 'STACS2027.PolyHyp.first_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.first_eq

/-- info: 'STACS2027.PolyHyp.last_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.last_eq

/-- info: 'STACS2027.PolyHyp.rprev_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.rprev_one

/-- info: 'STACS2027.PolyHyp.rnext_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.rnext_last

/-- info: 'STACS2027.PolyHyp.rprev_nonwrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.rprev_nonwrap

/-- info: 'STACS2027.PolyHyp.polyRot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.polyRot

/-- info: 'STACS2027.PolyHyp.polyRot_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.polyRot_rot

/-- info: 'STACS2027.PolyHyp.polyRot_rotInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.polyRot_rotInv

/-- info: 'STACS2027.PolyHyp.polyMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.polyMap

/-- info: 'STACS2027.PolyHyp.polySucc_adjs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.polySucc_adjs

/-- info: 'STACS2027.PolyHyp.polySucc_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.polySucc_lt

/-- info: 'STACS2027.PolyHyp.polyPred_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.polyPred_lt

/-- info: 'STACS2027.PolyHyp.polySucc_polyPred' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.polySucc_polyPred

/-- info: 'STACS2027.PolyHyp.outerDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.outerDart

/-- info: 'STACS2027.PolyHyp.dtail_outerDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.dtail_outerDart

/-- info: 'STACS2027.PolyHyp.dhead_outerDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.dhead_outerDart

/-- info: 'STACS2027.PolyHyp.face_outerDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.face_outerDart

/-- info: 'STACS2027.PolyHyp.iterate_face_outerDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.iterate_face_outerDart

/-- info: 'STACS2027.PolyHyp.outerDart_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.outerDart_reach

/-- info: 'STACS2027.PolyHyp.outerFaceCond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PolyHyp.outerFaceCond

/-- info: 'STACS2027.dtail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.dtail

/-- info: 'STACS2027.dhead' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.dhead

/-- info: 'STACS2027.dtail_even' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.dtail_even

/-- info: 'STACS2027.dtail_odd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.dtail_odd

/-- info: 'STACS2027.dhead_even' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.dhead_even

/-- info: 'STACS2027.dhead_odd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.dhead_odd

/-- info: 'STACS2027.halfEdgeEnd_eq_dtail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.halfEdgeEnd_eq_dtail

/-- info: 'STACS2027.ed_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.ed_lt

/-- info: 'STACS2027.ed_even' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.ed_even

/-- info: 'STACS2027.ed_odd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.ed_odd

/-- info: 'STACS2027.dtail_ed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.dtail_ed

/-- info: 'STACS2027.dhead_ed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.dhead_ed

/-- info: 'STACS2027.SimpleList' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.SimpleList

/-- info: 'STACS2027.dart_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.dart_inj

/-- info: 'STACS2027.Adjs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Adjs

/-- info: 'STACS2027.adjs_dart' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.adjs_dart

/-- info: 'STACS2027.Adjs.symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Adjs.symm

/-- info: 'STACS2027.adjs_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.adjs_iff

/-- info: 'STACS2027.findDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.findDart

/-- info: 'STACS2027.findDart_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.findDart_spec

/-- info: 'STACS2027.findDart_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.findDart_self

/-- info: 'STACS2027.fin_dart_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fin_dart_inj

/-- info: 'STACS2027.RotSystem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RotSystem

/-- info: 'STACS2027.RotSystem.nodeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.nodeN

/-- info: 'STACS2027.RotSystem.faceN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.faceN

/-- info: 'STACS2027.RotSystem.nodeN_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.nodeN_spec

/-- info: 'STACS2027.RotSystem.faceN_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.faceN_spec

/-- info: 'STACS2027.RotSystem.hypermap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.hypermap

/-- info: 'STACS2027.RotSystem.edge_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.edge_eq

/-- info: 'STACS2027.RotSystem.dtail_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.dtail_node

/-- info: 'STACS2027.RotSystem.dhead_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.dhead_node

/-- info: 'STACS2027.RotSystem.dtail_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.dtail_face

/-- info: 'STACS2027.RotSystem.dhead_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.dhead_face

/-- info: 'STACS2027.RotSystem.dtail_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.dtail_edge

/-- info: 'STACS2027.RotSystem.dhead_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.dhead_edge

/-- info: 'STACS2027.RotSystem.iterate_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.iterate_node

/-- info: 'STACS2027.RotSystem.nodeCond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.nodeCond

/-- info: 'STACS2027.RotSystem.nodes_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.nodes_ge

/-- info: 'STACS2027.RotSystem.sphOuter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RotSystem.sphOuter

/-- info: 'STACS2027.SphOuter' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.SphOuter

/-- info: 'STACS2027.SphOuter.outerplanarEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SphOuter.outerplanarEmbedding

/-- info: 'STACS2027.SphOuter.of_graphDartEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SphOuter.of_graphDartEquiv

/-- info: 'STACS2027.SphOuter.perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SphOuter.perm

/-- info: 'STACS2027.SphOuter.map_injOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SphOuter.map_injOn

/-- info: 'STACS2027.emptyHypermap' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.emptyHypermap

/-- info: 'STACS2027.sphOuter_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sphOuter_nil

/-- info: 'STACS2027.sumLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sumLabel

/-- info: 'STACS2027.sumLabel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sumLabel_step

/-- info: 'STACS2027.sumLabel_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sumLabel_path

/-- info: 'STACS2027.disjointSum_linked_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_linked_left

/-- info: 'STACS2027.disjointSum_linked_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_linked_right

/-- info: 'STACS2027.disjointSum_left_ne_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_left_ne_right

/-- info: 'STACS2027.disjointSum_iterate_face_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_iterate_face_left

/-- info: 'STACS2027.disjointSum_iterate_face_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_iterate_face_right

/-- info: 'STACS2027.disjointSum_iterate_node_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_iterate_node_left

/-- info: 'STACS2027.disjointSum_iterate_node_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.disjointSum_iterate_node_right

/-- info: 'STACS2027.OuterFaceCond.disjointSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterFaceCond.disjointSum

/-- info: 'STACS2027.SphOuter.append_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.SphOuter.append_disjoint

/-- info: 'STACS2027.simpleEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.simpleEdges

/-- info: 'STACS2027.OuterplanarEmbedding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding

/-- info: 'STACS2027.OuterplanarDrawing' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarDrawing

/-- info: 'STACS2027.HypermapEuler' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.HypermapEuler

/-- info: 'STACS2027.OuterplanarEmbedding.planarGraph' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.planarGraph

/-- info: 'STACS2027.HypEuler.exists_list_of_forall_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.HypEuler.exists_list_of_forall_mem

/-- info: 'STACS2027.not_outerplanarEmbedding_of_girth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.not_outerplanarEmbedding_of_girth

/-- info: 'STACS2027.simpleEdges_k4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.simpleEdges_k4

/-- info: 'STACS2027.simpleEdges_k23' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.simpleEdges_k23

/-- info: 'STACS2027.not_outerplanarDrawing_k4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.not_outerplanarDrawing_k4

/-- info: 'STACS2027.not_outerplanarDrawing_k23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.not_outerplanarDrawing_k23

/-- info: 'STACS2027.OuterplanarMinor.nodup_eraseDups'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.nodup_eraseDups'

/-- info: 'STACS2027.OuterplanarMinor.simpleEdges_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.simpleEdges_nodup

/-- info: 'STACS2027.OuterplanarMinor.exists_of_mem_simpleEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.exists_of_mem_simpleEdges

/-- info: 'STACS2027.OuterplanarMinor.edge_mem_simpleEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.edge_mem_simpleEdges

/-- info: 'STACS2027.OuterplanarMinor.LAdj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.LAdj

/-- info: 'STACS2027.OuterplanarMinor.BStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.BStep

/-- info: 'STACS2027.OuterplanarMinor.ListMinor' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.ListMinor

/-- info: 'STACS2027.OuterplanarMinor.weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.weight

/-- info: 'STACS2027.OuterplanarMinor.renameTo_self' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.renameTo_self

/-- info: 'STACS2027.OuterplanarMinor.renameTo_target' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.renameTo_target

/-- info: 'STACS2027.OuterplanarMinor.renameTo_of_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.renameTo_of_ne

/-- info: 'STACS2027.OuterplanarMinor.listMinor_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.listMinor_contract

/-- info: 'STACS2027.OuterplanarMinor.weight_contract_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.weight_contract_lt

/-- info: 'STACS2027.OuterplanarMinor.outerplanar_of_listMinor_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.outerplanar_of_listMinor_const

/-- info: 'STACS2027.OuterplanarMinor.outerplanar_of_listMinor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.outerplanar_of_listMinor

/-- info: 'STACS2027.OuterplanarMinor.reflTransGen_of_walk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.reflTransGen_of_walk

/-- info: 'STACS2027.OuterplanarDrawing.of_hasMinor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarDrawing.of_hasMinor

/-- info: 'STACS2027.OuterplanarDrawing.not_hasMinor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarDrawing.not_hasMinor

/-- info: 'STACS2027.OuterplanarDrawing.outerplanar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarDrawing.outerplanar

/-- info: 'STACS2027.OuterplanarMinor.node_face_a' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.node_face_a

/-- info: 'STACS2027.OuterplanarMinor.node_face_b' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.node_face_b

/-- info: 'STACS2027.OuterplanarMinor.face_b_ne_face_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.face_b_ne_face_a

/-- info: 'STACS2027.OuterplanarMinor.contract_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_sep

/-- info: 'STACS2027.OuterplanarMinor.contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract

/-- info: 'STACS2027.OuterplanarMinor.contract_node_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_node_inj

/-- info: 'STACS2027.OuterplanarMinor.contract_node_face_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_node_face_b

/-- info: 'STACS2027.OuterplanarMinor.contract_node_face_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_node_face_a

/-- info: 'STACS2027.OuterplanarMinor.contract_node_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_node_reaches

/-- info: 'STACS2027.OuterplanarMinor.contract_node_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_node_ab

/-- info: 'STACS2027.OuterplanarMinor.contract_node_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_node_invariant

/-- info: 'STACS2027.OuterplanarMinor.contract_step_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_step_lift

/-- info: 'STACS2027.OuterplanarMinor.contract_step_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_step_of

/-- info: 'STACS2027.OuterplanarMinor.contract_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_planar

/-- info: 'STACS2027.OuterplanarMinor.outerFaces_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.outerFaces_contract

/-- info: 'STACS2027.OuterplanarMinor.contract_last_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_last_fixed

/-- info: 'STACS2027.OuterplanarMinor.contract_shrink_last_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_shrink_last_fixed

/-- info: 'STACS2027.OuterplanarMinor.contractThenShrink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contractThenShrink

/-- info: 'STACS2027.OuterplanarMinor.contractThenShrink_edge_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contractThenShrink_edge_lift

/-- info: 'STACS2027.OuterplanarMinor.contractThenShrink_node_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contractThenShrink_node_orbit

/-- info: 'STACS2027.OuterplanarMinor.contractThenShrink_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contractThenShrink_planar

/-- info: 'STACS2027.OuterplanarMinor.outerFaces_contractThenShrink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.outerFaces_contractThenShrink

/-- info: 'STACS2027.OuterplanarMinor.renameTo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.renameTo

/-- info: 'STACS2027.OuterplanarMinor.contract_node_of_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.contract_node_of_label

/-- info: 'STACS2027.OuterplanarMinor.halfEdgeEnd_last_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.halfEdgeEnd_last_pair

/-- info: 'STACS2027.OuterplanarEmbedding.contractLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.contractLast

/-- info: 'STACS2027.OuterplanarMinor.OuterFaces' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.OuterFaces

/-- info: 'STACS2027.OuterplanarMinor.outerFaces_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.outerFaces_iff

/-- info: 'STACS2027.OuterplanarMinor.iterate_fixed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.iterate_fixed

/-- info: 'STACS2027.OuterplanarMinor.reaches_of_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.reaches_of_ne

/-- info: 'STACS2027.OuterplanarMinor.linkedPath_of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.linkedPath_of_steps

/-- info: 'STACS2027.OuterplanarMinor.componentCount_le_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.componentCount_le_of_steps

/-- info: 'STACS2027.OuterplanarMinor.transpose_reaches_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.transpose_reaches_three

/-- info: 'STACS2027.OuterplanarMinor.outerFaces_shrinkLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.outerFaces_shrinkLast

/-- info: 'STACS2027.OuterplanarMinor.cut_step_off' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.cut_step_off

/-- info: 'STACS2027.OuterplanarMinor.cut_step_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.cut_step_lift

/-- info: 'STACS2027.OuterplanarMinor.cut_path_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.cut_path_lift

/-- info: 'STACS2027.OuterplanarMinor.cut_linked_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.cut_linked_three

/-- info: 'STACS2027.OuterplanarMinor.cut_linked_of_linked_a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.cut_linked_of_linked_a

/-- info: 'STACS2027.OuterplanarMinor.cut_step_of_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.cut_step_of_linked

/-- info: 'STACS2027.OuterplanarMinor.cut_not_linked_of_same_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.cut_not_linked_of_same_face

/-- info: 'STACS2027.OuterplanarMinor.cut_face_iterate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.cut_face_iterate

/-- info: 'STACS2027.OuterplanarMinor.outerFaces_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.outerFaces_cut

/-- info: 'STACS2027.OuterplanarMinor.outerFaces_cutThenShrink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarMinor.outerFaces_cutThenShrink

/-- info: 'STACS2027.OuterplanarEmbedding.dropLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.dropLast

/-- info: 'STACS2027.OuterplanarEmbedding.sublist_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.sublist_prefix

/-- info: 'STACS2027.OuterplanarEmbedding.sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.sublist

/-- info: 'STACS2027.OuterplanarEmbedding.subperm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.subperm

/-- info: 'STACS2027.flipGraphDartEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.flipGraphDartEquiv

/-- info: 'STACS2027.OuterplanarEmbedding.flipEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.flipEdges

/-- info: 'STACS2027.OuterplanarEmbedding.canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.canonical

/-- info: 'STACS2027.OuterplanarEmbedding.contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarEmbedding.contract

/-- info: 'STACS2027.CycAdj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.CycAdj

/-- info: 'STACS2027.NoCross' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.NoCross

/-- info: 'STACS2027.OHam' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OHam

/-- info: 'STACS2027.getD_snoc_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.getD_snoc_of_lt

/-- info: 'STACS2027.getD_snoc_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.getD_snoc_length

/-- info: 'STACS2027.getD_mem_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.getD_mem_of_lt

/-- info: 'STACS2027.getD_ne_of_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.getD_ne_of_ne

/-- info: 'STACS2027.CycAdj.rotate_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.CycAdj.rotate_one

/-- info: 'STACS2027.CycAdj.rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.CycAdj.rotate

/-- info: 'STACS2027.CycAdj.isRotated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.CycAdj.isRotated

/-- info: 'STACS2027.NoCross.rotate_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.NoCross.rotate_one

/-- info: 'STACS2027.NoCross.rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.NoCross.rotate

/-- info: 'STACS2027.NoCross.isRotated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.NoCross.isRotated

/-- info: 'STACS2027.CycAdj.reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.CycAdj.reverse

/-- info: 'STACS2027.NoCross.reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.NoCross.reverse

/-- info: 'STACS2027.OHam.isRotated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OHam.isRotated

/-- info: 'STACS2027.OHam.reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OHam.reverse

/-- info: 'STACS2027.OHam.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OHam.congr

/-- info: 'STACS2027.OHam.rotate_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OHam.rotate_to

/-- info: 'STACS2027.OHam.ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OHam.ends

/-- info: 'STACS2027.OHam.drop_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OHam.drop_head

/-- info: 'STACS2027.OuterplanarHam.oham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.oham

/-- info: 'STACS2027.OHam.isCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OHam.isCycle

/-- info: 'STACS2027.OHam.outerplanarHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OHam.outerplanarHam

/-- info: 'STACS2027.OuterplanarHam.isRotated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.isRotated

/-- info: 'STACS2027.OuterplanarHam.rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.rotate

/-- info: 'STACS2027.OuterplanarHam.reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.reverse

/-- info: 'STACS2027.Palm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm

/-- info: 'STACS2027.Palm.Anc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.Anc

/-- info: 'STACS2027.Palm.anc_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.anc_refl

/-- info: 'STACS2027.Palm.anc_par' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.anc_par

/-- info: 'STACS2027.Palm.anc_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.anc_trans

/-- info: 'STACS2027.Palm.anc_of_anc_par' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.anc_of_anc_par

/-- info: 'STACS2027.Palm.anc_par_of_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.anc_par_of_ne

/-- info: 'STACS2027.Palm.isVertex_par' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Palm.isVertex_par

/-- info: 'STACS2027.Palm.isVertex_iterate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Palm.isVertex_iterate

/-- info: 'STACS2027.Palm.isVertex_anc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Palm.isVertex_anc

/-- info: 'STACS2027.Palm.pre_anc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.pre_anc

/-- info: 'STACS2027.Palm.anc_antisymm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.anc_antisymm

/-- info: 'STACS2027.Palm.anc_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.anc_chain

/-- info: 'STACS2027.Palm.anc_root' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.anc_root

/-- info: 'STACS2027.Palm.par_ne_of_anc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.par_ne_of_anc

/-- info: 'STACS2027.Palm.IsHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.IsHead

/-- info: 'STACS2027.Palm.isHead_of_root_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.isHead_of_root_child

/-- info: 'STACS2027.Palm.headAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.headAux

/-- info: 'STACS2027.Palm.head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.head

/-- info: 'STACS2027.Palm.NoHeadBetween' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.NoHeadBetween

/-- info: 'STACS2027.Palm.headAux_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.headAux_spec

/-- info: 'STACS2027.Palm.head_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.head_spec

/-- info: 'STACS2027.Palm.par_ne_of_head_anc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Palm.par_ne_of_head_anc

/-- info: 'STACS2027.Palm.anc_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.anc_head

/-- info: 'STACS2027.Palm.head_eq_of_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.head_eq_of_between

/-- info: 'STACS2027.mem_mapGraph_k4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.mem_mapGraph_k4

/-- info: 'STACS2027.IsK4Graph.relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsK4Graph.relabel

/-- info: 'STACS2027.IsK4Graph.hasAssignment_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsK4Graph.hasAssignment_iff

/-- info: 'STACS2027.perfect_of_outerplanarHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.perfect_of_outerplanarHam

/-- info: 'STACS2027.hasAssignment_of_no_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_of_no_cycle

/-- info: 'STACS2027.Palm.heads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.heads

/-- info: 'STACS2027.Palm.heads_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.heads_nodup

/-- info: 'STACS2027.Palm.mem_heads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.mem_heads

/-- info: 'STACS2027.Palm.blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.blocks

/-- info: 'STACS2027.Palm.mem_block_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.mem_block_iff

/-- info: 'STACS2027.Palm.blocks_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.blocks_flatten

/-- info: 'STACS2027.Palm.blocks_edgeDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.blocks_edgeDisjoint

/-- info: 'STACS2027.Palm.blocks_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.blocks_cycles

/-- info: 'STACS2027.Palm.block_k23MinorFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.block_k23MinorFree

/-- info: 'STACS2027.Palm.block_loopfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.block_loopfree

/-- info: 'STACS2027.Palm.block_no_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Palm.block_no_cycle

/-- info: 'STACS2027.k23_perfect_of_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k23_perfect_of_structure

/-- info: 'STACS2027.k23_perfect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.k23_perfect

/-- info: 'STACS2027.PlanarTriangleGeometry.completeFive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.completeFive

/-- info: 'STACS2027.PlanarTriangleGeometry.bipartiteThree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.bipartiteThree

/-- info: 'STACS2027.PlanarTriangleGeometry.simpleEdges_completeFive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.simpleEdges_completeFive

/-- info: 'STACS2027.PlanarTriangleGeometry.simpleEdges_bipartiteThree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.simpleEdges_bipartiteThree

/-- info: 'STACS2027.PlanarTriangleGeometry.completeFive_not_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.completeFive_not_planar

/-- info: 'STACS2027.PlanarTriangleGeometry.bipartiteThree_not_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.bipartiteThree_not_planar

/-- info: 'STACS2027.PlanarTriangleGeometry.finset_card_le_two_of_repetitions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.finset_card_le_two_of_repetitions

/-- info: 'STACS2027.PlanarTriangleGeometry.planar_light_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.planar_light_edge

/-- info: 'Complexity.PlanarGraph.perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.perm

/-- info: 'Complexity.PlanarGraph.dropLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.dropLast

/-- info: 'Complexity.PlanarGraph.sublist_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.sublist_prefix

/-- info: 'Complexity.PlanarGraph.sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.sublist

/-- info: 'Complexity.PlanarGraph.subperm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.subperm

/-- info: 'Complexity.PlanarGraph.canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.canonical

/-- info: 'Complexity.PlanarGraph.map_injOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.map_injOn

/-- info: 'Complexity.PlanarGraph.contractLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.contractLast

/-- info: 'Complexity.PlanarGraph.contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.contract

/-- info: 'Complexity.PlanarGraph.simpleEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.simpleEdges

/-- info: 'STACS2027.PlanarMinor.planar_of_listMinor_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarMinor.planar_of_listMinor_const

/-- info: 'STACS2027.PlanarMinor.planar_of_listMinor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarMinor.planar_of_listMinor

/-- info: 'Complexity.PlanarGraph.of_hasMinor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.PlanarGraph.of_hasMinor

/-- info: 'STACS2027.PlanarTriangleGeometry.hasMinor_target_subset' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.hasMinor_target_subset

/-- info: 'STACS2027.PlanarTriangleGeometry.clique_vertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.clique_vertex

/-- info: 'STACS2027.PlanarTriangleGeometry.biclique_vertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.biclique_vertex

/-- info: 'STACS2027.PlanarTriangleGeometry.planar_neighbours_outerplanar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.PlanarTriangleGeometry.planar_neighbours_outerplanar

/-- info: 'STACS2027.TriangleMatching.planar_vertexFamily_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.planar_vertexFamily_card

/-- info: 'STACS2027.TriangleMatching.planar_triangle_hall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.planar_triangle_hall

/-- info: 'STACS2027.TriangleMatching.planar_triangle_perfect_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.planar_triangle_perfect_assignment

/-- info: 'STACS2027.IsPolygon' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon

/-- info: 'STACS2027.Adj.symm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Adj.symm

/-- info: 'STACS2027.adj_iff_edge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.adj_iff_edge

/-- info: 'STACS2027.mem_pathEdges_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_pathEdges_iff

/-- info: 'STACS2027.edge_mem_pathEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_mem_pathEdges

/-- info: 'STACS2027.IsCycle.rotate_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsCycle.rotate_edge

/-- info: 'STACS2027.IsPolygon.three_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.three_le

/-- info: 'STACS2027.IsPolygon.lt_of_adj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.lt_of_adj

/-- info: 'STACS2027.IsPolygon.getD_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.getD_range

/-- info: 'STACS2027.IsPolygon.noncross' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.noncross
