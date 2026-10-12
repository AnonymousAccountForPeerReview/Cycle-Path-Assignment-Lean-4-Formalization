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

/-- info: 'STACS2027.IsPolygon.range_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.range_split

/-- info: 'STACS2027.IsPolygon.adj_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.adj_succ

/-- info: 'STACS2027.IsPolygon.adj_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.adj_wrap

/-- info: 'STACS2027.RAM.Block.wlab_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.wlab_run

/-- info: 'STACS2027.RAM.Block.wlabs_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.wlabs_run

/-- info: 'STACS2027.RAM.Block.wlabs_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.wlabs_addrOK

/-- info: 'STACS2027.RAM.Block.length_k4Base_flatten' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.length_k4Base_flatten

/-- info: 'STACS2027.RAM.Block.k4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.k4_spec

/-- info: 'STACS2027.RAM.Block.polyBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.polyBound

/-- info: 'STACS2027.RAM.Block.dispatch_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.dispatch_spec

/-- info: 'STACS2027.RAM.Block.CB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.CB

/-- info: 'STACS2027.RAM.Block.polyMem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.polyMem_le

/-- info: 'STACS2027.RAM.Block.blockProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.blockProg_spec

/-- info: 'STACS2027.RAM.Block.map_take_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.map_take_succ

/-- info: 'STACS2027.RAM.Block.take_succ_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.take_succ_eq

/-- info: 'STACS2027.RAM.Block.blockVerts_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.blockVerts_take_succ

/-- info: 'STACS2027.RAM.Block.length_blockVerts_take_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.length_blockVerts_take_le

/-- info: 'STACS2027.RAM.Block.length_blockVerts_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.length_blockVerts_le

/-- info: 'STACS2027.RAM.Block.mem_blockVerts_of_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.mem_blockVerts_of_take

/-- info: 'STACS2027.RAM.Block.lt_of_mem_blockVerts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.lt_of_mem_blockVerts

/-- info: 'STACS2027.RAM.Block.dictOf_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.dictOf_of_mem

/-- info: 'STACS2027.RAM.Block.localEdges_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.localEdges_bounds

/-- info: 'STACS2027.RAM.Block.localEdges_nodup'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.localEdges_nodup'

/-- info: 'STACS2027.RAM.Block.length_localEdges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.length_localEdges

/-- info: 'STACS2027.RAM.Block.getElem_localEdges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.getElem_localEdges

/-- info: 'STACS2027.RAM.Block.out_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.out_small

/-- info: 'STACS2027.RAM.Block.out_k4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.out_k4

/-- info: 'STACS2027.RAM.Block.out_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.out_poly

/-- info: 'STACS2027.RAM.Block.k4Base_lt' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.k4Base_lt

/-- info: 'STACS2027.RAM.Block.length_walk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.length_walk

/-- info: 'STACS2027.RAM.Block.length_earHam' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.length_earHam

/-- info: 'STACS2027.RAM.Block.ham_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.ham_pos

/-- info: 'STACS2027.RAM.Block.HamFacts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.HamFacts

/-- info: 'STACS2027.RAM.Block.hamFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.hamFacts

/-- info: 'STACS2027.RAM.Block.HamFacts.ends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.HamFacts.ends

/-- info: 'STACS2027.RAM.Block.pg_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.pg_lt

/-- info: 'STACS2027.RAM.Block.pg_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.pg_nodup

/-- info: 'STACS2027.RAM.Block.HamFacts.idxOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.HamFacts.idxOf_lt

/-- info: 'STACS2027.RAM.Block.HamFacts.outerplanarHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.HamFacts.outerplanarHam

/-- info: 'STACS2027.RAM.Block.polyOut_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.polyOut_lt

/-- info: 'STACS2027.RAM.Block.map_omap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.map_omap

/-- info: 'STACS2027.RAM.Block.omapOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.omapOf

/-- info: 'STACS2027.RAM.Block.out_poly_omap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.out_poly_omap

/-- info: 'STACS2027.RAM.Block.hamOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.hamOf

/-- info: 'STACS2027.RAM.Block.pgOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.pgOf

/-- info: 'STACS2027.RAM.Block.DRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.DRep

/-- info: 'STACS2027.RAM.Block.BPost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.BPost

/-- info: 'STACS2027.RAM.Block.polyMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.polyMem

/-- info: 'STACS2027.RAM.Block.length_locG' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.length_locG

/-- info: 'STACS2027.RAM.Block.length_pgOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.length_pgOf

/-- info: 'STACS2027.RAM.Block.ERep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.ERep

/-- info: 'STACS2027.RAM.Block.not_mem_ear' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.not_mem_ear

/-- info: 'STACS2027.RAM.Block.ear_footprint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.ear_footprint

/-- info: 'STACS2027.RAM.Block.ear_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.ear_step

/-- info: 'STACS2027.RAM.Block.PMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.PMem

/-- info: 'STACS2027.RAM.Block.PMem.below_upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.PMem.below_upd

/-- info: 'STACS2027.RAM.Block.PMem.upd_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.PMem.upd_pos

/-- info: 'STACS2027.RAM.Block.PMem.upd_pu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.PMem.upd_pu

/-- info: 'STACS2027.RAM.Block.PMem.upd_pv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.PMem.upd_pv

/-- info: 'STACS2027.RAM.Block.PMem.upd_om' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.PMem.upd_om

/-- info: 'STACS2027.RAM.Block.PRep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.PRep

/-- info: 'STACS2027.RAM.Block.PRep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.PRep.indep

/-- info: 'STACS2027.RAM.Block.PRep.run_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.PRep.run_of

/-- info: 'STACS2027.RAM.Block.pInit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.pInit_spec

/-- info: 'STACS2027.RAM.Block.posF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.posF

/-- info: 'STACS2027.RAM.Block.posF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.posF_zero

/-- info: 'STACS2027.RAM.Block.posF_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.posF_succ

/-- info: 'STACS2027.RAM.Block.posF_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.posF_full

/-- info: 'STACS2027.RAM.Block.posBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.posBody_spec

/-- info: 'STACS2027.RAM.Block.posLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.posLoop_spec

/-- info: 'STACS2027.RAM.Block.pgBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.pgBody_spec

/-- info: 'STACS2027.RAM.Block.pgLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.pgLoop_spec

/-- info: 'STACS2027.RAM.Block.getElem_omapOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.getElem_omapOf

/-- info: 'STACS2027.RAM.Block.length_omapOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.length_omapOf

/-- info: 'STACS2027.RAM.Block.omBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.omBody_spec

/-- info: 'STACS2027.RAM.Block.omLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.omLoop_spec

/-- info: 'STACS2027.RAM.Block.poly_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.poly_step

/-- info: 'STACS2027.RAM.Block.polyBranch_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.polyBranch_spec

/-- info: 'STACS2027.RAM.Block.Glob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.Glob

/-- info: 'STACS2027.RAM.Block.Glob.of_regs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.Glob.of_regs

/-- info: 'STACS2027.RAM.Block.not_mem_of_footprint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.not_mem_of_footprint

/-- info: 'STACS2027.RAM.Block.Glob.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.Glob.frame

/-- info: 'STACS2027.RAM.Block.Glob.run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.Glob.run

/-- info: 'STACS2027.RAM.Block.W' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.W

/-- info: 'STACS2027.RAM.Block.footprint_of_W' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.footprint_of_W

/-- info: 'STACS2027.RAM.Block.Lay' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.Lay

/-- info: 'STACS2027.RAM.Block.BMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.BMem

/-- info: 'STACS2027.RAM.Block.BMem.upd_cu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.BMem.upd_cu

/-- info: 'STACS2027.RAM.Block.BMem.upd_cv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.BMem.upd_cv

/-- info: 'STACS2027.RAM.Block.BMem.upd_vs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.BMem.upd_vs

/-- info: 'STACS2027.RAM.Block.BMem.upd_lu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.BMem.upd_lu

/-- info: 'STACS2027.RAM.Block.BMem.upd_lv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.BMem.upd_lv

/-- info: 'STACS2027.RAM.Block.BMem.upd_loc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.BMem.upd_loc

/-- info: 'STACS2027.RAM.Block.BMem.sameOn_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.BMem.sameOn_zero

/-- info: 'STACS2027.RAM.Block.Rep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.Rep

/-- info: 'STACS2027.RAM.Block.Rep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.Rep.indep

/-- info: 'STACS2027.RAM.Block.Rep.run_of'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.Rep.run_of'

/-- info: 'STACS2027.RAM.Block.Rep.run_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.Rep.run_of

/-- info: 'STACS2027.RAM.Block.Glob.init' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.Glob.init

/-- info: 'STACS2027.RAM.Block.initB_footprint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.initB_footprint

/-- info: 'STACS2027.RAM.Block.initB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.initB_spec

/-- info: 'STACS2027.RAM.Block.edge_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.edge_read

/-- info: 'STACS2027.RAM.Block.copyBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.copyBody_spec

/-- info: 'STACS2027.RAM.Block.copy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.copy_spec

/-- info: 'STACS2027.RAM.Block.loopFree_visit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.loopFree_visit

/-- info: 'STACS2027.RAM.Block.wregs_visit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.wregs_visit

/-- info: 'STACS2027.RAM.Block.visit_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.visit_wregs

/-- info: 'STACS2027.RAM.Block.visit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.visit_run

/-- info: 'STACS2027.RAM.Block.visit_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.visit_addrOK

/-- info: 'STACS2027.RAM.Block.collBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.collBody_spec

/-- info: 'STACS2027.RAM.Block.collect_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.collect_spec

/-- info: 'STACS2027.RAM.Block.order_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.order_run

/-- info: 'STACS2027.RAM.Block.locG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.locG

/-- info: 'STACS2027.RAM.Block.locBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.locBody_spec

/-- info: 'STACS2027.RAM.Block.localE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.localE_spec

/-- info: 'STACS2027.RAM.Block.resF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.resF

/-- info: 'STACS2027.RAM.Block.resF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.resF_zero

/-- info: 'STACS2027.RAM.Block.resF_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.resF_length

/-- info: 'STACS2027.RAM.Block.resF_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.resF_succ

/-- info: 'STACS2027.RAM.Block.resBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.resBody_spec

/-- info: 'STACS2027.RAM.Block.reset_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.reset_spec

/-- info: 'STACS2027.RAM.Block.gPOS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.gPOS

/-- info: 'STACS2027.RAM.Block.gCU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.gCU

/-- info: 'STACS2027.RAM.Block.gCV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.gCV

/-- info: 'STACS2027.RAM.Block.rI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.rI

/-- info: 'STACS2027.RAM.Block.rA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.rA

/-- info: 'STACS2027.RAM.Block.rB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.rB

/-- info: 'STACS2027.RAM.Block.rU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.rU

/-- info: 'STACS2027.RAM.Block.rV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.rV

/-- info: 'STACS2027.RAM.Block.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.rX

/-- info: 'STACS2027.RAM.Block.rY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.rY

/-- info: 'STACS2027.RAM.Block.rC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.rC

/-- info: 'STACS2027.RAM.Block.rP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.rP

/-- info: 'STACS2027.RAM.Block.r2L' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.r2L

/-- info: 'STACS2027.RAM.Block.initB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.initB

/-- info: 'STACS2027.RAM.Block.copyBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.copyBody

/-- info: 'STACS2027.RAM.Block.copy' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.copy

/-- info: 'STACS2027.RAM.Block.visit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.visit

/-- info: 'STACS2027.RAM.Block.collBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.collBody

/-- info: 'STACS2027.RAM.Block.collect' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.collect

/-- info: 'STACS2027.RAM.Block.order' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.order

/-- info: 'STACS2027.RAM.Block.locRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.locRead

/-- info: 'STACS2027.RAM.Block.locBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.locBody

/-- info: 'STACS2027.RAM.Block.localE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.localE

/-- info: 'STACS2027.RAM.Block.resBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.resBody

/-- info: 'STACS2027.RAM.Block.reset' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.reset

/-- info: 'STACS2027.RAM.Block.wlab' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.wlab

/-- info: 'STACS2027.RAM.Block.wlabs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.wlabs

/-- info: 'STACS2027.RAM.Block.k4Prog' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.k4Prog

/-- info: 'STACS2027.RAM.Block.pInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.pInit

/-- info: 'STACS2027.RAM.Block.posBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.posBody

/-- info: 'STACS2027.RAM.Block.posLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.posLoop

/-- info: 'STACS2027.RAM.Block.pgRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.pgRead

/-- info: 'STACS2027.RAM.Block.pgBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.pgBody

/-- info: 'STACS2027.RAM.Block.pgLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.pgLoop

/-- info: 'STACS2027.RAM.Block.omBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.omBody

/-- info: 'STACS2027.RAM.Block.omLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.omLoop

/-- info: 'STACS2027.RAM.Block.polyBranch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.polyBranch

/-- info: 'STACS2027.RAM.Block.smallTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.smallTest

/-- info: 'STACS2027.RAM.Block.k4Test' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.k4Test

/-- info: 'STACS2027.RAM.Block.dispatch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.dispatch

/-- info: 'STACS2027.RAM.Block.blockProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.blockProg

/-- info: 'STACS2027.RAM.Block.wregs_wlabs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.wregs_wlabs

/-- info: 'STACS2027.RAM.Block.stores_wlabs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.stores_wlabs

/-- info: 'STACS2027.RAM.Block.loopFree_wlabs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.loopFree_wlabs

/-- info: 'STACS2027.RAM.Block.size_wlabs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.size_wlabs

/-- info: 'STACS2027.RAM.Block.wregs_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.wregs_fixed

/-- info: 'STACS2027.RAM.Block.blockProg_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Block.blockProg_wregs

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

/-- info: 'STACS2027.RAM.EchoDemo.rI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EchoDemo.rI

/-- info: 'STACS2027.RAM.EchoDemo.rP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EchoDemo.rP

/-- info: 'STACS2027.RAM.EchoDemo.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EchoDemo.rX

/-- info: 'STACS2027.RAM.EchoDemo.rN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EchoDemo.rN

/-- info: 'STACS2027.RAM.EchoDemo.body' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EchoDemo.body

/-- info: 'STACS2027.RAM.EchoDemo.echo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EchoDemo.echo

/-- info: 'STACS2027.RAM.EchoDemo.Inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EchoDemo.Inv

/-- info: 'STACS2027.RAM.EchoDemo.body_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EchoDemo.body_spec

/-- info: 'STACS2027.RAM.EchoDemo.echo_computesIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EchoDemo.echo_computesIn

/-- info: 'STACS2027.RAM.ExecB.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.frame

/-- info: 'STACS2027.RAM.ExecB.reg_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.reg_frame

/-- info: 'STACS2027.RAM.ExecB.mem_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.mem_frame

/-- info: 'STACS2027.RAM.ExecB.out_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.out_frame

/-- info: 'STACS2027.RAM.RegIndep.execB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.execB

/-- info: 'STACS2027.RAM.AddrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK

/-- info: 'STACS2027.RAM.addrOK_skip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_skip

/-- info: 'STACS2027.RAM.addrOK_const' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_const

/-- info: 'STACS2027.RAM.addrOK_add' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_add

/-- info: 'STACS2027.RAM.addrOK_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_sub

/-- info: 'STACS2027.RAM.addrOK_write' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_write

/-- info: 'STACS2027.RAM.addrOK_load' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_load

/-- info: 'STACS2027.RAM.addrOK_store' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_store

/-- info: 'STACS2027.RAM.addrOK_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_seq

/-- info: 'STACS2027.RAM.addrOK_ifz' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_ifz

/-- info: 'STACS2027.RAM.addrOK_of_memFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_of_memFree

/-- info: 'STACS2027.RAM.AddrOK.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.mono

/-- info: 'STACS2027.RAM.AddrOK.seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.seq

/-- info: 'STACS2027.RAM.AddrOK.ifz' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.ifz

/-- info: 'STACS2027.RAM.AddrOK.of_memFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.of_memFree

/-- info: 'STACS2027.RAM.execB_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.execB_run

/-- info: 'STACS2027.RAM.ExecB.addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.addrOK

/-- info: 'STACS2027.RAM.HTBt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTBt

/-- info: 'STACS2027.RAM.HTB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB

/-- info: 'STACS2027.RAM.HTBt.toHTt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTBt.toHTt

/-- info: 'STACS2027.RAM.HTBt.of_HTt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTBt.of_HTt

/-- info: 'STACS2027.RAM.HTBt.mono_S' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTBt.mono_S

/-- info: 'STACS2027.RAM.HTB.toHT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.toHT

/-- info: 'STACS2027.RAM.HTB.of_HT' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.of_HT

/-- info: 'STACS2027.RAM.HTB.of_HT_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.of_HT_addrOK

/-- info: 'STACS2027.RAM.HTB.mono_S' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.mono_S

/-- info: 'STACS2027.RAM.HTB.computesIn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.computesIn

/-- info: 'STACS2027.RAM.HTB.computesIn_post' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.computesIn_post

/-- info: 'STACS2027.RAM.HTB.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.mono

/-- info: 'STACS2027.RAM.HTB.pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.pre

/-- info: 'STACS2027.RAM.HTB.post' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.post

/-- info: 'STACS2027.RAM.HTB.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.weaken

/-- info: 'STACS2027.RAM.HTB.seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.seq

/-- info: 'STACS2027.RAM.HTB.ifz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.ifz

/-- info: 'STACS2027.RAM.HTB.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.run

/-- info: 'STACS2027.RAM.HTB.loopPot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.loopPot

/-- info: 'STACS2027.RAM.HTB.loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.loop

/-- info: 'STACS2027.RAM.HTB.body_of_HT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.body_of_HT

/-- info: 'STACS2027.RAM.HTB.skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.skip

/-- info: 'STACS2027.RAM.HTB.run_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.run_le

/-- info: 'STACS2027.RAM.HTB.run_le'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.run_le'

/-- info: 'STACS2027.RAM.HTB.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.frame

/-- info: 'STACS2027.RAM.HTB.frameReg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.frameReg

/-- info: 'STACS2027.RAM.HTB.frameIndep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.frameIndep

/-- info: 'STACS2027.RAM.HTB.withFrame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.withFrame

/-- info: 'STACS2027.RAM.HTB.and' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.and

/-- info: 'STACS2027.RAM.HTB.and_HT' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.and_HT

/-- info: 'STACS2027.RAM.HTB.exists_pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.exists_pre

/-- info: 'STACS2027.RAM.HTB.prop_pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.prop_pre

/-- info: 'STACS2027.RAM.HTB.cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.cases

/-- info: 'STACS2027.RAM.HTB.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.casesOn

/-- info: 'STACS2027.RAM.HTB.of_forall' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.of_forall

/-- info: 'STACS2027.RAM.HTB.seq3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.seq3

/-- info: 'STACS2027.RAM.HTB.seq_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.seq_le

/-- info: 'STACS2027.RAM.HTB.loopT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.loopT

/-- info: 'STACS2027.RAM.HTB.of_false' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.of_false

/-- info: 'STACS2027.RAM.HTB.pre_fact' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.pre_fact

/-- info: 'STACS2027.RAM.HTB.assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.assoc

/-- info: 'STACS2027.RAM.HTB.reassoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.reassoc

/-- info: 'STACS2027.RAM.HTB.memRestore' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.memRestore

/-- info: 'STACS2027.RAM.memFree_mov' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_mov

/-- info: 'STACS2027.RAM.memFree_addc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_addc

/-- info: 'STACS2027.RAM.memFree_subc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_subc

/-- info: 'STACS2027.RAM.memFree_inc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_inc

/-- info: 'STACS2027.RAM.memFree_dec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_dec

/-- info: 'STACS2027.RAM.memFree_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_swap

/-- info: 'STACS2027.RAM.memFree_alloc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_alloc

/-- info: 'STACS2027.RAM.memFree_mul' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_mul

/-- info: 'STACS2027.RAM.memFree_ld' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_ld

/-- info: 'STACS2027.RAM.memFree_st' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_st

/-- info: 'STACS2027.RAM.memFree_ifLt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_ifLt

/-- info: 'STACS2027.RAM.memFree_ifLe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_ifLe

/-- info: 'STACS2027.RAM.memFree_ifEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_ifEq

/-- info: 'STACS2027.RAM.memFree_upLoop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_upLoop

/-- info: 'STACS2027.RAM.memFree_forUp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_forUp

/-- info: 'STACS2027.RAM.memFree_forRange' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_forRange

/-- info: 'STACS2027.RAM.memFree_whileC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_whileC

/-- info: 'STACS2027.RAM.addrOK_mov' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_mov

/-- info: 'STACS2027.RAM.addrOK_addc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_addc

/-- info: 'STACS2027.RAM.addrOK_subc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_subc

/-- info: 'STACS2027.RAM.addrOK_inc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_inc

/-- info: 'STACS2027.RAM.addrOK_dec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_dec

/-- info: 'STACS2027.RAM.addrOK_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_swap

/-- info: 'STACS2027.RAM.addrOK_alloc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_alloc

/-- info: 'STACS2027.RAM.addrOK_ld' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_ld

/-- info: 'STACS2027.RAM.addrOK_st' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_st

/-- info: 'STACS2027.RAM.addrOK_ifLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_ifLt

/-- info: 'STACS2027.RAM.addrOK_ifLe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_ifLe

/-- info: 'STACS2027.RAM.addrOK_ifEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_ifEq

/-- info: 'STACS2027.RAM.AddrOK.ifLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.ifLt

/-- info: 'STACS2027.RAM.AddrOK.ifLe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.ifLe

/-- info: 'STACS2027.RAM.AddrOK.ifEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.ifEq

/-- info: 'STACS2027.RAM.HTB.const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.const

/-- info: 'STACS2027.RAM.HTB.add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.add

/-- info: 'STACS2027.RAM.HTB.sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.sub

/-- info: 'STACS2027.RAM.HTB.load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.load

/-- info: 'STACS2027.RAM.HTB.store' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.store

/-- info: 'STACS2027.RAM.HTB.write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.write

/-- info: 'STACS2027.RAM.HTB.mov' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.mov

/-- info: 'STACS2027.RAM.HTB.addc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.addc

/-- info: 'STACS2027.RAM.HTB.subc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.subc

/-- info: 'STACS2027.RAM.HTB.ld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.ld

/-- info: 'STACS2027.RAM.HTB.st' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.st

/-- info: 'STACS2027.RAM.HTB.ifLt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.ifLt

/-- info: 'STACS2027.RAM.HTB.ifLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.ifLe

/-- info: 'STACS2027.RAM.HTB.ifEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.ifEq

/-- info: 'STACS2027.RAM.HTB.upLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.upLoop

/-- info: 'STACS2027.RAM.HTB.forUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.forUp

/-- info: 'STACS2027.RAM.HTB.forUpC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.forUpC

/-- info: 'STACS2027.RAM.HTB.forRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.forRange

/-- info: 'STACS2027.RAM.HTB.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.mul

/-- info: 'STACS2027.RAM.HTB.whileC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.whileC

/-- info: 'STACS2027.RAM.HTB.whileCPot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.whileCPot

/-- info: 'STACS2027.RAM.HTB.loopG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.loopG

/-- info: 'STACS2027.RAM.HTB.whileG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.whileG

/-- info: 'STACS2027.RAM.HTB.toG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.toG

/-- info: 'STACS2027.RAM.HTB.alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HTB.alloc

/-- info: 'STACS2027.RAM.EarR.prepend_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.prepend_mem

/-- info: 'STACS2027.RAM.EarR.prepend_np' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.prepend_np

/-- info: 'STACS2027.RAM.EarR.prepend_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.prepend_reg

/-- info: 'STACS2027.RAM.EarR.incDeg_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.incDeg_mem

/-- info: 'STACS2027.RAM.EarR.incDeg_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.incDeg_reg

/-- info: 'STACS2027.RAM.EarR.push_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.push_mem

/-- info: 'STACS2027.RAM.EarR.push_sp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.push_sp

/-- info: 'STACS2027.RAM.EarR.push_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.push_reg

/-- info: 'STACS2027.RAM.EarR.prepend_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.prepend_addrOK

/-- info: 'STACS2027.RAM.EarR.incDeg_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.incDeg_addrOK

/-- info: 'STACS2027.RAM.EarR.push_addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.push_addrOK

/-- info: 'STACS2027.RAM.EarR.decDegP_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.decDegP_addrOK

/-- info: 'STACS2027.RAM.EarR.prepend_emem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.prepend_emem

/-- info: 'STACS2027.RAM.EarR.incDeg_emem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.incDeg_emem

/-- info: 'STACS2027.RAM.EarR.push_emem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.push_emem

/-- info: 'STACS2027.RAM.EarR.decDegP_emem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.decDegP_emem

/-- info: 'STACS2027.RAM.EarR.LRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.LRep

/-- info: 'STACS2027.RAM.EarR.LRep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.LRep.indep

/-- info: 'STACS2027.RAM.EarR.OutAdj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.OutAdj

/-- info: 'STACS2027.RAM.EarR.OutOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.OutOK

/-- info: 'STACS2027.RAM.EarR.killLog_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.killLog_mem

/-- info: 'STACS2027.RAM.EarR.killLog_cnt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.killLog_cnt

/-- info: 'STACS2027.RAM.EarR.killLog_lc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.killLog_lc

/-- info: 'STACS2027.RAM.EarR.killLog_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.killLog_reg

/-- info: 'STACS2027.RAM.EarR.outChk_Z' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.outChk_Z

/-- info: 'STACS2027.RAM.EarR.outChk_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.outChk_mem

/-- info: 'STACS2027.RAM.EarR.outChk_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.outChk_reg

/-- info: 'STACS2027.RAM.EarR.elimBlk_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.elimBlk_run

/-- info: 'STACS2027.RAM.EarR.roundCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.roundCost

/-- info: 'STACS2027.RAM.EarR.roundCost_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.roundCost_cons

/-- info: 'STACS2027.RAM.EarR.round_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.round_spec

/-- info: 'STACS2027.RAM.EarR.WE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.WE

/-- info: 'STACS2027.RAM.EarR.Inp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.Inp

/-- info: 'STACS2027.RAM.EarR.Inp.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.Inp.regIndep

/-- info: 'STACS2027.RAM.EarR.eSt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.eSt

/-- info: 'STACS2027.RAM.EarR.init_eq_eSt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.init_eq_eSt

/-- info: 'STACS2027.RAM.EarR.EMem.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.congr

/-- info: 'STACS2027.RAM.EarR.AllocPost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.AllocPost

/-- info: 'STACS2027.RAM.EarR.allocs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.allocs_spec

/-- info: 'STACS2027.RAM.EarR.EdgeInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EdgeInv

/-- info: 'STACS2027.RAM.EarR.deg_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.deg_take_succ

/-- info: 'STACS2027.RAM.EarR.edgeBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.edgeBody_spec

/-- info: 'STACS2027.RAM.EarR.edges_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.edges_spec

/-- info: 'STACS2027.RAM.EarR.StkInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.StkInv

/-- info: 'STACS2027.RAM.EarR.stkBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.stkBody_spec

/-- info: 'STACS2027.RAM.EarR.stk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.stk_spec

/-- info: 'STACS2027.RAM.EarR.init0_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.init0_spec

/-- info: 'STACS2027.RAM.EarR.LL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.LL

/-- info: 'STACS2027.RAM.EarR.LL_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.LL_nil

/-- info: 'STACS2027.RAM.EarR.LL_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.LL_cons

/-- info: 'STACS2027.RAM.EarR.LL.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.LL.congr

/-- info: 'STACS2027.RAM.EarR.LL.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.LL.mono

/-- info: 'STACS2027.RAM.EarR.LL.eq_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.LL.eq_zero_iff

/-- info: 'STACS2027.RAM.EarR.LL.upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.LL.upd

/-- info: 'STACS2027.RAM.EarR.AdjRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.AdjRep

/-- info: 'STACS2027.RAM.EarR.AdjRep.upd_of_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.AdjRep.upd_of_disjoint

/-- info: 'STACS2027.RAM.EarR.AdjRep.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.AdjRep.mono

/-- info: 'STACS2027.RAM.EarR.AdjRep.prepend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.AdjRep.prepend

/-- info: 'STACS2027.RAM.EarR.HT.of_false' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.HT.of_false

/-- info: 'STACS2027.RAM.EarR.HT.loopG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.HT.loopG

/-- info: 'STACS2027.RAM.EarR.HT.whileG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.HT.whileG

/-- info: 'STACS2027.RAM.EarR.HT.toG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.HT.toG

/-- info: 'STACS2027.RAM.EarR.phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.phi

/-- info: 'STACS2027.RAM.EarR.phi_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.phi_round

/-- info: 'STACS2027.RAM.EarR.good_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.good_init

/-- info: 'STACS2027.RAM.EarR.phi_init_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.phi_init_le

/-- info: 'STACS2027.RAM.EarR.MInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.MInv

/-- info: 'STACS2027.RAM.EarR.mainLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.mainLoop_spec

/-- info: 'STACS2027.RAM.EarR.recon_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.recon_spec

/-- info: 'STACS2027.RAM.EarR.CE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.CE

/-- info: 'STACS2027.RAM.EarR.outOK_of_peel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.outOK_of_peel

/-- info: 'STACS2027.RAM.EarR.earProg_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.earProg_writes

/-- info: 'STACS2027.RAM.EarR.earProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.earProg_spec

/-- info: 'STACS2027.RAM.EarR.earProg_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.earProg_wregs

/-- info: 'STACS2027.RAM.EarR.PMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PMem

/-- info: 'STACS2027.RAM.EarR.PRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PRep

/-- info: 'STACS2027.RAM.EarR.PRep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PRep.indep

/-- info: 'STACS2027.RAM.EarR.PRep.lrep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PRep.lrep

/-- info: 'STACS2027.RAM.EarR.WP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.WP

/-- info: 'STACS2027.RAM.EarR.PRep.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PRep.step

/-- info: 'STACS2027.RAM.EarR.reg_of_WP' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.reg_of_WP

/-- info: 'STACS2027.RAM.EarR.PMem.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PMem.congr

/-- info: 'STACS2027.RAM.EarR.PMem.setPD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PMem.setPD

/-- info: 'STACS2027.RAM.EarR.PMem.setRM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PMem.setRM

/-- info: 'STACS2027.RAM.EarR.PMem.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PMem.push

/-- info: 'STACS2027.RAM.EarR.PMem.pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PMem.pop

/-- info: 'STACS2027.RAM.EarR.PMem.setO1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PMem.setO1

/-- info: 'STACS2027.RAM.EarR.PMem.setO2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PMem.setO2

/-- info: 'STACS2027.RAM.EarR.pPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pPre

/-- info: 'STACS2027.RAM.EarR.pPre_N' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pPre_N

/-- info: 'STACS2027.RAM.EarR.pstackPre_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pstackPre_succ

/-- info: 'STACS2027.RAM.EarR.length_pstackPre_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.length_pstackPre_le

/-- info: 'STACS2027.RAM.EarR.ppush_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.ppush_mem

/-- info: 'STACS2027.RAM.EarR.ppush_psp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.ppush_psp

/-- info: 'STACS2027.RAM.EarR.pInitBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pInitBody_spec

/-- info: 'STACS2027.RAM.EarR.pTop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pTop

/-- info: 'STACS2027.RAM.EarR.premove_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.premove_eq

/-- info: 'STACS2027.RAM.EarR.stack_take_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.stack_take_le

/-- info: 'STACS2027.RAM.EarR.pUpd_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pUpd_run

/-- info: 'STACS2027.RAM.EarR.getD_snoc_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.getD_snoc_d

/-- info: 'STACS2027.RAM.EarR.first_two_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.first_two_snoc

/-- info: 'STACS2027.RAM.EarR.PScanInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PScanInv

/-- info: 'STACS2027.RAM.EarR.pScanStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pScanStep

/-- info: 'STACS2027.RAM.EarR.pScan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pScan_spec

/-- info: 'STACS2027.RAM.EarR.pPop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pPop_spec

/-- info: 'STACS2027.RAM.EarR.pOut_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pOut_spec

/-- info: 'STACS2027.RAM.EarR.pCond_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pCond_spec

/-- info: 'STACS2027.RAM.EarR.pRound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pRound_spec

/-- info: 'STACS2027.RAM.EarR.PLInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.PLInv

/-- info: 'STACS2027.RAM.EarR.peelLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.peelLoop_spec

/-- info: 'STACS2027.RAM.EarR.sum_adj_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.sum_adj_succ

/-- info: 'STACS2027.RAM.EarR.peel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.peel_spec

/-- info: 'STACS2027.RAM.EarR.init_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.init_spec

/-- info: 'STACS2027.RAM.EarR.rO1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rO1

/-- info: 'STACS2027.RAM.EarR.rO2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rO2

/-- info: 'STACS2027.RAM.EarR.rHD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rHD

/-- info: 'STACS2027.RAM.EarR.rDEG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rDEG

/-- info: 'STACS2027.RAM.EarR.rDEAD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rDEAD

/-- info: 'STACS2027.RAM.EarR.rSTK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rSTK

/-- info: 'STACS2027.RAM.EarR.rLGV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rLGV

/-- info: 'STACS2027.RAM.EarR.rLGU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rLGU

/-- info: 'STACS2027.RAM.EarR.rLGW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rLGW

/-- info: 'STACS2027.RAM.EarR.rVAL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rVAL

/-- info: 'STACS2027.RAM.EarR.rNXT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rNXT

/-- info: 'STACS2027.RAM.EarR.rSUCC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rSUCC

/-- info: 'STACS2027.RAM.EarR.rTWO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rTWO

/-- info: 'STACS2027.RAM.EarR.rSP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rSP

/-- info: 'STACS2027.RAM.EarR.rCNT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rCNT

/-- info: 'STACS2027.RAM.EarR.rLC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rLC

/-- info: 'STACS2027.RAM.EarR.rNP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rNP

/-- info: 'STACS2027.RAM.EarR.rI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rI

/-- info: 'STACS2027.RAM.EarR.rA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rA

/-- info: 'STACS2027.RAM.EarR.rB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rB

/-- info: 'STACS2027.RAM.EarR.rV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rV

/-- info: 'STACS2027.RAM.EarR.rU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rU

/-- info: 'STACS2027.RAM.EarR.rW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rW

/-- info: 'STACS2027.RAM.EarR.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rX

/-- info: 'STACS2027.RAM.EarR.rK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rK

/-- info: 'STACS2027.RAM.EarR.rP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rP

/-- info: 'STACS2027.RAM.EarR.rQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rQ

/-- info: 'STACS2027.RAM.EarR.rZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rZ

/-- info: 'STACS2027.RAM.EarR.rD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rD

/-- info: 'STACS2027.RAM.EarR.rY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rY

/-- info: 'STACS2027.RAM.EarR.rC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rC

/-- info: 'STACS2027.RAM.EarR.rPD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rPD

/-- info: 'STACS2027.RAM.EarR.rSZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rSZ

/-- info: 'STACS2027.RAM.EarR.rPRM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rPRM

/-- info: 'STACS2027.RAM.EarR.rPSTK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rPSTK

/-- info: 'STACS2027.RAM.EarR.rPSP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rPSP

/-- info: 'STACS2027.RAM.EarR.poolSz' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.poolSz

/-- info: 'STACS2027.RAM.EarR.bPD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bPD

/-- info: 'STACS2027.RAM.EarR.bPRM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bPRM

/-- info: 'STACS2027.RAM.EarR.bPSTK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bPSTK

/-- info: 'STACS2027.RAM.EarR.bO1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bO1

/-- info: 'STACS2027.RAM.EarR.bO2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bO2

/-- info: 'STACS2027.RAM.EarR.bHD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bHD

/-- info: 'STACS2027.RAM.EarR.bDEG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bDEG

/-- info: 'STACS2027.RAM.EarR.bDEAD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bDEAD

/-- info: 'STACS2027.RAM.EarR.bSTK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bSTK

/-- info: 'STACS2027.RAM.EarR.bLGV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bLGV

/-- info: 'STACS2027.RAM.EarR.bLGU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bLGU

/-- info: 'STACS2027.RAM.EarR.bLGW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bLGW

/-- info: 'STACS2027.RAM.EarR.bVAL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bVAL

/-- info: 'STACS2027.RAM.EarR.bNXT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bNXT

/-- info: 'STACS2027.RAM.EarR.bSUCC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bSUCC

/-- info: 'STACS2027.RAM.EarR.bHAM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bHAM

/-- info: 'STACS2027.RAM.EarR.bEND' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bEND

/-- info: 'STACS2027.RAM.EarR.bEND_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.bEND_le

/-- info: 'STACS2027.RAM.EarR.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.fits

/-- info: 'STACS2027.RAM.EarR.prepend' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.prepend

/-- info: 'STACS2027.RAM.EarR.incDeg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.incDeg

/-- info: 'STACS2027.RAM.EarR.push' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.push

/-- info: 'STACS2027.RAM.EarR.decDegP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.decDegP

/-- info: 'STACS2027.RAM.EarR.allocs1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.allocs1

/-- info: 'STACS2027.RAM.EarR.allocs2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.allocs2

/-- info: 'STACS2027.RAM.EarR.edgeBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.edgeBody

/-- info: 'STACS2027.RAM.EarR.stkBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.stkBody

/-- info: 'STACS2027.RAM.EarR.mcond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.mcond

/-- info: 'STACS2027.RAM.EarR.pop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pop

/-- info: 'STACS2027.RAM.EarR.scanInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scanInit

/-- info: 'STACS2027.RAM.EarR.scanUpd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scanUpd

/-- info: 'STACS2027.RAM.EarR.scanBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scanBody

/-- info: 'STACS2027.RAM.EarR.scanCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scanCond

/-- info: 'STACS2027.RAM.EarR.scan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scan

/-- info: 'STACS2027.RAM.EarR.killLog' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.killLog

/-- info: 'STACS2027.RAM.EarR.eqChk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.eqChk

/-- info: 'STACS2027.RAM.EarR.outChk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.outChk

/-- info: 'STACS2027.RAM.EarR.addVirt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.addVirt

/-- info: 'STACS2027.RAM.EarR.decBoth' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.decBoth

/-- info: 'STACS2027.RAM.EarR.elimBlk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.elimBlk

/-- info: 'STACS2027.RAM.EarR.checkDeg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.checkDeg

/-- info: 'STACS2027.RAM.EarR.mbody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.mbody

/-- info: 'STACS2027.RAM.EarR.mainLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.mainLoop

/-- info: 'STACS2027.RAM.EarR.ppush' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.ppush

/-- info: 'STACS2027.RAM.EarR.pInitBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pInitBody

/-- info: 'STACS2027.RAM.EarR.pUpd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pUpd

/-- info: 'STACS2027.RAM.EarR.pScanBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pScanBody

/-- info: 'STACS2027.RAM.EarR.pScanInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pScanInit

/-- info: 'STACS2027.RAM.EarR.pScan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pScan

/-- info: 'STACS2027.RAM.EarR.pPop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pPop

/-- info: 'STACS2027.RAM.EarR.pBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pBody

/-- info: 'STACS2027.RAM.EarR.pCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pCond

/-- info: 'STACS2027.RAM.EarR.peelProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.peelProg

/-- info: 'STACS2027.RAM.EarR.initProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.initProg

/-- info: 'STACS2027.RAM.EarR.triInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triInit

/-- info: 'STACS2027.RAM.EarR.triUpd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triUpd

/-- info: 'STACS2027.RAM.EarR.triBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triBody

/-- info: 'STACS2027.RAM.EarR.succInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.succInit

/-- info: 'STACS2027.RAM.EarR.reinsBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.reinsBody

/-- info: 'STACS2027.RAM.EarR.walkBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.walkBody

/-- info: 'STACS2027.RAM.EarR.recon' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.recon

/-- info: 'STACS2027.RAM.EarR.earProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.earProg

/-- info: 'STACS2027.RAM.EarR.Glob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.Glob

/-- info: 'STACS2027.RAM.EarR.WV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.WV

/-- info: 'STACS2027.RAM.EarR.Glob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.Glob.regIndep

/-- info: 'STACS2027.RAM.EarR.EMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem

/-- info: 'STACS2027.RAM.EarR.EMem.updLow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.updLow

/-- info: 'STACS2027.RAM.EarR.EMem.rebase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.rebase

/-- info: 'STACS2027.RAM.EarR.EMem.prepend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.prepend

/-- info: 'STACS2027.RAM.EarR.EMem.setDeg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.setDeg

/-- info: 'STACS2027.RAM.EarR.EMem.kill' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.kill

/-- info: 'STACS2027.RAM.EarR.EMem.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.push

/-- info: 'STACS2027.RAM.EarR.EMem.log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.log

/-- info: 'STACS2027.RAM.EarR.EMem.setSucc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.setSucc

/-- info: 'STACS2027.RAM.EarR.EMem.hamSnoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.hamSnoc

/-- info: 'STACS2027.RAM.EarR.EMem.pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.EMem.pop

/-- info: 'STACS2027.RAM.EarR.triPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triPre

/-- info: 'STACS2027.RAM.EarR.succ0Of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.succ0Of

/-- info: 'STACS2027.RAM.EarR.earHam_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.earHam_eq

/-- info: 'STACS2027.RAM.EarR.triPre_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triPre_succ

/-- info: 'STACS2027.RAM.EarR.triPre_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triPre_lt

/-- info: 'STACS2027.RAM.EarR.good_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.good_loop

/-- info: 'STACS2027.RAM.EarR.rev_map_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.rev_map_get

/-- info: 'STACS2027.RAM.EarR.RRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.RRep

/-- info: 'STACS2027.RAM.EarR.RRep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.RRep.indep

/-- info: 'STACS2027.RAM.EarR.triUpd_K' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triUpd_K

/-- info: 'STACS2027.RAM.EarR.triUpd_X' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triUpd_X

/-- info: 'STACS2027.RAM.EarR.triUpd_Y' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triUpd_Y

/-- info: 'STACS2027.RAM.EarR.triUpd_Z' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triUpd_Z

/-- info: 'STACS2027.RAM.EarR.triUpd_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triUpd_reg

/-- info: 'STACS2027.RAM.EarR.TriInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.TriInv

/-- info: 'STACS2027.RAM.EarR.triBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.triBody_spec

/-- info: 'STACS2027.RAM.EarR.succInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.succInit_spec

/-- info: 'STACS2027.RAM.EarR.ReInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.ReInv

/-- info: 'STACS2027.RAM.EarR.reinsBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.reinsBody_spec

/-- info: 'STACS2027.RAM.EarR.WInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.WInv

/-- info: 'STACS2027.RAM.EarR.walkBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.walkBody_spec

/-- info: 'STACS2027.RAM.EarR.pop_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pop_addrOK

/-- info: 'STACS2027.RAM.EarR.pop_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.pop_run

/-- info: 'STACS2027.RAM.EarR.mcond_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.mcond_run

/-- info: 'STACS2027.RAM.EarR.alive' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.alive

/-- info: 'STACS2027.RAM.EarR.scanUpd_K' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scanUpd_K

/-- info: 'STACS2027.RAM.EarR.scanUpd_U' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scanUpd_U

/-- info: 'STACS2027.RAM.EarR.scanUpd_W' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scanUpd_W

/-- info: 'STACS2027.RAM.EarR.scanUpd_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scanUpd_reg

/-- info: 'STACS2027.RAM.EarR.ScanInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.ScanInv

/-- info: 'STACS2027.RAM.EarR.alive_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.alive_take_succ

/-- info: 'STACS2027.RAM.EarR.scanStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scanStep

/-- info: 'STACS2027.RAM.EarR.scan_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scan_core

/-- info: 'STACS2027.RAM.EarR.scan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.scan_spec

/-- info: 'STACS2027.RAM.EarR.Running' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.Running

/-- info: 'STACS2027.RAM.EarR.loop_eq_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.loop_eq_loop

/-- info: 'STACS2027.RAM.EarR.fin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.fin

/-- info: 'STACS2027.RAM.EarR.loop_eq_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.loop_eq_fin

/-- info: 'STACS2027.RAM.EarR.fin_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.fin_step

/-- info: 'STACS2027.RAM.EarR.fin_stop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.fin_stop

/-- info: 'STACS2027.RAM.EarR.loop_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.loop_init

/-- info: 'STACS2027.RAM.EarR.Good' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.Good

/-- info: 'STACS2027.RAM.EarR.getD_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.getD_lt

/-- info: 'STACS2027.RAM.EarR.mem_decDeg_stack' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.mem_decDeg_stack

/-- info: 'STACS2027.RAM.EarR.mem_elim_stack' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.mem_elim_stack

/-- info: 'STACS2027.RAM.EarR.mem_elim_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.mem_elim_adj

/-- info: 'STACS2027.RAM.EarR.nbOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.nbOf

/-- info: 'STACS2027.RAM.EarR.nbOf_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.nbOf_lt

/-- info: 'STACS2027.RAM.EarR.good_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.good_step

/-- info: 'STACS2027.RAM.EarR.matInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.matInit

/-- info: 'STACS2027.RAM.EarR.stackPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.stackPre

/-- info: 'STACS2027.RAM.EarR.init_adj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.init_adj

/-- info: 'STACS2027.RAM.EarR.init_deg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.init_deg

/-- info: 'STACS2027.RAM.EarR.init_dead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.init_dead

/-- info: 'STACS2027.RAM.EarR.init_stack' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.init_stack

/-- info: 'STACS2027.RAM.EarR.init_log' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.init_log

/-- info: 'STACS2027.RAM.EarR.init_cnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.init_cnt

/-- info: 'STACS2027.RAM.EarR.take_succ_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.take_succ_eq

/-- info: 'STACS2027.RAM.EarR.initAdj_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.initAdj_append

/-- info: 'STACS2027.RAM.EarR.initAdj_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.initAdj_take_succ

/-- info: 'STACS2027.RAM.EarR.initAdj_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.initAdj_nil

/-- info: 'STACS2027.RAM.EarR.stackPre_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.stackPre_succ

/-- info: 'STACS2027.RAM.EarR.stackPre_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.stackPre_lt

/-- info: 'STACS2027.RAM.EarR.length_stackPre_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.length_stackPre_le

/-- info: 'STACS2027.RAM.EarR.mem_update_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.mem_update_cons

/-- info: 'STACS2027.RAM.EarR.initAdj_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.initAdj_lt

/-- info: 'STACS2027.RAM.EarR.length_update_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.length_update_cons

/-- info: 'STACS2027.RAM.EarR.sum_initAdj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.sum_initAdj

/-- info: 'STACS2027.RAM.EarR.asum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.asum

/-- info: 'STACS2027.RAM.EarR.length_elim_adj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.length_elim_adj

/-- info: 'STACS2027.RAM.EarR.asum_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.asum_elim

/-- info: 'STACS2027.RAM.EarR.asum_init_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.asum_init_le

/-- info: 'STACS2027.RAM.EarR.getD_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.getD_snoc

/-- info: 'STACS2027.RAM.EarR.filter_take_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.filter_take_succ

/-- info: 'STACS2027.RAM.EarR.foldl_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.foldl_take_succ

/-- info: 'STACS2027.RAM.EarR.reinsert_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.reinsert_lt

/-- info: 'STACS2027.RAM.EarR.foldl_reinsert_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.foldl_reinsert_lt

/-- info: 'STACS2027.RAM.EarR.length_walk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.length_walk

/-- info: 'STACS2027.RAM.EarR.walk_getElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.walk_getElem

/-- info: 'STACS2027.RAM.EarR.iterate_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarR.iterate_lt

/-- info: 'STACS2027.RAM.wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs

/-- info: 'STACS2027.RAM.stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores

/-- info: 'STACS2027.RAM.writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes

/-- info: 'STACS2027.RAM.wregs_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_seq

/-- info: 'STACS2027.RAM.wregs_ifz' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_ifz

/-- info: 'STACS2027.RAM.wregs_loop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_loop

/-- info: 'STACS2027.RAM.stores_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_seq

/-- info: 'STACS2027.RAM.stores_ifz' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_ifz

/-- info: 'STACS2027.RAM.stores_loop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_loop

/-- info: 'STACS2027.RAM.writes_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_seq

/-- info: 'STACS2027.RAM.writes_ifz' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_ifz

/-- info: 'STACS2027.RAM.writes_loop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_loop

/-- info: 'STACS2027.RAM.Frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Frame

/-- info: 'STACS2027.RAM.Exec.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Exec.frame

/-- info: 'STACS2027.RAM.Exec.reg_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Exec.reg_frame

/-- info: 'STACS2027.RAM.Exec.mem_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Exec.mem_frame

/-- info: 'STACS2027.RAM.Exec.out_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Exec.out_frame

/-- info: 'STACS2027.RAM.run_reg_of_not_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_reg_of_not_mem

/-- info: 'STACS2027.RAM.run_mem_of_stores' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_mem_of_stores

/-- info: 'STACS2027.RAM.run_out_of_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_out_of_writes

/-- info: 'STACS2027.RAM.Agree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Agree

/-- info: 'STACS2027.RAM.Indep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep

/-- info: 'STACS2027.RAM.Agree.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Agree.refl

/-- info: 'STACS2027.RAM.Agree.symm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Agree.symm

/-- info: 'STACS2027.RAM.Agree.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Agree.trans

/-- info: 'STACS2027.RAM.Agree.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Agree.mono

/-- info: 'STACS2027.RAM.agree_setReg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.agree_setReg

/-- info: 'STACS2027.RAM.Frame.agree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Frame.agree

/-- info: 'STACS2027.RAM.run_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_frame

/-- info: 'STACS2027.RAM.agree_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.agree_run

/-- info: 'STACS2027.RAM.Indep.iff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.iff

/-- info: 'STACS2027.RAM.Indep.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.mono

/-- info: 'STACS2027.RAM.Indep.and' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.and

/-- info: 'STACS2027.RAM.Indep.or' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.or

/-- info: 'STACS2027.RAM.Indep.imp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.imp

/-- info: 'STACS2027.RAM.Indep.not' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.not

/-- info: 'STACS2027.RAM.Indep.forall' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.«forall»

/-- info: 'STACS2027.RAM.Indep.exists' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.«exists»

/-- info: 'STACS2027.RAM.Indep.const' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.const

/-- info: 'STACS2027.RAM.Indep.reg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.reg

/-- info: 'STACS2027.RAM.Indep.memOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.memOut

/-- info: 'STACS2027.RAM.Indep.mem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.mem

/-- info: 'STACS2027.RAM.Indep.out' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.out

/-- info: 'STACS2027.RAM.Indep.setReg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.setReg

/-- info: 'STACS2027.RAM.RegIndep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep

/-- info: 'STACS2027.RAM.RegIndep.indep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.indep

/-- info: 'STACS2027.RAM.RegIndep.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.mono

/-- info: 'STACS2027.RAM.RegIndep.and' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.and

/-- info: 'STACS2027.RAM.RegIndep.const' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.const

/-- info: 'STACS2027.RAM.RegIndep.reg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.reg

/-- info: 'STACS2027.RAM.RegIndep.exec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.exec

/-- info: 'STACS2027.RAM.RegIndep.run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.run

/-- info: 'STACS2027.RAM.RegIndep.run_of_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.run_of_sub

/-- info: 'STACS2027.RAM.RegIndep.setReg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.setReg

/-- info: 'STACS2027.RAM.RegIndep.setMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.setMem

/-- info: 'STACS2027.RAM.RegIndep.emit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.RegIndep.emit

/-- info: 'STACS2027.RAM.Indep.run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Indep.run

/-- info: 'STACS2027.RAM.decLoopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.decLoopFree

/-- info: 'STACS2027.RAM.HT.skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.skip

/-- info: 'STACS2027.RAM.HT.run_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.run_le

/-- info: 'STACS2027.RAM.HT.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.frame

/-- info: 'STACS2027.RAM.HT.frameReg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.frameReg

/-- info: 'STACS2027.RAM.HT.frameIndep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.frameIndep

/-- info: 'STACS2027.RAM.HT.withFrame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.withFrame

/-- info: 'STACS2027.RAM.HT.and' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.and

/-- info: 'STACS2027.RAM.HT.exists_pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.exists_pre

/-- info: 'STACS2027.RAM.HT.prop_pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.prop_pre

/-- info: 'STACS2027.RAM.HT.cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.cases

/-- info: 'STACS2027.RAM.HT.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.casesOn

/-- info: 'STACS2027.RAM.HT.of_forall' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.of_forall

/-- info: 'STACS2027.RAM.HT.seq3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.seq3

/-- info: 'STACS2027.RAM.HT.seq_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.seq_le

/-- info: 'STACS2027.RAM.HT.loopT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.loopT

/-- info: 'STACS2027.RAM.HTt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HTt

/-- info: 'STACS2027.RAM.HT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HT

/-- info: 'STACS2027.RAM.HT.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.mono

/-- info: 'STACS2027.RAM.HT.pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.pre

/-- info: 'STACS2027.RAM.HT.post' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.post

/-- info: 'STACS2027.RAM.HT.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.weaken

/-- info: 'STACS2027.RAM.HT.seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.seq

/-- info: 'STACS2027.RAM.HT.ifz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.ifz

/-- info: 'STACS2027.RAM.HT.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.run

/-- info: 'STACS2027.RAM.HT.loopPot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.loopPot

/-- info: 'STACS2027.RAM.HT.loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.loop

/-- info: 'STACS2027.RAM.HT.body_of_HT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.body_of_HT

/-- info: 'STACS2027.RAM.gBS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gBS

/-- info: 'STACS2027.RAM.gBL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gBL

/-- info: 'STACS2027.RAM.gLOC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gLOC

/-- info: 'STACS2027.RAM.gPN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gPN

/-- info: 'STACS2027.RAM.gPE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gPE

/-- info: 'STACS2027.RAM.gPU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gPU

/-- info: 'STACS2027.RAM.gPV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gPV

/-- info: 'STACS2027.RAM.gOMAP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gOMAP

/-- info: 'STACS2027.RAM.gP0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gP0

/-- info: 'STACS2027.RAM.GraphBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.GraphBase

/-- info: 'STACS2027.RAM.R0.R0Post.base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.R0Post.base

/-- info: 'STACS2027.RAM.csrOff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.csrOff

/-- info: 'STACS2027.RAM.csrAdj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.csrAdj

/-- info: 'STACS2027.RAM.R1Post' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1Post

/-- info: 'STACS2027.RAM.lowsOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.lowsOf

/-- info: 'STACS2027.RAM.headsOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.headsOf

/-- info: 'STACS2027.RAM.R2Post' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2Post

/-- info: 'STACS2027.RAM.blockStarts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.blockStarts

/-- info: 'STACS2027.RAM.R3Post' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3Post

/-- info: 'STACS2027.RAM.BlockIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.BlockIn

/-- info: 'STACS2027.RAM.BlockGood' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.BlockGood

/-- info: 'STACS2027.RAM.BlockSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.BlockSpec

/-- info: 'STACS2027.RAM.PolyIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PolyIn

/-- info: 'STACS2027.RAM.PolySpecB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PolySpecB

/-- info: 'STACS2027.RAM.gVN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gVN

/-- info: 'STACS2027.RAM.gVS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gVS

/-- info: 'STACS2027.RAM.gLN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gLN

/-- info: 'STACS2027.RAM.gLU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gLU

/-- info: 'STACS2027.RAM.gLV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gLV

/-- info: 'STACS2027.RAM.gHAM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gHAM

/-- info: 'STACS2027.RAM.gB1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gB1

/-- info: 'STACS2027.RAM.EarIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.EarIn

/-- info: 'STACS2027.RAM.EarSpec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.EarSpec

/-- info: 'STACS2027.RAM.rZERO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.rZERO

/-- info: 'STACS2027.RAM.rONE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.rONE

/-- info: 'STACS2027.RAM.rFREE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.rFREE

/-- info: 'STACS2027.RAM.rT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.rT

/-- info: 'STACS2027.RAM.gM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gM

/-- info: 'STACS2027.RAM.gMX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gMX

/-- info: 'STACS2027.RAM.gD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gD

/-- info: 'STACS2027.RAM.gN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gN

/-- info: 'STACS2027.RAM.gNE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gNE

/-- info: 'STACS2027.RAM.gLB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gLB

/-- info: 'STACS2027.RAM.gEU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gEU

/-- info: 'STACS2027.RAM.gEV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gEV

/-- info: 'STACS2027.RAM.gROW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gROW

/-- info: 'STACS2027.RAM.gMAT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gMAT

/-- info: 'STACS2027.RAM.gR1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gR1

/-- info: 'STACS2027.RAM.gOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gOFF

/-- info: 'STACS2027.RAM.gADJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gADJ

/-- info: 'STACS2027.RAM.gPRE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gPRE

/-- info: 'STACS2027.RAM.gPAR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gPAR

/-- info: 'STACS2027.RAM.gPTR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gPTR

/-- info: 'STACS2027.RAM.gORD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gORD

/-- info: 'STACS2027.RAM.gSTK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gSTK

/-- info: 'STACS2027.RAM.gSP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gSP

/-- info: 'STACS2027.RAM.gCNT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gCNT

/-- info: 'STACS2027.RAM.gR1x' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gR1x

/-- info: 'STACS2027.RAM.gR2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gR2

/-- info: 'STACS2027.RAM.gLOW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gLOW

/-- info: 'STACS2027.RAM.gHEAD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gHEAD

/-- info: 'STACS2027.RAM.gR3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gR3

/-- info: 'STACS2027.RAM.gBST' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gBST

/-- info: 'STACS2027.RAM.gBU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gBU

/-- info: 'STACS2027.RAM.gBV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gBV

/-- info: 'STACS2027.RAM.gR4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gR4

/-- info: 'STACS2027.RAM.rS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.rS

/-- info: 'STACS2027.RAM.Arr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr

/-- info: 'STACS2027.RAM.Tab' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab

/-- info: 'STACS2027.RAM.ZeroFrom' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ZeroFrom

/-- info: 'STACS2027.RAM.SameOn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SameOn

/-- info: 'STACS2027.RAM.upd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.upd

/-- info: 'STACS2027.RAM.upd_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.upd_apply

/-- info: 'STACS2027.RAM.setMem_mem_upd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.setMem_mem_upd

/-- info: 'STACS2027.RAM.upd_same' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.upd_same

/-- info: 'STACS2027.RAM.upd_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.upd_ne

/-- info: 'STACS2027.RAM.getD_eq_getElem'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.getD_eq_getElem'

/-- info: 'STACS2027.RAM.Arr.get' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.get

/-- info: 'STACS2027.RAM.Arr.getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.getD

/-- info: 'STACS2027.RAM.Arr.get'' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.get'

/-- info: 'STACS2027.RAM.Arr.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.congr

/-- info: 'STACS2027.RAM.Arr.of_sameOn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.of_sameOn

/-- info: 'STACS2027.RAM.Arr.ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.ext

/-- info: 'STACS2027.RAM.arr_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.arr_nil

/-- info: 'STACS2027.RAM.arr_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.arr_cons

/-- info: 'STACS2027.RAM.arr_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.arr_append

/-- info: 'STACS2027.RAM.arr_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.arr_singleton

/-- info: 'STACS2027.RAM.arr_replicate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.arr_replicate

/-- info: 'STACS2027.RAM.arr_iff_tab' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.arr_iff_tab

/-- info: 'STACS2027.RAM.Arr.upd_of_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.upd_of_disjoint

/-- info: 'STACS2027.RAM.Arr.upd_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.upd_set

/-- info: 'STACS2027.RAM.Arr.push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.push

/-- info: 'STACS2027.RAM.Arr.upd_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.upd_snoc

/-- info: 'STACS2027.RAM.Arr.snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.snoc

/-- info: 'STACS2027.RAM.Arr.take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.take

/-- info: 'STACS2027.RAM.Arr.prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.prefix

/-- info: 'STACS2027.RAM.Tab.get' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.get

/-- info: 'STACS2027.RAM.Tab.get'' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.get'

/-- info: 'STACS2027.RAM.Tab.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.mono

/-- info: 'STACS2027.RAM.Tab.congr_fun' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.congr_fun

/-- info: 'STACS2027.RAM.Tab.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.congr

/-- info: 'STACS2027.RAM.Tab.of_sameOn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.of_sameOn

/-- info: 'STACS2027.RAM.Tab.snoc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.snoc

/-- info: 'STACS2027.RAM.Tab.ext' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.ext

/-- info: 'STACS2027.RAM.Tab.toArr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.toArr

/-- info: 'STACS2027.RAM.tab_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.tab_zero

/-- info: 'STACS2027.RAM.Tab.upd_of_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.upd_of_disjoint

/-- info: 'STACS2027.RAM.Tab.upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.upd

/-- info: 'STACS2027.RAM.ZeroFrom.get' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ZeroFrom.get

/-- info: 'STACS2027.RAM.ZeroFrom.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ZeroFrom.mono

/-- info: 'STACS2027.RAM.ZeroFrom.arr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ZeroFrom.arr

/-- info: 'STACS2027.RAM.ZeroFrom.tab' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ZeroFrom.tab

/-- info: 'STACS2027.RAM.ZeroFrom.upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ZeroFrom.upd

/-- info: 'STACS2027.RAM.ZeroFrom.of_sameOn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ZeroFrom.of_sameOn

/-- info: 'STACS2027.RAM.SameOn.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SameOn.refl

/-- info: 'STACS2027.RAM.SameOn.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SameOn.trans

/-- info: 'STACS2027.RAM.SameOn.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SameOn.mono

/-- info: 'STACS2027.RAM.SameOn.upd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.SameOn.upd

/-- info: 'STACS2027.RAM.Arr.of_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Arr.of_below

/-- info: 'STACS2027.RAM.Tab.of_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Tab.of_below

/-- info: 'STACS2027.RAM.SameOn.upd_of_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.SameOn.upd_of_ge

/-- info: 'STACS2027.RAM.ZeroFrom.alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ZeroFrom.alloc

/-- info: 'STACS2027.RAM.cell_div' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cell_div

/-- info: 'STACS2027.RAM.cell_mod' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.cell_mod

/-- info: 'STACS2027.RAM.cell_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cell_lt

/-- info: 'STACS2027.RAM.cell_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cell_inj

/-- info: 'STACS2027.RAM.initial_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.initial_reg

/-- info: 'STACS2027.RAM.initial_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.initial_out

/-- info: 'STACS2027.RAM.initial_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.initial_mem

/-- info: 'STACS2027.RAM.arr_initial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.arr_initial

/-- info: 'STACS2027.RAM.zeroFrom_initial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.zeroFrom_initial

/-- info: 'STACS2027.RAM.graphInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.graphInput

/-- info: 'STACS2027.RAM.labelBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.labelBound

/-- info: 'STACS2027.RAM.length_flatMap_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.length_flatMap_pair

/-- info: 'STACS2027.RAM.length_graphInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.length_graphInput

/-- info: 'STACS2027.RAM.getD_flatMap_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.getD_flatMap_pair

/-- info: 'STACS2027.RAM.initial_graphInput_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.initial_graphInput_entry

/-- info: 'STACS2027.RAM.setReg_setReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.setReg_setReg

/-- info: 'STACS2027.RAM.setReg_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.setReg_comm

/-- info: 'STACS2027.RAM.setReg_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.setReg_self

/-- info: 'STACS2027.RAM.run_const' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_const

/-- info: 'STACS2027.RAM.run_add' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_add

/-- info: 'STACS2027.RAM.run_sub' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_sub

/-- info: 'STACS2027.RAM.run_load' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_load

/-- info: 'STACS2027.RAM.run_store' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_store

/-- info: 'STACS2027.RAM.run_write' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_write

/-- info: 'STACS2027.RAM.run_skip' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_skip

/-- info: 'STACS2027.RAM.run_seq'' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_seq'

/-- info: 'STACS2027.RAM.run_ifz'' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_ifz'

/-- info: 'STACS2027.RAM.config_ite_reg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.config_ite_reg

/-- info: 'STACS2027.RAM.config_ite_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.config_ite_mem

/-- info: 'STACS2027.RAM.config_ite_out' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.config_ite_out

/-- info: 'STACS2027.RAM.HT.const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.const

/-- info: 'STACS2027.RAM.HT.add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.add

/-- info: 'STACS2027.RAM.HT.sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.sub

/-- info: 'STACS2027.RAM.HT.load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.load

/-- info: 'STACS2027.RAM.HT.store' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.store

/-- info: 'STACS2027.RAM.HT.write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.write

/-- info: 'STACS2027.RAM.mov' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.mov

/-- info: 'STACS2027.RAM.addc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.addc

/-- info: 'STACS2027.RAM.subc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.subc

/-- info: 'STACS2027.RAM.inc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.inc

/-- info: 'STACS2027.RAM.dec' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.dec

/-- info: 'STACS2027.RAM.swap' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.swap

/-- info: 'STACS2027.RAM.run_mov' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_mov

/-- info: 'STACS2027.RAM.run_addc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_addc

/-- info: 'STACS2027.RAM.run_subc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_subc

/-- info: 'STACS2027.RAM.run_inc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_inc

/-- info: 'STACS2027.RAM.run_dec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_dec

/-- info: 'STACS2027.RAM.run_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_swap

/-- info: 'STACS2027.RAM.ld' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ld

/-- info: 'STACS2027.RAM.st' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.st

/-- info: 'STACS2027.RAM.run_ld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_ld

/-- info: 'STACS2027.RAM.run_st' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_st

/-- info: 'STACS2027.RAM.ifLt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ifLt

/-- info: 'STACS2027.RAM.ifLe' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ifLe

/-- info: 'STACS2027.RAM.ifEq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ifEq

/-- info: 'STACS2027.RAM.run_ifLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_ifLt

/-- info: 'STACS2027.RAM.run_ifLe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_ifLe

/-- info: 'STACS2027.RAM.run_ifEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_ifEq

/-- info: 'STACS2027.RAM.loopFree_mov' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_mov

/-- info: 'STACS2027.RAM.loopFree_addc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_addc

/-- info: 'STACS2027.RAM.loopFree_subc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_subc

/-- info: 'STACS2027.RAM.loopFree_inc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_inc

/-- info: 'STACS2027.RAM.loopFree_dec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_dec

/-- info: 'STACS2027.RAM.loopFree_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_swap

/-- info: 'STACS2027.RAM.loopFree_ld' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_ld

/-- info: 'STACS2027.RAM.loopFree_st' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_st

/-- info: 'STACS2027.RAM.loopFree_ifLt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_ifLt

/-- info: 'STACS2027.RAM.loopFree_ifLe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_ifLe

/-- info: 'STACS2027.RAM.loopFree_ifEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_ifEq

/-- info: 'STACS2027.RAM.size_mov' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_mov

/-- info: 'STACS2027.RAM.size_addc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_addc

/-- info: 'STACS2027.RAM.size_subc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_subc

/-- info: 'STACS2027.RAM.size_inc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_inc

/-- info: 'STACS2027.RAM.size_dec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_dec

/-- info: 'STACS2027.RAM.size_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_swap

/-- info: 'STACS2027.RAM.size_ld' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_ld

/-- info: 'STACS2027.RAM.size_st' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_st

/-- info: 'STACS2027.RAM.size_ifLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_ifLt

/-- info: 'STACS2027.RAM.size_ifLe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_ifLe

/-- info: 'STACS2027.RAM.size_ifEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_ifEq

/-- info: 'STACS2027.RAM.wregs_mov' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_mov

/-- info: 'STACS2027.RAM.wregs_addc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_addc

/-- info: 'STACS2027.RAM.wregs_subc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_subc

/-- info: 'STACS2027.RAM.wregs_inc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_inc

/-- info: 'STACS2027.RAM.wregs_dec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_dec

/-- info: 'STACS2027.RAM.wregs_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_swap

/-- info: 'STACS2027.RAM.wregs_ld' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_ld

/-- info: 'STACS2027.RAM.wregs_st' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_st

/-- info: 'STACS2027.RAM.wregs_ifLt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_ifLt

/-- info: 'STACS2027.RAM.wregs_ifEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_ifEq

/-- info: 'STACS2027.RAM.stores_mov' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_mov

/-- info: 'STACS2027.RAM.stores_addc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_addc

/-- info: 'STACS2027.RAM.stores_subc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_subc

/-- info: 'STACS2027.RAM.stores_inc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_inc

/-- info: 'STACS2027.RAM.stores_dec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_dec

/-- info: 'STACS2027.RAM.stores_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_swap

/-- info: 'STACS2027.RAM.stores_ld' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_ld

/-- info: 'STACS2027.RAM.stores_st' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_st

/-- info: 'STACS2027.RAM.stores_ifLt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_ifLt

/-- info: 'STACS2027.RAM.stores_ifEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_ifEq

/-- info: 'STACS2027.RAM.writes_mov' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_mov

/-- info: 'STACS2027.RAM.writes_addc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_addc

/-- info: 'STACS2027.RAM.writes_subc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_subc

/-- info: 'STACS2027.RAM.writes_inc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_inc

/-- info: 'STACS2027.RAM.writes_dec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_dec

/-- info: 'STACS2027.RAM.writes_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_swap

/-- info: 'STACS2027.RAM.writes_ld' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_ld

/-- info: 'STACS2027.RAM.writes_st' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_st

/-- info: 'STACS2027.RAM.writes_ifLt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_ifLt

/-- info: 'STACS2027.RAM.writes_ifEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_ifEq

/-- info: 'STACS2027.RAM.HT.mov' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.mov

/-- info: 'STACS2027.RAM.HT.addc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.addc

/-- info: 'STACS2027.RAM.HT.subc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.subc

/-- info: 'STACS2027.RAM.HT.ld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.ld

/-- info: 'STACS2027.RAM.HT.st' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.st

/-- info: 'STACS2027.RAM.HT.ifLt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.ifLt

/-- info: 'STACS2027.RAM.HT.ifLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.ifLe

/-- info: 'STACS2027.RAM.HT.ifEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.ifEq

/-- info: 'STACS2027.RAM.upLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.upLoop

/-- info: 'STACS2027.RAM.forUp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.forUp

/-- info: 'STACS2027.RAM.forRange' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.forRange

/-- info: 'STACS2027.RAM.wregs_upLoop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_upLoop

/-- info: 'STACS2027.RAM.stores_upLoop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_upLoop

/-- info: 'STACS2027.RAM.writes_upLoop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_upLoop

/-- info: 'STACS2027.RAM.wregs_forUp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_forUp

/-- info: 'STACS2027.RAM.stores_forUp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_forUp

/-- info: 'STACS2027.RAM.writes_forUp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_forUp

/-- info: 'STACS2027.RAM.wregs_forRange' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_forRange

/-- info: 'STACS2027.RAM.stores_forRange' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_forRange

/-- info: 'STACS2027.RAM.writes_forRange' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_forRange

/-- info: 'STACS2027.RAM.HT.upLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.upLoop

/-- info: 'STACS2027.RAM.HT.forUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.forUp

/-- info: 'STACS2027.RAM.HT.forUpC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.forUpC

/-- info: 'STACS2027.RAM.HT.forRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.forRange

/-- info: 'STACS2027.RAM.mul' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.mul

/-- info: 'STACS2027.RAM.wregs_mul' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_mul

/-- info: 'STACS2027.RAM.stores_mul' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_mul

/-- info: 'STACS2027.RAM.writes_mul' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_mul

/-- info: 'STACS2027.RAM.HT.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.mul

/-- info: 'STACS2027.RAM.whileC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.whileC

/-- info: 'STACS2027.RAM.wregs_whileC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_whileC

/-- info: 'STACS2027.RAM.stores_whileC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_whileC

/-- info: 'STACS2027.RAM.writes_whileC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_whileC

/-- info: 'STACS2027.RAM.HT.whileC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.whileC

/-- info: 'STACS2027.RAM.HT.whileCPot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.whileCPot

/-- info: 'STACS2027.RAM.alloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.alloc

/-- info: 'STACS2027.RAM.wregs_alloc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.wregs_alloc

/-- info: 'STACS2027.RAM.stores_alloc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.stores_alloc

/-- info: 'STACS2027.RAM.writes_alloc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.writes_alloc

/-- info: 'STACS2027.RAM.loopFree_alloc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_alloc

/-- info: 'STACS2027.RAM.size_alloc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_alloc

/-- info: 'STACS2027.RAM.run_alloc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_alloc

/-- info: 'STACS2027.RAM.HT.alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.HT.alloc

/-- info: 'STACS2027.RAM.Main.polyProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.polyProg

/-- info: 'STACS2027.RAM.Main.solverProg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.solverProg

/-- info: 'STACS2027.RAM.Main.k23Prog' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.k23Prog

/-- info: 'STACS2027.RAM.Main.CP' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.CP

/-- info: 'STACS2027.RAM.Main.CBk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.CBk

/-- info: 'STACS2027.RAM.Main.Ck23' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.Ck23

/-- info: 'STACS2027.RAM.Main.polyProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.polyProg_spec

/-- info: 'STACS2027.RAM.Main.polyProg_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.polyProg_wregs

/-- info: 'STACS2027.RAM.Main.solverProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.solverProg_spec

/-- info: 'STACS2027.RAM.Main.solverProg_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.solverProg_wregs

/-- info: 'STACS2027.RAM.Main.space_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.space_le

/-- info: 'STACS2027.RAM.Main.k23Prog_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.k23Prog_spec

/-- info: 'STACS2027.RAM.Main.k23Prog_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.k23Prog_computes

/-- info: 'STACS2027.RAM.Main.mem_idEdges_of_blocksOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.mem_idEdges_of_blocksOf

/-- info: 'STACS2027.RAM.Main.blocksOf_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.blocksOf_ends

/-- info: 'STACS2027.RAM.Main.blocksOf_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.blocksOf_nodup

/-- info: 'STACS2027.RAM.Main.blockGood_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.blockGood_of

/-- info: 'STACS2027.RAM.Main.blockGood_blocksOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.blockGood_blocksOf

/-- info: 'STACS2027.RAM.Main.rH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.rH

/-- info: 'STACS2027.RAM.Main.rH1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.rH1

/-- info: 'STACS2027.RAM.Main.setBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.setBlock

/-- info: 'STACS2027.RAM.Main.loopBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.loopBody

/-- info: 'STACS2027.RAM.Main.blockLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.blockLoop

/-- info: 'STACS2027.RAM.Main.CL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.CL

/-- info: 'STACS2027.RAM.Main.loopEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.loopEnd

/-- info: 'STACS2027.RAM.Main.loopEnd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.loopEnd_le

/-- info: 'STACS2027.RAM.Main.blk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.blk

/-- info: 'STACS2027.RAM.Main.length_blocksOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.length_blocksOf

/-- info: 'STACS2027.RAM.Main.blk_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.blk_mem

/-- info: 'STACS2027.RAM.Main.getElem_blocksOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.getElem_blocksOf

/-- info: 'STACS2027.RAM.Main.sum_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.sum_blk

/-- info: 'STACS2027.RAM.Main.outPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.outPre

/-- info: 'STACS2027.RAM.Main.outPre_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.outPre_zero

/-- info: 'STACS2027.RAM.Main.outPre_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.outPre_succ

/-- info: 'STACS2027.RAM.Main.flatMap_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.flatMap_out

/-- info: 'STACS2027.RAM.Main.outPre_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.outPre_full

/-- info: 'STACS2027.RAM.Main.LoopInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.LoopInv

/-- info: 'STACS2027.RAM.Main.bst_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.bst_read

/-- info: 'STACS2027.RAM.Main.bu_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.bu_read

/-- info: 'STACS2027.RAM.Main.bv_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.bv_read

/-- info: 'STACS2027.RAM.Main.run_setBlock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.run_setBlock

/-- info: 'STACS2027.RAM.Main.loopInv_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.loopInv_indep

/-- info: 'STACS2027.RAM.Main.setBlock_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.setBlock_spec

/-- info: 'STACS2027.RAM.Main.not_mem_of_footprint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.not_mem_of_footprint

/-- info: 'STACS2027.RAM.Main.body_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.body_spec

/-- info: 'STACS2027.RAM.Main.alloc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.alloc_spec

/-- info: 'STACS2027.RAM.Main.blockLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Main.blockLoop_spec

/-- info: 'STACS2027.RAM.Config' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Config

/-- info: 'STACS2027.RAM.Stmt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Stmt

/-- info: 'STACS2027.RAM.Config.setReg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Config.setReg

/-- info: 'STACS2027.RAM.Config.setMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Config.setMem

/-- info: 'STACS2027.RAM.Config.emit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Config.emit

/-- info: 'STACS2027.RAM.Exec' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Exec

/-- info: 'STACS2027.RAM.initial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.initial

/-- info: 'STACS2027.RAM.Computes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Computes

/-- info: 'STACS2027.RAM.Exec.det' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Exec.det

/-- info: 'STACS2027.RAM.PairIds.rPU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rPU

/-- info: 'STACS2027.RAM.PairIds.rPV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rPV

/-- info: 'STACS2027.RAM.PairIds.rPL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rPL

/-- info: 'STACS2027.RAM.PairIds.rPN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rPN

/-- info: 'STACS2027.RAM.PairIds.rLD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rLD

/-- info: 'STACS2027.RAM.PairIds.rID' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rID

/-- info: 'STACS2027.RAM.PairIds.rCT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rCT

/-- info: 'STACS2027.RAM.PairIds.rNE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rNE

/-- info: 'STACS2027.RAM.PairIds.rST' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rST

/-- info: 'STACS2027.RAM.PairIds.rLQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rLQ

/-- info: 'STACS2027.RAM.PairIds.rJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rJ

/-- info: 'STACS2027.RAM.PairIds.rQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rQ

/-- info: 'STACS2027.RAM.PairIds.rU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rU

/-- info: 'STACS2027.RAM.PairIds.rV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rV

/-- info: 'STACS2027.RAM.PairIds.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rX

/-- info: 'STACS2027.RAM.PairIds.rY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rY

/-- info: 'STACS2027.RAM.PairIds.sortArgs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.sortArgs

/-- info: 'STACS2027.RAM.PairIds.leadAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.leadAlloc

/-- info: 'STACS2027.RAM.PairIds.grpRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.grpRead

/-- info: 'STACS2027.RAM.PairIds.grpHit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.grpHit

/-- info: 'STACS2027.RAM.PairIds.grpNew' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.grpNew

/-- info: 'STACS2027.RAM.PairIds.grpBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.grpBody

/-- info: 'STACS2027.RAM.PairIds.stepGrp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.stepGrp

/-- info: 'STACS2027.RAM.PairIds.pairLeads' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairLeads

/-- info: 'STACS2027.RAM.PairIds.bORD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.bORD

/-- info: 'STACS2027.RAM.PairIds.bST' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.bST

/-- info: 'STACS2027.RAM.PairIds.bLQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.bLQ

/-- info: 'STACS2027.RAM.PairIds.bLD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.bLD

/-- info: 'STACS2027.RAM.PairIds.leadsEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.leadsEnd

/-- info: 'STACS2027.RAM.PairIds.leads_eqs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.leads_eqs

/-- info: 'STACS2027.RAM.PairIds.leadsEnd_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.leadsEnd_le

/-- info: 'STACS2027.RAM.PairIds.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.fits

/-- info: 'STACS2027.RAM.PairIds.PIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.PIn

/-- info: 'STACS2027.RAM.PairIds.GGlob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.GGlob

/-- info: 'STACS2027.RAM.PairIds.WG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.WG

/-- info: 'STACS2027.RAM.PairIds.GGlob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.GGlob.regIndep

/-- info: 'STACS2027.RAM.PairIds.GMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.GMem

/-- info: 'STACS2027.RAM.PairIds.GrpInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.GrpInv

/-- info: 'STACS2027.RAM.PairIds.length_ord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.length_ord

/-- info: 'STACS2027.RAM.PairIds.GMem.hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.GMem.hit

/-- info: 'STACS2027.RAM.PairIds.GMem.new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.GMem.new

/-- info: 'STACS2027.RAM.PairIds.grpBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.grpBody_spec

/-- info: 'STACS2027.RAM.PairIds.stepGrp_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.stepGrp_spec

/-- info: 'STACS2027.RAM.PairIds.LOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.LOut

/-- info: 'STACS2027.RAM.PairIds.CL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.CL

/-- info: 'STACS2027.RAM.PairIds.KeepIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.KeepIn

/-- info: 'STACS2027.RAM.PairIds.pairLeads_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairLeads_core

/-- info: 'STACS2027.RAM.PairIds.pairLeads_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairLeads_spec

/-- info: 'STACS2027.RAM.PairIds.pairLeads_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairLeads_wregs

/-- info: 'STACS2027.RAM.PairIds.pairLeads_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairLeads_writes

/-- info: 'STACS2027.RAM.PairIds.not_mem_wregs_pairLeads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.not_mem_wregs_pairLeads

/-- info: 'STACS2027.RAM.PairIds.rankAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rankAlloc

/-- info: 'STACS2027.RAM.PairIds.rnkNew' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rnkNew

/-- info: 'STACS2027.RAM.PairIds.rnkOld' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rnkOld

/-- info: 'STACS2027.RAM.PairIds.rnkBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rnkBody

/-- info: 'STACS2027.RAM.PairIds.stepRnk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.stepRnk

/-- info: 'STACS2027.RAM.PairIds.cntBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.cntBody

/-- info: 'STACS2027.RAM.PairIds.stepCnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.stepCnt

/-- info: 'STACS2027.RAM.PairIds.rankIds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rankIds

/-- info: 'STACS2027.RAM.PairIds.pairIds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairIds

/-- info: 'STACS2027.RAM.PairIds.eids' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.eids

/-- info: 'STACS2027.RAM.PairIds.length_eids' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.length_eids

/-- info: 'STACS2027.RAM.PairIds.eids_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.eids_lt

/-- info: 'STACS2027.RAM.PairIds.count_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.count_take_succ

/-- info: 'STACS2027.RAM.PairIds.RIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.RIn

/-- info: 'STACS2027.RAM.PairIds.RGlob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.RGlob

/-- info: 'STACS2027.RAM.PairIds.WR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.WR

/-- info: 'STACS2027.RAM.PairIds.RGlob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.RGlob.regIndep

/-- info: 'STACS2027.RAM.PairIds.RnkInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.RnkInv

/-- info: 'STACS2027.RAM.PairIds.rnkBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rnkBody_spec

/-- info: 'STACS2027.RAM.PairIds.stepRnk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.stepRnk_spec

/-- info: 'STACS2027.RAM.PairIds.CtInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.CtInv

/-- info: 'STACS2027.RAM.PairIds.cntBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.cntBody_spec

/-- info: 'STACS2027.RAM.PairIds.stepCnt_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.stepCnt_spec

/-- info: 'STACS2027.RAM.PairIds.ROut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.ROut

/-- info: 'STACS2027.RAM.PairIds.CR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.CR

/-- info: 'STACS2027.RAM.PairIds.rankIds_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rankIds_core

/-- info: 'STACS2027.RAM.PairIds.rankIds_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rankIds_spec

/-- info: 'STACS2027.RAM.PairIds.rankIds_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rankIds_wregs

/-- info: 'STACS2027.RAM.PairIds.rankIds_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rankIds_writes

/-- info: 'STACS2027.RAM.PairIds.idsEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.idsEnd

/-- info: 'STACS2027.RAM.PairIds.idsEnd_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.idsEnd_le

/-- info: 'STACS2027.RAM.PairIds.IOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.IOut

/-- info: 'STACS2027.RAM.PairIds.CI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.CI

/-- info: 'STACS2027.RAM.PairIds.pairIds_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairIds_spec

/-- info: 'STACS2027.RAM.PairIds.pairIds_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairIds_wregs

/-- info: 'STACS2027.RAM.PairIds.pairIds_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairIds_writes

/-- info: 'STACS2027.RAM.PairIds.first_of_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.first_of_sorted

/-- info: 'STACS2027.RAM.PairIds.ldF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.ldF

/-- info: 'STACS2027.RAM.PairIds.ldF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.ldF_zero

/-- info: 'STACS2027.RAM.PairIds.ldF_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.ldF_succ

/-- info: 'STACS2027.RAM.PairIds.rSQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rSQ

/-- info: 'STACS2027.RAM.PairIds.rKY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.rKY

/-- info: 'STACS2027.RAM.PairIds.sldNew' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.sldNew

/-- info: 'STACS2027.RAM.PairIds.sldBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.sldBody

/-- info: 'STACS2027.RAM.PairIds.sortedLeads' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.sortedLeads

/-- info: 'STACS2027.RAM.PairIds.SIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.SIn

/-- info: 'STACS2027.RAM.PairIds.SGlob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.SGlob

/-- info: 'STACS2027.RAM.PairIds.SldInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.SldInv

/-- info: 'STACS2027.RAM.PairIds.sldBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.sldBody_spec

/-- info: 'STACS2027.RAM.PairIds.stepSld_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.stepSld_spec

/-- info: 'STACS2027.RAM.PairIds.sortedLeads_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.sortedLeads_spec

/-- info: 'STACS2027.RAM.PairIds.sortedLeads_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.sortedLeads_wregs

/-- info: 'STACS2027.RAM.PairIds.sortedIds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.sortedIds

/-- info: 'STACS2027.RAM.PairIds.sortedIds_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.sortedIds_spec

/-- info: 'STACS2027.RAM.PairIds.idxOf_getElem_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.idxOf_getElem_eq

/-- info: 'STACS2027.RAM.PairIds.idxOf_getElem_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.idxOf_getElem_eq_self_iff

/-- info: 'STACS2027.RAM.PairIds.idxOf_getElem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.idxOf_getElem_le

/-- info: 'STACS2027.RAM.PairIds.getElem_idxOf_getElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.getElem_idxOf_getElem

/-- info: 'STACS2027.RAM.PairIds.eraseDups_take_succ'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.eraseDups_take_succ'

/-- info: 'STACS2027.RAM.PairIds.eraseDups_take_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.eraseDups_take_succ

/-- info: 'STACS2027.RAM.PairIds.eraseDups_take_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.eraseDups_take_prefix

/-- info: 'STACS2027.RAM.PairIds.idxOf_eraseDups_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.idxOf_eraseDups_of_not_mem

/-- info: 'STACS2027.RAM.PairIds.idxOf_eraseDups_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.idxOf_eraseDups_lt

/-- info: 'STACS2027.RAM.PairIds.pr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pr

/-- info: 'STACS2027.RAM.PairIds.pr_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pr_eq

/-- info: 'STACS2027.RAM.PairIds.getD_map_fst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.getD_map_fst

/-- info: 'STACS2027.RAM.PairIds.getD_map_snd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.getD_map_snd

/-- info: 'STACS2027.RAM.PairIds.GS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.GS

/-- info: 'STACS2027.RAM.PairIds.gs0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.gs0

/-- info: 'STACS2027.RAM.PairIds.gstep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.gstep

/-- info: 'STACS2027.RAM.PairIds.grun' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.grun

/-- info: 'STACS2027.RAM.PairIds.grun_append_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.grun_append_singleton

/-- info: 'STACS2027.RAM.PairIds.GInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.GInv

/-- info: 'STACS2027.RAM.PairIds.ginv_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.ginv_nil

/-- info: 'STACS2027.RAM.PairIds.GInv.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.GInv.step

/-- info: 'STACS2027.RAM.PairIds.KeyLt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.KeyLt

/-- info: 'STACS2027.RAM.PairIds.pairwise_bkt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairwise_bkt

/-- info: 'STACS2027.RAM.PairIds.pairwise_bucketIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairwise_bucketIdx

/-- info: 'STACS2027.RAM.PairIds.mem_bucketIdx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.mem_bucketIdx

/-- info: 'STACS2027.RAM.PairIds.keyLt_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.keyLt_split

/-- info: 'STACS2027.RAM.PairIds.keyLt_irrefl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.keyLt_irrefl

/-- info: 'STACS2027.RAM.PairIds.ordOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.ordOf

/-- info: 'STACS2027.RAM.PairIds.pairwise_ordOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.pairwise_ordOf

/-- info: 'STACS2027.RAM.PairIds.lt_of_mem_ordOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.lt_of_mem_ordOf

/-- info: 'STACS2027.RAM.PairIds.length_ordOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.length_ordOf

/-- info: 'STACS2027.RAM.PairIds.mem_ordOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.mem_ordOf

/-- info: 'STACS2027.RAM.PairIds.grun_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.grun_take_succ

/-- info: 'STACS2027.RAM.PairIds.ginv_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.ginv_take

/-- info: 'STACS2027.RAM.PairIds.grun_lead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PairIds.grun_lead

/-- info: 'STACS2027.RAM.P1.poly1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.poly1

/-- info: 'STACS2027.RAM.P1.CP1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.CP1

/-- info: 'STACS2027.RAM.P1.W1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.W1

/-- info: 'STACS2027.RAM.P1.W1_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.W1_eq

/-- info: 'STACS2027.RAM.P1.mem_W1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.mem_W1

/-- info: 'STACS2027.RAM.P1.not_mem_W1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.not_mem_W1

/-- info: 'STACS2027.RAM.P1.Allowed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Allowed

/-- info: 'STACS2027.RAM.P1.poly1_wregs'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.poly1_wregs'

/-- info: 'STACS2027.RAM.P1.poly1_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.poly1_wregs

/-- info: 'STACS2027.RAM.P1.poly1_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.poly1_writes

/-- info: 'STACS2027.RAM.P1.MP1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.MP1

/-- info: 'STACS2027.RAM.P1.poly1_HG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.poly1_HG

/-- info: 'STACS2027.RAM.P1.poly1_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.poly1_specB

/-- info: 'STACS2027.RAM.P1.rL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rL

/-- info: 'STACS2027.RAM.P1.rASRC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rASRC

/-- info: 'STACS2027.RAM.P1.rATGT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rATGT
