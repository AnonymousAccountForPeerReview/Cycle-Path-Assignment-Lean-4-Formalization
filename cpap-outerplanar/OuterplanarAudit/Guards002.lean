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

/-- info: 'STACS2027.RAM.P1.rS1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rS1

/-- info: 'STACS2027.RAM.P1.rT1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rT1

/-- info: 'STACS2027.RAM.P1.rOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rOFF

/-- info: 'STACS2027.RAM.P1.rNB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rNB

/-- info: 'STACS2027.RAM.P1.rAI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rAI

/-- info: 'STACS2027.RAM.P1.rAX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rAX

/-- info: 'STACS2027.RAM.P1.rAY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rAY

/-- info: 'STACS2027.RAM.P1.rAZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rAZ

/-- info: 'STACS2027.RAM.P1.arcInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arcInit

/-- info: 'STACS2027.RAM.P1.arcBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arcBody

/-- info: 'STACS2027.RAM.P1.arcStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arcStep

/-- info: 'STACS2027.RAM.P1.sort1Args' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sort1Args

/-- info: 'STACS2027.RAM.P1.sort1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sort1

/-- info: 'STACS2027.RAM.P1.gath1Args' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gath1Args

/-- info: 'STACS2027.RAM.P1.gath1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gath1

/-- info: 'STACS2027.RAM.P1.gath2Args' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gath2Args

/-- info: 'STACS2027.RAM.P1.gath2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gath2

/-- info: 'STACS2027.RAM.P1.sort2Args' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sort2Args

/-- info: 'STACS2027.RAM.P1.sort2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sort2

/-- info: 'STACS2027.RAM.P1.gath3Args' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gath3Args

/-- info: 'STACS2027.RAM.P1.gath3Res' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gath3Res

/-- info: 'STACS2027.RAM.P1.gath3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gath3

/-- info: 'STACS2027.RAM.P1.stageA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageA

/-- info: 'STACS2027.RAM.P1.WA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.WA

/-- info: 'STACS2027.RAM.P1.Zf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Zf

/-- info: 'STACS2027.RAM.P1.ArcSt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.ArcSt

/-- info: 'STACS2027.RAM.P1.Csr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Csr

/-- info: 'STACS2027.RAM.P1.stable_arcSt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stable_arcSt

/-- info: 'STACS2027.RAM.P1.stable_csOut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stable_csOut

/-- info: 'STACS2027.RAM.P1.stable_csr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stable_csr

/-- info: 'STACS2027.RAM.P1.grow_movs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.grow_movs

/-- info: 'STACS2027.RAM.P1.movs_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.movs_mem

/-- info: 'STACS2027.RAM.P1.ArcMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.ArcMem

/-- info: 'STACS2027.RAM.P1.ArcInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.ArcInv

/-- info: 'STACS2027.RAM.P1.take_succ_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.take_succ_map

/-- info: 'STACS2027.RAM.P1.ArcMem.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.ArcMem.step

/-- info: 'STACS2027.RAM.P1.arcBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arcBody_spec

/-- info: 'STACS2027.RAM.P1.arcInit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arcInit_spec

/-- info: 'STACS2027.RAM.P1.arcStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arcStep_spec

/-- info: 'STACS2027.RAM.P1.keys_arcs_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.keys_arcs_lt

/-- info: 'STACS2027.RAM.P1.keys_arcs1_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.keys_arcs1_lt

/-- info: 'STACS2027.RAM.P1.length_bucketIdx_arcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_bucketIdx_arcs

/-- info: 'STACS2027.RAM.P1.length_bucketIdx_arcs1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_bucketIdx_arcs1

/-- info: 'STACS2027.RAM.P1.sort1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sort1_spec

/-- info: 'STACS2027.RAM.P1.idx1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.idx1

/-- info: 'STACS2027.RAM.P1.idx2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.idx2

/-- info: 'STACS2027.RAM.P1.gath1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gath1_spec

/-- info: 'STACS2027.RAM.P1.gath2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gath2_spec

/-- info: 'STACS2027.RAM.P1.sort2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sort2_spec

/-- info: 'STACS2027.RAM.P1.gath3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gath3_spec

/-- info: 'STACS2027.RAM.P1.stageA_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageA_spec

/-- info: 'STACS2027.RAM.P1.rSEA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSEA

/-- info: 'STACS2027.RAM.P1.rSEB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSEB

/-- info: 'STACS2027.RAM.P1.rSEP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSEP

/-- info: 'STACS2027.RAM.P1.rLSEG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rLSEG

/-- info: 'STACS2027.RAM.P1.rSEK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSEK

/-- info: 'STACS2027.RAM.P1.rLAST' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rLAST

/-- info: 'STACS2027.RAM.P1.rEA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rEA

/-- info: 'STACS2027.RAM.P1.rELo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rELo

/-- info: 'STACS2027.RAM.P1.rEHi' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rEHi

/-- info: 'STACS2027.RAM.P1.rEPrev' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rEPrev

/-- info: 'STACS2027.RAM.P1.rEA2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rEA2

/-- info: 'STACS2027.RAM.P1.rEJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rEJ

/-- info: 'STACS2027.RAM.P1.rEB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rEB

/-- info: 'STACS2027.RAM.P1.rEX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rEX

/-- info: 'STACS2027.RAM.P1.rEA1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rEA1

/-- info: 'STACS2027.RAM.P1.enAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enAlloc

/-- info: 'STACS2027.RAM.P1.enPush' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enPush

/-- info: 'STACS2027.RAM.P1.enInner' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enInner

/-- info: 'STACS2027.RAM.P1.enPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enPre

/-- info: 'STACS2027.RAM.P1.enLseg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enLseg

/-- info: 'STACS2027.RAM.P1.enPost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enPost

/-- info: 'STACS2027.RAM.P1.enOuter' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enOuter

/-- info: 'STACS2027.RAM.P1.stageB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageB

/-- info: 'STACS2027.RAM.P1.enEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enEnd

/-- info: 'STACS2027.RAM.P1.WB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.WB

/-- info: 'STACS2027.RAM.P1.EnumSt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.EnumSt

/-- info: 'STACS2027.RAM.P1.stable_enumSt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stable_enumSt

/-- info: 'STACS2027.RAM.P1.EnGlob' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.EnGlob

/-- info: 'STACS2027.RAM.P1.EnMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.EnMem

/-- info: 'STACS2027.RAM.P1.EnSt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.EnSt

/-- info: 'STACS2027.RAM.P1.EnMem.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.EnMem.push

/-- info: 'STACS2027.RAM.P1.EnSt.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.EnSt.indep

/-- info: 'STACS2027.RAM.P1.enPush_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enPush_run

/-- info: 'STACS2027.RAM.P1.InInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.InInv

/-- info: 'STACS2027.RAM.P1.arr_nbP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arr_nbP

/-- info: 'STACS2027.RAM.P1.length_enumPre_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_enumPre_lt

/-- info: 'STACS2027.RAM.P1.nbOff_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.nbOff_mono

/-- info: 'STACS2027.RAM.P1.enInner_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enInner_spec

/-- info: 'STACS2027.RAM.P1.OutInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.OutInv

/-- info: 'STACS2027.RAM.P1.nbOff_le_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.nbOff_le_succ

/-- info: 'STACS2027.RAM.P1.enOuter_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enOuter_spec

/-- info: 'STACS2027.RAM.P1.enAlloc_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enAlloc_spec

/-- info: 'STACS2027.RAM.P1.stageB_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageB_core

/-- info: 'STACS2027.RAM.P1.stageB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageB_spec

/-- info: 'STACS2027.RAM.P1.rFT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rFT

/-- info: 'STACS2027.RAM.P1.rFA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rFA

/-- info: 'STACS2027.RAM.P1.rFB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rFB

/-- info: 'STACS2027.RAM.P1.rFX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rFX

/-- info: 'STACS2027.RAM.P1.rFI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rFI

/-- info: 'STACS2027.RAM.P1.rFD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rFD

/-- info: 'STACS2027.RAM.P1.rFN1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rFN1

/-- info: 'STACS2027.RAM.P1.push' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.push

/-- info: 'STACS2027.RAM.P1.addrOK_push' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.addrOK_push

/-- info: 'STACS2027.RAM.P1.faInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faInit

/-- info: 'STACS2027.RAM.P1.faRd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faRd

/-- info: 'STACS2027.RAM.P1.faOff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faOff

/-- info: 'STACS2027.RAM.P1.faPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faPre

/-- info: 'STACS2027.RAM.P1.faCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faCond

/-- info: 'STACS2027.RAM.P1.faStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faStep

/-- info: 'STACS2027.RAM.P1.faBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faBody

/-- info: 'STACS2027.RAM.P1.faFin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faFin

/-- info: 'STACS2027.RAM.P1.stageE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageE

/-- info: 'STACS2027.RAM.P1.WE' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.WE

/-- info: 'STACS2027.RAM.P1.FaceSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FaceSt

/-- info: 'STACS2027.RAM.P1.stable_faceSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stable_faceSt

/-- info: 'STACS2027.RAM.P1.walkTo_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.walkTo_self

/-- info: 'STACS2027.RAM.P1.walk_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.walk_start

/-- info: 'STACS2027.RAM.P1.walk_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.walk_step

/-- info: 'STACS2027.RAM.P1.walk_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.walk_done

/-- info: 'STACS2027.RAM.P1.walk_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.walk_mem

/-- info: 'STACS2027.RAM.P1.length_walk_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_walk_lt

/-- info: 'STACS2027.RAM.P1.doneOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.doneOf

/-- info: 'STACS2027.RAM.P1.length_doneOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_doneOf

/-- info: 'STACS2027.RAM.P1.doneOf_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.doneOf_succ

/-- info: 'STACS2027.RAM.P1.FaSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FaSt

/-- info: 'STACS2027.RAM.P1.FaSt.indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FaSt.indep

/-- info: 'STACS2027.RAM.P1.push_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.push_run

/-- info: 'STACS2027.RAM.P1.faEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faEnd

/-- info: 'STACS2027.RAM.P1.faPre_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faPre_spec

/-- info: 'STACS2027.RAM.P1.WInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.WInv

/-- info: 'STACS2027.RAM.P1.wMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.wMu

/-- info: 'STACS2027.RAM.P1.faCond_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faCond_run

/-- info: 'STACS2027.RAM.P1.walk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.walk_spec

/-- info: 'STACS2027.RAM.P1.faBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faBody_spec

/-- info: 'STACS2027.RAM.P1.FaIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FaIn

/-- info: 'STACS2027.RAM.P1.faInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faInit_spec

/-- info: 'STACS2027.RAM.P1.stageE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageE_spec

/-- info: 'STACS2027.RAM.P1.HTB.grow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HTB.grow

/-- info: 'STACS2027.RAM.P1.Grow.agree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Grow.agree

/-- info: 'STACS2027.RAM.P1.HGB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB

/-- info: 'STACS2027.RAM.P1.HGB.toHTB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.toHTB

/-- info: 'STACS2027.RAM.P1.HGB.seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.seq

/-- info: 'STACS2027.RAM.P1.HGB.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.mono

/-- info: 'STACS2027.RAM.P1.HGB.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.weaken

/-- info: 'STACS2027.RAM.P1.HGB.post' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.post

/-- info: 'STACS2027.RAM.P1.HGB.pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.pre

/-- info: 'STACS2027.RAM.P1.HGB.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.frame

/-- info: 'STACS2027.RAM.P1.HGB.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.run

/-- info: 'STACS2027.RAM.P1.HGB.runG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.runG

/-- info: 'STACS2027.RAM.P1.HGB.runR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.runR

/-- info: 'STACS2027.RAM.P1.HGB.runM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.runM

/-- info: 'STACS2027.RAM.P1.HGB.ofGhost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.ofGhost

/-- info: 'STACS2027.RAM.P1.HGB.of_pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.of_pre

/-- info: 'STACS2027.RAM.P1.HGB.ghost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.ghost

/-- info: 'STACS2027.RAM.P1.HGB.exists_pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.exists_pre

/-- info: 'STACS2027.RAM.P1.HGB.ifz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.ifz

/-- info: 'STACS2027.RAM.P1.HGB.skip'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.skip'

/-- info: 'STACS2027.RAM.P1.HGB.forUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.forUp

/-- info: 'STACS2027.RAM.P1.HGB.forUpC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.forUpC

/-- info: 'STACS2027.RAM.P1.HGB.forUpCle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGB.forUpCle

/-- info: 'STACS2027.RAM.P1.HGMB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB

/-- info: 'STACS2027.RAM.P1.HGMB.bound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.bound

/-- info: 'STACS2027.RAM.P1.HGMB.seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.seq

/-- info: 'STACS2027.RAM.P1.HGMB.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.mono

/-- info: 'STACS2027.RAM.P1.HGMB.weaken' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.weaken

/-- info: 'STACS2027.RAM.P1.HGMB.pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.pre

/-- info: 'STACS2027.RAM.P1.HGMB.post' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.post

/-- info: 'STACS2027.RAM.P1.HGMB.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.frame

/-- info: 'STACS2027.RAM.P1.HGMB.zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.zero

/-- info: 'STACS2027.RAM.P1.HGMB.zeroRun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.zeroRun

/-- info: 'STACS2027.RAM.P1.HGMB.ofGhost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.ofGhost

/-- info: 'STACS2027.RAM.P1.HGMB.ofHG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.ofHG

/-- info: 'STACS2027.RAM.P1.HGMB.ghost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.ghost

/-- info: 'STACS2027.RAM.P1.HGMB.of_pre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HGMB.of_pre

/-- info: 'STACS2027.RAM.P1.csort_specMB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csort_specMB

/-- info: 'STACS2027.RAM.P1.gaBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gaBody_spec

/-- info: 'STACS2027.RAM.P1.gather_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gather_spec

/-- info: 'STACS2027.RAM.P1.Grow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Grow

/-- info: 'STACS2027.RAM.P1.Grow.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Grow.refl

/-- info: 'STACS2027.RAM.P1.Grow.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Grow.mono

/-- info: 'STACS2027.RAM.P1.Grow.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Grow.trans

/-- info: 'STACS2027.RAM.P1.Grow.sameOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Grow.sameOn

/-- info: 'STACS2027.RAM.P1.Grow.le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Grow.le

/-- info: 'STACS2027.RAM.P1.Grow.arr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Grow.arr

/-- info: 'STACS2027.RAM.P1.Grow.tab' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Grow.tab

/-- info: 'STACS2027.RAM.P1.Grow.arr'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Grow.arr'

/-- info: 'STACS2027.RAM.P1.HT.grow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HT.grow

/-- info: 'STACS2027.RAM.P1.grow_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.grow_run

/-- info: 'STACS2027.RAM.P1.HG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HG

/-- info: 'STACS2027.RAM.P1.HG.ofGhost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HG.ofGhost

/-- info: 'STACS2027.RAM.P1.ArrAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.ArrAt

/-- info: 'STACS2027.RAM.P1.TabAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.TabAt

/-- info: 'STACS2027.RAM.P1.Stable' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Stable

/-- info: 'STACS2027.RAM.P1.Stable.and' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Stable.and

/-- info: 'STACS2027.RAM.P1.Stable.of_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Stable.of_iff

/-- info: 'STACS2027.RAM.P1.Stable.const' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Stable.const

/-- info: 'STACS2027.RAM.P1.Stable.reg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Stable.reg

/-- info: 'STACS2027.RAM.P1.Stable.regEq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Stable.regEq

/-- info: 'STACS2027.RAM.P1.Stable.arrAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Stable.arrAt

/-- info: 'STACS2027.RAM.P1.Stable.tabAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Stable.tabAt

/-- info: 'STACS2027.RAM.P1.Stable.sameOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.Stable.sameOn

/-- info: 'STACS2027.RAM.P1.ArrAt.of_reg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.ArrAt.of_reg

/-- info: 'STACS2027.RAM.P1.TabAt.of_reg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.TabAt.of_reg

/-- info: 'STACS2027.RAM.P1.partOff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.partOff

/-- info: 'STACS2027.RAM.P1.partOff_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.partOff_succ

/-- info: 'STACS2027.RAM.P1.length_flatMap_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_flatMap_range

/-- info: 'STACS2027.RAM.P1.arr_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arr_flatMap

/-- info: 'STACS2027.RAM.P1.arr_flatMap_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arr_flatMap_get

/-- info: 'STACS2027.RAM.P1.rGI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rGI

/-- info: 'STACS2027.RAM.P1.rGF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rGF

/-- info: 'STACS2027.RAM.P1.rGL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rGL

/-- info: 'STACS2027.RAM.P1.rGO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rGO

/-- info: 'STACS2027.RAM.P1.rGJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rGJ

/-- info: 'STACS2027.RAM.P1.rGX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rGX

/-- info: 'STACS2027.RAM.P1.gaBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gaBody

/-- info: 'STACS2027.RAM.P1.gather' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gather

/-- info: 'STACS2027.RAM.P1.GaIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.GaIn

/-- info: 'STACS2027.RAM.P1.GaInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.GaInv

/-- info: 'STACS2027.RAM.P1.rORD3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rORD3

/-- info: 'STACS2027.RAM.P1.rPOS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rPOS

/-- info: 'STACS2027.RAM.P1.rDT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rDT

/-- info: 'STACS2027.RAM.P1.rDX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rDX

/-- info: 'STACS2027.RAM.P1.rDY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rDY

/-- info: 'STACS2027.RAM.P1.sort3Args' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sort3Args

/-- info: 'STACS2027.RAM.P1.sort3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sort3

/-- info: 'STACS2027.RAM.P1.gathAArgs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gathAArgs

/-- info: 'STACS2027.RAM.P1.gathA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gathA

/-- info: 'STACS2027.RAM.P1.gathBArgs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gathBArgs

/-- info: 'STACS2027.RAM.P1.gathB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gathB

/-- info: 'STACS2027.RAM.P1.stageC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageC

/-- info: 'STACS2027.RAM.P1.posBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posBody

/-- info: 'STACS2027.RAM.P1.posAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posAlloc

/-- info: 'STACS2027.RAM.P1.stageD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageD

/-- info: 'STACS2027.RAM.P1.WC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.WC

/-- info: 'STACS2027.RAM.P1.WD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.WD

/-- info: 'STACS2027.RAM.P1.ord3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.ord3

/-- info: 'STACS2027.RAM.P1.keys_size_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.keys_size_lt

/-- info: 'STACS2027.RAM.P1.length_ord3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_ord3

/-- info: 'STACS2027.RAM.P1.lt_of_mem_ord3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.lt_of_mem_ord3

/-- info: 'STACS2027.RAM.P1.getD_ord3_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.getD_ord3_mem

/-- info: 'STACS2027.RAM.P1.mem_ord3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.mem_ord3

/-- info: 'STACS2027.RAM.P1.getD_ord3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.getD_ord3

/-- info: 'STACS2027.RAM.P1.getD_segEnum_ord3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.getD_segEnum_ord3

/-- info: 'STACS2027.RAM.P1.posId_ord3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posId_ord3

/-- info: 'STACS2027.RAM.P1.OrdSt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.OrdSt

/-- info: 'STACS2027.RAM.P1.stable_ordSt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stable_ordSt

/-- info: 'STACS2027.RAM.P1.sort3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sort3_spec

/-- info: 'STACS2027.RAM.P1.gathA_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gathA_spec

/-- info: 'STACS2027.RAM.P1.gathB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.gathB_spec

/-- info: 'STACS2027.RAM.P1.stageC_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageC_spec

/-- info: 'STACS2027.RAM.P1.posPart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posPart

/-- info: 'STACS2027.RAM.P1.posPart_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posPart_zero

/-- info: 'STACS2027.RAM.P1.posPart_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posPart_succ

/-- info: 'STACS2027.RAM.P1.posPart_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posPart_full

/-- info: 'STACS2027.RAM.P1.PosSt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.PosSt

/-- info: 'STACS2027.RAM.P1.PosInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.PosInv

/-- info: 'STACS2027.RAM.P1.posBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posBody_spec

/-- info: 'STACS2027.RAM.P1.stageD_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageD_core

/-- info: 'STACS2027.RAM.P1.stageD_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageD_spec

/-- info: 'STACS2027.RAM.P1.rST' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rST

/-- info: 'STACS2027.RAM.P1.rSA0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSA0

/-- info: 'STACS2027.RAM.P1.rSE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSE

/-- info: 'STACS2027.RAM.P1.rSP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSP

/-- info: 'STACS2027.RAM.P1.rSO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSO

/-- info: 'STACS2027.RAM.P1.rSQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSQ

/-- info: 'STACS2027.RAM.P1.rSH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSH

/-- info: 'STACS2027.RAM.P1.rSX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSX

/-- info: 'STACS2027.RAM.P1.rSL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSL

/-- info: 'STACS2027.RAM.P1.rSN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSN

/-- info: 'STACS2027.RAM.P1.rSA2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rSA2

/-- info: 'STACS2027.RAM.P1.fsAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsAlloc

/-- info: 'STACS2027.RAM.P1.fsHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsHead

/-- info: 'STACS2027.RAM.P1.fsFirst' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsFirst

/-- info: 'STACS2027.RAM.P1.fsMid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsMid

/-- info: 'STACS2027.RAM.P1.fsBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsBody

/-- info: 'STACS2027.RAM.P1.stageF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageF

/-- info: 'STACS2027.RAM.P1.WF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.WF

/-- info: 'STACS2027.RAM.P1.SlotSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.SlotSt

/-- info: 'STACS2027.RAM.P1.arr_segOrder_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arr_segOrder_part

/-- info: 'STACS2027.RAM.P1.faceOffs_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faceOffs_get

/-- info: 'STACS2027.RAM.P1.faceSids_take_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faceSids_take_succ

/-- info: 'STACS2027.RAM.P1.faceSids_eq_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faceSids_eq_last

/-- info: 'STACS2027.RAM.P1.enumId_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enumId_le

/-- info: 'STACS2027.RAM.P1.FsCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FsCtx

/-- info: 'STACS2027.RAM.P1.FsSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FsSt

/-- info: 'STACS2027.RAM.P1.FsSt.indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FsSt.indep

/-- info: 'STACS2027.RAM.P1.FsSt.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FsSt.push

/-- info: 'STACS2027.RAM.P1.FsSt.rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FsSt.rd

/-- info: 'STACS2027.RAM.P1.HeadR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.HeadR

/-- info: 'STACS2027.RAM.P1.fsHead_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsHead_spec

/-- info: 'STACS2027.RAM.P1.fsFirst_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsFirst_spec

/-- info: 'STACS2027.RAM.P1.MidInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.MidInv

/-- info: 'STACS2027.RAM.P1.fsMid_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsMid_spec

/-- info: 'STACS2027.RAM.P1.tFs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.tFs

/-- info: 'STACS2027.RAM.P1.fsBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsBody_spec

/-- info: 'STACS2027.RAM.P1.FsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FsIn

/-- info: 'STACS2027.RAM.P1.fsAlloc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsAlloc_spec

/-- info: 'STACS2027.RAM.P1.stageF_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageF_core

/-- info: 'STACS2027.RAM.P1.stageF_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.stageF_spec

/-- info: 'STACS2027.RAM.P1.rKB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rKB

/-- info: 'STACS2027.RAM.P1.rKL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rKL

/-- info: 'STACS2027.RAM.P1.rKN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rKN

/-- info: 'STACS2027.RAM.P1.rKO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rKO

/-- info: 'STACS2027.RAM.P1.rKF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rKF

/-- info: 'STACS2027.RAM.P1.rKP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rKP

/-- info: 'STACS2027.RAM.P1.rKI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rKI

/-- info: 'STACS2027.RAM.P1.rKX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rKX

/-- info: 'STACS2027.RAM.P1.rKY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rKY

/-- info: 'STACS2027.RAM.P1.rKZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.rKZ

/-- info: 'STACS2027.RAM.P1.csInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csInit

/-- info: 'STACS2027.RAM.P1.csCount' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csCount

/-- info: 'STACS2027.RAM.P1.csPrefix' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csPrefix

/-- info: 'STACS2027.RAM.P1.csFill' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csFill

/-- info: 'STACS2027.RAM.P1.csort' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csort

/-- info: 'STACS2027.RAM.P1.CsIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.CsIn

/-- info: 'STACS2027.RAM.P1.CsOut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.CsOut

/-- info: 'STACS2027.RAM.P1.CsGlob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.CsGlob

/-- info: 'STACS2027.RAM.P1.CsBase' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.CsBase

/-- info: 'STACS2027.RAM.P1.CsBase.upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.CsBase.upd

/-- info: 'STACS2027.RAM.P1.key_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.key_lt

/-- info: 'STACS2027.RAM.P1.CntInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.CntInv

/-- info: 'STACS2027.RAM.P1.cntS_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.cntS_succ

/-- info: 'STACS2027.RAM.P1.csCount_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csCount_spec

/-- info: 'STACS2027.RAM.P1.preF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.preF

/-- info: 'STACS2027.RAM.P1.PreInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.PreInv

/-- info: 'STACS2027.RAM.P1.preF_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.preF_succ

/-- info: 'STACS2027.RAM.P1.csPrefix_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csPrefix_spec

/-- info: 'STACS2027.RAM.P1.FillInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.FillInv

/-- info: 'STACS2027.RAM.P1.csFill_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csFill_spec

/-- info: 'STACS2027.RAM.P1.csInit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csInit_spec

/-- info: 'STACS2027.RAM.P1.csCountLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csCountLoop_spec

/-- info: 'STACS2027.RAM.P1.csPrefixLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csPrefixLoop_spec

/-- info: 'STACS2027.RAM.P1.csFillLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csFillLoop_spec

/-- info: 'STACS2027.RAM.P1.csort_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csort_specB

/-- info: 'STACS2027.RAM.P1.csort_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.csort_spec

/-- info: 'STACS2027.RAM.P1.arcs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arcs

/-- info: 'STACS2027.RAM.P1.arcs1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arcs1

/-- info: 'STACS2027.RAM.P1.nbCat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.nbCat

/-- info: 'STACS2027.RAM.P1.nbOff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.nbOff

/-- info: 'STACS2027.RAM.P1.length_arcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_arcs

/-- info: 'STACS2027.RAM.P1.mem_arcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.mem_arcs

/-- info: 'STACS2027.RAM.P1.mem_arcs_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.mem_arcs_iff

/-- info: 'STACS2027.RAM.P1.arcs_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.arcs_nodup

/-- info: 'STACS2027.RAM.P1.lt_of_mem_arcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.lt_of_mem_arcs

/-- info: 'STACS2027.RAM.P1.flatMap_ite_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.flatMap_ite_singleton

/-- info: 'STACS2027.RAM.P1.map_snd_filter_arcs1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.map_snd_filter_arcs1

/-- info: 'STACS2027.RAM.P1.map_bucketIdx_arcs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.map_bucketIdx_arcs

/-- info: 'STACS2027.RAM.P1.length_arcs1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_arcs1

/-- info: 'STACS2027.RAM.P1.mem_arcs_of_mem_arcs1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.mem_arcs_of_mem_arcs1

/-- info: 'STACS2027.RAM.P1.map_bucketIdx_arcs1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.map_bucketIdx_arcs1

/-- info: 'STACS2027.RAM.P1.length_bkt_arcs1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_bkt_arcs1

/-- info: 'STACS2027.RAM.P1.offOf_arcs1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.offOf_arcs1

/-- info: 'STACS2027.RAM.P1.length_nbCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_nbCat

/-- info: 'STACS2027.RAM.P1.nbOff_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.nbOff_succ

/-- info: 'STACS2027.RAM.P1.nbOff_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.nbOff_eq

/-- info: 'STACS2027.RAM.P1.segsOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.segsOf

/-- info: 'STACS2027.RAM.P1.enumPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enumPre

/-- info: 'STACS2027.RAM.P1.predOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.predOf

/-- info: 'STACS2027.RAM.P1.cellOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.cellOf

/-- info: 'STACS2027.RAM.P1.sizeOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sizeOf

/-- info: 'STACS2027.RAM.P1.segEnum_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.segEnum_eq

/-- info: 'STACS2027.RAM.P1.segsOf_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.segsOf_nil

/-- info: 'STACS2027.RAM.P1.segsOf_snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.segsOf_snoc

/-- info: 'STACS2027.RAM.P1.enumPre_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enumPre_snoc

/-- info: 'STACS2027.RAM.P1.enumPre_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enumPre_zero

/-- info: 'STACS2027.RAM.P1.enumPre_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enumPre_succ

/-- info: 'STACS2027.RAM.P1.enumPre_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enumPre_full

/-- info: 'STACS2027.RAM.P1.enumPre_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enumPre_prefix

/-- info: 'STACS2027.RAM.P1.mem_pg_of_mem_segEnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.mem_pg_of_mem_segEnum

/-- info: 'STACS2027.RAM.P1.length_segEnum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_segEnum_le

/-- info: 'STACS2027.RAM.P1.lt_of_mem_segEnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.lt_of_mem_segEnum

/-- info: 'STACS2027.RAM.P1.map_bucketIdx_segEnum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.map_bucketIdx_segEnum

/-- info: 'STACS2027.RAM.P1.sizeOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sizeOf_lt

/-- info: 'STACS2027.RAM.P1.length_segOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_segOrder

/-- info: 'STACS2027.RAM.P1.filter_lt_getElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.filter_lt_getElem

/-- info: 'STACS2027.RAM.P1.predNb_getElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.predNb_getElem

/-- info: 'STACS2027.RAM.P1.getLastD_take_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.getLastD_take_succ

/-- info: 'STACS2027.RAM.P1.idxOf_append_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.idxOf_append_singleton

/-- info: 'STACS2027.RAM.P1.lt_of_mem_segOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.lt_of_mem_segOrder

/-- info: 'STACS2027.RAM.P1.take_succ_segOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.take_succ_segOrder

/-- info: 'STACS2027.RAM.P1.getElem_segOrder_not_mem_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.getElem_segOrder_not_mem_take

/-- info: 'STACS2027.RAM.P1.mem_segOrder_iff_segEnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.mem_segOrder_iff_segEnum

/-- info: 'STACS2027.RAM.P1.enumId' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enumId

/-- info: 'STACS2027.RAM.P1.posId' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posId

/-- info: 'STACS2027.RAM.P1.segId_of_not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.segId_of_not_mem

/-- info: 'STACS2027.RAM.P1.segId_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.segId_of_mem

/-- info: 'STACS2027.RAM.P1.segId_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.segId_of_lt

/-- info: 'STACS2027.RAM.P1.segId_getElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.segId_getElem

/-- info: 'STACS2027.RAM.P1.posId_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posId_zero

/-- info: 'STACS2027.RAM.P1.posId_enumId' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.posId_enumId

/-- info: 'STACS2027.RAM.P1.idxOf_segEnum_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.idxOf_segEnum_of_prefix

/-- info: 'STACS2027.RAM.P1.enumId_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enumId_last

/-- info: 'STACS2027.RAM.P1.enumId_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.enumId_pred

/-- info: 'STACS2027.RAM.P1.infix_getElem_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.infix_getElem_pair

/-- info: 'STACS2027.RAM.P1.faceVerts_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faceVerts_start

/-- info: 'STACS2027.RAM.P1.faceVerts_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.faceVerts_next

/-- info: 'STACS2027.RAM.P1.segId_last_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.segId_last_slot

/-- info: 'STACS2027.RAM.P1.length_faceSids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_faceSids

/-- info: 'STACS2027.RAM.P1.length_fsidCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_fsidCat

/-- info: 'STACS2027.RAM.P1.fOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fOff

/-- info: 'STACS2027.RAM.P1.fOff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fOff_zero

/-- info: 'STACS2027.RAM.P1.fOff_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fOff_succ

/-- info: 'STACS2027.RAM.P1.fOff_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fOff_full

/-- info: 'STACS2027.RAM.P1.fOff_le_faceCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fOff_le_faceCat

/-- info: 'STACS2027.RAM.P1.map_fOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.map_fOff

/-- info: 'STACS2027.RAM.P1.length_pairs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_pairs

/-- info: 'STACS2027.RAM.P1.slot_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.slot_unique

/-- info: 'STACS2027.RAM.P1.slotsCat_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.slotsCat_nodup

/-- info: 'STACS2027.RAM.P1.length_faceCat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_faceCat_le

/-- info: 'STACS2027.RAM.P1.doneS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.doneS

/-- info: 'STACS2027.RAM.P1.length_doneS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_doneS

/-- info: 'STACS2027.RAM.P1.doneS_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.doneS_succ

/-- info: 'STACS2027.RAM.P1.doneS_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.doneS_full

/-- info: 'STACS2027.RAM.P1.fsidCat_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.fsidCat_getD

/-- info: 'STACS2027.RAM.P2.iA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.iA

/-- info: 'STACS2027.RAM.P2.iB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.iB

/-- info: 'STACS2027.RAM.P2.p2Init' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.p2Init

/-- info: 'STACS2027.RAM.P2.poly2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poly2

/-- info: 'STACS2027.RAM.P2.lay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.lay

/-- info: 'STACS2027.RAM.P2.layOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.layOK

/-- info: 'STACS2027.RAM.P2.IOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.IOut

/-- info: 'STACS2027.RAM.P2.p2Init_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.p2Init_spec

/-- info: 'STACS2027.RAM.P2.P2New' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.P2New

/-- info: 'STACS2027.RAM.P2.T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.T2

/-- info: 'STACS2027.RAM.P2.M2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.M2

/-- info: 'STACS2027.RAM.P2.poly2_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poly2_main

/-- info: 'STACS2027.RAM.P2.CT2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.CT2

/-- info: 'STACS2027.RAM.P2.CM2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.CM2

/-- info: 'STACS2027.RAM.P2.CP2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.CP2

/-- info: 'STACS2027.RAM.P2.length_pool_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_pool_le

/-- info: 'STACS2027.RAM.P2.flatten_pool_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.flatten_pool_length

/-- info: 'STACS2027.RAM.P2.T2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.T2_le

/-- info: 'STACS2027.RAM.P2.M2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.M2_le

/-- info: 'STACS2027.RAM.P2.poly1Post_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poly1Post_keep

/-- info: 'STACS2027.RAM.P2.wregs_poly2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.wregs_poly2

/-- info: 'STACS2027.RAM.P2.Ok2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Ok2

/-- info: 'STACS2027.RAM.P2.ok_seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.ok_seq

/-- info: 'STACS2027.RAM.P2.ok_forUp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.ok_forUp

/-- info: 'STACS2027.RAM.P2.ok_peBody' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.ok_peBody

/-- info: 'STACS2027.RAM.P2.ok_stageR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.ok_stageR

/-- info: 'STACS2027.RAM.P2.ok_stageP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.ok_stageP

/-- info: 'STACS2027.RAM.P2.ok_stageB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.ok_stageB

/-- info: 'STACS2027.RAM.P2.poly2_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poly2_wregs

/-- info: 'STACS2027.RAM.P2.poly2_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poly2_writes

/-- info: 'STACS2027.RAM.P2.poly2_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poly2_specB

/-- info: 'STACS2027.RAM.P2.rMD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rMD

/-- info: 'STACS2027.RAM.P2.rBI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rBI

/-- info: 'STACS2027.RAM.P2.rBA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rBA

/-- info: 'STACS2027.RAM.P2.rBB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rBB

/-- info: 'STACS2027.RAM.P2.rPC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rPC

/-- info: 'STACS2027.RAM.P2.rU0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rU0

/-- info: 'STACS2027.RAM.P2.rUL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rUL

/-- info: 'STACS2027.RAM.P2.rBX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rBX

/-- info: 'STACS2027.RAM.P2.rBY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rBY

/-- info: 'STACS2027.RAM.P2.rBW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rBW

/-- info: 'STACS2027.RAM.P2.rBW2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rBW2

/-- info: 'STACS2027.RAM.P2.bRd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bRd

/-- info: 'STACS2027.RAM.P2.bTop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bTop

/-- info: 'STACS2027.RAM.P2.bPush' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bPush

/-- info: 'STACS2027.RAM.P2.bbBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bbBody

/-- info: 'STACS2027.RAM.P2.bbLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bbLoop

/-- info: 'STACS2027.RAM.P2.baBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.baBody

/-- info: 'STACS2027.RAM.P2.baLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.baLoop

/-- info: 'STACS2027.RAM.P2.biHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.biHead

/-- info: 'STACS2027.RAM.P2.biBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.biBody

/-- info: 'STACS2027.RAM.P2.bscan' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bscan

/-- info: 'STACS2027.RAM.P2.pick' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.pick

/-- info: 'STACS2027.RAM.P2.BCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BCtx

/-- info: 'STACS2027.RAM.P2.BCtx.stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BCtx.stable

/-- info: 'STACS2027.RAM.P2.bel_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bel_cyc

/-- info: 'STACS2027.RAM.P2.topOf_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.topOf_cyc

/-- info: 'STACS2027.RAM.P2.HGB.push'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.HGB.push'

/-- info: 'STACS2027.RAM.P2.length_flatMap_take_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_flatMap_take_le

/-- info: 'STACS2027.RAM.P2.bRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bRow

/-- info: 'STACS2027.RAM.P2.BbF0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BbF0

/-- info: 'STACS2027.RAM.P2.BbFr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BbFr

/-- info: 'STACS2027.RAM.P2.BbF0.stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BbF0.stable

/-- info: 'STACS2027.RAM.P2.BbFr.stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BbFr.stable

/-- info: 'STACS2027.RAM.P2.bbBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bbBody_spec

/-- info: 'STACS2027.RAM.P2.BbInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BbInv

/-- info: 'STACS2027.RAM.P2.bbLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bbLoop_spec

/-- info: 'STACS2027.RAM.P2.bAx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bAx

/-- info: 'STACS2027.RAM.P2.BaInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BaInv

/-- info: 'STACS2027.RAM.P2.baBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.baBody_spec

/-- info: 'STACS2027.RAM.P2.baLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.baLoop_spec

/-- info: 'STACS2027.RAM.P2.BiInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BiInv

/-- info: 'STACS2027.RAM.P2.biBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.biBody_spec

/-- info: 'STACS2027.RAM.P2.trip_len_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.trip_len_le

/-- info: 'STACS2027.RAM.P2.bscan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bscan_spec

/-- info: 'STACS2027.RAM.P2.TBs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.TBs

/-- info: 'STACS2027.RAM.P2.rK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rK

/-- info: 'STACS2027.RAM.P2.rFB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rFB

/-- info: 'STACS2027.RAM.P2.rFC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rFC

/-- info: 'STACS2027.RAM.P2.rKm1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rKm1

/-- info: 'STACS2027.RAM.P2.rY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rY

/-- info: 'STACS2027.RAM.P2.rCB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rCB

/-- info: 'STACS2027.RAM.P2.rCN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rCN

/-- info: 'STACS2027.RAM.P2.rQN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rQN

/-- info: 'STACS2027.RAM.P2.rPP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rPP

/-- info: 'STACS2027.RAM.P2.rE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rE

/-- info: 'STACS2027.RAM.P2.rLN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rLN

/-- info: 'STACS2027.RAM.P2.rL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rL

/-- info: 'STACS2027.RAM.P2.rCP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rCP

/-- info: 'STACS2027.RAM.P2.rCJ2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rCJ2

/-- info: 'STACS2027.RAM.P2.rER' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rER

/-- info: 'STACS2027.RAM.P2.rW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rW

/-- info: 'STACS2027.RAM.P2.rW2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rW2

/-- info: 'STACS2027.RAM.P2.rW3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rW3

/-- info: 'STACS2027.RAM.P2.rPJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rPJ

/-- info: 'STACS2027.RAM.P2.rPN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rPN

/-- info: 'STACS2027.RAM.P2.prepCp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prepCp

/-- info: 'STACS2027.RAM.P2.emCa' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emCa

/-- info: 'STACS2027.RAM.P2.emCb' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emCb

/-- info: 'STACS2027.RAM.P2.emC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emC

/-- info: 'STACS2027.RAM.P2.cTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cTest

/-- info: 'STACS2027.RAM.P2.cAdv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cAdv

/-- info: 'STACS2027.RAM.P2.cBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cBody

/-- info: 'STACS2027.RAM.P2.cLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cLoop

/-- info: 'STACS2027.RAM.P2.lInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.lInit

/-- info: 'STACS2027.RAM.P2.lBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.lBody

/-- info: 'STACS2027.RAM.P2.lLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.lLoop

/-- info: 'STACS2027.RAM.P2.em2a' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.em2a

/-- info: 'STACS2027.RAM.P2.em2b' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.em2b

/-- info: 'STACS2027.RAM.P2.em2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.em2

/-- info: 'STACS2027.RAM.P2.peHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.peHead

/-- info: 'STACS2027.RAM.P2.peMid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.peMid

/-- info: 'STACS2027.RAM.P2.peAdv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.peAdv

/-- info: 'STACS2027.RAM.P2.peBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.peBody

/-- info: 'STACS2027.RAM.P2.peLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.peLoop

/-- info: 'STACS2027.RAM.P2.TC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.TC

/-- info: 'STACS2027.RAM.P2.TL' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.TL

/-- info: 'STACS2027.RAM.P2.TPe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.TPe

/-- info: 'STACS2027.RAM.P2.TPL' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.TPL

/-- info: 'STACS2027.RAM.P2.SCtx' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.SCtx

/-- info: 'STACS2027.RAM.P2.SCtx.stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.SCtx.stable

/-- info: 'STACS2027.RAM.P2.PCtx' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.PCtx

/-- info: 'STACS2027.RAM.P2.PCtx.stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.PCtx.stable

/-- info: 'STACS2027.RAM.P2.Bel.rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Bel.rec

/-- info: 'STACS2027.RAM.P2.Bel.tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Bel.tail

/-- info: 'STACS2027.RAM.P2.enc_flatMap_take_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.enc_flatMap_take_le

/-- info: 'STACS2027.RAM.P2.pushPrep_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.pushPrep_run

/-- info: 'STACS2027.RAM.P2.emC_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emC_spec

/-- info: 'STACS2027.RAM.P2.emJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emJ

/-- info: 'STACS2027.RAM.P2.CInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.CInv

/-- info: 'STACS2027.RAM.P2.CInv.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.CInv.indep

/-- info: 'STACS2027.RAM.P2.emJ_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emJ_zero

/-- info: 'STACS2027.RAM.P2.emJ_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emJ_succ

/-- info: 'STACS2027.RAM.P2.emJ_len_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emJ_len_le

/-- info: 'STACS2027.RAM.P2.cBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cBody_spec

/-- info: 'STACS2027.RAM.P2.cLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cLoop_spec

/-- info: 'STACS2027.RAM.P2.emL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emL

/-- info: 'STACS2027.RAM.P2.LInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.LInv

/-- info: 'STACS2027.RAM.P2.LInv.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.LInv.indep

/-- info: 'STACS2027.RAM.P2.emL_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emL_zero

/-- info: 'STACS2027.RAM.P2.emL_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emL_succ

/-- info: 'STACS2027.RAM.P2.emL_len_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emL_len_le

/-- info: 'STACS2027.RAM.P2.lBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.lBody_spec

/-- info: 'STACS2027.RAM.P2.lLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.lLoop_spec

/-- info: 'STACS2027.RAM.P2.em2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.em2_spec

/-- info: 'STACS2027.RAM.P2.extPe_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.extPe_eq

/-- info: 'STACS2027.RAM.P2.peBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.peBody_spec

/-- info: 'STACS2027.RAM.P2.extJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.extJ

/-- info: 'STACS2027.RAM.P2.extJ_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.extJ_zero

/-- info: 'STACS2027.RAM.P2.PeInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.PeInv

/-- info: 'STACS2027.RAM.P2.peLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.peLoop_spec

/-- info: 'STACS2027.RAM.P2.rGTY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGTY

/-- info: 'STACS2027.RAM.P2.rGOT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGOT

/-- info: 'STACS2027.RAM.P2.rGFT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGFT

/-- info: 'STACS2027.RAM.P2.rGOS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGOS

/-- info: 'STACS2027.RAM.P2.rGFS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGFS

/-- info: 'STACS2027.RAM.P2.rGST' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGST

/-- info: 'STACS2027.RAM.P2.rGSV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGSV

/-- info: 'STACS2027.RAM.P2.rGX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGX

/-- info: 'STACS2027.RAM.P2.rGX1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGX1

/-- info: 'STACS2027.RAM.P2.rGJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGJ

/-- info: 'STACS2027.RAM.P2.rGLo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGLo

/-- info: 'STACS2027.RAM.P2.rGHi' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGHi

/-- info: 'STACS2027.RAM.P2.rGT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGT

/-- info: 'STACS2027.RAM.P2.rGY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGY

/-- info: 'STACS2027.RAM.P2.rGV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rGV

/-- info: 'STACS2027.RAM.P2.gpAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.gpAlloc

/-- info: 'STACS2027.RAM.P2.gpHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.gpHead

/-- info: 'STACS2027.RAM.P2.stBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stBody

/-- info: 'STACS2027.RAM.P2.gpMid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.gpMid

/-- info: 'STACS2027.RAM.P2.scRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.scRead

/-- info: 'STACS2027.RAM.P2.scBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.scBody

/-- info: 'STACS2027.RAM.P2.gpBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.gpBody

/-- info: 'STACS2027.RAM.P2.grpPass' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.grpPass

/-- info: 'STACS2027.RAM.P2.tAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tAll

/-- info: 'STACS2027.RAM.P2.tkeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tkeys

/-- info: 'STACS2027.RAM.P2.skeys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.skeys

/-- info: 'STACS2027.RAM.P2.gS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.gS

/-- info: 'STACS2027.RAM.P2.gT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.gT

/-- info: 'STACS2027.RAM.P2.tGrp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tGrp

/-- info: 'STACS2027.RAM.P2.keysPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.keysPre

/-- info: 'STACS2027.RAM.P2.keysPre_zero_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.keysPre_zero_succ

/-- info: 'STACS2027.RAM.P2.keysPre_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.keysPre_full

/-- info: 'STACS2027.RAM.P2.keysPre_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.keysPre_succ

/-- info: 'STACS2027.RAM.P2.length_keysPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_keysPre

/-- info: 'STACS2027.RAM.P2.gT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.gT_eq

/-- info: 'STACS2027.RAM.P2.length_gT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_gT

/-- info: 'STACS2027.RAM.P2.length_gS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_gS

/-- info: 'STACS2027.RAM.P2.offOf_tkeys_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.offOf_tkeys_succ

/-- info: 'STACS2027.RAM.P2.gS_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.gS_mem

/-- info: 'STACS2027.RAM.P2.gS_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.gS_nodup

/-- info: 'STACS2027.RAM.P2.mem_gS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.mem_gS

/-- info: 'STACS2027.RAM.P2.read_gS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.read_gS

/-- info: 'STACS2027.RAM.P2.read_gT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.read_gT

/-- info: 'STACS2027.RAM.P2.getD_gT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.getD_gT

/-- info: 'STACS2027.RAM.P2.tGrp_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tGrp_mem

/-- info: 'STACS2027.RAM.P2.StA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.StA

/-- info: 'STACS2027.RAM.P2.StB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.StB

/-- info: 'STACS2027.RAM.P2.stA_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stA_zero

/-- info: 'STACS2027.RAM.P2.stB_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stB_zero

/-- info: 'STACS2027.RAM.P2.StA.le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.StA.le

/-- info: 'STACS2027.RAM.P2.StA.upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.StA.upd

/-- info: 'STACS2027.RAM.P2.StB.upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.StB.upd

/-- info: 'STACS2027.RAM.P2.snd_lt_of_gS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.snd_lt_of_gS

/-- info: 'STACS2027.RAM.P2.stamp_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stamp_step

/-- info: 'STACS2027.RAM.P2.key_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.key_eq

/-- info: 'STACS2027.RAM.P2.GPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.GPre

/-- info: 'STACS2027.RAM.P2.GSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.GSt

/-- info: 'STACS2027.RAM.P2.GSt.indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.GSt.indep

/-- info: 'STACS2027.RAM.P2.GSt.rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.GSt.rd

/-- info: 'STACS2027.RAM.P2.offS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.offS

/-- info: 'STACS2027.RAM.P2.offT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.offT

/-- info: 'STACS2027.RAM.P2.OInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.OInv

/-- info: 'STACS2027.RAM.P2.SInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.SInv

/-- info: 'STACS2027.RAM.P2.KInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.KInv

/-- info: 'STACS2027.RAM.P2.GSt.stamp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.GSt.stamp

/-- info: 'STACS2027.RAM.P2.offS_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.offS_le

/-- info: 'STACS2027.RAM.P2.offT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.offT_le

/-- info: 'STACS2027.RAM.P2.stBody_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stBody_run

/-- info: 'STACS2027.RAM.P2.stBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stBody_spec

/-- info: 'STACS2027.RAM.P2.scRead_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.scRead_run

/-- info: 'STACS2027.RAM.P2.scBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.scBody_spec

/-- info: 'STACS2027.RAM.P2.tGp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tGp

/-- info: 'STACS2027.RAM.P2.gpBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.gpBody_spec

/-- info: 'STACS2027.RAM.P2.sum_groups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.sum_groups

/-- info: 'STACS2027.RAM.P2.grpPass_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.grpPass_spec

/-- info: 'STACS2027.RAM.P2.Strm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Strm

/-- info: 'STACS2027.RAM.P2.Bel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Bel

/-- info: 'STACS2027.RAM.P2.stable_bel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stable_bel

/-- info: 'STACS2027.RAM.P2.Strm.bel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Strm.bel

/-- info: 'STACS2027.RAM.P2.Bel.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Bel.mono

/-- info: 'STACS2027.RAM.P2.Bel.sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Bel.sub

/-- info: 'STACS2027.RAM.P2.Bel.get' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Bel.get

/-- info: 'STACS2027.RAM.P2.Bel.cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Bel.cons

/-- info: 'STACS2027.RAM.P2.take_succ_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.take_succ_eq

/-- info: 'STACS2027.RAM.P2.run_push' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.run_push

/-- info: 'STACS2027.RAM.P2.push_strm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.push_strm

/-- info: 'STACS2027.RAM.P2.grow_agree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.grow_agree

/-- info: 'STACS2027.RAM.P2.grow_run_of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.grow_run_of

/-- info: 'STACS2027.RAM.P2.grow_of_agree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.grow_of_agree

/-- info: 'STACS2027.RAM.P2.strm_agree' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.strm_agree

/-- info: 'STACS2027.RAM.P2.push_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.push_grow

/-- info: 'STACS2027.RAM.P2.push_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.push_reg

/-- info: 'STACS2027.RAM.P2.rCS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rCS

/-- info: 'STACS2027.RAM.P2.rCL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rCL

/-- info: 'STACS2027.RAM.P2.rCJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rCJ

/-- info: 'STACS2027.RAM.P2.rCX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rCX

/-- info: 'STACS2027.RAM.P2.cpBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cpBody

/-- info: 'STACS2027.RAM.P2.copy' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.copy

/-- info: 'STACS2027.RAM.P2.CpInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.CpInv

/-- info: 'STACS2027.RAM.P2.cpBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cpBody_spec

/-- info: 'STACS2027.RAM.P2.copy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.copy_spec

/-- info: 'STACS2027.RAM.P2.sel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.sel

/-- info: 'STACS2027.RAM.P2.cycPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cycPre

/-- info: 'STACS2027.RAM.P2.cycPre_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cycPre_zero

/-- info: 'STACS2027.RAM.P2.cycPre_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cycPre_succ

/-- info: 'STACS2027.RAM.P2.cycPre_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cycPre_full

/-- info: 'STACS2027.RAM.P2.flatten_flatMap_take_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.flatten_flatMap_take_le

/-- info: 'STACS2027.RAM.P2.cycPre_le_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cycPre_le_pool

/-- info: 'STACS2027.RAM.P2.topStarts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.topStarts_eq

/-- info: 'STACS2027.RAM.P2.DataB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.DataB

/-- info: 'STACS2027.RAM.P2.DataB.of_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.DataB.of_below

/-- info: 'STACS2027.RAM.P2.SegInv.dataB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.SegInv.dataB

/-- info: 'STACS2027.RAM.P2.QCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.QCtx

/-- info: 'STACS2027.RAM.P2.QCtx.of_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.QCtx.of_below

/-- info: 'STACS2027.RAM.P2.QCtx.stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.QCtx.stable

/-- info: 'STACS2027.RAM.P2.poInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poInit

/-- info: 'STACS2027.RAM.P2.prTest' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prTest

/-- info: 'STACS2027.RAM.P2.prCpA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prCpA

/-- info: 'STACS2027.RAM.P2.prCp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prCp

/-- info: 'STACS2027.RAM.P2.prBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prBody

/-- info: 'STACS2027.RAM.P2.prLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prLoop

/-- info: 'STACS2027.RAM.P2.poRd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poRd

/-- info: 'STACS2027.RAM.P2.poBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poBody

/-- info: 'STACS2027.RAM.P2.poFin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poFin

/-- info: 'STACS2027.RAM.P2.stageP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stageP

/-- info: 'STACS2027.RAM.P2.TPr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.TPr

/-- info: 'STACS2027.RAM.P2.TPo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.TPo

/-- info: 'STACS2027.RAM.P2.PoFr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.PoFr

/-- info: 'STACS2027.RAM.P2.PoFr.stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.PoFr.stable

/-- info: 'STACS2027.RAM.P2.prJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prJ

/-- info: 'STACS2027.RAM.P2.prJ_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prJ_zero

/-- info: 'STACS2027.RAM.P2.PrInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.PrInv

/-- info: 'STACS2027.RAM.P2.prInv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prInv_iff

/-- info: 'STACS2027.RAM.P2.PrInv.indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.PrInv.indep

/-- info: 'STACS2027.RAM.P2.prBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prBody_spec

/-- info: 'STACS2027.RAM.P2.prLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.prLoop_spec

/-- info: 'STACS2027.RAM.P2.PoInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.PoInv

/-- info: 'STACS2027.RAM.P2.PoInv.indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.PoInv.indep

/-- info: 'STACS2027.RAM.P2.poBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.poBody_spec

/-- info: 'STACS2027.RAM.P2.PoOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.PoOut

/-- info: 'STACS2027.RAM.P2.stageP_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stageP_spec

/-- info: 'STACS2027.RAM.P2.sgRd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.sgRd

/-- info: 'STACS2027.RAM.P2.sgInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.sgInit

/-- info: 'STACS2027.RAM.P2.sgFin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.sgFin

/-- info: 'STACS2027.RAM.P2.segBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.segBody

/-- info: 'STACS2027.RAM.P2.stageR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stageR

/-- info: 'STACS2027.RAM.P2.SegInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.SegInv

/-- info: 'STACS2027.RAM.P2.FrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.FrS

/-- info: 'STACS2027.RAM.P2.SegInv.indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.SegInv.indep

/-- info: 'STACS2027.RAM.P2.TSg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.TSg

/-- info: 'STACS2027.RAM.P2.RCtx.of_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.RCtx.of_below

/-- info: 'STACS2027.RAM.P2.segBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.segBody_spec

/-- info: 'STACS2027.RAM.P2.sum_slots_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.sum_slots_le

/-- info: 'STACS2027.RAM.P2.stageR_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stageR_spec

/-- info: 'STACS2027.RAM.P2.bElem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bElem

/-- info: 'STACS2027.RAM.P2.bCyc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bCyc

/-- info: 'STACS2027.RAM.P2.bAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bAll

/-- info: 'STACS2027.RAM.P2.flatMap_eq_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.flatMap_eq_single

/-- info: 'STACS2027.RAM.P2.flatMap_flatMap_eq_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.flatMap_flatMap_eq_single

/-- info: 'STACS2027.RAM.P2.idxOf_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.idxOf_eq_iff

/-- info: 'STACS2027.RAM.P2.bElem_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bElem_filter

/-- info: 'STACS2027.RAM.P2.bCyc_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bCyc_filter

/-- info: 'STACS2027.RAM.P2.flatMap_range_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.flatMap_range_getD

/-- info: 'STACS2027.RAM.P2.cyc_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cyc_facts

/-- info: 'STACS2027.RAM.P2.bnd_eq_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bnd_eq_scan

/-- info: 'STACS2027.RAM.P2.fst_lt_of_mem_bElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.fst_lt_of_mem_bElem

/-- info: 'STACS2027.RAM.P2.length_bCyc_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_bCyc_le

/-- info: 'STACS2027.RAM.P2.length_bAll_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_bAll_le

/-- info: 'STACS2027.RAM.P2.bndCat_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bndCat_eq

/-- info: 'STACS2027.RAM.P2.sum_range_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.sum_range_take

/-- info: 'STACS2027.RAM.P2.bndOffs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bndOffs_eq

/-- info: 'STACS2027.RAM.P2.tElem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tElem

/-- info: 'STACS2027.RAM.P2.tCyc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tCyc

/-- info: 'STACS2027.RAM.P2.trip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.trip

/-- info: 'STACS2027.RAM.P2.tripX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tripX

/-- info: 'STACS2027.RAM.P2.keyOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.keyOf

/-- info: 'STACS2027.RAM.P2.flatMap_ite_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.flatMap_ite_eq

/-- info: 'STACS2027.RAM.P2.tCyc_filter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tCyc_filter

/-- info: 'STACS2027.RAM.P2.trip_filter_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.trip_filter_seg

/-- info: 'STACS2027.RAM.P2.keyOf_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.keyOf_eq_iff

/-- info: 'STACS2027.RAM.P2.tripX_filter_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tripX_filter_key

/-- info: 'STACS2027.RAM.P2.tripX_key_bnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tripX_key_bnd

/-- info: 'STACS2027.RAM.P2.bndCat_eq_trip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bndCat_eq_trip

/-- info: 'STACS2027.RAM.P2.bndOffs_eq_trip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bndOffs_eq_trip

/-- info: 'STACS2027.RAM.P2.keyOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.keyOf_lt

/-- info: 'STACS2027.RAM.P2.trip_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.trip_lt

/-- info: 'STACS2027.RAM.P2.length_tCyc_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_tCyc_le

/-- info: 'STACS2027.RAM.P2.length_trip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_trip_le

/-- info: 'STACS2027.RAM.P2.length_tripX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_tripX

/-- info: 'STACS2027.RAM.P2.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rX

/-- info: 'STACS2027.RAM.P2.rCH' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rCH

/-- info: 'STACS2027.RAM.P2.rQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rQ

/-- info: 'STACS2027.RAM.P2.rP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rP

/-- info: 'STACS2027.RAM.P2.rSj' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rSj

/-- info: 'STACS2027.RAM.P2.rNSL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rNSL

/-- info: 'STACS2027.RAM.P2.rOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rOFF

/-- info: 'STACS2027.RAM.P2.rSt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rSt

/-- info: 'STACS2027.RAM.P2.rSA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rSA

/-- info: 'STACS2027.RAM.P2.slRdA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slRdA

/-- info: 'STACS2027.RAM.P2.slRdB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slRdB

/-- info: 'STACS2027.RAM.P2.slRd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slRd

/-- info: 'STACS2027.RAM.P2.slInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slInit

/-- info: 'STACS2027.RAM.P2.slFin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slFin

/-- info: 'STACS2027.RAM.P2.slotBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slotBody

/-- info: 'STACS2027.RAM.P2.slotLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slotLoop

/-- info: 'STACS2027.RAM.P2.TSl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.TSl

/-- info: 'STACS2027.RAM.P2.Lay' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.Lay

/-- info: 'STACS2027.RAM.P2.LayOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.LayOK

/-- info: 'STACS2027.RAM.P2.RCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.RCtx

/-- info: 'STACS2027.RAM.P2.RCtx.stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.RCtx.stable

/-- info: 'STACS2027.RAM.P2.FinOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.FinOK

/-- info: 'STACS2027.RAM.P2.FinOK.stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.FinOK.stable

/-- info: 'STACS2027.RAM.P2.fOff_le_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.fOff_le_length

/-- info: 'STACS2027.RAM.P2.faceCat_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.faceCat_getD

/-- info: 'STACS2027.RAM.P2.fOff_add_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.fOff_add_lt

/-- info: 'STACS2027.RAM.P2.faceOffs_getElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.faceOffs_getElem

/-- info: 'STACS2027.RAM.P2.slot_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slot_facts

/-- info: 'STACS2027.RAM.P2.slRdA_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slRdA_run

/-- info: 'STACS2027.RAM.P2.slRd_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slRd_run

/-- info: 'STACS2027.RAM.P2.segId_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.segId_le

/-- info: 'STACS2027.RAM.P2.slRd_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slRd_addrOK

/-- info: 'STACS2027.RAM.P2.RSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.RSt

/-- info: 'STACS2027.RAM.P2.RSt.stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.RSt.stable

/-- info: 'STACS2027.RAM.P2.encB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.encB

/-- info: 'STACS2027.RAM.P2.length_enc_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_enc_le

/-- info: 'STACS2027.RAM.P2.two_le_encB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.two_le_encB

/-- info: 'STACS2027.RAM.P2.FrB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.FrB

/-- info: 'STACS2027.RAM.P2.SlInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.SlInv

/-- info: 'STACS2027.RAM.P2.slInv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slInv_iff

/-- info: 'STACS2027.RAM.P2.SlInv.indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.SlInv.indep

/-- info: 'STACS2027.RAM.P2.slotBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slotBody_spec

/-- info: 'STACS2027.RAM.P2.slotLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.slotLoop_spec

/-- info: 'STACS2027.RAM.P2.finPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.finPre

/-- info: 'STACS2027.RAM.P2.fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.fin

/-- info: 'STACS2027.RAM.P2.cfin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cfin

/-- info: 'STACS2027.RAM.P2.enc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.enc

/-- info: 'STACS2027.RAM.P2.WF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.WF

/-- info: 'STACS2027.RAM.P2.emit2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emit2

/-- info: 'STACS2027.RAM.P2.emitR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emitR

/-- info: 'STACS2027.RAM.P2.emitL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.emitL

/-- info: 'STACS2027.RAM.P2.extPe' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.extPe

/-- info: 'STACS2027.RAM.P2.flatMap_ite_single' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.flatMap_ite_single

/-- info: 'STACS2027.RAM.P2.getElem_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.getElem_pairs

/-- info: 'STACS2027.RAM.P2.enc_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.enc_nil

/-- info: 'STACS2027.RAM.P2.enc_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.enc_append

/-- info: 'STACS2027.RAM.P2.enc_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.enc_cons

/-- info: 'STACS2027.RAM.P2.enc_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.enc_singleton

/-- info: 'STACS2027.RAM.P2.enc_flatMap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.enc_flatMap

/-- info: 'STACS2027.RAM.P2.encOff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.encOff

/-- info: 'STACS2027.RAM.P2.encOff_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.encOff_succ

/-- info: 'STACS2027.RAM.P2.encOff_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.encOff_length

/-- info: 'STACS2027.RAM.P2.enc_take_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.enc_take_succ

/-- info: 'STACS2027.RAM.P2.arr_enc_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.arr_enc_get

/-- info: 'STACS2027.RAM.P2.encOff_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.encOff_le

/-- info: 'STACS2027.RAM.P2.finPre_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.finPre_zero

/-- info: 'STACS2027.RAM.P2.finPre_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.finPre_succ

/-- info: 'STACS2027.RAM.P2.finPre_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.finPre_full

/-- info: 'STACS2027.RAM.P2.finPre_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.finPre_bound

/-- info: 'STACS2027.RAM.P2.fin_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.fin_bound

/-- info: 'STACS2027.RAM.P2.cfin_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.cfin_bound

/-- info: 'STACS2027.RAM.P2.rpF_eq_cfin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rpF_eq_cfin

/-- info: 'STACS2027.RAM.P2.extendParts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.extendParts_eq

/-- info: 'STACS2027.RAM.P2.filter_map_fst_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.filter_map_fst_eq

/-- info: 'STACS2027.RAM.P2.rpF_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rpF_seg

/-- info: 'STACS2027.RAM.P2.child_idx_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.child_idx_lt

/-- info: 'STACS2027.RAM.P2.rTX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rTX

/-- info: 'STACS2027.RAM.P2.rTI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rTI

/-- info: 'STACS2027.RAM.P2.rTL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rTL

/-- info: 'STACS2027.RAM.P2.rKY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rKY

/-- info: 'STACS2027.RAM.P2.rVB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.rVB

/-- info: 'STACS2027.RAM.P2.bS1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bS1

/-- info: 'STACS2027.RAM.P2.bS2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bS2

/-- info: 'STACS2027.RAM.P2.bS3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bS3

/-- info: 'STACS2027.RAM.P2.bS4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bS4

/-- info: 'STACS2027.RAM.P2.bS5' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bS5

/-- info: 'STACS2027.RAM.P2.bS6' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bS6

/-- info: 'STACS2027.RAM.P2.bS7' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bS7

/-- info: 'STACS2027.RAM.P2.bS8' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bS8

/-- info: 'STACS2027.RAM.P2.bS9' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bS9

/-- info: 'STACS2027.RAM.P2.bS10' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.bS10

/-- info: 'STACS2027.RAM.P2.stageB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stageB

/-- info: 'STACS2027.RAM.P2.BOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BOut

/-- info: 'STACS2027.RAM.P2.BCtx.of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.BCtx.of

/-- info: 'STACS2027.RAM.P2.pick_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.pick_zero

/-- info: 'STACS2027.RAM.P2.pick_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.pick_one

/-- info: 'STACS2027.RAM.P2.pick_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.pick_two

/-- info: 'STACS2027.RAM.P2.grpPass_HG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.grpPass_HG

/-- info: 'STACS2027.RAM.P2.vals_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.vals_eq

/-- info: 'STACS2027.RAM.P2.tkeys_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.tkeys_lt

/-- info: 'STACS2027.RAM.P2.skeys_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.skeys_lt

/-- info: 'STACS2027.RAM.P2.length_tripX'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.length_tripX'

/-- info: 'STACS2027.RAM.P2.TB2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.TB2

/-- info: 'STACS2027.RAM.P2.MB2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.MB2

/-- info: 'STACS2027.RAM.P2.stageB_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P2.stageB_spec

/-- info: 'STACS2027.RAM.P3.wregs_poly3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.wregs_poly3

/-- info: 'STACS2027.RAM.P3.wregs_prep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.wregs_prep

/-- info: 'STACS2027.RAM.P3.poly3_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.poly3_wregs

/-- info: 'STACS2027.RAM.P3.poly3_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.poly3_writes

/-- info: 'STACS2027.RAM.P3.not_mem_of_footprint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.not_mem_of_footprint

/-- info: 'STACS2027.RAM.P3.poly2Post_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.poly2Post_of_frame

/-- info: 'STACS2027.RAM.P3.prep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.prep_spec

/-- info: 'STACS2027.RAM.P3.cSeg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.cSeg

/-- info: 'STACS2027.RAM.P3.CT3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.CT3

/-- info: 'STACS2027.RAM.P3.CM3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.CM3

/-- info: 'STACS2027.RAM.P3.CP3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.CP3

/-- info: 'STACS2027.RAM.P3.M3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.M3

/-- info: 'STACS2027.RAM.P3.toffAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffAt_le

/-- info: 'STACS2027.RAM.P3.M3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.M3_le

/-- info: 'STACS2027.RAM.P3.tSeg_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tSeg_le

/-- info: 'STACS2027.RAM.P3.sum_faceVerts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.sum_faceVerts

/-- info: 'STACS2027.RAM.P3.segLoop_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segLoop_bound

/-- info: 'STACS2027.RAM.P3.poly3_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.poly3_specB

/-- info: 'STACS2027.RAM.P3.valsAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.valsAB

/-- info: 'STACS2027.RAM.P3.foldB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.foldB

/-- info: 'STACS2027.RAM.P3.length_valsAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_valsAB

/-- info: 'STACS2027.RAM.P3.valsAB_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.valsAB_lt

/-- info: 'STACS2027.RAM.P3.run_keepB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.run_keepB

/-- info: 'STACS2027.RAM.P3.BInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.BInv

/-- info: 'STACS2027.RAM.P3.tBeta' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tBeta

/-- info: 'STACS2027.RAM.P3.betaBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.betaBody_spec

/-- info: 'STACS2027.RAM.P3.betaLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.betaLoop_spec

/-- info: 'STACS2027.RAM.P3.AInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.AInv

/-- info: 'STACS2027.RAM.P3.tAlpha' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tAlpha

/-- info: 'STACS2027.RAM.P3.alphaBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.alphaBody_spec

/-- info: 'STACS2027.RAM.P3.alphaLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.alphaLoop_spec

/-- info: 'STACS2027.RAM.P3.scanL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.scanL

/-- info: 'STACS2027.RAM.P3.run_scanBody' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.run_scanBody

/-- info: 'STACS2027.RAM.P3.scanV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.scanV

/-- info: 'STACS2027.RAM.P3.scan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.scan_spec

/-- info: 'STACS2027.RAM.P3.encT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.encT

/-- info: 'STACS2027.RAM.P3.encL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.encL

/-- info: 'STACS2027.RAM.P3.tEnc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tEnc

/-- info: 'STACS2027.RAM.P3.encBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.encBody_spec

/-- info: 'STACS2027.RAM.P3.tCC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tCC

/-- info: 'STACS2027.RAM.P3.rd_bnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rd_bnd

/-- info: 'STACS2027.RAM.P3.childCost_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.childCost_spec

/-- info: 'STACS2027.RAM.P3.MSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.MSt

/-- info: 'STACS2027.RAM.P3.SegD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.SegD

/-- info: 'STACS2027.RAM.P3.sum_take_succ_seg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.sum_take_succ_seg

/-- info: 'STACS2027.RAM.P3.topIdx_sg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.topIdx_sg

/-- info: 'STACS2027.RAM.P3.length_topIdx_sg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_topIdx_sg

/-- info: 'STACS2027.RAM.P3.segRd_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segRd_spec

/-- info: 'STACS2027.RAM.P3.segPow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segPow_spec

/-- info: 'STACS2027.RAM.P3.getD_rel_sg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_rel_sg

/-- info: 'STACS2027.RAM.P3.run_relBody' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.run_relBody

/-- info: 'STACS2027.RAM.P3.RInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.RInv

/-- info: 'STACS2027.RAM.P3.relBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.relBody_spec

/-- info: 'STACS2027.RAM.P3.cfg_zero_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.cfg_zero_eq

/-- info: 'STACS2027.RAM.P3.segRel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segRel_spec

/-- info: 'STACS2027.RAM.P3.tSeg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tSeg

/-- info: 'STACS2027.RAM.P3.FrP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.FrP

/-- info: 'STACS2027.RAM.P3.segBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segBody_spec

/-- info: 'STACS2027.RAM.P3.segLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segLoop_spec

/-- info: 'STACS2027.RAM.P3.OdoSt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.OdoSt

/-- info: 'STACS2027.RAM.P3.odoBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.odoBody_spec

/-- info: 'STACS2027.RAM.P3.odo_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.odo_spec

/-- info: 'STACS2027.RAM.P3.pow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.pow_spec

/-- info: 'STACS2027.RAM.P3.powTo_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.powTo_spec

/-- info: 'STACS2027.RAM.P3.TInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.TInv

/-- info: 'STACS2027.RAM.P3.tToff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tToff

/-- info: 'STACS2027.RAM.P3.toffBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffBody_spec

/-- info: 'STACS2027.RAM.P3.toffInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffInit_spec

/-- info: 'STACS2027.RAM.P3.rK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rK

/-- info: 'STACS2027.RAM.P3.rJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rJ

/-- info: 'STACS2027.RAM.P3.rREL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rREL

/-- info: 'STACS2027.RAM.P3.rVAL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rVAL

/-- info: 'STACS2027.RAM.P3.rNB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rNB

/-- info: 'STACS2027.RAM.P3.rNC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rNC

/-- info: 'STACS2027.RAM.P3.rNR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rNR

/-- info: 'STACS2027.RAM.P3.rPB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rPB

/-- info: 'STACS2027.RAM.P3.rPC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rPC

/-- info: 'STACS2027.RAM.P3.rA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rA

/-- info: 'STACS2027.RAM.P3.rB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rB

/-- info: 'STACS2027.RAM.P3.rBEST' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rBEST

/-- info: 'STACS2027.RAM.P3.rARGB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rARGB

/-- info: 'STACS2027.RAM.P3.rTO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rTO

/-- info: 'STACS2027.RAM.P3.rFO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rFO

/-- info: 'STACS2027.RAM.P3.rFL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rFL

/-- info: 'STACS2027.RAM.P3.rSA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rSA

/-- info: 'STACS2027.RAM.P3.rSB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rSB

/-- info: 'STACS2027.RAM.P3.rVB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rVB

/-- info: 'STACS2027.RAM.P3.rTOT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rTOT

/-- info: 'STACS2027.RAM.P3.rQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rQ

/-- info: 'STACS2027.RAM.P3.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rX

/-- info: 'STACS2027.RAM.P3.rY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rY

/-- info: 'STACS2027.RAM.P3.rEX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rEX

/-- info: 'STACS2027.RAM.P3.rEY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rEY

/-- info: 'STACS2027.RAM.P3.rCNT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rCNT

/-- info: 'STACS2027.RAM.P3.rR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rR

/-- info: 'STACS2027.RAM.P3.rI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rI

/-- info: 'STACS2027.RAM.P3.rV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rV

/-- info: 'STACS2027.RAM.P3.rSEL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rSEL

/-- info: 'STACS2027.RAM.P3.rCB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rCB

/-- info: 'STACS2027.RAM.P3.rW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rW

/-- info: 'STACS2027.RAM.P3.rJJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rJJ

/-- info: 'STACS2027.RAM.P3.rPA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rPA

/-- info: 'STACS2027.RAM.P3.rPN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rPN

/-- info: 'STACS2027.RAM.P3.rM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rM

/-- info: 'STACS2027.RAM.P3.rMK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rMK

/-- info: 'STACS2027.RAM.P3.rWI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rWI

/-- info: 'STACS2027.RAM.P3.rWB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rWB

/-- info: 'STACS2027.RAM.P3.rBL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rBL

/-- info: 'STACS2027.RAM.P3.rT2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rT2

/-- info: 'STACS2027.RAM.P3.rACC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rACC

/-- info: 'STACS2027.RAM.P3.rPW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rPW

/-- info: 'STACS2027.RAM.P3.rDI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rDI

/-- info: 'STACS2027.RAM.P3.rIX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rIX

/-- info: 'STACS2027.RAM.P3.rR2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rR2

/-- info: 'STACS2027.RAM.P3.rU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rU

/-- info: 'STACS2027.RAM.P3.rOB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rOB

/-- info: 'STACS2027.RAM.P3.rOL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rOL

/-- info: 'STACS2027.RAM.P3.rOT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rOT

/-- info: 'STACS2027.RAM.P3.rCY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rCY

/-- info: 'STACS2027.RAM.P3.rOD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rOD

/-- info: 'STACS2027.RAM.P3.rSBO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rSBO

/-- info: 'STACS2027.RAM.P3.rTS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rTS

/-- info: 'STACS2027.RAM.P3.rPE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rPE

/-- info: 'STACS2027.RAM.P3.rPT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rPT

/-- info: 'STACS2027.RAM.P3.rPR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rPR

/-- info: 'STACS2027.RAM.P3.rN1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rN1

/-- info: 'STACS2027.RAM.P3.rX2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rX2

/-- info: 'STACS2027.RAM.P3.rACC2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rACC2

/-- info: 'STACS2027.RAM.P3.chk' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.chk

/-- info: 'STACS2027.RAM.P3.icBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.icBody

/-- info: 'STACS2027.RAM.P3.inCyc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.inCyc

/-- info: 'STACS2027.RAM.P3.selPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.selPre

/-- info: 'STACS2027.RAM.P3.selPost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.selPost

/-- info: 'STACS2027.RAM.P3.isSel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.isSel

/-- info: 'STACS2027.RAM.P3.lcBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.lcBody

/-- info: 'STACS2027.RAM.P3.loadCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.loadCost

/-- info: 'STACS2027.RAM.P3.scanBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.scanBody

/-- info: 'STACS2027.RAM.P3.encRd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.encRd

/-- info: 'STACS2027.RAM.P3.encBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.encBody

/-- info: 'STACS2027.RAM.P3.ccPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.ccPre

/-- info: 'STACS2027.RAM.P3.ccPost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.ccPost

/-- info: 'STACS2027.RAM.P3.childCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.childCost

/-- info: 'STACS2027.RAM.P3.slotRd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.slotRd

/-- info: 'STACS2027.RAM.P3.sideCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.sideCost

/-- info: 'STACS2027.RAM.P3.slotBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.slotBody

/-- info: 'STACS2027.RAM.P3.totInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.totInit

/-- info: 'STACS2027.RAM.P3.total' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.total

/-- info: 'STACS2027.RAM.P3.odoBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.odoBody

/-- info: 'STACS2027.RAM.P3.odo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.odo

/-- info: 'STACS2027.RAM.P3.powBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.powBody

/-- info: 'STACS2027.RAM.P3.pow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.pow

/-- info: 'STACS2027.RAM.P3.keep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.keep

/-- info: 'STACS2027.RAM.P3.keepB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.keepB

/-- info: 'STACS2027.RAM.P3.bOdoArgs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.bOdoArgs

/-- info: 'STACS2027.RAM.P3.betaBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.betaBody

/-- info: 'STACS2027.RAM.P3.store' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.store

/-- info: 'STACS2027.RAM.P3.aInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.aInit

/-- info: 'STACS2027.RAM.P3.aOdoArgs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.aOdoArgs

/-- info: 'STACS2027.RAM.P3.alphaBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.alphaBody

/-- info: 'STACS2027.RAM.P3.segRd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segRd

/-- info: 'STACS2027.RAM.P3.powTo' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.powTo

/-- info: 'STACS2027.RAM.P3.segPow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segPow

/-- info: 'STACS2027.RAM.P3.relBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.relBody

/-- info: 'STACS2027.RAM.P3.valAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.valAlloc

/-- info: 'STACS2027.RAM.P3.segRel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segRel

/-- info: 'STACS2027.RAM.P3.segBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segBody

/-- info: 'STACS2027.RAM.P3.toffRd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffRd

/-- info: 'STACS2027.RAM.P3.toffSt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffSt

/-- info: 'STACS2027.RAM.P3.toffBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffBody

/-- info: 'STACS2027.RAM.P3.toffAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffAlloc

/-- info: 'STACS2027.RAM.P3.tabAlloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tabAlloc

/-- info: 'STACS2027.RAM.P3.toffInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffInit

/-- info: 'STACS2027.RAM.P3.prep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.prep

/-- info: 'STACS2027.RAM.P3.segLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.segLoop

/-- info: 'STACS2027.RAM.P3.poly3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.poly3

/-- info: 'STACS2027.RAM.P3.Glob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.Glob

/-- info: 'STACS2027.RAM.P3.SegR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.SegR

/-- info: 'STACS2027.RAM.P3.SSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.SSt

/-- info: 'STACS2027.RAM.P3.Lay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.Lay

/-- info: 'STACS2027.RAM.P3.tabPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tabPre

/-- info: 'STACS2027.RAM.P3.argPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.argPre

/-- info: 'STACS2027.RAM.P3.AMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.AMem

/-- info: 'STACS2027.RAM.P3.length_tabPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_tabPre

/-- info: 'STACS2027.RAM.P3.length_argPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_argPre

/-- info: 'STACS2027.RAM.P3.toffAt_le_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffAt_le_full

/-- info: 'STACS2027.RAM.P3.AMem.updV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.AMem.updV

/-- info: 'STACS2027.RAM.P3.AMem.store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.AMem.store

/-- info: 'STACS2027.RAM.P3.Glob.rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.Glob.rd

/-- info: 'STACS2027.RAM.P3.rd_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.rd_of

/-- info: 'STACS2027.RAM.P3.sg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.sg

/-- info: 'STACS2027.RAM.P3.sg_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.sg_eq

/-- info: 'STACS2027.RAM.P3.sg_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.sg_mem

/-- info: 'STACS2027.RAM.P3.Rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.Rd

/-- info: 'STACS2027.RAM.P3.pool_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.pool_read

/-- info: 'STACS2027.RAM.P3.pool_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.pool_bound

/-- info: 'STACS2027.RAM.P3.run_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.run_chk

/-- info: 'STACS2027.RAM.P3.EdgeIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.EdgeIn

/-- info: 'STACS2027.RAM.P3.icBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.icBody_spec

/-- info: 'STACS2027.RAM.P3.inCyc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.inCyc_spec

/-- info: 'STACS2027.RAM.P3.run_selPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.run_selPost

/-- info: 'STACS2027.RAM.P3.isSel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.isSel_spec

/-- info: 'STACS2027.RAM.P3.cntR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.cntR

/-- info: 'STACS2027.RAM.P3.countP_range_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.countP_range_succ

/-- info: 'STACS2027.RAM.P3.tSel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tSel

/-- info: 'STACS2027.RAM.P3.lcBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.lcBody_spec

/-- info: 'STACS2027.RAM.P3.tLC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tLC

/-- info: 'STACS2027.RAM.P3.loadCost_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.loadCost_spec

/-- info: 'STACS2027.RAM.P3.tabArg_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tabArg_fuel

/-- info: 'STACS2027.RAM.P3.totV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.totV

/-- info: 'STACS2027.RAM.P3.totAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.totAB

/-- info: 'STACS2027.RAM.P3.stepB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.stepB

/-- info: 'STACS2027.RAM.P3.best' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.best

/-- info: 'STACS2027.RAM.P3.foldl_stepB_tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.foldl_stepB_tail

/-- info: 'STACS2027.RAM.P3.foldl_stepB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.foldl_stepB

/-- info: 'STACS2027.RAM.P3.tabArg_eq_best' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tabArg_eq_best

/-- info: 'STACS2027.RAM.P3.table_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.table_eq

/-- info: 'STACS2027.RAM.P3.argTab_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.argTab_eq

/-- info: 'STACS2027.RAM.P3.foldl_stepB_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.foldl_stepB_succ

/-- info: 'STACS2027.RAM.P3.slotCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.slotCost

/-- info: 'STACS2027.RAM.P3.pairs_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.pairs_lt

/-- info: 'STACS2027.RAM.P3.pairs_eq_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.pairs_eq_map

/-- info: 'STACS2027.RAM.P3.sum_map_ite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.sum_map_ite

/-- info: 'STACS2027.RAM.P3.totV_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.totV_eq

/-- info: 'STACS2027.RAM.P3.selQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.selQ

/-- info: 'STACS2027.RAM.P3.zip_eq_map_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.zip_eq_map_range

/-- info: 'STACS2027.RAM.P3.loadAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.loadAt_eq

/-- info: 'STACS2027.RAM.P3.mem_pathEdges_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.mem_pathEdges_iff

/-- info: 'STACS2027.RAM.P3.nxt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.nxt

/-- info: 'STACS2027.RAM.P3.mem_cycleEdges_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.mem_cycleEdges_iff

/-- info: 'STACS2027.RAM.P3.eq_edge_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.eq_edge_iff

/-- info: 'STACS2027.RAM.P3.length_of_mem_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_of_mem_pool

/-- info: 'STACS2027.RAM.P3.length_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_cyc

/-- info: 'STACS2027.RAM.P3.getD_flatten_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_flatten_const

/-- info: 'STACS2027.RAM.P3.length_flatten_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_flatten_const

/-- info: 'STACS2027.RAM.P3.getD_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_pool

/-- info: 'STACS2027.RAM.P3.length_flatten_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_flatten_pool

/-- info: 'STACS2027.RAM.P3.blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.blk

/-- info: 'STACS2027.RAM.P3.ablk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.ablk

/-- info: 'STACS2027.RAM.P3.tabDone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tabDone

/-- info: 'STACS2027.RAM.P3.argDone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.argDone

/-- info: 'STACS2027.RAM.P3.toffAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffAt

/-- info: 'STACS2027.RAM.P3.getD_prefixSums' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_prefixSums

/-- info: 'STACS2027.RAM.P3.length_prefixSums' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_prefixSums

/-- info: 'STACS2027.RAM.P3.getD_prefixSums_seg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_prefixSums_seg

/-- info: 'STACS2027.RAM.P3.getD_flatMap_seg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_flatMap_seg

/-- info: 'STACS2027.RAM.P3.lt_length_flatMap_seg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.lt_length_flatMap_seg

/-- info: 'STACS2027.RAM.P3.arr_flatMap_seg_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.arr_flatMap_seg_read

/-- info: 'STACS2027.RAM.P3.arr_prefixSums_seg_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.arr_prefixSums_seg_read

/-- info: 'STACS2027.RAM.P3.idxOf_child_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.idxOf_child_lt

/-- info: 'STACS2027.RAM.P3.length_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_blk

/-- info: 'STACS2027.RAM.P3.length_ablk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_ablk

/-- info: 'STACS2027.RAM.P3.length_tabDone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_tabDone

/-- info: 'STACS2027.RAM.P3.length_argDone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_argDone

/-- info: 'STACS2027.RAM.P3.tabDone_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tabDone_succ

/-- info: 'STACS2027.RAM.P3.argDone_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.argDone_succ

/-- info: 'STACS2027.RAM.P3.tabDone_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tabDone_full

/-- info: 'STACS2027.RAM.P3.argDone_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.argDone_full

/-- info: 'STACS2027.RAM.P3.toffAt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffAt_succ

/-- info: 'STACS2027.RAM.P3.sum_take_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.sum_take_mono

/-- info: 'STACS2027.RAM.P3.toffAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffAt_mono

/-- info: 'STACS2027.RAM.P3.toffAt_add_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.toffAt_add_lt

/-- info: 'STACS2027.RAM.P3.getD_tabOffs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_tabOffs

/-- info: 'STACS2027.RAM.P3.length_tabOffs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_tabOffs

/-- info: 'STACS2027.RAM.P3.getD_tabDone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_tabDone

/-- info: 'STACS2027.RAM.P3.getD_argDone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_argDone

/-- info: 'STACS2027.RAM.P3.getD_tabCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_tabCat

/-- info: 'STACS2027.RAM.P3.getD_argCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.getD_argCat

/-- info: 'STACS2027.RAM.P3.digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.digit

/-- info: 'STACS2027.RAM.P3.enc_append_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.enc_append_singleton

/-- info: 'STACS2027.RAM.P3.map_range_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.map_range_getD

/-- info: 'STACS2027.RAM.P3.childIdx_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.childIdx_eq

/-- info: 'STACS2027.RAM.P3.enc_range_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.enc_range_succ

/-- info: 'STACS2027.RAM.P3.digit_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.digit_lt

/-- info: 'STACS2027.RAM.P3.childIdx_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.childIdx_lt

/-- info: 'STACS2027.RAM.P3.scan_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.scan_step

/-- info: 'STACS2027.RAM.P3.scan_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.scan_done

/-- info: 'STACS2027.RAM.P3.odoL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.odoL

/-- info: 'STACS2027.RAM.P3.odoc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.odoc

/-- info: 'STACS2027.RAM.P3.odoL_cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.odoL_cfg

/-- info: 'STACS2027.RAM.P3.cfg_pow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.cfg_pow

/-- info: 'STACS2027.RAM.P3.odoc_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.odoc_zero

/-- info: 'STACS2027.RAM.P3.odoc_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.odoc_nil

/-- info: 'STACS2027.RAM.P3.set_middle' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.set_middle

/-- info: 'STACS2027.RAM.P3.Rb' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.Rb

/-- info: 'STACS2027.RAM.P3.length_bnd_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_bnd_le'

/-- info: 'STACS2027.RAM.P3.length_topIdx_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_topIdx_le'

/-- info: 'STACS2027.RAM.P3.length_rel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.length_rel_le

/-- info: 'STACS2027.RAM.P3.fOff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.fOff_eq

/-- info: 'STACS2027.RAM.P3.slotAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.slotAt

/-- info: 'STACS2027.RAM.P3.totQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.totQ

/-- info: 'STACS2027.RAM.P3.slotAt_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.slotAt_mem

/-- info: 'STACS2027.RAM.P3.totQ_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.totQ_full

/-- info: 'STACS2027.RAM.P3.tSlot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tSlot

/-- info: 'STACS2027.RAM.P3.slotBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.slotBody_spec

/-- info: 'STACS2027.RAM.P3.tTot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.tTot

/-- info: 'STACS2027.RAM.P3.total_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P3.total_spec

/-- info: 'STACS2027.RAM.P4.rOI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rOI

/-- info: 'STACS2027.RAM.P4.rPP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rPP

/-- info: 'STACS2027.RAM.P4.rV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rV

/-- info: 'STACS2027.RAM.P4.rOT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rOT

/-- info: 'STACS2027.RAM.P4.rOP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rOP

/-- info: 'STACS2027.RAM.P4.rOX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rOX

/-- info: 'STACS2027.RAM.P4.outInner' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.outInner

/-- info: 'STACS2027.RAM.P4.outBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.outBody

/-- info: 'STACS2027.RAM.P4.outLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.outLoop

/-- info: 'STACS2027.RAM.P4.poly4' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.poly4

/-- info: 'STACS2027.RAM.P4.CP4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.CP4

/-- info: 'STACS2027.RAM.P4.outPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.outPre

/-- info: 'STACS2027.RAM.P4.OutInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.OutInv

/-- info: 'STACS2027.RAM.P4.InInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.InInv

/-- info: 'STACS2027.RAM.P4.outInner_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.outInner_spec

/-- info: 'STACS2027.RAM.P4.outPre_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.outPre_succ

/-- info: 'STACS2027.RAM.P4.outPre_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.outPre_full

/-- info: 'STACS2027.RAM.P4.outBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.outBody_spec

/-- info: 'STACS2027.RAM.P4.outLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.outLoop_spec

/-- info: 'STACS2027.RAM.P4.IfRegs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.IfRegs

/-- info: 'STACS2027.RAM.P4.M4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.M4

/-- info: 'STACS2027.RAM.P4.M4_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.M4_le

/-- info: 'STACS2027.RAM.P4.poly4_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.poly4_specB

/-- info: 'STACS2027.RAM.P4.poly4_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.poly4_wregs

/-- info: 'STACS2027.RAM.P4.segHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.segHead

/-- info: 'STACS2027.RAM.P4.segE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.segE

/-- info: 'STACS2027.RAM.P4.segBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.segBody

/-- info: 'STACS2027.RAM.P4.Tdec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.Tdec

/-- info: 'STACS2027.RAM.P4.Tseg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.Tseg

/-- info: 'STACS2027.RAM.P4.nSl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.nSl

/-- info: 'STACS2027.RAM.P4.BtInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.BtInv

/-- info: 'STACS2027.RAM.P4.SegR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.SegR

/-- info: 'STACS2027.RAM.P4.BtMem.wr_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.BtMem.wr_val

/-- info: 'STACS2027.RAM.P4.arr_wr_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.arr_wr_of_lt

/-- info: 'STACS2027.RAM.P4.segHead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.segHead_run

/-- info: 'STACS2027.RAM.P4.segHead_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.segHead_addrOK

/-- info: 'STACS2027.RAM.P4.decode_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.decode_le

/-- info: 'STACS2027.RAM.P4.segBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.segBody_spec

/-- info: 'STACS2027.RAM.P4.sum_map_le'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.sum_map_le'

/-- info: 'STACS2027.RAM.P4.sum_nSl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.sum_nSl_le

/-- info: 'STACS2027.RAM.P4.btLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.btLoop_spec

/-- info: 'STACS2027.RAM.P4.Fix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.Fix

/-- info: 'STACS2027.RAM.P4.BtMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.BtMem

/-- info: 'STACS2027.RAM.P4.F₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.F₁
