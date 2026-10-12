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

/-- info: 'STACS2027.RAM.P4.BtMem.wr_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.BtMem.wr_above

/-- info: 'STACS2027.RAM.P4.bOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.bOff

/-- info: 'STACS2027.RAM.P4.tOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.tOff

/-- info: 'STACS2027.RAM.P4.fOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.fOf

/-- info: 'STACS2027.RAM.P4.sum_take_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.sum_take_succ

/-- info: 'STACS2027.RAM.P4.sum_take_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.sum_take_le

/-- info: 'STACS2027.RAM.P4.lt_boff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_boff

/-- info: 'STACS2027.RAM.P4.rd_boff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rd_boff

/-- info: 'STACS2027.RAM.P4.bOff_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.bOff_succ

/-- info: 'STACS2027.RAM.P4.lt_bidx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_bidx

/-- info: 'STACS2027.RAM.P4.rd_bidx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rd_bidx

/-- info: 'STACS2027.RAM.P4.lt_tst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_tst

/-- info: 'STACS2027.RAM.P4.rd_tst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rd_tst

/-- info: 'STACS2027.RAM.P4.lt_toff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_toff

/-- info: 'STACS2027.RAM.P4.rd_toff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rd_toff

/-- info: 'STACS2027.RAM.P4.lt_arg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_arg

/-- info: 'STACS2027.RAM.P4.rd_arg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rd_arg

/-- info: 'STACS2027.RAM.P4.lt_foff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_foff

/-- info: 'STACS2027.RAM.P4.rd_foff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rd_foff

/-- info: 'STACS2027.RAM.P4.fOf_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.fOf_succ

/-- info: 'STACS2027.RAM.P4.lt_fv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_fv

/-- info: 'STACS2027.RAM.P4.rd_fv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rd_fv

/-- info: 'STACS2027.RAM.P4.fOf_eq_fOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.fOf_eq_fOff

/-- info: 'STACS2027.RAM.P4.lt_fsidCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_fsidCat

/-- info: 'STACS2027.RAM.P4.lt_fsid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_fsid

/-- info: 'STACS2027.RAM.P4.rd_fsid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rd_fsid

/-- info: 'STACS2027.RAM.P4.lt_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_pool

/-- info: 'STACS2027.RAM.P4.rd_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rd_pool

/-- info: 'STACS2027.RAM.P4.lt_omap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_omap

/-- info: 'STACS2027.RAM.P4.rd_omap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rd_omap

/-- info: 'STACS2027.RAM.P4.slotHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.slotHead

/-- info: 'STACS2027.RAM.P4.slotBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.slotBody

/-- info: 'STACS2027.RAM.P4.Tch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.Tch

/-- info: 'STACS2027.RAM.P4.Tsl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.Tsl

/-- info: 'STACS2027.RAM.P4.SegRegs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.SegRegs

/-- info: 'STACS2027.RAM.P4.SlInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.SlInv

/-- info: 'STACS2027.RAM.P4.lkp_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lkp_congr

/-- info: 'STACS2027.RAM.P4.getElem_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.getElem_slots

/-- info: 'STACS2027.RAM.P4.length_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.length_slots

/-- info: 'STACS2027.RAM.P4.BtMem.upd_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.BtMem.upd_a

/-- info: 'STACS2027.RAM.P4.dig_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.dig_eq

/-- info: 'STACS2027.RAM.P4.slotBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.slotBody_spec

/-- info: 'STACS2027.RAM.P4.iteT' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.iteT

/-- info: 'STACS2027.RAM.P4.iteF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.iteF

/-- info: 'STACS2027.RAM.P4.getD_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.getD_lt

/-- info: 'STACS2027.RAM.P4.wr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.wr

/-- info: 'STACS2027.RAM.P4.wr_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.wr_nil

/-- info: 'STACS2027.RAM.P4.wr_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.wr_of_lt

/-- info: 'STACS2027.RAM.P4.wr_of_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.wr_of_ge

/-- info: 'STACS2027.RAM.P4.wr_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.wr_snoc

/-- info: 'STACS2027.RAM.P4.arr_wr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.arr_wr

/-- info: 'STACS2027.RAM.P4.sameOn_wr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.sameOn_wr

/-- info: 'STACS2027.RAM.P4.zeroFrom_wr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.zeroFrom_wr

/-- info: 'STACS2027.RAM.P4.enc_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.enc_append

/-- info: 'STACS2027.RAM.P4.enc_take_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.enc_take_succ

/-- info: 'STACS2027.RAM.P4.cfg_take_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.cfg_take_succ

/-- info: 'STACS2027.RAM.P4.div_pow_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.div_pow_succ

/-- info: 'STACS2027.RAM.P4.pairs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.pairs_eq

/-- info: 'STACS2027.RAM.P4.map_rotateTo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.map_rotateTo

/-- info: 'STACS2027.RAM.P4.lkp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lkp

/-- info: 'STACS2027.RAM.P4.idxOf_range'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.idxOf_range'

/-- info: 'STACS2027.RAM.P4.getD_idxOf_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.getD_idxOf_rel

/-- info: 'STACS2027.RAM.P4.abAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.abAt

/-- info: 'STACS2027.RAM.P4.valAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.valAt

/-- info: 'STACS2027.RAM.P4.rpLen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rpLen

/-- info: 'STACS2027.RAM.P4.tst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.tst

/-- info: 'STACS2027.RAM.P4.chPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.chPart

/-- info: 'STACS2027.RAM.P4.valsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.valsOf

/-- info: 'STACS2027.RAM.P4.fPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.fPart

/-- info: 'STACS2027.RAM.P4.abAt_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.abAt_zero

/-- info: 'STACS2027.RAM.P4.abAt_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.abAt_length

/-- info: 'STACS2027.RAM.P4.abAt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.abAt_succ

/-- info: 'STACS2027.RAM.P4.abAt_succ_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.abAt_succ_fst

/-- info: 'STACS2027.RAM.P4.abAt_succ_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.abAt_succ_snd

/-- info: 'STACS2027.RAM.P4.abAt_fst_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.abAt_fst_lt

/-- info: 'STACS2027.RAM.P4.chPart_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.chPart_zero

/-- info: 'STACS2027.RAM.P4.chPart_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.chPart_full

/-- info: 'STACS2027.RAM.P4.chPart_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.chPart_succ

/-- info: 'STACS2027.RAM.P4.fPart_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.fPart_zero

/-- info: 'STACS2027.RAM.P4.fPart_succ_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.fPart_succ_child

/-- info: 'STACS2027.RAM.P4.fPart_succ_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.fPart_succ_side

/-- info: 'STACS2027.RAM.P4.tst_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.tst_zero

/-- info: 'STACS2027.RAM.P4.tst_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.tst_succ

/-- info: 'STACS2027.RAM.P4.tst_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.tst_length

/-- info: 'STACS2027.RAM.P4.tst_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.tst_mono

/-- info: 'STACS2027.RAM.P4.topIdx_tst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.topIdx_tst

/-- info: 'STACS2027.RAM.P4.length_topIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.length_topIdx

/-- info: 'STACS2027.RAM.P4.mem_tst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.mem_tst

/-- info: 'STACS2027.RAM.P4.valAt_update_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.valAt_update_self

/-- info: 'STACS2027.RAM.P4.valAt_update_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.valAt_update_ne

/-- info: 'STACS2027.RAM.P4.cyc_mem_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.cyc_mem_pool

/-- info: 'STACS2027.RAM.P4.length_of_mem_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.length_of_mem_pool

/-- info: 'STACS2027.RAM.P4.length_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.length_cyc

/-- info: 'STACS2027.RAM.P4.lt_of_mem_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lt_of_mem_cyc

/-- info: 'STACS2027.RAM.P4.mem_childSegs'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.mem_childSegs'

/-- info: 'STACS2027.RAM.P4.argTab_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.argTab_lt

/-- info: 'STACS2027.RAM.P4.Lk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.Lk

/-- info: 'STACS2027.RAM.P4.length_bnd_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.length_bnd_le'

/-- info: 'STACS2027.RAM.P4.length_topIdx_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.length_topIdx_le'

/-- info: 'STACS2027.RAM.P4.length_pool_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.length_pool_le

/-- info: 'STACS2027.RAM.P4.getD_prefixSums' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.getD_prefixSums

/-- info: 'STACS2027.RAM.P4.arr_prefixSums_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.arr_prefixSums_get

/-- info: 'STACS2027.RAM.P4.arr_flatMap_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.arr_flatMap_part

/-- info: 'STACS2027.RAM.P4.arr_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.arr_pool

/-- info: 'STACS2027.RAM.P4.rK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rK

/-- info: 'STACS2027.RAM.P4.rA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rA

/-- info: 'STACS2027.RAM.P4.rVAL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rVAL

/-- info: 'STACS2027.RAM.P4.rJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rJ

/-- info: 'STACS2027.RAM.P4.rM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rM

/-- info: 'STACS2027.RAM.P4.rAL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rAL

/-- info: 'STACS2027.RAM.P4.rBE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rBE

/-- info: 'STACS2027.RAM.P4.rBO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rBO

/-- info: 'STACS2027.RAM.P4.rNB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rNB

/-- info: 'STACS2027.RAM.P4.rTS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rTS

/-- info: 'STACS2027.RAM.P4.rTE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rTE

/-- info: 'STACS2027.RAM.P4.rAD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rAD

/-- info: 'STACS2027.RAM.P4.rFO' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rFO

/-- info: 'STACS2027.RAM.P4.rNSL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rNSL

/-- info: 'STACS2027.RAM.P4.rQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rQ

/-- info: 'STACS2027.RAM.P4.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rX

/-- info: 'STACS2027.RAM.P4.rY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rY

/-- info: 'STACS2027.RAM.P4.rJW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rJW

/-- info: 'STACS2027.RAM.P4.rBW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rBW

/-- info: 'STACS2027.RAM.P4.rNW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rNW

/-- info: 'STACS2027.RAM.P4.rACC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rACC

/-- info: 'STACS2027.RAM.P4.rPW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rPW

/-- info: 'STACS2027.RAM.P4.rQ2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rQ2

/-- info: 'STACS2027.RAM.P4.rI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rI

/-- info: 'STACS2027.RAM.P4.rD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rD

/-- info: 'STACS2027.RAM.P4.rF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rF

/-- info: 'STACS2027.RAM.P4.rP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rP

/-- info: 'STACS2027.RAM.P4.rZ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rZ

/-- info: 'STACS2027.RAM.P4.rTMP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rTMP

/-- info: 'STACS2027.RAM.P4.rMC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rMC

/-- info: 'STACS2027.RAM.P4.rTN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rTN

/-- info: 'STACS2027.RAM.P4.rDX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rDX

/-- info: 'STACS2027.RAM.P4.rDL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rDL

/-- info: 'STACS2027.RAM.P4.rDB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rDB

/-- info: 'STACS2027.RAM.P4.rDT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rDT

/-- info: 'STACS2027.RAM.P4.rDQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.rDQ

/-- info: 'STACS2027.RAM.P4.dmCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.dmCond

/-- info: 'STACS2027.RAM.P4.dmBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.dmBody

/-- info: 'STACS2027.RAM.P4.divmod' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.divmod

/-- info: 'STACS2027.RAM.P4.DmInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.DmInv

/-- info: 'STACS2027.RAM.P4.divmod_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.divmod_spec

/-- info: 'STACS2027.RAM.P4.decBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.decBody

/-- info: 'STACS2027.RAM.P4.decode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.decode

/-- info: 'STACS2027.RAM.P4.DecInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.DecInv

/-- info: 'STACS2027.RAM.P4.decBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.decBody_spec

/-- info: 'STACS2027.RAM.P4.decode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.decode_spec

/-- info: 'STACS2027.RAM.P4.LkEnv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.LkEnv

/-- info: 'STACS2027.RAM.P4.LkRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.LkRegs

/-- info: 'STACS2027.RAM.P4.LkMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.LkMem

/-- info: 'STACS2027.RAM.P4.LkBnd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.LkBnd

/-- info: 'STACS2027.RAM.P4.LkEnv.dig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.LkEnv.dig

/-- info: 'STACS2027.RAM.P4.scanBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.scanBody

/-- info: 'STACS2027.RAM.P4.notFound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.notFound

/-- info: 'STACS2027.RAM.P4.lkInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lkInit

/-- info: 'STACS2027.RAM.P4.lookup' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lookup

/-- info: 'STACS2027.RAM.P4.ScInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.ScInv

/-- info: 'STACS2027.RAM.P4.scanBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.scanBody_spec

/-- info: 'STACS2027.RAM.P4.lookup_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.lookup_spec

/-- info: 'STACS2027.RAM.P4.digBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.digBody

/-- info: 'STACS2027.RAM.P4.chHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.chHead

/-- info: 'STACS2027.RAM.P4.child' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.child

/-- info: 'STACS2027.RAM.P4.DgInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.DgInv

/-- info: 'STACS2027.RAM.P4.digBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.digBody_spec

/-- info: 'STACS2027.RAM.P4.child_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P4.child_spec

/-- info: 'STACS2027.RAM.gNS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gNS

/-- info: 'STACS2027.RAM.gSA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gSA

/-- info: 'STACS2027.RAM.gSB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gSB

/-- info: 'STACS2027.RAM.gFSID' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gFSID

/-- info: 'STACS2027.RAM.gFOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gFOFF

/-- info: 'STACS2027.RAM.gFV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gFV

/-- info: 'STACS2027.RAM.gNP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gNP

/-- info: 'STACS2027.RAM.gPOOL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gPOOL

/-- info: 'STACS2027.RAM.gTST' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gTST

/-- info: 'STACS2027.RAM.gBOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gBOFF

/-- info: 'STACS2027.RAM.gBIDX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gBIDX

/-- info: 'STACS2027.RAM.gTOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gTOFF

/-- info: 'STACS2027.RAM.gTAB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gTAB

/-- info: 'STACS2027.RAM.gARG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gARG

/-- info: 'STACS2027.RAM.gPx' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.gPx

/-- info: 'STACS2027.RAM.prefixSums' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.prefixSums

/-- info: 'STACS2027.RAM.segId' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.segId

/-- info: 'STACS2027.RAM.faceSids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.faceSids

/-- info: 'STACS2027.RAM.fsidCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.fsidCat

/-- info: 'STACS2027.RAM.faceOffs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.faceOffs

/-- info: 'STACS2027.RAM.faceCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.faceCat

/-- info: 'STACS2027.RAM.topStarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.topStarts

/-- info: 'STACS2027.RAM.bndOffs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bndOffs

/-- info: 'STACS2027.RAM.bndCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bndCat

/-- info: 'STACS2027.RAM.tabOffs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.tabOffs

/-- info: 'STACS2027.RAM.tabCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.tabCat

/-- info: 'STACS2027.RAM.argCat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.argCat

/-- info: 'STACS2027.RAM.Poly1Post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Poly1Post

/-- info: 'STACS2027.RAM.Poly2Post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Poly2Post

/-- info: 'STACS2027.RAM.Poly3Post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Poly3Post

/-- info: 'STACS2027.RAM.PolyPhaseB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PolyPhaseB

/-- info: 'STACS2027.RAM.PolySolver.polySolver' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PolySolver.polySolver

/-- info: 'STACS2027.RAM.PolySolver.polySolver_specB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PolySolver.polySolver_specB

/-- info: 'STACS2027.RAM.PolySolver.polySolver_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.PolySolver.polySolver_wregs

/-- info: 'STACS2027.RAM.R0.R0Post' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.R0Post

/-- info: 'STACS2027.RAM.R0.R0Post.labels_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.R0Post.labels_le

/-- info: 'STACS2027.RAM.R0.R0Post.dict_label' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.R0Post.dict_label

/-- info: 'STACS2027.RAM.R0.C0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.C0

/-- info: 'STACS2027.RAM.R0.labels_take_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.labels_take_zero

/-- info: 'STACS2027.RAM.R0.r0_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.r0_core

/-- info: 'STACS2027.RAM.R0.keepInv_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.keepInv_post

/-- info: 'STACS2027.RAM.R0.r0_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.r0_zero

/-- info: 'STACS2027.RAM.R0.r0_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.r0_writes

/-- info: 'STACS2027.RAM.R0.r0_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.r0_spec

/-- info: 'STACS2027.RAM.R0.StaticMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.StaticMem

/-- info: 'STACS2027.RAM.R0.StaticMem.upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.StaticMem.upd

/-- info: 'STACS2027.RAM.R0.StaticMem.of_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.StaticMem.of_below

/-- info: 'STACS2027.RAM.R0.IdsMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.IdsMem

/-- info: 'STACS2027.RAM.R0.IdsRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.IdsRep

/-- info: 'STACS2027.RAM.R0.IdsRep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.IdsRep.indep

/-- info: 'STACS2027.RAM.R0.IdsInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.IdsInv

/-- info: 'STACS2027.RAM.R0.IdsMem.snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.IdsMem.snoc

/-- info: 'STACS2027.RAM.R0.idsInit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.idsInit_spec

/-- info: 'STACS2027.RAM.R0.loopFree_edgeIds' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.loopFree_edgeIds

/-- info: 'STACS2027.RAM.R0.edgeIds_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.edgeIds_run

/-- info: 'STACS2027.RAM.R0.idsIns_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.idsIns_run

/-- info: 'STACS2027.RAM.R0.idsBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.idsBody_spec

/-- info: 'STACS2027.RAM.R0.stepIds_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.stepIds_spec

/-- info: 'STACS2027.RAM.R0.IdsRep.pIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.IdsRep.pIn

/-- info: 'STACS2027.RAM.R0.KeepMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.KeepMem

/-- info: 'STACS2027.RAM.R0.KGlob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.KGlob

/-- info: 'STACS2027.RAM.R0.pairLeads_r0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.pairLeads_r0

/-- info: 'STACS2027.RAM.R0.KeepInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.KeepInv

/-- info: 'STACS2027.RAM.R0.KeepMem.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.KeepMem.add

/-- info: 'STACS2027.RAM.R0.KeepMem.skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.KeepMem.skip

/-- info: 'STACS2027.RAM.R0.keepBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.keepBody_spec

/-- info: 'STACS2027.RAM.R0.stepKeep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.stepKeep_spec

/-- info: 'STACS2027.RAM.R0.rI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.rI

/-- info: 'STACS2027.RAM.R0.r2M' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.r2M

/-- info: 'STACS2027.RAM.R0.rP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.rP

/-- info: 'STACS2027.RAM.R0.rA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.rA

/-- info: 'STACS2027.RAM.R0.rB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.rB

/-- info: 'STACS2027.RAM.R0.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.rX

/-- info: 'STACS2027.RAM.R0.rQ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.rQ

/-- info: 'STACS2027.RAM.R0.rY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.rY

/-- info: 'STACS2027.RAM.R0.rU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.rU

/-- info: 'STACS2027.RAM.R0.rV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.rV

/-- info: 'STACS2027.RAM.R0.maxInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.maxInit

/-- info: 'STACS2027.RAM.R0.maxBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.maxBody

/-- info: 'STACS2027.RAM.R0.stepMax' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.stepMax

/-- info: 'STACS2027.RAM.R0.stepLayout' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.stepLayout

/-- info: 'STACS2027.RAM.R0.readPair' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.readPair

/-- info: 'STACS2027.RAM.R0.visit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.visit

/-- info: 'STACS2027.RAM.R0.labBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.labBody

/-- info: 'STACS2027.RAM.R0.stepLabels' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.stepLabels

/-- info: 'STACS2027.RAM.R0.edgeIds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.edgeIds

/-- info: 'STACS2027.RAM.R0.idsIns' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.idsIns

/-- info: 'STACS2027.RAM.R0.idsBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.idsBody

/-- info: 'STACS2027.RAM.R0.idsInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.idsInit

/-- info: 'STACS2027.RAM.R0.stepIds' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.stepIds

/-- info: 'STACS2027.RAM.R0.keepAdd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.keepAdd

/-- info: 'STACS2027.RAM.R0.keepBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.keepBody

/-- info: 'STACS2027.RAM.R0.stepKeep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.stepKeep

/-- info: 'STACS2027.RAM.R0.r0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.r0

/-- info: 'STACS2027.RAM.R0.baseD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.baseD

/-- info: 'STACS2027.RAM.R0.baseLB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.baseLB

/-- info: 'STACS2027.RAM.R0.baseEU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.baseEU

/-- info: 'STACS2027.RAM.R0.baseEV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.baseEV

/-- info: 'STACS2027.RAM.R0.basePU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.basePU

/-- info: 'STACS2027.RAM.R0.basePV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.basePV

/-- info: 'STACS2027.RAM.R0.baseB2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.baseB2

/-- info: 'STACS2027.RAM.R0.endR0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.endR0

/-- info: 'STACS2027.RAM.R0.layout_eqs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.layout_eqs

/-- info: 'STACS2027.RAM.R0.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.fits

/-- info: 'STACS2027.RAM.R0.endR0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.endR0_le

/-- info: 'STACS2027.RAM.R0.Glob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.Glob

/-- info: 'STACS2027.RAM.R0.W0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.W0

/-- info: 'STACS2027.RAM.R0.Glob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.Glob.regIndep

/-- info: 'STACS2027.RAM.R0.MaxInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.MaxInv

/-- info: 'STACS2027.RAM.R0.maxInit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.maxInit_spec

/-- info: 'STACS2027.RAM.R0.maxBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.maxBody_spec

/-- info: 'STACS2027.RAM.R0.stepMax_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.stepMax_spec

/-- info: 'STACS2027.RAM.R0.maxInv_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.maxInv_full

/-- info: 'STACS2027.RAM.R0.LabMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.LabMem

/-- info: 'STACS2027.RAM.R0.LabRep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.LabRep

/-- info: 'STACS2027.RAM.R0.LabRep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.LabRep.indep

/-- info: 'STACS2027.RAM.R0.stepLayout_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.stepLayout_spec

/-- info: 'STACS2027.RAM.R0.LabMem.snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.LabMem.snoc

/-- info: 'STACS2027.RAM.R0.visit_wregs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.visit_wregs

/-- info: 'STACS2027.RAM.R0.visit_wregs_W0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.visit_wregs_W0

/-- info: 'STACS2027.RAM.R0.loopFree_visit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.loopFree_visit

/-- info: 'STACS2027.RAM.R0.visit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.visit_run

/-- info: 'STACS2027.RAM.R0.readPair_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.readPair_run

/-- info: 'STACS2027.RAM.R0.readPair_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.readPair_addrOK

/-- info: 'STACS2027.RAM.R0.LabInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.LabInv

/-- info: 'STACS2027.RAM.R0.labBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.labBody_spec

/-- info: 'STACS2027.RAM.R0.stepLabels_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.stepLabels_spec

/-- info: 'STACS2027.RAM.R0.ext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.ext

/-- info: 'STACS2027.RAM.R0.eraseDups_append_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.eraseDups_append_singleton

/-- info: 'STACS2027.RAM.R0.mem_ext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.mem_ext

/-- info: 'STACS2027.RAM.R0.length_ext_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.length_ext_le

/-- info: 'STACS2027.RAM.R0.length_eraseDups_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.length_eraseDups_le

/-- info: 'STACS2027.RAM.R0.ents' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.ents

/-- info: 'STACS2027.RAM.R0.maxLab' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.maxLab

/-- info: 'STACS2027.RAM.R0.length_ents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.length_ents

/-- info: 'STACS2027.RAM.R0.graphInput_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.graphInput_eq

/-- info: 'STACS2027.RAM.R0.foldl_max_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.foldl_max_take_succ

/-- info: 'STACS2027.RAM.R0.le_foldl_max_init' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.le_foldl_max_init

/-- info: 'STACS2027.RAM.R0.le_foldl_max' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.le_foldl_max

/-- info: 'STACS2027.RAM.R0.le_maxLab' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.le_maxLab

/-- info: 'STACS2027.RAM.R0.mem_ents_of_proper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.mem_ents_of_proper

/-- info: 'STACS2027.RAM.R0.pair_mem_ents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.pair_mem_ents

/-- info: 'STACS2027.RAM.R0.labels_le_maxLab' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.labels_le_maxLab

/-- info: 'STACS2027.RAM.R0.graphInput_getD_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.graphInput_getD_succ

/-- info: 'STACS2027.RAM.R0.ents_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.ents_pair

/-- info: 'STACS2027.RAM.R0.input_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.input_pair

/-- info: 'STACS2027.RAM.R0.length_le_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.length_le_ext

/-- info: 'STACS2027.RAM.R0.proper_take_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.proper_take_succ

/-- info: 'STACS2027.RAM.R0.labels_take_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.labels_take_succ

/-- info: 'STACS2027.RAM.R0.labels_take_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.labels_take_length

/-- info: 'STACS2027.RAM.R0.length_labels_take_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.length_labels_take_le

/-- info: 'STACS2027.RAM.R0.numV_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.numV_le

/-- info: 'STACS2027.RAM.R0.edgesPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.edgesPre

/-- info: 'STACS2027.RAM.R0.edgesPre_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.edgesPre_succ

/-- info: 'STACS2027.RAM.R0.edgesPre_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.edgesPre_zero

/-- info: 'STACS2027.RAM.R0.edgesPre_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.edgesPre_length

/-- info: 'STACS2027.RAM.R0.length_edgesPre_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.length_edgesPre_le

/-- info: 'STACS2027.RAM.R0.length_idEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.length_idEdges_le

/-- info: 'STACS2027.RAM.R0.edgesPre_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.edgesPre_below

/-- info: 'STACS2027.RAM.R0.dictOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.dictOf

/-- info: 'STACS2027.RAM.R0.dictOf_eq_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.dictOf_eq_zero_iff

/-- info: 'STACS2027.RAM.R0.dictOf_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.dictOf_nil

/-- info: 'STACS2027.RAM.R0.dictOf_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.dictOf_snoc

/-- info: 'STACS2027.RAM.R0.dictOf_ext_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.dictOf_ext_of_mem

/-- info: 'STACS2027.RAM.R0.ext_of_not_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.ext_of_not_mem

/-- info: 'STACS2027.RAM.R0.ext_of_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.ext_of_mem

/-- info: 'STACS2027.RAM.R0.dictOf_labels' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.dictOf_labels

/-- info: 'STACS2027.RAM.R0.labelBound_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.labelBound_eq

/-- info: 'STACS2027.RAM.R0.idPairs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.idPairs

/-- info: 'STACS2027.RAM.R0.idEdges_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.idEdges_eq

/-- info: 'STACS2027.RAM.R0.pairsPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.pairsPre

/-- info: 'STACS2027.RAM.R0.pairsPre_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.pairsPre_zero

/-- info: 'STACS2027.RAM.R0.pairsPre_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.pairsPre_succ

/-- info: 'STACS2027.RAM.R0.pairsPre_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.pairsPre_length

/-- info: 'STACS2027.RAM.R0.length_pairsPre_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.length_pairsPre_le

/-- info: 'STACS2027.RAM.R0.length_idPairs_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.length_idPairs_le

/-- info: 'STACS2027.RAM.R0.idPairs_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R0.idPairs_below

/-- info: 'STACS2027.RAM.R1.C1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.C1

/-- info: 'STACS2027.RAM.R1.r1_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.r1_wregs

/-- info: 'STACS2027.RAM.R1.r1_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.r1_writes

/-- info: 'STACS2027.RAM.R1.r1_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.r1_core

/-- info: 'STACS2027.RAM.R1.post_of_dfsRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.post_of_dfsRep

/-- info: 'STACS2027.RAM.R1.r1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.r1_spec

/-- info: 'STACS2027.RAM.R1.DfsMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.DfsMem

/-- info: 'STACS2027.RAM.R1.DfsRep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.DfsRep

/-- info: 'STACS2027.RAM.R1.DfsRep.indep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.DfsRep.indep

/-- info: 'STACS2027.RAM.R1.DfsMem.visit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.DfsMem.visit

/-- info: 'STACS2027.RAM.R1.DfsMem.bump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.DfsMem.bump

/-- info: 'STACS2027.RAM.R1.DfsMem.pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.DfsMem.pop

/-- info: 'STACS2027.RAM.R1.DfsMem.setRs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.DfsMem.setRs

/-- info: 'STACS2027.RAM.R1.wregs_visit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.wregs_visit

/-- info: 'STACS2027.RAM.R1.loopFree_visit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.loopFree_visit

/-- info: 'STACS2027.RAM.R1.visit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.visit_run

/-- info: 'STACS2027.RAM.R1.incRoot_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.incRoot_run

/-- info: 'STACS2027.RAM.R1.rootStep_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rootStep_run

/-- info: 'STACS2027.RAM.R1.topRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.topRead_run

/-- info: 'STACS2027.RAM.R1.advRead_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.advRead_run

/-- info: 'STACS2027.RAM.R1.pop_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.pop_run

/-- info: 'STACS2027.RAM.R1.topStep_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.topStep_run

/-- info: 'STACS2027.RAM.R1.dfsBody_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.dfsBody_run

/-- info: 'STACS2027.RAM.R1.dfsCond_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.dfsCond_run

/-- info: 'STACS2027.RAM.R1.visit_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.visit_addrOK

/-- info: 'STACS2027.RAM.R1.rootStep_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rootStep_addrOK

/-- info: 'STACS2027.RAM.R1.length_stk_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.length_stk_le

/-- info: 'STACS2027.RAM.R1.topRead_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.topRead_addrOK

/-- info: 'STACS2027.RAM.R1.advRead_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.advRead_addrOK

/-- info: 'STACS2027.RAM.R1.topStep_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.topStep_addrOK

/-- info: 'STACS2027.RAM.R1.dfsBody_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.dfsBody_addrOK

/-- info: 'STACS2027.RAM.R1.absOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.absOf

/-- info: 'STACS2027.RAM.R1.muC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.muC

/-- info: 'STACS2027.RAM.R1.muC_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.muC_eq

/-- info: 'STACS2027.RAM.R1.LoopInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.LoopInv

/-- info: 'STACS2027.RAM.R1.dfsRound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.dfsRound_spec

/-- info: 'STACS2027.RAM.R1.dfsInit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.dfsInit_spec

/-- info: 'STACS2027.RAM.R1.stepDfs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.stepDfs_spec

/-- info: 'STACS2027.RAM.R1.rI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rI

/-- info: 'STACS2027.RAM.R1.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rX

/-- info: 'STACS2027.RAM.R1.rY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rY

/-- info: 'STACS2027.RAM.R1.rU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rU

/-- info: 'STACS2027.RAM.R1.rV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rV

/-- info: 'STACS2027.RAM.R1.rP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rP

/-- info: 'STACS2027.RAM.R1.rA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rA

/-- info: 'STACS2027.RAM.R1.rB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rB

/-- info: 'STACS2027.RAM.R1.rW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rW

/-- info: 'STACS2027.RAM.R1.rAcc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rAcc

/-- info: 'STACS2027.RAM.R1.rDEG' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rDEG

/-- info: 'STACS2027.RAM.R1.rFIL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rFIL

/-- info: 'STACS2027.RAM.R1.rR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rR

/-- info: 'STACS2027.RAM.R1.alloc1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.alloc1

/-- info: 'STACS2027.RAM.R1.readEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.readEdge

/-- info: 'STACS2027.RAM.R1.bump' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bump

/-- info: 'STACS2027.RAM.R1.degBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.degBody

/-- info: 'STACS2027.RAM.R1.stepDeg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.stepDeg

/-- info: 'STACS2027.RAM.R1.preBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.preBody

/-- info: 'STACS2027.RAM.R1.stepPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.stepPre

/-- info: 'STACS2027.RAM.R1.put' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.put

/-- info: 'STACS2027.RAM.R1.fillBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.fillBody

/-- info: 'STACS2027.RAM.R1.stepFill' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.stepFill

/-- info: 'STACS2027.RAM.R1.visit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.visit

/-- info: 'STACS2027.RAM.R1.rootStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.rootStep

/-- info: 'STACS2027.RAM.R1.topRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.topRead

/-- info: 'STACS2027.RAM.R1.advRead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.advRead

/-- info: 'STACS2027.RAM.R1.advance' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.advance

/-- info: 'STACS2027.RAM.R1.topStep' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.topStep

/-- info: 'STACS2027.RAM.R1.dfsBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.dfsBody

/-- info: 'STACS2027.RAM.R1.dfsCond' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.dfsCond

/-- info: 'STACS2027.RAM.R1.dfsInit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.dfsInit

/-- info: 'STACS2027.RAM.R1.stepDfs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.stepDfs

/-- info: 'STACS2027.RAM.R1.stepCsr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.stepCsr

/-- info: 'STACS2027.RAM.R1.r1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.r1

/-- info: 'STACS2027.RAM.R1.bOFF' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bOFF

/-- info: 'STACS2027.RAM.R1.bFIL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bFIL

/-- info: 'STACS2027.RAM.R1.bADJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bADJ

/-- info: 'STACS2027.RAM.R1.bPRE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bPRE

/-- info: 'STACS2027.RAM.R1.bPAR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bPAR

/-- info: 'STACS2027.RAM.R1.bPTR' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bPTR

/-- info: 'STACS2027.RAM.R1.bORD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bORD

/-- info: 'STACS2027.RAM.R1.bSTK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bSTK

/-- info: 'STACS2027.RAM.R1.endL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.endL

/-- info: 'STACS2027.RAM.R1.layout_eqs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.layout_eqs

/-- info: 'STACS2027.RAM.R1.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.fits

/-- info: 'STACS2027.RAM.R1.endL_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.endL_le

/-- info: 'STACS2027.RAM.R1.Glob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.Glob

/-- info: 'STACS2027.RAM.R1.W1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.W1

/-- info: 'STACS2027.RAM.R1.Glob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.Glob.regIndep

/-- info: 'STACS2027.RAM.R1.edge_ends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.edge_ends

/-- info: 'STACS2027.RAM.R1.DegMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.DegMem

/-- info: 'STACS2027.RAM.R1.DegInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.DegInv

/-- info: 'STACS2027.RAM.R1.alloc1_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.alloc1_spec

/-- info: 'STACS2027.RAM.R1.readEdge_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.readEdge_run

/-- info: 'STACS2027.RAM.R1.DegMem.bmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.DegMem.bmp

/-- info: 'STACS2027.RAM.R1.loopFree_bump' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.loopFree_bump

/-- info: 'STACS2027.RAM.R1.wregs_bump' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.wregs_bump

/-- info: 'STACS2027.RAM.R1.bump_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bump_run

/-- info: 'STACS2027.RAM.R1.degBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.degBody_spec

/-- info: 'STACS2027.RAM.R1.stepDeg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.stepDeg_spec

/-- info: 'STACS2027.RAM.R1.PreMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.PreMem

/-- info: 'STACS2027.RAM.R1.PreInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.PreInv

/-- info: 'STACS2027.RAM.R1.PreMem.snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.PreMem.snoc

/-- info: 'STACS2027.RAM.R1.preBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.preBody_spec

/-- info: 'STACS2027.RAM.R1.stepPre_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.stepPre_spec

/-- info: 'STACS2027.RAM.R1.FillMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.FillMem

/-- info: 'STACS2027.RAM.R1.FillInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.FillInv

/-- info: 'STACS2027.RAM.R1.FillMem.app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.FillMem.app

/-- info: 'STACS2027.RAM.R1.loopFree_put' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.loopFree_put

/-- info: 'STACS2027.RAM.R1.wregs_put' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.wregs_put

/-- info: 'STACS2027.RAM.R1.put_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.put_run

/-- info: 'STACS2027.RAM.R1.readEdge_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.readEdge_addrOK

/-- info: 'STACS2027.RAM.R1.put_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.put_addrOK

/-- info: 'STACS2027.RAM.R1.fillBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.fillBody_spec

/-- info: 'STACS2027.RAM.R1.stepFill_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.stepFill_spec

/-- info: 'STACS2027.RAM.R1.CsrMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.CsrMem

/-- info: 'STACS2027.RAM.R1.CsrMem.upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.CsrMem.upd

/-- info: 'STACS2027.RAM.R1.stepCsr_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.stepCsr_spec

/-- info: 'STACS2027.RAM.R1.nbOf_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.nbOf_append

/-- info: 'STACS2027.RAM.R1.nbOf_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.nbOf_singleton

/-- info: 'STACS2027.RAM.R1.nbOf_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.nbOf_nil

/-- info: 'STACS2027.RAM.R1.nbOf_take_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.nbOf_take_succ

/-- info: 'STACS2027.RAM.R1.app' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.app

/-- info: 'STACS2027.RAM.R1.bmp' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bmp

/-- info: 'STACS2027.RAM.R1.nbOf_take_succ_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.nbOf_take_succ_eq

/-- info: 'STACS2027.RAM.R1.cnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.cnt

/-- info: 'STACS2027.RAM.R1.cnt_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.cnt_zero

/-- info: 'STACS2027.RAM.R1.cnt_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.cnt_full

/-- info: 'STACS2027.RAM.R1.length_nbOf_take_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.length_nbOf_take_le

/-- info: 'STACS2027.RAM.R1.cnt_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.cnt_le

/-- info: 'STACS2027.RAM.R1.length_app' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.length_app

/-- info: 'STACS2027.RAM.R1.cnt_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.cnt_succ

/-- info: 'STACS2027.RAM.R1.ps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.ps

/-- info: 'STACS2027.RAM.R1.ps_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.ps_zero

/-- info: 'STACS2027.RAM.R1.ps_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.ps_succ

/-- info: 'STACS2027.RAM.R1.ps_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.ps_mono

/-- info: 'STACS2027.RAM.R1.ps_add_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.ps_add_le

/-- info: 'STACS2027.RAM.R1.csrOff_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.csrOff_eq

/-- info: 'STACS2027.RAM.R1.length_csrAdj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.length_csrAdj

/-- info: 'STACS2027.RAM.R1.csrAdj_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.csrAdj_succ

/-- info: 'STACS2027.RAM.R1.arr_csrAdj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.arr_csrAdj

/-- info: 'STACS2027.RAM.R1.sum_indicator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.sum_indicator

/-- info: 'STACS2027.RAM.R1.length_nbOf_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.length_nbOf_cons

/-- info: 'STACS2027.RAM.R1.ps_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.ps_total

/-- info: 'STACS2027.RAM.R1.visitS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.visitS

/-- info: 'STACS2027.RAM.R1.bumpS' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.bumpS

/-- info: 'STACS2027.RAM.R1.step_push' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.step_push

/-- info: 'STACS2027.RAM.R1.step_exam' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.step_exam

/-- info: 'STACS2027.RAM.R1.step_pop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.step_pop

/-- info: 'STACS2027.RAM.R1.step_root' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.step_root

/-- info: 'STACS2027.RAM.R1.step_skip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.step_skip

/-- info: 'STACS2027.RAM.R1.drun_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.drun_add

/-- info: 'STACS2027.RAM.R1.drun_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.drun_succ

/-- info: 'STACS2027.RAM.R1.drun_eq_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.drun_eq_final

/-- info: 'STACS2027.RAM.R1.mu_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.mu_init

/-- info: 'STACS2027.RAM.R1.mu_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.mu_congr

/-- info: 'STACS2027.RAM.R1.lt_of_pre_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.lt_of_pre_ne

/-- info: 'STACS2027.RAM.R1.lt_of_mem_stk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.lt_of_mem_stk

/-- info: 'STACS2027.RAM.R1.length_stk_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.length_stk_lt

/-- info: 'STACS2027.RAM.R1.length_ord_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.length_ord_le

/-- info: 'STACS2027.RAM.R1.length_ord_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.length_ord_lt

/-- info: 'STACS2027.RAM.R1.idEdges_ps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.idEdges_ps

/-- info: 'STACS2027.RAM.R1.idEdges_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.idEdges_ne

/-- info: 'STACS2027.RAM.R1.idEdges_lt_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.idEdges_lt_get

/-- info: 'STACS2027.RAM.R1.lt_of_mem_nbOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R1.lt_of_mem_nbOf

/-- info: 'STACS2027.RAM.R2.HeadMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.HeadMem

/-- info: 'STACS2027.RAM.R2.HeadMem.upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.HeadMem.upd

/-- info: 'STACS2027.RAM.R2.HeadInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.HeadInv

/-- info: 'STACS2027.RAM.R2.headBody_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.headBody_mem

/-- info: 'STACS2027.RAM.R2.headBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.headBody_spec

/-- info: 'STACS2027.RAM.R2.stepHead_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.stepHead_spec

/-- info: 'STACS2027.RAM.R2.C2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.C2

/-- info: 'STACS2027.RAM.R2.r2_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.r2_wregs

/-- info: 'STACS2027.RAM.R2.r2_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.r2_writes

/-- info: 'STACS2027.RAM.R2.r2_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.r2_core

/-- info: 'STACS2027.RAM.R2.r2_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.r2_reg

/-- info: 'STACS2027.RAM.R2.post_of_headInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.post_of_headInv

/-- info: 'STACS2027.RAM.R2.r2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.r2_spec

/-- info: 'STACS2027.RAM.R2.rI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rI

/-- info: 'STACS2027.RAM.R2.rV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rV

/-- info: 'STACS2027.RAM.R2.rSK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rSK

/-- info: 'STACS2027.RAM.R2.rAcc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rAcc

/-- info: 'STACS2027.RAM.R2.rA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rA

/-- info: 'STACS2027.RAM.R2.rB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rB

/-- info: 'STACS2027.RAM.R2.rJ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rJ

/-- info: 'STACS2027.RAM.R2.rW' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rW

/-- info: 'STACS2027.RAM.R2.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rX

/-- info: 'STACS2027.RAM.R2.rY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rY

/-- info: 'STACS2027.RAM.R2.rP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rP

/-- info: 'STACS2027.RAM.R2.r2Alloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.r2Alloc

/-- info: 'STACS2027.RAM.R2.lowHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowHead

/-- info: 'STACS2027.RAM.R2.lowMin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowMin

/-- info: 'STACS2027.RAM.R2.lowInner' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowInner

/-- info: 'STACS2027.RAM.R2.lowBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowBody

/-- info: 'STACS2027.RAM.R2.stepLow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.stepLow

/-- info: 'STACS2027.RAM.R2.headElse' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.headElse

/-- info: 'STACS2027.RAM.R2.headBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.headBody

/-- info: 'STACS2027.RAM.R2.stepHead' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.stepHead

/-- info: 'STACS2027.RAM.R2.r2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.r2

/-- info: 'STACS2027.RAM.R2.Glob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.Glob

/-- info: 'STACS2027.RAM.R2.W2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.W2

/-- info: 'STACS2027.RAM.R2.Glob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.Glob.regIndep

/-- info: 'STACS2027.RAM.R2.endL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.endL

/-- info: 'STACS2027.RAM.R2.endL_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.endL_le

/-- info: 'STACS2027.RAM.R2.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.fits

/-- info: 'STACS2027.RAM.R2.rd_pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rd_pre

/-- info: 'STACS2027.RAM.R2.rd_par' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rd_par

/-- info: 'STACS2027.RAM.R2.rd_ord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rd_ord

/-- info: 'STACS2027.RAM.R2.rd_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rd_off

/-- info: 'STACS2027.RAM.R2.rd_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.rd_adj

/-- info: 'STACS2027.RAM.R2.LowMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.LowMem

/-- info: 'STACS2027.RAM.R2.LowMem.upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.LowMem.upd

/-- info: 'STACS2027.RAM.R2.LowInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.LowInv

/-- info: 'STACS2027.RAM.R2.r2Alloc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.r2Alloc_spec

/-- info: 'STACS2027.RAM.R2.InInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.InInv

/-- info: 'STACS2027.RAM.R2.lowHead_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowHead_spec

/-- info: 'STACS2027.RAM.R2.lowInner_acc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowInner_acc

/-- info: 'STACS2027.RAM.R2.lowInner_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowInner_spec

/-- info: 'STACS2027.RAM.R2.lowTail_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowTail_spec

/-- info: 'STACS2027.RAM.R2.lowBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowBody_spec

/-- info: 'STACS2027.RAM.R2.stepLow_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.stepLow_spec

/-- info: 'STACS2027.RAM.R2.dfs_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.dfs_inv

/-- info: 'STACS2027.RAM.R2.dfs_ordInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.dfs_ordInv

/-- info: 'STACS2027.RAM.R2.dfs_halted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.dfs_halted

/-- info: 'STACS2027.RAM.R2.pre_ne_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.pre_ne_of_lt

/-- info: 'STACS2027.RAM.R2.mem_ord_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.mem_ord_iff

/-- info: 'STACS2027.RAM.R2.ord_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.ord_perm

/-- info: 'STACS2027.RAM.R2.length_ord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.length_ord

/-- info: 'STACS2027.RAM.R2.par_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.par_lt

/-- info: 'STACS2027.RAM.R2.ord_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.ord_getD

/-- info: 'STACS2027.RAM.R2.ord_getD_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.ord_getD_lt

/-- info: 'STACS2027.RAM.R2.arr_csrAdj_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.arr_csrAdj_seg

/-- info: 'STACS2027.RAM.R2.vOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.vOf

/-- info: 'STACS2027.RAM.R2.vOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.vOf_lt

/-- info: 'STACS2027.RAM.R2.lowF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowF

/-- info: 'STACS2027.RAM.R2.lowF_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowF_zero

/-- info: 'STACS2027.RAM.R2.lowF_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowF_succ

/-- info: 'STACS2027.RAM.R2.lowF_full' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.lowF_full

/-- info: 'STACS2027.RAM.R2.skOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.skOf

/-- info: 'STACS2027.RAM.R2.accF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.accF

/-- info: 'STACS2027.RAM.R2.accF_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.accF_zero

/-- info: 'STACS2027.RAM.R2.accF_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.accF_full

/-- info: 'STACS2027.RAM.R2.accF_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.accF_succ

/-- info: 'STACS2027.RAM.R2.headF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.headF

/-- info: 'STACS2027.RAM.R2.headF_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.headF_zero

/-- info: 'STACS2027.RAM.R2.headF_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.headF_succ

/-- info: 'STACS2027.RAM.R2.headF_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.headF_full

/-- info: 'STACS2027.RAM.R2.sum_range_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.sum_range_getD

/-- info: 'STACS2027.RAM.R2.sum_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.sum_deg

/-- info: 'STACS2027.RAM.R2.base_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.base_transfer

/-- info: 'STACS2027.RAM.R2.r1_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R2.r1_transfer

/-- info: 'STACS2027.RAM.R3.C3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.C3

/-- info: 'STACS2027.RAM.R3.r3_wregs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.r3_wregs

/-- info: 'STACS2027.RAM.R3.r3_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.r3_writes

/-- info: 'STACS2027.RAM.R3.r3_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.r3_core

/-- info: 'STACS2027.RAM.R3.r3_reg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.r3_reg

/-- info: 'STACS2027.RAM.R3.post_of_fill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.post_of_fill

/-- info: 'STACS2027.RAM.R3.r3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.r3_spec

/-- info: 'STACS2027.RAM.R3.rI' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rI

/-- info: 'STACS2027.RAM.R3.rU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rU

/-- info: 'STACS2027.RAM.R3.rV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rV

/-- info: 'STACS2027.RAM.R3.rX' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rX

/-- info: 'STACS2027.RAM.R3.rY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rY

/-- info: 'STACS2027.RAM.R3.rL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rL

/-- info: 'STACS2027.RAM.R3.rK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rK

/-- info: 'STACS2027.RAM.R3.rAcc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rAcc

/-- info: 'STACS2027.RAM.R3.rP' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rP

/-- info: 'STACS2027.RAM.R3.rCNT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rCNT

/-- info: 'STACS2027.RAM.R3.rFIL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rFIL

/-- info: 'STACS2027.RAM.R3.r3Alloc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.r3Alloc

/-- info: 'STACS2027.RAM.R3.keyOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.keyOf

/-- info: 'STACS2027.RAM.R3.cntBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.cntBody

/-- info: 'STACS2027.RAM.R3.stepCnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.stepCnt

/-- info: 'STACS2027.RAM.R3.preBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.preBody

/-- info: 'STACS2027.RAM.R3.stepPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.stepPre

/-- info: 'STACS2027.RAM.R3.fillBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.fillBody

/-- info: 'STACS2027.RAM.R3.stepFill' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.stepFill

/-- info: 'STACS2027.RAM.R3.r3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.r3

/-- info: 'STACS2027.RAM.R3.bBST' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bBST

/-- info: 'STACS2027.RAM.R3.bFIL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bFIL

/-- info: 'STACS2027.RAM.R3.bBU' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bBU

/-- info: 'STACS2027.RAM.R3.bBV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bBV

/-- info: 'STACS2027.RAM.R3.endL' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.endL

/-- info: 'STACS2027.RAM.R3.layout_eqs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.layout_eqs

/-- info: 'STACS2027.RAM.R3.endL_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.endL_le

/-- info: 'STACS2027.RAM.R3.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.fits

/-- info: 'STACS2027.RAM.R3.Glob' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.Glob

/-- info: 'STACS2027.RAM.R3.W3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.W3

/-- info: 'STACS2027.RAM.R3.Glob.regIndep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.Glob.regIndep

/-- info: 'STACS2027.RAM.R3.rd_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.rd_head

/-- info: 'STACS2027.RAM.R3.keyOf_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.keyOf_run

/-- info: 'STACS2027.RAM.R3.keyOf_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.keyOf_addrOK

/-- info: 'STACS2027.RAM.R3.CntMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.CntMem

/-- info: 'STACS2027.RAM.R3.CntInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.CntInv

/-- info: 'STACS2027.RAM.R3.r3Alloc_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.r3Alloc_spec

/-- info: 'STACS2027.RAM.R3.CntMem.bmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.CntMem.bmp

/-- info: 'STACS2027.RAM.R3.cnt_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.cnt_succ

/-- info: 'STACS2027.RAM.R3.cntBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.cntBody_spec

/-- info: 'STACS2027.RAM.R3.stepCnt_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.stepCnt_spec

/-- info: 'STACS2027.RAM.R3.PreMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.PreMem

/-- info: 'STACS2027.RAM.R3.PreInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.PreInv

/-- info: 'STACS2027.RAM.R3.PreMem.snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.PreMem.snoc

/-- info: 'STACS2027.RAM.R3.preBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.preBody_spec

/-- info: 'STACS2027.RAM.R3.stepPre_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.stepPre_spec

/-- info: 'STACS2027.RAM.R3.FillMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.FillMem

/-- info: 'STACS2027.RAM.R3.FillInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.FillInv

/-- info: 'STACS2027.RAM.R3.FillMem.app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.FillMem.app

/-- info: 'STACS2027.RAM.R3.fillBody_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.fillBody_spec

/-- info: 'STACS2027.RAM.R3.stepFill_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.stepFill_spec

/-- info: 'STACS2027.RAM.R3.key' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.key

/-- info: 'STACS2027.RAM.R3.bk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bk

/-- info: 'STACS2027.RAM.R3.bs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bs

/-- info: 'STACS2027.RAM.R3.bk_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bk_zero

/-- info: 'STACS2027.RAM.R3.bk_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bk_succ

/-- info: 'STACS2027.RAM.R3.bk_succ_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bk_succ_eq

/-- info: 'STACS2027.RAM.R3.length_bk_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.length_bk_succ

/-- info: 'STACS2027.RAM.R3.length_bk_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.length_bk_le

/-- info: 'STACS2027.RAM.R3.bs_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bs_succ

/-- info: 'STACS2027.RAM.R3.bs_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bs_mono

/-- info: 'STACS2027.RAM.R3.bs_add_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bs_add_le

/-- info: 'STACS2027.RAM.R3.foldl_head_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.foldl_head_lt

/-- info: 'STACS2027.RAM.R3.headsOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.headsOf_lt

/-- info: 'STACS2027.RAM.R3.key_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.key_lt

/-- info: 'STACS2027.RAM.R3.key_get_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.key_get_lt

/-- info: 'STACS2027.RAM.R3.sum_length_filter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.sum_length_filter

/-- info: 'STACS2027.RAM.R3.bs_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bs_total

/-- info: 'STACS2027.RAM.R3.bs_add_le_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.bs_add_le_total

/-- info: 'STACS2027.RAM.R3.blocksOf_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.blocksOf_eq

/-- info: 'STACS2027.RAM.R3.blockStarts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.blockStarts_eq

/-- info: 'STACS2027.RAM.R3.flatten_blocksOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.flatten_blocksOf

/-- info: 'STACS2027.RAM.R3.flatten_fst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.flatten_fst

/-- info: 'STACS2027.RAM.R3.flatten_snd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.flatten_snd

/-- info: 'STACS2027.RAM.R3.length_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.length_flatten

/-- info: 'STACS2027.RAM.R3.arr_flatMap_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.R3.arr_flatMap_parts

/-- info: 'STACS2027.RAM.P1.getD_of_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.getD_of_lt

/-- info: 'STACS2027.RAM.P1.getD_append_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.getD_append_of_lt

/-- info: 'STACS2027.RAM.P1.sum_range_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sum_range_eq

/-- info: 'STACS2027.RAM.P1.sum_range_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sum_range_getD

/-- info: 'STACS2027.RAM.P1.bkt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.bkt

/-- info: 'STACS2027.RAM.P1.offOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.offOf

/-- info: 'STACS2027.RAM.P1.bucketIdx' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.bucketIdx

/-- info: 'STACS2027.RAM.P1.cntS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.cntS

/-- info: 'STACS2027.RAM.P1.bkt_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.bkt_zero

/-- info: 'STACS2027.RAM.P1.bkt_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.bkt_succ

/-- info: 'STACS2027.RAM.P1.length_bkt_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_bkt_succ

/-- info: 'STACS2027.RAM.P1.length_bkt_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_bkt_mono

/-- info: 'STACS2027.RAM.P1.mem_bkt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.mem_bkt

/-- info: 'STACS2027.RAM.P1.offOf_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.offOf_zero

/-- info: 'STACS2027.RAM.P1.offOf_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.offOf_succ

/-- info: 'STACS2027.RAM.P1.offOf_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.offOf_mono

/-- info: 'STACS2027.RAM.P1.sum_bkt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.sum_bkt

/-- info: 'STACS2027.RAM.P1.offOf_eq_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.offOf_eq_length

/-- info: 'STACS2027.RAM.P1.length_bucketIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_bucketIdx

/-- info: 'STACS2027.RAM.P1.lt_of_mem_bucketIdx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.lt_of_mem_bucketIdx

/-- info: 'STACS2027.RAM.P1.offOf_add_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.offOf_add_le

/-- info: 'STACS2027.RAM.P1.map_getD_filter_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.map_getD_filter_range

/-- info: 'STACS2027.RAM.P1.getD_map_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.getD_map_lt

/-- info: 'STACS2027.RAM.P1.map_bkt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.map_bkt

/-- info: 'STACS2027.RAM.P1.length_bkt_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.length_bkt_map

/-- info: 'STACS2027.RAM.P1.map_bucketIdx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.map_bucketIdx

/-- info: 'STACS2027.RAM.P1.bucketIdx_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.bucketIdx_succ

/-- info: 'STACS2027.RAM.P1.map_bucketIdx_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.map_bucketIdx_congr

/-- info: 'STACS2027.RAM.P1.offOf_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.P1.offOf_congr

/-- info: 'STACS2027.RAM.setReg_reg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.setReg_reg

/-- info: 'STACS2027.RAM.setReg_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.setReg_mem

/-- info: 'STACS2027.RAM.setReg_out' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.setReg_out

/-- info: 'STACS2027.RAM.setMem_reg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.setMem_reg

/-- info: 'STACS2027.RAM.setMem_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.setMem_mem

/-- info: 'STACS2027.RAM.setMem_out' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.setMem_out

/-- info: 'STACS2027.RAM.emit_reg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.emit_reg

/-- info: 'STACS2027.RAM.emit_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.emit_mem

/-- info: 'STACS2027.RAM.emit_out' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.emit_out

/-- info: 'STACS2027.RAM.LoopFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.LoopFree

/-- info: 'STACS2027.RAM.run' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run

/-- info: 'STACS2027.RAM.cost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.cost

/-- info: 'STACS2027.RAM.size' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.size

/-- info: 'STACS2027.RAM.exec_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.exec_run

/-- info: 'STACS2027.RAM.cost_le_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cost_le_size

/-- info: 'STACS2027.RAM.Sat' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Sat

/-- info: 'STACS2027.RAM.Sat.ofLoopFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Sat.ofLoopFree

/-- info: 'STACS2027.RAM.Sat.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Sat.mono

/-- info: 'STACS2027.RAM.Sat.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Sat.congr

/-- info: 'STACS2027.RAM.Sat.seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Sat.seq

/-- info: 'STACS2027.RAM.iterate' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.iterate

/-- info: 'STACS2027.RAM.Sat.loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.Sat.loop

/-- info: 'STACS2027.RAM.iterate_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.iterate_invariant

/-- info: 'STACS2027.RAM.seqs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.seqs

/-- info: 'STACS2027.RAM.loopFree_seqs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_seqs

/-- info: 'STACS2027.RAM.run_seqs_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_seqs_nil

/-- info: 'STACS2027.RAM.run_seqs_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_seqs_cons

/-- info: 'STACS2027.RAM.size_seqs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.size_seqs

/-- info: 'STACS2027.Reach' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Reach

/-- info: 'STACS2027.WalkWithin.mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WalkWithin.mem

/-- info: 'STACS2027.WalkWithin.snoc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.WalkWithin.snoc

/-- info: 'STACS2027.WalkWithin.reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.WalkWithin.reverse

/-- info: 'STACS2027.Reach.left' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Reach.left

/-- info: 'STACS2027.Reach.right' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Reach.right

/-- info: 'STACS2027.Reach.edge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Reach.edge

/-- info: 'STACS2027.Reach.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Reach.trans

/-- info: 'STACS2027.Reach.symm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Reach.symm

/-- info: 'STACS2027.Reach.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Reach.mono

/-- info: 'STACS2027.Reach.graph_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Reach.graph_mono

/-- info: 'STACS2027.reach_of_walk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.reach_of_walk

/-- info: 'STACS2027.walk_of_reach' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.walk_of_reach

/-- info: 'STACS2027.connectedWithin_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.connectedWithin_iff

/-- info: 'STACS2027.connectedWithin_of_hub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.connectedWithin_of_hub

/-- info: 'STACS2027.IsRPath' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsRPath

/-- info: 'STACS2027.IsRPath.pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsRPath.pairwise

/-- info: 'STACS2027.IsRPath.head_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsRPath.head_mem

/-- info: 'STACS2027.IsRPath.last_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.IsRPath.last_mem

/-- info: 'STACS2027.IsRPath.bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsRPath.bounds

/-- info: 'STACS2027.IsRPath.two_le_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsRPath.two_le_length

/-- info: 'STACS2027.IsRPath.eq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsRPath.eq_singleton

/-- info: 'STACS2027.isRPath_pair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.isRPath_pair

/-- info: 'STACS2027.isRPath_side_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isRPath_side_iff

/-- info: 'STACS2027.exists_straddle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_straddle

/-- info: 'STACS2027.Joins' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Joins

/-- info: 'STACS2027.Joins.head?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Joins.head?

/-- info: 'STACS2027.Joins.isRPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Joins.isRPath

/-- info: 'STACS2027.Joins.mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Joins.mem

/-- info: 'STACS2027.Joins.length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Joins.length_le

/-- info: 'STACS2027.joins_iff_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.joins_iff_slots

/-- info: 'STACS2027.joins_of_superset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.joins_of_superset

/-- info: 'STACS2027.isChain_rstep_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isChain_rstep_iff

/-- info: 'STACS2027.convexCycle_iff_isRPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.convexCycle_iff_isRPath

/-- info: 'STACS2027.IsPolygon.isRPath_iff_joins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.isRPath_iff_joins

/-- info: 'STACS2027.IsPolygon.isRPath_iff_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.isRPath_iff_slots

/-- info: 'STACS2027.IsPolygon.faceVerts_isRPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.faceVerts_isRPath

/-- info: 'STACS2027.IsPolygon.faceVerts_convexCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.faceVerts_convexCycle

/-- info: 'STACS2027.rootLeafDelete' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.rootLeafDelete

/-- info: 'STACS2027.IsPolygon.within_unique_root_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.within_unique_root_child

/-- info: 'STACS2027.IsPolygon.root_leaf_face_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_face_vertices

/-- info: 'STACS2027.IsPolygon.root_leaf_delete_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_delete_hamiltonian

/-- info: 'STACS2027.IsPolygon.root_leaf_delete_twoConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_delete_twoConnected

/-- info: 'STACS2027.IsPolygon.root_leaf_delete_outerplanar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_delete_outerplanar

/-- info: 'STACS2027.IsPolygon.root_leaf_incident_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_incident_face

/-- info: 'STACS2027.IsPolygon.root_leaf_retained_face_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_retained_face_edge

/-- info: 'STACS2027.IsPolygon.root_leaf_delete_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_delete_edges

/-- info: 'STACS2027.IsPolygon.root_leaf_unique_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_unique_chord

/-- info: 'STACS2027.IsPolygon.root_leaf_inner_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_inner_degree

/-- info: 'STACS2027.IsPolygon.root_leaf_delete_faces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_delete_faces

/-- info: 'STACS2027.IsPolygon.root_leaf_delete_face_bijection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_delete_face_bijection

/-- info: 'STACS2027.IsPolygon.root_leaf_delete_weakDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_leaf_delete_weakDual

/-- info: 'STACS2027.Within' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Within

/-- info: 'STACS2027.Within.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Within.refl

/-- info: 'STACS2027.Within.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Within.trans

/-- info: 'STACS2027.Within.antisymm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Within.antisymm

/-- info: 'STACS2027.IsPolygon.laminar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.laminar

/-- info: 'STACS2027.IsPolygon.segs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.segs

/-- info: 'STACS2027.IsPolygon.mem_segs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_segs

/-- info: 'STACS2027.IsPolygon.root_mem_segs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root_mem_segs

/-- info: 'STACS2027.IsPolygon.within_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.within_root

/-- info: 'STACS2027.IsPolygon.nested_of_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.nested_of_within

/-- info: 'STACS2027.IsPolygon.Seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.Seg

/-- info: 'STACS2027.IsPolygon.IsChild' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.IsChild

/-- info: 'STACS2027.IsPolygon.segSize' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.segSize

/-- info: 'STACS2027.IsPolygon.exists_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.exists_child

/-- info: 'STACS2027.IsPolygon.child_size_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.child_size_lt

/-- info: 'STACS2027.IsPolygon.child_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.child_disjoint

/-- info: 'STACS2027.IsPolygon.segTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.segTree

/-- info: 'STACS2027.IsPolygon.root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.root

/-- info: 'STACS2027.IsPolygon.mem_sub_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_sub_root

/-- info: 'STACS2027.IsPolygon.mem_sub_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_sub_iff

/-- info: 'STACS2027.IsPolygon.mem_children_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_children_iff

/-- info: 'STACS2027.ConvexCycle.head_lt_getLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.ConvexCycle.head_lt_getLast

/-- info: 'STACS2027.IsPolygon.top_mem_segs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.top_mem_segs

/-- info: 'STACS2027.IsPolygon.mem_within_head_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_within_head_last

/-- info: 'STACS2027.IsPolygon.containing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.containing

/-- info: 'STACS2027.IsPolygon.exists_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.exists_own

/-- info: 'STACS2027.IsPolygon.own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.own

/-- info: 'STACS2027.IsPolygon.own_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.own_spec

/-- info: 'STACS2027.IsPolygon.own_of_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.own_of_seg

/-- info: 'STACS2027.IsPolygon.own_within_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.own_within_iff

/-- info: 'STACS2027.hasAssignment_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_proper

/-- info: 'STACS2027.isMinCost_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isMinCost_proper

/-- info: 'STACS2027.posGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.posGraph

/-- info: 'STACS2027.mem_posGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_posGraph

/-- info: 'STACS2027.posGraph_normalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.posGraph_normalized

/-- info: 'STACS2027.adj_posGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.adj_posGraph

/-- info: 'STACS2027.edge_getD_mem_pathEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.edge_getD_mem_pathEdges

/-- info: 'STACS2027.OuterplanarHam.adj_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.adj_succ

/-- info: 'STACS2027.OuterplanarHam.adj_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OuterplanarHam.adj_wrap

/-- info: 'STACS2027.isPolygon_posGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isPolygon_posGraph

/-- info: 'STACS2027.posGraph_relabel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.posGraph_relabel

/-- info: 'STACS2027.hasAssignment_posGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.hasAssignment_posGraph

/-- info: 'STACS2027.isMinCost_posGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.isMinCost_posGraph

/-- info: 'STACS2027.TreeDP.Tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Tree

/-- info: 'STACS2027.TreeDP.Tree.eq_of_mem_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Tree.eq_of_mem_sub

/-- info: 'STACS2027.TreeDP.Tree.mem_child_of_mem_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Tree.mem_child_of_mem_sub

/-- info: 'STACS2027.TreeDP.Tree.child_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Tree.child_unique

/-- info: 'STACS2027.TreeDP.Problem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem

/-- info: 'STACS2027.TreeDP.Problem.loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.loc

/-- info: 'STACS2027.TreeDP.Problem.tot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.tot

/-- info: 'STACS2027.TreeDP.Problem.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.total

/-- info: 'STACS2027.TreeDP.Problem.upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.upd

/-- info: 'STACS2027.TreeDP.Problem.ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.ext

/-- info: 'STACS2027.TreeDP.Problem.tot_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.tot_split

/-- info: 'STACS2027.TreeDP.Problem.loc_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.loc_ext

/-- info: 'STACS2027.TreeDP.Problem.tot_ext_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.tot_ext_child

/-- info: 'STACS2027.TreeDP.Problem.dp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.dp

/-- info: 'STACS2027.TreeDP.Problem.dp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.dp_eq

/-- info: 'STACS2027.TreeDP.Problem.dp_eq_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.dp_eq_min

/-- info: 'STACS2027.TreeDP.Problem.dp_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.dp_root

/-- info: 'STACS2027.TreeDP.Problem.boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.boundary

/-- info: 'STACS2027.TreeDP.Problem.dp_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.dp_congr

/-- info: 'STACS2027.TreeDP.Problem.top_eq_or_mem_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.top_eq_or_mem_boundary

/-- info: 'STACS2027.TreeDP.Problem.boundary_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TreeDP.Problem.boundary_child

/-- info: 'STACS2027.TriangleMatching.edge_mem_vertexSides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.edge_mem_vertexSides

/-- info: 'STACS2027.TriangleMatching.edge_mem_edgeVertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.edge_mem_edgeVertices

/-- info: 'STACS2027.TriangleMatching.identifyTriangle_eq_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyTriangle_eq_of_not_mem

/-- info: 'STACS2027.TriangleMatching.identifyTriangle_eq_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyTriangle_eq_of_mem

/-- info: 'STACS2027.TriangleMatching.identifyVertex_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyVertex_injOn

/-- info: 'STACS2027.TriangleMatching.identifyFamily_isTriangles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyFamily_isTriangles

/-- info: 'STACS2027.TriangleMatching.mixed_collision_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.mixed_collision_exceptional

/-- info: 'STACS2027.TriangleMatching.surviving_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.surviving_collision

/-- info: 'STACS2027.TriangleMatching.thirdVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.thirdVertex

/-- info: 'STACS2027.TriangleMatching.collapsed_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.collapsed_shape

/-- info: 'STACS2027.TriangleMatching.collapsed_card_le_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.collapsed_card_le_common

/-- info: 'STACS2027.TriangleMatching.identifyFamily_card_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyFamily_card_bound

/-- info: 'STACS2027.TriangleMatching.identifyFamily_sideUnion_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyFamily_sideUnion_subset

/-- info: 'STACS2027.TriangleMatching.canonicalEdge_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.canonicalEdge_eq

/-- info: 'STACS2027.TriangleMatching.identifyVertex_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyVertex_eq_iff

/-- info: 'STACS2027.TriangleMatching.identifyEdge_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyEdge_collision

/-- info: 'STACS2027.TriangleMatching.mem_commonVertices_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.mem_commonVertices_iff

/-- info: 'STACS2027.TriangleMatching.identifyEdge_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyEdge_map

/-- info: 'STACS2027.TriangleMatching.identifyEdges_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyEdges_card

/-- info: 'STACS2027.TriangleMatching.vertexSides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.vertexSides

/-- info: 'STACS2027.TriangleMatching.VertexTriangleFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.VertexTriangleFamily

/-- info: 'STACS2027.TriangleMatching.vertexSideUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.vertexSideUnion

/-- info: 'STACS2027.TriangleMatching.vertexFamilyGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.vertexFamilyGraph

/-- info: 'STACS2027.TriangleMatching.edgeVertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.edgeVertices

/-- info: 'STACS2027.TriangleMatching.commonVertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.commonVertices

/-- info: 'STACS2027.TriangleMatching.identifyVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyVertex

/-- info: 'STACS2027.TriangleMatching.identifyTriangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyTriangle

/-- info: 'STACS2027.TriangleMatching.identifyFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyFamily

/-- info: 'STACS2027.TriangleMatching.identifyEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyEdges

/-- info: 'STACS2027.TriangleMatching.card_le_image_add_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.card_le_image_add_exceptional

/-- info: 'STACS2027.TriangleMatching.card_le_image_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.card_le_image_add_one

/-- info: 'STACS2027.TriangleMatching.triangle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.triangle

/-- info: 'STACS2027.TriangleMatching.triangle_isCycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.triangle_isCycle

/-- info: 'STACS2027.TriangleMatching.triangle_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.triangle_shape

/-- info: 'STACS2027.TriangleMatching.mem_triangle_paths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.mem_triangle_paths

/-- info: 'STACS2027.TriangleMatching.getD_map_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.getD_map_range

/-- info: 'STACS2027.TriangleMatching.validChoices_of_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.validChoices_of_getD

/-- info: 'STACS2027.TriangleMatching.triangleSides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.triangleSides

/-- info: 'STACS2027.TriangleMatching.TriangleSideHall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.TriangleSideHall

/-- info: 'STACS2027.TriangleMatching.triangle_distinct_sides_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.triangle_distinct_sides_iff

/-- info: 'STACS2027.TriangleMatching.triangle_assignment_of_distinct_sides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.triangle_assignment_of_distinct_sides

/-- info: 'STACS2027.TriangleMatching.triangle_perfect_of_hall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.triangle_perfect_of_hall

/-- info: 'STACS2027.TriangleMatching.identifyEdges_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyEdges_planar

/-- info: 'STACS2027.TriangleMatching.identifyEdges_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.identifyEdges_proper

/-- info: 'STACS2027.TriangleMatching.enumeratedVertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.enumeratedVertices

/-- info: 'STACS2027.TriangleMatching.enumeratedFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.enumeratedFamily

/-- info: 'STACS2027.TriangleMatching.triangle_vertexSides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.triangle_vertexSides

/-- info: 'STACS2027.TriangleMatching.enumeratedVertices_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.enumeratedVertices_sides

/-- info: 'STACS2027.TriangleMatching.enumeratedVertices_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.enumeratedVertices_injective

/-- info: 'STACS2027.TriangleMatching.enumeratedFamily_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.enumeratedFamily_card

/-- info: 'STACS2027.TriangleMatching.enumeratedFamily_triangles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.enumeratedFamily_triangles

/-- info: 'STACS2027.TriangleMatching.enumeratedFamily_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.enumeratedFamily_edges

/-- info: 'STACS2027.TriangleMatching.vertexSides_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.vertexSides_proper

/-- info: 'STACS2027.TriangleMatching.enumeratedFamily_graph_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.TriangleMatching.enumeratedFamily_graph_planar

/-- info: 'STACS2027.K23Struct.walkWithin_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.walkWithin_iff

/-- info: 'STACS2027.K23Struct.reach_head_of_isChain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.reach_head_of_isChain

/-- info: 'STACS2027.K23Struct.connectedWithin_of_isChain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.connectedWithin_of_isChain

/-- info: 'STACS2027.K23Struct.exists_adj_of_infix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.exists_adj_of_infix

/-- info: 'STACS2027.K23Struct.exists_adj_of_infix_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.exists_adj_of_infix_rev

/-- info: 'STACS2027.Reach.exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Reach.exit

/-- info: 'STACS2027.Reach.exists_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Reach.exists_path

/-- info: 'STACS2027.K23Struct.mem_of_head?' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.K23Struct.mem_of_head?

/-- info: 'STACS2027.K23Struct.mem_of_getLast?' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.mem_of_getLast?

/-- info: 'STACS2027.K23Struct.isChain_cons_append_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.isChain_cons_append_singleton

/-- info: 'STACS2027.K23Struct.vertList' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.K23Struct.vertList

/-- info: 'STACS2027.K23Struct.mem_vertList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.mem_vertList

/-- info: 'STACS2027.K23Struct.IsCyc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.K23Struct.IsCyc

/-- info: 'STACS2027.K23Struct.isCyc_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.isCyc_cons

/-- info: 'STACS2027.K23Struct.IsCyc.append_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.IsCyc.append_comm

/-- info: 'STACS2027.K23Struct.isVertex_of_isChain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.isVertex_of_isChain

/-- info: 'STACS2027.K23Struct.IsCyc.isVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.IsCyc.isVertex

/-- info: 'STACS2027.K23Struct.IsCyc.length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.IsCyc.length_le

/-- info: 'STACS2027.K23Struct.pathEdges_mem_of_isChain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.pathEdges_mem_of_isChain

/-- info: 'STACS2027.K23Struct.IsCyc.isCycle' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.IsCyc.isCycle

/-- info: 'STACS2027.K23Struct.IsCyc.extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.IsCyc.extend

/-- info: 'STACS2027.K23Struct.hasMinor_k23_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.hasMinor_k23_of

/-- info: 'STACS2027.K23Struct.two_le_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.two_le_length

/-- info: 'STACS2027.K23Struct.exists_isCyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.exists_isCyc

/-- info: 'STACS2027.K23Struct.IsCyc.rotate_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.IsCyc.rotate_to

/-- info: 'STACS2027.K23Struct.longer_or_minor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.longer_or_minor

/-- info: 'STACS2027.K23Struct.exists_ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.exists_ham

/-- info: 'STACS2027.K23Struct.exists_split_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.exists_split_getD

/-- info: 'STACS2027.K23Struct.exists_split4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.exists_split4

/-- info: 'STACS2027.K23Struct.crossing_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.crossing_core

/-- info: 'STACS2027.K23Struct.crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.crossing

/-- info: 'STACS2027.K23Struct.isK4Graph_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.K23Struct.isK4Graph_of

/-- info: 'STACS2027.twoConnectedK23_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.twoConnectedK23_structure

/-- info: 'STACS2027.faceEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.faceEdges

/-- info: 'STACS2027.bdry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.bdry

/-- info: 'STACS2027.encl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.encl

/-- info: 'STACS2027.DualAdj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.DualAdj

/-- info: 'STACS2027.IsSubtree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsSubtree

/-- info: 'STACS2027.IsRooted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsRooted

/-- info: 'STACS2027.mem_bdry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_bdry

/-- info: 'STACS2027.mem_pathEdges_of_pairwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_pathEdges_of_pairwise

/-- info: 'STACS2027.mem_cycleEdges_of_pairwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_cycleEdges_of_pairwise

/-- info: 'STACS2027.IsRPath.eq_cons_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsRPath.eq_cons_snoc

/-- info: 'STACS2027.IsRPath.exists_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsRPath.exists_inner

/-- info: 'STACS2027.IsPolygon.faceVerts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.faceVerts_eq

/-- info: 'STACS2027.IsPolygon.exists_inner_faceVert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.exists_inner_faceVert

/-- info: 'STACS2027.IsPolygon.mem_faceEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_faceEdges

/-- info: 'STACS2027.IsPolygon.mem_faceEdges_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_faceEdges_iff

/-- info: 'STACS2027.IsPolygon.adj_of_mem_faceEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.adj_of_mem_faceEdges

/-- info: 'STACS2027.IsPolygon.side_infix_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.side_infix_iff

/-- info: 'STACS2027.IsPolygon.exists_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.exists_parent

/-- info: 'STACS2027.IsPolygon.parent_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.parent_unique

/-- info: 'STACS2027.IsPolygon.parent_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.parent_within

/-- info: 'STACS2027.IsPolygon.not_isChild_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.not_isChild_root

/-- info: 'STACS2027.IsPolygon.faces_of_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.faces_of_seg

/-- info: 'STACS2027.IsPolygon.faces_of_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.faces_of_side

/-- info: 'STACS2027.IsPolygon.eq_of_side_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.eq_of_side_mem

/-- info: 'STACS2027.IsPolygon.dualAdj_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.dualAdj_iff

/-- info: 'STACS2027.IsPolygon.rooted_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.rooted_within

/-- info: 'STACS2027.IsPolygon.reflTransGen_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.reflTransGen_symm

/-- info: 'STACS2027.IsPolygon.isSubtree_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.isSubtree_iff

/-- info: 'STACS2027.mem_encl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_encl

/-- info: 'STACS2027.encl_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.encl_subset

/-- info: 'STACS2027.IsRPath.adj_of_infix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsRPath.adj_of_infix

/-- info: 'STACS2027.IsRPath.splice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsRPath.splice

/-- info: 'STACS2027.odd_card_filter_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.odd_card_filter_pair

/-- info: 'STACS2027.IsPolygon.mem_encl_of_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_encl_of_ends

/-- info: 'STACS2027.IsPolygon.mem_encl_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_encl_iff

/-- info: 'STACS2027.IsPolygon.top_mem_encl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.top_mem_encl

/-- info: 'STACS2027.IsPolygon.encl_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.encl_parent

/-- info: 'STACS2027.IsPolygon.isRooted_encl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.isRooted_encl

/-- info: 'STACS2027.IsPolygon.exists_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.exists_top

/-- info: 'STACS2027.IsPolygon.mem_cycleEdges_iff_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.mem_cycleEdges_iff_odd

/-- info: 'STACS2027.IsPolygon.bdry_encl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.bdry_encl

/-- info: 'STACS2027.IsPolygon.isSubtree_encl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.isSubtree_encl

/-- info: 'STACS2027.IsPolygon.exists_rpath_of_rooted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.exists_rpath_of_rooted

/-- info: 'STACS2027.IsPolygon.exists_convex_of_isSubtree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.exists_convex_of_isSubtree

/-- info: 'STACS2027.ConvexCycle.card_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.ConvexCycle.card_edges

/-- info: 'STACS2027.ConvexCycle.eq_of_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.ConvexCycle.eq_of_edges

/-- info: 'STACS2027.IsPolygon.cycle_subtree_bij' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.cycle_subtree_bij

/-- info: 'STACS2027.IsPolygon.cycle_subtree_bij_simpleCycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.cycle_subtree_bij_simpleCycles

/-- info: 'STACS2027.wt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.wt

/-- info: 'STACS2027.wt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.wt_nonneg

/-- info: 'STACS2027.rpSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rpSet

/-- info: 'STACS2027.mem_rpSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_rpSet

/-- info: 'STACS2027.jpSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.jpSet

/-- info: 'STACS2027.mem_jpSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_jpSet

/-- info: 'STACS2027.Joins.head_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Joins.head_pairwise

/-- info: 'STACS2027.wt_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.wt_append

/-- info: 'STACS2027.sum_insert_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_insert_le

/-- info: 'STACS2027.sum_jpSet_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_jpSet_le

/-- info: 'STACS2027.IsPolygon.sum_rpSet_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.sum_rpSet_le

/-- info: 'STACS2027.encSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.encSum

/-- info: 'STACS2027.encSum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.encSum_nonneg

/-- info: 'STACS2027.IsPolygon.three_le_of_mem_encl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.three_le_of_mem_encl

/-- info: 'STACS2027.IsPolygon.filter_rpSet_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.filter_rpSet_subset

/-- info: 'STACS2027.sum_jpSet_encl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_jpSet_encl_le

/-- info: 'STACS2027.IsPolygon.encSum_self_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.encSum_self_le

/-- info: 'STACS2027.IsPolygon.encSum_le_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.encSum_le_child

/-- info: 'STACS2027.chainSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chainSum

/-- info: 'STACS2027.IsPolygon.chainSum_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.chainSum_add_le

/-- info: 'STACS2027.IsPolygon.length_filter_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.length_filter_le_add

/-- info: 'STACS2027.IsPolygon.face_cycle_half_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.face_cycle_half_bound

/-- info: 'STACS2027.IsPolygon.face_cycle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.face_cycle_bound

/-- info: 'STACS2027.IsPolygon.faces_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.faces_le_two

/-- info: 'STACS2027.IsPolygon.edge_cycle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.edge_cycle_bound

/-- info: 'STACS2027.chords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chords

/-- info: 'STACS2027.dualEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.dualEdges

/-- info: 'STACS2027.degIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.degIn

/-- info: 'STACS2027.mem_dualEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.mem_dualEdges

/-- info: 'STACS2027.IsPolygon.polyEdges_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.polyEdges_eq

/-- info: 'STACS2027.IsPolygon.euler_face_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.euler_face_count

/-- info: 'STACS2027.IsPolygon.dualAdj_iff_dualEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.dualAdj_iff_dualEdges

/-- info: 'STACS2027.IsPolygon.chord_dualEdge_bij' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.chord_dualEdge_bij

/-- info: 'STACS2027.IsPolygon.weakDual_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.weakDual_tree

/-- info: 'STACS2027.IsPolygon.bdry_ne_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.bdry_ne_empty

/-- info: 'STACS2027.IsPolygon.degIn_cycleEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.degIn_cycleEdges

/-- info: 'STACS2027.IsPolygon.bdry_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.bdry_deg

/-- info: 'STACS2027.IsPolygon.exists_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.exists_leaf

/-- info: 'STACS2027.IsPolygon.leaf_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.IsPolygon.leaf_face

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
