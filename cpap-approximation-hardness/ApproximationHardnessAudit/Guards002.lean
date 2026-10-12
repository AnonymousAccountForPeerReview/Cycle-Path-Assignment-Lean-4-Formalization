module

import all ApproximationHardness

/-!
Exact-message axiom guards for every explicitly named ApproximationHardness declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.RAM.flagOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.flagOf

/-- info: 'STACS2027.RAM.loadTerm_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.loadTerm_flag

/-- info: 'STACS2027.RAM.flagOf_snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.flagOf_snoc

/-- info: 'STACS2027.RAM.edgeCodes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.edgeCodes_length

/-- info: 'STACS2027.RAM.sum_map_const_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.sum_map_const_succ

/-- info: 'STACS2027.RAM.PathFixed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PathFixed

/-- info: 'STACS2027.RAM.pathCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.pathCost

/-- info: 'STACS2027.RAM.pathBody_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.pathBody_step

/-- info: 'STACS2027.RAM.edgeCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.edgeCode

/-- info: 'STACS2027.RAM.pathCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.pathCode

/-- info: 'STACS2027.RAM.pathsCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.pathsCode

/-- info: 'STACS2027.RAM.decInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.decInput

/-- info: 'STACS2027.RAM.decOutput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.decOutput

/-- info: 'STACS2027.RAM.DR.np' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.np

/-- info: 'STACS2027.RAM.DR.E' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.E

/-- info: 'STACS2027.RAM.DR.bi' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.bi

/-- info: 'STACS2027.RAM.DR.u' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.u

/-- info: 'STACS2027.RAM.DR.x' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.x

/-- info: 'STACS2027.RAM.DR.w' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.w

/-- info: 'STACS2027.RAM.DR.addr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.addr

/-- info: 'STACS2027.RAM.DR.Wb' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.Wb

/-- info: 'STACS2027.RAM.DR.len' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.len

/-- info: 'STACS2027.RAM.DR.cnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.cnt

/-- info: 'STACS2027.RAM.DR.ps' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.ps

/-- info: 'STACS2027.RAM.DR.b0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.b0

/-- info: 'STACS2027.RAM.DR.flag' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.flag

/-- info: 'STACS2027.RAM.DR.ex' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.ex

/-- info: 'STACS2027.RAM.DR.ey' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.ey

/-- info: 'STACS2027.RAM.DR.bx' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.bx

/-- info: 'STACS2027.RAM.DR.bY' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.bY

/-- info: 'STACS2027.RAM.DR.ox' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.ox

/-- info: 'STACS2027.RAM.DR.oy' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.oy

/-- info: 'STACS2027.RAM.DR.t' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.t

/-- info: 'STACS2027.RAM.DR.t2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.t2

/-- info: 'STACS2027.RAM.DR.z1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.z1

/-- info: 'STACS2027.RAM.DR.z2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.z2

/-- info: 'STACS2027.RAM.DR.z3' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.z3

/-- info: 'STACS2027.RAM.DR.v' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.v

/-- info: 'STACS2027.RAM.DR.vi' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.vi

/-- info: 'STACS2027.RAM.DR.w0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.w0

/-- info: 'STACS2027.RAM.DR.w1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.w1

/-- info: 'STACS2027.RAM.DR.w2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.w2

/-- info: 'STACS2027.RAM.DR.nb' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.nb

/-- info: 'STACS2027.RAM.DR.ui' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DR.ui

/-- info: 'STACS2027.RAM.scanPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.scanPre

/-- info: 'STACS2027.RAM.skipPath' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.skipPath

/-- info: 'STACS2027.RAM.tabPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.tabPre

/-- info: 'STACS2027.RAM.fillCell' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.fillCell

/-- info: 'STACS2027.RAM.fillBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.fillBlock

/-- info: 'STACS2027.RAM.blkOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.blkOf

/-- info: 'STACS2027.RAM.offOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.offOf

/-- info: 'STACS2027.RAM.readEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.readEdge

/-- info: 'STACS2027.RAM.flagIfNe' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.flagIfNe

/-- info: 'STACS2027.RAM.flagEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.flagEdge

/-- info: 'STACS2027.RAM.portInc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.portInc

/-- info: 'STACS2027.RAM.countEdge' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.countEdge

/-- info: 'STACS2027.RAM.pathPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.pathPre

/-- info: 'STACS2027.RAM.pathBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.pathBody

/-- info: 'STACS2027.RAM.procPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.procPre

/-- info: 'STACS2027.RAM.outPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.outPre

/-- info: 'STACS2027.RAM.outBodyD' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.outBodyD

/-- info: 'STACS2027.RAM.decProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.decProgram

/-- info: 'STACS2027.RAM.passAqPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passAqPre

/-- info: 'STACS2027.RAM.passAq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passAq

/-- info: 'STACS2027.RAM.InvAq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvAq

/-- info: 'STACS2027.RAM.InvAq.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvAq.step

/-- info: 'STACS2027.RAM.InvAq.len_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvAq.len_le

/-- info: 'STACS2027.RAM.InvAq.m_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvAq.m_le

/-- info: 'STACS2027.RAM.InvAq.p_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvAq.p_le

/-- info: 'STACS2027.RAM.HoldsInput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.HoldsInput

/-- info: 'STACS2027.RAM.InvAq.start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvAq.start

/-- info: 'STACS2027.RAM.passAq_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passAq_eq

/-- info: 'STACS2027.RAM.passAqModel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passAqModel

/-- info: 'STACS2027.RAM.sat_passAq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.sat_passAq

/-- info: 'STACS2027.RAM.passAqModel_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.passAqModel_spec

/-- info: 'STACS2027.RAM.pathCode_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.pathCode_length

/-- info: 'STACS2027.RAM.SkipInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SkipInv

/-- info: 'STACS2027.RAM.skip_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.skip_step

/-- info: 'STACS2027.RAM.tabVal' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.tabVal

/-- info: 'STACS2027.RAM.tabMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.tabMem

/-- info: 'STACS2027.RAM.tabMem_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.tabMem_zero

/-- info: 'STACS2027.RAM.tabMem_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.tabMem_cell

/-- info: 'STACS2027.RAM.FillFixed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.FillFixed

/-- info: 'STACS2027.RAM.fillCell_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.fillCell_run

/-- info: 'STACS2027.RAM.FillInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.FillInv

/-- info: 'STACS2027.RAM.fillBlock_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.fillBlock_exec

/-- info: 'STACS2027.RAM.ExecB.reg_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ExecB.reg_frame

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

/-- info: 'STACS2027.RAM.flatMap_clauseCode_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.flatMap_clauseCode_length

/-- info: 'STACS2027.RAM.ramInput_length_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ramInput_length_eq

/-- info: 'STACS2027.RAM.orInput_getD_rot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.orInput_getD_rot

/-- info: 'STACS2027.RAM.orInput_getD_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.orInput_getD_left

/-- info: 'STACS2027.RAM.csOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.csOf

/-- info: 'STACS2027.RAM.csBit_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.csBit_prefix

/-- info: 'STACS2027.RAM.orClausePre_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orClausePre_run

/-- info: 'STACS2027.RAM.orClausePre_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orClausePre_addrOK

/-- info: 'STACS2027.RAM.ClauseInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ClauseInv

/-- info: 'STACS2027.RAM.orClauseCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.orClauseCost

/-- info: 'STACS2027.RAM.orClause_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orClause_step

/-- info: 'STACS2027.RAM.orCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.orCost

/-- info: 'STACS2027.RAM.orInput_getD_high' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orInput_getD_high

/-- info: 'STACS2027.RAM.orOutput_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.orOutput_eq

/-- info: 'STACS2027.RAM.or_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.or_computes

/-- info: 'STACS2027.RAM.orConst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.orConst

/-- info: 'STACS2027.RAM.orClause_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orClause_sum

/-- info: 'STACS2027.RAM.orCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orCost_le

/-- info: 'STACS2027.RAM.orOutput_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orOutput_bits

/-- info: 'STACS2027.RAM.orientation_linear_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orientation_linear_time

/-- info: 'STACS2027.RAM.orE' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orE

/-- info: 'STACS2027.RAM.orB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orB

/-- info: 'STACS2027.RAM.orSpace' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orSpace

/-- info: 'STACS2027.RAM.Layout' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Layout

/-- info: 'STACS2027.RAM.layoutRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.layoutRegs

/-- info: 'STACS2027.RAM.Layout.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.Layout.frame

/-- info: 'STACS2027.RAM.MemInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.MemInv

/-- info: 'STACS2027.RAM.At.agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.At.agree

/-- info: 'STACS2027.RAM.literal_var_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.literal_var_lt

/-- info: 'STACS2027.RAM.litPortM' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.litPortM

/-- info: 'STACS2027.RAM.litMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.litMem

/-- info: 'STACS2027.RAM.orLit_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orLit_mem

/-- info: 'STACS2027.RAM.litMem_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.litMem_other

/-- info: 'STACS2027.RAM.orLit_regs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.orLit_regs

/-- info: 'STACS2027.RAM.orLit_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orLit_addrOK

/-- info: 'STACS2027.RAM.orLit_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orLit_step

/-- info: 'STACS2027.RAM.orOutA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orOutA

/-- info: 'STACS2027.RAM.orOutC' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orOutC

/-- info: 'STACS2027.RAM.orOut_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orOut_eq

/-- info: 'STACS2027.RAM.run_orOut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_orOut

/-- info: 'STACS2027.RAM.orOutA_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orOutA_run

/-- info: 'STACS2027.RAM.vsOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.vsOf

/-- info: 'STACS2027.RAM.orVarSign_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orVarSign_run

/-- info: 'STACS2027.RAM.orOutC_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orOutC_run

/-- info: 'STACS2027.RAM.bitNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.bitNat

/-- info: 'STACS2027.RAM.portRead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.portRead

/-- info: 'STACS2027.RAM.occVar_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.occVar_lt

/-- info: 'STACS2027.RAM.vsOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.vsOf_eq

/-- info: 'STACS2027.RAM.csBit_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.csBit_le

/-- info: 'STACS2027.RAM.orOutA_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orOutA_addrOK

/-- info: 'STACS2027.RAM.orVarSign_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orVarSign_addrOK

/-- info: 'STACS2027.RAM.OrOutInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OrOutInv

/-- info: 'STACS2027.RAM.orOut_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.orOut_step

/-- info: 'STACS2027.RAM.orInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orInput

/-- info: 'STACS2027.RAM.rotFun' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.rotFun

/-- info: 'STACS2027.RAM.orOutput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.orOutput

/-- info: 'STACS2027.RAM.OR.E' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.E

/-- info: 'STACS2027.RAM.OR.B' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.B

/-- info: 'STACS2027.RAM.OR.occ' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.occ

/-- info: 'STACS2027.RAM.OR.cnt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.cnt

/-- info: 'STACS2027.RAM.OR.L' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.L

/-- info: 'STACS2027.RAM.OR.cs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.cs

/-- info: 'STACS2027.RAM.OR.t' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.t

/-- info: 'STACS2027.RAM.OR.t2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.t2

/-- info: 'STACS2027.RAM.OR.a' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.a

/-- info: 'STACS2027.RAM.OR.x' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.x

/-- info: 'STACS2027.RAM.OR.y' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.y

/-- info: 'STACS2027.RAM.OR.v' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.v

/-- info: 'STACS2027.RAM.OR.s' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.s

/-- info: 'STACS2027.RAM.OR.nc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.nc

/-- info: 'STACS2027.RAM.OR.port' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.port

/-- info: 'STACS2027.RAM.OR.q' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.q

/-- info: 'STACS2027.RAM.OR.i' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.i

/-- info: 'STACS2027.RAM.OR.a1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.a1

/-- info: 'STACS2027.RAM.OR.vs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.vs

/-- info: 'STACS2027.RAM.OR.d' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.d

/-- info: 'STACS2027.RAM.OR.pd' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.pd

/-- info: 'STACS2027.RAM.OR.sm' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.sm

/-- info: 'STACS2027.RAM.OR.three' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.three

/-- info: 'STACS2027.RAM.OR.five' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.five

/-- info: 'STACS2027.RAM.OR.two' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.OR.two

/-- info: 'STACS2027.RAM.orPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orPre

/-- info: 'STACS2027.RAM.orClausePre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orClausePre

/-- info: 'STACS2027.RAM.orLit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orLit

/-- info: 'STACS2027.RAM.orClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orClause

/-- info: 'STACS2027.RAM.orOutPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orOutPre

/-- info: 'STACS2027.RAM.orVarSign' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orVarSign

/-- info: 'STACS2027.RAM.orOut' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orOut

/-- info: 'STACS2027.RAM.orProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.orProgram

/-- info: 'STACS2027.RAM.placeLiterals_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.placeLiterals_getElem?

/-- info: 'STACS2027.RAM.occList_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.occList_getElem?

/-- info: 'STACS2027.RAM.occList_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.occList_length

/-- info: 'STACS2027.RAM.litPort' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.litPort

/-- info: 'STACS2027.RAM.occPort_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.occPort_flat

/-- info: 'STACS2027.RAM.occVar_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.occVar_flat

/-- info: 'STACS2027.RAM.positiveIndex_flat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.positiveIndex_flat

/-- info: 'STACS2027.RAM.posCode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.posCode

/-- info: 'STACS2027.RAM.posCode_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.posCode_snoc

/-- info: 'STACS2027.RAM.posCode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.posCode_eq

/-- info: 'STACS2027.RAM.off_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.off_prefix

/-- info: 'STACS2027.RAM.kl_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.kl_prefix

/-- info: 'STACS2027.RAM.prefix_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.prefix_lt

/-- info: 'STACS2027.RAM.oj_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.oj_prefix

/-- info: 'STACS2027.RAM.flatten_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.flatten_prefix

/-- info: 'STACS2027.RAM.getElem_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.getElem_prefix

/-- info: 'STACS2027.RAM.csBit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.csBit

/-- info: 'STACS2027.RAM.regsW' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.regsW

/-- info: 'STACS2027.RAM.hasStore' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.hasStore

/-- info: 'STACS2027.RAM.hasWrite' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.hasWrite

/-- info: 'STACS2027.RAM.run_reg_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_reg_frame

/-- info: 'STACS2027.RAM.run_mem_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_mem_frame

/-- info: 'STACS2027.RAM.run_out_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_out_frame

/-- info: 'STACS2027.RAM.regsW_seqs_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.regsW_seqs_cons

/-- info: 'STACS2027.RAM.regsW_seqs_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.regsW_seqs_nil

/-- info: 'STACS2027.RAM.hasStore_seqs_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.hasStore_seqs_cons

/-- info: 'STACS2027.RAM.hasStore_seqs_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.hasStore_seqs_nil

/-- info: 'STACS2027.RAM.hasWrite_seqs_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.hasWrite_seqs_cons

/-- info: 'STACS2027.RAM.hasWrite_seqs_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.hasWrite_seqs_nil

/-- info: 'STACS2027.RAM.loopFree_seqs_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_seqs_cons

/-- info: 'STACS2027.RAM.loopFree_seqs_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_seqs_nil

/-- info: 'STACS2027.RAM.run_seqs_app' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_seqs_app

/-- info: 'STACS2027.RAM.run_seq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_seq

/-- info: 'STACS2027.RAM.run_ifz' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.run_ifz

/-- info: 'STACS2027.RAM.PassInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.PassInv

/-- info: 'STACS2027.RAM.sat_clausePass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.sat_clausePass

/-- info: 'STACS2027.RAM.sat_countLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.sat_countLoop

/-- info: 'STACS2027.RAM.exec_listPass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.exec_listPass

/-- info: 'STACS2027.RAM.exec_countLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.exec_countLoop

/-- info: 'STACS2027.RAM.exec_loopFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.exec_loopFree

/-- info: 'STACS2027.RAM.At' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.At

/-- info: 'STACS2027.RAM.At.head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.At.head

/-- info: 'STACS2027.RAM.At.tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.At.tail

/-- info: 'STACS2027.RAM.At.append_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.At.append_left

/-- info: 'STACS2027.RAM.At.drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.At.drop

/-- info: 'STACS2027.RAM.At.of_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.At.of_mem

/-- info: 'STACS2027.RAM.litARegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.litARegs

/-- info: 'STACS2027.RAM.litA_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.litA_run

/-- info: 'STACS2027.RAM.litA_iter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.litA_iter

/-- info: 'STACS2027.RAM.clauseApre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseApre

/-- info: 'STACS2027.RAM.clauseA_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseA_eq

/-- info: 'STACS2027.RAM.clauseAModel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseAModel

/-- info: 'STACS2027.RAM.clauseA_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseA_run

/-- info: 'STACS2027.RAM.litCodes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.litCodes_length

/-- info: 'STACS2027.RAM.clauseCode_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseCode_length

/-- info: 'STACS2027.RAM.clauseCodes_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseCodes_length_le

/-- info: 'STACS2027.RAM.clauseACost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseACost

/-- info: 'STACS2027.RAM.sat_clauseA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.sat_clauseA

/-- info: 'STACS2027.RAM.passApre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passApre

/-- info: 'STACS2027.RAM.passApost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passApost

/-- info: 'STACS2027.RAM.passA_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passA_eq

/-- info: 'STACS2027.RAM.InvA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvA

/-- info: 'STACS2027.RAM.InvA.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvA.step

/-- info: 'STACS2027.RAM.InvA.len_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvA.len_le

/-- info: 'STACS2027.RAM.InvA.m_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvA.m_le

/-- info: 'STACS2027.RAM.ramInput_clause_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ramInput_clause_le

/-- info: 'STACS2027.RAM.InvA.p_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvA.p_le

/-- info: 'STACS2027.RAM.passAModel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passAModel

/-- info: 'STACS2027.RAM.passACost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.passACost

/-- info: 'STACS2027.RAM.InvA.start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvA.start

/-- info: 'STACS2027.RAM.sat_passA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.sat_passA

/-- info: 'STACS2027.RAM.passAModel_initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.passAModel_initial

/-- info: 'STACS2027.RAM.signCode_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.signCode_lt

/-- info: 'STACS2027.RAM.literal_of_code' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.literal_of_code

/-- info: 'STACS2027.RAM.code_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.code_eq_iff

/-- info: 'STACS2027.RAM.port_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.port_endpoints

/-- info: 'STACS2027.RAM.litRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.litRegs

/-- info: 'STACS2027.RAM.readLit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.readLit_run

/-- info: 'STACS2027.RAM.clausePortAt_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clausePortAt_lt

/-- info: 'STACS2027.RAM.endpointVal' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.endpointVal

/-- info: 'STACS2027.RAM.endpointCode_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.endpointCode_run

/-- info: 'STACS2027.RAM.endpointVal_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.endpointVal_congr

/-- info: 'STACS2027.RAM.clauseEmit_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseEmit_run

/-- info: 'STACS2027.RAM.endpointVal_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.endpointVal_eq

/-- info: 'STACS2027.RAM.clauseEmit_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseEmit_pairs

/-- info: 'STACS2027.RAM.At.drop'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.At.drop'

/-- info: 'STACS2027.RAM.LitPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.LitPre

/-- info: 'STACS2027.RAM.readLit_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.readLit_step

/-- info: 'STACS2027.RAM.slot_not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.slot_not_mem

/-- info: 'STACS2027.RAM.clausePairsFrom_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clausePairsFrom_snoc

/-- info: 'STACS2027.RAM.StateB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.StateB

/-- info: 'STACS2027.RAM.LitPre.of_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.LitPre.of_eq

/-- info: 'STACS2027.RAM.SlotOK' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SlotOK

/-- info: 'STACS2027.RAM.clauseB_split' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseB_split

/-- info: 'STACS2027.RAM.placeLiterals_two'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.placeLiterals_two'

/-- info: 'STACS2027.RAM.placeLiterals_three'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.placeLiterals_three'

/-- info: 'STACS2027.RAM.emit_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.emit_finish

/-- info: 'STACS2027.RAM.memFree_clauseEmit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_clauseEmit

/-- info: 'STACS2027.RAM.StateB.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.StateB.step

/-- info: 'STACS2027.RAM.run_seqs_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_seqs_append

/-- info: 'STACS2027.RAM.loopFree_seqs_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_seqs_append

/-- info: 'STACS2027.RAM.loopFree_edgeConst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_edgeConst

/-- info: 'STACS2027.RAM.loopFree_flatMap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_flatMap

/-- info: 'STACS2027.RAM.varEmit_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.varEmit_run

/-- info: 'STACS2027.RAM.varBodyPre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.varBodyPre

/-- info: 'STACS2027.RAM.varBodyPost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.varBodyPost

/-- info: 'STACS2027.RAM.varBody_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.varBody_eq

/-- info: 'STACS2027.RAM.loopFree_varBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_varBody

/-- info: 'STACS2027.RAM.InvV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.InvV

/-- info: 'STACS2027.RAM.varPairs_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.varPairs_succ

/-- info: 'STACS2027.RAM.edgeWord_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.edgeWord_append

/-- info: 'STACS2027.RAM.InvV.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvV.step

/-- info: 'STACS2027.RAM.InvV.cv_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvV.cv_le

/-- info: 'STACS2027.RAM.memFree_varEmit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_varEmit

/-- info: 'STACS2027.RAM.InvV.addrOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvV.addrOK

/-- info: 'STACS2027.RAM.passVpre' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passVpre

/-- info: 'STACS2027.RAM.passVpost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passVpost

/-- info: 'STACS2027.RAM.passV_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passV_eq

/-- info: 'STACS2027.RAM.passVModel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passVModel

/-- info: 'STACS2027.RAM.passVCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.passVCost

/-- info: 'STACS2027.RAM.AfterA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.AfterA

/-- info: 'STACS2027.RAM.InvV.start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.InvV.start

/-- info: 'STACS2027.RAM.sat_passV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.sat_passV

/-- info: 'STACS2027.RAM.passVModel_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.passVModel_spec

/-- info: 'STACS2027.RAM.loopFree_cntBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_cntBody

/-- info: 'STACS2027.RAM.loopFree_keepBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_keepBody

/-- info: 'STACS2027.RAM.loopFree_outBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_outBody

/-- info: 'STACS2027.RAM.loopFree_padBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.loopFree_padBody

/-- info: 'STACS2027.RAM.polCost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.polCost

/-- info: 'STACS2027.RAM.polarize_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.polarize_length

/-- info: 'STACS2027.RAM.pol_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.pol_computes

/-- info: 'STACS2027.RAM.polConst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.polConst

/-- info: 'STACS2027.RAM.deletedCount_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.deletedCount_le

/-- info: 'STACS2027.RAM.polCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.polCost_le

/-- info: 'STACS2027.RAM.literal_count_bound3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.literal_count_bound3

/-- info: 'STACS2027.RAM.ThreeOccurrence.clause_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.ThreeOccurrence.clause_count

/-- info: 'STACS2027.RAM.polLinConst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.polLinConst

/-- info: 'STACS2027.RAM.polarize_linear_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.polarize_linear_time

/-- info: 'STACS2027.RAM.signCode_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.signCode_inj

/-- info: 'STACS2027.RAM.signCode_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.signCode_le

/-- info: 'STACS2027.RAM.pureCounts_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.pureCounts_eq

/-- info: 'STACS2027.RAM.clash' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.clash

/-- info: 'STACS2027.RAM.clash_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clash_comm

/-- info: 'STACS2027.RAM.clash_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clash_self

/-- info: 'STACS2027.RAM.tautological_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.tautological_two

/-- info: 'STACS2027.RAM.tautological_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.tautological_three

/-- info: 'STACS2027.RAM.deleted_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.deleted_two

/-- info: 'STACS2027.RAM.deleted_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.deleted_three

/-- info: 'STACS2027.RAM.CountsAt' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.CountsAt

/-- info: 'STACS2027.RAM.clash_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.clash_iff

/-- info: 'STACS2027.RAM.pure_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.pure_iff

/-- info: 'STACS2027.RAM.del_step' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.del_step

/-- info: 'STACS2027.RAM.ifThird_skip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ifThird_skip

/-- info: 'STACS2027.RAM.ifThird_do' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ifThird_do

/-- info: 'STACS2027.RAM.LitIn.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.LitIn.frame

/-- info: 'STACS2027.RAM.CountsAt.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.CountsAt.frame

/-- info: 'STACS2027.RAM.DelScratch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DelScratch

/-- info: 'STACS2027.RAM.tautPair_frame'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.tautPair_frame'

/-- info: 'STACS2027.RAM.pureLit_frame'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.pureLit_frame'

/-- info: 'STACS2027.RAM.tautPair_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.tautPair_step

/-- info: 'STACS2027.RAM.pureLit_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.pureLit_step

/-- info: 'STACS2027.RAM.Consts.scratch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Consts.scratch

/-- info: 'STACS2027.RAM.delCode_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.delCode_prefix

/-- info: 'STACS2027.RAM.run_delCode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_delCode

/-- info: 'STACS2027.RAM.DelScratchT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.DelScratchT

/-- info: 'STACS2027.RAM.delCode_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.delCode_two

/-- info: 'STACS2027.RAM.delCode_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.delCode_three

/-- info: 'STACS2027.RAM.count_map_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.count_map_inj

/-- info: 'STACS2027.RAM.litAddr_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.litAddr_inj

/-- info: 'STACS2027.RAM.litAddr_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.litAddr_false

/-- info: 'STACS2027.RAM.litAddr_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.litAddr_true

/-- info: 'STACS2027.RAM.kpMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.kpMem

/-- info: 'STACS2027.RAM.kpMem_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.kpMem_below

/-- info: 'STACS2027.RAM.kpMem_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.kpMem_at

/-- info: 'STACS2027.RAM.kpMem_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.kpMem_snoc

/-- info: 'STACS2027.RAM.kpLit_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.kpLit_mem

/-- info: 'STACS2027.RAM.kpLit_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.kpLit_frame

/-- info: 'STACS2027.RAM.kpLit_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.kpLit_out

/-- info: 'STACS2027.RAM.kpLit_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.kpLit_step

/-- info: 'STACS2027.RAM.outSign' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.outSign

/-- info: 'STACS2027.RAM.outLit_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.outLit_out

/-- info: 'STACS2027.RAM.outLit_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.outLit_mem

/-- info: 'STACS2027.RAM.outLit_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.outLit_frame

/-- info: 'STACS2027.RAM.outSign_flip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.outSign_flip

/-- info: 'STACS2027.RAM.SlotsHold' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SlotsHold

/-- info: 'STACS2027.RAM.SlotsHold.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SlotsHold.frame

/-- info: 'STACS2027.RAM.readDel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.readDel

/-- info: 'STACS2027.RAM.KeepFixed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.KeepFixed

/-- info: 'STACS2027.RAM.keepBody_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.keepBody_frame

/-- info: 'STACS2027.RAM.keepBody_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.keepBody_out

/-- info: 'STACS2027.RAM.run_keepBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_keepBody

/-- info: 'STACS2027.RAM.keepBody_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.keepBody_step

/-- info: 'STACS2027.RAM.outBody_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.outBody_frame

/-- info: 'STACS2027.RAM.outBody_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.outBody_mem

/-- info: 'STACS2027.RAM.run_outBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_outBody

/-- info: 'STACS2027.RAM.flip_code' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.flip_code

/-- info: 'STACS2027.RAM.outBody_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.outBody_step

/-- info: 'STACS2027.RAM.cntLit_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntLit_mem

/-- info: 'STACS2027.RAM.cntLit_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntLit_out

/-- info: 'STACS2027.RAM.cntLit_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntLit_frame

/-- info: 'STACS2027.RAM.tautPair_del' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.tautPair_del

/-- info: 'STACS2027.RAM.tautPair_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.tautPair_mem

/-- info: 'STACS2027.RAM.tautPair_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.tautPair_out

/-- info: 'STACS2027.RAM.tautPair_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.tautPair_frame

/-- info: 'STACS2027.RAM.pureCounts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.pureCounts

/-- info: 'STACS2027.RAM.pureLit_del' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.pureLit_del

/-- info: 'STACS2027.RAM.pureLit_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.pureLit_mem

/-- info: 'STACS2027.RAM.pureLit_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.pureLit_out

/-- info: 'STACS2027.RAM.pureLit_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.pureLit_frame

/-- info: 'STACS2027.RAM.polBase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.polBase

/-- info: 'STACS2027.RAM.polN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.polN

/-- info: 'STACS2027.RAM.polB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.polB

/-- info: 'STACS2027.RAM.polMc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.polMc

/-- info: 'STACS2027.RAM.PolRegs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PolRegs

/-- info: 'STACS2027.RAM.PolRegs.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PolRegs.frame

/-- info: 'STACS2027.RAM.polBase_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.polBase_zero

/-- info: 'STACS2027.RAM.polBase_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.polBase_code

/-- info: 'STACS2027.RAM.polBase_above' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.polBase_above

/-- info: 'STACS2027.RAM.polN_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.polN_eq

/-- info: 'STACS2027.RAM.InputBelow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.InputBelow

/-- info: 'STACS2027.RAM.inputBelow_cnt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.inputBelow_cnt

/-- info: 'STACS2027.RAM.inputBelow_kp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.inputBelow_kp

/-- info: 'STACS2027.RAM.restart_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.restart_run

/-- info: 'STACS2027.RAM.CntInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.CntInv

/-- info: 'STACS2027.RAM.polSpace' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.polSpace

/-- info: 'STACS2027.RAM.bodyPre_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bodyPre_of

/-- info: 'STACS2027.RAM.cnt_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cnt_step

/-- info: 'STACS2027.RAM.polMc_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.polMc_input

/-- info: 'STACS2027.RAM.litAddr_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.litAddr_lt

/-- info: 'STACS2027.RAM.polMc_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.polMc_count

/-- info: 'STACS2027.RAM.polMc_B' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.polMc_B

/-- info: 'STACS2027.RAM.McBelow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.McBelow

/-- info: 'STACS2027.RAM.mcBelow_kp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.mcBelow_kp

/-- info: 'STACS2027.RAM.countsAt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.countsAt_of

/-- info: 'STACS2027.RAM.At.advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.At.advance

/-- info: 'STACS2027.RAM.vars_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.vars_lt

/-- info: 'STACS2027.RAM.keptOf' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.keptOf

/-- info: 'STACS2027.RAM.keptOf_snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.keptOf_snoc

/-- info: 'STACS2027.RAM.KeepInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.KeepInv

/-- info: 'STACS2027.RAM.keep_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.keep_step

/-- info: 'STACS2027.RAM.kept_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.kept_eq

/-- info: 'STACS2027.RAM.OutInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.OutInv

/-- info: 'STACS2027.RAM.out_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.out_step

/-- info: 'STACS2027.RAM.padding_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.padding_succ

/-- info: 'STACS2027.RAM.PadInv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PadInv

/-- info: 'STACS2027.RAM.pad_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.pad_step

/-- info: 'STACS2027.RAM.litAddr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.litAddr

/-- info: 'STACS2027.RAM.cntMem' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.cntMem

/-- info: 'STACS2027.RAM.cntMem_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntMem_snoc

/-- info: 'STACS2027.RAM.cntLit_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntLit_step

/-- info: 'STACS2027.RAM.CntScratch' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.CntScratch

/-- info: 'STACS2027.RAM.cntBody_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntBody_frame

/-- info: 'STACS2027.RAM.cntBody_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntBody_out

/-- info: 'STACS2027.RAM.run_cntBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.run_cntBody

/-- info: 'STACS2027.RAM.cntLit_frame'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntLit_frame'

/-- info: 'STACS2027.RAM.cntLit_frame_slot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntLit_frame_slot

/-- info: 'STACS2027.RAM.cntMem_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntMem_below

/-- info: 'STACS2027.RAM.At.of_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.At.of_agree

/-- info: 'STACS2027.RAM.CntState' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.CntState

/-- info: 'STACS2027.RAM.readClause_fr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.readClause_fr

/-- info: 'STACS2027.RAM.ReadFixed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ReadFixed

/-- info: 'STACS2027.RAM.readClause_fixed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.readClause_fixed

/-- info: 'STACS2027.RAM.ReadResult' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ReadResult

/-- info: 'STACS2027.RAM.readClause_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.readClause_result

/-- info: 'STACS2027.RAM.cntBody_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntBody_step

/-- info: 'STACS2027.RAM.PR.v0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.v0

/-- info: 'STACS2027.RAM.PR.s0' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.s0

/-- info: 'STACS2027.RAM.PR.v1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.v1

/-- info: 'STACS2027.RAM.PR.s1' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.s1

/-- info: 'STACS2027.RAM.PR.v2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.v2

/-- info: 'STACS2027.RAM.PR.s2' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.s2

/-- info: 'STACS2027.RAM.PR.addr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.addr

/-- info: 'STACS2027.RAM.PR.x' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.x

/-- info: 'STACS2027.RAM.PR.y' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.y

/-- info: 'STACS2027.RAM.PR.z' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.z

/-- info: 'STACS2027.RAM.PR.u' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.u

/-- info: 'STACS2027.RAM.PR.del' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.del

/-- info: 'STACS2027.RAM.PR.r' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.r

/-- info: 'STACS2027.RAM.PR.two' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.two

/-- info: 'STACS2027.RAM.PR.three' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.three

/-- info: 'STACS2027.RAM.PR.w' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.PR.w

/-- info: 'STACS2027.RAM.rdLit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.rdLit

/-- info: 'STACS2027.RAM.readClause' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.readClause

/-- info: 'STACS2027.RAM.ifThird' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ifThird

/-- info: 'STACS2027.RAM.restart' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.restart

/-- info: 'STACS2027.RAM.cntLit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.cntLit

/-- info: 'STACS2027.RAM.cntBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.cntBody

/-- info: 'STACS2027.RAM.tautPair' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.tautPair

/-- info: 'STACS2027.RAM.pureLit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.pureLit

/-- info: 'STACS2027.RAM.delCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.delCode

/-- info: 'STACS2027.RAM.kpLit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.kpLit

/-- info: 'STACS2027.RAM.keepBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.keepBody

/-- info: 'STACS2027.RAM.outLit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.outLit

/-- info: 'STACS2027.RAM.outBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.outBody

/-- info: 'STACS2027.RAM.padBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.padBody

/-- info: 'STACS2027.RAM.polSetup' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.polSetup

/-- info: 'STACS2027.RAM.polProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.polProgram

/-- info: 'STACS2027.RAM.LitIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.LitIn

/-- info: 'STACS2027.RAM.Consts' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Consts

/-- info: 'STACS2027.RAM.Consts.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Consts.frame

/-- info: 'STACS2027.RAM.At.getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.At.getD

/-- info: 'STACS2027.RAM.readClause_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.readClause_two

/-- info: 'STACS2027.RAM.readClause_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.readClause_three

/-- info: 'STACS2027.RAM.readClause_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.readClause_frame

/-- info: 'STACS2027.RAM.SlotsBelow' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SlotsBelow

/-- info: 'STACS2027.RAM.SlotsBelow.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.SlotsBelow.frame

/-- info: 'STACS2027.RAM.slotsBelow_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.slotsBelow_read

/-- info: 'STACS2027.RAM.readClause_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.readClause_addrOK

/-- info: 'STACS2027.RAM.delCode_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.delCode_addrOK

/-- info: 'STACS2027.RAM.cntTail_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntTail_addrOK

/-- info: 'STACS2027.RAM.kpTail_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.kpTail_addrOK

/-- info: 'STACS2027.RAM.outTail_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.outTail_addrOK

/-- info: 'STACS2027.RAM.restart_addrOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.restart_addrOK

/-- info: 'STACS2027.RAM.BodyPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.BodyPre

/-- info: 'STACS2027.RAM.BodyPre.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.BodyPre.read

/-- info: 'STACS2027.RAM.cntBody_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cntBody_addrOK

/-- info: 'STACS2027.RAM.delCode_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.delCode_keeps

/-- info: 'STACS2027.RAM.keepBody_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.keepBody_eq

/-- info: 'STACS2027.RAM.outBody_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.outBody_eq

/-- info: 'STACS2027.RAM.keepBody_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.keepBody_addrOK

/-- info: 'STACS2027.RAM.outBody_addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.outBody_addrOK

/-- info: 'STACS2027.RAM.signCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.signCode

/-- info: 'STACS2027.RAM.litCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.litCode

/-- info: 'STACS2027.RAM.clauseCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseCode

/-- info: 'STACS2027.RAM.ramInput' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.ramInput

/-- info: 'STACS2027.RAM.rawPairs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.rawPairs

/-- info: 'STACS2027.RAM.varPairs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.varPairs

/-- info: 'STACS2027.RAM.clausePairs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.clausePairs

/-- info: 'STACS2027.RAM.clausePairsFrom' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.clausePairsFrom

/-- info: 'STACS2027.RAM.formulaPairs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.formulaPairs

/-- info: 'STACS2027.RAM.edgeWord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.edgeWord

/-- info: 'STACS2027.RAM.ramOutput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.ramOutput

/-- info: 'STACS2027.RAM.formulaRecords_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.formulaRecords_pairs

/-- info: 'STACS2027.RAM.formulaGraph_eq_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.formulaGraph_eq_pairs

/-- info: 'STACS2027.RAM.Reg.p' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.p

/-- info: 'STACS2027.RAM.Reg.m' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.m

/-- info: 'STACS2027.RAM.Reg.len' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.len

/-- info: 'STACS2027.RAM.Reg.v' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.v

/-- info: 'STACS2027.RAM.Reg.sg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.sg

/-- info: 'STACS2027.RAM.Reg.n' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.n

/-- info: 'STACS2027.RAM.Reg.t' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.t

/-- info: 'STACS2027.RAM.Reg.one' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.one

/-- info: 'STACS2027.RAM.Reg.N' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.N

/-- info: 'STACS2027.RAM.Reg.B' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.B

/-- info: 'STACS2027.RAM.Reg.vb' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.vb

/-- info: 'STACS2027.RAM.Reg.cv' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.cv

/-- info: 'STACS2027.RAM.Reg.vi' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.vi

/-- info: 'STACS2027.RAM.Reg.W' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.W

/-- info: 'STACS2027.RAM.Reg.cb' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.cb

/-- info: 'STACS2027.RAM.Reg.addr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.addr

/-- info: 'STACS2027.RAM.Reg.cc' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.cc

/-- info: 'STACS2027.RAM.Reg.x' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.x

/-- info: 'STACS2027.RAM.Reg.zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.Reg.zero

/-- info: 'STACS2027.RAM.bReg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg

/-- info: 'STACS2027.RAM.eReg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg

/-- info: 'STACS2027.RAM.litA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.litA

/-- info: 'STACS2027.RAM.clauseA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseA

/-- info: 'STACS2027.RAM.passA' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passA

/-- info: 'STACS2027.RAM.edgeConst' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.edgeConst

/-- info: 'STACS2027.RAM.varEmit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.varEmit

/-- info: 'STACS2027.RAM.varBody' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.varBody

/-- info: 'STACS2027.RAM.passV' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passV

/-- info: 'STACS2027.RAM.readLit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.readLit

/-- info: 'STACS2027.RAM.endpointCode' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.endpointCode

/-- info: 'STACS2027.RAM.clauseEmit' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseEmit

/-- info: 'STACS2027.RAM.clauseB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.clauseB

/-- info: 'STACS2027.RAM.passB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.passB

/-- info: 'STACS2027.RAM.program' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.program

/-- info: 'STACS2027.RAM.eReg_ne_p' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_p

/-- info: 'STACS2027.RAM.p_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.p_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_p' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_p

/-- info: 'STACS2027.RAM.p_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.p_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_m' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_m

/-- info: 'STACS2027.RAM.m_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.m_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_m' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_m

/-- info: 'STACS2027.RAM.m_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.m_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_len

/-- info: 'STACS2027.RAM.len_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.len_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_len

/-- info: 'STACS2027.RAM.len_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.len_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_v' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_v

/-- info: 'STACS2027.RAM.v_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.v_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_v' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_v

/-- info: 'STACS2027.RAM.v_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.v_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_sg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_sg

/-- info: 'STACS2027.RAM.sg_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.sg_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_sg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_sg

/-- info: 'STACS2027.RAM.sg_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.sg_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_n

/-- info: 'STACS2027.RAM.n_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.n_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_n

/-- info: 'STACS2027.RAM.n_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.n_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_t' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_t

/-- info: 'STACS2027.RAM.t_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.t_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_t' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_t

/-- info: 'STACS2027.RAM.t_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.t_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_one

/-- info: 'STACS2027.RAM.one_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.one_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_one

/-- info: 'STACS2027.RAM.one_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.one_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_N' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_N

/-- info: 'STACS2027.RAM.N_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.N_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_N' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_N

/-- info: 'STACS2027.RAM.N_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.N_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_B' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_B

/-- info: 'STACS2027.RAM.B_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.B_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_B' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_B

/-- info: 'STACS2027.RAM.B_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.B_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_vb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_vb

/-- info: 'STACS2027.RAM.vb_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.vb_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_vb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_vb

/-- info: 'STACS2027.RAM.vb_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.vb_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_cv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_cv

/-- info: 'STACS2027.RAM.cv_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cv_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_cv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_cv

/-- info: 'STACS2027.RAM.cv_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cv_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_vi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_vi

/-- info: 'STACS2027.RAM.vi_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.vi_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_vi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_vi

/-- info: 'STACS2027.RAM.vi_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.vi_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_W' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_W

/-- info: 'STACS2027.RAM.W_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.W_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_W' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_W

/-- info: 'STACS2027.RAM.W_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.W_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_cb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_cb

/-- info: 'STACS2027.RAM.cb_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cb_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_cb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_cb

/-- info: 'STACS2027.RAM.cb_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cb_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_addr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_addr

/-- info: 'STACS2027.RAM.addr_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.addr_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_addr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_addr

/-- info: 'STACS2027.RAM.addr_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.addr_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_cc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_cc

/-- info: 'STACS2027.RAM.cc_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cc_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_cc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_cc

/-- info: 'STACS2027.RAM.cc_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.cc_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_x' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_x

/-- info: 'STACS2027.RAM.x_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.x_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_x' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_x

/-- info: 'STACS2027.RAM.x_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.x_ne_bReg

/-- info: 'STACS2027.RAM.eReg_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_zero

/-- info: 'STACS2027.RAM.zero_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.zero_ne_eReg

/-- info: 'STACS2027.RAM.bReg_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_zero

/-- info: 'STACS2027.RAM.zero_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.zero_ne_bReg

/-- info: 'STACS2027.RAM.bReg_ne_eReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_ne_eReg

/-- info: 'STACS2027.RAM.eReg_ne_bReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_ne_bReg

/-- info: 'STACS2027.RAM.eReg_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_inj

/-- info: 'STACS2027.RAM.eReg_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.eReg_side

/-- info: 'STACS2027.RAM.bReg_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.bReg_inj

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

/-- info: 'STACS2027.RAM.reg_ite' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.reg_ite

/-- info: 'STACS2027.RAM.mem_ite' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.mem_ite

/-- info: 'STACS2027.RAM.out_ite' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.out_ite

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

/-- info: 'STACS2027.RAM.addrOK_loop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_loop

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

/-- info: 'STACS2027.RAM.addrOK_seqs_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_seqs_cons

/-- info: 'STACS2027.RAM.addrOK_seqs_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_seqs_nil

/-- info: 'STACS2027.RAM.addrOK_seqs_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_seqs_append

/-- info: 'STACS2027.RAM.addrOK_of_memFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.addrOK_of_memFree

/-- info: 'STACS2027.RAM.AddrOK.of_memFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.of_memFree

/-- info: 'STACS2027.RAM.AddrOK.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.mono

/-- info: 'STACS2027.RAM.AddrOK.seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.seq

/-- info: 'STACS2027.RAM.AddrOK.ifz' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.ifz

/-- info: 'STACS2027.RAM.AddrOK.append_memFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.AddrOK.append_memFree

/-- info: 'STACS2027.RAM.memFree_seqs_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_seqs_cons

/-- info: 'STACS2027.RAM.memFree_seqs_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_seqs_nil

/-- info: 'STACS2027.RAM.memFree_seqs_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_seqs_append

/-- info: 'STACS2027.RAM.memFree_flatMap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.memFree_flatMap

/-- info: 'STACS2027.RAM.execB_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.execB_run

/-- info: 'STACS2027.RAM.SatB' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SatB

/-- info: 'STACS2027.RAM.SatB.toSat' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SatB.toSat

/-- info: 'STACS2027.RAM.SatB.of_Sat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.SatB.of_Sat

/-- info: 'STACS2027.RAM.SatB.mono_S' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SatB.mono_S

/-- info: 'STACS2027.RAM.SatB.ofLoopFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.SatB.ofLoopFree

/-- info: 'STACS2027.RAM.SatB.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SatB.mono

/-- info: 'STACS2027.RAM.SatB.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RAM.SatB.congr

/-- info: 'STACS2027.RAM.SatB.seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.SatB.seq

/-- info: 'STACS2027.RAM.SatB.loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RAM.SatB.loop

/-- info: 'STACS2027.RAM.SatB.computesIn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.RAM.SatB.computesIn

/-- info: 'STACS2027.boolLists' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.boolLists

/-- info: 'STACS2027.ofList' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.ofList

/-- info: 'STACS2027.boolLists_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.boolLists_length

/-- info: 'STACS2027.length_of_mem_boolLists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.length_of_mem_boolLists

/-- info: 'STACS2027.getD_append_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.getD_append_left

/-- info: 'STACS2027.getD_append_end' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.getD_append_end

/-- info: 'STACS2027.countP_flatMap_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.countP_flatMap_pair

/-- info: 'STACS2027.count_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.count_one

/-- info: 'STACS2027.count_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.count_two

/-- info: 'STACS2027.clause_satisfied_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.clause_satisfied_count

/-- info: 'STACS2027.sum_satisfiedCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_satisfiedCount

/-- info: 'STACS2027.exists_ge_of_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_ge_of_sum

/-- info: 'STACS2027.exists_three_quarters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.exists_three_quarters

/-- info: 'STACS2027.Registered.setupClause' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.setupClause

/-- info: 'STACS2027.Registered.setupModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.setupModel

/-- info: 'STACS2027.Registered.setupCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.setupCost

/-- info: 'STACS2027.Registered.setupClause_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.setupClause_writes

/-- info: 'STACS2027.Registered.Spec.setupClause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.setupClause

/-- info: 'STACS2027.Registered.slotRegs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotRegs

/-- info: 'STACS2027.Registered.clearAll' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.clearAll

/-- info: 'STACS2027.Registered.clearAllModel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.clearAllModel

/-- info: 'STACS2027.Registered.clearAll_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clearAll_writes

/-- info: 'STACS2027.Registered.Spec.clearAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.clearAll

/-- info: 'STACS2027.Registered.finishClause' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.finishClause

/-- info: 'STACS2027.Registered.finishModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.finishModel

/-- info: 'STACS2027.Registered.finishCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.finishCost

/-- info: 'STACS2027.Registered.finishClause_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.finishClause_writes

/-- info: 'STACS2027.Registered.gadgetWidth_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.gadgetWidth_pos

/-- info: 'STACS2027.Registered.Work.set_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.set_slot

/-- info: 'STACS2027.Registered.gadgetEdges' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.gadgetEdges

/-- info: 'STACS2027.Registered.clauseEndpoint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseEndpoint

/-- info: 'STACS2027.Registered.clauseEdges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseEdges

/-- info: 'STACS2027.Registered.clauseEndpoint_sane' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseEndpoint_sane

/-- info: 'STACS2027.Registered.clauseEndpoint_constant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseEndpoint_constant

/-- info: 'STACS2027.Registered.gadgetEdges_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.gadgetEdges_below

/-- info: 'STACS2027.Registered.clauseEndpoint_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseEndpoint_good

/-- info: 'STACS2027.Registered.Work.emitEdge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.emitEdge

/-- info: 'STACS2027.Registered.recordBound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.recordBound

/-- info: 'STACS2027.Registered.clauseEdges_length_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseEdges_length_le

/-- info: 'STACS2027.Registered.clauseEmitCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseEmitCost

/-- info: 'STACS2027.Registered.Spec.clauseEmit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.clauseEmit

/-- info: 'STACS2027.Registered.ClauseInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.ClauseInv

/-- info: 'STACS2027.Registered.BodyPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPre

/-- info: 'STACS2027.Registered.BodyPost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPost

/-- info: 'STACS2027.Registered.clauseLits' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseLits

/-- info: 'STACS2027.Registered.clauseLitsModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseLitsModel

/-- info: 'STACS2027.Registered.clauseK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseK

/-- info: 'STACS2027.Registered.clauseKModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseKModel

/-- info: 'STACS2027.Registered.clauseKCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseKCost

/-- info: 'STACS2027.Registered.BodyPre.readLit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPre.readLit

/-- info: 'STACS2027.Registered.Spec.clauseLits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.clauseLits

/-- info: 'STACS2027.Registered.BodyPre.clauseLits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPre.clauseLits

/-- info: 'STACS2027.Registered.BodyPre.setup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPre.setup

/-- info: 'STACS2027.Registered.BodyPre.emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPre.emit

/-- info: 'STACS2027.Registered.BodyPost.finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPost.finish

/-- info: 'STACS2027.Registered.Spec.clauseK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.clauseK

/-- info: 'STACS2027.Registered.BodyPre.clauseK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPre.clauseK

/-- info: 'STACS2027.Registered.caseLen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.caseLen

/-- info: 'STACS2027.Registered.caseLenModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.caseLenModel

/-- info: 'STACS2027.Registered.caseLen_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.caseLen_writes

/-- info: 'STACS2027.Registered.Spec.caseLen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.caseLen

/-- info: 'STACS2027.Registered.clauseBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseBody

/-- info: 'STACS2027.Registered.clauseBodyModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseBodyModel

/-- info: 'STACS2027.Registered.clauseBodyCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseBodyCost

/-- info: 'STACS2027.Registered.BodyPre.set_len' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPre.set_len

/-- info: 'STACS2027.Registered.BodyPre.readLen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPre.readLen

/-- info: 'STACS2027.Registered.Spec.clauseBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.clauseBody

/-- info: 'STACS2027.Registered.BodyPre.clauseBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.BodyPre.clauseBody

/-- info: 'STACS2027.Registered.clauseBody_writes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseBody_writes

/-- info: 'STACS2027.Registered.passB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.passB

/-- info: 'STACS2027.Registered.passBModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.passBModel

/-- info: 'STACS2027.Registered.passBCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.passBCost

/-- info: 'STACS2027.Registered.recordBudget' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.recordBudget

/-- info: 'STACS2027.Registered.PassBPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.PassBPre

/-- info: 'STACS2027.Registered.ClauseInv.pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.ClauseInv.pop

/-- info: 'STACS2027.Registered.PassBPre.start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.PassBPre.start

/-- info: 'STACS2027.Registered.Spec.passB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.passB

/-- info: 'STACS2027.Registered.finishModel_j' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.finishModel_j

/-- info: 'STACS2027.Registered.finishModel_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.finishModel_other

/-- info: 'STACS2027.Registered.emitEdgesModel_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEdgesModel_out

/-- info: 'STACS2027.Registered.emitEdgesModel_cnt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEdgesModel_cnt

/-- info: 'STACS2027.Registered.emitEdgesModel_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEdgesModel_other

/-- info: 'STACS2027.Registered.setupModel_bnj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.setupModel_bnj

/-- info: 'STACS2027.Registered.setupModel_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.setupModel_other

/-- info: 'STACS2027.Registered.litState_inB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litState_inB

/-- info: 'STACS2027.Registered.litState_done' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litState_done

/-- info: 'STACS2027.Registered.litState_dc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litState_dc

/-- info: 'STACS2027.Registered.litState_B' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litState_B

/-- info: 'STACS2027.Registered.litState_E' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litState_E

/-- info: 'STACS2027.Registered.litRegs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litRegs

/-- info: 'STACS2027.Registered.litState_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litState_other

/-- info: 'STACS2027.Registered.clauseEndpoint_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseEndpoint_value

/-- info: 'STACS2027.Registered.clauseEdges_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseEdges_records

/-- info: 'STACS2027.Registered.unary_append_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.unary_append_comm

/-- info: 'STACS2027.Registered.tail_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.tail_eval

/-- info: 'STACS2027.Registered.allLitRegs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.allLitRegs

/-- info: 'STACS2027.Registered.litRegs_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.litRegs_sub

/-- info: 'STACS2027.Registered.slot_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.slot_not_mem

/-- info: 'STACS2027.Registered.placeLiterals_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.placeLiterals_two

/-- info: 'STACS2027.Registered.placeLiterals_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.placeLiterals_three

/-- info: 'STACS2027.Registered.placed_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.placed_eq

/-- info: 'STACS2027.Registered.count_rev_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.count_rev_cons

/-- info: 'STACS2027.Registered.count_rev_cons₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.count_rev_cons₂

/-- info: 'STACS2027.Registered.SlotFacts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.SlotFacts

/-- info: 'STACS2027.Registered.lits_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.lits_eval

/-- info: 'STACS2027.Registered.encodeClause_split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.encodeClause_split

/-- info: 'STACS2027.Registered.placeLiterals_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.placeLiterals_length

/-- info: 'STACS2027.Registered.caseLen_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.caseLen_eval

/-- info: 'STACS2027.Registered.bodyRegs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.bodyRegs

/-- info: 'STACS2027.Registered.body_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.body_eval

/-- info: 'STACS2027.Registered.writeValues_reverse_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.writeValues_reverse_append

/-- info: 'STACS2027.Registered.passB_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.passB_iter

/-- info: 'STACS2027.Registered.varRecords_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.varRecords_succ

/-- info: 'STACS2027.Registered.variableEdges_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.variableEdges_records

/-- info: 'STACS2027.Registered.var_iter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.var_iter

/-- info: 'STACS2027.Registered.litA_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.litA_eval

/-- info: 'STACS2027.Registered.litA_iter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.litA_iter

/-- info: 'STACS2027.Registered.clauseA_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseA_eval

/-- info: 'STACS2027.Registered.passA_iter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.passA_iter

/-- info: 'STACS2027.Registered.initModel_read' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.initModel_read

/-- info: 'STACS2027.Registered.mainModel_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.mainModel_encode

/-- info: 'STACS2027.Registered.instanceMapWord_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.instanceMapWord_encode

/-- info: 'STACS2027.Registered.K' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.K

/-- info: 'STACS2027.Registered.Regs' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Regs

/-- info: 'STACS2027.Registered.Reg' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Reg

/-- info: 'STACS2027.Registered.Realizes' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Realizes

/-- info: 'STACS2027.Registered.Spec' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec

/-- info: 'STACS2027.Registered.SpecT' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.SpecT

/-- info: 'STACS2027.Registered.Spec.of_total' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.of_total

/-- info: 'STACS2027.Registered.Spec.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.mono

/-- info: 'STACS2027.Registered.Spec.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.congr

/-- info: 'STACS2027.Registered.Spec.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.frame

/-- info: 'STACS2027.Registered.Spec.seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.seq

/-- info: 'STACS2027.Registered.iter' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.iter

/-- info: 'STACS2027.Registered.iter_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.iter_nil

/-- info: 'STACS2027.Registered.iter_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.iter_cons

/-- info: 'STACS2027.Registered.Spec.repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.repeat

/-- info: 'STACS2027.Registered.iter_invariant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.iter_invariant

/-- info: 'STACS2027.Registered.Spec.branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.branch

/-- info: 'STACS2027.Registered.Spec.ifThenElse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.ifThenElse

/-- info: 'STACS2027.Registered.Spec.stop_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.stop_true

/-- info: 'STACS2027.Registered.Spec.stop_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.stop_false

/-- info: 'STACS2027.Registered.Spec.push' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.push

/-- info: 'STACS2027.Registered.Spec.pop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.pop

/-- info: 'STACS2027.Registered.Spec.clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.clear

/-- info: 'STACS2027.Registered.Spec.copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.copy

/-- info: 'STACS2027.Registered.Spec.length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.length

/-- info: 'STACS2027.Registered.Spec.add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.add

/-- info: 'STACS2027.Registered.Spec.multiply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.multiply

/-- info: 'STACS2027.Registered.Spec.prependNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.prependNat

/-- info: 'STACS2027.Registered.Spec.prependLiteral' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.prependLiteral

/-- info: 'STACS2027.Registered.pushN' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.pushN

/-- info: 'STACS2027.Registered.Spec.pushN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.pushN

/-- info: 'STACS2027.Registered.Base' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Base

/-- info: 'STACS2027.Registered.Base.set' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Base.set

/-- info: 'STACS2027.Registered.Work' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work

/-- info: 'STACS2027.Registered.Work.v' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.v

/-- info: 'STACS2027.Registered.Work.sg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.sg

/-- info: 'STACS2027.Registered.Work.b' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.b

/-- info: 'STACS2027.Registered.Work.e' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.e

/-- info: 'STACS2027.Registered.setSign' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.setSign

/-- info: 'STACS2027.Registered.exec_setSign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.exec_setSign

/-- info: 'STACS2027.Registered.litRest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litRest

/-- info: 'STACS2027.Registered.readLitCode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.readLitCode

/-- info: 'STACS2027.Registered.afterLit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.afterLit

/-- info: 'STACS2027.Registered.readLitCodeModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.readLitCodeModel

/-- info: 'STACS2027.Registered.readLitCodeModel_encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.readLitCodeModel_encode

/-- info: 'STACS2027.Registered.readLitCodeCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.readLitCodeCost

/-- info: 'STACS2027.Registered.exec_litRest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.exec_litRest

/-- info: 'STACS2027.Registered.Spec.readLitCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.readLitCode

/-- info: 'STACS2027.Registered.cmp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.cmp

/-- info: 'STACS2027.Registered.cmpIf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.cmpIf

/-- info: 'STACS2027.Registered.sgTest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.sgTest

/-- info: 'STACS2027.Registered.scanTail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.scanTail

/-- info: 'STACS2027.Registered.scanStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.scanStep

/-- info: 'STACS2027.Registered.scanStepModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.scanStepModel

/-- info: 'STACS2027.Registered.scanStepCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.scanStepCost

/-- info: 'STACS2027.Registered.scanStep_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.scanStep_writes

/-- info: 'STACS2027.Registered.exec_eqU_sv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.exec_eqU_sv

/-- info: 'STACS2027.Registered.exec_cmpIf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.exec_cmpIf

/-- info: 'STACS2027.Registered.exec_scanTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.exec_scanTail

/-- info: 'STACS2027.Registered.Spec.scanStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.scanStep

/-- info: 'STACS2027.Registered.Base.of_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Base.of_eq

/-- info: 'STACS2027.Registered.slot_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.slot_cases

/-- info: 'STACS2027.Registered.scanStart' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.scanStart

/-- info: 'STACS2027.Registered.Work.readLitCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.readLitCode

/-- info: 'STACS2027.Registered.scanLoop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.scanLoop

/-- info: 'STACS2027.Registered.scanLoopModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.scanLoopModel

/-- info: 'STACS2027.Registered.scanLoopCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.scanLoopCost

/-- info: 'STACS2027.Registered.ScanInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.ScanInv

/-- info: 'STACS2027.Registered.Work.scanStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.scanStep

/-- info: 'STACS2027.Registered.ScanInv.start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.ScanInv.start

/-- info: 'STACS2027.Registered.Work.scanLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.scanLoop

/-- info: 'STACS2027.Registered.Spec.scanLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.scanLoop

/-- info: 'STACS2027.Registered.scanLoop_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.scanLoop_writes

/-- info: 'STACS2027.Registered.portEndpoints' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.portEndpoints

/-- info: 'STACS2027.Registered.portState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.portState

/-- info: 'STACS2027.Registered.portModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.portModel

/-- info: 'STACS2027.Registered.portCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.portCost

/-- info: 'STACS2027.Registered.portEndpoints_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.portEndpoints_writes

/-- info: 'STACS2027.Registered.Spec.portEndpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.portEndpoints

/-- info: 'STACS2027.Registered.Work.port' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.port

/-- info: 'STACS2027.Registered.mulW' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.mulW

/-- info: 'STACS2027.Registered.mulWModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.mulWModel

/-- info: 'STACS2027.Registered.mulWCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.mulWCost

/-- info: 'STACS2027.Registered.Spec.mulW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.mulW

/-- info: 'STACS2027.Registered.Work.mulW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.mulW

/-- info: 'STACS2027.Registered.readLit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.readLit

/-- info: 'STACS2027.Registered.readLitModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.readLitModel

/-- info: 'STACS2027.Registered.readLitCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.readLitCost

/-- info: 'STACS2027.Registered.Work.readLit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Work.readLit

/-- info: 'STACS2027.Registered.Spec.readLit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.readLit

/-- info: 'STACS2027.Registered.readLit_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.readLit_writes

/-- info: 'STACS2027.Registered.initPhase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.initPhase

/-- info: 'STACS2027.Registered.initModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.initModel

/-- info: 'STACS2027.Registered.initCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.initCost

/-- info: 'STACS2027.Registered.initRegs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.initRegs

/-- info: 'STACS2027.Registered.zeroRegs₁' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.zeroRegs₁

/-- info: 'STACS2027.Registered.Initialized' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Initialized

/-- info: 'STACS2027.Registered.initModel_initialized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.initModel_initialized

/-- info: 'STACS2027.Registered.Spec.initPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.initPhase

/-- info: 'STACS2027.Registered.main' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.main

/-- info: 'STACS2027.Registered.mainModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.mainModel

/-- info: 'STACS2027.Registered.mainCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.mainCost

/-- info: 'STACS2027.Registered.varLoop_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.varLoop_writes

/-- info: 'STACS2027.Registered.Initialized.passA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Initialized.passA

/-- info: 'STACS2027.Registered.Initialized.varLoopPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Initialized.varLoopPre

/-- info: 'STACS2027.Registered.AfterVar' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.AfterVar

/-- info: 'STACS2027.Registered.Initialized.varLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Initialized.varLoop

/-- info: 'STACS2027.Registered.AfterVar.passBPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.AfterVar.passBPre

/-- info: 'STACS2027.Registered.Spec.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.main

/-- info: 'STACS2027.Registered.program' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.program

/-- info: 'STACS2027.Registered.exec_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.exec_program

/-- info: 'STACS2027.Registered.machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.machine

/-- info: 'STACS2027.Registered.bound' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.bound

/-- info: 'STACS2027.Registered.machine_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.machine_run

/-- info: 'STACS2027.Registered.instanceMapWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.instanceMapWord

/-- info: 'STACS2027.Registered.instanceMapWord_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.instanceMapWord_eq

/-- info: 'STACS2027.Registered.machine_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.machine_computes

/-- info: 'STACS2027.Registered.pb_affine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_affine

/-- info: 'STACS2027.Registered.pb_edgeCost_W' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_edgeCost_W

/-- info: 'STACS2027.Registered.pb_edgeCost_2W' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_edgeCost_2W

/-- info: 'STACS2027.Registered.pb_readLitCodeCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_readLitCodeCost

/-- info: 'STACS2027.Registered.pb_scanStepCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_scanStepCost

/-- info: 'STACS2027.Registered.pb_scanLoopCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_scanLoopCost

/-- info: 'STACS2027.Registered.pb_mulWCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_mulWCost

/-- info: 'STACS2027.Registered.pb_readLitCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_readLitCost

/-- info: 'STACS2027.Registered.pb_setupCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_setupCost

/-- info: 'STACS2027.Registered.pb_clauseEmitCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_clauseEmitCost

/-- info: 'STACS2027.Registered.pb_finishCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_finishCost

/-- info: 'STACS2027.Registered.pb_clauseKCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_clauseKCost

/-- info: 'STACS2027.Registered.pb_clauseBodyCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_clauseBodyCost

/-- info: 'STACS2027.Registered.pb_passBCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_passBCost

/-- info: 'STACS2027.Registered.pb_varBodyCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_varBodyCost

/-- info: 'STACS2027.Registered.pb_varLoopCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_varLoopCost

/-- info: 'STACS2027.Registered.pb_litACost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_litACost

/-- info: 'STACS2027.Registered.pb_clauseACost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_clauseACost

/-- info: 'STACS2027.Registered.pb_passACost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_passACost

/-- info: 'STACS2027.Registered.pb_initCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_initCost

/-- info: 'STACS2027.Registered.pb_recordBudget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_recordBudget

/-- info: 'STACS2027.Registered.pb_mainCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pb_mainCost

/-- info: 'STACS2027.Registered.polynomial_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.polynomial_bound

/-- info: 'STACS2027.Registered.polyTime_instanceMapWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.polyTime_instanceMapWord

/-- info: 'STACS2027.Registered.readUnary' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.readUnary

/-- info: 'STACS2027.Registered.readUnaryModel' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.readUnaryModel

/-- info: 'STACS2027.Registered.readUnaryModel_writeNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.readUnaryModel_writeNat

/-- info: 'STACS2027.Registered.readUnary_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.readUnary_writes

/-- info: 'STACS2027.Registered.Spec.readUnary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.readUnary

/-- info: 'STACS2027.Registered.leU' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.leU

/-- info: 'STACS2027.Registered.SpecT.leU' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.SpecT.leU

/-- info: 'STACS2027.Registered.Endpoint' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Endpoint

/-- info: 'STACS2027.Registered.Endpoint.value' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Endpoint.value

/-- info: 'STACS2027.Registered.Endpoint.constant' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Endpoint.constant

/-- info: 'STACS2027.Registered.emitEndpoint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEndpoint

/-- info: 'STACS2027.Registered.emitEndpointModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEndpointModel

/-- info: 'STACS2027.Registered.Endpoint.Good' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.Endpoint.Good

/-- info: 'STACS2027.Registered.Endpoint.value_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Endpoint.value_le

/-- info: 'STACS2027.Registered.Endpoint.Sane' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Endpoint.Sane

/-- info: 'STACS2027.Registered.Endpoint.value_set' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Endpoint.value_set

/-- info: 'STACS2027.Registered.pushN_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.pushN_writes

/-- info: 'STACS2027.Registered.emitEndpoint_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEndpoint_writes

/-- info: 'STACS2027.Registered.Spec.emitEndpoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.emitEndpoint

/-- info: 'STACS2027.Registered.emitEdge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEdge

/-- info: 'STACS2027.Registered.edgeRecord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.edgeRecord

/-- info: 'STACS2027.Registered.emitEdgeModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEdgeModel

/-- info: 'STACS2027.Registered.encodeClause_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.encodeClause_two

/-- info: 'STACS2027.Registered.Spec.emitEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.emitEdge

/-- info: 'STACS2027.Registered.emitEdge_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEdge_writes

/-- info: 'STACS2027.Registered.emitEdges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEdges

/-- info: 'STACS2027.Registered.recordsWord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.recordsWord

/-- info: 'STACS2027.Registered.emitEdgesModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEdgesModel

/-- info: 'STACS2027.Registered.writeValues_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.writeValues_append

/-- info: 'STACS2027.Registered.Endpoint.value_emitEdgeModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Endpoint.value_emitEdgeModel

/-- info: 'STACS2027.Registered.Endpoint.good_emitEdgeModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.Endpoint.good_emitEdgeModel

/-- info: 'STACS2027.Registered.edgeRecord_emitEdgeModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.edgeRecord_emitEdgeModel

/-- info: 'STACS2027.Registered.recordsWord_emitEdgeModel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.recordsWord_emitEdgeModel

/-- info: 'STACS2027.Registered.edgeCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.edgeCost

/-- info: 'STACS2027.Registered.Spec.emitEdges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.emitEdges

/-- info: 'STACS2027.Registered.emitEdges_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.emitEdges_writes

/-- info: 'STACS2027.Registered.variableEdges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.variableEdges

/-- info: 'STACS2027.Registered.varBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.varBody

/-- info: 'STACS2027.Registered.varBodyModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.varBodyModel

/-- info: 'STACS2027.Registered.varLoop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.varLoop

/-- info: 'STACS2027.Registered.varLoopModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.varLoopModel

/-- info: 'STACS2027.Registered.varBodyCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.varBodyCost

/-- info: 'STACS2027.Registered.varLoopCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.varLoopCost

/-- info: 'STACS2027.Registered.VarInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.VarInv

/-- info: 'STACS2027.Registered.VarPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.VarPre

/-- info: 'STACS2027.Registered.VarInv.pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.VarInv.pop

/-- info: 'STACS2027.Registered.variableEdges_sane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.variableEdges_sane

/-- info: 'STACS2027.Registered.variableEdges_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.variableEdges_constant

/-- info: 'STACS2027.Registered.VarEmit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.VarEmit

/-- info: 'STACS2027.Registered.Spec.varBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.varBody

/-- info: 'STACS2027.Registered.VarPre.body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.VarPre.body

/-- info: 'STACS2027.Registered.varBody_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.varBody_writes

/-- info: 'STACS2027.Registered.VarLoopPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.VarLoopPre

/-- info: 'STACS2027.Registered.VarLoopPre.start' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.VarLoopPre.start

/-- info: 'STACS2027.Registered.Spec.varLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.varLoop

/-- info: 'STACS2027.Registered.VarLoopPre.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.VarLoopPre.run

/-- info: 'STACS2027.Registered.maxStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.maxStep

/-- info: 'STACS2027.Registered.litA'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litA'

/-- info: 'STACS2027.Registered.litA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litA

/-- info: 'STACS2027.Registered.litAModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litAModel

/-- info: 'STACS2027.Registered.litACost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.litACost

/-- info: 'STACS2027.Registered.AInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.AInv

/-- info: 'STACS2027.Registered.AInv.set_inA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.AInv.set_inA

/-- info: 'STACS2027.Registered.AInv.set_m' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.AInv.set_m

/-- info: 'STACS2027.Registered.AInv.set_len' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.AInv.set_len

/-- info: 'STACS2027.Registered.exec_maxStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.exec_maxStep

/-- info: 'STACS2027.Registered.Spec.litA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.litA

/-- info: 'STACS2027.Registered.AInv.litA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.AInv.litA

/-- info: 'STACS2027.Registered.litA_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litA_writes

/-- info: 'STACS2027.Registered.clauseA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseA

/-- info: 'STACS2027.Registered.clauseAModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseAModel

/-- info: 'STACS2027.Registered.clauseACost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseACost

/-- info: 'STACS2027.Registered.AInv.readUnary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.AInv.readUnary

/-- info: 'STACS2027.Registered.AInv.pop_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.AInv.pop_len

/-- info: 'STACS2027.Registered.AInv.pop_m' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.AInv.pop_m

/-- info: 'STACS2027.Registered.Spec.clauseA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.clauseA

/-- info: 'STACS2027.Registered.AInv.clauseA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.AInv.clauseA

/-- info: 'STACS2027.Registered.clauseA_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseA_writes

/-- info: 'STACS2027.Registered.passA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.passA

/-- info: 'STACS2027.Registered.passAModel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.passAModel

/-- info: 'STACS2027.Registered.passACost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.passACost

/-- info: 'STACS2027.Registered.Spec.passA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.Spec.passA

/-- info: 'STACS2027.Registered.AInv.passA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.AInv.passA

/-- info: 'STACS2027.Registered.passA_writes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.passA_writes

/-- info: 'STACS2027.Registered.pairRecord' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.pairRecord

/-- info: 'STACS2027.Registered.rawRecords' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.rawRecords

/-- info: 'STACS2027.Registered.pairRecord_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.pairRecord_output

/-- info: 'STACS2027.Registered.rawRecords_output' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.rawRecords_output

/-- info: 'STACS2027.Registered.GraphOutput.reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.GraphOutput.reverse

/-- info: 'STACS2027.Registered.GraphOutput.mapIdx_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.GraphOutput.mapIdx_flatten

/-- info: 'STACS2027.Registered.varRecords' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.varRecords

/-- info: 'STACS2027.Registered.clauseRecords' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseRecords

/-- info: 'STACS2027.Registered.clauseRecordsFrom' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseRecordsFrom

/-- info: 'STACS2027.Registered.clauseRecordsFrom_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.clauseRecordsFrom_eq

/-- info: 'STACS2027.Registered.formulaRecords' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.formulaRecords

/-- info: 'STACS2027.Registered.formulaRecords_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.formulaRecords_output

/-- info: 'STACS2027.Registered.R.out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.out

/-- info: 'STACS2027.Registered.R.inA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.inA

/-- info: 'STACS2027.Registered.R.inB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.inB

/-- info: 'STACS2027.Registered.R.s' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.s

/-- info: 'STACS2027.Registered.R.g' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.g

/-- info: 'STACS2027.Registered.R.mc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.mc

/-- info: 'STACS2027.Registered.R.cnt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.cnt

/-- info: 'STACS2027.Registered.R.W' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.W

/-- info: 'STACS2027.Registered.R.two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.two

/-- info: 'STACS2027.Registered.R.n' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.n

/-- info: 'STACS2027.Registered.R.j' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.j

/-- info: 'STACS2027.Registered.R.nj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.nj

/-- info: 'STACS2027.Registered.R.bnj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.bnj

/-- info: 'STACS2027.Registered.R.done' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.done

/-- info: 'STACS2027.Registered.R.dc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.dc

/-- info: 'STACS2027.Registered.R.m' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.m

/-- info: 'STACS2027.Registered.R.len' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.len

/-- info: 'STACS2027.Registered.R.tmp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.tmp

/-- info: 'STACS2027.Registered.R.t1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.t1

/-- info: 'STACS2027.Registered.R.t2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.t2

/-- info: 'STACS2027.Registered.R.scan' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.scan

/-- info: 'STACS2027.Registered.R.sc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.sc

/-- info: 'STACS2027.Registered.R.sv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.sv

/-- info: 'STACS2027.Registered.R.cE' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.cE

/-- info: 'STACS2027.Registered.R.v0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.v0

/-- info: 'STACS2027.Registered.R.v1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.v1

/-- info: 'STACS2027.Registered.R.v2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.v2

/-- info: 'STACS2027.Registered.R.sg0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.sg0

/-- info: 'STACS2027.Registered.R.sg1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.sg1

/-- info: 'STACS2027.Registered.R.sg2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.sg2

/-- info: 'STACS2027.Registered.R.b0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.b0

/-- info: 'STACS2027.Registered.R.b1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.b1

/-- info: 'STACS2027.Registered.R.b2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.b2

/-- info: 'STACS2027.Registered.R.ef0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.ef0

/-- info: 'STACS2027.Registered.R.et0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.et0

/-- info: 'STACS2027.Registered.R.ef1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.ef1

/-- info: 'STACS2027.Registered.R.et1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.et1

/-- info: 'STACS2027.Registered.R.ef2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.ef2

/-- info: 'STACS2027.Registered.R.et2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.et2

/-- info: 'STACS2027.Registered.R.vb' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.vb

/-- info: 'STACS2027.Registered.R.vc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.vc

/-- info: 'STACS2027.Registered.R.x' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.R.x

/-- info: 'STACS2027.Registered.slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV

/-- info: 'STACS2027.Registered.slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS

/-- info: 'STACS2027.Registered.slotB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotB

/-- info: 'STACS2027.Registered.slotE' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotE

/-- info: 'STACS2027.Registered.unary' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.unary

/-- info: 'STACS2027.Registered.unary_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.unary_length

/-- info: 'STACS2027.Registered.unary_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.unary_zero

/-- info: 'STACS2027.Registered.unary_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.unary_succ

/-- info: 'STACS2027.Registered.unary_add' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.unary_add

/-- info: 'STACS2027.Registered.writeValues_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.writeValues_cons

/-- info: 'STACS2027.Registered.scanStepModel_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.scanStepModel_cons

/-- info: 'STACS2027.Registered.scan_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.scan_eval

/-- info: 'STACS2027.Registered.scanLoopModel_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.scanLoopModel_eval

/-- info: 'STACS2027.Registered.portModel_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.portModel_eval

/-- info: 'STACS2027.Registered.placed' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Registered.placed

/-- info: 'STACS2027.Registered.litState' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.litState

/-- info: 'STACS2027.Registered.readLitModel_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Registered.readLitModel_eval

/-- info: 'STACS2027.Registered.slotV_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_cases

/-- info: 'STACS2027.Registered.slotS_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_cases

/-- info: 'STACS2027.Registered.slotB_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotB_cases

/-- info: 'STACS2027.Registered.slotE_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotE_cases

/-- info: 'STACS2027.Registered.slotV_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne

/-- info: 'STACS2027.Registered.slotS_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne

/-- info: 'STACS2027.Registered.slotB_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotB_ne

/-- info: 'STACS2027.Registered.slotE_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotE_ne

/-- info: 'STACS2027.Registered.slotV_ne_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_out

/-- info: 'STACS2027.Registered.out_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.out_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_inA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_inA

/-- info: 'STACS2027.Registered.inA_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.inA_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_inB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_inB

/-- info: 'STACS2027.Registered.inB_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.inB_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_s' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_s

/-- info: 'STACS2027.Registered.s_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.s_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_g' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_g

/-- info: 'STACS2027.Registered.g_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.g_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_mc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_mc

/-- info: 'STACS2027.Registered.mc_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.mc_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_cnt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_cnt

/-- info: 'STACS2027.Registered.cnt_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.cnt_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_W' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_W

/-- info: 'STACS2027.Registered.W_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.W_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_two

/-- info: 'STACS2027.Registered.two_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.two_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_n' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_n

/-- info: 'STACS2027.Registered.n_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.n_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_j' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_j

/-- info: 'STACS2027.Registered.j_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.j_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_nj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_nj

/-- info: 'STACS2027.Registered.nj_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.nj_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_bnj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_bnj

/-- info: 'STACS2027.Registered.bnj_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.bnj_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_done' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_done

/-- info: 'STACS2027.Registered.done_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.done_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_dc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_dc

/-- info: 'STACS2027.Registered.dc_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.dc_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_m' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_m

/-- info: 'STACS2027.Registered.m_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.m_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_len' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_len

/-- info: 'STACS2027.Registered.len_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.len_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_tmp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_tmp

/-- info: 'STACS2027.Registered.tmp_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.tmp_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_t1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_t1

/-- info: 'STACS2027.Registered.t1_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.t1_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_t2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_t2

/-- info: 'STACS2027.Registered.t2_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.t2_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_scan' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_scan

/-- info: 'STACS2027.Registered.scan_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.scan_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_sc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_sc

/-- info: 'STACS2027.Registered.sc_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.sc_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_sv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_sv

/-- info: 'STACS2027.Registered.sv_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.sv_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_cE' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_cE

/-- info: 'STACS2027.Registered.cE_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.cE_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_vb' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_vb

/-- info: 'STACS2027.Registered.vb_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.vb_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_vc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_vc

/-- info: 'STACS2027.Registered.vc_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.vc_ne_slotV

/-- info: 'STACS2027.Registered.slotV_ne_x' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotV_ne_x

/-- info: 'STACS2027.Registered.x_ne_slotV' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.x_ne_slotV

/-- info: 'STACS2027.Registered.slotS_ne_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne_out

/-- info: 'STACS2027.Registered.out_ne_slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.out_ne_slotS

/-- info: 'STACS2027.Registered.slotS_ne_inA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne_inA

/-- info: 'STACS2027.Registered.inA_ne_slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.inA_ne_slotS

/-- info: 'STACS2027.Registered.slotS_ne_inB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne_inB

/-- info: 'STACS2027.Registered.inB_ne_slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.inB_ne_slotS

/-- info: 'STACS2027.Registered.slotS_ne_s' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne_s

/-- info: 'STACS2027.Registered.s_ne_slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.s_ne_slotS

/-- info: 'STACS2027.Registered.slotS_ne_g' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne_g

/-- info: 'STACS2027.Registered.g_ne_slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.g_ne_slotS

/-- info: 'STACS2027.Registered.slotS_ne_mc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne_mc

/-- info: 'STACS2027.Registered.mc_ne_slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.mc_ne_slotS

/-- info: 'STACS2027.Registered.slotS_ne_cnt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne_cnt

/-- info: 'STACS2027.Registered.cnt_ne_slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.cnt_ne_slotS

/-- info: 'STACS2027.Registered.slotS_ne_W' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne_W

/-- info: 'STACS2027.Registered.W_ne_slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.W_ne_slotS

/-- info: 'STACS2027.Registered.slotS_ne_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne_two

/-- info: 'STACS2027.Registered.two_ne_slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.two_ne_slotS

/-- info: 'STACS2027.Registered.slotS_ne_n' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.slotS_ne_n

/-- info: 'STACS2027.Registered.n_ne_slotS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.Registered.n_ne_slotS
