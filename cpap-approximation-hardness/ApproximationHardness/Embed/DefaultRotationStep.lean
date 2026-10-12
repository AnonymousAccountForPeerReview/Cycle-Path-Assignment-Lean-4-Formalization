module

public import ApproximationHardness.Embed.DefaultRotationRead
public import ApproximationHardness.Embed.DefaultRotationPure
import Lean.Elab.Tactic.Omega

/-! # Constant bounded step writing both default rotation caches -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

def rotationStore : Stmt := seqs [
  .add 257 261 240,.store 257 254,.add 257 262 240,.store 257 255,
  .add 240 240 1,.sub 241 241 1]

def defaultRotationStep : Stmt := .seq rotationRead (.seq nextPredCode rotationStore)
def defaultRotationLoop : Stmt := .loop 241 defaultRotationStep

theorem nextPredCode_reg (c : Config) (r : Nat)
    (hr : r≠254 ∧ r≠255 ∧ r≠263 ∧ r≠264) :
    (run nextPredCode c).reg r=c.reg r := by
  apply run_reg_frame
  simp only [nextPredCode,rotationIfEq,nextPredValues,seqs,regsW,List.mem_append,
    List.mem_cons,List.mem_nil_iff,or_false,not_or]
  repeat' constructor
  all_goals omega

theorem defaultRotationStep_loopFree : LoopFree defaultRotationStep := by
  exact ⟨rotationRead_loopFree,nextPredCode_loopFree,by simp [rotationStore,seqs,LoopFree]⟩

theorem defaultRotationStep_size : size defaultRotationStep≤1200 := by
  simp only [defaultRotationStep,size]
  have := rotationRead_size
  have := nextPredCode_size
  have hs : size rotationStore=7 := rfl
  omega

theorem rotationStore_mem (c : Config) (a : Nat) :
    (run rotationStore c).mem a=
      if a=c.reg 262+c.reg 240 then c.reg 255
      else if a=c.reg 261+c.reg 240 then c.reg 254 else c.mem a := by
  simp [rotationStore,seqs,run]

theorem defaultRotationStep_out (c : Config) : (run defaultRotationStep c).out=c.out := by
  simp only [defaultRotationStep,run]
  simp [rotationStore,seqs,run,nextPredCode_out,rotationRead_out]

theorem defaultRotationStep_reg (c : Config) (r : Nat)
    (hr : r<240 ∨ r=261 ∨ r=262 ∨ 265<r) :
    (run defaultRotationStep c).reg r=c.reg r := by
  apply run_reg_frame
  simp only [defaultRotationStep,rotationRead,readBothParts,readLeftPart,readRightPart,
    decodePart,nextPredCode,rotationIfEq,nextPredValues,rotationStore,seqs,regsW,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,not_or,not_false_eq_true]
  repeat' constructor
  all_goals omega

theorem defaultRotationStep_advance (c : Config) (hone : c.reg 1=1) :
    (run defaultRotationStep c).reg 240=c.reg 240+1 ∧
    (run defaultRotationStep c).reg 241=c.reg 241-1 := by
  simp only [defaultRotationStep,run]
  simp [rotationStore,seqs,run]
  rw [nextPredCode_reg _ 240 (by decide),nextPredCode_reg _ 241 (by decide),
    nextPredCode_reg _ 1 (by decide),rotationRead_reg _ 240 (by omega),
    rotationRead_reg _ 241 (by omega),rotationRead_reg _ 1 (by omega),hone]
  exact ⟨rfl,rfl⟩

theorem defaultRotationStep_mem (c : Config) (a : Nat) :
    (run defaultRotationStep c).mem a=
      if a=c.reg 262+c.reg 240 then (run nextPredCode (run rotationRead c)).reg 255
      else if a=c.reg 261+c.reg 240 then (run nextPredCode (run rotationRead c)).reg 254
      else c.mem a := by
  simp only [defaultRotationStep,run,rotationStore_mem]
  rw [nextPredCode_reg _ 262 (by decide),nextPredCode_reg _ 261 (by decide),
    nextPredCode_reg _ 240 (by decide),rotationRead_reg _ 262 (by omega),
    rotationRead_reg _ 261 (by omega),rotationRead_reg _ 240 (by omega),
    nextPredCode_mem,rotationRead_mem]

theorem defaultRotationStep_addrOK {S : Nat} (c : Config)
    (hread : AddrOK S rotationRead c)
    (hnext : c.reg 261+c.reg 240<S) (hpred : c.reg 262+c.reg 240<S) :
    AddrOK S defaultRotationStep c := by
  refine ⟨hread,AddrOK.of_memFree (by rfl),?_⟩
  simp [rotationStore,seqs,AddrOK,run,
    nextPredCode_reg _ 261 (by decide),nextPredCode_reg _ 262 (by decide),
    nextPredCode_reg _ 240 (by decide),rotationRead_reg _ 261 (by omega),
    rotationRead_reg _ 262 (by omega),rotationRead_reg _ 240 (by omega),hnext,hpred]


end STACS2027.Embed.RAMSolver
