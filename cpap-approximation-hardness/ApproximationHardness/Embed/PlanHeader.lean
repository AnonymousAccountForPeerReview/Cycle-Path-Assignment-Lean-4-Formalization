module

public import ApproximationHardness.Embed.DFSLoop
public import ApproximationHardness.Embed.SolverRAM
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! # Install the solver and distinguished-dart cache layout -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM

open RAM

def solverLayout (L : DFSRAM.Layout) : RAMSolver.Layout := ⟨L.limit,L.width⟩
def zLimit (L : DFSRAM.Layout) : Nat := (solverLayout L).limit + L.width

def solverHeader : Stmt := seqs [
  .add 2 170 148,
  .add 3 148 0,
  .add 50 2 0,
  .add 51 50 3,
  .add 52 51 3,
  .add 53 52 3,
  .add 54 53 3,
  .add 55 54 3,
  .add 56 55 3,
  .add 57 56 3,
  .add 58 57 3,
  .add 59 58 3,
  .add 60 59 3,
  .add 61 60 3,
  .add 62 61 3,
  .add 63 62 3,
  .add 64 63 3,
  .add 65 64 3,
  .add 66 65 3,
  .add 67 66 3,
  .add 68 67 3,
  .add 69 68 3,
  .add 70 69 3,
  .add 71 70 3,
  .add 280 71 3,
  .add 4 145 0,
  .add 5 144 1,
  .add 5 5 1,
  .add 291 140 140]

theorem solverHeader_loopFree : LoopFree solverHeader := by
  simp [solverHeader,seqs,LoopFree]

theorem solverHeader_size : size solverHeader ≤ 60 := by decide

theorem solverHeader_bases {L : DFSRAM.Layout} {G : DG} {c : Config}
    (hb : DFSRAM.Bases L G c) : RAMSolver.Bases (solverLayout L) (run solverHeader c) := by
  have hz := hb.1
  have ho := hb.2.1
  have hw := hb.2.2.2.2.1
  have hbase := hb.2.2.2.2.2 10 (by decide)
  constructor
  · simpa [solverHeader,seqs,run] using hz
  constructor
  · simpa [solverHeader,seqs,run] using ho
  constructor
  · simp [solverHeader,seqs,run,hz,hw,hbase,solverLayout,DFSRAM.Layout.limit,DFSRAM.Layout.block]
    omega
  constructor
  · simp [solverHeader,seqs,run,hz,hw,solverLayout]
  · intro j hj
    interval_cases j
    all_goals simp [solverHeader,seqs,run,hz,hw,hbase,solverLayout,
      RAMSolver.Layout.block,DFSRAM.Layout.limit,DFSRAM.Layout.block]
    all_goals omega

theorem solverHeader_metadata {L : DFSRAM.Layout} {G : DG} {c : Config}
    (hb : DFSRAM.Bases L G c) :
    (run solverHeader c).reg 280=(solverLayout L).limit ∧
    (run solverHeader c).reg 4=c.reg 145 ∧
    (run solverHeader c).reg 5=c.reg 144+2 ∧
    (run solverHeader c).reg 291=4*G.E := by
  have hz := hb.1
  have ho := hb.2.1
  have hw := hb.2.2.2.2.1
  have hbase := hb.2.2.2.2.2 10 (by decide)
  have hd := hb.2.2.1
  simp [solverHeader,seqs,run,hz,ho,hw,hbase,hd,solverLayout,
    RAMSolver.Layout.limit,DFSRAM.Layout.limit,DFSRAM.Layout.block]
  constructor <;> omega

theorem solverHeader_frame (c : Config) :
    (run solverHeader c).mem=c.mem ∧ (run solverHeader c).out=c.out ∧
    ∀ r, r≠2 → r≠3 → r≠4 → r≠5 → r≠280 → r≠291 →
      (r<50 ∨ 71<r) → (run solverHeader c).reg r=c.reg r := by
  refine ⟨run_mem_frame _ _ (by decide),run_out_frame _ _ (by decide),?_⟩
  intro r h2 h3 h4 h5 h280 h291 hr
  apply run_reg_frame
  simp [solverHeader,seqs,regsW]
  omega

theorem solverHeader_spec {L : DFSRAM.Layout} {G : DG} {c : Config} (S : Nat)
    (hb : DFSRAM.Bases L G c) :
    ∃ t, ExecB S solverHeader c t (run solverHeader c) ∧ t≤60 ∧
      RAMSolver.Bases (solverLayout L) (run solverHeader c) ∧
      (run solverHeader c).reg 280=(solverLayout L).limit := by
  exact ⟨_,execB_run _ solverHeader_loopFree c (AddrOK.of_memFree (by decide)),
    (cost_le_size solverHeader c).trans solverHeader_size,solverHeader_bases hb,
    (solverHeader_metadata hb).1⟩

end STACS2027.Embed.PlanRAM
