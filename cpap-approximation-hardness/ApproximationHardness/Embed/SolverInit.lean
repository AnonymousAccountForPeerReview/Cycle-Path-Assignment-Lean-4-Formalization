module

public import ApproximationHardness.Embed.PlanHeader
public import ApproximationHardness.Embed.SolverFrameRAM
public import ApproximationHardness.Embed.SolverBounds
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! # Actual initialization of the linked embedding solver -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

def initialMem : SMem := ⟨fun _=>0,fun _=>0,fun _=>0,fun _=>0,fun _=>0,fun _=>0,
  fun _=>0,fun _=>0,fun _=>0,fun _=>0,fun _=>0,fun _=>0⟩
def initialState : SMS := ⟨initialMem,0,0,0,0,0,0,0,0,0,0,0,0,0,0,[]⟩

def solverInit : Stmt := seqs [
  .const 6 0,
  .const 7 0,
  .const 8 0,
  .const 9 0,
  .const 10 0,
  .const 11 0,
  .const 12 0,
  .const 13 0,
  .const 14 0,
  .const 15 0,
  .const 16 0,
  .const 17 0,
  .const 18 0,
  .const 19 0]

theorem solverInit_loopFree : LoopFree solverInit := by simp [solverInit,seqs,LoopFree]
theorem solverInit_size : size solverInit≤30 := by decide

theorem solverInit_frame (c : Config) (r : Nat) (hr : r<6 ∨ 19<r) :
    (run solverInit c).reg r=c.reg r := by
  apply run_reg_frame
  simp [solverInit,seqs,regsW]
  omega

theorem solverInit_bases {L : Layout} {c : Config} (hb : Bases L c) :
    Bases L (run solverInit c) := by
  rcases hb with ⟨hz,ho,hb,hw,hblocks⟩
  refine ⟨(solverInit_frame c 0 (by decide)).trans hz,
    (solverInit_frame c 1 (by decide)).trans ho,
    (solverInit_frame c 2 (by decide)).trans hb,
    (solverInit_frame c 3 (by decide)).trans hw,?_⟩
  intro j hj
  rw [solverInit_frame c (50+j) (by omega)]
  exact hblocks j hj

theorem solverInit_rep {L : Layout} {c : Config} (hb : Bases L c)
    (hz : ∀ j,j<12 → ∀ i,i<L.width → c.mem (L.cell j i)=0) :
    Rep L (run solverInit c) initialState := by
  refine ⟨solverInit_bases hb,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj i hi
    rw [run_mem_frame solverInit c (by decide)]
    rw [hz j hj i hi]
    interval_cases j <;> rfl
  all_goals simp [solverInit,seqs,run,initialState]

theorem solverInit_tables {L : Layout} {S : Sol} {post : List Nat}
    {vertices darts : Nat} {c : Config} (ht : Tables L c S post vertices darts) :
    Tables L (run solverInit c) S post vertices darts := by
  apply ht.frame (solverInit_frame c 4 (by decide)) (solverInit_frame c 5 (by decide))
  rw [run_mem_frame solverInit c (by decide)]
  exact TableMemEq.refl _ _

theorem initialState_bounds {L : Layout} {darts : Nat}
    (hw : 0<L.width) (hd : darts≤L.width) : StateBounds L initialState darts := by
  refine ⟨hw,hd,⟨?_,?_,?_,?_,?_,?_,?_⟩,hw,hw,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | (intro _;exact Nat.zero_le _) | exact Nat.zero_le _

theorem solverInit_spec {L : Layout} {c : Config} (S : Nat) (hb : Bases L c)
    (hz : ∀ j,j<12 → ∀ i,i<L.width → c.mem (L.cell j i)=0) :
    ∃ t,ExecB S solverInit c t (run solverInit c) ∧ t≤30 ∧
      Rep L (run solverInit c) initialState ∧ (run solverInit c).mem=c.mem ∧
      (run solverInit c).out=c.out := by
  exact ⟨_,execB_run _ solverInit_loopFree c (AddrOK.of_memFree (by decide)),
    (cost_le_size solverInit c).trans solverInit_size,solverInit_rep hb hz,
    run_mem_frame _ _ (by decide),run_out_frame _ _ (by decide)⟩

end STACS2027.Embed.RAMSolver
