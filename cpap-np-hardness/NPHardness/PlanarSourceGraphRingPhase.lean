module

public import NPHardness.PlanarSourceGraphRingLocal

/-! Global counted-loop composition for all graph implication blocks. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Grid
open Complexity.Planar.Emit

structure GraphRingBlocks {n : Nat} (d : Layout n) (length : Nat) (w : SAT.Word) (env : Env n)
    (edge : Nat → CNF) : Prop where
  start : ∀ k odd, 2*k+(if odd then 2 else 1) ≤ d.M.eval env →
    (d.lift.startGraphProgram length (.var 0) odd true).emit w (extend k env) =
      expandCopyRecords edge ((d.lift.startProgram (.var 0) odd false).emit w (extend k env))
  cell : ∀ k idx odd, 2*k+(if odd then 2 else 1) ≤ d.M.eval env → idx < d.W.eval env →
    (d.lift.lift.cellGraphProgram length (.var 1) (.var 0) odd true).emit w (extend idx (extend k env)) =
      expandCopyRecords edge ((d.lift.lift.cellProgram (.var 1) (.var 0) odd false).emit w
        (extend idx (extend k env)))
  finish : ∀ k odd, 2*k+(if odd then 2 else 1) ≤ d.M.eval env →
    (d.lift.endGraphProgram length (.var 0) odd true).emit w (extend k env) =
      expandCopyRecords edge ((d.lift.endProgram (.var 0) odd false).emit w (extend k env))
  rainbow : ∀ k v odd, 2*k+(if odd then 3 else 2) ≤ d.M.eval env → v < d.W.eval env →
    (d.lift.lift.rainbowGraphProgram length (.var 1) (.var 0) odd true).emit w (extend v (extend k env)) =
      expandCopyRecords edge ((d.lift.lift.rainbowProgram (.var 1) (.var 0) odd false).emit w
        (extend v (extend k env)))

theorem GraphRingBlocks.column {n : Nat} {d : Layout n} {length : Nat} {w : SAT.Word} {env : Env n}
    {edge : Nat → CNF} (h : GraphRingBlocks d length w env edge) (k : Nat) (odd : Bool)
    (hk : 2*k+(if odd then 2 else 1) ≤ d.M.eval env) :
    (d.lift.columnGraphProgram length (.var 0) odd true).emit w (extend k env) =
      expandCopyRecords edge ((d.lift.columnProgram (.var 0) odd false).emit w (extend k env)) := by
  simp only [Layout.columnGraphProgram,Layout.columnProgram, ClauseProgram.emit_seq, ClauseProgram.emit_forDown,
    expandCopyRecords_append, expandCopyRecords_flatMap, h.start k odd hk, h.finish k odd hk]
  congr 2
  apply flatMap_congr_range
  intro idx hidx
  have hi : idx < d.W.eval env := by simpa only [Layout.lift, NumExpr.eval_lift] using hidx
  exact h.cell k idx odd hk hi

theorem GraphRingBlocks.row {n : Nat} {d : Layout n} {length : Nat} {w : SAT.Word} {env : Env n}
    {edge : Nat → CNF} (h : GraphRingBlocks d length w env edge) (k : Nat) (odd : Bool)
    (hk : 2*k+(if odd then 3 else 2) ≤ d.M.eval env) :
    (ClauseProgram.forDown d.W.lift
      (d.lift.lift.rainbowGraphProgram length (.var 1) (.var 0) odd true)).emit w (extend k env) =
      expandCopyRecords edge ((ClauseProgram.forDown d.W.lift
        (d.lift.lift.rainbowProgram (.var 1) (.var 0) odd false)).emit w (extend k env)) := by
  simp only [ClauseProgram.emit_forDown, expandCopyRecords_flatMap]
  apply flatMap_congr_range
  intro v hv
  have hv' : v < d.W.eval env := by simpa only [NumExpr.eval_lift] using hv
  exact h.rainbow k v odd hk hv'

theorem graphPhase_rings_of_blocks {n : Nat} (d : Layout n) (length : Nat) (w : SAT.Word) (env : Env n)
    (edge : Nat → CNF) (h : GraphRingBlocks d length w env edge) :
    (d.graphPhase length true).emit w env = expandCopyRecords edge ((d.gridPhase false).emit w env) := by
  simp only [Layout.graphPhase,Layout.gridPhase, ClauseProgram.emit_seq, expandCopyRecords_append,
    forDown_guard_emit, expandCopyRecords_flatMap]
  have happend {a b c d : CNF} (ha : a=c) (hb : b=d) : a++b=c++d := by rw [ha,hb]
  refine happend (happend (happend ?_ ?_) ?_) ?_
  all_goals
    apply flatMap_congr_range
    intro k hk
    simp only [twoE, NumExpr.eval, NumExpr.eval_lift, extend_zero]
    split
    · next hl =>
        first
        | exact h.column k false hl
        | exact h.column k true hl
        | exact h.row k false hl
        | exact h.row k true hl
    · rfl

@[simp] theorem Layout.sourceRingRecords_lift {n : Nat} (d : Layout n) (length : Nat)
    (w : SAT.Word) (env : Env n) (j : Nat) :
    d.lift.sourceRingRecords length w (extend j env)=d.sourceRingRecords length w env := by
  funext i
  simp only [Layout.sourceRingRecords, Layout.source_lift]
  simp [Layout.occurrenceCount, Layout.formulaLength, Layout.columnSize,
    Layout.lift, NumExpr.eval, addN, mulN, subN]

theorem Layout.graphRingBlocks {n : Nat} (d : Layout n) (length : Nat) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1) :
    GraphRingBlocks d length w env (d.sourceRingRecords length w env) := by
  constructor
  · intro k odd hk
    simpa only [Layout.sourceRingRecords_lift] using d.lift.startGraphProgram_rings length (.var 0) odd w (extend k env)
      (by simpa only [Layout.lift,NumExpr.eval_lift] using hq) (by simpa only [Layout.lift,NumExpr.eval_lift,NumExpr.eval,extend_zero] using hk)
  · intro k idx odd hk hi
    simpa only [Layout.sourceRingRecords_lift] using d.lift.lift.cellGraphProgram_rings length (.var 1) (.var 0) odd w (extend idx (extend k env))
      (by simpa only [Layout.lift,NumExpr.eval_lift] using hq)
      (by change 2*k+(if odd then 2 else 1) ≤ d.M.lift.lift.eval (extend idx (extend k env)); simpa only [NumExpr.eval_lift] using hk)
      (by simpa only [Layout.lift,NumExpr.eval_lift,NumExpr.eval,extend_zero] using hi)
  · intro k odd hk
    simpa only [Layout.sourceRingRecords_lift] using d.lift.endGraphProgram_rings length (.var 0) odd w (extend k env)
      (by simpa only [Layout.lift,NumExpr.eval_lift] using hq) (by simpa only [Layout.lift,NumExpr.eval_lift,NumExpr.eval,extend_zero] using hk)
  · intro k v odd hk hi
    simpa only [Layout.sourceRingRecords_lift] using d.lift.lift.rainbowGraphProgram_rings length (.var 1) (.var 0) odd w (extend v (extend k env))
      (by simpa only [Layout.lift,NumExpr.eval_lift] using hq)
      (by change 2*k+(if odd then 3 else 2) ≤ d.M.lift.lift.eval (extend v (extend k env)); simpa only [NumExpr.eval_lift] using hk)
      (by simpa only [Layout.lift,NumExpr.eval_lift,NumExpr.eval,extend_zero] using hi)

theorem Layout.graphPhase_rings {n : Nat} (d : Layout n) (length : Nat)
    (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1) :
    (d.graphPhase length true).emit w env=
      expandCopyRecords (d.sourceRingRecords length w env) ((d.gridPhase false).emit w env) :=
  graphPhase_rings_of_blocks d length w env _ (d.graphRingBlocks length w env hq)

end STACS2027.PlanarSource.Packed
