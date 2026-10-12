module

public import ApproximationHardness.Embed.ForkStart
import Lean.Elab.Tactic.Omega

/-!
# Completing a fork in the array solver

The representation proof includes the empty operand case and the exact number
of array-machine transitions. The bound counts each consumed group once.
-/

@[expose] public section

namespace STACS2027.Embed.Sol

variable (S : Sol)

def forkTicks (rx ry : Res) : Nat :=
  if ry.seg = [] then 0 else (S.popped ry.low rx).length + 1 + ry.seg.length + 1

def forkFinish (s : SMS) (m : SMem) (v hx hy code : Nat) (rx ry : Res) : SMS :=
  let start := S.forkStart s m v hx rx.low hy ry.low code
  if ry.seg = [] then start else S.mergeState start rx ry

theorem forkFinish_refines {s : SMS} {m : SMem} {v hx hy code : Nat} {rx ry : Res}
    (Hmode : s.mode = 0) (Hrx : StackRep m hx rx.seg) (Hry : StackRep m hy ry.seg)
    (Hnd : (els rx.seg ++ els ry.seg).Nodup)
    (fresh : ∀ g ∈ rx.seg, g.id ≠ S.gid v)
    (Hstop : ∀ g ∈ S.rest ry.low rx, S.gtop g ≤ ry.low) :
    Stored (S.forkFinish s m v hx hy code rx ry).m v (S.mergeRes v rx ry) ∧
      (S.forkFinish s m v hx hy code rx ry).mode = 0 ∧
      (S.forkFinish s m v hx hy code rx ry).k = s.k + 1 ∧
      ∀ post, S.forkFinish s m v hx hy code rx ry =
        (S.mstep post)^[S.forkTicks rx ry] (S.forkStart s m v hx rx.low hy ry.low code) := by
  by_cases hnil : ry.seg = []
  · have hyzero : hy = 0 := Hry.head_zero_iff.mpr hnil
    have Hstored := stored_store Hrx v
    refine ⟨?_, ?_, ?_, ?_⟩
    · constructor
      · simpa [forkFinish, hnil, forkStart, hyzero, mergeRes, SMem.store] using
          Hstored.stack.inf_frame v 0
      · simp [forkFinish, hnil, forkStart, hyzero, mergeRes, SMem.store]
    · simp [forkFinish, hnil, forkStart, hyzero, Hmode]
    · simp [forkFinish, hnil, forkStart, hyzero]
    · intro post; simp [forkFinish, forkTicks, hnil]
  · have hynonzero : hy ≠ 0 := fun hz => hnil (Hry.head_zero_iff.mp hz)
    let start := S.forkStart s m v hx rx.low hy ry.low code
    have Hrx' : StackRep start.m start.rxp rx.seg := by
      simpa [start, forkStart, hynonzero] using Hrx.inf_frame v code
    have Hry' : StackRep start.m start.ryp ry.seg := by
      simpa [start, forkStart, hynonzero] using Hry.inf_frame v code
    obtain ⟨Hs, Hm, _, Hi⟩ := S.mergeState_refines
      (s := start) (v := v) (rx := rx) (ry := ry)
      (by simp [start, forkStart, hynonzero])
      (by simp [start, forkStart, hynonzero])
      (by simp [start, forkStart, hynonzero])
      (by simp [start, forkStart, hynonzero])
      (by simp [start, forkStart, hynonzero])
      (by simp [start, forkStart, hynonzero])
      (by simp [start, forkStart, hynonzero]) Hrx' Hry' hnil Hnd fresh
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [forkFinish, hnil, start] using Hs
    · simpa [forkFinish, hnil, start] using Hm
    · simp only [forkFinish, hnil, ↓reduceIte]
      rw [S.mergeState_index]
      simp [forkStart, hynonzero]
    · intro post
      simpa [forkFinish, forkTicks, hnil, start] using
        Hi post (by simp [start, forkStart, hynonzero]) Hstop

theorem forkTicks_le (rx ry : Res) :
    S.forkTicks rx ry ≤ (S.mergeCons rx ry).length + 2 := by
  by_cases hnil : ry.seg = []
  · simp [forkTicks, mergeCons, hnil]
  · simp [forkTicks, mergeCons, hnil]; omega

end STACS2027.Embed.Sol
