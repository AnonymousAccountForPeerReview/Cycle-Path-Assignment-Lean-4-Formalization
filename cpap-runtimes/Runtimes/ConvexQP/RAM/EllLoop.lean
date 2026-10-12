module

public import Runtimes.ConvexQP.RAM.EllIter
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: the main loop

`.loop eCnt iterB` with the invariant `MInv` (the globals, `H`, the free memory, and the state
`MSt i` of some iteration `i ≤ N`) and the measure `eCnt` (`loop_specB`, by `HTB.loopT` and
`iter_specB`). When the loop stops (`eCnt = 0`) after a successful run (`ellRun = some Xs`), the
output `Xs` is at `qBX` and `QMid I Xs` holds (`mid_of_inv`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

/-- The invariant of the main loop. -/
def MInv (I : Inst) (Ly : Lay) (c : Config) : Prop :=
  EG I Ly c ∧ HMem I c.mem Ly.bh ∧ ZeroFrom c.mem Ly.F ∧ ∃ i ≤ iters I.t I.k, MSt I Ly i c

/-- **The main loop**: at most `N` iterations. -/
theorem loop_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (hI : I.Valid)
    (hS : Ly.F + ellSc I.t I.k ≤ S) :
    HTB S (.loop eCnt iterB) (fun c => MInv I Ly c ∧ c.reg eCnt ≤ iters I.t I.k)
      (fun c => MInv I Ly c ∧ c.reg eCnt = 0) (iters I.t I.k * (iterCost I + 1) + 1) := by
  refine HTB.loopT (S := S) (a := eCnt) (body := iterB) (Inv := MInv I Ly) (fun c => c.reg eCnt)
    (fun v => HTB.of_forall fun c₀ ⟨⟨hE, hH, hz, i, hiN, hM⟩, hne, hv⟩ => ?_) _
  unfold MSt at hM
  rcases hst : ellIter I (consts I.t I.k) i with st | Xs
  · rw [hst] at hM
    obtain ⟨hc, hSt⟩ := hM
    have hi : i < iters I.t I.k := by omega
    refine ((iter_specB I Ly hL hI hi hst c₀.mem hSt hH hz hS).pre fun c hc' => ?_).post
      fun c ⟨hE', hH', hz', hM'⟩ => ⟨⟨hE', hH', hz', i + 1, hi, hM'⟩, ?_⟩
    · subst hc'; exact ⟨hE, rfl, hc⟩
    · unfold MSt at hM'
      rcases hst' : ellIter I (consts I.t I.k) (i + 1) with st' | Xs'
      · rw [hst'] at hM'; omega
      · rw [hst'] at hM'; omega
  · rw [hst] at hM
    exact absurd hM.1 hne

/-- After the loop: the output of `ellRun` at `qBX`. -/
theorem mid_of_inv (I : Inst) (Ly : Lay) (hL : Ly.Ok I) {Xs : Fin I.t → Fin I.k → ℤ}
    (hrun : ellRun I (consts I.t I.k) = some Xs) {c : Config} (hc : MInv I Ly c)
    (h0 : c.reg eCnt = 0) (hout : c.out = []) : QMid I Xs c := by
  obtain ⟨hE, hH, hz, i, hiN, hM⟩ := hc
  have hLh := hL.h; have hLq := hL.q; have hLx := hL.x; have hLl := hL.l; have hLg := hL.g
  have hLu := hL.u; have hLf := hL.f
  have hX : SArr c.mem Ly.pX 2 (I.t * I.k) (flat Xs) := by
    unfold MSt at hM
    rcases hst : ellIter I (consts I.t I.k) i with st | Xs'
    · rw [hst] at hM
      have hiN' : i = iters I.t I.k := by omega
      have : ellRun I (consts I.t I.k) = none := by
        unfold ellRun; rw [show (consts I.t I.k).N = i from hiN'.symm, hst]
      rw [this] at hrun; exact absurd hrun (by simp)
    · rw [hst] at hM
      have h1 : ellIter I (consts I.t I.k) (consts I.t I.k).N = .inr Xs' :=
        ellIter_inr_le hiN hst
      have h2 : ellRun I (consts I.t I.k) = some Xs' := by unfold ellRun; rw [h1]
      rw [h2] at hrun
      rw [← Option.some_inj.mp hrun]
      exact hM.2
  refine ⟨hE.q, by rw [hE.bh]; exact hH, by rw [hE.bh, hE.free]; omega, by rw [hE.x]; exact hX,
    by rw [hE.x, hE.free]; omega, by rw [hE.free]; exact hz, hout⟩

end STACS2027.Runtimes.QPRam
