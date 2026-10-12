module

public import ApproximationHardness.Embed.SolverStepRAM
public import ApproximationHardness.Embed.SolverBits

/-! # Finite address bounds for every linked solver transition -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

structure MemoryBounds (m : SMem) (width darts : Nat) : Prop where
  successor : ∀ e, m.nx e ≤ darts
  positiveHead : ∀ g, m.ph g ≤ darts
  negativeHead : ∀ g, m.mh g ≤ darts
  positiveTail : ∀ g, m.pt g ≤ width
  negativeTail : ∀ g, m.mt g ≤ width
  nextGroup : ∀ g, m.gn g ≤ width
  resultHead : ∀ v, m.rs v ≤ width

structure StateBounds (L : Layout) (s : SMS) (darts : Nat) : Prop where
  width : 0 < L.width
  dartWidth : darts ≤ L.width
  memory : MemoryBounds s.m L.width darts
  node : s.v < L.width
  group : s.G < L.width
  upper : s.rxp ≤ L.width
  lower : s.ryp ≤ L.width
  positiveHead : s.ah ≤ darts
  negativeHead : s.bh ≤ darts
  lowerClassHead : s.ch ≤ darts
  positiveTail : s.at' ≤ L.width
  negativeTail : s.bt ≤ L.width
  lowerClassTail : s.ct ≤ L.width

theorem StateBounds.stepBounds {L : Layout} {s : SMS} {darts : Nat}
    (H : StateBounds L s darts) : StepBounds L s darts :=
  ⟨H.width, H.group, H.node, H.upper, H.lower, H.positiveTail,
    H.negativeTail, H.lowerClassTail, fun g _ => H.memory.positiveHead g,
    fun g _ => H.memory.negativeHead g, fun g _ => H.memory.positiveTail g,
    fun g _ => H.memory.negativeTail g⟩

theorem appL_bounded {nx : Nat → Nat} {h t h' t' width darts : Nat}
    (Hnx : ∀ e, nx e ≤ darts) (Hh : h ≤ darts) (Hh' : h' ≤ darts)
    (Ht : t ≤ width) (Ht' : t' ≤ width) :
    (appL nx h t h' t').1 ≤ darts ∧ (appL nx h t h' t').2.1 ≤ width ∧
      ∀ e, (appL nx h t h' t').2.2 e ≤ darts := by
  unfold appL
  split
  · exact ⟨Hh', Ht', Hnx⟩
  · split
    · exact ⟨Hh, Ht, Hnx⟩
    · exact ⟨Hh, Ht', by intro e; dsimp only; unfold upd; split; exact Hh'; exact Hnx e⟩

theorem popStep_bounded (S : Sol) {L : Layout} {s : SMS} {darts : Nat}
    (H : StateBounds L s darts) : StateBounds L (S.popStep s) darts := by
  unfold Sol.popStep
  split
  · let g := s.rxp - 1
    have Huh : (if decide (s.lh < S.khM (s.m.ph g)) then s.m.ph g else s.m.mh g) ≤ darts := by
      split <;> first | exact H.memory.positiveHead g | exact H.memory.negativeHead g
    have Hwh : (if decide (s.lh < S.khM (s.m.ph g)) then s.m.mh g else s.m.ph g) ≤ darts := by
      split <;> first | exact H.memory.positiveHead g | exact H.memory.negativeHead g
    have Hut : (if decide (s.lh < S.khM (s.m.ph g)) then s.m.pt g else s.m.mt g) ≤ L.width := by
      split <;> first | exact H.memory.positiveTail g | exact H.memory.negativeTail g
    have Hwt : (if decide (s.lh < S.khM (s.m.ph g)) then s.m.mt g else s.m.pt g) ≤ L.width := by
      split <;> first | exact H.memory.positiveTail g | exact H.memory.negativeTail g
    have Ha := appL_bounded H.memory.successor H.positiveHead Huh H.positiveTail Hut
    have Hb := appL_bounded Ha.2.2 H.negativeHead Hwh H.negativeTail Hwt
    exact ⟨H.width, H.dartWidth,
      ⟨Hb.2.2, H.memory.positiveHead, H.memory.negativeHead, H.memory.positiveTail,
        H.memory.negativeTail, H.memory.nextGroup, H.memory.resultHead⟩,
      H.node, H.group, H.memory.nextGroup g, H.lower, Ha.1, Hb.1, H.lowerClassHead,
      Ha.2.1, Hb.2.1, H.lowerClassTail⟩
  · exact ⟨H.width, H.dartWidth, H.memory, H.node, H.group, H.upper, H.lower,
      H.positiveHead, H.negativeHead, H.lowerClassHead, H.positiveTail, H.negativeTail,
      H.lowerClassTail⟩

theorem consStep_bounded {L : Layout} {s : SMS} {darts : Nat}
    (H : StateBounds L s darts) : StateBounds L (Sol.consStep s) darts := by
  unfold Sol.consStep
  split
  · let g := s.ryp - 1
    have Ha := appL_bounded H.memory.successor H.lowerClassHead (H.memory.positiveHead g)
      H.lowerClassTail (H.memory.positiveTail g)
    have Hb := appL_bounded Ha.2.2 Ha.1 (H.memory.negativeHead g) Ha.2.1 (H.memory.negativeTail g)
    exact ⟨H.width, H.dartWidth,
      ⟨Hb.2.2, H.memory.positiveHead, H.memory.negativeHead, H.memory.positiveTail,
        H.memory.negativeTail, H.memory.nextGroup, H.memory.resultHead⟩,
      H.node, H.group, H.upper, H.memory.nextGroup g, H.positiveHead, H.negativeHead,
      Hb.1, H.positiveTail, H.negativeTail, Hb.2.1⟩
  · have Hy := appL_bounded H.memory.successor H.lowerClassHead H.negativeHead
      H.lowerClassTail H.negativeTail
    refine ⟨H.width, H.dartWidth, ?_, H.node, H.group, H.upper, H.lower,
      H.positiveHead, H.negativeHead, H.lowerClassHead, H.positiveTail, H.negativeTail,
      H.lowerClassTail⟩
    refine ⟨Hy.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g; dsimp only; unfold upd; split; exact H.positiveHead; exact H.memory.positiveHead g
    · intro g; dsimp only; unfold upd; split; exact Hy.1; exact H.memory.negativeHead g
    · intro g; dsimp only; unfold upd; split; exact H.positiveTail; exact H.memory.positiveTail g
    · intro g; dsimp only; unfold upd; split; exact Hy.2.1; exact H.memory.negativeTail g
    · intro g; dsimp only; unfold upd; split; exact H.upper; exact H.memory.nextGroup g
    · intro v; dsimp only [SMem.store]; unfold upd; split
      · exact Nat.add_one_le_iff.mpr H.group
      · exact H.memory.resultHead v

end STACS2027.Embed.RAMSolver
