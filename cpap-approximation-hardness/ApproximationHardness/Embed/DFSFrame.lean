module

public import ApproximationHardness.Embed.DFSStepProof
import Lean.Elab.Tactic.Omega

/-! # The search preserves its graph tables and input prefix -/

@[expose] public section

namespace STACS2027.Embed.DFSRAM

open RAM

attribute [local simp] dartCount scan current inner height postLength remaining
  baseRegister widthRegister address pointer degree nextDart opposite nextVertex
  parent value needHeight test otherTest repValue

def CacheFrame (L : Layout) (G : DG) (p : Stmt) : Prop :=
  ∀ c, Bases L G c → Bases L G (run p c) ∧
    ∀ a, a < L.block 6 → (run p c).mem a = c.mem a

theorem CacheFrame.noStore {L : Layout} {G : DG} {p : Stmt}
    (hs : hasStore p = false)
    (hp : ∀ r, r ∈ regsW p → (141 ≤ r ∧ r ≤ 145) ∨ (180 ≤ r ∧ r ≤ 191)) :
    CacheFrame L G p := by
  intro c hc
  exact ⟨hc.run_aux hp, fun _ _ => congrFun (run_mem_frame p c hs) _⟩

theorem CacheFrame.store_cell {L : Layout} {G : DG} (j i src : Nat)
    (hj : 6 ≤ j) (hj' : j < 11) : CacheFrame L G (storeCell j i src) := by
  intro c hc
  refine ⟨hc.run_aux ?_, ?_⟩
  · intro r hn
    simp [storeCell, seqs, regsW] at hn <;> omega
  · intro a ha
    have hb := hc.2.2.2.2.2 j hj'
    have hle := Nat.mul_le_mul_right L.width hj
    have hne : a ≠ L.block j + c.reg i := by
      dsimp [Layout.block] at ha ⊢
      omega
    simp [storeCell, seqs, run, hb, hne]

theorem CacheFrame.seq {L : Layout} {G : DG} {p q : Stmt}
    (hp : CacheFrame L G p) (hq : CacheFrame L G q) : CacheFrame L G (.seq p q) := by
  intro c hc
  obtain ⟨hpB, hpM⟩ := hp c hc
  obtain ⟨hqB, hqM⟩ := hq (run p c) hpB
  exact ⟨hqB, fun a ha => (hqM a ha).trans (hpM a ha)⟩

theorem CacheFrame.ifz {L : Layout} {G : DG} {r : Nat} {p q : Stmt}
    (hp : CacheFrame L G p) (hq : CacheFrame L G q) : CacheFrame L G (.ifz r p q) := by
  intro c hc
  simp only [run_ifz]
  split
  · exact hp c hc
  · exact hq c hc

theorem stepProgram_cacheFrame (L : Layout) (G : DG) : CacheFrame L G stepProgram := by
  simp only [stepProgram, outsideStep, outsideRead, insideStep, insideRead, startRoot,
    exploreStep, explorePrefix, exploreRead, exploreNew, finishStep, finishRoot,
    finishChild, advanceScan, readNext, pushPost, seqs]
  repeat' first
    | apply CacheFrame.store_cell <;> decide
    | (refine CacheFrame.noStore ?_ ?_
       · decide
       · intro r hn
         simp [regsW, loadCell, seqs] at hn <;> omega)
    | apply CacheFrame.seq
    | apply CacheFrame.ifz

theorem Tables.run_cacheFrame {L : Layout} {G : DG} {c : Config} {p : Stmt}
    (hp : CacheFrame L G p) (hb : Bases L G c) (ht : Tables L G c)
    (hw : 2 * G.E ≤ L.width) : Tables L G (run p c) := by
  have hf := (hp c hb).2
  have hlt (j i : Nat) (hj : j < 6) (hi : i < 2 * G.E) : L.cell j i < L.block 6 := by
    have hm := Nat.mul_le_mul_right L.width (show j + 1 ≤ 6 by omega)
    rw [Nat.add_mul] at hm
    dsimp [Layout.cell, Layout.block]
    omega
  constructor
  · intro d hd
    rw [hf _ (hlt 0 d (by decide) hd)]
    exact ht.representatives d hd
  · intro d hd
    rw [hf _ (hlt 1 d (by decide) hd)]
    exact ht.partners d hd
  · intro v hv
    rw [hf _ (hlt 2 v (by decide) hv)]
    exact ht.degrees v hv
  · intro k hk v hv
    rw [hf _ (hlt (3+k) v (by omega) hv)]
    exact ht.adjacent k hk v hv

theorem Tables.run_step {L : Layout} {G : DG} {c : Config}
    (hb : Bases L G c) (ht : Tables L G c) (hw : 2 * G.E ≤ L.width) :
    Tables L G (run stepProgram c) :=
  ht.run_cacheFrame (stepProgram_cacheFrame L G) hb hw

end STACS2027.Embed.DFSRAM
