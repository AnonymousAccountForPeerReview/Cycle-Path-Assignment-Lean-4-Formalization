module

public import ApproximationHardness.Embed.SolverCloseRAM
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Bounded memory accesses of target-end closing. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- The exact group and dart address bounds needed by the closing instruction. -/
def CloseAddressOK (bound : Nat) (c : Config) : Prop :=
  c.reg 24 ≠ 0 →
    (∀ j ∈ [1, 2, 3, 4, 5], c.reg (50 + j) + (c.reg 24 - 1) < bound) ∧
    (∀ j ∈ [0, 12], c.reg (50 + j) + c.reg 23 < bound)

/-- Closing accesses only a bounded open-end group, its successor cell, and its key. -/
theorem closeResultProgram_addrOK {bound : Nat} {c : Config}
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) (ha : CloseAddressOK bound c) :
    AddrOK bound closeResultProgram c := by
  by_cases hh : c.reg 24 = 0
  · simp [closeResultProgram, AddrOK, run, hh]
  · obtain ⟨hg, he⟩ := ha hh
    have h₁ := hg 1 (by simp)
    have h₂ := hg 2 (by simp)
    have h₃ := hg 3 (by simp)
    have h₄ := hg 4 (by simp)
    have h₅ := hg 5 (by simp)
    have h₀ := he 0 (by simp)
    have h₁₂ := he 12 (by simp)
    by_cases hp : c.mem (c.reg 51 + (c.reg 24 - 1)) = c.reg 23 + 1 <;>
      by_cases hpt : c.mem (c.reg 51 + (c.reg 24 - 1)) = c.mem (c.reg 52 + (c.reg 24 - 1)) <;>
      by_cases hmt : c.mem (c.reg 53 + (c.reg 24 - 1)) = c.mem (c.reg 54 + (c.reg 24 - 1))
    all_goals
      try simp only [hp] at hpt
      try simp only [hpt] at hp
      simp [closeResultProgram, closePositiveProgram, closeNegativeProgram, loadCell, storeCell,
        run, AddrOK, seqs, hz, ho, hh, hp, hpt, hmt, *]

/-- Finite representation bounds imply the actual closing-address bounds. -/
theorem CloseAddressOK.ofRep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound e h : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (he : e < dartBound) (hh : h ≤ L.width)
    (hec : c.reg 23 = e) (hhc : c.reg 24 = h) : CloseAddressOK L.limit c := by
  intro hne
  have hn : h ≠ 0 := by simpa only [hhc] using hne
  have hg : h - 1 < L.width := by omega
  have hew : e < L.width := he.trans_le ht.darts
  constructor
  · intro j hj
    have hj' : j < 22 := by simp at hj; omega
    rw [hr.bases.2.2.2.2 j hj', hhc]
    exact L.cell_lt hj' hg
  · intro j hj
    have hj' : j < 22 := by simp at hj; omega
    rw [hr.bases.2.2.2.2 j hj', hec]
    exact L.cell_lt hj' hew

/-- Closing has a fixed instruction bound. -/
theorem closeResultProgram_size : size closeResultProgram ≤ 100 := by decide

/-- Actual bounded execution of closing under the represented finite layout. -/
theorem closeResultProgram_exec {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound e h : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (he : e < dartBound) (hh : h ≤ L.width)
    (hec : c.reg 23 = e) (hhc : c.reg 24 = h) :
    ∃ t, ExecB L.limit closeResultProgram c t (run closeResultProgram c) ∧ t ≤ 100 := by
  have ha := closeResultProgram_addrOK hr.bases.1 hr.bases.2.1
    (CloseAddressOK.ofRep hr ht he hh hec hhc)
  have hlp : LoopFree closeResultProgram := by
    simp [closeResultProgram, closePositiveProgram, closeNegativeProgram, loadCell, storeCell, LoopFree, seqs]
  exact ⟨_, execB_run _ hlp c ha, Nat.le_trans (cost_le_size _ _) closeResultProgram_size⟩

end STACS2027.Embed.RAMSolver
