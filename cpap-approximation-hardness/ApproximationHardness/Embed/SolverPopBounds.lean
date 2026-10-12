module

public import ApproximationHardness.Embed.SolverPopRAM
public import ApproximationHardness.Embed.SolverStepBounds
import Lean.Elab.Tactic.Omega

/-! The exact bounded-address footprint of a pop step. -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Every possible indexed address of a nonempty upper-stack pop. -/
def PopAddressOK (bound : Nat) (c : Config) : Prop :=
  (∀ j ∈ [1, 2, 3, 4, 5, 8, 9], c.reg (50 + j) + (c.reg 12 - 1) < bound) ∧
  (c.mem (c.reg 51 + (c.reg 12 - 1)) ≠ 0 →
    c.reg 62 + (c.mem (c.reg 51 + (c.reg 12 - 1)) - 1) < bound) ∧
  (c.mem (c.reg 53 + (c.reg 12 - 1)) ≠ 0 →
    c.reg 62 + (c.mem (c.reg 53 + (c.reg 12 - 1)) - 1) < bound) ∧
  c.reg 50 + (c.reg 15 - 1) < bound ∧
  c.reg 50 + (c.reg 17 - 1) < bound

/-- The concrete pop program performs only its stated bounded accesses. -/
theorem popStepProgram_addrOK {bound : Nat} {c : Config}
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1)
    (ha : c.reg 12 ≠ 0 → PopAddressOK bound c) : AddrOK bound popStepProgram c := by
  by_cases hx : c.reg 12 = 0
  · simp [popStepProgram, AddrOK, hx]
  · obtain ⟨h, hp, hm, hat, hbt⟩ := ha hx
    have h₁ := h 1 (by simp)
    have h₂ := h 2 (by simp)
    have h₃ := h 3 (by simp)
    have h₄ := h 4 (by simp)
    have h₅ := h 5 (by simp)
    have h₈ := h 8 (by simp)
    have h₉ := h 9 (by simp)
    by_cases hph : c.mem (c.reg 51 + (c.reg 12 - 1)) = 0 <;>
      by_cases hmh : c.mem (c.reg 53 + (c.reg 12 - 1)) = 0 <;>
      by_cases hah : c.reg 14 = 0 <;> by_cases hbh : c.reg 16 = 0
    all_goals simp [popStepProgram, groupRead, headKey, popClasses, consumeRecord,
      appendInto, loadCell, storeCell, AddrOK, run, seqs, hz, ho, hx, hph, hmh, hah, hbh, *]

/-- Finite pointer bounds and key tables imply valid pop addresses. -/
theorem PopAddressOK.ofRep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound) (hx : s.rxp ≠ 0) :
    PopAddressOK L.limit c := by
  have hg : s.rxp - 1 < L.width := by have := hb.upper; omega
  have hbase := hr.bases.2.2.2.2
  have hph : c.mem (c.reg 51 + (c.reg 12 - 1)) = s.m.ph (s.rxp - 1) := by
    simpa [hbase 1 (by decide), hr.upperHead, memField, Layout.cell] using hr.arrays 1 (by decide) _ hg
  have hmh : c.mem (c.reg 53 + (c.reg 12 - 1)) = s.m.mh (s.rxp - 1) := by
    simpa [hbase 3 (by decide), hr.upperHead, memField, Layout.cell] using hr.arrays 3 (by decide) _ hg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : j < 22 := by simp at hj; omega
    rw [hbase j hj', hr.upperHead]
    exact L.cell_lt hj' hg
  · intro hp
    rw [hbase 12 (by decide), hph]
    have h : s.m.ph (s.rxp - 1) ≤ L.width := (hb.positiveHeads _ hg).trans ht.darts
    have hn : s.m.ph (s.rxp - 1) ≠ 0 := by simpa [hph] using hp
    exact L.cell_lt (by decide) (by omega)
  · intro hm
    rw [hbase 12 (by decide), hmh]
    have h : s.m.mh (s.rxp - 1) ≤ L.width := (hb.negativeHeads _ hg).trans ht.darts
    have hn : s.m.mh (s.rxp - 1) ≠ 0 := by simpa [hmh] using hm
    exact L.cell_lt (by decide) (by omega)
  · rw [hbase 0 (by decide), hr.positiveTail]
    exact L.cell_lt (by decide) (by have := hb.positive; have := hb.width; omega)
  · rw [hbase 0 (by decide), hr.negativeTail]
    exact L.cell_lt (by decide) (by have := hb.negative; have := hb.width; omega)

/-- A represented pop step executes in at most 200 instructions. -/
theorem popStepProgram_exec_ofRep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound : Nat} (hr : Rep L c s) (hb : StepBounds L s dartBound)
    (ht : Tables L c S post vertexBound dartBound) :
    ∃ t, ExecB L.limit popStepProgram c t (run popStepProgram c) ∧ t ≤ 200 := by
  have ha := popStepProgram_addrOK hr.bases.1 hr.bases.2.1
    (fun hx => PopAddressOK.ofRep hr hb ht (by simpa [hr.upperHead] using hx))
  exact ⟨_, execB_run popStepProgram popStepProgram_loopFree c ha,
    Nat.le_trans (cost_le_size _ _) popStepProgram_size⟩

end STACS2027.Embed.RAMSolver
