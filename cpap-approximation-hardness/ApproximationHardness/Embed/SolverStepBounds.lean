module

public import ApproximationHardness.Embed.SolverStepRAM
import Lean.Elab.Tactic.Omega

/-! Bounded-address execution of the linked solver's constant-time steps. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- The actual addresses possibly read or written while consuming a group. -/
def ConsumeAddressOK (bound : Nat) (c : Config) : Prop :=
  (∀ j ∈ [1, 2, 3, 4, 5, 8, 9], c.reg (50 + j) + (c.reg 13 - 1) < bound) ∧
  c.reg 50 + (c.reg 19 - 1) < bound ∧
  c.reg 50 + (c.mem (c.reg 52 + (c.reg 13 - 1)) - 1) < bound

/-- Consumption has no hidden memory accesses. -/
theorem consumeGroupProgram_addrOK {bound : Nat} {c : Config}
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) (ha : ConsumeAddressOK bound c) :
    AddrOK bound consumeGroupProgram c := by
  obtain ⟨h, hc, ht⟩ := ha
  have h₁ := h 1 (by simp)
  have h₂ := h 2 (by simp)
  have h₃ := h 3 (by simp)
  have h₄ := h 4 (by simp)
  have h₅ := h 5 (by simp)
  have h₈ := h 8 (by simp)
  have h₉ := h 9 (by simp)
  by_cases hp : c.mem (c.reg 51 + (c.reg 13 - 1)) = 0 <;>
    by_cases hm : c.mem (c.reg 53 + (c.reg 13 - 1)) = 0 <;>
    by_cases hch : c.reg 18 = 0
  all_goals simp [consumeGroupProgram, groupRead, consumeRecord, loadCell, storeCell,
    appendInto, AddrOK, run, seqs, hz, ho, hp, hm, hch, *]

/-- The actual addresses possibly written when completing a merge. -/
def FinishAddressOK (bound : Nat) (c : Config) : Prop :=
  (∀ j ∈ [1, 2, 3, 4, 5], c.reg (50 + j) + c.reg 9 < bound) ∧
  (∀ j ∈ [6, 7], c.reg (50 + j) + c.reg 8 < bound) ∧
  c.reg 50 + (c.reg 19 - 1) < bound

/-- Finishing a merge has only the seven declared array writes and possible tail link. -/
theorem finishMergeProgram_addrOK {bound : Nat} {c : Config}
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) (ha : FinishAddressOK bound c) :
    AddrOK bound finishMergeProgram c := by
  obtain ⟨h, hv, hc⟩ := ha
  have h₁ := h 1 (by simp)
  have h₂ := h 2 (by simp)
  have h₃ := h 3 (by simp)
  have h₄ := h 4 (by simp)
  have h₅ := h 5 (by simp)
  have h₆ := hv 6 (by simp)
  have h₇ := hv 7 (by simp)
  by_cases hch : c.reg 18 = 0 <;> by_cases hb : c.reg 16 = 0
  all_goals simp [finishMergeProgram, loadCell, storeCell, appendInto,
    AddrOK, run, seqs, hz, ho, hch, hb, *]

/-- A consume step executes within a fixed instruction bound. -/
theorem consStepProgram_exec {bound : Nat} {c : Config}
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1)
    (hf : c.reg 13 = 0 → FinishAddressOK bound c)
    (hc : c.reg 13 ≠ 0 → ConsumeAddressOK bound c) :
    ∃ t, ExecB bound consStepProgram c t (run consStepProgram c) ∧ t ≤ 200 := by
  have ha : AddrOK bound consStepProgram c := by
    exact ⟨fun h => finishMergeProgram_addrOK hz ho (hf h),
      fun h => consumeGroupProgram_addrOK hz ho (hc h)⟩
  exact ⟨_, execB_run consStepProgram consStepProgram_loopFree c ha,
    Nat.le_trans (cost_le_size _ _) consStepProgram_size⟩

/-- Representation and pointer bounds imply every possible consume address is valid. -/
theorem ConsumeAddressOK.ofRep {L : Layout} {c : Config} {s : SMS} {dartBound : Nat}
    (hr : Rep L c s) (hb : StepBounds L s dartBound) (hy : s.ryp ≠ 0) :
    ConsumeAddressOK L.limit c := by
  have hg : s.ryp - 1 < L.width := by have := hb.lower; omega
  have hbase := hr.bases.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hj' : j < 22 := by simp at hj; omega
    rw [hbase j hj', hr.lowerHead]
    exact L.cell_lt hj' hg
  · rw [hbase 0 (by decide), hr.lowerClassTail]
    exact L.cell_lt (by decide) (by have := hb.lowerClass; have := hb.width; omega)
  · have hpt : c.mem (c.reg 52 + (c.reg 13 - 1)) = s.m.pt (s.ryp - 1) := by
      simpa [hbase 2 (by decide), hr.lowerHead, memField, Layout.cell] using
        hr.arrays 2 (by decide) (s.ryp - 1) hg
    rw [hbase 0 (by decide), hpt]
    exact L.cell_lt (by decide) (by have := hb.positiveTails _ hg; have := hb.width; omega)

/-- Representation and pointer bounds imply every possible finish address is valid. -/
theorem FinishAddressOK.ofRep {L : Layout} {c : Config} {s : SMS} {dartBound : Nat}
    (hr : Rep L c s) (hb : StepBounds L s dartBound) :
    FinishAddressOK L.limit c := by
  have hbase := hr.bases.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hj' : j < 22 := by simp at hj; omega
    rw [hbase j hj', hr.group]
    exact L.cell_lt hj' hb.group
  · intro j hj
    have hj' : j < 22 := by simp at hj; omega
    rw [hbase j hj', hr.node]
    exact L.cell_lt hj' hb.node
  · rw [hbase 0 (by decide), hr.lowerClassTail]
    exact L.cell_lt (by decide) (by have := hb.lowerClass; have := hb.width; omega)

/-- Every represented consume step has bounded execution in at most 200 instructions. -/
theorem consStepProgram_exec_ofRep {L : Layout} {c : Config} {s : SMS} {dartBound : Nat}
    (hr : Rep L c s) (hb : StepBounds L s dartBound) :
    ∃ t, ExecB L.limit consStepProgram c t (run consStepProgram c) ∧ t ≤ 200 := by
  exact consStepProgram_exec hr.bases.1 hr.bases.2.1
    (fun _ => FinishAddressOK.ofRep hr hb)
    (fun hy => ConsumeAddressOK.ofRep hr hb (by simpa [hr.lowerHead] using hy))

end STACS2027.Embed.RAMSolver
