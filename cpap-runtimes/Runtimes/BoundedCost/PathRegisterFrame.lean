module

public import Runtimes.BoundedCost.ActualPathRAM
import Mathlib.Tactic

/-! Generic caller-register frames for the complete physical path program. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem flowReset_wregs (registers : List ℕ) :
    wregs (Flow.resetCallRegisters registers) = registers.map (Flow.rl 0) := by
  induction registers <;> simp_all [Flow.resetCallRegisters, wregs]

theorem flowRelocated_wregs (program : Stmt) {r : ℕ}
    (hr : r ∈ wregs (Flow.tr 0 true program)) : r = Flow.xT ∨ r = Flow.xP ∨ r % 4 = 0 := by
  induction program with
  | skip => simp [Flow.tr, wregs] at hr
  | const d v => simp only [Flow.tr, wregs, List.mem_singleton] at hr; subst r; exact Or.inr (Or.inr (Flow.rl_mod (by decide) d))
  | add d a b => simp only [Flow.tr, wregs, List.mem_singleton] at hr; subst r; exact Or.inr (Or.inr (Flow.rl_mod (by decide) d))
  | sub d a b => simp only [Flow.tr, wregs, List.mem_singleton] at hr; subst r; exact Or.inr (Or.inr (Flow.rl_mod (by decide) d))
  | load d a =>
    simp only [Flow.tr, Flow.addrOf, wregs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hr
    rcases hr with h | h
    · exact Or.inl h
    · subst r; exact Or.inr (Or.inr (Flow.rl_mod (by decide) d))
  | store a b =>
    simp only [Flow.tr, Flow.addrOf, wregs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hr
    exact Or.inl hr
  | write a =>
    simp [Flow.tr, wregs] at hr
    exact Or.inr (Or.inl hr)
  | seq s u ihs ihu =>
    simp only [Flow.tr, wregs, List.mem_append] at hr
    exact hr.elim ihs ihu
  | ifz a s u ihs ihu =>
    simp only [Flow.tr, wregs, List.mem_append] at hr
    exact hr.elim ihs ihu
  | loop a body ih => exact ih hr

theorem not_mem_reusableCall_wregs {program : Stmt} {r : ℕ}
    (hhigh : 152 ≤ r) (hclass : r % 4 ≠ 0) : r ∉ wregs (Flow.reusableCall program) := by
  intro hr
  simp only [Flow.reusableCall, wregs, List.mem_append] at hr
  rcases hr with hr | hr | hr | hr | hr | hr
  · simp +decide [Flow.initializeCall, wregs, Flow.callZero, Flow.callOne, Flow.xFour,
      Flow.xJ, Flow.callCount, Flow.callBegin, Flow.xP] at hr
    omega
  · simp +decide [forUp, upLoop, Flow.clearCallBody, inc, addc, wregs,
      Flow.callIndex, Flow.callAddress, rT] at hr
    omega
  · simp +decide [forUp, upLoop, Flow.copyCallBody, inc, addc, wregs,
      Flow.callIndex, Flow.callAddress, Flow.callValue, rT] at hr
    omega
  · rw [flowReset_wregs] at hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    exact hclass (Flow.rl_mod (by decide) i)
  · rcases flowRelocated_wregs program hr with h | h | h
    · simp only [Flow.xT] at h; omega
    · simp only [Flow.xP] at h; omega
    · exact hclass h
  · simp +decide [Flow.countCallOutput, Flow.countCallBody, wregs,
      Flow.callRemaining, Flow.callCount] at hr
    omega

theorem not_mem_searchNode_wregs {F : Stmt} {r : ℕ}
    (hr : 38 ≤ r) (hb : r ∉ wregs contractionBuild) (hd : r ∉ wregs CandidateDecode.program)
    (hs : r ∉ wregs searchScan) (hu : r ∉ wregs annotatedNodeUpdate) :
    callerRegister r ∉ wregs (searchNode F) := by
  have hb' := not_mem_renameRegisters_wregs callerRegister_injective hb
  have hd' := not_mem_renameRegisters_wregs callerRegister_injective hd
  have hs' := not_mem_renameRegisters_wregs callerRegister_injective hs
  have hu' := not_mem_renameRegisters_wregs callerRegister_injective hu
  have hcall := not_mem_reusableCall_wregs (program := Flow.hornSeparator F)
    (r := callerRegister r) (by unfold callerRegister; omega)
    (by simp [callerRegister, Nat.add_mod])
  have hmeta : callerRegister r ∉ wregs leastCutMetadata := by
    simp +decide [leastCutMetadata, wregs, callerRegister, Flow.callZero, Flow.callValue,
      Flow.callSpan, Flow.callInput, Flow.callLength, Flow.callOutput]
    omega
  have hLive : callerRegister r ≠ callerRegister nodeLive := by
    intro he
    have he' := callerRegister_injective he
    exact hu (he' ▸ (by decide : nodeLive ∈ wregs annotatedNodeUpdate))
  simp only [searchNode, leastCutBackend, wregs, List.mem_append, List.mem_singleton,
    List.not_mem_nil, or_false, not_or]
  tauto

theorem not_mem_actualPath_wregs {F : Stmt} {r : ℕ}
    (hr : 38 ≤ r) (hb : r ∉ wregs contractionBuild) (hd : r ∉ wregs CandidateDecode.program)
    (hs : r ∉ wregs searchScan) (hu : r ∉ wregs annotatedNodeUpdate)
    (hi : r ≠ pathIndex) (hc : r ≠ nodeChoice) :
    callerRegister r ∉ wregs (renamedPathControl callerRegister (searchNode F)) := by
  have hn := not_mem_searchNode_wregs hr hb hd hs hu (F := F)
  have hindex : callerRegister r ≠ callerRegister pathIndex := fun h => hi (callerRegister_injective h)
  have hchoice : callerRegister r ≠ callerRegister nodeChoice := fun h => hc (callerRegister_injective h)
  have htemp : callerRegister r ≠ rT := by unfold callerRegister; simp only [rT]; omega
  simp only [renamedPathControl, renamedPathControlStep, forUp, upLoop, ld, inc, addc,
    wregs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
  tauto

theorem actualPath_registerFrame {F : Stmt} {S time : ℕ} {c₀ c : Config}
    (he : ExecB S (renamedPathControl callerRegister (searchNode F)) c₀ time c)
    {r : ℕ} (hr : 38 ≤ r) (hb : r ∉ wregs contractionBuild)
    (hd : r ∉ wregs CandidateDecode.program) (hs : r ∉ wregs searchScan)
    (hu : r ∉ wregs annotatedNodeUpdate) (hi : r ≠ pathIndex) (hc : r ≠ nodeChoice) :
    c.reg (callerRegister r) = c₀.reg (callerRegister r) :=
  he.reg_frame (not_mem_actualPath_wregs hr hb hd hs hu hi hc)

end STACS2027.Runtimes.BoundedCost
