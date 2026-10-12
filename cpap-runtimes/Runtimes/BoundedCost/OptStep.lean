module

public import Runtimes.BoundedCost.OptCall
public import BoundedCost.Algorithm3Search
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptStep

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost OptControl

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def Done (component : Stmt) (C : ℕ) (g : Graph) (k p : ℕ) (c : Config) : Prop :=
  Fixed g k c ∧ c.reg (callerRegister budget) = p ∧ c.reg (callerRegister alive) = 0 ∧
    c.reg (callerRegister span) = OptCall.bound C g k p ∧
    Flow.OffsetInput c.mem (bD g k) (CoreRAM.coreInput g k p) ∧
    (∀ r, r ∉ wregs component → c.reg (Flow.rl 0 r) = 0) ∧ c.out = [] ∧
    ∃ output, c.reg Flow.callCount = output.length ∧
      (∀ i, i < output.length → c.mem (4 * (OptCall.bound C g k p + i) + 1) = output.getD i 0) ∧
      BoundedCostAnswer g k p output ∧ output.getD 0 0 = 1

def program (component : Stmt) (C : ℕ) : Stmt :=
  .seq (OptCall.program component C) (onCallerRegisters decideAnswer)

def cost (component : Stmt) (C : ℕ) (g : Graph) (k p : ℕ) : ℕ :=
  (1150 + (wregs component).length) * (OptCall.bound C g k p + 1)

theorem callSpace_mono {C k p q : ℕ} {g : Graph} (hpq : p ≤ q) :
    OptCall.callSpace C g k p ≤ OptCall.callSpace C g k q := by
  have h := OptSpanRAM.span_mono (C := C) (k := k) (t := (cycles g k).length) hpq
  unfold OptCall.callSpace OptCall.bound
  omega

theorem decide_registerFrame {S time : ℕ} {c d : Config}
    (he : ExecB S (onCallerRegisters decideAnswer) c time d) {r : ℕ}
    (hr : r ∉ [budget, alive, address, answerBit, rT]) :
    d.reg (callerRegister r) = c.reg (callerRegister r) := by
  apply he.reg_frame
  rw [onCallerRegisters, renameRegisters_wregs]
  intro hm
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
  have har : a = r := callerRegister_injective heq
  subst a
  have : r ∈ [budget, alive, address, answerBit, rT] := by
    simp only [decideAnswer, readAnswer, reject, mov, inc, dec, addc, subc, wregs,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    tauto
  exact hr this

theorem decide_fixed {S time : ℕ} {c d : Config} {g : Graph} {k : ℕ}
    (he : ExecB S (onCallerRegisters decideAnswer) c time d) (h : Fixed g k c) : Fixed g k d := by
  apply h.transfer
  intro r hr
  apply decide_registerFrame he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

theorem step_spec {component : Stmt} {C : ℕ} (hcomponent : OptCall.BoundedProgram component C)
    {g : Graph} {k P : ℕ} (hopt : IsOptimalCost g k P) (hk : 3 ≤ k)
    (ht : 0 < (cycles g k).length) (S p : ℕ) (hpP : p ≤ P)
    (hspace : OptCall.callSpace C g k P ≤ S) :
    HTB S (program component C) (OptCall.State component g k p)
      (fun c => if p = P then Done component C g k P c else OptCall.State component g k (p + 1) c)
      (cost component C g k p) := by
  obtain ⟨output, hcall⟩ := OptCall.call_spec hcomponent g k p S hk ht
    ((callSpace_mono hpP).trans hspace)
  intro c₀ h₀
  obtain ⟨c₁, t₁, he₁, h₁, ht₁⟩ := hcall c₀ h₀
  obtain ⟨hg, hp, ha, hb, hi, hz, ho, hl, hm, hans⟩ := h₁
  have hS := (callSpace_mono hpP).trans hspace
  have hinputSpace : 4 * (bD g k + (CoreRAM.coreInput g k p).length - 1) + 2 < S := by
    simp only [OptCall.callSpace, CoreRAM.coreInput_length] at hS ⊢
    omega
  have houtputSpace : 4 * OptCall.bound C g k p + 1 < S := by
    unfold OptCall.callSpace at hS
    omega
  have hglobals : DecisionGlobals (bD g k) (CoreRAM.coreInput g k p).length
      (OptCall.bound C g k p) p (registerView callerRegister c₁) := by
    exact ⟨hg.2.2.1, by simpa only [CoreRAM.coreInput_length, registerView] using hg.2.2.2, hb, hp, ha⟩
  by_cases heq : p = P
  · have hpositive : HasAssignment g k p := by simpa only [heq] using hopt.1
    obtain ⟨pos, hpos⟩ := hans.positive hpositive
    have hlength : 0 < output.length := by simp [hpos]
    have hhead : c₁.mem (4 * OptCall.bound C g k p + 1) = 1 := by
      have hh := hm 0 hlength
      simpa [hpos] using hh
    obtain ⟨c₂, t₂, he₂, h₂, ht₂⟩ := onCallerRegisters_htb
      (decideAnswer_one_spec hinputSpace houtputSpace hhead) c₁ ⟨hglobals, rfl, rfl⟩
    simp only [registerView] at h₂
    have hg₂ := decide_fixed he₂ hg
    have hb₂ := (decide_registerFrame he₂ (r := span) (by decide)).trans hb
    have hz₂ : ∀ r, r ∉ wregs component → c₂.reg (Flow.rl 0 r) = 0 := by
      intro r hr
      rw [callerRegister_exec_zero he₂ r]
      exact hz r hr
    refine ⟨c₂, t₁ + t₂, .seq he₁ he₂, ?_, ?_⟩
    · simp only [heq, if_pos rfl]
      refine ⟨hg₂, ?_, h₂.2.1, ?_, ?_, hz₂, ?_, output, ?_, ?_, ?_, ?_⟩
      · simpa only [registerView, heq] using h₂.1
      · simpa only [heq] using hb₂
      · change Flow.OffsetInput c₂.mem _ _
        rw [h₂.2.2.1]
        simpa only [heq] using hi
      · exact h₂.2.2.2.trans ho
      · have hf : c₂.reg Flow.callCount = c₁.reg Flow.callCount := by
          exact he₂.reg_frame (by decide)
        exact hf.trans hl
      · intro i hidx
        rw [h₂.2.2.1]
        simpa only [heq] using hm i hidx
      · simpa only [heq] using hans
      · simp [hpos]
    · unfold cost
      nlinarith only [ht₁, ht₂]
  · have hnegative : ¬ HasAssignment g k p := by
      intro hx
      have := hopt.2 p hx
      omega
    have houtput : output = [0] := hans.negative hnegative
    have hhead : c₁.mem (4 * OptCall.bound C g k p + 1) = 0 := by
      have hh := hm 0 (by simp [houtput])
      simpa [houtput] using hh
    obtain ⟨c₂, t₂, he₂, h₂, ht₂⟩ := onCallerRegisters_htb
      (decideAnswer_zero_spec (by simp [CoreRAM.coreInput_length]) hinputSpace houtputSpace hhead)
      c₁ ⟨hglobals, rfl, rfl⟩
    simp only [registerView] at h₂
    have hz₂ : ∀ r, r ∉ wregs component → c₂.reg (Flow.rl 0 r) = 0 := by
      intro r hr
      rw [callerRegister_exec_zero he₂ r]
      exact hz r hr
    refine ⟨c₂, t₁ + t₂, .seq he₁ he₂, ?_, ?_⟩
    · simp only [if_neg heq]
      refine ⟨decide_fixed he₂ hg, h₂.1, h₂.2.1, ?_, hz₂, h₂.2.2.2.trans ho⟩
      change Flow.OffsetInput c₂.mem _ _
      rw [h₂.2.2.1]
      rw [show bD g k + (CoreRAM.coreInput g k p).length - 1 =
        bD g k + 3 * (k * (cycles g k).length) + 3 by rw [CoreRAM.coreInput_length]; omega]
      exact coreInput_update_budget (new := p + 1) hi
    · unfold cost
      nlinarith only [ht₁, ht₂]

end STACS2027.Runtimes.BoundedCost.OptStep
