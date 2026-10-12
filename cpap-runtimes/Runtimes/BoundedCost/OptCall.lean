module

public import Runtimes.BoundedCost.OptControl
public import Runtimes.BoundedCost.OptSpanRAM
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptCall

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost
open OptControl

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The verified bounded-cost program's pointwise contract. -/
def BoundedProgram (program : Stmt) (C : ℕ) : Prop :=
  ∀ g k p, 3 ≤ k → ∃ output steps,
    ComputesIn program (boundedCostInput g k p) output steps (C * paper5 g k p) ∧
      steps ≤ C * paper5 g k p ∧ BoundedCostAnswer g k p output

def bound (C : ℕ) (g : Graph) (k p : ℕ) : ℕ := OptSpanRAM.span C k (cycles g k).length p

def callSpace (C : ℕ) (g : Graph) (k p : ℕ) : ℕ :=
  8 * bound C g k p + 4 * (bD g k + 3 * (k * (cycles g k).length) + 4) + 8

def State (program : Stmt) (g : Graph) (k p : ℕ) (c : Config) : Prop :=
  Fixed g k c ∧ c.reg (callerRegister budget) = p ∧ c.reg (callerRegister alive) = 1 ∧
    Flow.OffsetInput c.mem (bD g k) (CoreRAM.coreInput g k p) ∧
    (∀ r, r ∉ wregs program → c.reg (Flow.rl 0 r) = 0) ∧ c.out = []

def Result (program : Stmt) (C : ℕ) (g : Graph) (k p : ℕ) (output : List ℕ) (c : Config) : Prop :=
  Fixed g k c ∧ c.reg (callerRegister budget) = p ∧ c.reg (callerRegister alive) = 1 ∧
    c.reg (callerRegister span) = bound C g k p ∧
    Flow.OffsetInput c.mem (bD g k) (CoreRAM.coreInput g k p) ∧
    (∀ r, r ∉ wregs program → c.reg (Flow.rl 0 r) = 0) ∧ c.out = [] ∧
    c.reg Flow.callCount = output.length ∧
    (∀ i, i < output.length → c.mem (4 * (bound C g k p + i) + 1) = output.getD i 0) ∧
    BoundedCostAnswer g k p output

def program (component : Stmt) (C : ℕ) : Stmt :=
  .seq (onCallerRegisters (OptSpanRAM.program C))
    (.seq callReady (Flow.offsetCall component))

/-- The computed span equals the bounded-cost polynomial for the cached core. -/
theorem paper_core (g : Graph) (k p : ℕ) :
    paper5 (coreOccurrenceGraph g k) k p = OptSpanRAM.Q k (cycles g k).length p := by
  simp only [paper5, coreOccurrenceGraph_cycles, coreOccurrenceGraph_length, OptSpanRAM.Q,
    OptSpanRAM.z]

theorem bound_input (C : ℕ) (g : Graph) (k p : ℕ) :
    (CoreRAM.coreInput g k p).length + 1 ≤ bound C g k p := by
  simpa only [CoreRAM.coreInput_length, bound, Nat.mul_assoc] using
    OptSpanRAM.header_le_span C k (cycles g k).length p

theorem callReady_classZero {S t : ℕ} {c d : Config} (h : ExecB S callReady c t d) (r : ℕ) :
    d.reg (Flow.rl 0 r) = c.reg (Flow.rl 0 r) := by
  apply h.reg_frame
  simp [callReady, mov, wregs, Flow.rl, Flow.callSpan, Flow.callLength, Flow.offsetBase, rT]
  omega

theorem call_spec {component : Stmt} {C : ℕ} (hcomponent : BoundedProgram component C)
    (g : Graph) (k p S : ℕ) (hk : 3 ≤ k) (ht : 0 < (cycles g k).length)
    (hspace : callSpace C g k p ≤ S) :
    ∃ output, HTB S (program component C) (State component g k p)
      (Result component C g k p output)
      ((1100 + (wregs component).length) * (bound C g k p + 1)) := by
  obtain ⟨output, steps, hcompute, hsteps, hanswer⟩ := hcomponent (coreOccurrenceGraph g k) k p hk
  have hpaper := paper_core g k p
  have hscale : C * paper5 (coreOccurrenceGraph g k) k p ≤ bound C g k p := by
    rw [hpaper]
    unfold bound OptSpanRAM.span
    exact Nat.mul_le_mul_right _ (by omega)
  have hcompute' : ComputesIn component (CoreRAM.coreInput g k p) output steps (bound C g k p) := by
    rw [CoreRAM.coreInput_semantic]
    exact hcompute.mono hscale
  refine ⟨output, ?_⟩
  rintro c₀ ⟨hfixed, hp, ha, hinput, hzero, hout⟩
  obtain ⟨a, ta, hea, hb, hta, hma, hoa⟩ := OptSpanRAM.program_spec S C k (cycles g k).length p
    (by omega) ht (registerView callerRegister c₀) hfixed.1 hfixed.2.1 hp
  obtain ⟨c₁, he₁, hv₁⟩ := renameRegisters_exec callerRegister_injective hea c₀ rfl
  have hregs : ∀ r, r ≠ span → r < 650 ∨ 679 < r →
      c₁.reg (callerRegister r) = c₀.reg (callerRegister r) := by
    intro r hr hs
    have h := OptSpanRAM.program_registerFrame hea hr hs
    have hv := congrArg (fun cc : Config => cc.reg r) hv₁
    exact hv.trans h
  have hfixed₁ : Fixed g k c₁ := hfixed.transfer (by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hregs _ (by decide) (Or.inl (by decide)))
  have hb₁ : c₁.reg (callerRegister span) = bound C g k p := by
    exact (congrArg (fun cc : Config => cc.reg span) hv₁).trans hb
  have hp₁ := (hregs budget (by decide) (Or.inl (by decide))).trans hp
  have ha₁ := (hregs alive (by decide) (Or.inl (by decide))).trans ha
  have hm₁ : c₁.mem = c₀.mem := (congrArg Config.mem hv₁).trans hma
  have ho₁ : c₁.out = c₀.out := (congrArg Config.out hv₁).trans hoa
  have hz₁ : ∀ r, r ∉ wregs component → c₁.reg (Flow.rl 0 r) = 0 := by
    intro r hr
    rw [callerRegister_exec_zero he₁ r]
    exact hzero r hr
  obtain ⟨c₂, t₂, he₂, h₂, ht₂⟩ := callReady_spec (S := S) c₁ hfixed₁ hb₁ c₁ rfl
  have hi₂ : Flow.OffsetInput c₂.mem (bD g k) (CoreRAM.coreInput g k p) := by
    rw [h₂.2.2.2.2.1, hm₁]
    exact hinput
  have hz₂ : ∀ r, r ∉ wregs component → c₂.reg (Flow.rl 0 r) = 0 := by
    intro r hr
    rw [callReady_classZero he₂ r]
    exact hz₁ r hr
  have hl₂ : c₂.reg Flow.callLength = (CoreRAM.coreInput g k p).length := by
    simpa only [CoreRAM.coreInput_length] using h₂.2.2.1
  obtain ⟨c₃, t₃, he₃, h₃, ht₃⟩ := Flow.offsetCall_spec (S := S) (span := bound C g k p) (base := bD g k) (steps := steps) component (CoreRAM.coreInput g k p) output
    hcompute' (hsteps.trans hscale) (bound_input C g k p)
    (by simpa only [callSpace, CoreRAM.coreInput_length, Nat.add_assoc] using hspace)
    c₂ hi₂ h₂.2.1 hl₂ h₂.2.2.2.1 hz₂ c₂ rfl
  have hframe₂ : ∀ r ∈ [inputK, inputT, CoreRAM.coreBase, CoreRAM.coreLength, budget, alive, span],
      c₂.reg (callerRegister r) = c₁.reg (callerRegister r) := by
    intro r hr
    apply he₂.reg_frame
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hframe₃ : ∀ r ∈ [inputK, inputT, CoreRAM.coreBase, CoreRAM.coreLength, budget, alive, span],
      c₃.reg (callerRegister r) = c₂.reg (callerRegister r) := by
    intro r hr
    exact h₃.2.2.2.2.1 _ (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp [callerRegister, Nat.add_mod])
  have hfixed₃ : Fixed g k c₃ := h₂.1.transfer (by
    intro r hr
    exact hframe₃ r (by simpa using (show r ∈ [inputK, inputT, CoreRAM.coreBase, CoreRAM.coreLength] ++ [budget,alive,span] from List.mem_append_left _ hr)))
  refine ⟨c₃, ta + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_⟩
  · refine ⟨hfixed₃, ?_, ?_, ?_, ?_, h₃.2.2.2.1, ?_, h₃.1, h₃.2.1,
      (coreAnswer_transfer g k p output).mp hanswer⟩
    · exact (hframe₃ budget (by decide)).trans ((hframe₂ budget (by decide)).trans hp₁)
    · exact (hframe₃ alive (by decide)).trans ((hframe₂ alive (by decide)).trans ha₁)
    · exact (hframe₃ span (by decide)).trans ((hframe₂ span (by decide)).trans hb₁)
    · exact Flow.OffsetCallResult.input h₃ (bound_input C g k p) hi₂
    · exact h₃.2.2.1.trans (h₂.2.2.2.2.2.1.trans (ho₁.trans hout))
  · change t₃ ≤ (70 + (wregs component).length) * (bound C g k p + 1) at ht₃
    change ta ≤ 1000 * (bound C g k p + 1) at hta
    nlinarith only [hta, ht₂, ht₃]

end STACS2027.Runtimes.BoundedCost.OptCall
