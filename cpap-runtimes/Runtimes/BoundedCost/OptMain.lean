module

public import Runtimes.BoundedCost.OptLoop
public import Runtimes.BoundedCost.OptBounds
public import Runtimes.BoundedCost.ActualFPT
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptMain

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost OptControl

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def emptyAnswer : Stmt := onCallerRegisters
  (.seq (.const answerBit 0) (.seq (.write answerBit) (.seq (.const answerBit 1) (.write answerBit))))

def program (component : Stmt) (C : ℕ) : Stmt :=
  .seq CoreRAM.callerProgram (.seq startProgram
    (.ifz (callerRegister inputT) emptyAnswer (OptLoop.searchAndEmit component C)))

theorem emptyAnswer_spec {S : ℕ} (c₀ : Config) (h : c₀.out = []) :
    HTB S emptyAnswer (· = c₀) (fun c => c.out = [0, 1]) 4 := by
  refine HTB.run_le (by decide) (by decide) ?_
  intro c hc
  subst c
  refine ⟨AddrOK.of_memFree (by decide), ?_⟩
  simp +decide [emptyAnswer, onCallerRegisters, renameRegisters, h]

theorem emptyAnswer_correct {g : Graph} {k : ℕ} (ht : (cycles g k).length = 0) :
    OptEmit.OptimumAnswer g k [0, 1] := by
  have hc : cycles g k = [] := List.eq_nil_of_length_eq_zero ht
  have hhas : HasAssignment g k 0 := by
    refine ⟨[], ?_, ?_⟩ <;> simp [hc, ValidChoices, STACS2027.cost]
  refine ⟨0, [1], rfl, ⟨hhas, fun B _ => Nat.zero_le B⟩, Or.inr ?_, rfl⟩
  exact ⟨[], rfl, by simp [ht], by simp, by simp [hc, ValidChoices], by simp [STACS2027.cost]⟩

theorem program_computes {component : Stmt} {C : ℕ} (hcomponent : OptCall.BoundedProgram component C)
    (g : Graph) (k P : ℕ) (hk : 3 ≤ k) (hopt : IsOptimalCost g k P) :
    ∃ output steps, ComputesIn (program component C) (zeroCostInput g k) output steps
      (OptBounds.uniformConstant C (wregs component).length * paper5 g k P) ∧
      steps ≤ OptBounds.uniformConstant C (wregs component).length * paper5 g k P ∧
      OptEmit.OptimumAnswer g k output := by
  let S := OptBounds.uniformConstant C (wregs component).length * paper5 g k P
  obtain ⟨c₁, t₁, he₁, h₁, ht₁⟩ := CoreRAM.callerProgram_spec (by omega : 1 ≤ k)
    (OptBounds.coreSpace_le (C := C) (w := (wregs component).length) g hk P)
    (initial (zeroCostInput g k)) rfl
  obtain ⟨hg, hi, ho, hz⟩ := h₁
  obtain ⟨c₂, t₂, he₂, h₂, ht₂⟩ := startProgram_spec (S := S) c₁ hg c₁ rfl
  obtain ⟨hf, hp, ha, hm, hout⟩ := h₂
  have hstate : OptCall.State component g k 0 c₂ := by
    refine ⟨hf, hp, ha, ?_, ?_, hout.trans ho⟩
    · rw [hm]
      exact hi
    · intro r _
      exact (callerRegister_exec_zero he₂ r).trans (hz r)
  by_cases ht : (cycles g k).length = 0
  · obtain ⟨c₃, t₃, he₃, h₃, ht₃⟩ := emptyAnswer_spec (S := S) c₂ (hout.trans ho) c₂ rfl
    refine ⟨[0, 1], t₁ + (t₂ + (t₃ + 1)), ⟨c₃, ?_, h₃⟩, ?_, emptyAnswer_correct ht⟩
    · exact .seq he₁ (.seq he₂ (.ifzTrue (by rw [hf.2.1, ht]) he₃))
    · have hbound := OptBounds.emptyTime_le (C := C) (w := (wregs component).length) g k P
      rw [ht] at ht₁
      simp only [Nat.mul_zero, zero_add] at ht₁
      omega
  · have hpositive : 0 < (cycles g k).length := by omega
    have hspace := OptBounds.callSpace_le (C := C) (w := (wregs component).length) g hk P
    obtain ⟨c₃, t₃, he₃, h₃, ht₃⟩ := OptLoop.searchAndEmit_spec hcomponent hopt hk hpositive hspace c₂ hstate
    refine ⟨c₃.out, t₁ + (t₂ + (t₃ + 1)), ⟨c₃, ?_, rfl⟩, ?_, h₃⟩
    · exact .seq he₁ (.seq he₂ (.ifzFalse (by rw [hf.2.1]; exact ht) he₃))
    · have hbound := OptBounds.totalTime_le (component := component) (C := C) g hk (by omega) P
      change _ ≤ OptBounds.uniformConstant C (wregs component).length * paper5 g k P
      unfold OptBounds.totalTime at hbound
      omega

end STACS2027.Runtimes.BoundedCost.OptMain

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM

/-- The executed increasing-budget search constructs the occurrence core once,
returns `OPT` and a valid assignment, and has the last successful budget's bound. -/
theorem optimalCost_ram_fpt_from_citedFlow {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ program constant, ∀ (g : Graph) (k optimum : ℕ), 3 ≤ k → IsOptimalCost g k optimum →
      ∃ output steps,
        ComputesIn program (ZeroCost.zeroCostInput g k) output steps (constant * paper5 g k optimum) ∧
        steps ≤ constant * paper5 g k optimum ∧ OptEmit.OptimumAnswer g k output := by
  obtain ⟨component, C, hcomponent⟩ := boundedCost_ram_all_from_citedFlow hF hAL
  have hcomp : OptCall.BoundedProgram component C := hcomponent
  exact ⟨OptMain.program component C, OptBounds.uniformConstant C (wregs component).length,
    fun g k optimum hk hopt => OptMain.program_computes hcomp g k optimum hk hopt⟩

end STACS2027.Runtimes.BoundedCost
