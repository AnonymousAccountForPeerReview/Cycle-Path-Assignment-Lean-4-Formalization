module

public import Runtimes.BoundedCost.PrefixRepresentation
public import Runtimes.BoundedCost.CompilerRegisterFrame
import Mathlib.Tactic

/-! The actual counted prefix loop refreshes its dense tables, tests the budget,
and invokes compression precisely when the new occurrence exceeds it. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Compiler

open STACS2027 STACS2027.RAM Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def CompressionReady (F : Stmt) (layout : CompilerLayout) (f : CNF) (k depth : ℕ)
    (oldOutput : List ℕ) (index : ℕ) (τ : Assignment) (c : Config) : Prop :=
  PrefixBasic F layout f k depth oldOutput c ∧
    TruthTable c.mem layout.candidate (2 * f.length + 1) τ ∧
    TruthTable c.mem layout.reference (2 * f.length + 1) τ ∧
    c.reg (callerRegister processed) = index + 1 ∧ c.reg (callerRegister alive) = 1

theorem prefixBasic_caller_exec {F s : Stmt} {layout : CompilerLayout} {f : CNF}
    {k depth S time : ℕ} {oldOutput : List ℕ} {c c' : Config}
    (h : PrefixBasic F layout f k depth oldOutput c)
    (hW : ∀ r ∈ globalRegisters, r ∉ wregs s)
    (hstores : stores s = false) (hwrites : writes s = false)
    (he : ExecB S (onCallerRegisters s) c time c') :
    PrefixBasic F layout f k depth oldOutput c' := by
  rcases h with ⟨hg, hc, hz, ho⟩
  refine ⟨globals_reg_frame hg (fun r hr => he.reg_frame
    (not_mem_renameRegisters_wregs callerRegister_injective (hW r hr))), ?_,
    hz.caller_exec he, ?_⟩
  · rw [he.mem_frame (by simpa [onCallerRegisters, renameRegisters_stores] using hstores)]
    exact hc
  · exact (he.out_frame (by simpa [onCallerRegisters, renameRegisters_writes] using hwrites)).trans ho

private theorem globals_not_inc (r : ℕ) (hr : r ∈ globalRegisters) : r ∉ wregs (inc processed) := by
  simp +decide [globalRegisters, wregs, inc, addc, processed, rT] at hr ⊢
  all_goals omega

private theorem globals_not_excess (r : ℕ) (hr : r ∈ globalRegisters) :
    r ∉ wregs (.sub prefixExcess scanUnsatisfied budget) := by
  simp +decide [globalRegisters, wregs, prefixExcess] at hr ⊢
  omega

theorem prefixBody_spec {F : Stmt} {factory : LeastCutFactory} {S B k depth : ℕ}
    {layout : CompilerLayout} {f : CNF} {oldOutput : List ℕ}
    (hf : SolverDomain f)
    (hgeo : layout.formula + 2 * f.length ≤ layout.active ∧
      layout.active + f.length ≤ layout.candidate ∧
      layout.candidate + 2 * (2 * f.length + 1) ≤ layout.reference ∧
      layout.reference + 2 * (2 * f.length + 1) ≤ S)
    (hcomp : ∀ (i : ℕ) (hi : i < f.length) (τ : Assignment),
      unsatisfiedCount τ (f.take i) ≤ k → k < unsatisfiedCount τ (f.take (i + 1)) →
      HTB S (compression F) (CompressionReady F layout f k depth oldOutput i τ)
        (PrefixRep F layout f k depth oldOutput (i + 1)
          (encodedCompressionSearch (factory τ) τ depth (compressionBase τ (f.take i))
            (compressionSpecial τ (f.take i) (f.getD i [])) k)) B)
    (i : ℕ) (hi : i < f.length) (state : Option Assignment)
    (hcorrect : PrefixCorrect f k i state) :
    HTB S (prefixBody F)
      (fun c => PrefixRep F layout f k depth oldOutput i state c ∧
        c.reg (callerRegister prefixIndex) = i ∧ c.reg (callerRegister scanClauseCount) = f.length)
      (fun c => PrefixRep F layout f k depth oldOutput (i + 1)
          (prefixStep factory depth k f i state) c ∧
        c.reg (callerRegister prefixIndex) = i ∧ c.reg (callerRegister scanClauseCount) = f.length)
      (B + 16 * (2 * f.length + 1) + 116 * f.length + 26) := by
  intro c₀ ⟨⟨hbasic, hanswer⟩, hindex, hcount⟩
  cases state with
  | none =>
    exact ⟨c₀, 2, .ifzTrue hanswer (.skip c₀),
      ⟨⟨hbasic, hanswer⟩, hindex, hcount⟩, by omega⟩
  | some τ =>
    obtain ⟨halive, hprocessed, htruth⟩ := hanswer
    have hincFree : LoopFree (onCallerRegisters (inc processed)) := by decide
    let c₁ := run (onCallerRegisters (inc processed)) c₀
    have he₁ := execB_run (S := S) (onCallerRegisters (inc processed)) hincFree c₀
      (AddrOK.of_memFree (by decide))
    have hb₁ : PrefixBasic F layout f k depth oldOutput c₁ :=
      prefixBasic_caller_exec hbasic globals_not_inc (by decide) (by decide) he₁
    have hp₁ : c₁.reg (callerRegister processed) = i + 1 := by
      simp +decide [c₁, onCallerRegisters, renameRegisters, inc, addc, hprocessed]
    have ht₁ : TruthTable c₁.mem layout.candidate (2 * f.length + 1) τ := by
      simpa only [c₁, run_mem_of_stores hincFree (by decide) c₀] using htruth
    have hg₁ : PrefixCheckGlobals layout.formula layout.active layout.candidate layout.reference
        (2 * f.length + 1) f.length (i + 1) (registerView callerRegister c₁) :=
      ⟨⟨hb₁.1.formula, hb₁.1.active, hb₁.1.candidate, hb₁.1.reference, hb₁.1.clauses⟩,
        hp₁, hb₁.1.truthLength⟩
    obtain ⟨c₂, t₂, he₂, hr₂, ht₂⟩ := prefixCheckCaller_spec hf hgeo c₁ hg₁ hb₁.2.1 ht₁ c₁ rfl
    have hb₂ : PrefixBasic F layout f k depth oldOutput c₂ := by
      refine ⟨globals_prefixCheck_frame hb₁.1 he₂, hr₂.1.2.1, ?_, ?_⟩
      · intro r hr
        exact (hr₂.2.2 _ (Flow.rl_mod (by decide) r)).trans (hb₁.2.2.1 r hr)
      · exact hr₂.1.2.2.2.2.2.2.2.2.1.trans hb₁.2.2.2
    have hp₂ : c₂.reg (callerRegister processed) = i + 1 := hr₂.1.1.2.1
    have halive₂ : c₂.reg (callerRegister alive) = 1 := by
      exact (he₂.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans
        ((he₁.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans halive)
    have hsubFree : LoopFree (onCallerRegisters (.sub prefixExcess scanUnsatisfied budget)) := by decide
    let c₃ := run (onCallerRegisters (.sub prefixExcess scanUnsatisfied budget)) c₂
    have he₃ := execB_run (S := S)
      (onCallerRegisters (.sub prefixExcess scanUnsatisfied budget)) hsubFree c₂
      (AddrOK.of_memFree (by decide))
    have hb₃ : PrefixBasic F layout f k depth oldOutput c₃ :=
      prefixBasic_caller_exec hb₂ globals_not_excess (by decide) (by decide) he₃
    have hsub : c₃.reg (callerRegister prefixExcess) = unsatisfiedCount τ (f.take (i + 1)) - k := by
      have hu := hr₂.1.2.2.2.2.2.2.1
      have hk := hb₂.1.budget
      change c₂.reg (callerRegister scanUnsatisfied) = _ at hu
      change c₂.reg (callerRegister budget) = k at hk
      simp +decide [c₃, onCallerRegisters, renameRegisters, hu, hk]
    have hp₃ : c₃.reg (callerRegister processed) = i + 1 := by
      exact (he₃.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hp₂
    have halive₃ : c₃.reg (callerRegister alive) = 1 := by
      exact (he₃.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans halive₂
    have ht₃ : TruthTable c₃.mem layout.candidate (2 * f.length + 1) τ := by
      exact hr₂.1.2.2.1
    have hr₃ : TruthTable c₃.mem layout.reference (2 * f.length + 1) τ := by
      exact hr₂.1.2.2.2.1
    have hrest : ∃ c₄ t₄,
        ExecB S (.ifz (callerRegister prefixExcess) .skip (compression F)) c₃ t₄ c₄ ∧
        PrefixRep F layout f k depth oldOutput (i + 1)
          (prefixStep factory depth k f i (some τ)) c₄ ∧ t₄ ≤ B + 2 := by
      by_cases hs : unsatisfiedCount τ (f.take (i + 1)) ≤ k
      · have hzero : c₃.reg (callerRegister prefixExcess) = 0 := by rw [hsub]; omega
        exact ⟨c₃, 2, .ifzTrue hzero (.skip c₃),
          by simpa [prefixStep, hs] using (show PrefixRep F layout f k depth oldOutput
            (i + 1) (some τ) c₃ from ⟨hb₃, halive₃, hp₃, ht₃⟩), by omega⟩
      · obtain ⟨c₄, t₄, he₄, hp₄, ht₄⟩ := hcomp i hi τ hcorrect (by omega) c₃
          ⟨hb₃, ht₃, hr₃, hp₃, halive₃⟩
        have hnonzero : c₃.reg (callerRegister prefixExcess) ≠ 0 := by rw [hsub]; omega
        exact ⟨c₄, t₄ + 1, .ifzFalse hnonzero he₄,
          by simpa [prefixStep, hs] using hp₄, by omega⟩
    obtain ⟨c₄, t₄, he₄, hp₄, ht₄⟩ := hrest
    have he : ExecB S (prefixBody F) c₀
        (RAM.cost (onCallerRegisters (inc processed)) c₀ + (t₂ + (1 + t₄)) + 1) c₄ :=
      .ifzFalse (by rw [halive]; decide) (.seq he₁ (.seq he₂ (.seq he₃ he₄)))
    refine ⟨c₄, _, he, ⟨hp₄, ?_, hp₄.1.1.clauses⟩, ?_⟩
    · exact (he.reg_frame (by
        have hcompframe := not_mem_compression_prefixIndex F
        have hincframe : callerRegister prefixIndex ∉ wregs (onCallerRegisters (inc processed)) :=
          not_mem_renameRegisters_wregs callerRegister_injective (by decide)
        have hcheckframe : callerRegister prefixIndex ∉ wregs prefixCheckCaller :=
          not_mem_renameRegisters_wregs callerRegister_injective (by decide)
        simp only [prefixBody, wregs, List.mem_append, List.not_mem_nil, List.mem_singleton,
          not_or, onCallerRegisters, renameRegisters_wregs]
        simp only [not_false_eq_true, true_and, and_true]
        exact ⟨hincframe, hcheckframe, by decide, hcompframe⟩)).trans hindex
    · have hcost : RAM.cost (onCallerRegisters (inc processed)) c₀ = 2 := rfl
      rw [hcost]
      omega

end STACS2027.Runtimes.BoundedCost.Compiler
