module

public import Runtimes.BoundedCost.InitialCompilerRAM
import Mathlib.Tactic

/-! Initialization, the budget guard, the full prefix loop and certificate
output compose as bounded executions of the fixed compiler program. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Compiler

open STACS2027 STACS2027.RAM Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def compilerExecutionCost (constant compression clauses : ℕ) : ℕ :=
  400 + 5 * (constant + 1) + 80 * (clauses + 1) +
    clauses * (compression + 16 * (2 * clauses + 1) + 116 * clauses + 30) +
    320 * (clauses + 1) ^ 2 + 8

theorem compilerExecution_spec {F : Stmt} {constant k S B : ℕ} {f : CNF}
    {factory : LeastCutFactory} (hf : SolverDomain f)
    (hfactory : LeastCutFactoryCorrect factory)
    (hspace : (compilerLayout constant f.length k).space ≤ S)
    (hcomp : k < f.length → ∀ (i : ℕ) (hi : i < f.length) (τ : Assignment),
      unsatisfiedCount τ (f.take i) ≤ k → k < unsatisfiedCount τ (f.take (i + 1)) →
      HTB S (compression F)
        (CompressionReady F (compilerLayout constant f.length k) f k
          (min k f.length + 1) [] i τ)
        (PrefixRep F (compilerLayout constant f.length k) f k (min k f.length + 1) [] (i + 1)
          (encodedCompressionSearch (factory τ) τ (min k f.length + 1)
            (compressionBase τ (f.take i)) (compressionSpecial τ (f.take i) (f.getD i [])) k)) B) :
    ∃ output steps, ComputesIn (program F constant) (a2In f k) output steps S ∧
      steps ≤ compilerExecutionCost constant B f.length ∧ A2Answer f k output := by
  let layout := compilerLayout constant f.length k
  have hgeo : layout.formula + 2 * f.length ≤ layout.active ∧
      layout.active + f.length ≤ layout.candidate ∧
      layout.candidate + 2 * (2 * f.length + 1) ≤ layout.reference ∧
      layout.reference + 2 * (2 * f.length + 1) ≤ S := by
    dsimp [layout, compilerLayout] at hspace ⊢
    omega
  have houtput : layout.formula + 2 * f.length ≤ S ∧
      layout.candidate + 2 * (2 * f.length + 1) ≤ S := by omega
  obtain ⟨c₁, t₁, he₁, hp₁, ht₁⟩ := initialCompilerRAM_spec (F := F) hf hspace
    (initial (a2In f k)) rfl
  let guard := onCallerRegisters (.sub trivialExcess scanClauseCount budget)
  let c₂ := run guard c₁
  have he₂ : ExecB S guard c₁ 1 c₂ := execB_run guard (by decide) c₁
    (AddrOK.of_memFree (by decide))
  have hb₂ : PrefixBasic F layout f k (min k f.length + 1) [] c₂ :=
    prefixBasic_caller_exec hp₁.1
      (by intro r hr; simp +decide [globalRegisters, wregs, trivialExcess] at hr ⊢; omega)
      rfl rfl he₂
  have ht₂ : TruthTable c₂.mem layout.candidate (2 * f.length + 1) (fun _ => false) := hp₁.2.1
  have hp₂ : c₂.reg (callerRegister processed) = 0 :=
    (he₂.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hp₁.2.2
  have hguard : c₂.reg (callerRegister trivialExcess) = f.length - k := by
    have hm := hp₁.1.1.clauses
    have hk := hp₁.1.1.budget
    change c₁.reg (callerRegister scanClauseCount) = f.length at hm
    change c₁.reg (callerRegister budget) = k at hk
    simp +decide [c₂, guard, onCallerRegisters, renameRegisters, hm, hk]
  by_cases hkm : f.length ≤ k
  · have hzero : c₂.reg (callerRegister trivialExcess) = 0 := by rw [hguard]; omega
    have hfalse : unsatisfiedCount (fun _ => false) f ≤ k :=
      (List.countP_le_length).trans hkm
    obtain ⟨c₃, t₃, he₃, hp₃, ht₃⟩ := positiveOutput_answer hf houtput c₂ hb₂.1 hb₂.2.1
      ht₂ hb₂.2.2.2 hfalse c₂ rfl
    refine ⟨c₃.out, t₁ + (1 + (t₃ + 1)), ⟨c₃, .seq he₁ (.seq he₂ (.ifzTrue hzero he₃)), rfl⟩,
      ?_, hp₃⟩
    unfold compilerExecutionCost
    omega
  · have hlt : k < f.length := by omega
    have hnonzero : c₂.reg (callerRegister trivialExcess) ≠ 0 := by rw [hguard]; omega
    have hdepth : k < min k f.length + 1 := by rw [Nat.min_eq_left (by omega)]; omega
    let c₃ := c₂.setReg (callerRegister alive) 1
    have he₃ : ExecB S (.const (callerRegister alive) 1) c₂ 1 c₃ := .const _ _ _
    have hpre : PrefixRep F layout f k (min k f.length + 1) [] 0 (some (fun _ => false)) c₃ :=
      initialPrefixRep_alive hb₂ ht₂ hp₂
    obtain ⟨c₄, t₄, he₄, hp₄, ht₄⟩ := prefixLoop_spec hf hfactory hdepth hgeo (hcomp hlt) c₃ hpre
    obtain ⟨c₅, t₅, he₅, hp₅, ht₅⟩ := finish_spec hf hfactory hdepth houtput c₄ hp₄.1
    refine ⟨c₅.out, t₁ + (1 + (1 + (t₄ + t₅) + 1)),
      ⟨c₅, .seq he₁ (.seq he₂ (.ifzFalse hnonzero (.seq he₃ (.seq he₄ he₅)))), rfl⟩,
      ?_, hp₅⟩
    unfold compilerExecutionCost
    omega

end STACS2027.Runtimes.BoundedCost.Compiler
