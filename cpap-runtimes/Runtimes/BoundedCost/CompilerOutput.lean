module

public import Runtimes.BoundedCost.CompilerState
import Mathlib.Tactic

/-! The fixed compiler's positive and negative terminal output programs. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Compiler

open STACS2027 STACS2027.RAM Complexity.SAT

theorem initialized_tables {constant k : ℕ} {f : CNF} (hf : SolverDomain f)
    (memory : ℕ → ℕ) :
    let layout := compilerLayout constant f.length k
    let next := CompilerInit.initializedMemory constant f.length k memory (TwoSat.codes f)
    Arr next layout.formula (TwoSat.codes f) ∧
      TruthTable next layout.candidate (2 * f.length + 1) (fun _ => false) := by
  dsimp only
  let layout := compilerLayout constant f.length k
  let copied := ArrayBlocks.prefixMemory memory layout.formula (TwoSat.codes f) (TwoSat.codes f).length
  have hcodes := ArrayBlocks.prefixMemory_array memory layout.formula (TwoSat.codes f)
  have hlen := TwoSat.length_codes hf
  refine ⟨?_, ?_⟩
  · intro i hi
    change CandidateDecode.prefixMemory copied layout.candidate (fun _ => false)
      (2 * f.length + 1) (layout.formula + i) = _
    rw [CandidateDecode.prefixMemory_outside (by
      left
      dsimp [layout, compilerLayout]
      rw [hlen] at hi
      omega)]
    exact hcodes i hi
  · intro u hu
    change CandidateDecode.prefixMemory copied layout.candidate (fun _ => false)
      (2 * f.length + 1) (layout.candidate + u) = _
    simp only [CandidateDecode.prefixMemory, CandidateDecode.bit,
      if_pos (show layout.candidate ≤ layout.candidate + u ∧
        layout.candidate + u < layout.candidate + 2 * (2 * f.length + 1) by omega),
      Nat.add_sub_cancel_left]

theorem positiveOutput_spec {S : ℕ} {layout : CompilerLayout} {f : CNF} {k depth : ℕ}
    {σ : Assignment} (hf : SolverDomain f)
    (hspace : layout.formula + 2 * f.length ≤ S ∧
      layout.candidate + 2 * (2 * f.length + 1) ≤ S)
    (c₀ : Config) (hg : Globals layout (2 * f.length + 1) f.length k depth
      (registerView callerRegister c₀))
    (hcodes : Arr c₀.mem layout.formula (TwoSat.codes f))
    (htruth : TruthTable c₀.mem layout.candidate (2 * f.length + 1) σ) :
    HTB S positiveOutput (· = c₀)
      (fun c => c.out = c₀.out ++ assignmentAnswer f σ)
      (320 * (f.length + 1) ^ 2) := by
  have hcertificate := Certificate.outputCertificate_assignmentAnswer
    (O := c₀.out) (clauseMemory_of_tables hf hcodes htruth) (TwoSat.length_codes hf)
    hcodes (truthTable_positive htruth) hspace
  have hrenamed := onCallerRegisters_htb hcertificate
  refine hrenamed.mono ?_ (fun c hc => hc.2) le_rfl
  intro c hc
  subst c
  exact ⟨⟨hg.formula, hg.candidate, hg.clauses, hg.nodes, rfl⟩, rfl⟩

theorem negativeOutput_spec {S : ℕ} (c₀ : Config) :
    HTB S negativeOutput (· = c₀) (fun c => c.out = c₀.out ++ [0]) 2 := by
  refine HTB.run_le (by decide) (by decide) ?_
  intro c hc
  subst c
  refine ⟨AddrOK.of_memFree (by decide), ?_⟩
  simp +decide [negativeOutput, onCallerRegisters, renameRegisters]

theorem positiveOutput_answer {S : ℕ} {layout : CompilerLayout} {f : CNF} {k depth : ℕ}
    {σ : Assignment} (hf : SolverDomain f)
    (hspace : layout.formula + 2 * f.length ≤ S ∧
      layout.candidate + 2 * (2 * f.length + 1) ≤ S)
    (c₀ : Config) (hg : Globals layout (2 * f.length + 1) f.length k depth
      (registerView callerRegister c₀))
    (hcodes : Arr c₀.mem layout.formula (TwoSat.codes f))
    (htruth : TruthTable c₀.mem layout.candidate (2 * f.length + 1) σ)
    (hout : c₀.out = []) (hσ : unsatisfiedCount σ f ≤ k) :
    HTB S positiveOutput (· = c₀) (fun c => A2Answer f k c.out)
      (320 * (f.length + 1) ^ 2) := by
  refine (positiveOutput_spec hf hspace c₀ hg hcodes htruth).mono
    (fun c hc => hc) ?_ le_rfl
  intro c hc
  rw [hout, List.nil_append] at hc
  rw [hc]
  exact assignmentAnswer_correct hf hσ

theorem negativeOutput_answer {S : ℕ} {f : CNF} {k : ℕ}
    (hno : ¬ AlmostSatisfiable f k) (c₀ : Config) (hout : c₀.out = []) :
    HTB S negativeOutput (· = c₀) (fun c => A2Answer f k c.out) 2 := by
  refine (negativeOutput_spec c₀).mono (fun c hc => hc) ?_ le_rfl
  intro c hc
  rw [hout, List.nil_append] at hc
  exact Or.inl ⟨hno, hc⟩

end STACS2027.Runtimes.BoundedCost.Compiler
