module

public import Runtimes.BoundedCost.PrefixRAM
public import Runtimes.BoundedCost.CompilerOutput
import Mathlib.Tactic

/-! The fixed prefix loop and terminal output execute the exact semantic
prefix fold; concrete compression execution supplies its only callback. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Compiler

open STACS2027 STACS2027.RAM Complexity.SAT

theorem prefixLoop_spec {F : Stmt} {factory : LeastCutFactory} {S B k depth : ℕ}
    {layout : CompilerLayout} {f : CNF} {oldOutput : List ℕ}
    (hf : SolverDomain f) (hfactory : LeastCutFactoryCorrect factory) (hdepth : k < depth)
    (hgeo : layout.formula + 2 * f.length ≤ layout.active ∧
      layout.active + f.length ≤ layout.candidate ∧
      layout.candidate + 2 * (2 * f.length + 1) ≤ layout.reference ∧
      layout.reference + 2 * (2 * f.length + 1) ≤ S)
    (hcomp : ∀ (i : ℕ) (hi : i < f.length) (τ : Assignment),
      unsatisfiedCount τ (f.take i) ≤ k → k < unsatisfiedCount τ (f.take (i + 1)) →
      HTB S (compression F) (CompressionReady F layout f k depth oldOutput i τ)
        (PrefixRep F layout f k depth oldOutput (i + 1)
          (encodedCompressionSearch (factory τ) τ depth (compressionBase τ (f.take i))
            (compressionSpecial τ (f.take i) (f.getD i [])) k)) B) :
    HTB S (prefixLoop F)
      (PrefixRep F layout f k depth oldOutput 0 (some (fun _ => false)))
      (fun c => PrefixRep F layout f k depth oldOutput f.length
          (prefixFold factory depth k f f.length) c ∧
        c.reg (callerRegister prefixIndex) = f.length)
      (f.length * (B + 16 * (2 * f.length + 1) + 116 * f.length + 30) + 3) := by
  let Inv := fun count => PrefixRep F layout f k depth oldOutput count
    (prefixFold factory depth k f count)
  have h := HTB.forUpC (S := S) (i := callerRegister prefixIndex)
    (n := callerRegister scanClauseCount) (N := f.length) (body := prefixBody F)
    Inv (B + 16 * (2 * f.length + 1) + 116 * f.length + 26)
    (by decide) (by decide) (by decide)
    (fun count => prefixRep_indep F layout f k depth oldOutput count _)
    (fun i hi => by
      have hc := prefixFold_correct factory hfactory hdepth (solverDomain_clauses2 hf) i (by omega)
      simpa only [Inv, prefixFold_succ] using prefixBody_spec hf hgeo hcomp i hi _ hc)
  refine h.mono ?_ ?_ (by
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega)
  · intro c hc
    exact ⟨by simpa [Inv] using hc, hc.1.1.clauses⟩
  · rintro c ⟨hi, hindex, _⟩
    exact ⟨hi, hindex⟩

theorem finish_spec {F : Stmt} {factory : LeastCutFactory} {S k depth : ℕ}
    {layout : CompilerLayout} {f : CNF}
    (hf : SolverDomain f) (hfactory : LeastCutFactoryCorrect factory) (hdepth : k < depth)
    (hspace : layout.formula + 2 * f.length ≤ S ∧
      layout.candidate + 2 * (2 * f.length + 1) ≤ S) :
    HTB S finish
      (PrefixRep F layout f k depth [] f.length (prefixFold factory depth k f f.length))
      (fun c => A2Answer f k c.out) (320 * (f.length + 1) ^ 2 + 2) := by
  intro c₀ ⟨hb, ha⟩
  have hc := prefixFold_correct factory hfactory hdepth (solverDomain_clauses2 hf) f.length le_rfl
  cases hanswer : prefixFold factory depth k f f.length with
  | none =>
    rw [hanswer] at ha hc
    have hno : ¬ AlmostSatisfiable f k := by simpa [PrefixCorrect] using hc
    obtain ⟨c, time, he, hp, ht⟩ := negativeOutput_answer hno c₀ hb.2.2.2 c₀ rfl
    exact ⟨c, time + 1, .ifzTrue ha he, hp, by nlinarith⟩
  | some σ =>
    rw [hanswer] at ha hc
    obtain ⟨halive, _, htruth⟩ := ha
    have hσ : unsatisfiedCount σ f ≤ k := by simpa [PrefixCorrect] using hc
    obtain ⟨c, time, he, hp, ht⟩ := positiveOutput_answer hf hspace c₀ hb.1 hb.2.1
      htruth hb.2.2.2 hσ c₀ rfl
    exact ⟨c, time + 1, .ifzFalse (by rw [halive]; decide) he, hp, by omega⟩

end STACS2027.Runtimes.BoundedCost.Compiler
