module

public import Complexity.Composition
import Lean.Elab.Tactic.Omega

/-!
# Composition with a stack machine that is correct only on a domain

`polyTime_comp` composes two total polynomial-time transducers. Here the second stage is a
Boolean-stack machine `S` whose behaviour is only known on words satisfying a predicate `D`
(for instance, the valid encodings of some data type), and the first stage always produces such
words. The proof compiles `S` to a tape machine (`StackCompile.simulate`), runs the two tape
machines in sequence on three stacks (`TapeToStacks.run_compositionMachine`) and compiles the
result back (`StackCompile.polyTime_of_stack`).

This file is core-only (no Mathlib).
-/

@[expose] public section

namespace Complexity

set_option backward.isDefEq.respectTransparency false

/-- `StackCompile.budget` is monotone in the input length and in the fuel. -/
theorem StackCompile.budget_mono_both (S : StackMachine.Machine) {n m fuel fuel' : Nat}
    (hn : n ≤ m) (hfuel : fuel ≤ fuel') :
    StackCompile.budget S n fuel ≤ StackCompile.budget S m fuel' := by
  unfold StackCompile.budget StackInit.initBudget
  have h := Nat.mul_le_mul hfuel
    (StackCompile.instructionBudget_mono S (Nat.add_le_add hn hfuel))
  omega

/-- The time bound of `polyTime_comp_stack_on`: first stage with time `powerBound c k`, second
stage a stack machine `S` with time `powerBound d l`. -/
def compositionOnBound (S : StackMachine.Machine) (c k d l : Nat) (n : Nat) : Nat :=
  72 * (n + powerBound c k n +
    StackCompile.budget S (n + 2 * powerBound c k n)
      (powerBound d l (n + 2 * powerBound c k n)) + 1)

theorem polynomialBound_compositionOnBound (S : StackMachine.Machine) (c k d l : Nat) :
    PolynomialBound (compositionOnBound S c k d l) := by
  have hf := PolynomialBound.power c k
  have hmiddle := PolynomialBound.identity.add ((PolynomialBound.constant 2).mul hf)
  have hbudget := StackCompile.polynomialBound_budget S (powerBound d l) (PolynomialBound.power d l)
  have hg := hbudget.comp hmiddle
  exact (PolynomialBound.constant 72).mul
    (((PolynomialBound.identity.add hf).add hg).add (PolynomialBound.constant 1))

/-- Composition with a machine that is only guaranteed on a domain `D`. -/
theorem polyTime_comp_stack_on {f : Word → Word} (hf : PolyTime f) (D : Word → Prop)
    (hD : ∀ x, D (f x)) (S : StackMachine.Machine) (bound : Nat → Nat) (hb : PolynomialBound bound)
    (g : Word → Word)
    (hS : ∀ w, D w → ∃ time registers, time ≤ bound w.length ∧
      StackMachine.runInput S time w = some (true, registers) ∧ registers 0 = g w) :
    PolyTime (fun x => g (f x)) := by
  obtain ⟨first, c, k, hf⟩ := hf
  obtain ⟨d, l, hb⟩ := hb
  refine StackCompile.polyTime_of_stack
    (TapeToStacks.compositionMachine first (StackCompile.compile S))
    (compositionOnBound S c k d l) (polynomialBound_compositionOnBound S c k d l) ?_
  intro input
  obtain ⟨t, middle, ht, hfirst, hmiddle⟩ := hf input
  obtain ⟨s, registers, hs, hrunS, hout⟩ := hS middle.output (hmiddle ▸ hD input)
  obtain ⟨τ, out, hτ, hsecond, hout'⟩ :=
    StackCompile.simulate S s middle.output (true, registers) hrunS
  obtain ⟨time, htime, hrun⟩ :=
    TapeToStacks.run_compositionMachine first (StackCompile.compile S) t τ input middle out
      hfirst hsecond
  have hlength := runInput_output_length_le first t input (true, middle) hfirst
  simp only at hlength
  have hmiddleBound : middle.output.length ≤ input.length + 2 * powerBound c k input.length := by
    omega
  have hs' : s ≤ powerBound d l (input.length + 2 * powerBound c k input.length) :=
    Nat.le_trans hs (Nat.le_trans (hb _) (powerBound_mono d l hmiddleBound))
  have hτ' := Nat.le_trans hτ (StackCompile.budget_mono_both S hmiddleBound hs')
  refine ⟨time, TapeToStacks.regs out.output [] [], ?_, hrun, ?_⟩
  · unfold compositionOnBound
    omega
  · rw [TapeToStacks.regs_zero, hout']
    exact hout.trans (congrArg g hmiddle)

end Complexity
