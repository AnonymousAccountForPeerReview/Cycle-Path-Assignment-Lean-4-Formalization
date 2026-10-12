module

public import Hardness.MaxSNP.Main
import Lean.Elab.Tactic.Omega

/-!
# The statement for polynomial-time approximation schemes

A polynomial-time approximation scheme (`OptProblem.HasPTAS`) gives, for every fixed `k`, a
polynomial-time approximation algorithm with ratio `1 + 1 / (k + 1)`: the precision is
hard-wired by composing the uniform machine with `x ↦ pairWords (unary k) x`. Hence the
theorems of `Hardness.MaxSNP.Main` apply to problems with a PTAS.

Throughout this file MAX-3-SAT is the auxiliary problem `max3SATu` of `Hardness.Unbounded`, in
which every word is an assignment; the results are transferred to `max3SAT` (assignments no
longer than the instance) in `Hardness.Final.Max3SAT`.
-/

@[expose] public section

namespace Complexity

open Complexity.Reg

set_option backward.isDefEq.respectTransparency false in
/-- Every section `F k` of a uniformly polynomial-time family is polynomial-time. -/
theorem UniformPolyTime.polyTime {F : Nat → Word → Word} (hF : UniformPolyTime F) (k : Nat) :
    PolyTime (F k) := by
  obtain ⟨M, hM⟩ := hF
  obtain ⟨d, l, hM⟩ := hM k
  have hf : PolyTime (fun x : Word => pairWords (unary k) x) :=
    polyTime_pair (polyTime_const _) polyTime_id
  obtain ⟨first, c, e, hf⟩ := hf
  refine StackCompile.polyTime_of_stack (TapeToStacks.compositionMachine first M)
    (fun n => 72 * (n + powerBound c e n + powerBound d l n + 1))
    ((PolynomialBound.constant 72).mul
      (((PolynomialBound.identity.add (PolynomialBound.power c e)).add
        (PolynomialBound.power d l)).add (PolynomialBound.constant 1))) ?_
  intro input
  obtain ⟨t, middle, ht, hfirst, hmiddle⟩ := hf input
  obtain ⟨s, out, hs, hsecond, hout⟩ := hM input
  have hmiddle' : middle.output = pairWords (unary k) input := hmiddle
  rw [← hmiddle'] at hsecond
  obtain ⟨time, htime, hrun⟩ :=
    TapeToStacks.run_compositionMachine first M t s input middle out hfirst hsecond
  refine ⟨time, TapeToStacks.regs out.output [] [], ?_, hrun, ?_⟩
  · show time ≤ 72 * (input.length + powerBound c e input.length +
      powerBound d l input.length + 1)
    omega
  · rw [TapeToStacks.regs_zero]
    exact hout

/-- A polynomial-time approximation scheme gives polynomial-time approximation algorithms of
every ratio `1 + 1 / (k + 1)`. -/
theorem OptProblem.HasPTAS.approximable {P : OptProblem} (h : P.HasPTAS) :
    ∀ k, P.ApproximableWithin (k + 2) (k + 1) := by
  obtain ⟨A, hA, hA'⟩ := h
  exact fun k => ⟨A k, hA.polyTime k, hA' k⟩

/-- **MAX-3-SAT has no polynomial-time approximation scheme unless P = NP**, from the gap form
of the PCP theorem. -/
theorem max3SATu_not_hasPTAS_of_gap (ob : Obligations)
    (hgap : ∃ num den : Nat, 0 < num ∧
      ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g)
    (h : max3SATu.HasPTAS) : PEqNP :=
  max3SATu_not_approximable_of_gap ob hgap h.approximable

/-- **Problems to which MAX-3-SAT L-reduces have no polynomial-time approximation scheme
unless P = NP**, from the gap form of the PCP theorem. -/
theorem not_hasPTAS_of_lReducible_of_gap (ob : Obligations)
    (hgap : ∃ num den : Nat, 0 < num ∧
      ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g)
    {P : OptProblem} (hP : LReducible max3SATu P) (h : P.HasPTAS) : PEqNP :=
  no_ptas_of_lReducible_of_gap ob hgap hP h.approximable

end Complexity
