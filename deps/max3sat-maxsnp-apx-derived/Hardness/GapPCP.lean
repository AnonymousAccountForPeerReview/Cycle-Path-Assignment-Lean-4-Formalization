module

public import Hardness.PolyTimeOn
public import Hardness.Formula
public import ComplexityExt.Witness.Main
public import Bridge.TM2
public import OAI.Computability.UniqueGames.PCP.GapTheorem

/-!
# The PCP theorem in gap form, modulo two encoding converters

For every language `L` in NP the reduction is

`x ↦ ofOAI (gap (toOAI (g₀ x)))`,

where `g₀` is the ANONYMIZED–ANONYMIZED 3-CNF map of `Complexity.Witness.Main` and `gap` is the vendored
gap-amplification map (`OAI.…PCP.GapTheorem.exists_gapMap`). Its code is computed as

`x ↦ c₂ (G (c₁ (SAT.encode (g₀ x))))`,

where `G` is the word function of the Boolean-stack machine that `Bridge.stack_of_tm2` extracts
from the vendored multi-stack machine, and `c₁`, `c₂` are polynomial-time converters between the
project's code `SAT.encode` and the vendored serialisation `formulaBits`
(`ConvertsIn`, `ConvertsOut` of `Hardness.Formula`). The converters are hypotheses of
`pcp_gap_of_converters`.
-/

@[expose] public section

namespace Complexity

open OAI.UniqueGamesTheorem
open Foundations.Target (Formula)
open Foundations.Complexity (formulaBits)

/-- ANONYMIZED–ANONYMIZED for 3-SAT as a map to formulas, with both directions: every NP language has a
polynomial-time map `g` to 3-CNF formulas with `x ∈ L ↔ g x` satisfiable. -/
theorem InNP.exists_threeCNF {L : Language} (hL : InNP L) :
    ∃ g : Word → SAT.CNF, PolyTime (fun x => SAT.encode (g x)) ∧
      (∀ x, SAT.IsThreeCNF (g x)) ∧ ∀ x, L x ↔ SAT.Satisfiable (g x) := by
  obtain ⟨M, wc, wk, rc, rk, -, hchar, hpoly, h3, hcomplete, hsound⟩ :=
    hL.threeSAT_witness_explicit
  refine ⟨Witness.threeCNF M wc wk rc rk, hpoly, h3, fun x => ⟨hcomplete x, ?_⟩⟩
  rintro ⟨a, ha⟩
  exact (hchar x).mpr ⟨_, hsound x a ha⟩

/-- A polynomial-time multi-stack machine on serialised formulas, as a Boolean-stack machine
together with the word function `G` it computes on the serialisations. -/
theorem exists_stack_of_formulaMachine (gap : Formula → Formula)
    (machine : Turing.TM2ComputableInPolyTime formulaBits formulaBits gap)
    (hfin : ∀ k, Finite (machine.tm.Γ k)) :
    ∃ (S : StackMachine.Machine) (bound : Nat → Nat) (G : Word → Word),
      PolynomialBound bound ∧
      (∀ F, G (formulaBits F) = formulaBits (gap F)) ∧
      ∀ w, (∃ F, formulaBits F = w) → ∃ time registers, time ≤ bound w.length ∧
        StackMachine.runInput S time w = some (true, registers) ∧ registers 0 = G w := by
  classical
  obtain ⟨S, bound, hbound, hS⟩ := Bridge.stack_of_tm2 machine hfin
  let G : Word → Word := fun w =>
    if h : ∃ F, formulaBits F = w then formulaBits (gap (Classical.choose h)) else []
  have hG : ∀ F, G (formulaBits F) = formulaBits (gap F) := by
    intro F
    have h : ∃ F', formulaBits F' = formulaBits F := ⟨F, rfl⟩
    have hGF : G (formulaBits F) = formulaBits (gap (Classical.choose h)) := by
      simp only [G, h, ↓reduceDIte]
    obtain ⟨t, r, -, hrun, hr⟩ := hS F
    obtain ⟨t', r', -, hrun', hr'⟩ := hS (Classical.choose h)
    rw [Classical.choose_spec h] at hrun'
    have heq := StackMachine.run_deterministic S _ hrun hrun'
    have hreg : r = r' := congrArg Prod.snd heq
    rw [hGF, ← hr', ← hr, hreg]
  refine ⟨S, bound, G, hbound, hG, ?_⟩
  rintro w ⟨F, rfl⟩
  obtain ⟨t, r, ht, hrun, hr⟩ := hS F
  exact ⟨t, r, ht, hrun, hr.trans (hG F).symm⟩

/-- The PCP theorem in gap form, given the two encoding converters: there is a constant
`den` such that every NP language has a polynomial-time map `g` to nonempty 3-CNF formulas with
`g x` satisfiable for `x ∈ L`, while for `x ∉ L` every assignment leaves at least one clause in
`den` unsatisfied. -/
theorem pcp_gap_of_converters {c₁ c₂ : Word → Word} (h₁ : PolyTime c₁) (hc₁ : ConvertsIn c₁)
    (h₂ : PolyTime c₂) (hc₂ : ConvertsOut c₂) :
    ∃ num den : Nat, 0 < num ∧
      ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g := by
  obtain ⟨gap, machine, hfin, hcomplete, hpos, hsound⟩ := Foundations.PCP.GapTheorem.exists_gapMap
  obtain ⟨S, bound, G, hbound, hG, hS⟩ := exists_stack_of_formulaMachine gap machine hfin
  refine ⟨1, Foundations.PCP.FinalConstants.walkLength * 40960, Nat.one_pos, fun L hL => ?_⟩
  obtain ⟨g₀, hg₀, h3, hiff⟩ := hL.exists_threeCNF
  refine ⟨fun x => ofOAI (gap (toOAI (g₀ x))), ?_, fun x => ⟨ofOAI_isThreeCNF _, ?_, ?_, ?_⟩⟩
  · have hin : PolyTime (fun x => c₁ (SAT.encode (g₀ x))) := polyTime_comp h₁ hg₀
    have hmid : PolyTime (fun x => G (c₁ (SAT.encode (g₀ x)))) :=
      polyTime_comp_stack_on hin (fun w => ∃ F, formulaBits F = w)
        (fun x => ⟨toOAI (g₀ x), (hc₁ (g₀ x) (h3 x)).symm⟩) S bound hbound G hS
    have hout : PolyTime (fun x => c₂ (G (c₁ (SAT.encode (g₀ x))))) := polyTime_comp h₂ hmid
    refine polyTime_congr (fun x => ?_) hout
    change c₂ (G (c₁ (SAT.encode (g₀ x)))) = SAT.encode (ofOAI (gap (toOAI (g₀ x))))
    rw [hc₁ (g₀ x) (h3 x), hG, hc₂]
  · intro hnil
    have hlen := hpos (toOAI (g₀ x))
    rw [← ofOAI_length] at hlen
    change ofOAI (gap (toOAI (g₀ x))) = [] at hnil
    rw [hnil] at hlen
    exact Nat.lt_irrefl 0 hlen
  · intro hx
    exact satisfiable_ofOAI _
      (hcomplete _ ((toOAI_satisfiable_iff (g₀ x) (h3 x)).mpr ((hiff x).mp hx)))
  · intro hx a
    have hunsat : ¬ (toOAI (g₀ x)).Satisfiable := fun hs =>
      hx ((hiff x).mpr ((toOAI_satisfiable_iff (g₀ x) (h3 x)).mp hs))
    have hgap := hsound (toOAI (g₀ x)) hunsat (fun i => a i.val)
    have hcount := satCount_ofOAI_add_failedCount (gap (toOAI (g₀ x))) a
    change _ * SAT.satCount a (ofOAI (gap (toOAI (g₀ x)))) +
      1 * (ofOAI (gap (toOAI (g₀ x)))).length ≤ _ * (ofOAI (gap (toOAI (g₀ x)))).length
    rw [ofOAI_length]
    have hmul := Nat.mul_add (Foundations.PCP.FinalConstants.walkLength * 40960)
      (SAT.satCount a (ofOAI (gap (toOAI (g₀ x)))))
      (Foundations.PCP.NameCompaction.failedCount (gap (toOAI (g₀ x))) (fun i => a i.val))
    rw [hcount] at hmul
    omega

end Complexity
