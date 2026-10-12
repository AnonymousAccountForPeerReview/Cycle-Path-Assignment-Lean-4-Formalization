module

public import Hardness.Verifier.Sampling
public import Hardness.Verifier.Checker

/-!
# The PCP theorem in verifier form, from its gap form

`pcp_theorem_of` derives `InNP L ↔ ∃ c q, InPCP c q L` from

* `hgap`: the gap form of the PCP theorem (a gap reduction to 3-SAT for every NP language,
  with a uniform gap `num / den`, `0 < num`);
* `hsample`: polynomial-time computability of the clause-sampling verifiers
  `samplingVerifier g k B` of polynomial-time `g`;
* `hcheck`: polynomial-time computability of the exhaustive checkers `pcpChecker V c` of
  polynomial-time `V`.

The last two concern explicitly defined list programs and carry no mathematical content
beyond running time; the counting and soundness arguments are proved in
`Hardness.Verifier.Sampling` and `Hardness.Verifier.Checker`.
-/

@[expose] public section

namespace Complexity

/-- PCP ⊆ NP, given that the exhaustive checkers are polynomial-time computable. -/
theorem inNP_of_inPCP {c q : Nat} {L : Language} (h : InPCP c q L)
    (hcheck : ∀ V : Word → SAT.CNF, PolyTime (fun w => SAT.encode (V w)) →
      PolyTime (pcpChecker V c)) : InNP L := by
  obtain ⟨V, hV, hspec⟩ := h
  exact inNP_of_inPCP_checker hV hspec (hcheck V hV)

/-- NP ⊆ PCP with `3 * (2 * den)` queries, from gap reductions with gap `num / den`. -/
theorem exists_inPCP_of_inNP {num den : Nat} (hnum : 0 < num)
    (hgap : ∀ L, InNP L → ∃ g, GapReduction num den L g)
    (hsample : ∀ (g : Word → SAT.CNF) (k B : Nat), PolyTime (fun x => SAT.encode (g x)) →
        PolyTime (fun w => SAT.encode (samplingVerifier g k B w)))
    {L : Language} (hL : InNP L) : ∃ c, InPCP c (3 * (2 * den)) L := by
  obtain ⟨g, hg⟩ := hgap L hL
  obtain ⟨B, hB⟩ := exists_blockExponent_of_polyTime hg.1
  exact ⟨_, inPCP_of_gapReduction hnum hg B hB (hsample g (2 * den) B hg.1)⟩

/-- **The PCP theorem in verifier form**, `NP = PCP(O(log n), O(1))`, derived from its gap
form, modulo the polynomial-time computability of the two explicitly defined families
`samplingVerifier` and `pcpChecker`. -/
theorem pcp_theorem_of
    (hgap : ∃ num den, 0 < num ∧ ∀ L, InNP L → ∃ g, GapReduction num den L g)
    (hsample : ∀ (g : Word → SAT.CNF) (k B : Nat), PolyTime (fun x => SAT.encode (g x)) →
        PolyTime (fun w => SAT.encode (samplingVerifier g k B w)))
    (hcheck : ∀ (V : Word → SAT.CNF) (c : Nat), PolyTime (fun w => SAT.encode (V w)) →
        PolyTime (pcpChecker V c)) (L : Language) :
    InNP L ↔ ∃ c q, InPCP c q L := by
  constructor
  · intro hL
    obtain ⟨num, den, hnum, hgap⟩ := hgap
    obtain ⟨c, hc⟩ := exists_inPCP_of_inNP hnum hgap hsample hL
    exact ⟨c, _, hc⟩
  · rintro ⟨c, q, h⟩
    exact inNP_of_inPCP h (fun V hV => hcheck V c hV)

end Complexity
