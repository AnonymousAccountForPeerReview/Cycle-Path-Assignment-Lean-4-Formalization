module

public import Hardness.GapPCP
public import Hardness.Verifier.Main
public import Hardness.MaxSNP.Final
public import Hardness.MaxSNP.PTAS
public import Hardness.APX.Membership
public import Hardness.Final.Converters
public import Hardness.Final.Verifier

/-!
# The final theorems, without hypotheses

* `pcp_gap`: the PCP theorem in gap form.  `Hardness.GapPCP.pcp_gap_of_converters` applied to
  the two encoding converters of `Hardness.Final.Converters`.
* `pcp_theorem`: the PCP theorem in verifier form, `NP = PCP(O(log n), O(1))`.
  `Hardness.Verifier.Main.pcp_theorem_of` applied to `pcp_gap` and the two polynomial-time
  obligations of `Hardness.Final.Verifier`.
* `maxSNPHard_no_ptas`, `maxSNPHard_not_hasPTAS`: MaxSNP-hard problems have no polynomial-time
  approximation scheme unless `P = NP`: MAX-3-SAT L-reduces to them
  (`MaxSNPHard.max3SATu_lReducible`, from `max3SAT_inMaxSNP` in `Hardness.APX.Membership`).
-/

@[expose] public section

namespace Complexity

/-- PCP theorem, gap form. -/
theorem pcp_gap : ∃ num den : Nat, 0 < num ∧
    ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g := by
  obtain ⟨c₁, h₁, hc₁⟩ := exists_converterIn
  obtain ⟨c₂, h₂, hc₂⟩ := exists_converterOut
  exact pcp_gap_of_converters h₁ hc₁ h₂ hc₂

/-- PCP theorem, verifier form: NP = PCP(O(log n), O(1)). -/
theorem pcp_theorem (L : Language) : InNP L ↔ ∃ c q, InPCP c q L :=
  pcp_theorem_of pcp_gap polyTime_samplingVerifier polyTime_pcpChecker L

/-- MaxSNP-hard problems have no polynomial-time approximation scheme unless P = NP
(even a non-uniform family of algorithms, one for each precision, is excluded). -/
theorem maxSNPHard_no_ptas {P : OptProblem} (hP : MaxSNPHard P)
    (h : ∀ k, P.ApproximableWithin (k + 2) (k + 1)) : PEqNP :=
  no_scheme_of_lReducible_of_gap pcp_gap hP.max3SATu_lReducible h

theorem maxSNPHard_not_hasPTAS {P : OptProblem} (hP : MaxSNPHard P) (h : P.HasPTAS) : PEqNP :=
  no_hasPTAS_of_lReducible_of_gap pcp_gap hP.max3SATu_lReducible h

theorem hasPTAS_approximable {P : OptProblem} (h : P.HasPTAS) :
    ∀ k, P.ApproximableWithin (k + 2) (k + 1) :=
  h.approximable

end Complexity
