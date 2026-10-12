module

public import ApproximationHardness.Hardness.Reduction
public import Hardness.Occ.Main
public import Hardness.Final.Main
public import Hardness.Final.Max3SAT
public import Hardness.Witness.Main

/-!
# Theorem 11 and Corollary 12

With the L-reduction `Hardness.lReducible_max3SAT3_cpap` from 3-OCCURRENCE MAX-3-SAT to
`CPAP(·, k)`, the results of the MaxSNP-completeness formalization (Max3SAT-MaxSNP-APX-Lean4)
give, for every `k ≥ 5`:

* **Theorem 11**: `CPAP(·, k)` is MaxSNP-hard (`cpap_maxSNPHard`: every problem of MaxSNP — an
  NPO problem L-reducible to a problem of the syntactic class MaxSNP₀ for fixed input and
  solution signatures — L-reduces to it; from `max3SAT3_maxSNPHard`, ANONYMIZED–ANONYMIZED)
  and APX-hard
  (`cpap_apxHard`: every problem of APX PTAS-reduces to it; from the witness-recovering PCP gap
  theorem `witnessGap` and `apxHard_of_lReducible_max3SAT`, through MAX-3-SAT, which L-reduces
  to 3-OCCURRENCE MAX-3-SAT by `lReducible_max3SAT_max3SAT3`);
* **Corollary 12**: unless `P = NP`, `CPAP(·, k)` has no PTAS (`cpap_no_ptas`), and not even a
  family of polynomial-time algorithms achieving every ratio `1 + 1/(j+1)`
  (`cpap_not_approximable`); from the PCP theorem (`maxSNPHard_not_hasPTAS`,
  `maxSNPHard_no_ptas`).
-/

@[expose] public section

namespace STACS2027

open Complexity

/-- **Theorem 11** (L-reduction): for every `k ≥ 5`, 3-OCCURRENCE MAX-3-SAT L-reduces to
`CPAP(·, k)`. -/
theorem max3SAT3_lReducible_cpap {k : Nat} (hk : 5 ≤ k) : LReducible max3SAT3 (cpapProblem k) :=
  Hardness.lReducible_max3SAT3_cpap hk

/-- **Theorem 11** (MaxSNP-hardness): for every `k ≥ 5`, `CPAP(·, k)` is MaxSNP-hard. -/
theorem cpap_maxSNPHard {k : Nat} (hk : 5 ≤ k) : MaxSNPHard (cpapProblem k) :=
  MaxSNPHard.of_lReducible max3SAT3_maxSNPHard (max3SAT3_lReducible_cpap hk)

/-- **Theorem 11** (APX-hardness): for every `k ≥ 5`, `CPAP(·, k)` is APX-hard. -/
theorem cpap_apxHard {k : Nat} (hk : 5 ≤ k) : APXHard (cpapProblem k) := by
  obtain ⟨num, den, hnum, h⟩ := witnessGap
  exact apxHard_of_lReducible_max3SAT hnum h
    (lReducible_max3SAT_max3SAT3.trans (max3SAT3_lReducible_cpap hk))

/-- **Corollary 12**: for every `k ≥ 5`, if `CPAP(·, k)` has a polynomial-time approximation
scheme then `P = NP`. -/
theorem cpap_no_ptas {k : Nat} (hk : 5 ≤ k) (h : (cpapProblem k).HasPTAS) : PEqNP :=
  maxSNPHard_not_hasPTAS (cpap_maxSNPHard hk) h

/-- **Corollary 12**, non-uniform form: for every `k ≥ 5`, if for every `j` some polynomial-time
algorithm approximates `CPAP(·, k)` within the ratio `1 + 1/(j+1)`, then `P = NP`. -/
theorem cpap_not_approximable {k : Nat} (hk : 5 ≤ k)
    (h : ∀ j, (cpapProblem k).ApproximableWithin (j + 2) (j + 1)) : PEqNP :=
  maxSNPHard_no_ptas (cpap_maxSNPHard hk) h

end STACS2027
