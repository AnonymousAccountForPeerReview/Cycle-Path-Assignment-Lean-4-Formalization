module

public import Hardness.APX.Main
public import Hardness.MaxSNP.Hard.Main

/-!
# The final theorems about MAX-3-SAT

For the problem `max3SAT` of `Complexity.Approx.Defs` (assignments are words no longer than
the instance):

* `max3SAT_maxSNPComplete`: MAX-3-SAT is MaxSNP-complete (ANONYMIZED–ANONYMIZED).
* `max3SAT_inAPX` (`Hardness.APX.Membership`): MAX-3-SAT is in APX.
* `max3SAT_apxComplete_of_witnessGap`: MAX-3-SAT is APX-complete, given the PCP theorem in
  its witness-recovering gap form (`WitnessGap`, with a positive gap).
* `apxHard_of_lReducible_max3SAT`: every problem to which MAX-3-SAT is L-reducible is
  APX-hard, under the same hypothesis.

The reductions are proved for the auxiliary problem `max3SATu` of `Hardness.Unbounded`, in
which every word is an assignment (`max3SATu_maxSNPHard`,
`max3SATu_strongAPXHard_of_witnessGap`), and transferred along the two L-reductions between
`max3SATu` and `max3SAT` (`lReducible_max3SATu_max3SAT`, `lReducible_max3SAT_max3SATu`);
membership in MaxSNP is `max3SAT_inMaxSNP` (`Hardness.APX.Membership`).
-/

@[expose] public section

namespace Complexity

/-- MAX-3-SAT is MaxSNP-hard. -/
theorem max3SAT_maxSNPHard : MaxSNPHard max3SAT :=
  MaxSNPHard.of_lReducible max3SATu_maxSNPHard lReducible_max3SATu_max3SAT

/-- MAX-3-SAT is MaxSNP-complete. -/
theorem max3SAT_maxSNPComplete : MaxSNPComplete max3SAT :=
  ⟨max3SAT_inMaxSNP, max3SAT_maxSNPHard⟩

/-- APX-hardness of MAX-3-SAT from the witness-recovering gap theorem (hypothesis for now). -/
theorem max3SAT_apxComplete_of_witnessGap {num den : Nat} (hnum : 0 < num)
    (h : WitnessGap num den) : APXComplete max3SAT :=
  ⟨max3SAT_inAPX, max3SAT_apxHard_of_witnessGap hnum h⟩

/-- Any problem to which MAX-3-SAT L-reduces is APX-hard, given the witness gap. -/
theorem apxHard_of_lReducible_max3SAT {num den : Nat} (hnum : 0 < num)
    (h : WitnessGap num den) {Q : OptProblem} (hL : LReducible max3SAT Q) : APXHard Q :=
  APXHard.of_lReducible_max (max3SAT_strongAPXHard_of_witnessGap hnum h) hL

end Complexity
