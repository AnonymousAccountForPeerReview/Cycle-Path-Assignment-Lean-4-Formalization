module

public import Hardness.APX.Reduction
public import Hardness.APX.Uniform
public import Hardness.APX.Membership

/-!
# MAX-3-SAT is APX-hard

Assuming the PCP theorem in its witness-recovering gap form (`WitnessGap`, with a positive
gap), every problem of APX is PTAS-reducible to MAX-3-SAT
(ANONYMIZED–ANONYMIZED–ANONYMIZED–ANONYMIZED, ANONYMIZED–ANONYMIZED; ANONYMIZED et al., *Complexity and
Approximation*, Theorem 8.6):

* `max3SAT_apxHard_of_witnessGap : APXHard max3SAT`, and the strong (jointly polynomial-time)
  form `max3SAT_strongAPXHard_of_witnessGap`, which composes with L-reductions
  (`StrongAPXHard.of_lReducible`, `APXHard.of_lReducible_max`);
* the same for the auxiliary problem `max3SATu` of `Hardness.Unbounded`, in which every word
  is an assignment (`max3SATu_apxHard_of_witnessGap`, `max3SATu_strongAPXHard_of_witnessGap`,
  `apxHard_of_lReducible_max3SATu`); the reduction is built for `max3SATu` and transferred.

With `max3SAT_inAPX` (`Hardness.APX.Membership`) this gives APX-completeness of MAX-3-SAT:
see `Hardness.Final.Max3SAT`.  The problem `max3SATu` is not in `NPO` as defined
(`not_npo_max3SATu`), since every word is a solution of every instance; hence
`InAPX max3SATu` and `APXComplete max3SATu` are false (`not_inAPX_max3SATu`,
`not_apxComplete_max3SATu`).
-/

@[expose] public section

namespace Complexity

/-- MAX-3-SAT with unbounded assignments is APX-hard, given witness-recovering gap reductions
with a positive gap. -/
theorem max3SATu_apxHard_of_witnessGap {num den : Nat} (hnum : 0 < num)
    (h : WitnessGap num den) : APXHard max3SATu :=
  (max3SATu_strongAPXHard_of_witnessGap hnum h).apxHard

/-- Every problem to which MAX-3-SAT with unbounded assignments is L-reducible is APX-hard,
given witness-recovering gap reductions with a positive gap. -/
theorem apxHard_of_lReducible_max3SATu {num den : Nat} (hnum : 0 < num)
    (h : WitnessGap num den) {Q : OptProblem} (hL : LReducible max3SATu Q) : APXHard Q :=
  APXHard.of_lReducible_max (max3SATu_strongAPXHard_of_witnessGap hnum h) hL

/-- MAX-3-SAT is APX-hard in the strong form, given witness-recovering gap reductions with a
positive gap. -/
theorem max3SAT_strongAPXHard_of_witnessGap {num den : Nat} (hnum : 0 < num)
    (h : WitnessGap num den) : StrongAPXHard max3SAT :=
  (max3SATu_strongAPXHard_of_witnessGap hnum h).to_max3SAT

/-- **MAX-3-SAT is APX-hard**, given witness-recovering gap reductions with a positive gap. -/
theorem max3SAT_apxHard_of_witnessGap {num den : Nat} (hnum : 0 < num)
    (h : WitnessGap num den) : APXHard max3SAT :=
  (max3SAT_strongAPXHard_of_witnessGap hnum h).apxHard

end Complexity
