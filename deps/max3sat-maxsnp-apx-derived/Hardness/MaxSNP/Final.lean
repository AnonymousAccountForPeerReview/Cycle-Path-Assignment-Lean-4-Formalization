module

public import Hardness.MaxSNP.PTAS
public import PT.List
public import PT.ListMore

/-!
# The MaxSNP theorems without obligations

The polynomial-time obligations of `Hardness.MaxSNP.Defs` are discharged with the list library
of the `PT` framework (`obligations`), giving the unconditional forms of the theorems:

* `lReducible_max3SATu_maxSNP0_φ₃`: MAX-3-SAT L-reduces to the MaxSNP₀ problem of `φ₃`
  (membership of `max3SAT` in MaxSNP, which also needs `NPO max3SAT`, is
  `max3SAT_inMaxSNP` in `Hardness.APX.Membership`);
* `max3SATu_no_scheme_of_gap`, `no_scheme_of_lReducible_of_gap`: from the gap form of the PCP
  theorem, polynomial-time approximation algorithms of every ratio `1 + 1 / (k + 1)` for
  MAX-3-SAT, or for a problem to which MAX-3-SAT L-reduces, give `P = NP`;
* `max3SATu_no_hasPTAS_of_gap`, `no_hasPTAS_of_lReducible_of_gap`: the same for a
  polynomial-time approximation scheme (`OptProblem.HasPTAS`).

Throughout this file MAX-3-SAT is the auxiliary problem `max3SATu` of `Hardness.Unbounded`, in
which every word is an assignment; the results are transferred to `max3SAT` (assignments no
longer than the instance) in `Hardness.Final.Max3SAT`.
-/

@[expose] public section

namespace Complexity

open Complexity.PT

/-- Counting the clauses satisfied by an assignment written as a word is polynomial-time. -/
theorem pt_satCount :
    PT (fun p : Word × SAT.CNF => SAT.satCount (SAT.assignmentOf p.1) p.2) := by
  unfold SAT.satCount SAT.evalClause SAT.evalLiteral SAT.assignmentOf
  fun_prop

/-- The instance map of the L-reduction from MAX-3-SAT to `maxSNP0 ga₃ sa₃ 4 φ₃` is
polynomial-time. -/
theorem pt_sat2snp : PT sat2snp := by
  show PT (fun f : SAT.CNF =>
    ((Code.enc f : Word).length, [0, 1, 2, 3, 4, 5, 6, 7].map (snpRel f)))
  unfold snpRel clauseTuple clauseSign signCode lit3 lit2 lit1
  fun_prop

/-- The solution map of the L-reduction from MAX-3-SAT to `maxSNP0 ga₃ sa₃ 4 φ₃` is
polynomial-time. -/
theorem pt_snp2sat : PT (fun p : SAT.CNF × Relations => snp2sat p.1 p.2) := by
  show PT (fun p : SAT.CNF × Relations =>
    (List.range (Code.enc p.1 : Word).length).map fun v => p.2.holds 0 [v])
  unfold Relations.holds
  fun_prop

/-- All polynomial-time obligations of the MaxSNP theorems hold. -/
theorem obligations : Obligations :=
  ⟨pt_satCount, pt_sat2snp, pt_snp2sat⟩

/-- **MAX-3-SAT L-reduces to a MaxSNP₀ problem**, with constants `α = β = 1`: the problem of
the formula `φ₃` in four variables. -/
theorem lReducible_max3SATu_maxSNP0_φ₃ : LReducible max3SATu (maxSNP0 ga₃ sa₃ 4 φ₃) :=
  lReducible_max3SATu_maxSNP0_of obligations

/-- From the gap form of the PCP theorem: polynomial-time approximation algorithms for
MAX-3-SAT of every ratio `1 + 1 / (k + 1)` give `P = NP`. -/
theorem max3SATu_no_scheme_of_gap
    (hgap : ∃ num den : Nat, 0 < num ∧
      ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g)
    (h : ∀ k, max3SATu.ApproximableWithin (k + 2) (k + 1)) : PEqNP :=
  max3SATu_not_approximable_of_gap obligations hgap h

/-- From the gap form of the PCP theorem: polynomial-time approximation algorithms of every
ratio `1 + 1 / (k + 1)` for a problem to which MAX-3-SAT L-reduces give `P = NP`. -/
theorem no_scheme_of_lReducible_of_gap
    (hgap : ∃ num den : Nat, 0 < num ∧
      ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g)
    {P : OptProblem} (hP : LReducible max3SATu P)
    (h : ∀ k, P.ApproximableWithin (k + 2) (k + 1)) : PEqNP :=
  no_ptas_of_lReducible_of_gap obligations hgap hP h

/-- From the gap form of the PCP theorem: **MAX-3-SAT has no polynomial-time approximation
scheme unless P = NP**. -/
theorem max3SATu_no_hasPTAS_of_gap
    (hgap : ∃ num den : Nat, 0 < num ∧
      ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g)
    (h : max3SATu.HasPTAS) : PEqNP :=
  max3SATu_not_hasPTAS_of_gap obligations hgap h

/-- From the gap form of the PCP theorem: **a problem to which MAX-3-SAT L-reduces has no
polynomial-time approximation scheme unless P = NP**. -/
theorem no_hasPTAS_of_lReducible_of_gap
    (hgap : ∃ num den : Nat, 0 < num ∧
      ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g)
    {P : OptProblem} (hP : LReducible max3SATu P) (h : P.HasPTAS) : PEqNP :=
  not_hasPTAS_of_lReducible_of_gap obligations hgap hP h

end Complexity
