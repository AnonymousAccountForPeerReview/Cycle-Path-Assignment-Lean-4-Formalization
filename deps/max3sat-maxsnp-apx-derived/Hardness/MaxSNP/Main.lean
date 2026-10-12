module

public import Hardness.MaxSNP.Max3SAT
public import PT.ListBasic

/-!
# MaxSNP-hard problems have no approximation scheme unless P = NP

Assuming the PCP theorem in its gap form (every language of NP has a gap reduction to 3-SAT,
`GapReduction`), a family of polynomial-time approximation algorithms for MAX-3-SAT with
ratios `1 + 1 / (k + 1)` decides every language of NP in polynomial time
(`max3SATu_not_approximable_of_gap`). L-reductions transfer such families backwards, so the
same holds for every problem to which MAX-3-SAT L-reduces (`no_ptas_of_lReducible_of_gap`), in
particular, since MAX-3-SAT is in MaxSNP, for every MaxSNP-hard problem
(`maxSNPHard_no_ptas`, in `Hardness.Final.Main`).

The polynomial-time facts about the explicit list programs involved are collected in
`Obligations` (`Hardness.MaxSNP.Defs`).

Throughout this file MAX-3-SAT is the auxiliary problem `max3SATu` of `Hardness.Unbounded`, in
which every word is an assignment; the results are transferred to `max3SAT` (assignments no
longer than the instance) in `Hardness.Final.Max3SAT`.
-/

@[expose] public section

namespace Complexity

open Complexity.PT Complexity.Reg

/-! ### Optima of MAX-3-SAT -/

/-- Every 3-CNF formula has an optimum as an instance of MAX-3-SAT. -/
theorem max3SATu_exists_opt {f : SAT.CNF} (h3 : SAT.IsThreeCNF f) :
    ∃ opt, max3SATu.IsOpt (SAT.encode f) opt := by
  refine OptProblem.exists_isOpt_of_bounded rfl f.length
    ⟨[], _, max3SATu_sol_encode.mpr ⟨h3, rfl⟩⟩ ?_
  intro y v h
  obtain ⟨-, rfl⟩ := max3SATu_sol_encode.mp h
  exact SAT.satCount_le_length _ f

/-- A satisfying assignment satisfies every clause. -/
theorem SAT.satCount_eq_length {a : SAT.Assignment} {f : SAT.CNF}
    (h : SAT.evalCNF a f = true) : SAT.satCount a f = f.length :=
  List.countP_eq_length.mpr (List.all_eq_true.mp h)

/-- The optimum of a satisfiable 3-CNF formula is its number of clauses. -/
theorem max3SATu_isOpt_of_satisfiable {f : SAT.CNF} (h3 : SAT.IsThreeCNF f)
    (hs : SAT.Satisfiable f) : max3SATu.IsOpt (SAT.encode f) f.length := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨y, hy⟩ := SAT.exists_word_assignment a f
  refine ⟨⟨y, max3SATu_sol_encode.mpr ⟨h3, ?_⟩⟩, fun y' v' h' => ⟨fun _ => ?_, fun hmin => ?_⟩⟩
  · rw [SAT.satCount_congr hy, SAT.satCount_eq_length ha]
  · obtain ⟨-, rfl⟩ := max3SATu_sol_encode.mp h'
    exact SAT.satCount_le_length _ f
  · cases hmin

/-- The arithmetic of the gap: an assignment within the factor `1 + 1 / (den + 1)` of a
satisfiable formula with `m > 0` clauses leaves fewer than the fraction `num / den` of the
clauses unsatisfied. -/
theorem gap_arith {num den m v : Nat} (hnum : 0 < num) (hm : 0 < m) (hv : v ≤ m)
    (hr : (den + 1) * m ≤ (den + 2) * v) : den * m < den * v + num * m := by
  have h1 : m ≤ num * m := Nat.le_mul_of_pos_left m hnum
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at hr
  rcases Nat.lt_or_eq_of_le hv with hlt | rfl
  · omega
  · omega

/-! ### No approximation scheme for MAX-3-SAT -/

/-- Given gap reductions with a fixed gap for all of NP, polynomial-time approximation
algorithms for MAX-3-SAT with ratios `1 + 1 / (k + 1)`, for every `k`, give `P = NP`. The only
obligation used is that counting satisfied clauses is polynomial-time. -/
theorem max3SATu_not_approximable_of_gap_of
    (hsc : PT (fun p : Word × SAT.CNF => SAT.satCount (SAT.assignmentOf p.1) p.2))
    (hgap : ∃ num den : Nat, 0 < num ∧
      ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g)
    (h : ∀ k, max3SATu.ApproximableWithin (k + 2) (k + 1)) : PEqNP := by
  obtain ⟨num, den, hnum, hgap⟩ := hgap
  intro L hL
  obtain ⟨g, hg, hg'⟩ := hgap L hL
  obtain ⟨A, hA, hA'⟩ := h den
  have hgPT : PT g := PT.of_polyTime_enc hg
  have hAPT : PT A := PT.of_polyTime hA
  have hlen : PT (fun x : Word => (g x).length) := PT.length hgPT
  have hval : PT (fun x : Word =>
      SAT.satCount (SAT.assignmentOf (A (SAT.encode (g x)))) (g x)) :=
    hsc.comp (PT.pair (hAPT.comp (PT.enc hgPT)) hgPT)
  refine PT.inP (f := fun x => decide (den * (g x).length <
      den * SAT.satCount (SAT.assignmentOf (A (SAT.encode (g x)))) (g x) +
        num * (g x).length))
    (PT.natLt (PT.mul (PT.const den) hlen)
      (PT.add (PT.mul (PT.const den) hval) (PT.mul (PT.const num) hlen))) fun x => ?_
  obtain ⟨h3, hne, hyes, hno⟩ := hg' x
  rw [decide_eq_true_eq]
  constructor
  · intro hx
    have hopt := max3SATu_isOpt_of_satisfiable h3 (hyes hx)
    obtain ⟨v, hsol, hr⟩ := hA' _ _ hopt
    obtain ⟨-, rfl⟩ := max3SATu_sol_encode.mp hsol
    exact gap_arith hnum (List.length_pos_iff.mpr hne) (SAT.satCount_le_length _ _) (hr.1 rfl)
  · intro hlt
    refine Classical.byContradiction fun hx => ?_
    have := hno hx (SAT.assignmentOf (A (SAT.encode (g x))))
    omega

/-- **No approximation scheme for MAX-3-SAT unless P = NP**, from the gap form of the PCP
theorem. -/
theorem max3SATu_not_approximable_of_gap (ob : Obligations)
    (hgap : ∃ num den : Nat, 0 < num ∧
      ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g)
    (h : ∀ k, max3SATu.ApproximableWithin (k + 2) (k + 1)) : PEqNP :=
  max3SATu_not_approximable_of_gap_of ob.satCount hgap h

/-- **Problems to which MAX-3-SAT L-reduces have no approximation scheme unless P = NP**,
from the gap form of the PCP theorem: such a problem with polynomial-time approximation
algorithms of ratio `1 + 1 / (k + 1)` for every `k` gives `P = NP`. -/
theorem no_ptas_of_lReducible_of_gap (ob : Obligations)
    (hgap : ∃ num den : Nat, 0 < num ∧
      ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g)
    {P : OptProblem} (hP : LReducible max3SATu P)
    (h : ∀ k, P.ApproximableWithin (k + 2) (k + 1)) : PEqNP :=
  max3SATu_not_approximable_of_gap ob hgap (hP.approximable h)

end Complexity
