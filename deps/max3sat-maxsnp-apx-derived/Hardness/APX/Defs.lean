module

public import ComplexityExt.Approx.Defs
public import PT.Basic

/-!
# APX-hardness of MAX-3-SAT: definitions

* `WitnessGap num den`: the witness-recovering form of the PCP theorem used as a hypothesis.
* `StrongPTASReducible P Q`: PTAS-reducibility by maps that are polynomial-time jointly in the
  precision `k` (in unary) and the instance; `StrongAPXHard`.

The problem `max3SAT` of `Complexity.Approx.Defs` has assignments no longer than the instance;
the auxiliary problem `max3SATu` of `Hardness.Unbounded`, in which every word is an assignment,
is not in `NPO` as defined: see `not_npo_max3SATu` in `Hardness.APX.Membership`.
-/

@[expose] public section

namespace Complexity

open Complexity.PT

/-- Witness-recovering gap reductions with gap `num / den`: for every polynomial-time verifier
`M` and certificate bound `powerBound c e`, a polynomial-time map `g` to nonempty 3-CNF formulas
such that inputs with an accepted certificate give satisfiable formulas, and a polynomial-time
`dec` that turns any assignment (given as a word `y`) satisfying more than the fraction
`1 - num / den` of the clauses of `g x` into an accepted certificate for `x`. -/
def WitnessGap (num den : Nat) : Prop :=
  ∀ (M : Machine) (c e : Nat), PolynomialTimeMachine M →
    ∃ (g : Word → SAT.CNF) (dec : Word → Word),
      PolyTime (fun x => SAT.encode (g x)) ∧ PolyTime dec ∧
      ∀ x, SAT.IsThreeCNF (g x) ∧ g x ≠ [] ∧
        ((∃ w : Word, w.length ≤ powerBound c e x.length ∧ Accepts M (pairWords x w)) →
          SAT.Satisfiable (g x)) ∧
        ∀ y : Word,
          den * (g x).length < den * SAT.satCount (SAT.assignmentOf y) (g x) + num * (g x).length →
          (dec (pairWords x y)).length ≤ powerBound c e x.length ∧
            Accepts M (pairWords x (dec (pairWords x y)))

/-- PTAS-reducibility with uniformly polynomial-time maps: as `PTASReducible`, but the maps
`f` and `g` are polynomial-time jointly in the precision parameter `k` (a unary number) and
their word argument, and `c` is polynomial-time on unary numbers. -/
def StrongPTASReducible (P Q : OptProblem) : Prop :=
  ∃ (f g : Nat → Word → Word) (c : Nat → Nat),
    PT (fun p : Nat × Word => f p.1 p.2) ∧ PT (fun p : Nat × Word => g p.1 p.2) ∧ PT c ∧
    ∀ k x opt, P.IsOpt x opt →
      ∃ opt', Q.IsOpt (f k x) opt' ∧
        ∀ y v', Q.Sol (f k x) y v' →
          ∃ v, P.Sol x (g k (pairWords x y)) v ∧
            (Q.WithinRatio (c k + 2) (c k + 1) opt' v' → P.WithinRatio (k + 2) (k + 1) opt v)

/-- Every problem of APX is PTAS-reducible to `P` by uniformly polynomial-time maps. -/
def StrongAPXHard (P : OptProblem) : Prop :=
  ∀ Q, InAPX Q → StrongPTASReducible Q P

end Complexity
