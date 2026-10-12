module

public import Approximation.Weighted
public import Approximation.Greedy

/-!
The convex relaxation of Section 7.2 and its roundings. A fractional solution
is given with a common denominator `D`: for each cycle, its option list and the
weights `x_{C,P} · D ∈ ℕ` of its options, summing to `D`. Independent
randomized rounding (Theorem 17) picks each cycle's path with probability
`x_{C,P}`; Algorithm 2 derandomizes it by conditional expectation, choosing for
each cycle in turn a path of minimum expected load-sum (Theorem 18).
-/

@[expose] public section
namespace STACS2027

/-- `D · p_{C,e}`: the weight, among the options of a cycle, of those containing the edge `e`
(`D` times the probability that the cycle's rounded path contains `e`). -/
def optionLoad (opts : List (List Edge)) (w : List Nat) (e : Edge) : Nat :=
  weightedSum (fun p => p.count e) opts w

/-- `D · ∑_{C} p_{C,e}` over the cycles of `R` (with their weights): `D λ_e` restricted to the
cycles of `R`, the scaled expected load on `e` from their independent rounding. -/
def fractionalLoad (R : List (List (List Edge) × List Nat)) (e : Edge) : Nat :=
  (R.map fun r => optionLoad r.1 r.2 e).sum

/-- `D μ_e` in Algorithm 2 after the current cycle's contribution has been subtracted: the load
of the fixed paths `ps` plus the expected load of the cycles `R` still to be rounded, scaled by
`D`. -/
def meanLoad (D : Nat) (ps : List (List Edge)) (R : List (List (List Edge) × List Nat))
    (e : Edge) : Nat :=
  D * load ps e + fractionalLoad R e

/-- `D ∑_{e ∈ P} μ_e`: Algorithm 2's objective for the candidate path `P`. -/
def meanLoadSum (D : Nat) (ps : List (List Edge)) (R : List (List (List Edge) × List Nat))
    (p : List Edge) : Nat :=
  (p.map (meanLoad D ps R)).sum

/-- `D² ∑_{C ∈ R} p_{C,e}(1 − p_{C,e})`: the scaled variance of the load on `e` from the
independent rounding of the cycles of `R`. -/
def varianceLoad (D : Nat) (R : List (List (List Edge) × List Nat)) (e : Edge) : Nat :=
  (R.map fun r => optionLoad r.1 r.2 e * (D - optionLoad r.1 r.2 e)).sum

/-- `D² ∑_e E[l(e)²]` over the edges `es`: the scaled expected sum of squared loads when the
paths `ps` are fixed and the cycles of `R` are rounded independently with their weights
(`E[l(e)²] = E[l(e)]² + Var[l(e)]`). -/
def expectedSquares (D : Nat) (ps : List (List Edge)) (R : List (List (List Edge) × List Nat))
    (es : List Edge) : Nat :=
  (es.map fun e => meanLoad D ps R e * meanLoad D ps R e + varianceLoad D R e).sum

/-- Algorithm 2 continued after the paths `acc` have been fixed: for each remaining cycle, in
order, a path of minimum expected load-sum (`∑_{e ∈ P} μ_e`, with the current cycle's own
contribution removed) is fixed. -/
def roundFrom (D : Nat) (acc : List (List Edge)) :
    List (List (List Edge) × List Nat) → List (List Edge)
  | [] => []
  | (opts, _) :: R =>
    chooseMin (meanLoadSum D acc R) opts ::
      roundFrom D (acc ++ [chooseMin (meanLoadSum D acc R) opts]) R

/-- Algorithm 2 (deterministic rounding by conditional expectation) on the fractional solution
`R` with denominator `D`, breaking ties by position. -/
def conditionalRounding (D : Nat) (R : List (List (List Edge) × List Nat)) : List (List Edge) :=
  roundFrom D [] R

/-- `RoundingRun D acc R chosen`: `chosen` is a possible output of Algorithm 2 on the cycles of
`R` after the paths `acc` have been fixed: each path is an option of its cycle of minimum
expected load-sum with respect to the paths fixed before it and the cycles after it (ties broken
arbitrarily). -/
def RoundingRun (D : Nat) :
    List (List Edge) → List (List (List Edge) × List Nat) → List (List Edge) → Prop
  | _, [], [] => True
  | _, [], _ :: _ => False
  | _, _ :: _, [] => False
  | acc, (opts, _) :: R, p :: ps =>
    p ∈ opts ∧ (∀ q ∈ opts, meanLoadSum D acc R p ≤ meanLoadSum D acc R q) ∧
      RoundingRun D (acc ++ [p]) R ps

/-- `D^{|R|}` times the expectation of `f` at the final assignment, when the paths `acc` are
fixed and each cycle of `R` independently receives one of its options with the probability given
by its weights: `∑_{P₁, …, P_t} (∏ᵢ x_{Cᵢ,Pᵢ} D) f(acc ++ [P₁, …, P_t])`. -/
def rounded (f : List (List Edge) → Nat) (acc : List (List Edge)) :
    List (List (List Edge) × List Nat) → Nat
  | [] => f acc
  | (opts, w) :: R => weightedSum (fun p => rounded f (acc ++ [p]) R) opts w

/-- `D^t E[c(τ)]`: `D^t` times the expected cost of independent randomized rounding of the
fractional solution `R` with denominator `D`. -/
def expectedCost (R : List (List (List Edge) × List Nat)) : Nat :=
  rounded cost [] R

/-- `R` is a fractional solution of the relaxation with denominator `D`: for every cycle, one
weight per option, summing to `D` (the constraint `∑_P x_{C,P} = 1`). -/
def FractionalSolution (D : Nat) (R : List (List (List Edge) × List Nat)) : Prop :=
  0 < D ∧ ∀ r ∈ R, r.2.length = r.1.length ∧ r.2.sum = D

/-- `2 D²` times the objective `∑_e (λ_e² − λ_e)/2` of the relaxation at the fractional solution
`R` with denominator `D`, over the edges `es`. -/
def relaxationObjective (D : Nat) (R : List (List (List Edge) × List Nat)) (es : List Edge) :
    Int :=
  (es.map fun e =>
    ((fractionalLoad R e : Nat) : Int) * fractionalLoad R e - (D : Int) * fractionalLoad R e).sum

/-- `R` with denominator `D` is an optimal fractional solution: no fractional solution `R'` of the
same instance (the same option lists), with any denominator `D'`, has a smaller objective; the
objectives are compared after clearing the denominators. -/
def OptimalFractional (es : List Edge) (D : Nat) (R : List (List (List Edge) × List Nat)) : Prop :=
  FractionalSolution D R ∧
    ∀ (D' : Nat) (R' : List (List (List Edge) × List Nat)), FractionalSolution D' R' →
      R'.map Prod.fst = R.map Prod.fst →
      (D' : Int) * D' * relaxationObjective D R es ≤ (D : Int) * D * relaxationObjective D' R' es

/-- The cycle-path assignment `ps` of the option lists `options` as a fractional solution with
denominator `1`: each cycle gives its chosen path the whole weight. -/
def integralSolution :
    List (List (List Edge)) → List (List Edge) → List (List (List Edge) × List Nat)
  | [], _ => []
  | _ :: _, [] => []
  | opts :: options, p :: ps => (opts, unitWeights opts p) :: integralSolution options ps

end STACS2027
