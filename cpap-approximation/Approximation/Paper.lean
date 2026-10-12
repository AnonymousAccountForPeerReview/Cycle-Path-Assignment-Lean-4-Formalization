module

public import Approximation.Theorems

/-!
# Paper interface: Section 7 of the accompanying paper

This module restates the development in the manuscript's terms. It adds no
construction; each theorem is proved from the development.

Section 7 gives two approximation algorithms for `CPAP(G, k)`, `k ≥ 3` fixed, on the
enumerated `k`-cycles `𝒞_k` of a graph (`t = |𝒞_k|`): the greedy Algorithm 1, with the
mixed guarantee `ALG ≤ (3 + 2√2) OPT + (1 + √2)(k − 2) t` (Lemma 13, Theorem 14), and the
convex relaxation of Section 7.2 with independent randomized rounding
(`E[c(τ)] ≤ OPT + (k − 2) t / k`, Theorem 17) and its derandomization by conditional
expectation, Algorithm 2 (`c(τ) ≤ OPT + (k − 2) t / k`, Theorem 18). What is formalized is
the analysis of the two algorithms for every run (any tie-breaking), on the option lists of
the enumerated cycles of the Section 5 formalization, with the irrational constants
replaced by equivalent polynomial inequalities and the fractional solution given with a
common denominator. The polynomial-time solvability of the relaxation (Lemma 16, ANONYMIZED,
ANONYMIZED and ANONYMIZED) and the running times of the algorithms (Lemma 15 for Algorithm 1)
are formalized in the companion package `cpap-runtimes`: `STACS2027.Runtimes.Greedy.greedy_ram`
and `STACS2027.Runtimes.QPRam.relaxSolver_ram_optimal`. The latter proves an exact rational
solver using ellipsoid and KKT procedures rather than implementing the cited algorithm.
The approximation statements here use the enumerated cycles and the optimal fractional
solution supplied by those constructions.
-/

@[expose] public section
namespace STACS2027.Paper

/-! ## Section 7.1, the greedy algorithm -/

/-- "Adding a path `P` increases the covariance cost by `∑_{e ∈ P} l(e)`." -/
theorem cost_increase (ps : List (List Edge)) (p : List Edge) :
    cost (ps ++ [p]) = cost ps + (p.map (load ps)).sum :=
  cost_snoc_pathLoad ps p

/-- Algorithm 1 "processes the cycles in any fixed order and assigns each one to a path with
minimum current total load": a run of the algorithm (`GreedyRun`) chooses, for each cycle, an
option whose load-sum under the paths chosen so far is minimum, and `greedy` is such a run. -/
theorem algorithm1 (g : Graph) (k : Nat) :
    GreedyRun [] ((cycles g k).map selectedOptions) (greedy ((cycles g k).map selectedOptions)) :=
  greedy_cycles_run g k

/-- The output of Algorithm 1 is a cycle-path assignment. -/
theorem algorithm1_assignment (g : Graph) (k : Nat) :
    ValidChoices ((cycles g k).map selectedOptions) (greedy ((cycles g k).map selectedOptions)) :=
  (greedy_cycles_run g k).valid

/-- "Every assignment has total load `Q = (k − 2) t`." -/
theorem total_load_eq {g : Graph} {k : Nat} (hg : g.Nodup) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles g k).map selectedOptions) ps) :
    (g.map (load ps)).sum = (k - 2) * (cycles g k).length := by
  obtain ⟨hlen, _, hl, hs⟩ := enumerated_choices_properties hv
  rw [total_load hg hl hs, hlen]

/-- "`2 ALG + Q = ∑_e l(e)²`": the sum of squared loads of any assignment is twice its cost plus
the total load. -/
theorem sum_sq_eq {g : Graph} {k : Nat} (hg : g.Nodup) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles g k).map selectedOptions) ps) :
    (g.map fun e => load ps e * load ps e).sum = 2 * cost ps + (k - 2) * (cycles g k).length := by
  obtain ⟨hlen, hn, hl, hs⟩ := enumerated_choices_properties hv
  rw [sum_sq_load_assignment hg hn hl hs, hlen]

/-- "The greedy cost increase is no larger than the current load-sum on its path in the optimal
assignment. Current loads are at most the final greedy loads, so summing these inequalities over
all cycles gives `c(τ_greedy) ≤ ∑_e l(e) l*(e)`." -/
theorem greedy_cost_le_product {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    cost ps ≤ (g.map fun e => load ps e * load qs e).sum := by
  obtain ⟨_, _, _, hqs⟩ := enumerated_choices_properties hq
  have h := hrun.cost_le hq
  simp only [List.nil_append, cost, Nat.zero_add] at h
  rw [sum_pathLoad_eq hg ps qs hqs] at h
  exact Nat.le_trans h (Nat.le_of_eq (sum_map_congr g _ _ (fun e _ => Nat.mul_comm _ _)))

/-- "`∑_e l(e) l*(e) ≤ √(S S*)`" (Cauchy–Schwarz), squared. -/
theorem cauchy_schwarz_loads (g : Graph) (ps qs : List (List Edge)) :
    (g.map fun e => load ps e * load qs e).sum * (g.map fun e => load ps e * load qs e).sum ≤
      (g.map fun e => load ps e * load ps e).sum * (g.map fun e => load qs e * load qs e).sum :=
  cauchy_schwarz g (load ps) (load qs)

/-- **Lemma 13.** "Let `l(e)` and `l*(e)` be the edge loads of the greedy assignment and an
optimal assignment. Then `∑_e l(e)² ≤ (3 + 2√2) ∑_e l*(e)²`." With `S = ∑_e l(e)²` and
`S* = ∑_e l*(e)²`, the bound is `(S − S*)² ≤ 4 S S*` (for `S ≥ S*`, `S/S* ≤ (1 + √2)²`);
it holds against every assignment, in particular an optimal one. -/
theorem greedy_load_norm {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    ((g.map fun e => load ps e * load ps e).sum - (g.map fun e => load qs e * load qs e).sum) *
      ((g.map fun e => load ps e * load ps e).sum - (g.map fun e => load qs e * load qs e).sum) ≤
    4 * ((g.map fun e => load ps e * load ps e).sum * (g.map fun e => load qs e * load qs e).sum) :=
  greedy_sq_load_bound hg hrun hq

/-- Lemma 13 in integers: `∑_e l(e)² ≤ 6 ∑_e l*(e)²` (as `3 + 2√2 < 6`). -/
theorem greedy_load_norm_integer {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    (g.map fun e => load ps e * load ps e).sum ≤ 6 * (g.map fun e => load qs e * load qs e).sum :=
  le_six_of_quadratic (greedy_sq_load_bound hg hrun hq)

/-- **Theorem 14.** "The assignment returned by Algorithm 1 has cost
`ALG ≤ (3 + 2√2) OPT + (1 + √2)(k − 2) t`." With `Q = (k − 2) t`, `A = 2 ALG + Q` and
`B = 2 OPT + Q`, this is `A ≤ (3 + 2√2) B`, stated as `(A − B)² ≤ 4 A B`; it holds for every
run of Algorithm 1 against every assignment `qs`, in particular an optimal one. -/
theorem greedy_guarantee {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    (2 * cost ps + (k - 2) * (cycles g k).length - (2 * cost qs + (k - 2) * (cycles g k).length)) *
      (2 * cost ps + (k - 2) * (cycles g k).length - (2 * cost qs + (k - 2) * (cycles g k).length)) ≤
    4 * ((2 * cost ps + (k - 2) * (cycles g k).length) *
      (2 * cost qs + (k - 2) * (cycles g k).length)) :=
  greedy_cost_bound hg hrun hq

/-- Theorem 14 in integers: `2 ALG ≤ 12 OPT + 5 (k − 2) t`. -/
theorem greedy_guarantee_integer {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    2 * cost ps ≤ 12 * cost qs + 5 * ((k - 2) * (cycles g k).length) :=
  greedy_cost_integer_bound hg hrun hq

/-! ## Section 7.2, the relaxation and its roundings -/

/-- A fractional solution with denominator `D`: "`∑_P x_{C,P} = 1` for every cycle", one weight
per option. -/
theorem fractional_solution_iff (D : Nat) (R : List (List (List Edge) × List Nat)) :
    FractionalSolution D R ↔ 0 < D ∧ ∀ r ∈ R, r.2.length = r.1.length ∧ r.2.sum = D := Iff.rfl

/-- "`λ_e = ∑_C ∑_{P ∋ e} x_{C,P}`": `fractionalLoad R e` is `D λ_e`, the sum over the cycles of
the weight of the options containing `e`. -/
theorem fractional_load_eq (R : List (List (List Edge) × List Nat)) (e : Edge) :
    fractionalLoad R e = (R.map fun r => weightedSum (fun p => p.count e) r.1 r.2).sum := rfl

/-- "Integral feasible solutions are exactly cycle-path assignments, so the relaxed optimum
satisfies `OPT_CP ≤ OPT`": the objective of an optimal fractional solution (scaled by `2 D²`) is
at most `2 D²` times the cost of any assignment. -/
theorem relaxation_lower_bound {g : Graph} {k D : Nat} (hg : g.Nodup)
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) (hopt : OptimalFractional g D R)
    {qs : List (List Edge)} (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    relaxationObjective D R g ≤ (D : Int) * D * (2 * cost qs) := by
  have hq' : ValidChoices (R.map Prod.fst) qs := hR ▸ hq
  obtain ⟨_, hqn, _, hqs⟩ := enumerated_choices_properties hq
  have h := hopt.2 1 (integralSolution (R.map Prod.fst) qs)
    (integralSolution_fractional _ qs hq') (integralSolution_fst _ qs hq')
  rw [relaxationObjective_eq 1] at h
  have hload : (g.map (fractionalLoad (integralSolution (R.map Prod.fst) qs))) = g.map (load qs) :=
    List.map_congr_left (fun e _ => integralSolution_load _ qs hq' e)
  have hload2 : (g.map fun e => fractionalLoad (integralSolution (R.map Prod.fst) qs) e *
      fractionalLoad (integralSolution (R.map Prod.fst) qs) e) =
      g.map fun e => load qs e * load qs e :=
    List.map_congr_left (fun e _ => by rw [integralSolution_load _ qs hq' e])
  rw [hload, hload2, sum_sq_load hg qs hqn hqs] at h
  simp only [Int.natCast_one, Int.one_mul, Int.natCast_add, Int.add_sub_cancel] at h
  have h2 : ((2 * cost qs : Nat) : Int) = 2 * (cost qs : Int) := by
    rw [Int.natCast_mul]; rfl
  rw [h2] at h
  exact h

/-- **Theorem 17**. "Independent randomized rounding produces an
assignment `τ` satisfying `E[c(τ)] ≤ OPT + (k − 2) t / k`": with
`expectedCost R = D^t E[c(τ)]`, for every assignment `qs`,
`k D^t E[c(τ)] ≤ D^t (k c(qs) + (k − 2) t)`. -/
theorem rounding_guarantee {g : Graph} {k D : Nat} (hg : g.Nodup)
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) (hopt : OptimalFractional g D R)
    {qs : List (List Edge)} (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    k * expectedCost R ≤
      D ^ (cycles g k).length * (k * cost qs + (k - 2) * (cycles g k).length) :=
  randomized_rounding_cost_bound hg hR hopt hq

/-- "Before fixing a cycle `C`, the expected final cost is the weighted average, with weights
`x*_{C,P}`, of the expected costs obtained by fixing each candidate path `P`": the scaled
expected sum of squared loads satisfies the averaging identity. -/
theorem conditional_expectation_average {g : Graph} {D : Nat} {opts : List (List Edge)}
    {w : List Nat} (hn : ∀ p ∈ opts, p.Nodup) (hl : w.length = opts.length) (hw : w.sum = D)
    (ps : List (List Edge)) (R : List (List (List Edge) × List Nat)) :
    weightedSum (fun p => expectedSquares D (ps ++ [p]) R g) opts w =
      D * expectedSquares D ps ((opts, w) :: R) g :=
  average_identity_sum hn hl hw ps R

/-- "Fixing a path `P` adds `∑_{e ∈ P} μ_e` to the expected cost, up to a term independent of
`P`": scaled by `2 D²`, fixing `P` adds `2 D ∑_{e ∈ P} D μ_e + D² |P|`. -/
theorem fixing_a_path {g : Graph} (hg : g.Nodup) (D : Nat) (ps : List (List Edge))
    (R : List (List (List Edge) × List Nat)) {p : List Edge} (hp : p.Nodup)
    (hs : ∀ e ∈ p, e ∈ g) :
    expectedSquares D (ps ++ [p]) R g =
      expectedSquares D ps R g + 2 * D * meanLoadSum D ps R p + D * D * p.length :=
  expectedSquares_snoc hg D ps R hp hs

/-- Algorithm 2 "implements this choice using the greedy path rule with expected loads in place
of current integral loads": a run of Algorithm 2 (`RoundingRun`) chooses, for each cycle in
order, an option of minimum `∑_{e ∈ P} μ_e`, and `conditionalRounding` is such a run. -/
theorem algorithm2 {g : Graph} {k : Nat} (D : Nat) {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) :
    RoundingRun D [] R (conditionalRounding D R) :=
  conditionalRounding_cycles_run hR

/-- The output of Algorithm 2 is a cycle-path assignment. -/
theorem algorithm2_assignment {g : Graph} {k : Nat} (D : Nat)
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) :
    ValidChoices ((cycles g k).map selectedOptions) (conditionalRounding D R) :=
  (conditionalRounding_cycles_run hR).valid_cycles hR

/-- **Theorem 18**. "Algorithm 2 returns a deterministic assignment
`τ` with `c(τ) ≤ OPT + (k − 2) t / k`": for every run `ps` of Algorithm 2 and every
assignment `qs`, `k c(ps) ≤ k c(qs) + (k − 2) t`. -/
theorem derandomized_guarantee {g : Graph} {k D : Nat} (hg : g.Nodup)
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) (hopt : OptimalFractional g D R)
    {ps qs : List (List Edge)} (hrun : RoundingRun D [] R ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    k * cost ps ≤ k * cost qs + (k - 2) * (cycles g k).length :=
  conditional_rounding_cost_bound hg hR hopt hrun hq

end STACS2027.Paper
