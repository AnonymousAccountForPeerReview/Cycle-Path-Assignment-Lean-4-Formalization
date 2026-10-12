# Paper map: Section 7 in Lean

Result numbers and appendix letters follow the accompanying paper. Section 7.1 gives the greedy analysis, Section 7.2
the relaxation and randomized rounding, and Section 7.3 the derandomization. Lean names do not carry
result numbers (`Paper.greedy_load_norm`, `Paper.greedy_guarantee`, `Paper.rounding_guarantee`,
`Paper.derandomized_guarantee` restate Lemma 13 and Theorems 14, 17 and 18). Names without a namespace are in
`STACS2027`; `Paper.x` is `STACS2027.Paper.x` in `Approximation/Paper.lean`.
Every row is a proved theorem or a definition. The seven compared theorems are
marked **(Challenge)**; this denotes the optional generated comparison specification, which is omitted from the distribution and default build. Graph-level cost bounds require a duplicate-free edge list. Throughout, `t = |𝒞_k|` is `(cycles g k).length`, the
option list of a cycle `C` (its `k` paths `𝒫_C`) is `selectedOptions C`, and an
assignment `τ` is a list `ps` with `ValidChoices ((cycles g k).map selectedOptions) ps`.

## Definitions

| Manuscript | Lean | Notes |
|---|---|---|
| Definition 1 (CPAP), `c(τ)`, `l(e)`, `OPT` | `HasAssignment`, `cost`, `load` (`cpap-np-hardness` formalization, copied) | `OPT = c(qs)` for an optimal `qs`; every bound is proved against every assignment `qs`. |
| "Adding a path `P` increases the covariance cost by `∑_{e ∈ P} l(e)`" | `pathLoad ps p` **(Challenge)**, `cost_snoc_pathLoad`, `Paper.cost_increase` | |
| Algorithm 1: "processes the cycles in any fixed order and assigns each one to a path with minimum current total load", `argmin` | `chooseMin`, `greedyFrom`, `greedy` **(Challenge)**; `GreedyRun` **(Challenge)**: any run with any tie-breaking | `greedy_is_assignment` **(Challenge)**, `Paper.algorithm1`, `Paper.algorithm1_assignment`. The compared theorems process the cycles in their enumerated order (`cycles g k`), which is one fixed order; the greedy inequality `GreedyRun.cost_le` holds for any list of option lists. |
| "the total load is `∑_e l(e) = Q = (k − 2) t`" | `total_load`, `Paper.total_load_eq` | |
| "`2 ALG + Q = ∑_e l(e)²`" (`binom(l,2) = (l² − l)/2`) | `sum_sq_load`, `sum_sq_load_assignment`, `Paper.sum_sq_eq` | |
| Section 7.2, the relaxation: `x_{C,P}`, `∑_P x_{C,P} = 1`, `λ_e`, objective `∑_e (λ_e² − λ_e)/2` | `FractionalSolution D R` **(Challenge)** (weights `x_{C,P} D ∈ ℕ`, summing to `D`), `optionLoad` (`D p_{C,e}`), `fractionalLoad` (`D λ_e`), `relaxationObjective` (`2 D²` times the objective) **(Challenge)**; `Paper.fractional_solution_iff`, `Paper.fractional_load_eq` | `weightedSum` **(Challenge)** is `∑_P x_{C,P} f(P)` (times `D`). |
| "let `x*` be an optimal fractional solution" | `OptimalFractional es D R` **(Challenge)** | Among all fractional solutions of the same option lists, any denominator, compared after clearing denominators. |
| "`Y_{C,e}`", "`p_{C,e}`", "`E[l(e)] = λ_e`", "`Var[l(e)] = ∑_C p_{C,e}(1 − p_{C,e})`" | `optionLoad`, `meanLoad` (`D μ_e`) **(Challenge)**, `varianceLoad` (`D²` times the variance), `expectedSquares` (`D² ∑_e E[l(e)²]`) | |
| Independent randomized rounding, `E[c(τ)]` | `rounded` **(Challenge)** (the sum over the product distribution, times `D^t`), `expectedCost R = rounded cost [] R` **(Challenge)** | |
| Algorithm 2: "Initialize `p_{C,e} = 0` ... Set `p_{C,e} ← p_{C,e} + x*_{C,P}` for each edge `e ∈ P`", i.e. `p_{C,e} = ∑_{P ∋ e} x*_{C,P}`; `μ_e`, "`μ_e ← μ_e − p_{C,e}`", `argmin ∑_{e ∈ P} μ_e`, "breaking ties by a fixed rule" | `meanLoad D ps R e` (after the subtraction: fixed paths plus the remaining cycles), `meanLoadSum` **(Challenge)**, `roundFrom`, `conditionalRounding` **(Challenge)**; `RoundingRun` **(Challenge)**: any run with any tie-breaking | `optionLoad opts w e = ∑_j w_j · (P_j.count e)` is `D p_{C,e}` exactly as Algorithm 2 computes it (each path of a simple cycle contains `e` at most once). `rounding_is_assignment` **(Challenge)**, `Paper.algorithm2`, `Paper.algorithm2_assignment` |

## Section 7.1, the greedy algorithm

| Manuscript | Lean |
|---|---|
| "the greedy cost increase is no larger than the current load-sum on its path in the optimal assignment. Current loads are at most the final greedy loads, so summing ... `c(τ_greedy) ≤ ∑_e l(e) l*(e)`" | `GreedyRun.cost_le`, `pathLoad_le_pathLoad_append`, `sum_pathLoad_eq`, `Paper.greedy_cost_le_product` |
| "`∑_e l(e) l*(e) ≤ √(S S*)`" (Cauchy–Schwarz) | `cauchy_schwarz` (squared, in the naturals), `Paper.cauchy_schwarz_loads` |
| "`Q = ∑_e l*(e) ≤ S*`" | `load_le_sq` |
| "`S ≤ 2√(S S*) + S*`; ... `z ≤ 1 + √2`. Squaring proves the bound" | `quadratic_bound`: `(S − S')² ≤ 4 S S'`; `le_six_of_quadratic`: `S ≤ 6 S'` |
| **Lemma 13** | `greedy_sq_load_bound` **(Challenge)**, `Paper.greedy_load_norm`, `Paper.greedy_load_norm_integer` |
| **Theorem 14** ("`2 ALG + Q ≤ (3 + 2√2)(2 OPT + Q)`, which rearranges to the stated inequality") | `greedy_cost_bound` **(Challenge)**, `greedy_cost_integer_bound` **(Challenge)**, `Paper.greedy_guarantee`, `Paper.greedy_guarantee_integer` |
| Lemma 15 (`lem:greedy_time`): Algorithm 1 runs in `O(kt + Υ_k)` time | `STACS2027.Runtimes.Greedy.greedy_ram` in `cpap-runtimes`: a verified add/subtract RAM program on the supplied cycle list, with linear time in the cycle-edge incidences and graph input |

## Sections 7.2 and 7.3, the relaxation and its roundings

| Manuscript | Lean |
|---|---|
| "Integral feasible solutions are exactly cycle-path assignments, so the relaxed optimum `OPT_CP ≤ OPT`" | `integralSolution`, `integralSolution_fractional`, `integralSolution_load`, `fractional_le_integral`, `Paper.relaxation_lower_bound` |
| Lemma 16 (convex quadratic program, polynomial time for fixed `k` by ANONYMIZED et al.) | `STACS2027.Runtimes.ConvexQP.Inst.F_convex` and `STACS2027.Runtimes.QPRam.relaxSolver_ram_optimal` in `cpap-runtimes`: convexity and a verified polynomial-time exact rational solver; the ANONYMIZED et al. algorithm stays cited |
| "`∑_{e ∈ E(C)} p_{C,e} = k − 2`" | `sum_optionLoad`, `sum_fractionalLoad` |
| "`E[c(τ)] = OPT_CP + ½ ∑_e Var[l(e)]`" | `expectedSquares_start` (`D² ∑_e E[l(e)²] = ∑_e (D λ_e)² + D² ∑_e Var[l(e)]`), `rounded_sq_eq`, `expectedCost_bound` |
| "By Cauchy–Schwarz, `∑_{e ∈ E(C)} p_{C,e}(1 − p_{C,e}) ≤ 2(k − 2)/k`" | `variance_bound` (`k ∑_e Var ≤ 2 D² (k − 2)` for one cycle), `variance_sum_bound` |
| **Theorem 17** | `expectedCost_bound` (on any `CycleInstance`), `randomized_rounding_cost_bound` **(Challenge)**, `Paper.rounding_guarantee` |
| "Before fixing a cycle `C`, the expected final cost is the weighted average, with weights `x*_{C,P}`, of the expected costs obtained by fixing each candidate path" | `average_identity` (per edge), `average_identity_sum`, `Paper.conditional_expectation_average` |
| "fixing a path `P` adds `∑_{e ∈ P} μ_e` to the expected cost, up to a term independent of `P`. Thus the minimizing path implements conditional expectation" | `expectedSquares_snoc`, `expectedSquares_le_of_meanLoadSum_le`, `expectedSquares_step`, `Paper.fixing_a_path` |
| "A minimizing path therefore never increases this expectation ... after all choices are fixed it equals the cost of the returned assignment" | `RoundingRun.expectedSquares_le`, `expectedSquares_nil`, `sum_sq_load_assignment` |
| **Theorem 18** | `roundingRun_cost_bound` (on any `CycleInstance`), `conditional_rounding_cost_bound` **(Challenge)**, `Paper.derandomized_guarantee` |
| the cycle instance: options of `k − 2` edges in the `k` cycle edges | `cycleInstance_of_cycles`, `CycleInstance`, `OptionsIn` |

## Package boundary and companion programs

* Lemma 16 is proved by the exact solver in `cpap-runtimes`
  (`STACS2027.Runtimes.QPRam.relaxSolver_ram_optimal`). This package takes an optimal
  fractional solution with a common denominator as given. The algorithm of ANONYMIZED,
  ANONYMIZED and ANONYMIZED (1980) remains cited rather than implemented.
* The Lemma 15 program and its time bound are proved in `cpap-runtimes`
  (`STACS2027.Runtimes.Greedy.greedy_ram`) on the supplied cycle list.
  `STACS2027.Runtimes.generalCycleEnumerationRam` supplies a uniform actual RAM
  enumerator for arbitrary fixed cycle length; `Υ_k` records its listing cost
  when composing the manuscript's bound. The paper states Algorithm 2's
  correctness and cost guarantee without a separate running-time theorem.
* The greedy machine-job load-balancing analysis of ANONYMIZED et al. (1995) that
  the proof of Lemma 13 follows is not used; the inequality is proved directly.

## Differences

* Square roots are avoided: Lemma 13 and Theorem 14 are stated as the
  equivalent polynomial inequalities `(S − S')² ≤ 4 S S'` and
  `(A − B)² ≤ 4 A B` with `A = 2 ALG + Q`, `B = 2 OPT + Q` (for `A ≥ B`, that
  is `A/B ≤ (1 + √2)² = 3 + 2√2`), plus integer forms.
* Every bound is proved for every run of the algorithm (any tie-breaking) and
  against every assignment, not only the optimum.
* The fractional solution has a common denominator `D`; expectations and
  objectives are scaled by powers of `D` so that everything is in the naturals
  (the objective in the integers).
