# How the proofs work

Result numbers follow the accompanying paper. This package proves Lemma 13, Theorem 14 and Algorithm 1, Theorem 17, and Theorem 18 and Algorithm 2. The greedy program and running-time bound (Lemma 15) and the exact relaxation solver (Lemma 16) are proved in `cpap-runtimes`.

Throughout, `g` is a graph without repeated edges, its simple `k`-cycles are
`cycles g k` (`t` of them), each cycle's option list is `selectedOptions c` (its
`k` paths of `k − 2` edges), and an assignment is a list `ps` of paths with
`ValidChoices ((cycles g k).map selectedOptions) ps`. The `cpap-np-hardness` formalization proves
that each path of an assignment is duplicate-free, has `k − 2` edges that lie on
its cycle, and that `c(τ) = ∑_e binom(l(e), 2)` over the edges of `g`
(`enumerated_choices_properties`, `cost_eq_load_sum`).

## Loads (`Approximation/Loads.lean`)

Adding a path `p` to `ps` increases the cost by `∑_{e ∈ p} l(e)`
(`cost_snoc_pathLoad`, from the Section 5 lemmas `cost_snoc` and
`overlap_family`). Over any duplicate-free edge list containing the path edges,
`∑_e l(e) = ∑_p |p|` (`sum_load_eq_length`, by `sum_counts`), so an assignment
has total load `Q = (k − 2) t` (`total_load`), and `∑_e l(e)² = 2 c(τ) + ∑_e l(e)`
(`sum_sq_load`, from `2 binom(l, 2) + l = l²`).

## Arithmetic (`Approximation/Arithmetic.lean`)

`2xy ≤ x² + y²` is proved by writing the larger of `x, y` as the smaller plus
`d` and expanding (`two_mul_le_sq_add`); the Cauchy–Schwarz inequality
`(∑ aᵢbᵢ)² ≤ (∑ aᵢ²)(∑ bᵢ²)` by induction on the list, the inductive step
`2 C u v ≤ A v² + B u²` following from `C² ≤ A B` by squaring and
`4 (A v²)(B u²) ≤ (A v² + B u²)²` (`cauchy_schwarz`). The quadratic step of
Lemma 13 (`quadratic_bound`): if `2c + Q = S`, `Q ≤ S'`, `c ≤ P` and
`P² ≤ S S'`, then `S − S' ≤ 2P` and `(S − S')² ≤ 4P² ≤ 4 S S'` (trivial when
`S ≤ S'`). From `(S − S')² ≤ 4 S S'` follows `S ≤ 6 S'` (`le_six_of_quadratic`):
with `S = 6S' + 1 + d`, `(5S' + 1 + d)² > 4 S S'`.

## Algorithm 1 (`Approximation/Greedy.lean`, `Approximation/GreedyBound.lean`)

`chooseMin f` returns the first option minimizing `f` (`chooseMin_mem`,
`chooseMin_le`); `greedyFrom acc options` returns the paths chosen for the
remaining cycles, each a `chooseMin` under the loads of all paths chosen before
it. `GreedyRun acc options chosen` is the predicate "each chosen path is an
option of minimum load-sum with respect to the paths before it"; `greedy` is a
run (`greedyFrom_run`), and every run is an assignment (`GreedyRun.valid`).

The greedy inequality (`GreedyRun.cost_le`): by induction over the cycles with
the accumulated paths generalized, `cost (acc ++ chosen) ≤ cost acc +
∑_{q ∈ qs} pathLoad (acc ++ chosen) q` for every competing assignment `qs`,
because the cost increase of the chosen path is at most the current load-sum
of the competitor's path, which is at most its final load-sum
(`pathLoad_le_pathLoad_append`). With `acc = []` and `sum_pathLoad_eq`,
`c(greedy) ≤ ∑_e l(e) l'(e)`. Cauchy–Schwarz, `Q ≤ S'` (each `l'(e) ≤ l'(e)²`)
and `2 c + Q = S` give Lemma 13 through `quadratic_bound`
(`greedy_sq_load_bound`); rewriting `S = 2 ALG + Q` and `S' = 2 c(qs) + Q`
gives Theorem 14 (`greedy_cost_bound`), and `le_six_of_quadratic` its integer
form.

## Fractional solutions (`Approximation/Weighted.lean`, `Approximation/Rounding.lean`)

A fractional solution `R` lists, for each cycle, its options and their weights
(numerators over the common denominator `D`), one weight per option, summing
to `D`. `weightedSum f opts w = ∑_j w_j f(P_j)` is linear (`weightedSum_add`,
`weightedSum_mul_left`, `weightedSum_const`) and at least `D` times its minimum
(`weightedSum_ge_min`). `optionLoad opts w e = ∑_{j : e ∈ P_j} w_j` is
`D p_{C,e}`; summed over the cycles it is `D λ_e` (`fractionalLoad`); it is at
most `D` for duplicate-free options (`optionLoad_le_sum`) and vanishes off the
options' edges (`optionLoad_eq_zero`); over the edges of a cycle it sums to
`D (k − 2)` (`sum_optionLoad`).

The scaled expected sum of squared loads with the paths `ps` fixed and the
cycles `R` still random is
`expectedSquares D ps R es = ∑_e [(D l_ps(e) + D λ_R(e))² + D² Var_R(e)]`
with `D² Var_R(e) = ∑_{C ∈ R} D p_{C,e} (D − D p_{C,e})`: per edge,
`E[l(e)²] = E[l(e)]² + Var[l(e)]`. The linear term `− D ∑_e E[l(e)]` of
`2 D² E[c(τ)]` is omitted because it is constant along a run (the total load
is always `(k − 2) t`); it reappears in the final accounting through
`sum_sq_load`.

## The conditional-expectation step (`Approximation/RoundingSteps.lean`)

The averaging identity (`average_identity`): for one edge `e`, with
`m = D l_ps(e) + D λ_R(e)`, `q = D p_{C,e}` and `V = D² Var_R(e)`, fixing the
option `P_j` changes `m` to `m + D c_j` with `c_j = [e ∈ P_j] ∈ {0, 1}`, so
`∑_j w_j ((m + D c_j)² + V) = D (m² + V) + 2 m D q + D² q`, and this equals
`D ((m + q)² + q (D − q) + V)`, the value before fixing `C` (using `q ≤ D`).
Summed over the edges, the weighted average of `expectedSquares` after fixing
each option equals `D` times its value before (`average_identity_sum`).

Fixing a duplicate-free path `p` adds `2 D ∑_{e ∈ p} D μ_e + D² |p|`
(`expectedSquares_snoc`), so among options of equal length the one minimizing
`∑_{e ∈ p} D μ_e` (Algorithm 2's rule, `meanLoadSum`) minimizes the expected
sum after fixing (`expectedSquares_le_of_meanLoadSum_le`); as the average over
the options is the value before fixing, the minimizing option does not
increase it (`expectedSquares_step`, dividing by `D > 0`). By induction along a
run, `D² ∑_e l_τ(e)² = expectedSquares D τ [] ≤ expectedSquares D [] R`
(`RoundingRun.expectedSquares_le`, `expectedSquares_nil`).

## The two bounds (`Approximation/RoundingBounds.lean`)

Variance (`variance_bound`): for one cycle with edge list `U` of `k = L + 2`
edges and options of `L` edges, `X = ∑_e q_e (D − q_e)` and `Y = ∑_e q_e²`
satisfy `X + Y = D ∑_e q_e = D² L`, and Cauchy–Schwarz with the indicator of
`U` gives `(D L)² ≤ k Y` (the indicator has at most `k` ones among the
duplicate-free edges, `sum_indicator_le`); hence `k X ≤ 2 D² L`. Summed over
the cycles, `k ∑_e D² Var(e) ≤ 2 D² (k − 2) t` (`variance_sum_bound`).

Lower bound (`fractional_le_integral`): an assignment `qs` is the fractional
solution with denominator `1` whose weights are the unit vectors of its chosen
options (`integralSolution`, `unitWeights`), with `fractionalLoad = load qs`;
its objective is `∑_e (l(e)² − l(e)) = 2 c(qs)`. Optimality of `R` compared with
it, after clearing the casts (`relaxationObjective_eq`), gives
`∑_e (D λ_e)² ≤ 2 D² c(qs) + D ∑_e D λ_e`, where `∑_e D λ_e = D (k − 2) t`.

Theorem 18 (`roundingRun_cost_bound`): combining,
`D² (2 c(τ) + (k − 2) t) ≤ ∑_e (D λ_e)² + ∑_e D² Var(e) ≤ 2 D² c(qs) + D² (k − 2) t + ∑_e D² Var(e)`,
multiply by `k`, use the variance bound and cancel `2 D²`:
`k c(τ) ≤ k c(qs) + (k − 2) t`. The instantiation on `cycles g k`
(`conditional_rounding_cost_bound`) uses `L = k − 2` and `U = cycleEdges c`
(`cycleInstance_of_cycles`); when there are no cycles the bound is trivial.

## Theorem 17 (`Approximation/Expectation.lean`)

`rounded f acc R` is `∑_{P₁, …} (∏ w) f (acc ++ [P₁, …])`, the expectation over
the product distribution times `D^{|R|}`; it is linear and depends only on the
values at the reachable assignments (`rounded_congr`). The averaging identity
applied cycle by cycle gives `D² · rounded (∑_e l(e)²) [] R = D^t ·
expectedSquares D [] R` (`rounded_sq_eq`), and `∑_e l(e)² = 2 c + (k − 2) t` at
every reachable assignment turns the left side into
`D² (2 · expectedCost R + D^t (k − 2) t)`. The same two bounds then give
`k · expectedCost R ≤ D^t (k c(qs) + (k − 2) t)` (`expectedCost_bound`,
`randomized_rounding_cost_bound`).
