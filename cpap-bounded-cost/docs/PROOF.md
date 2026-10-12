# How the proofs work

The four compared theorems on the encodings are proved in
`BoundedCost/Equivalence.lean` (`almostSatisfiable_iff_hasAssignment`),
`BoundedCost/ZeroCost.lean` (`zeroCostFormula_satisfiable_iff`) and
`BoundedCost/Sizes.lean` (`almostFormula_size`, `zeroCostFormula_size`); the fifteen
on Algorithm 3 in `BoundedCost/Algorithm3Core.lean`, `BoundedCost/Algorithm3Recovery.lean`,
`BoundedCost/ZeroCost.lean` (`recoverAssignment_zeroCost`),
`BoundedCost/Algorithm3Search.lean` and `BoundedCost/Algorithm3.lean`
(`algorithm3_correct`). Throughout, the `i`-th
enumerated simple `k`-cycle is `kCycle g k i = (cycles g k).getD i []`, and an
assignment is handled as a function `f : Nat → List Edge` with `PathsOf g k f`:
for every `i < t`, `f i` is one of the `k` paths `selected (kCycle g k i) i₀` of
the `cpap-np-hardness` formalization (`BoundedCost/Tools.lean` converts to and from its
`ValidChoices` lists). Apart from the `k`-cycle core, no proof unfolds the
enumeration `cycles g k`; everything goes through `kCycle_isCycle` and the
position lemmas of `BoundedCost/CyclePositions.lean`.

## Positions on a cycle (`BoundedCost/CyclePositions.lean`)

The edge at position `j` of a simple `k`-cycle `c` is `(cycleEdges c).getD j`,
joining the vertices at positions `j` and `next k j` (`j + 1` mod `k`). Two
edges at positions `a, b` are vertex-disjoint iff `a ≠ b`, `a ≠ next k b` and
`b ≠ next k a` (`disjointEdges_edgeAt`); the path `selected c i` omits exactly
the edges at positions `i` and `next⁻¹ i` (`mem_selected_iff_position`). The
key combinatorial lemma is `common_vertex_positions`: for `k ≥ 4`, a set of
positions whose edges pairwise share a vertex all lie at one vertex — which is
the manuscript's "those two neighbors are vertex-disjoint when `k ≥ 4`, so they
cannot both be marked".

## `Γ_𝓘` (`BoundedCost/PathConstraints.lean`, `BoundedCost/Equivalence.lean`)

* Assignment to truth assignment: `assignmentOf g k f` sets `b_{C_i,e}` true iff
  `e ∉ f i`. The two omitted edges of `C_i` meet at the omitted vertex, so no
  path constraint is falsified (`pathConstraints_satisfied`), and an overlap
  constraint `λ_u` is falsified exactly when `u` is an overlap of `f`
  (`evalClause_overlapClause`, `violatedBy`).
* Truth assignment to assignment: given `σ` satisfying `Γ₁`, the marked
  positions of `C_i` pairwise share a vertex (a clause of `Γ₁` would otherwise
  be false), so by `common_vertex_positions` they lie at one vertex
  (`decode_of_satisfied`). The paths are those of Algorithm 3's recovery loop
  (`BoundedCost/Algorithm3Recovery.lean`, below): `recoveredPath g k σ` omits a
  vertex `ρ(C_i)` incident to every marked edge, hence omits every marked edge
  (`recoveredPath_omits`). A retained `λ_u` then forbids the overlap `u`
  (`recoveredPath_permitted`).
* `permittedFormula_satisfiable_iff` is the conjunction of the two.

## Almost 2-SAT (`almostSatisfiable_iff_hasAssignment`)

* From a satisfiable sublist `sub` of `Γ'` missing at most `Ψ` occurrences,
  the two steps of Algorithm 3 (`deletedOverlaps_spec`, then
  `recoverAssignment_correct`, below): each path constraint occurs `Ψ + 1`
  times in `Γ'` (`count_flatten_replicate`) and at most `Ψ` occurrences are
  missing (`Sublist.count_add_le`), so `Γ₁ ⊆ sub`, and `σ` satisfies `Γ_𝓘` for
  the overlaps `𝓘` whose `λ_u` is missing from `sub`; there are at most `Ψ` of
  them, since at most `Ψ` occurrences of the `λ_u` are missing
  (`Sublist.length_le_countP_contains`). The recovered paths then have cost at
  most `|𝓘| ≤ Ψ`.
* From an assignment of cost at most `Ψ`: keep all copies of `Γ₁` and the
  `λ_u` of the non-overlaps; `assignmentOf` satisfies it, and the number of
  dropped clauses is the cost (`cost_eq_countP_violated` again).

`cost_eq_countP_violated` (`BoundedCost/OverlapCost.lean`) rewrites the Section 5
formalization's pairwise cost `∑_{i<i'} overlap (f i) (f i')` as the number of violated
candidate overlaps, by `countP` over the rows of `candidateOverlaps`; each path
is a nodup sublist of its cycle's edges (`PathsOf.nodup`, `PathsOf.subset`).

## The zero-cost formula (`BoundedCost/PrefixVariables.lean`, `BoundedCost/ZeroCost.lean`)

The prefix variables `s_{e,1}, …, s_{e,p−1}` of the edge `e` are numbered
`prefixOffset g k e + x`, the offset being `kt` plus the `p' − 1` of the edges
listed before `e` in `edgesOnCycles g k`. `prefixVariable_lt` (`< 2kt`, since
`∑_e ϖ(e) = kt` by double counting, `sum_cyclesThrough_length`) and
`prefixVariable_inj` (distinct edges or indices give distinct variables; the
prefix-sum lemmas `prefixSum_le_of_after`, `prefixSum_add_le`) keep them apart
from the path variables and from each other.

* From a zero-cost assignment: `zeroAssignment` sets `b_{C,e}` as
  `assignmentOf` does and `s_{e,x}` to `prefixValue`, true iff one of
  `b_{C_1,e}, …, b_{C_x,e}` is false, by looking the variable up in the list
  `allPrefix` of all `(e, x)` pairs (`find?_key_injective` makes the lookup
  well defined). Each family of prefix clauses is then checked
  (`zeroCostFormula_satisfiable_of_assignment`).
* From a satisfying truth assignment: the recovered paths of Algorithm 3, as
  before (`recoverAssignment_zeroCost`); if two
  cycles `C_x, C_y` through `e`, `x < y`, both kept `e`, then `b_{C_x,e}` and
  `b_{C_y,e}` are false, the first two families force `s_{e,x}, …, s_{e,y−1}`
  true, and the clause `b_{C_y,e} ∨ ¬s_{e,y−1}` is false
  (`no_overlap_of_satisfied`). So every edge has load at most one, and the cost
  is zero.

## Sizes (`BoundedCost/Sizes.lean`)

* Every clause of both formulas has two literals, on variables below `kt`
  (`pathVariable_lt`, `edgeVariable_lt`) or `2kt` (`prefixVariable_lt`).
* `|Γ₁| = k(k−3)t/2`: for a fixed position `a` of a `k`-cycle, the positions
  `b > a` that are not vertex-disjoint from `a` are `a + 1` and, when `a = 0`,
  `k − 1` (`disjoint_pairs_count`); summing over `a` gives
  `binom(k, 2) − k = k(k−3)/2` disjoint pairs per cycle
  (`per_cycle_pathConstraints`), stated as `2|Γ₁| = k(k−3)t` to avoid
  division.
* `2|𝒰| ≤ kt(t−1)`: the row `(i, i')` of `𝒰` has at most `k` entries, there
  are `t − 1 − i` rows for each `i`, and `∑_i (t − 1 − i) = binom(t, 2)`
  (`two_mul_candidateOverlaps_length_le`).
* The zero-cost formula has at most `|Γ₁| + 3∑_e ϖ(e) = |Γ₁| + 3kt` clauses
  (`prefixClauses_length_le`, `zeroCostFormula_length_le`). The exact paper
  count is `prefixClauses_length`: `filterMap_positive_range_length` counts the
  positive positions of `range n` as `n − 1`, so the three clause families have
  `(p − 1) + (p − 2) + (p − 1) = 3p − 4` occurrences for `p ≥ 2`.
  `prefixAuxiliaryVariables_count` counts the injective map of `range (p − 1)`
  as exactly `p − 1` distinct auxiliary variables. `prefixEncodingClauseCount`
  proves the retained proposition `PrefixEncodingClauseCount`.

## Algorithm 3: the `k`-cycle core (`BoundedCost/Algorithm3Core.lean`)

`kCycleCore g k` keeps the edges of `g` on an enumerated `k`-cycle; since every
simple `k`-cycle has an enumerated representative with the same edges
(`isCycle_represented`), these are the edges on simple `k`-cycles
(`mem_kCycleCore_iff`), and the endpoints of its edges are the vertices on
simple `k`-cycles (`mem_vertices_kCycleCore_iff`, via `IsCycle.vertex_incident`
and `cycleEdges_endpoints`). A simple `k`-cycle of `g` uses only core edges, so
the two graphs have the same simple `k`-cycles (`isCycle_kCycleCore_iff`).

The enumeration itself is unchanged, as a list (`cycles_kCycleCore`). For a
subgraph `h` of `g`, `vertices h` is `vertices g` filtered to the endpoints of
`h`, because both are increasing filters of a range of naturals
(`vertices_filter_of_subgraph`, `range_filter_eq`); so the neighbors of `u` in
`h` are its neighbors in `g` along `h`-edges (`neighbors_of_subgraph`), and by
induction the walks of `h` from `v` are the walks of `g` from `v` that use only
`h`-edges, in the same order (`walksFrom_of_subgraph`). A walk of `g` that is a
`k`-cycle uses only core edges, and a vertex off the core starts no `k`-cycle,
so `rawCycles` and hence `cycles` agree (`rawCycles_kCycleCore`). Everything
else follows by rewriting: `HasAssignment` (`hasAssignment_kCycleCore_iff`) and
the formulas, which depend on the graph only through `cycles g k`
(`encodings_congr`, `encodings_kCycleCore`).

## Algorithm 3: deleted overlaps and recovery (`BoundedCost/Algorithm3Recovery.lean`)

* `deletedOverlaps g k kept` is `𝓘`, the candidate overlaps whose `λ_u` is not
  in the kept clauses. `deletedOverlaps_spec` is the counting argument of the
  Almost 2-SAT direction above, for any sublist missing at most `Ψ`
  occurrences; it does not need `k ≥ 4`.
* `omittedPosition g k σ i` searches the positions `0, …, k − 1` of `C_i` for
  the first whose vertex is incident to every edge of `markedEdges g k σ i`
  (`W_{C_i}`). If `σ` satisfies `Γ₁` (and `k ≥ 4`), `decode_of_satisfied`
  provides such a position, so the search succeeds and `omittedVertex` is
  incident to every marked edge (`omittedVertex_incident`). The recovered path
  `recoveredPath g k σ i = selected (C_i) (omittedPosition …)` is one of the
  Section 5 options, and its edges are those of `C_i` not incident to
  `ρ(C_i)` (`mem_selected_iff_incident`, from `selected_perm_selectedAt`);
  `recoveredPath_spec` collects these facts.
* `recoverAssignment_correct`: the recovered paths are `PathsOf` the cycles
  (`recoveredPath_pathsOf`), hence `ValidChoices`; each overlap of them is a
  candidate overlap whose `λ_u` fails under `σ`, hence is in `𝓘`
  (`recoveredPath_permitted`); and since the candidate overlaps are listed
  once, the cost `|{violated u}|` (`cost_eq_countP_violated`) is at most `|𝓘|`.
* `algorithm3_correct` (`BoundedCost/Algorithm3.lean`) composes these with the
  core: the formulas built on the core are those built on `g`, and the
  recovered assignment is valid for `cycles g k = cycles (kCycleCore g k) k`.

## Computing `OPT` by increasing `Ψ` (`BoundedCost/Algorithm3Search.lean`)

By Theorem 4 the test at `Ψ` is equivalent to `HasAssignment g k Ψ`, which is
monotone in `Ψ` (`almostSatisfiable_mono`) and holds at `firstOptionCost g k`,
the cost of the assignment omitting the first vertex of every cycle
(`hasAssignment_firstOptionCost`, `exists_almostSatisfiable`). The least
accepted `Ψ` is therefore the least budget admitting an assignment
(`isOptimalCost_iff_least_accepted`), which exists (`exists_isOptimalCost`,
by `exists_least_of_exists`). `searchOptimum g k test` is
`List.find? test` over `0, …, firstOptionCost g k`; `find?_range_eq_some_iff`
characterizes its result as the least accepted value, so with a correct
`test` it returns `OPT` (`searchOptimum_correct`). For `Ψ = 0`, `Γ'` is `Γ_∅`
and deleting no clause is satisfiability (`almostFormula_zero`,
`almostSatisfiable_zero_iff`, `permittedFormula_nil_satisfiable_iff`).

## Executed companion boundary

These local encoding and functional recovery proofs use only `propext`, `Classical.choice`, and `Quot.sound`. `algorithm3_correct` quantifies over correct retained clauses and truth assignments; `searchOptimum_correct` quantifies over a correct Boolean decision procedure. The companion `cpap-runtimes` package supplies the executed programs. Its concrete Almost 2-SAT compiler, fixed-parameter assignment programs and optimum-search runtime theorems have explicit `Flow.MinCostFlowSolver F T` and `Flow.AlmostLinear T` premises (F+). Its ordinary linear 2-SAT and k ≥ 4 zero-cost program are unconditional with respect to excluded algorithms. The k = 3 branch uses the flow reduction; there is no separate external Almost 2-SAT oracle.
