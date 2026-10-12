# Paper map: Section 4 and Appendix B in Lean

Result numbers and appendix letters follow the accompanying paper. Names without a namespace are in
`STACS2027`; `Paper.x` is `STACS2027.Paper.x` in `BoundedCost/Paper.lean`.
Every row is a proved theorem or a definition. The 21 compared theorems,
and the definitions of the Challenge, are marked **(Challenge)**.

## Definitions

| Manuscript | Lean | Notes |
|---|---|---|
| Definition 1 (CPAP, objective `∑_e binom(l(e),2)`), `t`, `𝒞_k` | `HasAssignment g k Ψ`, `cost` (`cpap-np-hardness` formalization, copied); `(cycles g k).length`; `kCycle g k i` is `C_i` | The `cpap-np-hardness` formalization proves `cost` is the load objective. |
| 2-CNF formulas, truth assignments, satisfiability | `Complexity.SAT.Literal`, `Clause`, `CNF`, `Assignment`, `evalClause`, `evalCNF`, `Satisfiable` (NP-completeness foundation, copied) | A clause is a list of literals; "2-CNF" is stated as "every clause has two literals" (`Paper.boundedCost_encoding_size`, `Paper.zeroCost_encoding_size`). |
| "a Boolean variable `b_{C,e}`" for `C ∈ 𝒞_k`, `e ∈ E(C)` | `pathVariable k i j = i·k + j` (edge at position `j` of `C_i`), `edgeVariable g k i e` (by edge name), `cycleEdgeAt`, `edgePosition` | `Paper.path_variables`: the variables are distinct and below `kt`. |
| "`b_{C,e} = True` ... do not use edge `e`", "marked for omission" | `assignmentOf g k f` (true iff `e ∉ f i`), `decode_of_satisfied`; `markedEdges g k σ i` **(Challenge)** is `W_{C_i}` | |
| path constraints `Γ₁`: `¬b_{C,e_a} ∨ ¬b_{C,e_b}` for vertex-disjoint `e_a, e_b ∈ E(C)` | `disjointEdges`, `pathConstraints` **(Challenge)**; `Paper.path_constraints` | One clause per pair of positions `a < b`. |
| candidate overlaps `𝒰 = {(e,{C,C'})}` | `candidateOverlaps` **(Challenge)**, elements `(i, i', e)` with `i < i'`; `Paper.candidate_overlaps` | Each listed once (`candidateOverlaps_nodup`). |
| overlap constraint `λ_u = b_{C,e} ∨ b_{C',e}` | `overlapClause` **(Challenge)**; `Paper.overlap_constraint` | |
| `Γ_𝓘 = Γ₁ ∧ ⋀_{u ∈ 𝒰∖𝓘} λ_u` | `permittedFormula g k 𝓘` **(Challenge)**; `Paper.permitted_formula` | `𝓘` is a list of candidate overlaps. |
| `Γ' = Γ₁ ∧ ⋯ ∧ Γ₁ (Ψ+1 copies) ∧ ⋀_{u∈𝒰} λ_u`, "repeated clauses as distinct occurrences" | `almostFormula g k Ψ` **(Challenge)**; `Paper.replicated_formula` | A CNF is a list, so copies are distinct occurrences. |
| Almost 2-SAT: "deleting at most `Ψ` clauses makes a 2-CNF formula satisfiable" | `AlmostSatisfiable f Ψ` **(Challenge)** | A sublist of `f` missing at most `Ψ` occurrences is satisfiable. |
| overlaps of an assignment, `overlap(τ)`, `c(τ) ≤ |𝓘|` | `violatedBy f u`, `cost_eq_countP_violated` (`c(τ) = |{u ∈ 𝒰 : violated}|`) | |
| Corollary 5: cycles `C_1, …, C_p` through `e`; variables `s_{e,1}, …, s_{e,p−1}` | `cyclesThrough g k e`, `prefixVariable g k e x` (`s_{e,x+1}`), `prefixOffset` **(Challenge)**; `edgesOnCycles` | Prefix variables are numbered from `kt` on, edge by edge (`Paper.prefix_variables`). |
| the three families of prefix clauses | `prefixClauses` **(Challenge)**; `Paper.prefix_clauses` | "No auxiliary variables or clauses are needed when `p ≤ 1`": `Paper.prefix_variables`. |
| the zero-cost formula (`Γ₁` with the prefix encodings) | `zeroCostFormula` **(Challenge)** | |

## Section 4 and Appendix B, proof of Theorem 4

| Manuscript | Lean |
|---|---|
| "Set `b_{C,e}` to true exactly when `e ∉ τ(C)`. Each path omits two adjacent cycle edges, so no two vertex-disjoint edges are both marked and every path constraint holds" | `assignmentOf`, `pathConstraints_satisfied` (with `omittedIndex`) |
| "For `u = (e,{C,C'}) ∉ 𝓘`, the two paths cannot both contain `e`. At least one of `b_{C,e}` and `b_{C',e}` is therefore true, satisfying `λ_u`" | `evalClause_overlapClause` |
| "The path constraints ensure that the edges in `W_C` are pairwise incident", "`W_C` consists of at most two adjacent edges", "Choose a vertex `ρ(C)` incident to every edge in `W_C`" | `common_vertex_positions`, `decode_of_satisfied`, `omittedVertex_incident`, `recoveredPath_omits` |
| "Every edge retained in `τ(C)` has `b_{C,e} = False`. Consequently, if two recovered paths both contain `e`, their overlap clause is false and must have been removed from `Γ_𝓘`", "the recovered assignment satisfies `c(τ) ≤ |𝓘|`" | `recoveredPath_permitted`, `recoverAssignment_correct` **(Challenge)** |
| "`Γ_𝓘` is satisfiable `⟺` `∃ τ : overlap(τ) ⊆ 𝓘`" | `permittedFormula_satisfiable_iff`, `Paper.encoding_correct`; with costs: `Paper.clause_deletion_correct` (an assignment of cost `≤ Ψ` exists iff some `𝓘 ⊆ 𝒰` with `|𝓘| ≤ Ψ` makes `Γ_𝓘` satisfiable) |
| "Each path constraint has `Ψ + 1` copies, so at least one copy remains", "Restoring deleted copies of path constraints preserves satisfiability. If `𝓘` indexes the deleted overlap clauses, the resulting formula is equivalent to `Γ_𝓘`, with `|𝓘| ≤ Ψ`" | `deletedOverlaps_spec` **(Challenge)** (`count_flatten_replicate`, `Sublist.count_add_le`, `Sublist.length_le_countP_contains`) |
| "an assignment `τ` of cost at most `Ψ` makes `Γ_{overlap(τ)}` satisfiable. Deleting from `Γ'` precisely the overlap clauses indexed by `overlap(τ)` therefore gives a valid deletion set" | `almostSatisfiable_iff_hasAssignment` (converse direction) |
| Theorem 4, the encoding: the Almost 2-SAT call on `Γ'` succeeds exactly when a cycle-path assignment of cost at most `Ψ` exists ("This proves correctness for `Ψ ≥ 1`") | `almostSatisfiable_iff_hasAssignment` **(Challenge)**, `Paper.boundedCost_encoding` |
| "There are `kt` Boolean variables", "`k(k − 3)t/2` path constraints" | `pathVariable_lt`, `almostFormula_two_cnf`; `two_mul_pathConstraints_length` (`per_cycle_pathConstraints`, `disjoint_pairs_count`) |
| "`|𝒰| = ∑_e binom(ϖ(e), 2) ≤ ½ ∑_e ϖ(e)² ≤ ½ kt²`" | `two_mul_candidateOverlaps_length_le` (`2|𝒰| ≤ kt(t−1)`) |
| "replication gives `m = O((Ψ+1)k²t + kt²)` clause occurrences" | `almostFormula_length`; together: `almostFormula_size` **(Challenge)**, `Paper.boundedCost_encoding_size` |

## Appendix B, Corollary 5

| Manuscript | Lean |
|---|---|
| "If `b_{C_i,e}` is false for some `i < p`, the first family forces `s_{e,i}` to be true and the second propagates this value through all later prefix variables. The third family then forces every later `b_{C_j,e}` to be true" | `no_overlap_of_satisfied` |
| "whenever at most one is false, assigning the prefix variables according to their intended meaning satisfies all three clause families" | `prefixValue`, `zeroAssignment`, `prefixValue_iff`, `zeroCostFormula_satisfiable_of_assignment` |
| "recover paths from any satisfying truth assignment as in the proof of Theorem 4. A retained edge has a false `b_{C,e}`, so at most one recovered path uses each edge and the total cost is zero" | `recoverAssignment_zeroCost` **(Challenge)** |
| Corollary 5, the encoding: "A zero-cost cycle-path assignment gives a satisfying truth assignment", and conversely | `zeroCostFormula_satisfiable_iff` **(Challenge)**, `Paper.zeroCost_encoding` |
| "these contribute `O(kt)` variables and clauses in total. Together with `Γ₁`, the formula has `O(kt)` variables and `O(k²t)` clauses" | `prefixVariable_lt` (every index `< 2kt`), `prefixVariable_inj`, `sum_cyclesThrough_length` (`∑_e ϖ(e) = kt`), `prefixClauses_length_le`, `zeroCostFormula_length_le`; together: `zeroCostFormula_size` **(Challenge)**, `Paper.zeroCost_encoding_size` |
| "For an edge occurring in `p ≥ 2` cycles, the encoding uses `p − 1` auxiliary variables and `3p − 4` clauses" | `prefixAuxiliaryVariables_count` proves exactly `p − 1` distinct variables; `prefixClauses_length` proves exactly `3p − 4` clause occurrences; `prefixEncodingClauseCount` proves the retained named proposition `PrefixEncodingClauseCount` (`BoundedCost/NamedHoles.lean`); `Paper.prefix_encoding_count` combines the counts |

## Appendix B, Algorithm 3

This package's `algorithm3_correct` quantifies over solver outputs: a
satisfiable sublist `kept` of `Γ'` missing at most `Ψ` occurrences, and a
satisfying truth assignment `σ`. Its functional `searchOptimum` accepts any
correct decision procedure. The companion `cpap-runtimes` package supplies
actual RAM implementations through `BoundedCost.actualCompilerRAM_fpt` and
`TwoSat.exists_linear_twoSat`, and instantiates the reduction in
`BoundedCost.boundedCost_ram_all_from_citedFlow`. The external algorithmic
premise of that executed theorem is only the cited almost-linear flow contract.

| Manuscript | Lean |
|---|---|
| "We first restrict `G` to its `k`-cycle core, the vertices and edges belonging to at least one `k`-cycle"; Algorithm 3: "Restrict `G` to its `k`-cycle core" | `kCycleCore g k` **(Challenge)**; `mem_kCycleCore_iff` **(Challenge)** (edges), `mem_vertices_kCycleCore_iff` **(Challenge)** (vertices) |
| "This restriction preserves all feasible assignments and their costs" | `isCycle_kCycleCore_iff` **(Challenge)** (same simple `k`-cycles), `cycles_kCycleCore` **(Challenge)** (same enumeration, as a list), `hasAssignment_kCycleCore_iff` **(Challenge)** (same assignments of every cost), `encodings_kCycleCore` (same `Γ'`, `Γ_𝓘` and zero-cost formula) |
| Algorithm 3: "`𝓘 ← {u ∈ 𝒰 : λ_u is deleted by 𝒟}`; `σ ← Solve-2-SAT(Γ_𝓘)`" | `deletedOverlaps g k kept` **(Challenge)**; `deletedOverlaps_spec` **(Challenge)**: `|𝓘| ≤ Ψ`, and every `σ` satisfying the kept clauses satisfies `Γ_𝓘` (so the 2-SAT call does not fail) |
| Algorithm 3: "`W_C ← {e ∈ E(C) : σ(b_{C,e}) = True}`" | `markedEdges g k σ i` **(Challenge)** |
| Algorithm 3: "Choose `ρ(C) ∈ V(C)` with `W_C ⊆ E(C, ρ(C))`" | `omittedPosition`, `omittedVertex` **(Challenge)** (the first such vertex of `C`), `incident` **(Challenge)** (`e ∈ E(C, v)`); `recoveredPath_spec` **(Challenge)**: `ρ(C) ∈ V(C)` and `W_C ⊆ E(C, ρ(C))` when `σ` satisfies `Γ₁` |
| Algorithm 3: "`τ(C) ← E(C) \ E(C, ρ(C))`"; "Return `τ`" | `recoveredPath` **(Challenge)** (the Section 5 option omitting `ρ(C)`), `recoverAssignment` **(Challenge)**; `recoveredPath_spec` **(Challenge)**: its edges are `E(C) \ E(C, ρ(C))` |
| "`Γ_𝓘` satisfiable ⟹ ... `c(τ) ≤ |𝓘|`", for the recovered `τ` | `recoverAssignment_correct` **(Challenge)** |
| Algorithm 3 and its proof: "For `Ψ = 0`, ordinary 2-SAT suffices" (`σ ← Solve-2-SAT(Γ_∅)`) | `almostFormula_zero` (`Γ'` is `Γ_∅` for `Ψ = 0`), `almostSatisfiable_zero_iff`, `permittedFormula_nil_satisfiable_iff` **(Challenge)**; recovery from `Γ_∅`: `recoverAssignment_correct` with `𝓘 = []` |
| Algorithm 3, output: "An assignment `τ` with `c(τ) ≤ Ψ`, or `⊥` if none exists" (for `k ≥ 4`) | `algorithm3_correct` **(Challenge)**, on the core: for `Ψ ≥ 1` and `Ψ = 0` |
| "To compute `OPT`, run the algorithm for `Ψ = 0, 1, 2, …` until it returns an assignment. The first successful bound is `OPT`" | `IsOptimalCost g k C` **(Challenge)** (`C = OPT`; Section 6's `IsMinCost`); `almostSatisfiable_mono` **(Challenge)** (monotone), `exists_almostSatisfiable` **(Challenge)** (terminates), `isOptimalCost_iff_least_accepted` **(Challenge)** (the first accepted `Ψ` is `OPT`); `searchOptimum` **(Challenge)**, `firstOptionCost` **(Challenge)** and `searchOptimum_correct` **(Challenge)** (the search returns `OPT`); `exists_isOptimalCost`, `isOptimalCost_unique` |

## Package boundary and executed companion programs

* Theorem 4 and Corollary 5's executed solvers and runtime bounds are proved in
  `cpap-runtimes`. `BoundedCost.boundedCost_ram_all_from_citedFlow` supplies one
  bounded-cost program for every `k≥3`; `TwoSat.exists_linear_twoSat` proves
  linear-time 2-SAT; `generalCycleEnumerationRam` supplies a uniform
  fixed-length cycle enumerator. The manuscript's citations stay cited.
* `BoundedCost.optimalCost_ram_fpt_from_citedFlow` executes the increasing-budget
  search and returns the exact optimum followed by a valid assignment. It
  constructs a deterministic occurrence core once, preserving every cycle and
  assignment, and proves the time and memory bound at the last successful
  budget. This meets the claimed bound without using expected-time hashing.
* The Section 3 flow correspondence and its companion runtime wrappers cover
  the triangle case. The encoding in this package covers every `k≥4`, including
  four-cycles; the executed all-`k` program uses that encoding for `k≥4`.
  The cited almost-linear flow implementation remains the sole external
  algorithmic contract. Empty cycle lists are covered throughout.

## Differences from the manuscript

* The cycles are those enumerated by `cycles g k` of the `cpap-np-hardness` formalization, each
  edge set once, and `t` is the length of that list. A candidate overlap is the
  triple `(i, i', e)` with `i < i'` rather than the pair `(e, {C_i, C_{i'}})`.
* Variables are natural numbers: `b_{C_i,e} = i·k + j` for the edge at position
  `j` of `C_i`, and the prefix variables of the edges on cycles follow, in the
  order of `edgesOnCycles`.
* A 2-CNF formula is a list of two-literal clauses of the NP-completeness
  foundation; Almost 2-SAT is defined as the existence of a satisfiable sublist
  missing at most `Ψ` clause occurrences, which is the decision problem the
  cited algorithm solves.
* The manuscript's variable `b_{C,e}` is interpreted by "do not use `e`"; the
  decoding of a satisfying assignment picks `ρ(C)` as in Appendix B (the first
  suitable vertex of `C` in its enumerated order), and its existence is proved
  by `decode_of_satisfied`, which handles the cases of zero, one and two marked
  edges at once through `common_vertex_positions`. The recovered path is the
  Section 5 option omitting `ρ(C)`, a list whose edge set is
  `E(C) \ E(C, ρ(C))`.
* The `k`-cycle core is a list of edges (a `Graph`); its vertices are the
  endpoints of its edges (`vertices`), proved to be the vertices on `k`-cycles.
* `OPT` is not a function here: `IsOptimalCost g k C` says that `C` is the
  optimum, and the search `searchOptimum` is bounded by an explicit upper bound
  on `OPT` (the cost of the assignment omitting the first vertex of every
  cycle) instead of running "until an assignment is returned".
