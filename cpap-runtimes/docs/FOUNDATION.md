# Use of the other formalizations, the NP-completeness foundation and Mathlib

Updated 2026-10-12. Foundation owner: ANONYMIZED.

This project depends on the following Lean developments, resolved by Lake as `lakefile.toml`
and `lake-manifest.json` record them, and never copied into this repository:

* `cpap-outerplanar`, the formalization of Appendix F (exact algorithms on outerplanar graphs)
  and of the machine of the manuscript's running-time claims (direct, `../cpap-outerplanar`).
  The library uses: the unit-cost RAM (`RAM.Config`, `RAM.Stmt`, `RAM.initial`,
  `Outerplanar/RAM/Model.lean`); its bounded runs (`RAM.ExecB S`: every `load` and `store` at an
  address below `S`; `RAM.ComputesIn s input output time space`, `Outerplanar/RAM/Bounded.lean`);
  its graph input `RAM.graphInput` and the label bound `RAM.labelBound` (`Layout.lean`); its
  verification library (Hoare triples with step bounds `HT` and their bounded form `HTB S`,
  the frame rules, array and table layouts, the loop macros `forUp`, `forRange`, `whileC` and
  their rules, the address tactics `addr_ok`; `Outerplanar/RAM/the module documentation`,
  `the module documentation`); the phases R0 (parsing and relabelling) and R1 (CSR neighbour lists),
  reused by the four-cycle listing; the module `PairIds` (identifiers of pairs by a counting
  sort, `pairIds`, `sortedLeads`, `rankIds`); the stable counting sort `P1.csort`; and the
  vertex labels `Algo.labels`, `Algo.numV`.
* `cpap-tractability`, the formalization of Section 3 (direct, `../cpap-tractability`): the flow
  networks (`FlowNode`, `Arc`, `IsFlow`, `flowValue`, `flowCost`), the network layers and the
  networks `fourCycleNetwork` and `triangleNetwork`. Section 3's correspondence between
  assignments and flows is re-proved here for any list `cs` of simple cycles
  (`Runtimes/Flow/Four.lean`, `Tri.lean`), since a listing program may produce the canonical
  cycles `cycles g k` in another order.
* `cpap-bounded-cost`, the formalization of Section 4 (direct, `../cpap-bounded-cost`): the encodings
  `almostFormula`, `zeroCostFormula`, `pathConstraints`, `candidateOverlaps`,
  `permittedFormula`, `AlmostSatisfiable`, the recovery (`omittedPosition`,
  `recoverAssignment`, `deletedOverlaps`) and the theorems on Algorithm 3. The machines of
  Corollary 5 and Theorem 4 compute these formulas and recoveries, and their correctness is
  that of the `cpap-bounded-cost` formalization; the restriction to the `k`-cycle core is skipped because
  that formalization proves it changes nothing (`cycles_kCycleCore`,
  `hasAssignment_kCycleCore_iff`).
* `cpap-approximation`, the formalization of Section 7 (direct, `../cpap-approximation`): Algorithm 1
  (`greedy`, `chooseMin`, `greedyFrom`, `pathLoad`) and Theorem 14 (`greedy_cost_integer_bound`,
  `greedy_is_assignment`), used by Lemma 15; the relaxation of Section 7.2
  (`FractionalSolution`, `relaxationObjective`, `OptimalFractional`), whose optimal solutions
  Lemma 16's machine computes (Theorems 17 and 18 take one as a hypothesis;
  `ConvexQP/Exact.lean` discharges it for `solveExactWith`).
* `cpap-np-hardness` (the cycle-path assignment problem of Section 5: `cycles`, `selected`,
  `ValidChoices`, `cost`, `HasAssignment`, the edge load `load`) and `cpap-minor-free`, through
  the others.
* The NP-completeness foundation `NPCompleteness-Lean4` (commit
  `3e603e795b44fedcf7d6dd65b7d1e30547ead925`), through the others: its CNF formulas
  (`Complexity.SAT`: `Literal`, `Clause`, `CNF`, `evalCNF`, `Satisfiable`) are the formulas of
  2-SAT and Almost 2-SAT.
* Mathlib, at the release tag `v4.35.0-rc2` of the toolchain, commit
  `065356127b1dc0016f66b7283ce0ce2c4055aa55` (direct). The statements use the real numbers and
  the real power `x ^ y` (`AlmostLinear`, `t^{1+ε}`); the proofs use, besides, finite sets and
  sums, matrices, determinants and adjugates, rational and real arithmetic, `Nat.sqrt`,
  `Nat.clog`, and tactics.

`scripts/check_repository.py` checks that the direct dependencies are required by path (the
published layout: sibling directories) or at full git commits, that the manifest agrees, that
Mathlib is pinned, and that no copy of a dependency is vendored. `lake exe cache get` fetches
Mathlib's official build cache.

## What the Challenge copies

`Challenge.lean` copies, verbatim, with docstrings and in the order of their sources:

* from the foundation (`Complexity/SAT.lean`), `Assignment` through `Satisfiable`;
* from `cpap-np-hardness`, the cycle-path assignment problem, `Edge` through `HasAssignment`,
  and the edge load `load` (`NPHardness/LoadCost.lean`; it has no docstring there, and the
  generator inserts one, the term unchanged);
* from `cpap-tractability` (`Tractability/FlowNetwork.lean`), `FlowNode` through `flowCost`;
* from `cpap-bounded-cost` (`BoundedCost/Encoding.lean`), the formula `Γ'` of Theorem 4 (`kCycle`,
  `pathVariable`, `cycleEdgeAt`, `edgePosition`, `edgeVariable`, `disjointEdges`,
  `pathConstraints`, `candidateOverlaps`, `overlapClause`, `almostFormula`) and
  `AlmostSatisfiable`;
* from `cpap-approximation`, `weightedSum`, Algorithm 1 (`pathLoad`, `chooseMin`, `greedyFrom`,
  `greedy`) and the relaxation (`optionLoad` through `OptimalFractional`);
* from `cpap-outerplanar`, the machine `RAM.Config` through `RAM.initial`
  (`Outerplanar/RAM/Model.lean`), `RAM.ExecB`, `RAM.ComputesIn` (`Outerplanar/RAM/Bounded.lean`),
  `RAM.graphInput`, `RAM.labelBound` (`Outerplanar/RAM/Layout.lean`), and `Algo.proper`,
  `Algo.labels`, `Algo.numV` (`Outerplanar/Algo/Graph.lean`);
* from this library, the encodings `TwoSat.code`, `TwoSat.IsTwoCNF`, `TwoSat.codes`,
  `ZeroCost.verts` (with its section variables `(g : Graph) (k : ℕ)`), `ZeroCost.zeroCostInput`, the flow
  hypothesis `Flow.select` through `Flow.AlmostLinear` (`Runtimes/Flow/Solver.lean`),
  `Flow.verts`, `Flow.OptCost`, `Flow.flowInput`, the exact claim `Flow.SortedNetworkConstruction`
  (`Runtimes/NamedHoles.lean`), `BoundedCost.boundedCostInput`, `BoundedCost.BoundedCostAnswer` and the
  Almost 2-SAT interface `BoundedCost.Clauses2` through `BoundedCost.FPTBound` with `BoundedCost.shiftL`,
  `BoundedCost.shiftF` (`Runtimes/BoundedCost/Solver.lean`);
* the compared statements, from `Runtimes/`, up to their `:=`, the proofs replaced by
  `sorry`, in `namespace … end` blocks with the `open` lines of their files.

`scripts/generate_challenge.py` reads the dependencies' sources through `lake-manifest.json` (a
`path` package at its `dir`, a `git` package under `.lake/packages/<name>`), so a copy cannot
drift from its source; `--check` fails if it has. Comparator checks that each copied
declaration is the same term as the library's and that each statement is the same.

The Challenge imports one module of the pinned Mathlib,
`Mathlib.Analysis.SpecialFunctions.Pow.Real`, for the real power `Real.rpow` (and with it the
real numbers, their order, casts from `ℕ`, and `Nat.log`) used by `AlmostLinear` and the almost-linear
statements. It contains no meta-level code (`check_repository.py` checks it).

## Elaboration pitfalls

* **`List.sum` with Mathlib imported.** The Section 3, 5 and 7 libraries are elaborated with
  Lean core only. There, the `[Zero α]` argument of `List.sum` is core's instance
  `Zero.ofOfNat0`; in the Challenge, which imports Mathlib, instance search would find
  Mathlib's `MulZeroClass.toZero`, and the copies would elaborate to different terms. The
  generator prefixes the eight copies that sum — `overlap`, `cost`, `load` (Section 5),
  `flowCost` (Section 3), `pathLoad`, `fractionalLoad`, `FractionalSolution` and
  `relaxationObjective` (Section 7, the last over `ℤ`) — with
  `attribute [local instance high] Zero.ofOfNat0 in`, which, for that one declaration only,
  ranks core's instance first; the term is unchanged.
* **Matcher sharing.** Lean shares, within one module, the auxiliary `match` functions of
  pattern-matching definitions of the same shape. Among the declarations copied here, no two
  match the same types with the same patterns, so each copy gets its own matcher with the
  library's name and value (the generator's `FRESH_MATCHER` set is empty).
* **Module names.** Every formalization of this manuscript has modules named `Challenge` and
  `Solution`, and the sibling packages required by path keep their own builds, so their
  `Challenge.olean` and `Solution.olean` are on Lean's search path before this package's.
  `lake build` resolves modules by package and is not affected, but `lean` on a file that
  imports `Challenge` would load the first match: `scripts/compare_challenge.py` puts this
  package's build directory first on `LEAN_PATH`, and `docs/VERIFICATION.md` records how the
  Comparator run was isolated.

These points were checked by `scripts/compare_challenge.py`: every `STACS2027` and
`Complexity` constant that the compared statements depend on (the definitions,
their matchers and auxiliaries, the `Decidable` instances and their proof auxiliaries, the
structures, inductive types and constructors, and the compared statements) prints identically, with
`pp.all`, in the library's environment and in the Challenge's; Comparator confirms it.

Every explicitly named library declaration has an exact axiom guard. Private
helpers are included: the source scanner records their module and user name,
the audit imports that module with `import all`, and the guard checks Lean's
actual private constant name and full transitive axiom report. The generator
also compares its declaration list with the built environment and rejects
unrecognized omissions or axioms outside `propext`, `Classical.choice`, and
`Quot.sound`.

## The cited algorithms as hypotheses

**Min-cost flow** (ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED,
FOCS 2023), `Runtimes/Flow/Solver.lean`:

* `netInput num n d net`: the encoding `n, m, s, z, d, (tail, head, cost)*` of the network
  `net` with its nodes numbered by `num` and the required value `d`;
* `GoodNet num n net`: `num` is injective on the nodes of `net` with values below `n`,
  `n ≤ m + 2`, no arc enters the source or leaves the sink, every cost is below `m`;
* `FlowAnswer net d out`: `[0]` if there is no integral flow of value `d`, otherwise `1` and a
  `0/1` vector over the arcs selecting (`select`) an integral flow of value `d` of minimum cost;
* `MinCostFlowSolver F T`: on every `netInput num n d net` with `GoodNet num n net`, the program
  `F` halts within `T N` steps, accessing only the addresses below `T N` (`N` the length of the
  encoding), with a `FlowAnswer`;
* `AlmostLinear T`: for every `ε > 0` some `C` has `T N ≤ C N^{1+ε}` for all `N ≥ 1`.

On the class `GoodNet` (capacities `U = 1`, costs below `N`) the cited algorithm performs
`N^{1+o(1)}` operations on `O(log N)`-bit words; the machine has no multiplication, division or
bit operations, and each word operation is simulated in `O(log N)` steps (this library's
arithmetic macros, `Runtimes/ConvexQP/RAM/Arith*.lean`, are such simulations for unbounded
numbers), with memory proportional to the time. So the cited algorithm gives a program `F` with
`MinCostFlowSolver F T` for some `T` with `AlmostLinear T`. This argument is not formalized.
`MinCostFlowSolver F T` alone is not vacuous: a brute-force program (trying every `0/1` vector
over the arcs) satisfies it for a suitable, exponential, `T`.

**Almost 2-SAT** (ANONYMIZED, ANONYMIZED, JCSS 2009), `Runtimes/BoundedCost/Solver.lean`:

* `a2In f Ψ = Ψ :: |f| :: codes f`, the input; `Clauses2 f`: every clause has two literals;
* `A2Answer f Ψ out`: `[0]` iff no deletion of at most `Ψ` clauses makes `f` satisfiable
  (`¬ AlmostSatisfiable f Ψ`); otherwise `1 :: |D| :: (D ++ T)`, `D` the deleted clause positions
  (increasing, below `|f|`, at most `Ψ`), `T` the increasing list of the variables set to true
  (each occurring in `f`), such that setting exactly the variables of `T` to true satisfies every
  clause outside `D` (the normal form lets the next program find the end of `T`);
* `Almost2SatSolver F T`: on every `a2In f Ψ` with `SolverDomain f`, `F` halts within `T Ψ N` steps
  and the addresses below `T Ψ N` (`N` the input length) with an `A2Answer`;
* `FPTBound T`: `T Ψ N ≤ C 15^Ψ (Ψ + 1) (N + 1)³`, the cited `O(15^Ψ Ψ m³)` in terms of the input
  length.

The Almost 2-SAT algorithm is now implemented as one fixed RAM program.
`BoundedCost.actualCompilerRAM_fpt` proves its `Almost2SatSolver` contract and
uniform `FPTBound`, including all annotated search, compression, prefix,
least-cut, and normalized-output phases. Its only algorithmic hypothesis is
`MinCostFlowSolver F T` together with `AlmostLinear T`, the external cited flow
contract. `Almost2SatSolver` is an interface instantiated by that proof.
`BoundedCost.boundedCost_ram_fpt_from_citedFlow` discharges the Almost 2-SAT
hypothesis in Theorem 4 for `k≥4`; `boundedCost_ram_all_from_citedFlow` gives the
same sole-flow result for every `k≥3`. The ANONYMIZED–ANONYMIZED [RO09] result remains cited.

`BoundedCost.optimalCost_ram_fpt_from_citedFlow` executes the increasing-budget
optimization loop with the same sole flow contract. It constructs the occurrence
core once, performs the actual repeated solver calls, and emits the exact optimum
followed by a valid assignment. Both time and memory satisfy the manuscript's
last-successful-budget bound, including zero optimum and empty cycle lists.

`Flow.polynomialMinCostFlowSolverExists_of_almostLinear` derives the ordinary
polynomial flow bound from the same external contract. No independent polynomial
flow solver hypothesis is introduced. General cycle enumeration and the
single-program glue of Corollary 3 are also executed and verified
(`generalCycleEnumerationRam`, `fourCycleAssignment_single`).

`scripts/check_repository.py` checks that exactly the intended compared statements take these
hypotheses, each once and as an explicit binder (`(hF : MinCostFlowSolver F T)`,
`(hT : AlmostLinear T)`, `(hA : Almost2SatSolver F T)`, `(hT : FPTBound T)`, primed in the
statements for all `k ≥ 3`).

## Re-pinning a dependency

The direct dependencies are required by path (`../<name>`) in the published layout, or by git
URL and commit. To change one, edit its `[[require]]` entry in `lakefile.toml` and run
`lake update <name>`, which rewrites `lake-manifest.json`; then re-run the checks of
`docs/VERIFICATION.md`. Through the direct dependencies, `cpap-np-hardness`, `cpap-minor-free` and
the foundation are resolved once for the whole workspace and must agree.
