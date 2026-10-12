# Executed algorithms and their resource bounds

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

**Coverage:** Sections 3, 4, and 7, and Appendices A and B: RAM programs for flow construction/extraction and composition, cycle enumeration, 2-SAT, Almost 2-SAT on the stated encoded-formula domain, optimum search, greedy assignment, and exact rational convex-relaxation solving on supplied cycle lists. Flow-dependent conclusions retain their explicit solver hypotheses; the cited almost-linear flow implementation remains external.

## Local statements and companion results

The unit-cost RAM has unbounded natural-number cells; bounds measure instructions and accessed addresses, not bit complexity. Most programs take an enumerated cycle list; the complete four-cycle pipeline includes enumeration itself. The Almost 2-SAT compiler's `SolverDomain` requires exactly two literals per clause and variable indices below twice the clause count plus one. Its FPT theorem requires both `Flow.MinCostFlowSolver F T` and `Flow.AlmostLinear T`. The exact convex solver takes a duplicate-free graph and `ZeroCost.zeroCostInput`, which includes its enumerated cycles.

**F** denotes an explicit correct flow solver with a resource bound; **F+** additionally requires its almost-linear bound. These are theorem premises, not Lean axioms. The only excluded algorithmic implementation is the cited almost-linear minimum-cost-flow algorithm. Other supplied programs retain the input and representation hypotheses in their linked statements.

For Corollary 5, `ZeroCost.zeroCost_ram` covers `k >= 4`; the `k = 3` branch uses the explicit-flow triangle program and its solver hypotheses.

The following source links identify declarations in this package. Definition rows identify representations; theorem and lemma rows identify proofs under their stated hypotheses. Names omit only the common `STACS2027.` namespace. The root README gives the complete paper-result map across packages.

| Paper result | Declarations in this package |
| --- | --- |
| Theorem 2 | [Runtimes.Flow.cpap4_flow_ram_semantic](Runtimes/Flow/Statement.lean#L76) **F**; [Runtimes.Flow.cpap4_flow_single](Runtimes/Flow/Single.lean#L129) **F**; [Runtimes.Flow.polynomialMinCostFlowSolverExists_of_almostLinear](Runtimes/Flow/PolynomialBound.lean#L63) **F+**; [Runtimes.Flow.cpap4_flow_ram_almostLinear](Runtimes/Flow/Main.lean#L302) **F+**; [Runtimes.Flow.cpap4_flow_single_almostLinear](Runtimes/Flow/Single.lean#L181) **F+** |
| Corollary 3 | [Runtimes.fourCycleAssignment_single_explicit](Runtimes/CpapSingle/Complete.lean#L21) **F**; [Runtimes.fourCycleAssignment_single](Runtimes/CpapSingle/Complete.lean#L68) **F+**; [Runtimes.C4.fourCycles_ram_semantic](Runtimes/C4/Statement.lean#L40); [Runtimes.C4.fourCycles_ram_paper_semantic](Runtimes/C4/Statement.lean#L57); [Runtimes.C4.fourCycles_ram_simple_semantic](Runtimes/C4/Statement.lean#L81) |
| Theorem 4 | [Runtimes.BoundedCost.actualCompilerRAM_fpt](Runtimes/BoundedCost/ActualCompilerRAM.lean#L56) **F+**; [Runtimes.BoundedCost.almostTwoSatFptSolverExists_of_citedFlow](Runtimes/BoundedCost/ActualCompilerRAM.lean#L89) **F+**; [Runtimes.BoundedCost.boundedCost_ram_fpt_from_citedFlow](Runtimes/BoundedCost/ActualFPT.lean#L15) **F+**; [Runtimes.BoundedCost.Almost2SatSolver](Runtimes/BoundedCost/Solver.lean#L76); [Runtimes.BoundedCost.FPTBound](Runtimes/BoundedCost/Solver.lean#L84) |
| Corollary 5 | [Runtimes.ZeroCost.zeroCost_ram](Runtimes/ZeroCost.lean#L240); [Runtimes.TwoSat.exists_linear_twoSat](Runtimes/TwoSatMain.lean#L189); [Runtimes.Flow.triangle_single](Runtimes/Flow/Single.lean#L155) **F**; [Runtimes.Flow.triangle_single_almostLinear](Runtimes/Flow/Single.lean#L210) **F+** |
| Lemma 15 | [Runtimes.Greedy.greedy_ram](Runtimes/Greedy/Main.lean#L120); [Runtimes.Greedy.greedy_guarantee_ram](Runtimes/Greedy/Main.lean#L137) |
| Lemma 16 | [Runtimes.QPRam.relaxSolver_ram_optimal](Runtimes/ConvexQP/RAM/RelaxSolver.lean#L80) |
| Algorithm 3 | [Runtimes.BoundedCost.optimalCost_ram_fpt_from_citedFlow](Runtimes/BoundedCost/OptMain.lean#L85) **F+** |

## Build and trust boundary

Use `leanprover/lean4:v4.35.0-rc2` and the supplied manifests. From this package directory, retaining the sibling layout:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The default targets are `Runtimes`, `Solution`, `RuntimesAudit`. The delivered proof libraries contain no `sorry` or added logical axioms; transitive axiom guards permit only `propext`, `Classical.choice`, and `Quot.sound`. Instance, representation, and solver hypotheses remain part of the theorem statements.

`comparator.json` lists selected comparison endpoints, not all proved declarations. Its temporary `Challenge.lean` specification is omitted from the distribution. To reproduce optional comparisons, generate it before building or checking it:

```sh
python3 scripts/generate_challenge.py
lake build Challenge
python3 scripts/check_repository.py
lake comparator --config comparator.json --paranoid
```

The comparator requires its configured checkers and runtime prerequisites. `docs/VERIFICATION.md` and `proofs/` distinguish current compilation from retained independent-comparison evidence.

## Direct dependencies

| Lake package | Declared source |
| --- | --- |
| `cpap-outerplanar` | Sibling/bundled path `../cpap-outerplanar`. |
| `cpap-tractability` | Sibling/bundled path `../cpap-tractability`. |
| `cpap-bounded-cost` | Sibling/bundled path `../cpap-bounded-cost`. |
| `cpap-approximation` | Sibling/bundled path `../cpap-approximation`. |
| `mathlib` | [https://github.com/leanprover-community/mathlib4.git](https://github.com/leanprover-community/mathlib4.git), revision `v4.35.0-rc2`. |

`lake-manifest.json` records resolved revisions and inherited dependencies. For each resolved Mathlib package, run `lake exe cache get` inside that Mathlib package directory. `Runtimes.lean` imports this package's library; `Solution.lean` exposes the comparison proofs.

## Cited flow result

J. V. D. Brand *et al.*, “A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow,” *2023 IEEE 64th Annual Symposium on Foundations of Computer Science (FOCS)*, Santa Cruz, CA, USA, 2023, pp. 503–514, doi: [10.1109/FOCS57990.2023.00037](https://doi.org/10.1109/FOCS57990.2023.00037).

Apache-2.0. Preserve `LICENSE` and `NOTICE`. The root README records reused-source citations and the AI disclosure.
