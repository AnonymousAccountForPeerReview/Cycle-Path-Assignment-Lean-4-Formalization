# Bounded-cost encodings and functional recovery

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

**Coverage:** Section 4 and Appendix B: bounded-cost and zero-cost encodings for cycle lengths at least four, Algorithm 3 recovery given correct solver outputs, and functional optimum-search correctness. The triangle branch and executed solver/search programs are in the companion packages.

## Local statements and companion results

The local encoding and recovery theorems apply to `k >= 4`. `algorithm3_correct` assumes correct solver outputs; `searchOptimum_correct` assumes a correct decision test. These are functional correctness statements. The actual Almost 2-SAT compiler and bounded/optimal-cost RAM programs are in `cpap-runtimes`, with the explicit flow premises stated there. The `k = 3` branch uses the triangle reduction in `cpap-tractability`.

The following source links identify declarations in this package. Definition rows identify representations; theorem and lemma rows identify proofs under their stated hypotheses. Names omit only the common `STACS2027.` namespace. The root README gives the complete paper-result map across packages.

| Paper result | Declarations in this package |
| --- | --- |
| Theorem 4 | [almostSatisfiable_iff_hasAssignment](BoundedCost/Equivalence.lean#L95); [almostFormula_size](BoundedCost/Sizes.lean#L415) |
| Corollary 5 | [zeroCostFormula_satisfiable_iff](BoundedCost/ZeroCost.lean#L310); [zeroCostFormula_size](BoundedCost/Sizes.lean#L426) |
| Algorithm 3 | [cycles_kCycleCore](BoundedCost/Algorithm3Core.lean#L268); [hasAssignment_kCycleCore_iff](BoundedCost/Algorithm3Core.lean#L274); [deletedOverlaps_spec](BoundedCost/Algorithm3Recovery.lean#L212); [recoverAssignment_correct](BoundedCost/Algorithm3Recovery.lean#L191); [algorithm3_correct](BoundedCost/Algorithm3.lean#L40); [searchOptimum_correct](BoundedCost/Algorithm3Search.lean#L182) |

## Build and trust boundary

Use `leanprover/lean4:v4.35.0-rc2` and the supplied manifests. From this package directory, retaining the sibling layout:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The default targets are `BoundedCost`, `Solution`, `BoundedCostAudit`. The delivered proof libraries contain no `sorry` or added logical axioms; transitive axiom guards permit only `propext`, `Classical.choice`, and `Quot.sound`. Instance, representation, and solver hypotheses remain part of the theorem statements.

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
| `np-completeness` | [https://github.com/RBarish-UTokyo/NPCompleteness-Lean4](https://github.com/RBarish-UTokyo/NPCompleteness-Lean4), revision `3e603e795b44fedcf7d6dd65b7d1e30547ead925`. |
| `cpap-np-hardness` | Sibling/bundled path `../cpap-np-hardness`. |

`lake-manifest.json` records resolved revisions and inherited dependencies. For each resolved Mathlib package, run `lake exe cache get` inside that Mathlib package directory. `BoundedCost.lean` imports this package's library; `Solution.lean` exposes the comparison proofs.

## Cited flow result

J. V. D. Brand *et al.*, “A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow,” *2023 IEEE 64th Annual Symposium on Foundations of Computer Science (FOCS)*, Santa Cruz, CA, USA, 2023, pp. 503–514, doi: [10.1109/FOCS57990.2023.00037](https://doi.org/10.1109/FOCS57990.2023.00037).

Apache-2.0. Preserve `LICENSE` and `NOTICE`. The root README records reused-source citations and the AI disclosure.
