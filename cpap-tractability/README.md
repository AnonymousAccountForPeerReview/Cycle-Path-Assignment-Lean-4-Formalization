# Four-cycle and triangle flow reductions

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

**Coverage:** Section 3 and Appendix A: four-cycle and triangle flow correspondences and network sizes; their timed programs are in `cpap-runtimes`.

## Local statements and companion results

The local theorems relate assignments to integral flows and prove network sizes. They do not assume a flow algorithm. The timed solver compositions in `cpap-runtimes` take a correct flow program and its resource bound as explicit premises; almost-linear conclusions additionally require its almost-linear bound.

The following source links identify declarations in this package. Definition rows identify representations; theorem and lemma rows identify proofs under their stated hypotheses. Names omit only the common `STACS2027.` namespace. The root README gives the complete paper-result map across packages.

| Paper result | Declarations in this package |
| --- | --- |
| Theorem 2 | [cpap4_iff_flow](Tractability/FlowEquivalence.lean#L336); [fourCycleNetwork_size](Tractability/NetworkSize.lean#L201) |
| Triangle flow branch in Section 3 | [cpap3_iff_flow](Tractability/TriangleEquivalence.lean#L312); [triangleNetwork_size](Tractability/TriangleSize.lean#L162) |

## Build and trust boundary

Use `leanprover/lean4:v4.35.0-rc2` and the supplied manifests. From this package directory, retaining the sibling layout:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The default targets are `Tractability`, `Solution`, `TractabilityAudit`. The delivered proof libraries contain no `sorry` or added logical axioms; transitive axiom guards permit only `propext`, `Classical.choice`, and `Quot.sound`. Instance, representation, and solver hypotheses remain part of the theorem statements.

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

`lake-manifest.json` records resolved revisions and inherited dependencies. For each resolved Mathlib package, run `lake exe cache get` inside that Mathlib package directory. `Tractability.lean` imports this package's library; `Solution.lean` exposes the comparison proofs.

## Cited flow result

J. V. D. Brand *et al.*, “A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow,” *2023 IEEE 64th Annual Symposium on Foundations of Computer Science (FOCS)*, Santa Cruz, CA, USA, 2023, pp. 503–514, doi: [10.1109/FOCS57990.2023.00037](https://doi.org/10.1109/FOCS57990.2023.00037).

Apache-2.0. Preserve `LICENSE` and `NOTICE`. The root README records reused-source citations and the AI disclosure.
