# Greedy and rounding guarantees

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

**Coverage:** Section 7: correctness and guarantees for Algorithm 1, independent randomized rounding, and Algorithm 2. The greedy running-time proof of Lemma 15 and the exact rational fractional-solution solver of Lemma 16 are in `cpap-runtimes`.

## Local statements and companion results

The graph-level cost bounds retain `g.Nodup` and a valid comparison assignment. Rounding takes an optimal rational fractional solution, represented with a positive common denominator, as an explicit input. `cpap-runtimes` supplies the exact fractional solver and the greedy running-time theorem. This package proves Algorithm 2's correctness and approximation guarantee; it does not provide a timed RAM implementation of Algorithm 2.

The following source links identify declarations in this package. Definition rows identify representations; theorem and lemma rows identify proofs under their stated hypotheses. Names omit only the common `STACS2027.` namespace. The root README gives the complete paper-result map across packages.

| Paper result | Declarations in this package |
| --- | --- |
| Lemma 13 | [greedy_sq_load_bound](Approximation/GreedyBound.lean#L37) |
| Theorem 14 | [greedy_is_assignment](Approximation/Theorems.lean#L119); [greedy_cost_bound](Approximation/GreedyBound.lean#L62); [greedy_cost_integer_bound](Approximation/GreedyBound.lean#L76) |
| Theorem 17 | [rounding_is_assignment](Approximation/Theorems.lean#L127); [randomized_rounding_cost_bound](Approximation/Theorems.lean#L85) |
| Theorem 18 | [conditional_rounding_cost_bound](Approximation/Theorems.lean#L61); [conditionalRounding](Approximation/Rounding.lean#L64) |
| Algorithm 1 | [greedy_is_assignment](Approximation/Theorems.lean#L119); [greedy_cost_bound](Approximation/GreedyBound.lean#L62); [greedy_cost_integer_bound](Approximation/GreedyBound.lean#L76) |
| Algorithm 2 | [conditional_rounding_cost_bound](Approximation/Theorems.lean#L61); [conditionalRounding](Approximation/Rounding.lean#L64) |

## Build and trust boundary

Use `leanprover/lean4:v4.35.0-rc2` and the supplied manifests. From this package directory, retaining the sibling layout:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The default targets are `Approximation`, `Solution`, `ApproximationAudit`. The delivered proof libraries contain no `sorry` or added logical axioms; transitive axiom guards permit only `propext`, `Classical.choice`, and `Quot.sound`. Instance, representation, and solver hypotheses remain part of the theorem statements.

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

`lake-manifest.json` records resolved revisions and inherited dependencies. For each resolved Mathlib package, run `lake exe cache get` inside that Mathlib package directory. `Approximation.lean` imports this package's library; `Solution.lean` exposes the comparison proofs.

Apache-2.0. Preserve `LICENSE` and `NOTICE`. The root README records reused-source citations and the AI disclosure.
