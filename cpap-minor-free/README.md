# Assignment interfaces, block combination, and the planar biclique family

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

**Coverage:** Section 8; Appendix E: Algorithm 4 assignment correctness given elimination-order and common-neighbor hypotheses, the $K_4$ four-cycle assignment, blockwise assignments, and planar biclique cost bounds. Appendix F: supporting $K_4$ no-long-cycle facts and block-combination results.

## Local statements and companion results

`algorithm4_perfect` assumes `EliminationOrder` and `CommonNeighbourBound`; it proves the assignment's validity and zero cost. This package proves blockwise cost combination and the $K_4$ assignment/no-long-cycle facts. It does not establish elimination-order existence or minor-free block structure. Those structural witnesses and the complete graph-class endpoints are proved in `cpap-outerplanar`. Lemma 23 concerns the planar family $K_{2,r}$, together with a general load inequality; it is not a cubic-cost claim about every planar graph.

The following source links identify declarations in this package. Definition rows identify representations; theorem and lemma rows identify proofs under their stated hypotheses. Names omit only the common `STACS2027.` namespace. The root README gives the complete paper-result map across packages.

| Paper result | Declarations in this package |
| --- | --- |
| Theorem 20 | [perfect_assignment_of_blocks](MinorFree/Blocks.lean#L158); [k4_cycle_assignments](MinorFree/K4.lean#L60); [hasAssignment_blocks](MinorFree/Blocks.lean#L109) |
| Lemma 23 | [biclique_planar_family](MinorFree/BicliquePlanar.lean#L319); [cost_lower_bound](MinorFree/LoadBounds.lean#L126) |
| Lemma 25 / Algorithm 4 assignment interface, with structural inputs supplied | [algorithm4_perfect](MinorFree/Elimination.lean#L258) |
| Appendix F: supporting facts and block combination | [k4_cycle_assignments](MinorFree/K4.lean#L60); [hasAssignment_blocks](MinorFree/Blocks.lean#L109) |

## Build and trust boundary

Use `leanprover/lean4:v4.35.0-rc2` and the supplied manifests. From this package directory, retaining the sibling layout:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The default targets are `MinorFree`, `Solution`, `MinorFreeAudit`. The delivered proof libraries contain no `sorry` or added logical axioms; transitive axiom guards permit only `propext`, `Classical.choice`, and `Quot.sound`. Instance, representation, and solver hypotheses remain part of the theorem statements.

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

`lake-manifest.json` records resolved revisions and inherited dependencies. For each resolved Mathlib package, run `lake exe cache get` inside that Mathlib package directory. `MinorFree.lean` imports this package's library; `Solution.lean` exposes the comparison proofs.

Apache-2.0. Preserve `LICENSE` and `NOTICE`. The root README records reused-source citations and the AI disclosure.
