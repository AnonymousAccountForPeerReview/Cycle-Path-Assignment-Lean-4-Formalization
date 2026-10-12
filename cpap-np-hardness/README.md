# CPAP model and NP-hardness

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

**Coverage:** Section 2.2, Section 5, and Appendix C: the shared CPAP model and objective identity, gadgets, planar bounded-occurrence SAT, and NP-hardness.

## Local statements and companion results

The CPAP hardness endpoints concern the foundation's encoded decision languages and polynomial-time reductions, for each fixed `k >= 5`. The planar SAT source theorem is independent of that cycle-length parameter. The gadget correctness theorem allows arbitrary endpoint choices; its planarity statement requires compatible choices. The source-hardness reduction computes the needed data for its source family. The linear RAM construction, gadget orientation, and formula-only embedding programs are in `cpap-approximation-hardness`.

The following source links identify declarations in this package. Definition rows identify representations; theorem and lemma rows identify proofs under their stated hypotheses. Names omit only the common `STACS2027.` namespace. The root README gives the complete paper-result map across packages.

| Paper result | Declarations in this package |
| --- | --- |
| Definition 1 | [cycles](NPHardness/Enumerate.lean#L35); [selected](NPHardness/FiniteCycles.lean#L57); [cost](NPHardness/FiniteCycles.lean#L105); [HasAssignment](NPHardness/CPAP.lean#L16); [Paper.cpap_objective](NPHardness/Paper.lean#L320) |
| Theorem 6 | [planarLeOneLeTwoSAT_np_complete](NPHardness/PlanarSourceHardness.lean#L41); [planarCPAP_np_hard](NPHardness/PlanarTargetHardness.lean#L39); [cpap_np_hard](NPHardness/CPAPHardness.lean#L70) |
| Definition 7 | [Paper.LeOneLeTwoCNF](NPHardness/Paper.lean#L328); [BoundedOccurrence](NPHardness/BoundedSAT.lean#L21) |
| Theorem 8 | [formulaGraph_sat_iff_assignment](NPHardness/GlobalCompleteness.lean#L126); [Paper.gadget_reduction_full_domain](NPHardness/Paper.lean#L386); [Paper.gadget_reduction_planar](NPHardness/Paper.lean#L377) |
| Definition 22 | [formulaGraph](NPHardness/GlobalGraph.lean#L30); [orientedFormulaGraph](NPHardness/OrientedGluing.lean#L28) |

## Build and trust boundary

Use `leanprover/lean4:v4.35.0-rc2` and the supplied manifests. From this package directory, retaining the sibling layout:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The default targets are `NPHardness`, `Solution`, `NPHardnessAudit`. The delivered proof libraries contain no `sorry` or added logical axioms; transitive axiom guards permit only `propext`, `Classical.choice`, and `Quot.sound`. Instance, representation, and solver hypotheses remain part of the theorem statements.

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

`lake-manifest.json` records resolved revisions and inherited dependencies. For each resolved Mathlib package, run `lake exe cache get` inside that Mathlib package directory. `NPHardness.lean` imports this package's library; `Solution.lean` exposes the comparison proofs.

## Source attribution and license

Robert D. Barish, *NP-completeness of SAT, 3-SAT and their variants (the
Cook–Levin theorem) in Lean 4*, 2026. Palomar,
[PALOMAR-2026-10-02-000013 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-02-000013&version=1).
This public foundation citation corresponds to the pinned source above.

Apache-2.0. `LICENSE` and `NOTICE` retain source and license attribution.
