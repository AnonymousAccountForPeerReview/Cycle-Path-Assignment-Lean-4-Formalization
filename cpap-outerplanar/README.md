# Outerplanar structure and exact assignment programs

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

**Coverage:** Section 8 and Appendices E and F: excluded-minor structure, common-neighbor and elimination-order proofs completing Algorithm 4, the planar-triangle assignment theorem, weak-dual and dynamic-programming proofs in the polygon representation, and exact linear-time algorithms.

## Local statements and companion results

The final graph-class endpoints prove perfect four-cycle assignments and exact programs from `K23MinorFree` or `OuterplanarDrawing`, with the representation conditions stated in each theorem. Perfectness is the `k = 4` conclusion; the exact solver covers each fixed `k >= 3`. Weak-dual and DP proofs use `IsPolygon`; abstract tree-DP lemmas are instantiated by that model. The exact RAM bounds are linear in graph-list size, with the numeric-label bound retained in accessed memory. The planar-triangle assignment theorem assumes `Complexity.PlanarGraph`. The assignment interfaces imported from `cpap-minor-free` are instantiated by structural proofs here.

The following source links identify declarations in this package. Definition rows identify representations; theorem and lemma rows identify proofs under their stated hypotheses. Names omit only the common `STACS2027.` namespace. The root README gives the complete paper-result map across packages.

| Paper result | Declarations in this package |
| --- | --- |
| Lemma 19 | [outerplanar_block_structure](Outerplanar/OuterplanarCharacterization.lean#L53); [outerplanarDrawing_iff_minorFree](Outerplanar/OuterplanarCharacterization.lean#L39); [twoConnected_outerplanar_or_k4](Outerplanar/OuterplanarConstruct.lean#L61) |
| Theorem 20 | [k23_perfect](Outerplanar/PerfectK23.lean#L207) |
| Theorem 21 | [k23_linear_ram](Outerplanar/LinearK23.lean#L100); [k23_linear_ram_solve](Outerplanar/LinearK23.lean#L89) |
| Lemma 24 | [common_neighbours_le_two](Outerplanar/Minors.lean#L67); [commonNeighbourBound_of_k23MinorFree](Outerplanar/Minors.lean#L90) |
| Lemma 25 | [outerplanar_degenerate](Outerplanar/GeneralDegenerate.lean#L157); [outerplanar_eliminationOrder](Outerplanar/GeneralDegenerate.lean#L193); [outerplanarDrawing_subgraph](Outerplanar/GeneralDegenerate.lean#L198); [outerplanar_algorithm_perfect](Outerplanar/GeneralAlgorithm.lean#L13); [outerplanar_algorithm_assignment](Outerplanar/GeneralAlgorithm.lean#L26) |
| Definition 26 | [DualAdj](Outerplanar/WeakDual.lean#L69); [IsSubtree](Outerplanar/WeakDual.lean#L75); [IsPolygon.segTree](Outerplanar/Segments.lean#L155); [IsPolygon.weakDual_tree](Outerplanar/WeakDualFacts.lean#L161) |
| Lemma 27 | [IsPolygon.chord_dualEdge_bij](Outerplanar/WeakDualFacts.lean#L106); [IsPolygon.bdry_ne_empty](Outerplanar/WeakDualFacts.lean#L170); [IsPolygon.bdry_deg](Outerplanar/WeakDualFacts.lean#L268) |
| Lemma 28 | [IsPolygon.leaf_face](Outerplanar/WeakDualFacts.lean#L305); [IsPolygon.leaf_face_deletion](Outerplanar/LeafFaceDeletion.lean#L146) |
| Lemma 29 | [IsPolygon.cycle_subtree_bij](Outerplanar/WeakDualBij.lean#L620); [IsPolygon.cycle_subtree_bij_simpleCycles](Outerplanar/WeakDualBij.lean#L652) |
| Lemma 30 | [IsPolygon.own_spec](Outerplanar/Segments.lean#L302); [IsPolygon.total_eq](Outerplanar/DPCorrect.lean#L243) |
| Lemma 31 | [IsPolygon.cycle_child_dichotomy](Outerplanar/NamedHoles.lean#L137); [IsPolygon.top_face_iff_parent_not_enclosed](Outerplanar/NamedHoles.lean#L77); [IsPolygon.boundary_iff_parent_enclosed](Outerplanar/NamedHoles.lean#L92) |
| Lemma 32 | [TreeDP.Problem.top_eq_or_mem_boundary](Outerplanar/TreeDP.lean#L311) |
| Lemma 33 | [TreeDP.Problem.boundary_child](Outerplanar/TreeDP.lean#L322) |
| Lemma 34 | [IsPolygon.dp_root_optimal](Outerplanar/DPCorrect.lean#L262); [IsPolygon.dp_table_correct](Outerplanar/DPCorrect.lean#L300) |
| Lemma 35 | [outerplanar_linear_ram](Outerplanar/LinearK23.lean#L113) |
| Algorithm 4 | [outerplanar_degenerate](Outerplanar/GeneralDegenerate.lean#L157); [outerplanar_eliminationOrder](Outerplanar/GeneralDegenerate.lean#L193); [outerplanarDrawing_subgraph](Outerplanar/GeneralDegenerate.lean#L198); [outerplanar_algorithm_perfect](Outerplanar/GeneralAlgorithm.lean#L13); [outerplanar_algorithm_assignment](Outerplanar/GeneralAlgorithm.lean#L26) |
| Contextual planar-triangle claim | [TriangleMatching.planar_triangle_perfect_assignment](Outerplanar/PlanarTriangles.lean#L31) |

## Build and trust boundary

Use `leanprover/lean4:v4.35.0-rc2` and the supplied manifests. From this package directory, retaining the sibling layout:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The default targets are `Outerplanar`, `Solution`, `OuterplanarAudit`. The delivered proof libraries contain no `sorry` or added logical axioms; transitive axiom guards permit only `propext`, `Classical.choice`, and `Quot.sound`. Instance, representation, and solver hypotheses remain part of the theorem statements.

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
| `cpap-minor-free` | Sibling/bundled path `../cpap-minor-free`. |
| `mathlib` | [https://github.com/leanprover-community/mathlib4.git](https://github.com/leanprover-community/mathlib4.git), revision `v4.35.0-rc2`. |

`lake-manifest.json` records resolved revisions and inherited dependencies. For each resolved Mathlib package, run `lake exe cache get` inside that Mathlib package directory. `Outerplanar.lean` imports this package's library; `Solution.lean` exposes the comparison proofs.

Apache-2.0. Preserve `LICENSE` and `NOTICE`. The root README records reused-source citations and the AI disclosure.
