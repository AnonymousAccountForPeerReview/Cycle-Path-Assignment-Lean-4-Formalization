# Paper map: Section 8 and Appendices E and F in Lean

Result numbers follow the accompanying paper. Lean names do not carry result numbers
(`Paper.outerplanar_algorithm4_perfect`, `Paper.outerplanar_algorithm4_disjoint` and
`Paper.k23_perfect_of_blocks` restate Lemma 25 and Theorem 20). Names without a namespace are in `STACS2027`; `Paper.x` is
`STACS2027.Paper.x` in `MinorFree/Paper.lean`. Every row is a proved theorem or
a definition. The six compared theorems, and
the definitions their statements use, are marked **(Challenge)**. Lemma 23 is
formalized in full, including the planarity of `K_{2,n−2}`.

## Definitions and hypotheses

| Manuscript | Lean | Notes |
|---|---|---|
| Definition 1 (CPAP), perfect assignment (`cost(τ) = 0`) | `HasAssignment g k 0`, `cost` (`cpap-np-hardness` formalization, copied) | |
| Algorithm 4: "select a node `v` with degree at most 2 ... delete `v` and the incident edges" | `EliminationOrder g rank` **(Challenge)**: `rank` injective, every vertex has at most two neighbours of larger rank | The deletion order of Algorithm 4. Its existence is a package-local hypothesis; cpap-outerplanar proves it from OuterplanarDrawing by outerplanar_eliminationOrder. |
| Lemma 24: "in a `K_{2,3}`-minor-free graph, any two distinct vertices have at most two common neighbours" | `CommonNeighbourBound g` **(Challenge)**, `Paper.common_neighbours_hypothesis` | Taken as a hypothesis in this package; cpap-outerplanar defines minors and proves commonNeighbourBound_of_k23MinorFree. |
| Algorithm 4: "set `τ((v,u,x,w)) = {{v,u},{v,w}}`" | `earliestIndex`, `algorithm4 rank g` **(Challenge)**: each four-cycle gets the path omitting the vertex opposite its earliest vertex, i.e. the two edges at the earliest vertex | `earliestIndex_spec`, `four_cycle_rotation`, `mem_selectedAt_four`, `earliestView`, `Paper.algorithm4_path` |
| `K₄` "with vertices 1, 2, 3, 4" and its three four-cycles | `k4`, `k4Assignment` | On `0, 1, 2, 3`; `IsK4 h` **(Challenge)**: `h` is `K₄` under an injective renaming of its vertices. |
| "every four-cycle lies in one 2-connected block", "distinct blocks have disjoint edge sets" | `CyclesInBlocks blocks k`, `EdgeDisjoint blocks` **(Challenge)** | This interface accepts an explicit block list; cpap-outerplanar proves its edge-disjointness and cycle-containment witnesses. |
| Lemma 19 (ANONYMIZED et al.): "every 2-connected `K_{2,3}`-minor-free graph is either outerplanar or isomorphic to `K₄`" | `OuterplanarOrK4 b` **(Challenge)** | OuterplanarOrK4 is an interface using the two structural predicates above; OuterplanarDrawing is defined in cpap-outerplanar. cpap-outerplanar proves the drawing/minor characterization and block structure in outerplanar_block_structure; the citation remains. |
| Lemma 23: `G = K_{2,n−2}` | `biclique r` **(Challenge)** (`r = n − 2`), `pairs`, `canonicalCycles` | Vertices `0, 1` joined to `2, …, r + 1`. |
| Lemma 23: "planar graphs" | `Complexity.PlanarGraph` **(Challenge)**, with `Complexity.iterate`, `Hypermap`, `cycleCount`, `Hypermap.linked`, `Hypermap.componentCount`, `Hypermap.eulerLhs`, `Hypermap.eulerRhs`, `Hypermap.genus`, `Hypermap.Planar`, `halfEdgeEnd` (NP-completeness foundation `NPCompleteness-Lean4`, `Complexity/Planarity.lean`, copied whole) | A graph, as its edge list, is planar when a hypermap of genus zero (Euler formula, after ANONYMIZED) on its half-edges pairs the two ends of each edge and has the half-edges at each vertex as its `node` cycles. The same definition as in the `cpap-np-hardness` formalization. |

## Appendix E, Lemma 25 (and Lemma 24)

| Manuscript | Lean |
|---|---|
| "When `v` is processed, the vertices `u, x, w` and all four edges of `C` are still present ... its current neighborhood is exactly `{u, w}` ... the algorithm detects the cycle `(v,u,x,w)` and assigns to it the length-two path `{{v,u},{v,w}}`" (validity) | `algorithm4_valid` (every four-cycle receives one of its paths), `EarliestView.path` |
| "`u` and `w` have at most two common neighbors. One of them is `v`, so there is at most one other common neighbor `x`, and therefore at most one four-cycle whose assigned path uses the two edges incident to `v`" | `algorithm4_disjoint`: two distinct four-cycles receive edge-disjoint paths (same earliest vertex: the two later neighbours coincide by `EliminationOrder`, the fourth vertex by `CommonNeighbourBound`, so the cycles coincide; different earliest vertices: a rank contradiction), `Paper.outerplanar_algorithm4_disjoint` |
| "no edge receives load more than one ... `cost(τ) = 0`" | `cost_eq_zero_of_pairwise`, `algorithm4_cost` |
| **Lemma 25**: "For any outerplanar graph `G = (V, E)`, Algorithm 4 outputs a perfect cycle-path assignment `τ` with `cost(τ) = 0` for `k = 4`" | `algorithm4_perfect` **(Challenge)**, `perfect_four_cycle_assignment`, `Paper.outerplanar_algorithm4_perfect` |

## Theorem 20

| Manuscript | Lean |
|---|---|
| "For a `K₄` ... assign its three four-cycles as follows ... These paths use every edge exactly once" | `k4Assignment_valid`, `k4Assignment_cost` (by `decide`), `k4_perfect`, `Paper.k4_assignment` |
| `K₄` has no `k`-cycle for `k ≥ 5`: the proof of Theorem 21 (Appendix F): "For a `K_4` block, use exhaustive search when `k ∈ {3,4}`; for `k ≥ 5`, there are no `k`-cycles" | `IsCycle.length_le_vertices`, `k4_cycles_nil`, `k4_perfect_large`, `k4_cycle_assignments` **(Challenge)**, `Paper.k4_no_long_cycles` |
| copies of `K₄` | `IsK4.perfect`, `IsK4.perfect_large` (`cpap-np-hardness`'s `hasAssignment_relabel`, `hasAssignment_graph_equiv`) |
| "Combining the blockwise assignments gives a perfect assignment for `G`" (and Theorem 21's sketch: "both the assignments and their costs can be optimized independently") | `hasAssignment_disjoint_union` (two edge-disjoint parts, summed budgets), `hasAssignment_blocks` **(Challenge)**, `Paper.blockwise_combination` |
| **Theorem 20** | `perfect_assignment_of_blocks` **(Challenge)**, `Paper.k23_perfect_of_blocks` |

## Appendix E, Lemma 23

| Manuscript | Lean |
|---|---|
| "every assignment has total load `Q = (n − 2)(n − 3)`" | `assignment_total_load` (`Q = (k − 2) t`), `Paper.total_load_general` |
| "By Cauchy–Schwarz, `c(τ) = ½(∑_e l(e)² − Q) ≥ ½(Q²/m − Q)`" | `schwarz_inequality`, `sq_sum_le`, `sq_load_sum`, `cost_lower_bound` **(Challenge)**, `Paper.cauchy_schwarz_lower_bound` |
| "Take `G = K_{2,n−2}`", a planar graph | `biclique_planar` (an explicit planar hypermap for every `r`: `BicliqueEmbedding.bicliqueMap`, `biclique_getElem?`, `halfEdgeEnd_biclique`, `nd_fc_ed`, `vert_nd`, `nd_reach`, `bicliqueMap_planar`), `Paper.biclique_planar'` |
| "It has `m = 2(n − 2)` edges and `binom(n − 2, 2)` four-cycles" | `biclique_length`, `biclique_nodup`, `biclique_cycle_shape` (every four-cycle is `[0, x, 1, y]` up to rotation and reversal), `canonical_pairwise`, `canonical_cover`, `biclique_cycles_perm`, `biclique_cycle_count`, `Paper.biclique_counts` |
| "`= (n − 2)(n − 3)(n − 5)/4`" | `biclique_cost_lower` |
| "each edge belongs to exactly `n − 3` four-cycles, so every assignment has cost at most `m binom(n − 3, 2) = O(n³)`" | `biclique_edge_cycles`, `load_le_cycle_count`, `cost_le_of_load_le`, `biclique_cost_upper`, `Paper.biclique_edge_count` |
| **Lemma 23**: "There is a family of planar graphs on `n` vertices whose optimal four-cycle assignment cost is `Θ(n³)`" | `biclique_planar_family` **(Challenge)**: `K_{2,r}` is planar, has `2r` edges and `binom(r, 2)` four-cycles, and every assignment has `r(r − 1)(r − 3) ≤ 4 c(τ)` and `c(τ) ≤ r(r − 1)(r − 2)`; `Paper.biclique_planar_family'` |

## Structural witnesses and full graph-class endpoints

This package proves the assignment interfaces under explicit elimination-order, common-neighbour and block predicates. `cpap-outerplanar` constructs the witnesses from the paper's graph classes and completes the global conclusions:

| Paper result | Proved endpoint in `cpap-outerplanar` |
| --- | --- |
| Lemma 19 | `outerplanar_block_structure`: drawing/minor equivalence and the two-connected block alternative. |
| Lemma 24 | `common_neighbours_le_two` and `commonNeighbourBound_of_k23MinorFree`. |
| Lemma 25; Algorithm 4 | `outerplanar_algorithm_perfect` and `outerplanar_algorithm_assignment` for loop-free `OuterplanarDrawing`. |
| Theorem 20 | `k23_perfect : K23MinorFree g → HasAssignment g 4 0`. |
| Theorem 21; Appendix F | `k23_linear_ram`, `outerplanar_linear_ram`, Definition 26 and Lemmas 27–35. This package supplies the block-combination and K₄ base cases used by the solver. |
| Contextual planar-triangle claim | `TriangleMatching.planar_triangle_hall` and `planar_triangle_perfect_assignment`, from `Complexity.PlanarGraph g` alone. |

The bibliographic sources cited by the paper remain cited; their structural counterparts are proved in this repository.

## Differences

* The structural hypotheses are stated directly on the edge list
  (`EliminationOrder`, `CommonNeighbourBound`, `EdgeDisjoint`, `CyclesInBlocks`,
  `OuterplanarOrK4`) rather than through outerplanarity or minors; the theorems
  hold for every graph satisfying them.
* Algorithm 4 is given by its output (the earliest-vertex rule), not as the
  deletion loop; the loop's invariant "at most one four-cycle contains the
  deleted vertex" is the edge-disjointness lemma.
* Lemma 23's bounds are exact in `r = n − 2`: `r(r − 1)(r − 3) ≤ 4 c(τ)` and
  `c(τ) ≤ r(r − 1)(r − 2)`, for every assignment. Planarity is the NP-completeness
  foundation's combinatorial one (a planar rotation system, as a genus-zero
  hypermap), not a drawing in the plane.
