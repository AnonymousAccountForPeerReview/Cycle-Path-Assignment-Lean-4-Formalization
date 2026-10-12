# How the proofs work

Result numbers follow the accompanying paper. This package proves assignment interfaces and Lemma 23; cpap-outerplanar proves the structural witnesses and full graph-class endpoints, including the exact algorithms of Appendix F.

## Four-cycles (`MinorFree/FourCycles.lean`)

A simple four-cycle `c`, rotated to start at its `i`-th vertex, is `[v, u, x, w]`
(`four_cycle_rotation`, with `c[i] = v` and `c[(i + 2) % 4] = x`); the rotation
is a cycle of the same graph with the same edges (`IsCycle.rotation`,
`sameCycle_rotation`, from the cpap-np-hardness lemmas `IsCycle.append_swap` and
`sameCycle_append_swap`). Its edges are `vu, ux, xw, wv` (`mem_cycleEdges_four`),
and the path omitting `x` consists of the two edges at `v`
(`mem_selectedAt_four`, from cpap-np-hardness's `selectedAt_mem`). The cost of a family
of pairwise edge-disjoint paths is zero (`cost_eq_zero_of_pairwise`).

## Lemma 25 (`MinorFree/Elimination.lean`)

`earliestIndex rank c` is the position of the vertex of minimum rank
(`earliestIndex_spec`). `earliestView` packages what the proof needs about a
four-cycle `c` seen from its earliest vertex `v`: its vertices `v, u, x, w`,
its edges, Algorithm 4's path `{wv, vu}` for it (through cpap-np-hardness's
`selected_perm_selectedAt` and `SameCycle.selectedAt_perm`), the distinctness
of the four vertices, the membership of the four edges in `g`, and
`rank v < rank u, rank x, rank w` (injectivity of `rank`).

`algorithm4_disjoint`: if the paths of two four-cycles `c`, `d` share an edge
`e = edge v y = edge v' y'` (`y ∈ {u, w}`, `y' ∈ {u', w'}`), then either
`v = v'` — so `u, w, u', w'` are all later neighbours of `v`, and the
elimination order forces `{u', w'} = {u, w}`; then `x` and `x'` are common
neighbours of `u` and `w` other than `v`, and the common-neighbour bound forces
`x = x'`; so `c` and `d` have the same four edges, contradicting their
distinctness as enumerated cycles — or `v' = y` and `v = y'`, so
`rank v < rank v' < rank v`. Hence the assigned paths are pairwise
edge-disjoint and the cost is zero (`algorithm4_cost`); validity is that
`(earliestIndex + 2) % 4 < 4` indexes one of the cycle's options
(`algorithm4_valid`).

## `K₄` and blocks (`MinorFree/K4.lean`, `MinorFree/Blocks.lean`)

The enumerated four-cycles of `k4` are `[0,1,2,3]`, `[0,1,3,2]`, `[0,2,1,3]`;
the manuscript's assignment is checked by `decide` (`k4Assignment_valid`,
`k4Assignment_cost`). A simple `k`-cycle of a graph on `n` vertices has
`k ≤ n` (duplicate-free vertex list inside `List.range n`), so `k4` has no
`k`-cycle for `k ≥ 5` (`k4_cycles_nil`). Copies of `K₄` are handled by cpap-np-hardness's `hasAssignment_relabel` and `hasAssignment_graph_equiv` (`IsK4.perfect`).

`hasAssignment_disjoint_union`: for edge-disjoint `g₁`, `g₂` with every cycle of
`g₁ ++ g₂` inside one of them, the concatenation `cycles g₁ k ++ cycles g₂ k` is
a complete, pairwise-distinct cycle family of the union (a cycle of `g₁` and
one of `g₂` cannot have the same edges), so cpap-np-hardness's
`hasAssignment_iff_complete_family` reduces the union to `FamilyAssignment`;
the two chosen-vertex functions are merged (`if c ∈ cycles g₁ k then … else …`),
the cost splits by `cost_append` into the two costs plus a cross term that
vanishes because the paths of the two parts use edges of different graphs
(`crossCost_zero_iff`). Induction over a list of blocks gives
`hasAssignment_blocks`, and with the elimination-order Lemma 25 interface and the `K₄` case, the zero-cost block interface `perfect_assignment_of_blocks`. The full Theorem 20 endpoint `k23_perfect` in cpap-outerplanar constructs and supplies the proved block witnesses.

## Lemma 23 (`MinorFree/LoadBounds.lean`, `MinorFree/Biclique.lean`, `MinorFree/BicliquePlanar.lean`)

On a duplicate-free graph edge list, `(∑_e l(e))² ≤ m ∑_e l(e)²` (Cauchy–Schwarz with the constant
sequence, `sq_sum_le`), `∑_e l(e)² = 2 c(τ) + Q` and `Q = (k − 2) t`, so
`Q² ≤ m (2 c(τ) + Q)` (`cost_lower_bound`). The load of an edge is at most the
number of cycles containing it (`load_le_cycle_count`), and with every load at
most `L`, `c(τ) ≤ m binom(L, 2)` (`cost_le_of_load_le`).

For `K_{2,r}` (vertices `0, 1` joined to `2, …, r + 1`): every edge joins
`{0, 1}` to the large side (`edge_mem_biclique`), so the vertices of a
four-cycle alternate and it is `[0, x, 1, y]` up to rotation and reversal with
`2 ≤ x < y < r + 2` (`biclique_cycle_shape`, the rotations and reversals being
`sameCycle_shapes`). The canonical cycles `[0, i + 2, 1, j + 2]`, one per pair
`i < j < r` (`pairs r`, of length `binom(r, 2)`), are pairwise distinct
(`canonical_injective`) and cover every four-cycle, so cpap-np-hardness's
`representatives_perm` gives a permutation between them and the enumerated
cycles: `t = binom(r, 2)` (`biclique_cycle_count`). The lower bound follows from
`cost_lower_bound` with `m = 2r` and `Q = 2t = r(r − 1)`:
`r(r − 1)(r − 3) ≤ 4 c(τ)` (`biclique_cost_lower`). An edge `(0, j + 2)` or
`(1, j + 2)` lies on the canonical cycles of the pairs containing `j`, which
number `r − 1` (`biclique_edge_cycles`), so every load is at most `r − 1` and
`c(τ) ≤ 2r binom(r − 1, 2) = r(r − 1)(r − 2)` (`biclique_cost_upper`).

### Planarity of `K_{2,r}` (`MinorFree/BicliquePlanar.lean`)

Planarity is the NP-completeness foundation's `Complexity.PlanarGraph`: a hypermap on
the `2m` half-edges (half-edges `2i`, `2i + 1` are the ends of edge `i`) whose
`edge` permutation swaps `2i` and `2i + 1`, whose `node` cycles are exactly the
sets of half-edges at a common vertex (`halfEdgeEnd`), and whose genus
`(2 · components + darts − (edges + nodes + faces)) / 2` is zero. Edge `i` of
`biclique r` is `(i mod 2, ⌊i/2⌋ + 2)` (`biclique_getElem?`), so half-edge `4j`
lies at `0`, `4j + 2` at `1`, and `4j + 1`, `4j + 3` at `j + 2`
(`halfEdgeEnd_biclique`, with the vertex label `vert`).

`BicliqueEmbedding.bicliqueMap r` is the hypermap on `4r` half-edges with, on
`Nat`, `ed` (swap `2i`, `2i + 1`), `nd` (`4j ↦ 4(j + 1)`, `4(r − 1) ↦ 0`: the
rotation at `0` in increasing order; `4j + 2 ↦ 4(j − 1) + 2`, `2 ↦ 4(r − 1) + 2`:
the rotation at `1` in decreasing order; `4j + 1 ↔ 4j + 3`) and
`fc = nd⁻¹ ∘ ed` (`4j ↦ 4j + 3 ↦ 4j' + 2 ↦ 4j' + 1 ↦ 4j` with
`j' = j + 1 mod r`), so that `nd (fc (ed d)) = d` (`nd_fc_ed`). Each of these
facts is a case analysis on `d mod 4` closed by `omega`.

* Node condition: `nd` preserves `vert` (`vert_nd`, `iterate_nd_vert`); conversely
  `iterate_nd_zero` and `iterate_nd_one` walk along the rotations at `0` and
  `1`, so every half-edge at `0` reaches `0` and is reached from it
  (`reach_zero`), likewise at `1` with `2` (`reach_one`), and the two
  half-edges at a middle vertex are one step apart (`nd_reach`).
* Euler's formula, through the foundation's `planar_of_bounds`
  (`Complexity/Planar/Hypermap.lean`), which needs only lower bounds on the
  three cycle counts and an upper bound on the components
  (`bicliqueMap_planar`): at least `2r` edge cycles
  (`cycleCount_graphEdge_ge`); at least `r + 2` node cycles, since the
  half-edges `0`, `2`, `4j + 1` have pairwise different `nd`-invariant labels
  `vert` (`cycleCount_ge`); at least `r` faces, since the half-edges `4j` have
  pairwise different `fc`-invariant labels `faceOf` (`faceOf_fc`); and at most
  one component, since every half-edge other than `0` reaches a smaller one in
  at most two steps (`componentCount_le`). For `r ≥ 1`,
  `2 · 1 + 4r ≤ 2r + (r + 2) + r + 1`, so the genus is zero; `r = 0` is the empty
  graph.

`biclique_planar r : Complexity.PlanarGraph (biclique r)` assembles the three
conditions, and `biclique_planar_family` adds it to the counts and the two cost bounds.
