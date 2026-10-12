# How the proofs work

Names are in the namespace `STACS2027` unless qualified otherwise; files are under
`Outerplanar/`. Throughout, a graph is a list of entries (pairs of natural numbers); its
simple graph has the edges `edge u v = (min u v, max u v)` with `u ≠ v` that occur in the
list (`Adj g u v`), as in the `cpap-np-hardness` formalization. `m = |g|` is the number of entries.

The sixteen compared theorems use only the hypotheses in their statements. Their main
proof chains include:

* **Lemma 19, third sentence** (`twoConnectedK23_structure`, in combinatorial form: a 2-connected
  `K_{2,3}`-minor-free graph is a `K₄` or has a Hamiltonian cycle with no two crossing edges),
  the result the manuscript cites, is proved by a longest-cycle argument (§1a).
* **Lemma 19, first two sentences** (`outerplanar_block_structure`): outerplanar drawings (`OuterplanarDrawing`,
  planar rotation systems with every vertex of a component on one face) are exactly the
  graphs without `K₄` and `K_{2,3}` minors, by an explicit construction, closure under minors,
  Euler's formula for hypermaps and a face count for `K₄` and `K_{2,3}` (§1b).
* **Lemma 24** is a direct minor argument (`Minors.lean`).
* **Theorem 20**: block decomposition by a depth-first search, Lemma 19 on each block,
  Algorithm 4 (Lemma 25, from the `cpap-minor-free` formalization) on the outerplanar blocks, the
  fixed assignment on the `K₄` blocks, and the blockwise combination (`cpap-minor-free`'s
  `hasAssignment_blocks`).
* **Theorem 21 / Lemma 35**: an algorithm `Algo.solve k g` written as executable Lean
  functions, proved to output an optimal assignment (`Algo.solve_optimal`, through Lemma 34),
  and a program `RAM.Main.k23Prog k` of the unit-cost RAM proved to output exactly
  `Algo.solve k g` within `RAM.Main.Ck23 k * (m + 1)` steps, accessing only the addresses
  below `RAM.Main.Ck23 k * (L + m + 1)` (`RAM.Main.k23Prog_computes`, `L = RAM.labelBound g`).
  `k23_linear_ram` and `outerplanar_linear_ram` (`LinearK23.lean`) combine the two with `twoConnectedK23_structure`
  (and, for Lemma 35, with `outerplanarDrawing_iff_outerplanar`). The intermediate theorems
  that take the third sentence of Lemma 19 as a hypothesis `hL : TwoConnectedK23Structure`
  (`Algo.solve_optimal`, `RAM.Main.k23Prog_computes`, `k23_perfect_of_structure`,
  `k23_linear_ram_of_structure`, …) are instantiated with `twoConnectedK23_structure`.
* **Lemmas 27 and 29, and the supporting cycle-count bounds** (`IsPolygon.euler_face_count`, `IsPolygon.cycle_subtree_bij`,
  `IsPolygon.cycle_subtree_bij_simpleCycles`, `IsPolygon.face_cycle_bound`, `IsPolygon.edge_cycle_bound`): the
  weak dual in the manuscript's terms (face boundaries, the boundary map, subtrees), proved in
  the polygon model (§5a). The algorithm does not use them; it uses the face decomposition
  of §5 and the separate bounds of §7.

## 1. Definitions and Lemma 24 (`Defs.lean`, `Minors.lean`, `Reach.lean`)

`Defs.lean` imports only Lean core (through cpap-np-hardness and cpap-minor-free) and holds
every definition the statements of Lemma 24, Theorems 20 and 21 and Lemma 35 use (besides
the machine and outerplanar drawings, `OuterplanarDef.lean`): walks within a vertex set (`WalkWithin`),
`ConnectedWithin`, `TwoConnected` (at least three vertices, connected, connected after
deleting any vertex), `HasMinor g size h` (nonempty, pairwise disjoint, connected branch
sets with an edge of `g` between the branch sets of the ends of every edge of `h`), `k23`,
`K23MinorFree`, `Outerplanar` (no `K₄` and no `K_{2,3}` minor), `IsK4Graph`,
`OuterplanarHam g ham` (a Hamiltonian cycle of the simple graph with respect to whose
order no two edges cross), `TwoConnectedK23Structure`, `IsMinCost` and `OptimalAssignmentOutput`.

`common_neighbours_le_two`: three common neighbours `a, b, c` of `u ≠ w` give a `K_{2,3}` subgraph, i.e. a
`K_{2,3}` minor with singleton branch sets (`hasMinor_of_embedding`). For a loop-free edge
list this is `cpap-minor-free`'s `CommonNeighbourBound` (`commonNeighbourBound_of_k23MinorFree`).
`HasMinor.mono` (minors of subgraphs) and `IsK4Graph.hasMinor` are used later. `Reach`
is reachability within a set as an inductive relation, equivalent to `ConnectedWithin`.

## 1a. Lemma 19, third sentence (`TwoConnectedK23Cycles.lean`, `TwoConnectedK23Structure.lean`)

`TwoConnectedK23Structure` (`Defs.lean`) states: every `TwoConnected`, `K23MinorFree` graph is a `K₄`
(`IsK4Graph`) or has a Hamiltonian cycle with respect to which no two of its edges cross
(`OuterplanarHam`). This is the combinatorial content that the manuscript draws from
ANONYMIZED, ANONYMIZED, ANONYMIZED and ANONYMIZED (every 2-connected `K_{2,3}`-minor-free graph is
outerplanar or `K₄`) together with the standard structure of 2-connected outerplanar graphs
(an outer Hamiltonian cycle whose other edges are non-crossing chords). `twoConnectedK23_structure : TwoConnectedK23Structure`
proves it for the formal notions (2-connectivity, minors by branch sets, `OuterplanarHam`),
by a longest cycle:

* **Tools** (`TwoConnectedK23Cycles.lean`, namespace `K23Struct`). Walks within a set are chains of the
  adjacency (`K23Struct.walkWithin_iff`), so Mathlib's `List.IsChain` lemmas apply; a walk leaving a
  set exits through an edge (`Reach.exit`) and shortens to a path (`Reach.exists_path`);
  `K23Struct.IsCyc g K` (at least three distinct vertices, cyclically consecutive ones adjacent) is
  invariant under rotation, bounded in length (`K23Struct.IsCyc.length_le`) and a cycle in the sense
  of cpap-np-hardness (`K23Struct.IsCyc.isCycle`); replacing an edge `uv` of a cycle by a path from `u` to
  `v` off the cycle makes it longer (`K23Struct.IsCyc.extend`); five disjoint connected vertex lists
  with the right edges are the branch sets of a `K_{2,3}` minor (`K23Struct.hasMinor_k23_of`).
* **A cycle exists** (`K23Struct.exists_isCyc`): a vertex has two neighbours, joined by a path
  avoiding it (2-connectivity).
* **A longest cycle is Hamiltonian** (`K23Struct.longer_or_minor`, `K23Struct.exists_ham`): a vertex `h`
  off a cycle `C` reaches `C`, and reaches `C` minus any one vertex, which gives two
  attachments `x ≠ y` on `C` joined through `h` by a path `Q` off `C`. If `x`, `y` are
  consecutive on `C`, `Q` lengthens `C`; otherwise `{x}`, `{y}`, `Q` and the interiors of the
  two arcs of `C` between `x` and `y` are the branch sets of a `K_{2,3}` minor.
* **Crossing chords** (`K23Struct.crossing`, `K23Struct.crossing_core`, `K23Struct.isK4Graph_of`): if two edges
  `ac`, `bd` cross with respect to the Hamiltonian cycle and an arc between consecutive ends
  has an inner vertex, the arcs give a `K_{2,3}` minor; otherwise the cycle is `a, b, c, d`
  and the graph is the `K₄` on these vertices.
* Otherwise no two edges cross: `OuterplanarHam` (`twoConnectedK23_structure`).

## 1b. Lemma 19, first two sentences (`OuterplanarDef.lean` through `OuterplanarCharacterization.lean`)

* **The definition** (`OuterplanarDef.lean`). `OuterplanarDrawing g` says that the simple graph
  of `g`, listed once as `simpleEdges g`, has an `OuterplanarEmbedding`: a hypermap on the
  half-edges (half-edges `2i`, `2i + 1` the ends of edge `i`) whose `edge` permutation pairs
  them and whose `node` cycles are the half-edges at a common vertex, planar in the
  foundation's sense (genus `0` by the Euler formula, `Complexity.Hypermap.Planar`), such that
  every connected component has a face meeting every vertex of the component. It does not
  depend on the order of the edges, on vertex names or on repeated entries
  (`OuterplanarBasic.lean`: `RepEdges.outerplanarEmbedding_iff`, `outerplanarEmbedding_map_iff`).
* **Euler's inequality and parity** (`HypermapEuler*.lean`, `hypermapEuler : HypermapEuler`):
  for every hypermap, `eulerRhs ≤ eulerLhs` and the difference is even (ANONYMIZED's walkup
  induction in algebraic form: edge transpositions `moveE` and the rotation of the three
  permutations).
* **Construction** (`OuterplanarConstruct*.lean`, `outerplanarDrawing_of_minorFree`): a graph
  without `K₄` and `K_{2,3}` minors gets explicit spherical outerplanar embeddings, by
  induction on the vertices: the polygon embedding of a 2-connected piece with an outerplanar
  Hamiltonian cycle (from `twoConnectedK23_structure`), gluing at a cut vertex and disjoint unions (using
  the planar gluing of the `cpap-np-hardness` formalization). `OuterplanarHam.outerplanarEmbedding` and
  `twoConnected_outerplanar_or_k4` give the third sentence in the drawing form.
* **Closure under minors** (`OuterplanarMinor*.lean`, `OuterplanarDrawing.of_hasMinor`): a
  minor of a graph with an outerplanar drawing has one, by contracting an edge of a branch set
  (renaming its end) and deleting the remaining edges (Euler's inequality keeps the genus `0`).
* **The excluded minors** (`OuterplanarK4K23.lean`): `K₄` and `K_{2,3}` have no outerplanar
  drawing: a connected outerplanar embedding has, by Euler's formula, at least
  `2 + |E| − |V|` faces, one of them with at least `|V|` darts and the others with at least the
  girth; for `K₄` (`3 · 3 + 4 > 12`) and `K_{2,3}` (`4 · 2 + 5 > 12`) the darts do not suffice.
* **Lemma 19** (`OuterplanarCharacterization.lean`): `outerplanarDrawing_iff_minorFree` (the two directions),
  `outerplanarDrawing_iff_outerplanar` (agreement with the minor condition `Outerplanar` used
  by the algorithms), and `outerplanar_block_structure`, the three sentences together.

## 2. Theorem 20 (`DFS.lean`, `Palm.lean`, `BlockTheory.lean`, `BlockConn.lean`, `Degenerate.lean`, `PerfectK23.lean`)

* **Depth-first search** (`DFS.lean`). `DFS.step` is an iterative search with explicit
  neighbour lists, a stack, a pointer per vertex to the next neighbour to examine, preorder
  numbers and parents, exactly as the machine runs it. The invariant `DFS.Inv` says that
  the stack is a tree path and that every examined neighbour of an open vertex, and every
  neighbour of a finished one, is an ancestor or a descendant. The measure `DFS.mu`
  decreases at every step (`DFS.mu_step`), so `DFS.final` (the state after `mu` steps) has
  halted (`DFS.halted_run`, `DFS.final_halted`) and its parents form a palm tree (`DFS.palm_of_final`); hence
  `exists_palm`: every graph has a palm tree.
* **Palm trees and heads** (`Palm.lean`). A palm tree has parents with decreasing preorder
  numbers and every edge between an ancestor and a descendant. A non-root `c` is a *head*
  (`Palm.IsHead`) when every edge leaving the subtree of `c` ends at the parent of `c`
  (ANONYMIZED and ANONYMIZED's `low(c) ≥ pre(par c)`); `Palm.head x` is the first head on the
  path from `x` to the root.
* **Blocks** (`BlockTheory.lean`, `BlockConn.lean`). An edge lies in the block of the head
  of its lower end (`Palm.block h`). Every simple cycle lies in one block
  (`Palm.cycle_in_block`, by the separation `Palm.cycle_sep`); a block with a third vertex
  besides `h` and `par h` is 2-connected (`Palm.twoConnected_block`): tree paths up to
  `par h` stay in the block (`Palm.reach_up`), and a deleted vertex `z` is bypassed through
  an edge from the subtree of the child of `z` to a proper ancestor of `z`, which exists
  because that child is not a head.
* **Outerplanar blocks are 2-degenerate** (`Degenerate.lean`). In a polygon with
  non-crossing chords every nonempty vertex set has a vertex with at most two neighbours in
  it (`IsPolygon.polygon_degenerate`); hence for a graph with an outerplanar Hamiltonian
  cycle (`outerplanarHam_degenerate`), which therefore has a degree-two elimination order
  in the cpap-minor-free interface (`eliminationOrder_of_degenerate`).
* **The theorem** (`PerfectK23.lean`). The blocks `Palm.blocks` of a palm tree are
  edge-disjoint, contain every cycle and together have the edges of `g`
  (`Palm.blocks_flatten`, `Palm.blocks_edgeDisjoint`, `Palm.blocks_cycles`); minors of a
  block are minors of `g` (`Palm.block_k23MinorFree`). A block without a third vertex has
  no cycle (`hasAssignment_of_no_cycle`, `Palm.block_no_cycle`); otherwise Lemma 19 makes it
  a `K₄` (perfect by `cpap-minor-free`'s `k4_perfect`, transported by `IsK4Graph.relabel`,
  `IsK4Graph.hasAssignment_iff`) or gives an outerplanar Hamiltonian cycle, and then
  Algorithm 4 (`cpap-minor-free`'s `algorithm4_perfect`, Lemma 25) applies with the elimination
  order above and Lemma 24 (`perfect_of_outerplanarHam`). `cpap-minor-free`'s
  `hasAssignment_blocks` adds the blockwise costs: `k23_perfect_of_structure`, and with
  `twoConnectedK23_structure`, `k23_perfect`.

## 3. The polygon model (`Polygon.lean`, `Transfer.lean`, `Convex.lean`)

Appendix F works with an outerplanar embedding, its bounded faces and its weak dual. The
formalization replaces the embedding by its combinatorial content: Lemma 19 provides a
Hamiltonian cycle with respect to which no two edges cross, and renaming each vertex by its
position on that cycle (`posGraph`, `isPolygon_posGraph`) gives a **polygon**,
`IsPolygon g n := OuterplanarHam g (List.range n)`: the positions `0, …, n − 1` in order
form the outer cycle, every other edge is a chord, and no two edges cross. The problem
depends only on the simple graph and is invariant under the renaming
(`hasAssignment_proper`, `hasAssignment_posGraph`, `isMinCost_posGraph`).

In a polygon every simple cycle is **convex** (`IsPolygon.convex_of_isCycle`): an edge
`pq` of a cycle has all other vertices of the cycle on one side (a walk from inside
`(p, q)` to outside would cross `pq`, `IsPolygon.walk_side`, `IsPolygon.cycle_side`), so the
cycle has the edges of its sorted vertex list. The simple cycles are thus, up to their edge
sets, the `ConvexCycle`s: strictly increasing lists of at least three positions whose
cyclically consecutive entries are adjacent; two convex cycles with the same edges are equal
(`ConvexCycle.eq_of_sameCycle`).

## 4. Faces and the segment tree: the weak dual (`Segments.lean`, `Faces.lean`)

* **Segments** (`IsPolygon.segs`) are the edges `(a, b)` with `a + 2 ≤ b`: the chords and
  the outer edge `(0, n − 1)`. Each bounds one bounded face from above: the face whose
  parent chord it is, or the root face for `(0, n − 1)`. Edges are laminar
  (`IsPolygon.laminar`: nested or with disjoint interiors), so ordered by containment the
  segments form a rooted tree (`IsPolygon.segTree`, root `IsPolygon.root`), whose children
  are the maximal proper sub-segments (`IsPolygon.mem_children_iff`, sizes decrease,
  `IsPolygon.child_size_lt`). This is the weak dual of Definition 26, rooted at the face on
  `(0, n − 1)`.
* **Faces** (`Faces.lean`). The face below `s = (a, b)` has the vertices `faceVerts g n s`:
  the positions of `[a, b]` strictly inside no other segment within `s` (`IsFaceVert`).
  They increase from `a` to `b`; consecutive face vertices are adjacent: a side
  `(x, x + 1)` or a child segment (`IsPolygon.face_gap`,
  `IsPolygon.adj_of_infix_faceVerts`); every child is a pair of consecutive face vertices
  (`IsPolygon.child_iff`); a face has at least three vertices
  (`IsPolygon.three_le_length_faceVerts`) and its boundary is a convex cycle
  (`IsPolygon.faceVerts_convexCycle`). This is the content of Lemma 27 used here.
* **Tops and ownership.** The top of a convex cycle `u` is the segment `(u₀, u_last)`
  (`IsPolygon.top_mem_segs`), the face of least depth it encloses (the paper's `top(c)`). An
  edge is owned by the deepest face it bounds (`IsPolygon.own`, the paper's `E_{v_f}`,
  Lemma 30): a segment owns itself, a side `(a, a + 1)` is owned by the smallest segment
  containing it (`IsPolygon.own_spec`). A cycle through an edge owned by `s` has its top
  at `s` or above.

## 5. Region paths and their enumeration (`RegionPaths.lean`, `Enumerate.lean`)

A *region path* of an edge `(a, b)`, `a < b`, is a strictly increasing list from `a` to
`b` with adjacent consecutive entries (`IsRPath`). Closed by `(b, a)`, those with at least
three entries are exactly the convex cycles with top `(a, b)`
(`convexCycle_iff_isRPath`). The **face decomposition** `IsPolygon.isRPath_iff_joins` is
the form of the cycle–subtree correspondence (Lemma 29) used here: a region path of a
segment `s` is either `[a, b]` or visits every vertex of the face below `s` and is the
concatenation (`Joins`) of region paths between consecutive face vertices; a side has only
itself (`isRPath_side_iff`), and a child segment contributes, recursively, a region path of
the child. So a cycle with top `s` corresponds to the subtree of the weak dual that it
encloses, and its length is the sum of the lengths of its pieces.

`rpaths g n a b L` enumerates the region paths with `L` entries by recursion over the faces
(`joinPaths`, fuel `b − a`, `rpathsAux`): exactly the region paths
(`IsPolygon.mem_rpaths`), each once (`IsPolygon.nodup_rpaths`), at most `rpathBound L` of
them (`IsPolygon.length_rpaths_le`), where `rpathBound 0 = 2` and
`rpathBound (L + 1) = 1 + (L · rpathBound L + 1)^L` (a face that contributes to a path with
`L` entries has at most `L` vertices, and each of its slots carries fewer than `L` entries).
This bound depends on `L` alone, which is all the linear running time needs; it is much
cruder than the supporting cycle-count bounds (`4^k`) (values `2, 2, 4, 82, 15069224, ≈ 1.3·10³¹` for
`L = 0, …, 5`), which is proved separately (§5a) and not used by the algorithm's analysis.

## 5a. The weak dual: Lemmas 27–29 and the supporting cycle-count bounds (`WeakDual.lean`, `WeakDualBij.lean`, `WeakDualCount.lean`, `WeakDualFacts.lean`)

These files state Appendix F's weak-dual lemmas in the manuscript's terms, on a polygon
`IsPolygon g n` whose bounded faces are the segments (`IsPolygon.segs`, `r = |segs g n|`):

* **Definitions** (`WeakDual.lean`). `faceEdges g n s`: the edge set `∂f` of the face below
  `s` (the edges of the cycle `faceVerts g n s`); `bdry g n T`: the boundary
  `∂T = Δ_{f ∈ T} ∂f`, a `Finset.fold` of symmetric differences (`mem_bdry`: the edges lying
  on an odd number of faces of `T`); `encl g n u`: the faces enclosed by a cycle `u` (those all
  of whose vertices lie on `u`); `DualAdj g n s t`: the weak dual of Definition 26 (two distinct
  faces sharing an edge); `IsSubtree g n S`: the manuscript's `𝒮` (a nonempty set of faces
  any two of which are joined by a walk of adjacent faces in `S`, `Relation.ReflTransGen`).
  Facts: the edges of a face are `s`, its child segments and sides `(x, x + 1)`
  (`IsPolygon.mem_faceEdges_iff`); a segment lies on the faces `s` and its parent, a side on
  exactly one face (`IsPolygon.faces_of_seg`, `IsPolygon.faces_of_side`); two faces are
  adjacent in the weak dual iff one is the parent of the other in the segment tree
  (`IsPolygon.dualAdj_iff`), so the weak dual *is* the segment tree; and a set of faces is a
  subtree iff it is rooted (`IsPolygon.isSubtree_iff`: some node `r` such that every other
  node has its parent in the set).
* **Lemma 29** (`WeakDualBij.lean`). For a convex cycle `u` with top segment `(a, b)`, a
  segment is enclosed iff it lies within `(a, b)` and `u` has an entry strictly inside it
  (`IsPolygon.mem_encl_iff`, by non-crossing); the enclosed faces form a subtree rooted at the
  top (`IsPolygon.isSubtree_encl`) and `∂(encl u)` is the edge set of `u`
  (`IsPolygon.bdry_encl`: an edge lies on an odd number of enclosed faces iff it is an edge of
  `u`). Conversely every subtree `S` is `encl u` for a convex cycle `u` with
  `|u| + 2 (|S| − 1) = ∑_{f ∈ S} d_f` (`IsPolygon.exists_convex_of_isSubtree`, by the
  manuscript's induction removing a leaf of `S`: the face of the leaf is spliced into the
  cycle of the rest in place of its chord, `IsRPath.splice`). With
  `ConvexCycle.eq_of_edges` (a convex cycle is determined by its edge set) this gives
  `IsPolygon.cycle_subtree_bij` (surjectivity, well-definedness, inverse `encl`, injectivity, the
  length formula) and `IsPolygon.cycle_subtree_bij_simpleCycles` (the same for the simple cycles
  `IsCycle`, through convexity).
* **the supporting cycle-count bounds** (`WeakDualCount.lean`). A separate generating-function argument establishes per-face and per-edge cycle-count bounds: with the weight `(1/4)^(|p| − 1)` of a
  path with `|p| − 1` edges (`wt`, in `ℚ`), the region paths of an edge weigh at most `1/2`
  in total (`IsPolygon.sum_rpSet_le`, by the face decomposition: the edge itself weighs `1/4`,
  and the concatenations along the at least two slots of a face weigh at most `(1/2)²`); the
  region paths of a segment `t ⊋ s` enclosing `s` weigh at most half of those of the child of
  `t` above `s` (`IsPolygon.encSum_le_child`); summing along the chain of segments from `s` to
  the root, the convex cycles enclosing `s` weigh at most `1/2` (`IsPolygon.chainSum_add_le`),
  so at most `4^(k−1)/2 ≤ 4^k` of them have length `k` (`IsPolygon.face_cycle_bound`). An edge lies
  on at most two faces (`IsPolygon.faces_le_two`), and a cycle through it encloses one of
  them, whence `IsPolygon.edge_cycle_bound` (`2 · 4^k`).
* **Lemmas 27 and 28** (`WeakDualFacts.lean`). The edges of a polygon are the `n − 1` sides
  `(i, i + 1)` and the segments (`IsPolygon.polyEdges_eq`), whence the face count
  `r + n = m + 1` (`IsPolygon.euler_face_count`; in the model a counting identity, which needs
  neither planarity nor Euler's formula). The weak dual's edges are the parent–child
  pairs (`dualEdges`, `IsPolygon.dualAdj_iff_dualEdges`); the faces `p`, `c` of a dual edge
  share exactly the chord `c`, and `(p, c) ↦ c` is a bijection onto the chords (the segments
  other than `(0, n − 1)`), so the weak dual has `r − 1` edges (`IsPolygon.chord_dualEdge_bij`) and,
  being connected, is a tree (`IsPolygon.weakDual_tree`: the fact that Appendix F cites from
  ANONYMIZED, ANONYMIZED and ANONYMIZED, proved in the polygon model). `∂T ≠ ∅` for a nonempty `T`: the
  segment of a largest face of `T` lies on no other face of `T` (`IsPolygon.bdry_ne_empty`);
  `deg_{∂S}(v) ∈ {0, 2}` for a subtree `S`, since `∂S` is the edge set of a cycle by Lemma 29
  (`IsPolygon.bdry_deg`). A segment without children (a leaf of the weak dual other than
  the root, which exists when `r ≥ 2`, `IsPolygon.exists_leaf`) has the face
  `s.1, s.1 + 1, …, s.2`, whose only chord is `s`, whose only neighbour in the weak dual is
  its parent, and whose inner vertices have degree two (`IsPolygon.leaf_face`, parts 1 and 2 of
  the manuscript's Lemma 28). `LeafDelete.lean` defines the actual induced deletion of
  these internal vertices. `leaf_delete_edges` identifies the removed path edges;
  `leaf_delete_outerplanar` inherits a drawing; `leaf_delete_hamiltonian` constructs an
  outer Hamiltonian cycle enclosing exactly the retained original faces, with every
  retained face cycle unchanged and the parent chord on its boundary; and
  `leaf_delete_twoConnected` proves 2-connectivity. `FaceTransport.lean` proves that
  bounded faces are exactly chordless simple cycles, first for the existing polygon
  faces and then for any outerplanar Hamiltonian embedding via its positional polygon.
  Induced deletion preserves exactly the surviving chordless cycles, giving exact
  bounded-face bijections and weak-dual adjacency restriction. `RootLeaf.lean` covers a
  root leaf by retaining the unique child's interval; it also proves that the root face
  has exactly that chord and that its internal outer-path vertices have degree two.
  `LeafFaceDeletion.lean` proves the removed face boundary minus its chord is a path of
  at least two edges. Its `leaf_face_deletion` bundles every clause of Lemma 28 (3) with
  the manuscript's `r ≥ 2` hypothesis for every actual weak-dual degree-one leaf.

## 6. The tree dynamic program and Lemma 34 (`TreeDP.lean`, `DPCorrect.lean`)

`TreeDP` is an abstract dynamic program on a rooted tree (`TreeDP.Tree`: subtrees, children,
a size decreasing to the children). A `TreeDP.Problem` has variables `X` with values in a
finite `D`, each with a *top* node, and cost terms (factors) with an *owner* node and a
scope of variables whose tops are ancestors of the owner (or the owner). `dp v α` minimizes,
over the values of the variables with top `v`, the cost of the factors owned by `v` plus the
`dp` values of the children; the other variables keep their values from `α`.

* `TreeDP.Problem.dp_eq_min`: `dp v α` is the least cost of the factors owned in the
  subtree of `v`, over the values of the variables whose top is in the subtree, the others
  from `α`; at the root it is the optimum (`TreeDP.Problem.dp_root`).
* `TreeDP.Problem.dp_congr`: `dp v α` depends on `α` only through the *boundary* variables
  of `v` (`TreeDP.Problem.boundary`: top outside the subtree, in the scope of a factor owned
  inside it), the paper's `B_{v_f}`.
* `TreeDP.Problem.top_eq_or_mem_boundary` and `TreeDP.Problem.boundary_child` are Lemmas 32
  and 33 in abstract form. The manuscript proves them through Lemma 31 (where `∂⁻¹(c)` lies
  relative to the subtree of a face); here that is the containment of segments behind the
  tops and the hypothesis `scope_top`. The separate face-set, top and parent-boundary statements
  of Lemma 31 are in `NamedHoles.lean`. Its graph-edge dichotomy is `cycle_child_dichotomy`,
  proved using the parent-boundary criterion and `own_within_iff`.

`polygonProblem` (`DPCorrect.lean`) instantiates it on the segment tree: the variables are
the convex `k`-cycles (`convexCycles`, type `CycVar`), a value `j : Fin k` omits the `j`-th
vertex; the top of a cycle is its top segment; the factors are the edges (`polyEdges`), each
owned by `IsPolygon.own`, with cost `binom(l(e), 2)` (`pairCount (cycLoad γ e)`); the scope
of an edge is the set of cycles through it. `IsPolygon.hasAssignment_iff_family` and
`IsPolygon.total_eq` identify assignments of `CPAP(g, k)` with values `γ` and their costs.

* `IsPolygon.dp_root_optimal`: `dp root α` is the optimum `C*` (`IsMinCost g k`);
* `IsPolygon.dp_table_correct`: every entry `dp v α` is the least cost of the edges owned in
  the subtree of `v` over the values extending `α` (the paper's statement of Lemma 34).

## 7. The algorithm `Algo.solve` and its optimality (`Algo/`)

The algorithm is written as Lean functions that are, phase by phase, what the machine
computes (the machine's proofs show that its memory holds these functions' values).

* **Graph-level phases** (`Algo/Graph.lean`). `proper` (the entries written smaller end
  first, `e.1 < e.2`), `labels` (in order of first appearance), `idOf`, `numV`, `idEdges`
  (the deduplicated edges between the ids `0, …, numV g − 1`), `nbOf` (neighbour lists in
  the order of the edges), `dfsOf` (the search of §2 from the roots `0, …, numV g − 1`),
  `lowOf` (low points, a fold over the reversed preorder), `headOf` (heads, a fold over the
  preorder: `v` is a head iff `pre (par v) ≤ low v`), `blocksOf` (the edges bucketed by the
  head of their lower end), `solveWith` (the block outputs concatenated, ids replaced by
  labels). `Algo/LowPoint.lean` proves them right: the low points are ANONYMIZED and ANONYMIZED's
  (`Algo.isLow_lowOf`), the heads those of the palm tree (`Algo.isHead_iff_lowOf`,
  `Algo.headOf_dfsOf`), and `blocksOf g` lists the blocks `P.block h`
  (`Algo.blocksOf_eq`).
* **Combination** (`Algo/Combine.lean`). Optimal outputs of the blocks of a palm tree
  concatenate to an optimal output of the graph (`Algo.optimalAssignmentOutput_blocks`:
  blocks are edge-disjoint, every cycle lies in one, paths in different blocks share no
  edge, so costs add); outputs transfer along injective renamings
  (`Algo.optimalAssignmentOutput_relabel`) and from ids back to labels
  (`Algo.optimalAssignmentOutput_labels`); minors of the id graph are minors of `g`.
* **The block solver** (`Algo/Solve.lean`, `Algo/K4Out.lean`). `Algo.solveBlock k E`: with
  `vs = blockVerts E` (the block's vertices) and local ids `0, …, |vs| − 1`: nothing if
  `|vs| ≤ 2`; the fixed output `Algo.k4Out` if `|vs| = 4` and `|E| = 6` (a `K₄`: for `k = 3`
  the four triangles, for `k = 4` the three four-cycles written from the vertices omitted
  by `cpap-minor-free`'s `k4Assignment`, nothing otherwise; optimal of cost zero,
  `Algo.optimalAssignmentOutput_k4Out`); otherwise the outerplanar case: the Hamiltonian
  cycle `ham = Ear.earHam` of the local graph, the polygon `localEdges ham L`, and
  `Poly.polyOut` on it, renamed back. `Algo.solve k g = solveWith (solveBlock k) g`.
* **Ear elimination** (`Algo/Ear.lean`, `Algo/EarCycle.lean`, `Algo/EarState.lean`,
  `Algo/EarInv.lean`, `Algo/EarCorrect.lean`, `OuterplanarSym.lean`). The Hamiltonian
  cycle of an outerplanar block is found by eliminating degree-two vertices: a stack holds
  vertices of degree two; while more than three vertices are alive, pop `v`; if it is alive
  with degree two, find its alive neighbours `u`, `w`, kill `v`, log `(v, u, w)` and replace
  the path `u v w` by the edge `u w` (lowering the degrees of `u` and `w` if `uw` already
  exists, else adding a *virtual* edge). The three survivors form a triangle; the logged
  vertices are reinserted in reverse order between their two logged neighbours (a successor
  function, `Algo/EarCycle.lean`), and the cycle is read off. Termination: the potential
  `Ear.pot = 3 · cnt + |stack|` drops at every iteration (`Ear.pot_step`, `Ear.loop_stopped`).
  Correctness: the invariant `Ear.Inv` carries a *ghost* Hamiltonian cycle without crossings
  (`OHam`, `OuterplanarSym.lean`) of the current graph; the stack is never empty while more
  than three vertices are alive (`Ear.Inv.stack_ne_nil`, by 2-degeneracy), an elimination
  deletes a vertex whose only neighbours are its two neighbours on the ghost (`OHam.drop_head`),
  and the reinsertions rebuild a rotation of the original cycle or of its reversal:
  `Ear.earHam_correct`.
* **The polygon solver** (`Algo/Poly.lean` and the files `Poly*`, `FaceWalk`, `Digits`,
  `TreeDPArgmin`). On a polygon `pg` on `n` positions: the neighbour lists `nbP`, the
  segments `segEnum` and `segOrder` (by size, children first), the face slots (pairs of
  consecutive face vertices; `Poly.faceWalk_eq`: the machine's walk along the face lists
  them), the region paths `Poly.rpF` built by folding `Poly.extendParts` over the slots
  (memoized per segment by the machine), the **pool** (`Poly.pool`, the convex `k`-cycles
  grouped by top segment, `Poly.mem_pool`), the boundary cycles `Poly.bnd s` (both ends of
  `s` on the cycle, another top: `Poly.mem_boundary` identifies them with
  `TreeDP.Problem.boundary`) and the cycles with top `s` (`Poly.topIdx`), configurations as
  base-`k` numbers (`cfg`, `enc`, `Algo/Digits.lean`), the tables `Poly.tabArg` (`DP[s, α]`
  and the first minimizing `β`), the top-down `Poly.backtrack`, the omitted index
  `Poly.valOf` of every pool cycle, and `Poly.polyOut` (each pool cycle rotated to start at
  its omitted vertex). Bounds: `Poly.length_rpF_le`, `Poly.length_topIdx_le`
  (`rpathBound k` cycles with top `s`), `Poly.length_bnd_le` (at most
  `(k − 2) · rpathBound k` boundary cycles: their tops are nested segments strictly above
  `s`, and a boundary cycle with the largest of these tops visits both ends of all of them).
  Correctness: `Poly.polyFacts` collects the combinatorial facts (`Poly.PolyFacts`);
  `Poly.tabArg_spec`: the tables compute `dp` of `polygonProblem` (`Algo/PolyDP.lean`); the
  backtracking attains the minimum at every segment, so its values are optimal
  (`Poly.isMinCost_total_chosen`, `Algo/PolyBacktrack.lean`, with
  `TreeDP.Problem.total_eq_dp_of_local`); `Poly.optimalAssignmentOutput_polyOut`.
* **Optimality** (`Algo/SolveCorrect.lean`, `Algo/SolveOptimal.lean`). Each block of the
  palm tree of the id graph is 2-connected when it has three vertices; given Lemma 19, a
  block with three or more vertices other than a `K₄` (which has four vertices and six edges,
  `Algo.IsK4Graph.counts`) has an outerplanar Hamiltonian cycle, transported to local ids, so the
  ear elimination succeeds and its positions form a polygon (`Algo.isPolygon_localEdges`):
  `Algo.optimalAssignmentOutput_solveBlock`; the blocks combine (`Algo.solve_correct`).
  `Algo.solve_optimal`: given Lemma 19, `Algo.solve k g` is an `OptimalAssignmentOutput`
  for every `k ≥ 3` and every `K_{2,3}`-minor-free `g`; with `twoConnectedK23_structure`,
  `STACS2027.solve_optimal` (`LinearK23.lean`) states it with the structure parameter discharged by twoConnectedK23_structure, retaining k≥3 and K23MinorFree g.

## 8. The RAM implementation (`RAM/`)

### The machine and its logic

`RAM/Model.lean` is the unit-cost RAM of the `cpap-approximation-hardness` formalization, copied verbatim: registers and
memory `Nat → Nat`, a write-only output, `const add sub load store write` (indirect load
and store, truncated subtraction, no multiplication), `seq`, `ifz` and `loop a body`
(`while reg a ≠ 0`); `Exec s c t c'` counts every instruction and every test as one step.
`RAM/Spec.lean` (copied from cpap-approximation-hardness) runs loop-free code (`run`). On top of it:

* `RAM/HT.lean`: Hoare triples with step bounds, `RAM.HT s P Q b` (from every `c` with
  `P c`, `s` halts within `b` steps in a `c'` with `Q c'`), and loop rules with a potential
  for amortized bounds;
* `RAM/Frame.lean`: syntactic footprints (`wregs`, `stores`, `writes`), the frame property
  of every run (`RAM.Exec.frame`), independence of assertions from registers (`RAM.Indep`,
  `RAM.RegIndep`, the tactic `indep`), the frame rules;
* `RAM/Layout.lean`: register conventions (`rZERO`, `rONE`, the free pointer `rFREE`, the
  macro temporary `rT`; global registers `10`–`99` by phase; scratch from `100`), memory
  predicates (`RAM.Arr`, `RAM.Tab`, `RAM.ZeroFrom` — fresh memory is zero —, `RAM.SameOn`),
  matrix cells `u * N + v`, and the input `RAM.graphInput g = m :: e₁.1 :: e₁.2 :: …`;
* `RAM/Lib.lean`: macros (moves, constants, indexed loads and stores, comparisons, counted
  and `while` loops, multiplication by repeated addition, allocation) with their equations
  and Hoare rules.

**Memory.** `RAM/Bounded.lean` restricts runs to the addresses below a bound `S`
(`RAM.ExecB S`: the inductive `Exec` with the premise `reg a < S` on every `load` and
`store`) and defines `RAM.ComputesIn s input output time space`. The result of a bounded run
does not depend on the memory at or above the bound (`RAM.ExecB.congr`,
`RAM.ComputesIn.of_eqBelow`), so the zero-initialization of the memory beyond the bound is
never used. `RAM/BoundedHT.lean` and `RAM/BoundedLib.lean` give the bounded twins `HTB S` of
the Hoare triples and of the macro rules, with the address obligations `AddrOK` of loop-free
code (tactics `addr_ok`, `addr_simp`); every phase below is proved with them, together with a
bound on its fresh memory (the growth of the free pointer `rFREE`), so the whole program
touches only the addresses below `RAM.Main.Ck23 k * (L + m + 1)`, `L = RAM.labelBound g`. No
table is indexed by pairs of vertices or positions; the only table indexed by labels is the
dictionary of R0, which is never initialized (its cells are written before they are read).

### Phases and interfaces

`RAM.Main.k23Prog k` (`RAM/Main.lean`) is

```
R0 ; R1 ; R2 ; R3 ; blockLoop (Block.blockProg k EarR.earProg
                                 (PolySolver.polySolver k (P2.poly2 k) (P3.poly3 k)))
```

The states between phases are fixed in advance (`RAM/Iface.lean`): `RAM.GraphBase`,
`RAM.R1Post`, `RAM.R2Post`, `RAM.R3Post` (graph level), `RAM.BlockIn` / `RAM.BlockSpec`
(the block solver), `RAM.EarIn` / `RAM.EarSpec` (the ear elimination), `RAM.PolyIn` /
`RAM.PolySpec` (the polygon solver); `RAM/PolyIface.lean` fixes `RAM.Poly1Post`,
`RAM.Poly2Post`, `RAM.Poly3Post` between the polygon phases. Each phase is verified against
its interfaces, with explicit register footprints and memory frames (every phase stores only
at or above its initial free pointer), and the proofs relate the memory to the functions of
§7 through *step lemmas* on prefixes (a loop after `j` rounds holds the fold over the first
`j` items).

* **R0, parsing** (`RAM/R0*.lean`, `RAM.R0.r0_spec`, `300 (m + 1)` steps, the addresses below
  `20 (L + m + 1)`): the largest label, a dictionary `label ↦ id + 1` indexed by the labels
  (written before it is read), the labels in order of first appearance, and the id edges
  `idEdges g`, deduplicated without an adjacency matrix by the module `RAM.PairIds`
  (`pairLeads`: the pairs sorted by two stable counting sorts, the first occurrence of each
  kept).
* **R1, neighbour lists and search** (`RAM/R1*.lean`, `RAM.R1.r1_spec`, `600 (m + 1)` steps,
  `18 (m + 1)` fresh cells):
  degree counts, prefix sums and the CSR neighbour lists of `idEdges g`, then the search
  `DFS.step` simulated one step per round; at most `DFS.mu = 3N + 2|E|` rounds.
* **R2, low points and heads** (`RAM/R2*.lean`, `RAM.R2.r2_spec`, `240 (m + 1)`): the two
  folds of `lowOf` and `headOf` over the preorder; `6 + 90|E| + 33N + 3 + 38N + 3` steps.
* **R3, blocks** (`RAM/R3*.lean`, `RAM.R3.r3_spec`, `100 (m + 1)`): a stable counting sort
  of the id edges by the head of their lower end, giving `blocksOf g` concatenated with
  their start offsets.
* **R4, the block loop** (`RAM/MainLoop.lean`, `RAM.Main.blockLoop_spec`): for every head
  `h`, the block solver on the block `h`; with a block solver of constant `CB`, at most
  `CB (|E| + N) + 11N + 6 ≤ RAM.Main.CL CB · (m + 1)` steps, `CL CB = 3 CB + 28`
  (`∑_h |E_h| = |E|`, `N ≤ 2m`, `|E| ≤ m`). `RAM.Main.blockGood_blocksOf`
  (`RAM/MainGood.lean`): given Lemma 19, every block satisfies the block solver's hypothesis
  `RAM.BlockGood` (the polygon branch receives a polygon).
* **The block solver** (`RAM/Block*.lean`, `RAM.Block.blockProg_spec`): copies of the edges,
  the vertices `blockVerts E` with local ids in a scratch array `LOC` (reset afterwards, so
  the memory below the initial free pointer is restored), the local edges, and the dispatch:
  nothing, the `K₄` patterns, or the polygon branch (the ear elimination, the positions
  `POS[ham[p]] := p`, the polygon, the output map `p ↦ label`, the polygon solver). Constant
  `RAM.Block.CB k CE CP = 3 CE + 3 CP + 6 |(Algo.k4Base k).flatten| + 200` per `|E| + 1`.
* **The ear program** (`RAM/Ear*.lean`, `RAM.EarR.earProg_spec`, `700 (N + |L| + 1)` steps):
  in `O(N + |L|)` time and memory, without an `N × N` matrix: the vertices of degree at most
  two are peeled first (`Algo/EarPeel.lean`), which orients every edge of a graph with an
  outerplanar Hamiltonian cycle (`Ear.peel_orient`), so that the elimination asks the
  orientation, not a matrix, whether two vertices are adjacent; adjacency as linked lists with
  prepending (`EarLL.lean`), the stack, the log and the successor array. The elimination loop
  is amortized by a potential (an elimination of `v` pays for the scan of its list);
  reconstruction follows the log backwards (`RAM.EarR.recon_spec`).
* **The polygon solver** (`RAM/PolySolver.lean`, `RAM.PolySolver.polySolver_spec`), on a
  polygon with `n` positions and `|pg|` edges, constant `RAM.Main.CP k = CP1 + CP2 k +
  CP3 k + CP4 k` per `n + |pg| + 1`:
  * **P1, structure** (`RAM/Poly1*.lean`, `RAM.P1.poly1_specB`, `CP1 = 450`, at most
    `27 |pg| + 8 n + 5` fresh cells): sorted neighbour lists by two stable counting sorts of
    the arcs; the segments in the order `segEnum`, then `segOrder` (a counting sort by size)
    and their ids (the inverse permutation); the faces, walked by largest neighbours
    (`Poly.faceWalk_eq`), and slot ids parallel to the face vertices. No table is indexed by
    pairs of positions.
  * **P2, cycles** (`RAM/Poly2*.lean`, `RAM.P2.poly2_spec`, `RAM.P2.CP2 k`): the region
    paths of every segment, children first, memoized (the final partial paths of a child are
    stored and scanned by its parent); the pool with the starts of each top segment's cycles;
    the boundary lists by a scan of the pairs of entries of every pool cycle and a counting
    sort.
  * **P3, tables** (`RAM/Poly3*.lean`, `RAM.P3.poly3_spec`, `RAM.P3.CP3 k`): for every
    segment, children first, and every configuration `α < k^|bnd s|`, the minimization over
    `β < k^|topIdx s|` (an odometer on the base-`k` digits) of the local cost plus the
    children's table entries, keeping the first strict minimum; per configuration `O(|face|)`
    steps.
  * **P4, backtracking and output** (`RAM/Poly4*.lean`, `RAM.P4.poly4_spec`,
    `RAM.P4.CP4 k`): the segments top-down, decoding `α` and `argTab s α` into the values of
    the cycles and passing each child its configuration; then every pool cycle, rotated to its
    omitted vertex, written to the output through the output map.
* **Main** (`RAM.Main.k23Prog_spec`, `RAM.Main.k23Prog_computes`): the phase triples
  chain through the interfaces, each phase's layout end bounding the next one's free address
  (`R0.endR0_le`, `R1.endL_le`, `R2.endL_le`, `R3.endL_le`, `Main.loopEnd_le`); the output is
  exactly `Algo.solve k g` within `RAM.Main.Ck23 k * (m + 1)` steps, every access below
  `RAM.Main.Ck23 k * (L + m + 1)` (`ComputesIn`).

`decide +kernel` is used in `RAM/Poly3.lean`, `RAM/Poly3Odo.lean`, `RAM/Poly3Total.lean` and
in the tactic macro `indepG` of `RAM/Poly3Sel.lean`, to check by kernel evaluation that one
list of registers is contained in another (register footprints of concrete programs). It
adds no axiom: the axiom guards record, for example, `RAM.P3.poly3_wregs` (`[propext]`),
`RAM.P3.odoBody_spec`, `RAM.P3.prep_spec`, `RAM.P3.odo_spec` and
`RAM.P3.total_spec` (the three standard axioms).

## 9. The running time and the memory

The bounds are linear in the number `m` of input entries (the memory also in
`L = RAM.labelBound g`), with an explicit constant `RAM.Main.Ck23 k`, which bounds both:

| Constant | Value | Where |
|---|---|---|
| R0 | `RAM.R0.C0 = 300` (memory `20 (L + m + 1)`) | `RAM/R0.lean` |
| R1 | `RAM.R1.C1 = 600` | `RAM/R1.lean` |
| R2 | `RAM.R2.C2 = 240` | `RAM/R2.lean` |
| R3 | `RAM.R3.C3 = 100` | `RAM/R3.lean` |
| ear elimination | `RAM.EarR.CE = 700` (per `N + |L| + 1`) | `RAM/EarMain.lean` |
| P1 | `RAM.P1.CP1 = 450` (per `n + |pg| + 1`) | `RAM/Poly1.lean` |
| P2 | `RAM.P2.CP2 k = CT2 k + CM2 k` (time and fresh cells) | `RAM/Poly2.lean` |
| P3 | `RAM.P3.CP3 k = CT3 k + CM3 k`, with `k^Rb` configurations, `Rb = RAM.P3.Rb k = (k − 2) · rpathBound k + rpathBound k` | `RAM/Poly3.lean` |
| P4 | `RAM.P4.CP4 k = 29 + (Tseg k + 7) + 2 (Tsl k + 4) + rpathBound k (14k + 10)` | `RAM/Poly4.lean` |
| polygon solver | `RAM.Main.CP k = CP1 + CP2 k + CP3 k + CP4 k` | `RAM/Main.lean` |
| block solver | `RAM.Main.CBk k = RAM.Block.CB k CE (CP k) = 3 CE + 3 CP k + 6 |(Algo.k4Base k).flatten| + 200` | `RAM/Block.lean` |
| block loop | `RAM.Main.CL CB = 3 CB + 28` | `RAM/MainLoop.lean` |
| whole program | `RAM.Main.Ck23 k = C0 + C1 + C2 + C3 + CL (CBk k)` | `RAM/Main.lean` |

Why it is linear: the graph-level phases are linear in `m` (`N ≤ 2m`, `|E| ≤ m`); the blocks
partition the id edges and have at most `2|E_h|` vertices, and the block solver frees its
scratch memory (blocks never free memory, but each allocates `O(|E_h| + N_h)` cells); in a
polygon there are at most `|pg|` segments and the faces have at most `2|pg|` vertices in all;
each segment has at most `rpathBound k` cycles with top `s` and `(k − 2) rpathBound k`
boundary cycles, so at most `k^Rb` configurations `α` and `k^Rb` configurations `β`, each
evaluated in `O(|face s|)` steps; the cycles have `k` entries each.

The proof of Lemma 35 bounds the per-face and boundary cycle sets by `2^{M_k}`,
giving `k^{2^{M_k}}` configurations, where `M_k = ∑_{i=0}^{k−3} k^i`. The
executed program uses separate explicit region-path bounds `rpathBound`
(`rpathBound 4 = 15069224`). The endpoint requires a constant for each fixed `k`;
these analyses do not identify the constants with one another.


## Bounds in the proof of Lemma 35 (`NamedHoles.lean`)

`enclosedFacesBound_proved` proves the retained proposition `EnclosedFacesBound`. The cycle
length identity gives `|u| + 2(|encl u| − 1) = ∑ d_f`; every bounded face has perimeter at
least three, so `|encl u| + 2 ≤ |u|`. The vertices of each enclosed face are a subset of the
cycle's vertices, proving its perimeter is at most `|u|`.

`enclosingCycleCountBound_proved` proves `EnclosingCycleCountBound`. The existing
generating-function proof provides `IsPolygon.face_cycle_half_bound`: twice the number
of cycles enclosing a face is at most `4^(k−1)`. A triangle enclosing a face equals that
face's sorted vertex list, so at most one triangle encloses the face. For `k = 4`, the
half-bound gives at most 32 cycles, equal to `2^(1+4)`. For `k ≥ 5`, the first three terms
of `M_k` give `M_k ≥ 1+k+k² ≥ 2k`, and the proved `4^k = 2^(2k)` bound implies the
paper bound. This proof establishes the manuscript's numerical claim by a different
counting argument; the implemented linear-time algorithm continues to use its own bounds.

## Contextual planar-triangle perfect assignments (`PlanarTriangles.lean`)

`TriangleMatching.planar_triangle_hall` proves the finite Hall inequality for every selected
family of enumerated triangles of a planar graph, using only its `Complexity.PlanarGraph`
embedding. `planar_triangle_perfect_assignment` then proves `HasAssignment g 3 0` by selecting
one distinct side of each triangle. The cited contextual result remains cited in the manuscript.

`PlanarMinor.lean` and `PlanarMinorClosure.lean` establish ordinary planar deletion,
contraction and branch-set minor closure by the existing hypermap surgeries.
`PlanarConeObstructions.lean` excludes the complete five-vertex graph and the complete
three-by-three bipartite graph by Euler's formula. `NeighbourConeMinor.lean` lifts a forbidden
outerplanar minor of a vertex's neighbour graph to one of these planar obstructions.
`PlanarNeighbour.lean` consequently gives an outerplanar drawing of the neighbour graph.
Its proved degeneracy yields `PlanarTriangleGeometry.planar_light_edge`: a nonempty planar canonical
edge set has an edge with at most two common neighbours.

`TriangleFamily.lean` represents a selected triangle by its unordered three-vertex set.
`TriangleEdgeCount.lean` proves the exact contraction loss: the contracted edge set has
cardinality smaller by one plus the number of common neighbours. In
`TriangleContractionBounds.lean`, triangles containing the contracted edge inject into the
common neighbours. Surviving triangles remain three-vertex sets; their only possible extra
collision identifies the triangles obtained by adjoining either endpoint to the two common
neighbours. Thus the family loses at most one plus the number of common neighbours.
`TrianglePlanarContract.lean` preserves the actual planar embedding of the canonical finite
contraction graph. `PlanarTriangleCardinality.lean` combines these facts by strong induction
on the number of edges to prove that every triangle family has at most as many members as
its edge union.

`TriangleRepresentation.lean` proves that the enumerator's unordered triples are injective,
have exactly three vertices, and have precisely the same side union as their cycles. It
also inherits planarity for that union graph. The final Hall and perfect-assignment proofs
therefore have no supplied light edge, minor exclusion, contraction trace, family inequality,
or matching hypothesis.
