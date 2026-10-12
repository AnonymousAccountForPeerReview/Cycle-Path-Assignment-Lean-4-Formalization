# Paper map: Section 8 and Appendices E and F in Lean

Result numbers and appendix letters follow the accompanying paper. Lean names do not carry result numbers
(`outerplanar_block_structure` is Lemma 19, `k23_perfect` Theorem 20, `k23_linear_ram`
Theorem 21, `IsPolygon.dp_root_optimal` Lemma 34, `outerplanar_linear_ram` Lemma 35).
The bounds in the proof of Lemma 35 are formalized, along with the cycle–subtree
correspondence and the parent-face characterizations. Names without a namespace are in
`STACS2027`; files are under `Outerplanar/`. The sixteen compared theorems are marked
**(Challenge)**; every other row is a proved
library theorem or a definition, unless marked otherwise. Statements are quoted from the LaTeX
source with the notation rendered in Unicode.

## Section 8: Lemma 19 and Theorems 20 and 21

> **Lemma 19** (Outerplanarity and block structure, ANONYMIZED et al.). A graph is
> *outerplanar* if it has a planar drawing with every vertex on the outer face.
> Equivalently, it contains neither `K₄` nor `K_{2,3}` as a minor. Every 2-connected
> `K_{2,3}`-minor-free graph is either outerplanar or isomorphic to `K₄`.

> **Theorem 20.** Every `K_{2,3}`-minor-free graph admits a perfect cycle-path assignment for
> `k = 4`.

> **Theorem 21.** For every fixed `k ≥ 3`, an optimal cycle-path assignment on a
> `K_{2,3}`-minor-free graph with `n` vertices can be computed in `O(n)` time.

| Manuscript | Lean | Notes |
|---|---|---|
| graph `G = (V, E)` | `g : Graph` (a list of entries), its simple graph `Adj g` | `Adj g u v := u ≠ v ∧ edge u v ∈ g`: an entry `(a, b)` is the edge `ab` when `a < b`; loops, repeated entries and entries written larger end first are ignored, as by `cpap-np-hardness`'s `IsCycle`. Isolated vertices are not represented (they lie on no cycle). |
| minor, `K₄`, `K_{2,3}` | `HasMinor g size h` (branch sets), `k4` (`cpap-minor-free` formalization), `k23` | |
| "`K_{2,3}`-minor-free" | `K23MinorFree g := ¬ HasMinor g 5 k23` | |
| "2-connected" | `TwoConnected g` | At least three vertices, connected, connected after deleting any vertex. |
| "isomorphic to `K₄`" | `IsK4Graph g` | Four distinct vertices, any two adjacent, no other adjacency. |
| **Lemma 19, first sentence** (definition: "a planar drawing with every vertex on the outer face") | `OuterplanarDrawing g := OuterplanarEmbedding (simpleEdges g)` (`OuterplanarDef.lean`) | A drawing is a rotation system: a planar hypermap on the half-edges (the foundation's `Complexity.Hypermap`, planar when its genus from the Euler formula is `0`, as in ANONYMIZED's proof of the Four Colour Theorem) whose `edge` permutation pairs the ends of each edge and whose `node` cycles are the half-edges at a vertex (exactly `Complexity.PlanarGraph`), such that every connected component has a face through all its vertices (the outer face of the component). `simpleEdges g` lists the simple graph (`mem_simpleEdges`). |
| **Lemma 19, second sentence** ("Equivalently, it contains neither `K₄` nor `K_{2,3}` as a minor") | `outerplanarDrawing_iff_minorFree : OuterplanarDrawing g ↔ (¬ HasMinor g 4 k4 ∧ ¬ HasMinor g 5 k23)` (`OuterplanarCharacterization.lean`) | `⇐`: `outerplanarDrawing_of_minorFree` (`OuterplanarConstruct*.lean`: polygon embeddings of the 2-connected pieces from the third sentence, glued at cut vertices and put side by side). `⇒`: drawings are closed under minors (`OuterplanarDrawing.of_hasMinor`, `OuterplanarMinor*.lean`: contraction and deletion on embeddings, using Euler's inequality and parity for hypermaps, `hypermapEuler`, `HypermapEuler*.lean`), and `K₄`, `K_{2,3}` have none (`not_outerplanarDrawing_k4`, `not_outerplanarDrawing_k23`, `OuterplanarK4K23.lean`, by counting faces). `Outerplanar g` (`Defs.lean`) is the minor condition; `outerplanarDrawing_iff_outerplanar`. |
| **Lemma 19, third sentence** | `twoConnected_outerplanar_or_k4 : TwoConnected g → K23MinorFree g → OuterplanarDrawing g ∨ IsK4Graph g` (`OuterplanarConstruct.lean`), from `twoConnectedK23_structure : TwoConnectedK23Structure` (`TwoConnectedK23Structure.lean`) | `TwoConnectedK23Structure` (`Defs.lean`) is the combinatorial form the algorithms use: a 2-connected `K_{2,3}`-minor-free graph is a `K₄` or has a Hamiltonian cycle with respect to which no two edges cross (`OuterplanarHam`, the outer cycle and the chords of an outerplanar embedding). Proved by a longest cycle (`docs/PROOF.md` §1a); the manuscript cites the lemma (ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED 2016). |
| **Lemma 19** (all three sentences) | `outerplanar_block_structure` **(Challenge)** (`OuterplanarCharacterization.lean`) | `(OuterplanarDrawing g ↔ (¬ HasMinor g 4 k4 ∧ ¬ HasMinor g 5 k23)) ∧ (TwoConnected g → K23MinorFree g → OuterplanarDrawing g ∨ IsK4Graph g)`, the first sentence being the definition `OuterplanarDrawing`. |
| "perfect cycle-path assignment for `k = 4`" | `HasAssignment g 4 0` (`cpap-np-hardness` formalization) | An assignment of cost `0`. |
| **Theorem 20** | `k23_perfect` **(Challenge)** (`PerfectK23.lean`) | `K23MinorFree g → HasAssignment g 4 0`, with its graph-class premise (`k23_perfect_of_structure` takes `TwoConnectedK23Structure` as a hypothesis; `k23_perfect` instantiates it with `twoConnectedK23_structure`). |
| proof sketch of Theorem 20: blocks, Lemma 19, deletion of degree-two vertices, `K₄`, combination | `exists_palm`, `Palm.blocks_flatten`, `Palm.blocks_edgeDisjoint`, `Palm.blocks_cycles`, `Palm.twoConnected_block`, `Palm.block_k23MinorFree`, `outerplanarHam_degenerate`, `eliminationOrder_of_degenerate`, `perfect_of_outerplanarHam`, `cpap-minor-free`'s `algorithm4_perfect`, `k4_perfect`, `hasAssignment_blocks` | `docs/PROOF.md` §2. |
| "an optimal cycle-path assignment" (output of the algorithm) | `OptimalAssignmentOutput g k out` | `out` is the concatenation of a list `cs` of `k`-cycles of `g`, one for each edge set of a `k`-cycle, each written from the vertex its path omits, whose paths `selected c 0` have the optimal cost `C*` (`IsMinCost g k`, the `cpap-approximation-hardness` formalization's definition). |
| "can be computed in `O(n)` time" | `∃ (prog : RAM.Stmt) (C : ℕ), ∀ g, K23MinorFree g → ∃ out T, RAM.ComputesIn prog (RAM.graphInput g) out T (C * (RAM.labelBound g + g.length + 1)) ∧ T ≤ C * (g.length + 1) ∧ OptimalAssignmentOutput g k out` | One program and one constant for each `k ≥ 3`, on the unit-cost RAM of the `cpap-approximation-hardness` formalization; the input is the number of entries followed by their ends. **Time** `T ≤ C (m + 1)` in the number `m = |g|` of entries; **memory**: the run reads and writes only the addresses below `C (L + m + 1)` (`ComputesIn`, `ExecB`), `L = RAM.labelBound g` one more than the largest vertex label (for labels `0, …, n − 1`, `L = n`). See Differences. |
| **Theorem 21** | `k23_linear_ram` **(Challenge)** (`LinearK23.lean`) | For every `k ≥ 3`, under `K23MinorFree g`; the intermediate structure parameter is discharged by its proof. Also `k23_linear_ram_solve` (the output is exactly `Algo.solve k g`), `solve_optimal` (it is optimal); `RAM.Main.k23Prog_computes` (the program `RAM.Main.k23Prog k`, the constant `RAM.Main.Ck23 k`) and `Algo.solve_optimal` take `TwoConnectedK23Structure` as a hypothesis, as do the `…_of_structure` versions. |
| proof sketch of Theorem 21 | `docs/PROOF.md` §§7–9 | |

## Appendix E: Lemmas 23–25, Algorithm 4 and the proof of Theorem 20

> **Lemma 24.** In a `K_{2,3}`-minor-free graph, any two distinct vertices have at most two
> common neighbors.

> **Lemma 25.** For any outerplanar graph `G = (V, E)`, Algorithm 4 outputs a perfect
> cycle-path assignment `τ` with `c(τ) = 0` for `k = 4`.

| Manuscript | Lean | Notes |
|---|---|---|
| **Lemma 23** (`K_{2,n−2}`: optimal four-cycle cost `Θ(n³)`) | the `cpap-minor-free` formalization (`cpap-minor-free`, `biclique_planar_family`) | Not used here. |
| "two distinct vertices have at most two common neighbors" | `CommonNeighbours2 g` (`Minors.lean`) | `∀ u w a b c, u ≠ w → (a, b, c common neighbours) → a = b ∨ a = c ∨ b = c`, on the simple graph. |
| **Lemma 24** | `common_neighbours_le_two` **(Challenge)** (`Minors.lean`) | The manuscript's proof: the `K_{2,3}` subgraph is a minor with singleton branch sets (`hasMinor_of_embedding`). `commonNeighbourBound_of_k23MinorFree`: the form `CommonNeighbourBound` of the `cpap-minor-free` formalization. |
| "Every nonempty outerplanar graph has a vertex of degree at most two, and deleting a vertex preserves outerplanarity" | `outerplanar_degenerate`, `outerplanar_eliminationOrder`, `outerplanarDrawing_subgraph` (`GeneralDegenerate.lean`) | Proved for arbitrary outerplanar drawings, including disconnected graphs and cut vertices. |
| **Algorithm 4**, **Lemma 25** | `outerplanar_algorithm_perfect`, `outerplanar_algorithm_assignment` (`GeneralAlgorithm.lean`) | The full loop-free outerplanar endpoints: an elimination order and valid zero-cost output are proved from `OuterplanarDrawing`. They instantiate cpap-minor-free’s assignment interface. |
| The `K₄` base case | `k4_perfect`, `k4Assignment` in `cpap-minor-free` | Used in the blockwise proofs of Theorems 20 and 21. |
| proof of Theorem 20 | `k23_perfect` | The block decomposition, the elimination order, Lemma 24 and Lemma 19 are all proved here. |

## Appendix F: the setting and Definition 26

| Manuscript | Lean | Notes |
|---|---|---|
| "a 2-connected outerplanar graph `G = (V, E)` together with an outerplanar embedding", "a Hamiltonian cycle `H` consisting only of edges that touch the outer unbounded face", chords | `IsPolygon g n := OuterplanarHam g (List.range n)` (`Polygon.lean`) | The **polygon model**: the vertices are the positions `0, …, n − 1` on the outer cycle, every other edge is a chord, and no two edges cross. A graph with an outerplanar Hamiltonian cycle becomes one by renaming (`posGraph`, `isPolygon_posGraph`), with the same optimum (`isMinCost_posGraph`). |
| simple cycles `𝒞`, `𝒞_k` | `IsCycle g k c` (`cpap-np-hardness` formalization); in a polygon, `ConvexCycle g u` | `IsPolygon.convex_of_isCycle`: every simple cycle of a polygon visits its vertices in increasing order (up to rotation and reversal); the `k`-cycles are, up to edge sets, the convex `k`-cycles (`convexList`, `convexCycles`), each represented once (`ConvexCycle.eq_of_sameCycle`). |
| bounded faces `ℱ`, `E(f)`, `d_f` | the face below a segment: `faceVerts g n s` (`Faces.lean`) | A segment is an edge `(a, b)` with `a + 2 ≤ b` (a chord or the outer edge `(0, n − 1)`, `IsPolygon.segs`); its face has the positions of `[a, b]` strictly inside no other segment within `s`. |
| `E(f)`, `∂T = Δ_{f ∈ fc(T)} E(f)`, `deg_X(w)` | `faceEdges g n s`, `bdry g n T` (`WeakDual.lean`, a `Finset.fold` of symmetric differences), `degIn F w` (`WeakDualFacts.lean`) | `mem_bdry`: the edges on an odd number of the faces of `T`. **(Challenge)**: `faceEdges`, `bdry`. |
| **Definition 26** (weak dual `D`) | `DualAdj g n s t` (`WeakDual.lean`) **(Challenge)**; rooted: `IsPolygon.segTree` (`Segments.lean`), root `IsPolygon.root = (0, n − 1)` | `IsPolygon.dualAdj_iff`: two faces are adjacent iff one is the parent of the other in the segment tree (segments ordered by containment), so the segment tree is the weak dual rooted at the face on `(0, n − 1)`. That `D` is a tree (cited from ANONYMIZED et al.) is `IsPolygon.weakDual_tree`. |
| `𝒮` (nonempty subtrees: `D[S]` connected) | `IsSubtree g n S` **(Challenge)** | Nonempty, a set of faces, any two joined by a walk of adjacent faces inside `S` (`Relation.ReflTransGen`). `IsPolygon.isSubtree_iff`: exactly the rooted sets. |
| "`c` encloses `f` if `v_f ∈ ∂⁻¹(c)`" | `encl g n u` **(Challenge)**: the faces all of whose vertices lie on `u` | By Lemma 29 it is `∂⁻¹(u)` for a convex cycle `u`; `IsPolygon.mem_encl_iff`. |

## Appendix F.1: Lemmas 27–29 and the cycle bounds

Lemmas 27–29 are stated in the polygon model, with `r = |segs g n|` faces (one per segment),
`m = |polyEdges g n|` edges, the outer cycle `H` on `0, …, n − 1` and the chords `chords g n`
(the segments other than `(0, n − 1)`); the simple cycles are the convex cycles.

> **Lemma 27.** (1) `r = m − n + 1`. The map `κ` sending each chord to the dual edge joining its
> incident faces is a bijection onto `E_D`. (2) If `∅ ≠ T ⊆ V_D`, then `∂T ≠ ∅`. (3) If
> `S ∈ 𝒮`, then `deg_{∂S}(w) ∈ {0, 2}` for every vertex `w ∈ V`.

> **Lemma 28.** Suppose `r ≥ 2` and `v_f` is a leaf of `D`. (1) The face `f` has exactly one
> chord `e = {u, v}`. The set `P = E(f) \ {e}` is a `u`–`v` path with at least two edges.
> (2) Every internal vertex of `P` has degree two in `G`. (3) The graph `G' = G − W` has edge set
> `E \ P` and is 2-connected and outerplanar. Its bounded faces are `ℱ \ {f}`, its weak dual is
> `D' = D − v_f`, and `e` lies on its outer boundary.

> **Lemma 29.** The restriction of `∂` to `𝒮` is a bijection onto `𝒞`. For every `S ∈ 𝒮`,
> `|∂S| = ∑_{f ∈ fc(S)} d_f − 2(|S| − 1)`.

| Manuscript | Lean | Notes |
|---|---|---|
| **Lemma 27 (1)**, `r = m − n + 1` | `IsPolygon.euler_face_count` **(Challenge)** (`WeakDualFacts.lean`): `(segs g n).card + n = (polyEdges g n).card + 1` | Stated as `r + n = m + 1` (subtraction-free in `ℕ`). |
| **Lemma 27 (1)**, the bijection `κ` | `IsPolygon.chord_dualEdge_bij`: the faces `p`, `c` of a dual edge share exactly the chord `c`; `Set.BijOn Prod.snd (dualEdges g n) (chords g n)`; `|dualEdges| + 1 = r` | The edges of `D` are written once each as (parent, child) pairs (`dualEdges`). `IsPolygon.weakDual_tree`. |
| **Lemma 27 (2)** | `IsPolygon.bdry_ne_empty` | The proof differs: the segment of a largest face of `T` lies on no other face of `T`. |
| **Lemma 27 (3)** | `IsPolygon.bdry_deg` | Derived from Lemma 29 (`∂S` is the edge set of a cycle). |
| **Lemma 28** (1), (2) | `IsPolygon.leaf_face` (`WeakDualFacts.lean`), `IsPolygon.root_leaf_unique_chord`, `IsPolygon.root_leaf_inner_degree` (`RootLeaf.lean`), `IsPolygon.face_path_of_edge` (`LeafFaceDeletion.lean`) | Childless non-root segments and the root face with a unique child are both covered. Removing the unique chord from the face cycle gives a path of at least two edges. |
| **Lemma 28** (3) | `IsPolygon.leaf_face_deletion` (`LeafFaceDeletion.lean`) | For every actual weak-dual degree-one leaf with `r ≥ 2`, one bundled witness gives the induced graph `G − W`, exact edge set `E \\ P`, 2-connectivity, outerplanarity, the new outer Hamiltonian boundary containing the chord, the bijection of surviving original faces onto all new bounded faces, and exact weak-dual adjacency restriction. `FaceTransport.lean` proves the chordless-cycle criterion equals the positional embedding's face definition, so the new bounded faces are identified against the new graph. |
| **Lemma 29** | `IsPolygon.cycle_subtree_bij` **(Challenge)** (`WeakDualBij.lean`) | For convex cycles: (1) every convex `u` is `∂(encl u)` with `encl u` a subtree; (2) for every subtree `S`, `∂S` is the edge set of exactly one convex cycle, which encloses exactly `S`; (3) every convex cycle with edge set `∂S` encloses `S`; (4) `∂` is injective on subtrees; (5) `|∂S| = ∑_{s ∈ S} d_s − 2 (|S| − 1)`. |
| **Lemma 29** for the simple cycles `𝒞` | `IsPolygon.cycle_subtree_bij_simpleCycles` **(Challenge)** | `∂S` is the edge set of a simple cycle for every subtree `S`, and the edge set of every simple cycle is `∂S` for exactly one subtree `S`. |
| equation (1), `k = 2 + ∑_{g ∈ fc(S)} (d_g − 2)` for a `k`-cycle with subtree `S` | part (5) of `IsPolygon.cycle_subtree_bij`, rearranged | The consequences used in the proof of Lemma 35 ("a `k`-cycle encloses at most `k − 2` faces, each of perimeter at most `k`") are `EnclosedFacesBound`, proved by `enclosedFacesBound_proved` and `IsPolygon.enclosed_faces_bound` (`NamedHoles.lean`). |
| proof of Lemma 35: "at most `2^{M_k}` cycle subtrees can contain any given node", `|C_{v_f}| ≤ 2^{M_k}`, `|B_{v_f}| ≤ 2^{M_k}`, `M_k = ∑_{i=0}^{k−3} k^i` | `EnclosingCycleCountBound`, proved by `enclosingCycleCountBound_proved` and `IsPolygon.enclosing_cycle_count_bound` (`NamedHoles.lean`) | A triangle enclosing a face is that face. For `k = 4`, the generating-function bound `IsPolygon.face_cycle_half_bound` gives at most 32 cycles, the stated bound. For `k ≥ 5`, `M_k ≥ 2k` makes the proved `4^k` bound stronger than `2^{M_k}`. The original per-face and per-edge bounds remain proved. |
| use of these bounds in the algorithm | — | The dynamic program and Theorem 21 use the face decomposition `IsPolygon.isRPath_iff_joins` (`RegionPaths.lean`, the recursive form of Lemma 29), the enumeration `rpaths`, and cruder bounds (`rpathBound`, depending on `k` alone); their correctness and running-time proofs use their own proved bounds. |

## Appendix F.2: Lemmas 30–33

| Manuscript | Lean | Notes |
|---|---|---|
| "Assign each graph edge to the deepest dual node whose face it bounds", `E_{v_f}` | `IsPolygon.own` (each edge owned by the smallest segment containing it) | |
| **Lemma 30** (the sets `E_{v_f}` partition `E`; an outer edge is assigned to its unique incident bounded face; a chord to the deeper of its two incident faces, where it is the parent chord) | proved, in the polygon model | `IsPolygon.own_spec`, `IsPolygon.own_of_seg` (a segment owns itself: the parent chord `e_{v_f}`), `Poly.mem_owned`. Ownership is a function, so the sets partition the edges. |
| `top(c)` ("the unique node of this subtree closest to the root"), `𝒞_{v_f}`, `B_{v_f}` (cycles meeting both `G_{v_f}` and its complement) | `top` of `polygonProblem` (the segment `(u₀, u_last)`), `TreeDP.Problem.boundary` | `B_{v_f}`: top outside the subtree, through an edge owned inside it; in a polygon, the cycles through both ends of the segment with another top (`Poly.mem_boundary`). |
| **Lemma 31** (`lem:dual_parent`, for `v_f ≠ v_r` with parent `v_p` and `S = ∂⁻¹(c)`: (1) if `v_p ∉ S`, then `S` and `c` lie inside `D_{v_f}`, `G_{v_f}` or are disjoint from them; (2) `top(c) = v_f` iff `v_f ∈ S`, `v_p ∉ S`; (3) `c ∈ B_{v_f}` iff `v_p ∈ S`) | `IsPolygon.cycle_child_dichotomy` **(Challenge)**, `IsPolygon.top_face_iff_parent_not_enclosed`, `IsPolygon.boundary_iff_parent_enclosed` (`NamedHoles.lean`) | Part (1) covers both the enclosed face set and the graph edges; polygon containment represents descendant membership, as proved by `own_within_iff`. Parts (2) and (3) are separate statements; part (3) uses the boundary variables of the proved dynamic program. |
| **Lemma 32** ("If `c ∈ 𝒞_k` contains an edge of `E_{v_f}`, then `c ∈ 𝒞_{v_f} ∪ B_{v_f}`") | proved, abstractly | `TreeDP.Problem.top_eq_or_mem_boundary`, with `scope_top`. |
| **Lemma 33** (`B_{v_g} ⊆ B_{v_f} ∪ 𝒞_{v_f}` for every child `v_g`) | proved, abstractly | `TreeDP.Problem.boundary_child`. |

## Appendix F.2: Lemmas 34 and 35 and the proof of Theorem 21

> **Lemma 34.** For every node `v_f` and state `α ∈ Ω(B_{v_f})`,
> `DP[v_f, α] = min_{η ∈ Ω(Q_{v_f}), η|_{B_{v_f}} = α} ∑_{e ∈ G_{v_f}} binom(l_η(e), 2)`, where
> `Q_{v_f} = {c ∈ 𝒞_k : c ∩ G_{v_f} ≠ ∅}`. In particular, `DP[v_r, ∅] = OPT`.

> **Lemma 35.** For every fixed `k ≥ 3`, an optimal cycle-path assignment on an outerplanar
> graph with `n` vertices can be computed in `O(n)` time.

| Manuscript | Lean | Notes |
|---|---|---|
| configurations `Ω`, states `α`, local configurations `β`, `γ = α ∪ β` | values `γ : CycVar g n k → Fin k` (`DPCorrect.lean`) | A value `j` omits the `j`-th vertex of the convex cycle, leaving the path `selectedAt u u[j]`; `IsPolygon.hasAssignment_iff_family`, `IsPolygon.total_eq`. |
| the recurrence for `DP[v_f, α]`, and its simplification for faces with `d_f > k` | `TreeDP.Problem.dp` of `polygonProblem` (`TreeDP.lean`); the machine's tables `Poly.tabArg`, `Poly.table` (`Algo/Poly.lean`) | One recursion for both: a large face (`d_f > k`) is the top of no `k`-cycle, so its minimization is over the single empty configuration ("the simplified recurrence is the same formula with the unique empty local configuration"). `Poly.tabArg_spec`: the tables compute `dp`. |
| `c(v_f, γ) = ∑_{e ∈ E_{v_f}} binom(l_γ(e), 2)` | `TreeDP.Problem.loc`; `Poly.localCost` | |
| **Lemma 34** | `IsPolygon.dp_table_correct` (every entry), `IsPolygon.dp_root_optimal` (`DP[root, α]` is `C*`) | Stated for values `α` of all cycles; `TreeDP.Problem.dp_congr` shows that an entry depends only on the boundary cycles. `G_{v_f}` is the set of edges owned in the subtree (`TreeDP.Problem.tot`); the cycles not determined by `α` are those with top in the subtree (equation (2), `eq:inner`). |
| **Lemma 35** | `outerplanar_linear_ram` **(Challenge)** (`LinearK23.lean`) | Theorem 21's form (time and memory) for `OuterplanarDrawing g`, the definition of Lemma 19; from `k23_linear_ram` by `outerplanarDrawing_iff_outerplanar` (outerplanar graphs are `K_{2,3}`-minor-free). Also `Algo.solve_optimal_outerplanar`. |
| proof of Lemma 35: blocks, an embedding (Mitchell 1979), `|𝒞_{v_f}|, |B_{v_f}| ≤ 2^{M_k}`, `k^{2^{M_k}}` states, cycle enumeration by subtrees of the radius-`(k − 3)` neighbourhoods, boundary lists, backtracking | `docs/PROOF.md` §§7–9: the block decomposition (`Algo.blocksOf_eq`), the bounds `Poly.length_topIdx_le`, `Poly.length_bnd_le`, the region paths memoized per segment (`Poly.rpF`, phase P2), the tables (phase P3), the backtracking (`Poly.backtrack`, phase P4) | The outerplanar embedding (the outer Hamiltonian cycle) is computed by ear elimination (`Ear.earHam_correct`) instead of Mitchell's algorithm; the cycles are enumerated as region paths, not as subsets of neighbourhoods. |
| proof of Theorem 21 | `Algo.solve_correct`, `Algo.solve_optimal`, `RAM.Main.k23Prog_spec` | `K₄` blocks: a fixed output (`Algo.k4Out`, cost `0`) instead of exhaustive search; for `k ≥ 5` a `K₄` has no `k`-cycle, as the proof says. |

## Differences

* **Lemma 19 is proved, with the manuscript's definition.** The manuscript cites it. Here
  outerplanarity is `OuterplanarDrawing` (a planar rotation system with every vertex of each
  component on one face), the equivalence with the excluded minors is `outerplanarDrawing_iff_minorFree`, and the
  2-connected sentence is `twoConnected_outerplanar_or_k4`; the algorithms use its combinatorial form
  `twoConnectedK23_structure` (a `K₄` or a Hamiltonian cycle with no two crossing edges).
* **The polygon model.** Appendix F reasons about an outerplanar embedding, its faces and its
  weak dual. Here a 2-connected outerplanar graph is a polygon on `0, …, n − 1` with
  non-crossing chords (obtained from `twoConnectedK23_structure` by renaming the vertices by their positions
  on the cycle); segments, faces, the segment tree (the rooted weak dual), tops, ownership and
  region paths are defined combinatorially, and the cycle–subtree correspondence takes the
  form of the face decomposition. The resulting dynamic program is the manuscript's
  (Lemma 34). Lemmas 27–29 are also stated in the manuscript's terms inside the polygon model;
  the proof of Lemma 27 (2) differs from the manuscript's. Lemma 28 includes exact
  induced graph, bounded-face and weak-dual deletion, including the root-leaf case.
  Lemma 31 has separate statements.
* **Input size.** The time bound is `C (m + 1)` in the number `m = |g|` of input entries, not
  in the number `n` of vertices. For a simple `K_{2,3}`-minor-free graph without isolated
  vertices, `m ≤ 2n − 2`, so this is `O(n)`; the input may also contain repeated entries, loops
  and entries written larger end first, which cost time but are ignored.
* **The machine and its memory.** The unit-cost RAM of the `cpap-approximation-hardness` formalization: unbounded
  registers, uniform cost, `const add sub load store write`, no multiplication; memory is zero
  initially. The memory bound `C (L + m + 1)` counts the addresses the run may access
  (`ExecB`: every `load` and `store` below the bound, the input cells included). `L`, one more
  than the largest label, enters because the program keeps a dictionary indexed by the labels,
  which it never initializes (so the time does not depend on `L`); for the usual labels
  `0, …, n − 1`, `L = n`.
* **Constants.** The constant is explicit (`RAM.Main.Ck23 k`, `docs/PROOF.md` §9) but
  astronomically larger than the manuscript's `k^{2^{M_k}}`-based ones: the number of region
  paths is bounded by `rpathBound` (tower-like) instead of `2^{M_k}`, and every phase's bound is
  crude.
  The compared statements only claim that a constant exists for each `k`.
* **Output.** The manuscript's "optimal cycle-path assignment" is written as
  `OptimalAssignmentOutput`: each `k`-cycle (up to its edge set) once, written from the vertex
  that its path omits, the paths having optimal cost.
* **`k ≥ 3`.** Theorem 21 and Lemma 35 are stated for every `k ≥ 3`, Theorem 20 for `k = 4`,
  as in the manuscript.

## Contextual planar-triangle result

| Manuscript statement | Lean | Proof coverage |
|---|---|---|
| Every planar graph admits a perfect assignment when `k = 3`, cited before Theorem 20 and in the concluding discussion | `TriangleMatching.planar_triangle_perfect_assignment : Complexity.PlanarGraph g → HasAssignment g 3 0` (`PlanarTriangles.lean`) | `planar_triangle_hall` proves every selected triangle-family Hall inequality from planarity. The proof derives a light edge through neighbour-graph outerplanarity, contracts it with exact edge and triangle losses, and inducts on the edge count. The checked Hall matching selects distinct triangle sides. The citation stays in the manuscript. |

## Coverage in other packages

* Lemma 23 (formalized in the `cpap-minor-free` formalization) and the planar examples of Appendix E.
* The timed min-cost-flow algorithm for `k = 3` is in `cpap-tractability` and `cpap-runtimes`;
  its only external algorithmic premise is the excluded almost-linear flow contract.
