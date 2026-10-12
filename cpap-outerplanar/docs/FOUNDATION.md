# Use of the foundation, the `cpap-np-hardness` and `cpap-minor-free` packages and Mathlib

This project depends on four Lean developments, each required by Lake and never copied into
this repository:

* **The NP-completeness foundation** `NPCompleteness-Lean4`, at commit
  `3e603e795b44fedcf7d6dd65b7d1e30547ead925` (also required by the Section 5 and Section 8
  formalizations). The library uses its combinatorial planarity (`Complexity/Planarity.lean`:
  hypermaps `Complexity.Hypermap`, their genus from the Euler formula, `Hypermap.Planar`, and
  the planar embeddings `Complexity.PlanarGraph` of an edge list, following ANONYMIZED's proof of
  the Four Colour Theorem) and the rotation lemmas of `Complexity/Planar/Rot.lean`. The
  manuscript's definition of outerplanarity (Lemma 19: a planar drawing with every vertex on
  the outer face) is stated in these terms (`OuterplanarDrawing`,
  `Outerplanar/OuterplanarDef.lean`).
* **`cpap-np-hardness`**, the formalization of Section 5 of the same manuscript (commit
  `d5e4bcfa1c1584104a87ad2aab48e21353823ebc` when required by git; in the published layout a
  sibling directory required by path). The library imports `NPHardness.FiniteCycles`,
  `NPHardness.CPAP` and `NPHardness.GlobalReduction` (the cycle-path assignment problem, its
  cost as a sum over edges of `binom(l(e), 2)`, the representative families of the
  enumerated cycles, invariance under relabelling), and the planar gluing and relabelling
  modules `NPHardness.PlanarGluing*`, `NPHardness.PlanarRelabel` and
  `NPHardness.PlanarPreprocessDeletion*` (embeddings of disjoint unions, gluing at a cut vertex,
  transpositions of darts, relabelling, edge deletion), on which the construction of
  outerplanar embeddings builds.
* **`cpap-minor-free`**, the formalization of Section 8 and Appendix E of the same manuscript
  (commit `c090168e8f0f8fb2410000d034d3d4f333309d84` when required by git; a sibling directory
  in the published layout). The library imports `MinorFree.K4`, `MinorFree.Elimination` and
  `MinorFree.Blocks`, and uses `k4`, `k4Assignment` and `k4_perfect` (`K₄` and its perfect
  four-cycle assignment), Algorithm 4 with its hypotheses `EliminationOrder` and
  `CommonNeighbourBound` and its correctness `algorithm4_perfect` (Lemma 25), and the
  blockwise combination `hasAssignment_blocks` with `EdgeDisjoint` and `CyclesInBlocks`. This
  project proves the hypotheses that the `cpap-minor-free` formalization leaves open: Lemma 19, Lemma
  24 from `K_{2,3}`-minor-freeness, the elimination order of an outerplanar block and the
  block decomposition, so that Theorem 20 becomes a theorem about every `K_{2,3}`-minor-free
  graph.
* **Mathlib**, at the release tag `v4.35.0-rc2` of the toolchain, commit
  `065356127b1dc0016f66b7283ce0ce2c4055aa55` (`lake-manifest.json` also pins its own
  dependencies to full commits). The weak-dual definitions and statements use finite sets,
  their sums, folds of symmetric differences, `Relation.ReflTransGen`, `List.sublistsLen` and
  the power `4 ^ k` on `ℕ`; the proofs use, besides, `Finset.inf'` (the tree dynamic program,
  Lemma 34), rational numbers (the generating function of the supporting cycle-count bounds) and tactics.

`lakefile.toml` requires all four and `lake-manifest.json` records them;
`scripts/check_repository.py` checks the pins (the foundation and Mathlib at their commits; the
`cpap-np-hardness` and `cpap-minor-free` packages either by git at their commits or by path) and that no
copy is vendored. `lake exe cache get` fetches Mathlib's official build cache.

### Where the scripts find the dependencies

`scripts/dependencies.py` reads each dependency's directory from `lake-manifest.json`: a path
dependency (`"type": "path"`) lives in its `"dir"`, relative to this package (in the published
layout, `../cpap-np-hardness` and `../cpap-minor-free`); a git dependency (`"type": "git"`) in
`.lake/packages/<name>`. The Challenge generator and the repository check go through it, so
they work in both layouts.

## The unit-cost RAM of the `cpap-approximation-hardness` formalization

The running-time theorems use the unit-cost random-access machine of the Section 6
formalization of the same manuscript. That formalization is not a dependency (it would bring
its own, much larger, dependency closure); instead `Outerplanar/RAM/Model.lean` is a verbatim
copy of its `ApproximationHardness/RAM/Model.lean` (one sentence of documentation added) and
`Outerplanar/RAM/Spec.lean` a copy of its `ApproximationHardness/RAM/Spec.lean` (its import renamed), both
in the namespace `STACS2027.RAM`. `Model.lean` imports only Lean core.
`Outerplanar/RAM/Bounded.lean` adds runs within a memory bound (`ExecB S`: every `load` and
`store` at an address below `S`) and `ComputesIn s input output time space`; it depends only on
`Model.lean`.

## What the Challenge copies

`Challenge.lean` copies, verbatim, with docstrings and in the same order:

* from the foundation, `Complexity.iterate`, `Complexity.Hypermap`, `Complexity.cycleCount`,
  `Complexity.Hypermap.linked`, `componentCount`, `eulerLhs`, `eulerRhs`, `genus`, `Planar`
  and `Complexity.halfEdgeEnd` and `Complexity.PlanarGraph` (`Complexity/Planarity.lean`);
* from `cpap-np-hardness`, the cycle-path assignment problem (`Edge` through `HasAssignment`,
  the declarations the `cpap-np-hardness` and `cpap-minor-free` challenge statements copy);
* from `cpap-minor-free`, `k4` (`MinorFree/K4.lean`), and `EliminationOrder`, `earliestIndex`
  and `algorithm4` (`MinorFree/Elimination.lean`);
* from this library, `Adj` through `OptimalAssignmentOutput` (`Outerplanar/Defs.lean`, without
  `Outerplanar` and `TwoConnectedK23Structure`, which no compared statement uses), `CommonNeighbours2`
  (`Outerplanar/Minors.lean`), `simpleEdges`, `OuterplanarEmbedding` and `OuterplanarDrawing`
  (`Outerplanar/OuterplanarDef.lean`), the machine `RAM.Config`, `RAM.Stmt`,
  `RAM.Config.setReg`, `RAM.Config.setMem`, `RAM.Config.emit` and `RAM.initial`
  (`Outerplanar/RAM/Model.lean`), `RAM.graphInput` and `RAM.labelBound`
  (`Outerplanar/RAM/Layout.lean`), `RAM.ExecB` and `RAM.ComputesIn`
  (`Outerplanar/RAM/Bounded.lean`), and the polygon model with its weak dual: `IsPolygon` and
  the decidability of `Adj` (`Polygon.lean`), `ConvexCycle` (`Convex.lean`), `Within` and
  `IsPolygon.segs` and `IsPolygon.IsChild` (`Segments.lean`), `IsFaceVert` and `faceVerts` (`Faces.lean`), the
  decidability of `ConvexCycle`, `convexList` and `polyEdges` (`DPCorrect.lean`), `faceEdges`,
  `bdry`, `encl`, `DualAdj` and `IsSubtree` (`WeakDual.lean`), `chords` (`WeakDualFacts.lean`),
  `ChordlessCycle`, `BoundedFaceBoundary` and `BoundaryDualAdj` (`FaceTransport.lean`),
  and `IsDualLeaf` and `leafInterior` (`LeafFaceDeletion.lean`); four `Decidable` instances
  without a documentation comment in the library get one from the generator's `DOCS` table
  (their terms are unchanged);
* the sixteen compared statements, from `Outerplanar/OuterplanarCharacterization.lean`, `PerfectK23.lean`,
  `LinearK23.lean`, `GeneralAlgorithm.lean`, `PlanarTriangles.lean`, `Minors.lean`,
  `WeakDualFacts.lean`, `WeakDualBij.lean`, `WeakDualCount.lean`, `NamedHoles.lean` and
  `LeafFaceDeletion.lean`, up to their `:=`, the proofs replaced by `sorry`; those of the
  namespace `IsPolygon` with the section variables `variable {g : Graph} {n : ℕ}` of their
  files.

`scripts/generate_challenge.py` reads them from the dependencies (located through
`lake-manifest.json`) and from this library, so a copy cannot drift from its source; `--check`
fails if it has. Comparator then checks that each copied declaration is the same term as the
library's and that each statement is the same.

The Challenge imports three modules of the pinned Mathlib,
`Mathlib.Algebra.BigOperators.Group.Finset.Defs`, `Mathlib.Data.Finset.Prod` and
`Mathlib.Data.List.Sublists`: the smallest set of modules whose import closure contains every
Mathlib declaration that the library's terms of the copied weak-dual definitions and
statements use (`List.toFinset`, `Finset.sum`, `Finset.filter`, `Finset.card`, `Finset.fold`,
`symmDiff`, the lattice and `SDiff` instances of `Finset`, `Finset.range`, `Finset.product`,
`Relation.ReflTransGen`, `ExistsUnique`, `List.sublistsLen`, `Nat.instMonoid` and
`Monoid.toNPow` for `4 ^ k`, `Nat.instAddCommMonoid` for the sums). With these modules,
instance search in the Challenge finds the library's instances (checked below). The Challenge
contains no meta-level code (`check_repository.py` checks it).

## Elaboration pitfalls

* **Matcher sharing.** Lean shares, within one module, the auxiliary `match` functions of
  pattern-matching definitions of the same shape. `STACS2027.pathEdges` (copied from
  Section 5) and `STACS2027.WalkWithin` both match a `List Nat` with the alternatives `[]`,
  `[_]`, `_ :: _ :: _`; in the libraries they live in different modules and each has its own
  matcher, but in the single-module Challenge `WalkWithin` would reuse `pathEdges.match_1`
  and elaborate to a different term. The generator therefore prefixes the copied
  `WalkWithin` with `set_option bootstrap.genMatcherCode false in`, which changes only the
  matcher's code generation and gives it a fresh auxiliary, `WalkWithin.match_1`, with the
  library's name and value. Section 8's `earliestIndex` uses nested empty/cons matches,
  whose matcher shape differs from this three-alternative pattern. This preserves its
  original executable result while letting the independent Challenge copy all three
  definitions with their exact auxiliary names and terms.
* **`List.sum` over `ℕ` with Mathlib imported.** The `cpap-np-hardness` library is elaborated with
  Lean core only. There, the `[Zero Nat]` argument of `List.sum` in `overlap` and `cost` is
  core's instance `Zero.ofOfNat0`; in the Challenge, which imports Mathlib, instance search
  finds Mathlib's `AddZero.toZero … Nat.instAddMonoid` first. The generator prefixes these two
  copies with `attribute [local instance high] Zero.ofOfNat0 in`, which, for that one
  declaration only, ranks core's instance first. Every other copied declaration elaborated
  without Mathlib (the foundation's hypermaps, the rest of Section 5, `k4`,
  `Outerplanar/Defs.lean`, the machine) elaborates to the library's term as it is.
* **Shared auxiliary proofs (avoided in the library).** Lean abstracts the proofs nested in a
  definition into auxiliary theorems `<declaration>._proof_<i>` and, within one module,
  reuses an auxiliary theorem of the same type. Section 5's `Decidable` instance of `IsCycle`
  contains the proof of `LawfulBEq (ℕ × ℕ)` behind list membership. If the `Decidable`
  instances of `Adj` (`Polygon.lean`) and `ConvexCycle` (`DPCorrect.lean`) contained that proof
  too, they would reuse `instDecidableIsCycle._proof_2` in the single-module Challenge and
  elaborate to a different term. The library therefore decides them through `List.contains`,
  which needs no proof:

  ```lean
  instance (g : Graph) (a b : ℕ) : Decidable (Adj g a b) :=
    decidable_of_iff (a ≠ b ∧ g.contains (edge a b) = true) (by simp [Adj])

  instance (g : Graph) : DecidablePred (ConvexCycle g) := fun u =>
    decidable_of_iff (u.Pairwise (· < ·) ∧ 3 ≤ u.length ∧ ∀ e ∈ cycleEdges u, g.contains e = true)
      (by simp [ConvexCycle])
  ```

These points are checked by `scripts/compare_challenge.py`: every `STACS2027` and
`Complexity` constant that the compared statements depend on (the definitions, their matchers
and structural-recursion auxiliaries, the `Decidable` instances and their proof auxiliaries,
the structures, inductive types and constructors, and the ten statements) prints identically,
with `pp.all`, in the library's environment and in the Challenge's (`docs/VERIFICATION.md`
records the count); Comparator confirms it.

## Re-pinning or switching layouts

If the `cpap-np-hardness` or `cpap-minor-free` package is published at another commit, replace the
`git` URL and `rev` of its `[[require]]` entry in `lakefile.toml` and run
`lake update cpap-np-hardness` (or `cpap-minor-free`), which rewrites `lake-manifest.json`; then
update `SIBLINGS` in `scripts/check_repository.py` and the commit named in `NOTICE`,
`README.md` and `formalization.yaml`, and re-run the checks of `docs/VERIFICATION.md`. To use
the published sibling directories instead, write `path = "../cpap-np-hardness"` (and
`../cpap-minor-free`) in place of `git` and `rev`; the scripts locate the sources through the
manifest in either case. The git URLs in `lakefile.toml` are placeholders for the published
repositories. The `cpap-minor-free` formalization itself requires `cpap-np-hardness` at the same commit
as this project.
