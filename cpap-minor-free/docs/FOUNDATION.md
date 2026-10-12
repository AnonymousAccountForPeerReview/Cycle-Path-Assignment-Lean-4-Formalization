# Use of the `cpap-np-hardness` formalization and of the NP-completeness foundation

This project depends on two Lean developments, both a Lake dependency and never copied into this package (the foundation is fetched by git
at a full commit; the formalizations of the other sections are taken from this repository by
path):

* `cpap-np-hardness`, the formalization of Section 5 of the same manuscript, in this repository (the Lake path dependency `../cpap-np-hardness`). The library imports
  `NPHardness.AssignmentFamilies`, `NPHardness.AssignmentRelabel` and
  `NPHardness.GlobalCost` (and through them the cycle-path assignment problem,
  the enumeration of simple `k`-cycles and its representative families, the
  selected paths and their properties, the relabelling lemmas and the cost of
  concatenated path families).
* The NP-completeness foundation `NPCompleteness-Lean4` (commit
  `3e603e795b44fedcf7d6dd65b7d1e30547ead925`), also required by
  `cpap-np-hardness`. Its planarity definition `Complexity.PlanarGraph`
  (`Complexity/Planarity.lean`) states the planarity of `K_{2,r}` in
  `biclique_planar_family`, and `MinorFree/BicliquePlanar.lean` imports
  `Complexity.Planar.Hypermap` for its bounds on the Euler counts
  (`planar_of_bounds`, `cycleCount_ge`, `cycleCount_graphEdge_ge`,
  `componentCount_le`, the reachability lemmas `Linked.*`). The statement
  mentions neither formulas nor machines.

`lakefile.toml` requires both and `lake-manifest.json` records them;
`scripts/check_repository.py` checks the pin of the foundation, the paths of the other
dependencies and that no copy is vendored.

## What the Challenge copies

The planarity block of the NP-completeness foundation (`iterate`, `Hypermap`,
`cycleCount`, `Hypermap.linked`, `Hypermap.componentCount`, `Hypermap.eulerLhs`,
`Hypermap.eulerRhs`, `Hypermap.genus`, `Hypermap.Planar`, `halfEdgeEnd`,
`PlanarGraph`, in the namespace `Complexity`) is copied whole and verbatim, as
the Section 5 Challenge copies it: `scripts/generate_challenge.py` takes the
text between the second `namespace Complexity` and its `end Complexity` in the
foundation's `Challenge.lean` and checks that it is identical to the
declarations of `Complexity/Planarity.lean`, the module the Solution imports.
It comes first in the Challenge, before any `STACS2027` declaration, as in the
foundation and in the Section 5 Challenge.

Following the `cpap-np-hardness` formalization's `docs/FOUNDATION.md` ("Reusing this formalization
downstream"), `Challenge.lean` copies, verbatim, with docstrings and in the
same order, the `STACS2027` declarations of the cycle-path assignment problem
(`Edge` through `HasAssignment`, exactly the declarations the Section 5
Challenge copies for its own statement), `pairCount` (`NPHardness/LoadCost.lean`)
and the vertex relabelling `mapEdge`, `mapGraph` (`NPHardness/GraphRelabel.lean`).
`scripts/generate_challenge.py` reads them from the Lake dependency, located through `lake-manifest.json` (`NPHardness/` of `cpap-np-hardness`), so a copy cannot drift from the
library text. Where a Section 5 declaration has no documentation comment
(`mapEdge`, `mapGraph`), the generator inserts one (its `DOCS` table); the
declaration itself is unchanged. Comparator then checks that each copied
declaration is the same term as the library's. The Section 8 definitions
(`EliminationOrder` through `biclique`) are copied from `MinorFree/` the same
way.

## Two elaboration pitfalls

A definition that uses `decide` on a proposition whose instance carries a proof
elaborates to a proof auxiliary named after the first declaration of its file
that needs it, which differs between the Challenge and the library. The new
definitions therefore use Boolean operations, as the Section 5 definitions do.

Lean shares, within one module, auxiliary `match` functions of the same shape.
`STACS2027.pathEdges` (copied from Section 5) uses three list alternatives;
`STACS2027.earliestIndex` now uses nested empty/cons matches, with the same
executable result. Their matcher shapes therefore differ even when copied into
one independent module. The generator retains the local
`set_option bootstrap.genMatcherCode false in` prefix on `earliestIndex`; it
changes code generation only. Exact constant comparison checks the copied
definition and its auxiliary terms.

## Publishing this package on its own

In this repository `cpap-np-hardness` is a Lake path dependency (`../cpap-np-hardness`). To
publish this package separately, require it by git at a full commit of its published
repository instead and run `lake update cpap-np-hardness`; `scripts/dependencies.py` then finds
its sources under `.lake/packages/`, and the sibling check of `scripts/check_repository.py`
must be adapted to the git form.
