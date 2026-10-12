# Use of the NP-completeness foundation and of the `cpap-np-hardness` formalization

This project depends on two Lean developments, both a Lake dependency and never copied into this package (the foundation is fetched by git
at a full commit; the formalizations of the other sections are taken from this repository by
path):

* The NP-completeness foundation `NPCompleteness-Lean4` (commit
  `3e603e795b44fedcf7d6dd65b7d1e30547ead925`). The library imports
  `Complexity.SAT` for CNF formulas, truth assignments and satisfiability;
  nothing about machines or complexity classes is used.
* `cpap-np-hardness`, the formalization of Section 5 of the same manuscript, in this repository (the Lake path dependency `../cpap-np-hardness`), which requires the same
  foundation at the same commit. The library imports `NPHardness.OmittedVertex`
  and `NPHardness.CPAP` for the cycle-path assignment problem.

`lakefile.toml` requires both and `lake-manifest.json` records them;
`scripts/check_repository.py` checks the pin of the foundation, the paths of the other
dependencies and that no copy is vendored.

## What the Challenge copies

Following the foundation's `docs/FOUNDATION.md` and the `cpap-np-hardness` formalization's
`docs/FOUNDATION.md` ("Reusing this formalization downstream"), `Challenge.lean`
copies, verbatim, with docstrings and in the same order:

* from the foundation's `Complexity/SAT.lean`, the `Complexity.SAT`
  declarations `Assignment`, `Literal`, `Clause`, `CNF`, `evalLiteral`,
  `evalClause`, `evalCNF` and `Satisfiable` — the declarations the foundation's
  own Challenge uses to state satisfiability;
* from the `cpap-np-hardness` library, the `STACS2027` declarations `Edge` through
  `cost` (`NPHardness/FiniteCycles.lean`), `cycleRepresentatives`, `vertices`
  through `cycles` (`NPHardness/Enumerate.lean`), `selectedOptions`,
  `ValidChoices` and `HasAssignment` — exactly the declarations the Section 5
  Challenge copies for its own statement, so the problem compared here is the
  one stated there.

`scripts/generate_challenge.py` reads them from the Lake dependencies, located through `lake-manifest.json` (`Complexity/SAT.lean` of `np-completeness` and
`NPHardness/` of `cpap-np-hardness`), so a copy cannot drift from the
library text. Comparator then checks that each copied declaration is the same
term as the library's. The encodings themselves (`kCycle` through
`zeroCostFormula`) are copied from `BoundedCost/Encoding.lean` the same way, and
the steps of Algorithm 3 from `BoundedCost/Algorithm3Core.lean` (`kCycleCore`),
`BoundedCost/Algorithm3Recovery.lean` (`markedEdges` through `deletedOverlaps`)
and `BoundedCost/Algorithm3Search.lean` (`IsOptimalCost`, `firstOptionCost`,
`searchOptimum`).

A definition that uses `decide` on a proposition whose instance carries a proof
(such as `decide (e ∈ l)`) elaborates to a proof auxiliary named after the
first declaration of its file that needs it, which differs between the
Challenge and the library. The new definitions therefore use Boolean
operations (`List.contains`, `List.any`, `List.find?`, `==`, `!=`,
`decide (a < b)` on naturals) instead, as the Section 5 definitions do.

## Publishing this package on its own

In this repository `cpap-np-hardness` is a Lake path dependency (`../cpap-np-hardness`). To
publish this package separately, require it by git at a full commit of its published
repository instead and run `lake update cpap-np-hardness`; `scripts/dependencies.py` then finds
its sources under `.lake/packages/`, and the sibling check of `scripts/check_repository.py`
must be adapted to the git form.
