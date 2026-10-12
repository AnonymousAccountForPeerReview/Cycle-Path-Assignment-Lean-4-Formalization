# Use of the `cpap-np-hardness` formalization and of the NP-completeness foundation

This project depends on two Lean developments, both a Lake dependency and never copied into this package (the foundation is fetched by git
at a full commit; the formalizations of the other sections are taken from this repository by
path):

* `cpap-np-hardness`, the formalization of Section 5 of the same manuscript, in this repository (the Lake path dependency `../cpap-np-hardness`). `lakefile.toml` requires it
  and `lake-manifest.json` records it; `scripts/check_repository.py` checks
  both. The library imports `NPHardness.CPAP` and `NPHardness.SelectedPaths`.
* The NP-completeness foundation `NPCompleteness-Lean4` (commit
  `3e603e795b44fedcf7d6dd65b7d1e30547ead925`), which `cpap-np-hardness` requires.
  It is required here at the same commit so that the workspace pins one copy.
  Nothing of it is imported or copied: the statement mentions neither machines
  nor formulas.

## What the Challenge copies

Following the `cpap-np-hardness` formalization's `docs/FOUNDATION.md` ("Reusing this formalization
downstream"), `Challenge.lean` copies from the `cpap-np-hardness` library, verbatim, with
docstrings and in the same order, the `STACS2027` declarations it uses:
`Edge` through `cost` (`NPHardness/FiniteCycles.lean`), `cycleRepresentatives`,
`vertices` through `cycles` (`NPHardness/Enumerate.lean`), `selectedOptions` and
`ValidChoices`, and `HasAssignment`. These are exactly the declarations the
Section 5 Challenge copies for its own statement, so the problem compared here
is the one stated there. `scripts/generate_challenge.py` reads them from the dependency (`NPHardness/` of `cpap-np-hardness`, located through `lake-manifest.json`), so a copy cannot drift
from the library text. Comparator then checks that each copied declaration is the
same term as the library's. The Section 3 definitions (`FlowNode` through
`flowCost` from `Tractability/FlowNetwork.lean`, `triangleAt` through
`triangleNodes` from `Tractability/TriangleNetwork.lean`) are copied from this
library the same way.

A definition that uses `decide` on a proposition whose instance carries a proof
(such as `decide (e ∈ l)`) elaborates to a proof auxiliary named after the
first declaration of its file that needs it, which differs between the
Challenge and the library. The new definitions therefore use Boolean
operations (`List.contains`, `==`, `FlowNode.beq`) instead, as the Section 5
definitions do.

## Publishing this package on its own

In this repository `cpap-np-hardness` is a Lake path dependency (`../cpap-np-hardness`). To
publish this package separately, require it by git at a full commit of its published
repository instead and run `lake update cpap-np-hardness`; `scripts/dependencies.py` then finds
its sources under `.lake/packages/`, and the sibling check of `scripts/check_repository.py`
must be adapted to the git form.
