# Use of the `cpap-np-hardness` formalization and of the NP-completeness foundation

This project has two direct Lake dependencies. The foundation is fetched by git at a full commit; the sibling CPAP package is required by path. Neither dependency's source library is vendored in this package:

* `cpap-np-hardness`, the formalization of Section 5 of the same manuscript, in this repository (the Lake path dependency `../cpap-np-hardness`). The library imports
  `NPHardness.AssignmentFamilies` (and through it the cycle-path assignment
  problem, the enumeration of simple `k`-cycles, the selected paths and their
  properties, and the load form of the cost).
* The NP-completeness foundation `NPCompleteness-Lean4` (commit
  `3e603e795b44fedcf7d6dd65b7d1e30547ead925`), required directly and also by `cpap-np-hardness`;
  nothing of it is used directly, as the statement mentions neither formulas
  nor machines.

`lakefile.toml` requires both and `lake-manifest.json` records them;
`scripts/check_repository.py` checks the pin of the foundation, the paths of the other
dependencies and that no copy is vendored.

## What the Challenge copies

`Challenge.lean` is an optional generated comparison specification. It is omitted from the distribution and default build; run `python3 scripts/generate_challenge.py` before building or comparing it. Its target placeholders are separate from the completed proofs in `Approximation/` and `Solution.lean`.

Following the `cpap-np-hardness` formalization's `docs/FOUNDATION.md` ("Reusing this formalization
downstream"), `Challenge.lean` copies, verbatim, with docstrings and in the
same order, the `STACS2027` declarations of the cycle-path assignment problem
(`Edge` through `HasAssignment`, exactly the declarations the Section 5
Challenge copies for its own statement) and the edge load `load`
(`NPHardness/LoadCost.lean`). `scripts/generate_challenge.py` reads them from the
dependency (`NPHardness/` of `cpap-np-hardness`, located through `lake-manifest.json`), so a copy cannot
drift from the library text. Where a Section 5 declaration has no documentation
comment (`load`), the generator inserts one (its `DOCS` table); the declaration
itself is unchanged. Comparator then checks that each copied declaration is the
same term as the library's. The Section 7 definitions (`pathLoad` through
`OptimalFractional`) are copied from `Approximation/` the same way.

## Two elaboration conventions

A definition that uses `decide` on a proposition whose instance carries a proof
elaborates to a proof auxiliary named after the first declaration of its file
that needs it, which differs between the Challenge and the library. The new
definitions therefore use Boolean operations and `List.count`, as the Section 5
definitions do.

Lean shares, within one module, the auxiliary functions that pattern-matching
definitions of the same shape generate (the `match` auxiliaries and, for
matches with a wildcard alternative, the `_sparseCasesOn` auxiliaries). In the
library the Section 7 definitions live in several modules, each with its own
auxiliaries; in the single-module Challenge a definition of the same shape as
an earlier one would reuse the earlier auxiliary and elaborate to a different
term. The Section 7 definitions therefore match with complete constructor
patterns and no wildcard alternative (`weightedSum`, `GreedyRun`,
`RoundingRun`), and no copied definition needs the `set_option` prefix the
generator can add (`FRESH_MATCHER` is empty). Comparator confirms the match.

## Publishing this package on its own

In this repository `cpap-np-hardness` is a Lake path dependency (`../cpap-np-hardness`). To
publish this package separately, require it by git at a full commit of its published
repository instead and run `lake update cpap-np-hardness`; `scripts/dependencies.py` then finds
its sources under `.lake/packages/`, and the sibling check of `scripts/check_repository.py`
must be adapted to the git form.
