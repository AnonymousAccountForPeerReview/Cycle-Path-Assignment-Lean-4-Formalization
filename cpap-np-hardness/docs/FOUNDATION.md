# Use of the NP-completeness foundation

This project depends on the NP-completeness foundation `NPCompleteness-Lean4`
(commit `3e603e795b44fedcf7d6dd65b7d1e30547ead925`). `lakefile.toml` requires the
repository at that full commit and `lake-manifest.json` records it;
`scripts/check_repository.py` checks both. No foundation file is copied into
this repository. The library imports `Complexity` modules; the Challenge, which
may import only Lean core, copies the declarations it needs.

## What the Challenge copies

Following the foundation's `docs/FOUNDATION.md`, `Challenge.lean` copies from the
foundation's `Challenge.lean`, verbatim, with docstrings and in the same order:

1. the whole block from `Symbol` through `NPComplete` (machines, polynomial
   time, NP, reductions, NP-hardness and NP-completeness);
2. from the `Complexity.SAT` block, the declarations the statements use:
   `Word` through `Satisfiable`, `writeNat` through `encode`, and
   `IsLeOneLeTwoCNF`;
3. the planarity block, `iterate` through `PlanarGraph`;
4. `incidenceGraph`.

`scripts/generate_challenge.py` reads these from the Lake dependency, located through `lake-manifest.json` (`Challenge.lean` of `np-completeness`), so a copy cannot drift from
the foundation's text. Comparator then checks that each copied declaration is the
same term as the library's.

The foundation's `Literal` derives `DecidableEq` in the library but not in the
foundation's Challenge. To keep the copy verbatim, nothing in this Challenge
needs that instance: `instructionBudget` counts empty records with
`List.countP List.isEmpty` rather than `List.count []`.

## What the library reuses

* `IsLeOneLeTwoCNF`: `boundedOccurrence_iff_registered` identifies Definition
  7's occurrence bounds with the foundation's restriction, and
  `planarLeOneLeTwoSAT_eq` identifies the planar language used in the proofs
  with the foundation-style `PlanarLeOneLeTwoSAT`.
* Planarity: `Complexity.PlanarGraph` is used directly, for incidence graphs
  and for target graphs. Gadget embeddings are the foundation's `EmbedTables`
  certificates checked by `EmbedOK`.
* Machines: the ANONYMIZED–ANONYMIZED emitter, the finite clause-program compiler
  (`StackTableauEmitter.polyTime_emitter`), the planar grid of the planar 3-SAT
  proof, and the foundation's verifier for planar 3-SAT, which
  `PlanarBoundedMembership` extends with the occurrence checks.

Separate NP-hardness of planar 3-SAT and of (≤1,≤2)-SAT does not give
NP-hardness of their intersection. `PlanarSourcePacked*` is a new reduction for
the intersection: an occurrence ring for each variable of the foundation's
planar grid, compiled with the foundation's compiler.

## Reusing this formalization downstream

A later development stating hardness from planar (≤1,≤2)-SAT or from CPAP can copy
this Challenge's declarations the same way: the foundation's blocks first, as
above, then the `STACS2027` declarations it uses, in order. Its Solution
requires this package (by path in this repository, or by git at a full commit) and imports `NPHardness`.
