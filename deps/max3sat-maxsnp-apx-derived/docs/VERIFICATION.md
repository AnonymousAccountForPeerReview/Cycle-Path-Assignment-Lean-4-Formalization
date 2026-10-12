# Verification record

All runs below used Lean `v4.35.0-rc2` (the version in `lean-toolchain`) and Mathlib tag
`v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`), on a Linux container with
4 cores and 15 GB of memory, for the revised definition of MaxSNP₀ (see the last item of the
final section), on the upstream tree at commit `10079b2a14bd0df47d2a24364133f6008b9c207f` (before
the repackaging described in `DERIVED.md`).

## Build

* `lake exe cache get`, then a clean `lake build` (project build directory removed first):
  builds `Solution` and all 375 project modules it imports, with no errors and no warnings,
  in 10 min 20 s on 4 cores. The files importing much of `OAI/` need up to about 5 GB of
  memory each.
* `lake build Challenge`: only the nine intended `sorry` warnings.
* `python3 scripts/generate_challenge.py --check`: `Challenge.lean` matches the declarations of
  the library it is generated from.
* `python3 scripts/check_repository.py` (the repository checks: layout, Lean source rules,
  Challenge limits and imports, `comparator.json`, `formalization.yaml`): passes; one warning,
  that `Challenge.lean` (591 lines, 26 KiB) is above the 300-line preferred audit size (the hard
  limit is 1,000 lines). `formalization.yaml` validates against the `formalization.yaml` v0.4
  JSON schema.
* No source file contains `sorry` (except the Challenge's intended holes), `native_decide`,
  `axiom`, `implemented_by` or `extern`. Every `.lean` file uses the module system, and the
  largest file has 1,746 lines.

## Axioms

`#print axioms` for each compared theorem (`Complexity.pcp_gap`, `pcp_theorem`,
`npo_maxSNP0`, `maxSNPHard_no_ptas`, `maxSNPHard_not_hasPTAS`, `max3SAT_maxSNPComplete`,
`max3SAT3_maxSNPComplete`, `max3SAT_apxComplete`, `max3SAT3_apxComplete`) and for the
intermediate `Complexity.witnessGap` prints

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Comparator

* `lake comparator --config comparator.json --paranoid` (sandboxed with bubblewrap, all
  checkers bundled with the toolchain on `PATH`), for the nine compared theorems: NanoDa, Lean's
  paranoid kernel, lean4lean (33,969 declarations), con-leche and con-ron (33,968 declarations
  each) and Lean's default kernel all accept the solution: "Your solution is okay!"
  (6 min 51 s).
* The previous version of the statement (commit `f308490`, before the revision of MaxSNP₀) was
  in addition checked with the standalone [Comparator](https://github.com/leanprover/comparator)
  (commit `ca04cfc`, with lean4export `v4.35.0-rc2` and landrun) and with the toolchain's
  `nanoda_bin` and `con-ron` run directly on the lean4export of `Solution`. These runs were not
  repeated for this version.

## Problems found and fixed along the way

* Comparator first reported `Const does not match between challenge and target
  'Complexity.tuples._f'`: inside the single Challenge module, the pattern-matching definitions
  `allWords` and `tuples` reused the match compiler's auxiliary declaration of `SAT.writeNat`,
  which the library, split into modules, does not. Both are now defined without pattern
  matching (with `Nat.repeat`) and come with equation lemmas `allWords_zero/succ`,
  `tuples_zero/succ`.
* NanoDa overflowed its 16 MB thread stack on `RoundTables.sizeFactor_positive` and
  `RoundTables.build_size_le` (vendored code), because it unfolded the definition of the
  astronomically large constant `RoundTables.sizeFactor` instead of comparing it lazily. The
  value of `sizeFactor` is now stored behind an opaque constant (`sizeFactorData`, as upstream
  already does for `fixedWalkParameter`) with the equation `sizeFactor_eq`.
* `max3SAT` first allowed assignment words of any length, which put it outside NPO (proved
  formally as `not_npo_max3SATu`); solutions are now required to be no longer than the
  instance. The unbounded variant survives as the internal auxiliary problem `max3SATu`.
* `maxSNP0` first allowed solutions with any number of relations, repeated tuples and tuples
  of any length or outside the universe, which put the problems of the syntactic class outside
  NPO (proved formally as `not_npo_maxSNP0` at commit `f308490`). MaxSNP₀ now has fixed input
  and solution signatures: instances and solutions are structures of those signatures on the
  universe of the instance (`Relations.Fits`), the formula must be well formed for them
  (`QF.WellFormed`), and MaxSNP consists of the NPO problems L-reducible to such a problem. The solution map of the
  L-reduction to MAX-3-SAT now cuts a structure of the solution signature out of the relations
  written by an assignment (`fitRel`, which does not change the value of a well-formed
  formula), and MAX-3-SAT reaches MaxSNP through `max3SAT` (in NPO) instead of the unbounded
  `max3SATu`. The new compared theorem `npo_maxSNP0` proves that every MaxSNP₀ problem is in
  NPO.
