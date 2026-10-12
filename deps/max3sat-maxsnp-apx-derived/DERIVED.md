# Derived packaging of Max3SAT-MaxSNP-APX-Lean4

This tree is the upstream repository Max3SAT-MaxSNP-APX-Lean4 at commit
`10079b2a14bd0df47d2a24364133f6008b9c207f`, repackaged by `derive_pcp.sh` so that it can share a Lake workspace with
the NP-completeness foundation NPCompleteness-Lean4 at commit `3e603e795b44fedcf7d6dd65b7d1e30547ead925`, on which the STACS 2027
formalization already depends.

Lake resolves an import by module name: every package whose libraries match the name provides
the module, and two packages cannot both provide one (each `.olean` records its package).
NPCompleteness-Lean4's library `Complexity` matches every module name `Complexity.*`.

The only changes:

* the 75 upstream `Complexity/` files that are byte-identical to NPCompleteness-Lean4 at
  `3e603e795b44fedcf7d6dd65b7d1e30547ead925` are removed (checked byte for byte with `cmp`); that package provides them;
* the 12 other `Complexity/` modules, which NPCompleteness-Lean4 does not have, are moved under
  the module prefix `ComplexityExt` (`Complexity/X.lean` becomes `ComplexityExt/X.lean`), and
  the `import` lines naming them are rewritten accordingly; declarations and namespaces are
  unchanged (they stay in `Complexity`, `Complexity.Reg`, ...);
* `lakefile.toml` requires np-completeness at `3e603e795b44fedcf7d6dd65b7d1e30547ead925` and declares the library
  `ComplexityExt` (globs `ComplexityExt.+`) in place of `Complexity`;
* the documentation and metadata (`README.md`, `formalization.yaml`, `docs/`,
  `.github/workflows/`) are edited after derivation, one upstream CI workflow is dropped, and the
  upstream repository-check scripts are renamed `scripts/check_repository.py` and
  `scripts/verify_all.sh`; `verify_derived_pcp.sh` does not compare these files;
* this file is added.

Undoing the move and the import rewriting gives back every other upstream file byte for byte
(`verify_derived_pcp.sh`). The moved modules:

* `Complexity.Approx.Defs` → `ComplexityExt.Approx.Defs`
* `Complexity.PCP.Defs` → `ComplexityExt.PCP.Defs`
* `Complexity.Reg` → `ComplexityExt.Reg`
* `Complexity.Reg.Clocked` → `ComplexityExt.Reg.Clocked`
* `Complexity.Reg.Closure` → `ComplexityExt.Reg.Closure`
* `Complexity.Reg.Cmd` → `ComplexityExt.Reg.Cmd`
* `Complexity.Reg.Compile` → `ComplexityExt.Reg.Compile`
* `Complexity.Reg.Decide` → `ComplexityExt.Reg.Decide`
* `Complexity.Reg.Derived` → `ComplexityExt.Reg.Derived`
* `Complexity.Witness.Extract` → `ComplexityExt.Witness.Extract`
* `Complexity.Witness.Main` → `ComplexityExt.Witness.Main`
* `Complexity.Witness.Tableau` → `ComplexityExt.Witness.Tableau`

Files whose `import` lines were rewritten:

* `Bridge/Total.lean`
* `ComplexityExt/Approx/Defs.lean`
* `ComplexityExt/Reg.lean`
* `ComplexityExt/Reg/Clocked.lean`
* `ComplexityExt/Reg/Closure.lean`
* `ComplexityExt/Reg/Compile.lean`
* `ComplexityExt/Reg/Decide.lean`
* `ComplexityExt/Reg/Derived.lean`
* `ComplexityExt/Witness/Main.lean`
* `ComplexityExt/Witness/Tableau.lean`
* `Hardness/APX/Defs.lean`
* `Hardness/APX/Reduction.lean`
* `Hardness/Formula.lean`
* `Hardness/GapPCP.lean`
* `Hardness/MaxSNP/Defs.lean`
* `Hardness/MaxSNP/Hard/Defs.lean`
* `Hardness/MaxSNP/LReduction.lean`
* `Hardness/Unbounded.lean`
* `Hardness/Verifier/Checker.lean`
* `Hardness/Verifier/Sampling.lean`
* `Hardness/Verifier/Words.lean`
* `Hardness/Witness/Main.lean`
* `Hardness/Witness/Pipeline.lean`
* `PT/SAT.lean`
* `PT/Word.lean`
* `PT/Words.lean`
