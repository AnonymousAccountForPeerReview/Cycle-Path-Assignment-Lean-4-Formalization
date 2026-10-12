# Verification

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

The distribution contains 1,448 Lean files and eight proof packages. Dependency
pins and mathematical declaration names are recorded in their manifests.

The retained package records document 101 compared endpoints, six configured
kernel checkers, 18,742 per-package axiom guards (including 74 repeated checks),
and 86 prescribed tests. Source fingerprint records agree with the original
sanitation provenance. These are the recorded verification results for the
mathematical source. Artifact dates have been normalized for this distribution.

For this release, source-rule, dependency-pin, applicable import-closure, and
axiom-guard coverage checks passed across all eight packages. Every retained
guard agrees with its recorded axiom set. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted; no executable `sorry`, `admit`, or added axioms occur
in the delivered proof libraries. The cited almost-linear minimum-cost-flow
result remains an explicit theorem hypothesis, with its scope explained in
README.md and the appendix.

Fresh compilation on 2026-10-12 passed for all eight packages, using
`leanprover/lean4:v4.35.0-rc2` (commit
`11acb17ec6b07a8f9e9173e6845197929540936b`) and Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The command `lake exe cache get`
succeeded from the actual Mathlib package root. Each subsequent `lake build`
succeeded with the package's library, `Solution`, and axiom-audit targets.
The supporting Python tests passed 86 of 86, with zero skips. All 1,448
distributed Lean files match the freshly built source copies byte for byte.

The official compiler distribution was checked against its release archive:
all 17,918 extracted regular files matched. This build host lacks
`/proc/self/exe`, so an executable-path adapter supplied the running executable
path solely for application-directory discovery. Other path queries delegated
to the system library. No compiler, kernel, proof library, or Lean source bytes
were changed by this adapter. It introduces no logical axiom; ordinary hosts
with executable-path discovery do not need it.

The six independent kernel comparisons described above are retained verification
evidence; they were not rerun in this fresh compilation. Exact compilation
results and dependency pins are recorded in `verification/compilation.json`.
Reproduction steps remain in each package's documentation and manifests.

Challenge.lean files are generated independent comparison statements and are
excluded from this distribution and all eight default build targets. They are
not part of the delivered proof library.
