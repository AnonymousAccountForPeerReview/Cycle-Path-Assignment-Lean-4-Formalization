# Verification

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

Current `lake build` compilation passed with `leanprover/lean4:v4.35.0-rc2`
and the pinned Mathlib. The default targets (`NPHardness`, `Solution`, `NPHardnessAudit`)
and every axiom-guard module passed. All 5 supporting Python tests passed,
with zero skips. The complete build record is `../../verification/compilation.json`.

Retained independent comparison evidence covers 3 selected endpoints,
accepted by six checkers, and 3,173 per-package axiom guards.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Those independent
comparisons were not rerun for the current compilation. Their comparison-input
fingerprints and logs remain separate from current source hashes. Additional OS
isolation was unavailable during the retained comparison runs.

`proofs/verification.json` records the endpoints, comparison outcomes, and current
compilation. `../../SANITATION.json` records all distributed-file hashes.
The root `VERIFICATION.md` explains the compiler environment adaptation and scope.
Generated `Challenge` statements are omitted from the delivered Lean libraries and
default targets. The cited almost-linear minimum-cost-flow algorithm remains an
explicit theorem hypothesis where required.
