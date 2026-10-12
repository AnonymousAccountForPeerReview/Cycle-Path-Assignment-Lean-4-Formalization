# Proof records

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

- `axiom-audit.json` records the transitive axiom reports checked by the compiled guards.
- `source-replay.json` records the selected comparison endpoints, accepted checkers, permitted axioms, and successful current package compilation.
- Comparison-input fingerprints and retained logs identify the independent-checker evidence. Where present, separate current-source fields identify distributed files; `../../SANITATION.json` records their complete hashes.
- Independent comparisons were not rerun for the current compilation. The proof library, `Solution`, and every axiom-audit target were compiled, and 5 supporting tests passed.

The generated `Challenge` comparison specification is omitted from the distributed
Lean sources and default targets. Its generator produces a temporary specification
for optional comparison. The delivered proof libraries contain no admitted proofs.
