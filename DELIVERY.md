# Source distribution

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

This release contains all eight proof packages, the derived hardness foundation,
verification records, and inline manuscript-result mappings. Preserve the
sibling package layout. Dependency checkouts, build products, and generated independent
comparison statements are excluded. Default Lake targets build the proved
libraries, solutions, and axiom guards.

Use `leanprover/lean4:v4.35.0-rc2` and the pinned Mathlib revision. Dependency
URLs identify the cited public source repositories; commit pins identify the exact revisions.
Run `lake exe cache get` from each actual Mathlib package root. Build packages
in the order recorded in README.md and follow their documented verification
commands. Generate Challenge.lean only for independent statement comparison;
its temporary comparison placeholders are excluded from this distribution.

Project ownership fields are ANONYMIZED. The public-source citations
and AI disclosure remain. Publication years, bibliographic identifiers, commit
pins, licence terms, and mathematical declaration names are preserved.

SANITATION.json records the distributed file hashes. VERIFICATION.md describes
compilation, axiom auditing, supporting tests, and independent comparison evidence.
