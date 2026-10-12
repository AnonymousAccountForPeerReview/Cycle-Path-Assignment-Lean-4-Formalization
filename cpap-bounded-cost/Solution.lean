module

public import BoundedCost

/-! Proofs of the twenty-one Challenge theorems listed in `comparator.json`: the encodings of
Theorem 4 and Corollary 5 and their sizes (`STACS2027.almostSatisfiable_iff_hasAssignment`,
`STACS2027.almostFormula_size`, `STACS2027.zeroCostFormula_satisfiable_iff`,
`STACS2027.zeroCostFormula_size`), the exact prefix counts added in the paper
(`STACS2027.prefixClauses_length`, `STACS2027.prefixAuxiliaryVariables_count`),
the steps of Algorithm 3 (the `k`-cycle core, the deleted
overlaps, the recovery of the paths, the case `Ψ = 0`, `STACS2027.algorithm3_correct`) and
computing `OPT` by increasing `Ψ`. Importing `BoundedCost` also brings in, and audits, the
paper-facing restatements in `BoundedCost.Paper` (Theorem 4, Appendix B and Corollary 5). -/
