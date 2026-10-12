module

public import ApproximationHardness

/-! Proofs of the thirteen Challenge theorems listed in `comparator.json`:
`STACS2027.cpap_lreduction`, `STACS2027.cpap_optimum`, `STACS2027.leOneLeTwo_lreduction`,
`STACS2027.threeOccurrence_cpap_lreduction`, `STACS2027.gadget_reduction_linear_ram`,
`STACS2027.orientation_linear_ram`, `STACS2027.orientation_polyTime`,
`STACS2027.max3SAT3_lReducible_cpap`, `STACS2027.cpap_maxSNPHard`, `STACS2027.cpap_apxHard`,
`STACS2027.cpap_no_ptas`, `STACS2027.cpap_not_approximable` and `STACS2027.Embed.planarEmbedding_linear_ram`. Importing `ApproximationHardness` also brings
in, and audits, the paper-facing restatements in `ApproximationHardness.Paper` (Theorem 11, Appendix D,
Lemma 10 and Corollary 12) and `ApproximationHardness.RunningTimes`, and the library theorems
`approximation_transfer`, `cpap_lreduction_polyTime`, `polarize_linear_ram`, `polarize_polyTime_machine`,
`decoder_linear_ram` and `decoder_polyTime`. The formula-only planar embedding program
is a compared target; docs/paper-map.md describes its exact scope. -/
