# Approximation hardness and reduction programs

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

**Coverage:** Section 6 and Appendix D: L-reductions and approximation hardness. Also supports Section 5 and Appendix C with the RAM model, reduction running time, formula-only planar embedding, and gadget-orientation programs.

## Local statements and companion results

The CPAP reduction and hardness results apply to each fixed `k >= 5`. The paper's bounded-occurrence source has L-reduction constants `alpha = 5/3`, `beta = 1`; the broader imported encoded source uses `alpha = 9`, `beta = 1`. The no-PTAS implications concern `cpapProblem` and the foundation's encoded polynomial-time approximation framework: a hypothetical scheme implies `P = NP`. Planar embedding is proved for the formula-generated incidence family, rather than as an algorithm for arbitrary graphs. RAM bounds count unit-cost instructions and accessed addresses.

The following source links identify declarations in this package. Definition rows identify representations; theorem and lemma rows identify proofs under their stated hypotheses. Names omit only the common `STACS2027.` namespace. The root README gives the complete paper-result map across packages.

| Paper result | Declarations in this package |
| --- | --- |
| Theorem 8 | [gadget_reduction_linear_ram](ApproximationHardness/LinearRAM.lean#L35); [orientation_linear_ram](ApproximationHardness/RunningTimes.lean#L114); [Embed.computedRotation_planar](ApproximationHardness/Embed/Computed.lean#L141); [Embed.computedChoices_planar](ApproximationHardness/Embed/Computed.lean#L150); [Embed.computed_reduction_planar](ApproximationHardness/Embed/Computed.lean#L157); [Embed.planarEmbedding_linear_ram](ApproximationHardness/Embed/PlanarEmbeddingRAM.lean#L76); [Embed.PlanarEmbeddingLinearRAM](ApproximationHardness/Embed/Computed.lean#L167) |
| Definition 9 | [LReductionToCPAP](ApproximationHardness/Optimization.lean#L35); [LReductionSat](ApproximationHardness/Optimization.lean#L43) |
| Lemma 10 | [leOneLeTwo_lreduction](ApproximationHardness/Composition.lean#L64); [polarize_linear_ram](ApproximationHardness/RunningTimes.lean#L46) |
| Theorem 11 | [cpap_lreduction](ApproximationHardness/LReduction.lean#L85); [threeOccurrence_cpap_lreduction](ApproximationHardness/Composition.lean#L71); [max3SAT3_lReducible_cpap](ApproximationHardness/Hardness/Main.lean#L37); [cpap_maxSNPHard](ApproximationHardness/Hardness/Main.lean#L41); [cpap_apxHard](ApproximationHardness/Hardness/Main.lean#L45) |
| Corollary 12 | [cpap_no_ptas](ApproximationHardness/Hardness/Main.lean#L52); [cpap_not_approximable](ApproximationHardness/Hardness/Main.lean#L57) |

## Build and trust boundary

Use `leanprover/lean4:v4.35.0-rc2` and the supplied manifests. From this package directory, retaining the sibling layout:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The default targets are `ApproximationHardness`, `Solution`, `ApproximationHardnessAudit`. The delivered proof libraries contain no `sorry` or added logical axioms; transitive axiom guards permit only `propext`, `Classical.choice`, and `Quot.sound`. Instance, representation, and solver hypotheses remain part of the theorem statements.

`comparator.json` lists selected comparison endpoints, not all proved declarations. Its temporary `Challenge.lean` specification is omitted from the distribution. To reproduce optional comparisons, generate it before building or checking it:

```sh
python3 scripts/generate_challenge.py
lake build Challenge
python3 scripts/check_repository.py
lake comparator --config comparator.json --paranoid
```

The comparator requires its configured checkers and runtime prerequisites. `docs/VERIFICATION.md` and `proofs/` distinguish current compilation from retained independent-comparison evidence.

## Direct dependencies

| Lake package | Declared source |
| --- | --- |
| `np-completeness` | [https://github.com/RBarish-UTokyo/NPCompleteness-Lean4](https://github.com/RBarish-UTokyo/NPCompleteness-Lean4), revision `3e603e795b44fedcf7d6dd65b7d1e30547ead925`. |
| `cpap-np-hardness` | Sibling/bundled path `../cpap-np-hardness`. |
| `pcp` | Sibling/bundled path `../deps/max3sat-maxsnp-apx-derived`. |

`lake-manifest.json` records resolved revisions and inherited dependencies. For each resolved Mathlib package, run `lake exe cache get` inside that Mathlib package directory. `ApproximationHardness.lean` imports this package's library; `Solution.lean` exposes the comparison proofs.

## Source attribution and license

* Robert D. Barish, *NP-completeness of SAT, 3-SAT and their variants (the
  Cook–Levin theorem) in Lean 4*, 2026. Palomar,
  [PALOMAR-2026-10-02-000013 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-02-000013&version=1).
* Robert D. Barish, *MaxSNP-completeness and APX-completeness of MAX-3-SAT and
  3-OCCURRENCE MAX-3-SAT (the PCP theorem and hardness of approximation) in
  Lean 4*, 2026. Palomar,
  [PALOMAR-2026-10-09-000010 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-09-000010&version=1).

Public source citations correspond to the pinned commits above. Apache-2.0;
`LICENSE` and `NOTICE` retain attribution and upstream provenance.
