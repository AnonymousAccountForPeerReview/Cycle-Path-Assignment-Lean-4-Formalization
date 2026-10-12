# Cycle-Path-Assignment-Lean-4-Formalization

Lean 4 formalization accompanying *Cycle-Path Assignment for Local Differential Privacy: Complexity and Approximation*.

This README describes the recorded verified proof scope as of **2026-10-12**. The delivered Lean libraries use only `propext`, `Classical.choice`, and `Quot.sound`: they contain no `sorry` or additional logical axioms. Algorithmic conclusions retain their stated graph, representation, comparison, and optimization hypotheses. In particular, results using almost-linear minimum-cost flow are implications with explicit solver premises; the cited flow algorithm itself is outside the formalization.

The differential-privacy introduction and covariance motivation are not an end-to-end proof of a privacy or statistical mechanism. The formalized subject is the cycle-path assignment problem (CPAP), its reductions, complexity, approximation guarantees, and specified computational models.

## Repository layout

The folders are named by mathematical topic. The table maps each package to the paper's sections and supporting appendices.

| Package | Coverage and role |
| --- | --- |
| `cpap-tractability` | Section 3 and Appendix A: four-cycle and triangle flow correspondences and network sizes; their timed programs are in `cpap-runtimes`. |
| `cpap-bounded-cost` | Section 4 and Appendix B: bounded-cost and zero-cost encodings for cycle lengths at least four, Algorithm 3 recovery given correct solver outputs, and functional optimum-search correctness. The triangle branch and executed solver/search programs are in the companion packages. |
| `cpap-np-hardness` | Section 2.2, Section 5, and Appendix C: the shared CPAP model and objective identity, gadgets, planar bounded-occurrence SAT, and NP-hardness. |
| `cpap-approximation-hardness` | Section 6 and Appendix D: L-reductions and approximation hardness. Also supports Section 5 and Appendix C with the RAM model, reduction running time, formula-only planar embedding, and gadget-orientation programs. |
| `cpap-approximation` | Section 7: correctness and guarantees for Algorithm 1, independent randomized rounding, and Algorithm 2. The greedy running-time proof of Lemma 15 and the exact rational fractional-solution solver of Lemma 16 are in `cpap-runtimes`. |
| `cpap-minor-free` | Section 8; Appendix E: Algorithm 4 assignment correctness given elimination-order and common-neighbor hypotheses, the $K_4$ four-cycle assignment, blockwise assignments, and planar biclique cost bounds. Appendix F: supporting $K_4$ no-long-cycle facts and block-combination results. |
| `cpap-outerplanar` | Section 8 and Appendices E and F: excluded-minor structure, common-neighbor and elimination-order proofs completing Algorithm 4, the planar-triangle assignment theorem, weak-dual and dynamic-programming proofs in the polygon representation, and exact linear-time algorithms. |
| `cpap-runtimes` | Sections 3, 4, and 7, and Appendices A and B: RAM programs for flow construction/extraction and composition, cycle enumeration, 2-SAT, Almost 2-SAT on the stated encoded-formula domain, optimum search, greedy assignment, and exact rational convex-relaxation solving on supplied cycle lists. Flow-dependent conclusions retain their explicit solver hypotheses; the cited almost-linear flow implementation remains external. |

The packages share definitions and supporting proofs across these topics. `cpap-np-hardness` supplies the CPAP model from Section 2.2; `cpap-approximation-hardness` also implements the Section 5 reduction and planar embedding. The two structural packages jointly cover Section 8. The result tables below identify each proof's precise source.

## Paper results and Lean proofs

The tables map every numbered Definition, Theorem, Corollary, and Lemma in the paper, followed by Algorithms 1–4, directly to Lean declarations. Each declaration links to its source. Names omit only the common `STACS2027.` namespace; `Runtimes.` is retained where needed. Definition rows identify representations; theorem and lemma rows identify checked proofs under their stated hypotheses.

**A** means the permitted Lean axioms only: `propext`, `Classical.choice`, and `Quot.sound`. **F** also requires an explicit correct minimum-cost-flow solver with a supplied resource bound. **F+** additionally requires its almost-linear bound, corresponding to the cited flow paper. Unmarked declarations have dependency A; F and F+ are marked beside the affected declarations. These are theorem premises, not added Lean axioms. Mixed rows distinguish the unconditional mathematical reduction from its flow-dependent running-time conclusions. Ordinary graph, representation, optimization, and input hypotheses remain explicit.

### Results in the main text

| Paper result | Formalized subject | Lean declarations (source links) | Dependencies |
| --- | --- | --- | --- |
| Definition 1 | Cycle-path assignments and load objective | [`cycles`](cpap-np-hardness/NPHardness/Enumerate.lean#L35); [`selected`](cpap-np-hardness/NPHardness/FiniteCycles.lean#L57); [`cost`](cpap-np-hardness/NPHardness/FiniteCycles.lean#L105); [`HasAssignment`](cpap-np-hardness/NPHardness/CPAP.lean#L16); [`Paper.cpap_objective`](cpap-np-hardness/NPHardness/Paper.lean#L320) | A |
| Theorem 2 | Four-cycle minimum-cost-flow reduction | [`cpap4_iff_flow`](cpap-tractability/Tractability/FlowEquivalence.lean#L336); [`fourCycleNetwork_size`](cpap-tractability/Tractability/NetworkSize.lean#L201); [`Runtimes.Flow.cpap4_flow_ram_semantic`](cpap-runtimes/Runtimes/Flow/Statement.lean#L76) **F**; [`Runtimes.Flow.cpap4_flow_single`](cpap-runtimes/Runtimes/Flow/Single.lean#L129) **F**; [`Runtimes.Flow.polynomialMinCostFlowSolverExists_of_almostLinear`](cpap-runtimes/Runtimes/Flow/PolynomialBound.lean#L63) **F+**; [`Runtimes.Flow.cpap4_flow_ram_almostLinear`](cpap-runtimes/Runtimes/Flow/Main.lean#L302) **F+**; [`Runtimes.Flow.cpap4_flow_single_almostLinear`](cpap-runtimes/Runtimes/Flow/Single.lean#L181) **F+** | A, F, F+ |
| Corollary 3 | Complete optimal four-cycle assignment algorithm | [`Runtimes.fourCycleAssignment_single_explicit`](cpap-runtimes/Runtimes/CpapSingle/Complete.lean#L21) **F**; [`Runtimes.fourCycleAssignment_single`](cpap-runtimes/Runtimes/CpapSingle/Complete.lean#L68) **F+**; [`Runtimes.C4.fourCycles_ram_semantic`](cpap-runtimes/Runtimes/C4/Statement.lean#L40); [`Runtimes.C4.fourCycles_ram_paper_semantic`](cpap-runtimes/Runtimes/C4/Statement.lean#L57); [`Runtimes.C4.fourCycles_ram_simple_semantic`](cpap-runtimes/Runtimes/C4/Statement.lean#L81) | A, F, F+ |
| Theorem 4 | Fixed-parameter bounded-cost assignment | [`almostSatisfiable_iff_hasAssignment`](cpap-bounded-cost/BoundedCost/Equivalence.lean#L95); [`almostFormula_size`](cpap-bounded-cost/BoundedCost/Sizes.lean#L415); [`Runtimes.BoundedCost.actualCompilerRAM_fpt`](cpap-runtimes/Runtimes/BoundedCost/ActualCompilerRAM.lean#L56) **F+**; [`Runtimes.BoundedCost.almostTwoSatFptSolverExists_of_citedFlow`](cpap-runtimes/Runtimes/BoundedCost/ActualCompilerRAM.lean#L89) **F+**; [`Runtimes.BoundedCost.boundedCost_ram_fpt_from_citedFlow`](cpap-runtimes/Runtimes/BoundedCost/ActualFPT.lean#L15) **F+**; [`Runtimes.BoundedCost.Almost2SatSolver`](cpap-runtimes/Runtimes/BoundedCost/Solver.lean#L76); [`Runtimes.BoundedCost.FPTBound`](cpap-runtimes/Runtimes/BoundedCost/Solver.lean#L84) | A, F+ |
| Corollary 5 | Zero-cost assignment via 2-SAT or triangle flow | [`zeroCostFormula_satisfiable_iff`](cpap-bounded-cost/BoundedCost/ZeroCost.lean#L310); [`zeroCostFormula_size`](cpap-bounded-cost/BoundedCost/Sizes.lean#L426); [`Runtimes.ZeroCost.zeroCost_ram`](cpap-runtimes/Runtimes/ZeroCost.lean#L240); [`Runtimes.TwoSat.exists_linear_twoSat`](cpap-runtimes/Runtimes/TwoSatMain.lean#L189); [`Runtimes.Flow.triangle_single`](cpap-runtimes/Runtimes/Flow/Single.lean#L155) **F**; [`Runtimes.Flow.triangle_single_almostLinear`](cpap-runtimes/Runtimes/Flow/Single.lean#L210) **F+** | A, F, F+ |
| Theorem 6 | Planar bounded-occurrence SAT and CPAP NP-hardness | [`planarLeOneLeTwoSAT_np_complete`](cpap-np-hardness/NPHardness/PlanarSourceHardness.lean#L41); [`planarCPAP_np_hard`](cpap-np-hardness/NPHardness/PlanarTargetHardness.lean#L39); [`cpap_np_hard`](cpap-np-hardness/NPHardness/CPAPHardness.lean#L70) | A |
| Definition 7 | Bounded positive/negative-occurrence CNF | [`Paper.LeOneLeTwoCNF`](cpap-np-hardness/NPHardness/Paper.lean#L328); [`BoundedOccurrence`](cpap-np-hardness/NPHardness/BoundedSAT.lean#L21) | A |
| Theorem 8 | SAT-to-CPAP gadget reduction and planar realization | [`formulaGraph_sat_iff_assignment`](cpap-np-hardness/NPHardness/GlobalCompleteness.lean#L126); [`Paper.gadget_reduction_full_domain`](cpap-np-hardness/NPHardness/Paper.lean#L386); [`Paper.gadget_reduction_planar`](cpap-np-hardness/NPHardness/Paper.lean#L377); [`gadget_reduction_linear_ram`](cpap-approximation-hardness/ApproximationHardness/LinearRAM.lean#L35); [`orientation_linear_ram`](cpap-approximation-hardness/ApproximationHardness/RunningTimes.lean#L114); [`Embed.computedRotation_planar`](cpap-approximation-hardness/ApproximationHardness/Embed/Computed.lean#L141); [`Embed.computedChoices_planar`](cpap-approximation-hardness/ApproximationHardness/Embed/Computed.lean#L150); [`Embed.computed_reduction_planar`](cpap-approximation-hardness/ApproximationHardness/Embed/Computed.lean#L157); [`Embed.planarEmbedding_linear_ram`](cpap-approximation-hardness/ApproximationHardness/Embed/PlanarEmbeddingRAM.lean#L76); [`Embed.PlanarEmbeddingLinearRAM`](cpap-approximation-hardness/ApproximationHardness/Embed/Computed.lean#L167) | A |
| Definition 9 | L-reductions between optimization problems | [`LReductionToCPAP`](cpap-approximation-hardness/ApproximationHardness/Optimization.lean#L35); [`LReductionSat`](cpap-approximation-hardness/ApproximationHardness/Optimization.lean#L43) | A |
| Lemma 10 | SAT normalization and approximation-preserving reduction | [`leOneLeTwo_lreduction`](cpap-approximation-hardness/ApproximationHardness/Composition.lean#L64); [`polarize_linear_ram`](cpap-approximation-hardness/ApproximationHardness/RunningTimes.lean#L46) | A |
| Theorem 11 | MaxSNP-hardness and APX-hardness of CPAP | [`cpap_lreduction`](cpap-approximation-hardness/ApproximationHardness/LReduction.lean#L85); [`threeOccurrence_cpap_lreduction`](cpap-approximation-hardness/ApproximationHardness/Composition.lean#L71); [`max3SAT3_lReducible_cpap`](cpap-approximation-hardness/ApproximationHardness/Hardness/Main.lean#L37); [`cpap_maxSNPHard`](cpap-approximation-hardness/ApproximationHardness/Hardness/Main.lean#L41); [`cpap_apxHard`](cpap-approximation-hardness/ApproximationHardness/Hardness/Main.lean#L45) | A |
| Corollary 12 | No PTAS and approximation-hardness implications | [`cpap_no_ptas`](cpap-approximation-hardness/ApproximationHardness/Hardness/Main.lean#L52); [`cpap_not_approximable`](cpap-approximation-hardness/ApproximationHardness/Hardness/Main.lean#L57) | A |
| Lemma 13 | Greedy squared-load inequality | [`greedy_sq_load_bound`](cpap-approximation/Approximation/GreedyBound.lean#L37) | A |
| Theorem 14 | Greedy assignment approximation bound | [`greedy_is_assignment`](cpap-approximation/Approximation/Theorems.lean#L119); [`greedy_cost_bound`](cpap-approximation/Approximation/GreedyBound.lean#L62); [`greedy_cost_integer_bound`](cpap-approximation/Approximation/GreedyBound.lean#L76) | A |
| Lemma 15 | Greedy algorithm running time and memory | [`Runtimes.Greedy.greedy_ram`](cpap-runtimes/Runtimes/Greedy/Main.lean#L120); [`Runtimes.Greedy.greedy_guarantee_ram`](cpap-runtimes/Runtimes/Greedy/Main.lean#L137) | A |
| Lemma 16 | Exact polynomial-time convex quadratic relaxation | [`Runtimes.QPRam.relaxSolver_ram_optimal`](cpap-runtimes/Runtimes/ConvexQP/RAM/RelaxSolver.lean#L80) | A |
| Theorem 17 | Randomized-rounding assignment and expected cost | [`rounding_is_assignment`](cpap-approximation/Approximation/Theorems.lean#L127); [`randomized_rounding_cost_bound`](cpap-approximation/Approximation/Theorems.lean#L85) | A |
| Theorem 18 | Deterministic conditional-rounding guarantee | [`conditional_rounding_cost_bound`](cpap-approximation/Approximation/Theorems.lean#L61); [`conditionalRounding`](cpap-approximation/Approximation/Rounding.lean#L64) | A |
| Lemma 19 | Excluded-minor characterization and block structure | [`outerplanar_block_structure`](cpap-outerplanar/Outerplanar/OuterplanarCharacterization.lean#L53); [`outerplanarDrawing_iff_minorFree`](cpap-outerplanar/Outerplanar/OuterplanarCharacterization.lean#L39); [`twoConnected_outerplanar_or_k4`](cpap-outerplanar/Outerplanar/OuterplanarConstruct.lean#L61) | A |
| Theorem 20 | Perfect assignments on K₂,₃-minor-free graphs | [`k23_perfect`](cpap-outerplanar/Outerplanar/PerfectK23.lean#L207); [`perfect_assignment_of_blocks`](cpap-minor-free/MinorFree/Blocks.lean#L158); [`k4_cycle_assignments`](cpap-minor-free/MinorFree/K4.lean#L60); [`hasAssignment_blocks`](cpap-minor-free/MinorFree/Blocks.lean#L109) | A |
| Theorem 21 | Linear-time exact assignment on K₂,₃-minor-free graphs | [`k23_linear_ram`](cpap-outerplanar/Outerplanar/LinearK23.lean#L100); [`k23_linear_ram_solve`](cpap-outerplanar/Outerplanar/LinearK23.lean#L89) | A |

### Results in the paper's appendices

| Paper result | Formalized subject | Lean declarations (source links) | Dependencies |
| --- | --- | --- | --- |
| Definition 22 | Gadget graph and edge identification | [`formulaGraph`](cpap-np-hardness/NPHardness/GlobalGraph.lean#L30); [`orientedFormulaGraph`](cpap-np-hardness/NPHardness/OrientedGluing.lean#L28) | A |
| Lemma 23 | Planar biclique family with cubic optimal cost | [`biclique_planar_family`](cpap-minor-free/MinorFree/BicliquePlanar.lean#L319); [`cost_lower_bound`](cpap-minor-free/MinorFree/LoadBounds.lean#L126) | A |
| Lemma 24 | At most two common neighbors in K₂,₃-minor-free graphs | [`common_neighbours_le_two`](cpap-outerplanar/Outerplanar/Minors.lean#L67); [`commonNeighbourBound_of_k23MinorFree`](cpap-outerplanar/Outerplanar/Minors.lean#L90) | A |
| Lemma 25 | Outerplanar elimination and perfect assignment | [`outerplanar_degenerate`](cpap-outerplanar/Outerplanar/GeneralDegenerate.lean#L157); [`outerplanar_eliminationOrder`](cpap-outerplanar/Outerplanar/GeneralDegenerate.lean#L193); [`outerplanarDrawing_subgraph`](cpap-outerplanar/Outerplanar/GeneralDegenerate.lean#L198); [`outerplanar_algorithm_perfect`](cpap-outerplanar/Outerplanar/GeneralAlgorithm.lean#L13); [`outerplanar_algorithm_assignment`](cpap-outerplanar/Outerplanar/GeneralAlgorithm.lean#L26) | A |
| Definition 26 | Weak dual and subtree representation | [`DualAdj`](cpap-outerplanar/Outerplanar/WeakDual.lean#L69); [`IsSubtree`](cpap-outerplanar/Outerplanar/WeakDual.lean#L75); [`IsPolygon.segTree`](cpap-outerplanar/Outerplanar/Segments.lean#L155); [`IsPolygon.weakDual_tree`](cpap-outerplanar/Outerplanar/WeakDualFacts.lean#L161) | A |
| Lemma 27 | Weak-dual edges and face boundaries | [`IsPolygon.chord_dualEdge_bij`](cpap-outerplanar/Outerplanar/WeakDualFacts.lean#L106); [`IsPolygon.bdry_ne_empty`](cpap-outerplanar/Outerplanar/WeakDualFacts.lean#L170); [`IsPolygon.bdry_deg`](cpap-outerplanar/Outerplanar/WeakDualFacts.lean#L268) | A |
| Lemma 28 | Leaf-face deletion and weak-dual transport | [`IsPolygon.leaf_face`](cpap-outerplanar/Outerplanar/WeakDualFacts.lean#L305); [`IsPolygon.leaf_face_deletion`](cpap-outerplanar/Outerplanar/LeafFaceDeletion.lean#L146) | A |
| Lemma 29 | Cycle–subtree bijection and boundary length | [`IsPolygon.cycle_subtree_bij`](cpap-outerplanar/Outerplanar/WeakDualBij.lean#L620); [`IsPolygon.cycle_subtree_bij_simpleCycles`](cpap-outerplanar/Outerplanar/WeakDualBij.lean#L652) | A |
| Lemma 30 | Owned edges and edge partition | [`IsPolygon.own_spec`](cpap-outerplanar/Outerplanar/Segments.lean#L302); [`IsPolygon.total_eq`](cpap-outerplanar/Outerplanar/DPCorrect.lean#L243) | A |
| Lemma 31 | Parent/child and enclosed-face dichotomies | [`IsPolygon.cycle_child_dichotomy`](cpap-outerplanar/Outerplanar/NamedHoles.lean#L137); [`IsPolygon.top_face_iff_parent_not_enclosed`](cpap-outerplanar/Outerplanar/NamedHoles.lean#L77); [`IsPolygon.boundary_iff_parent_enclosed`](cpap-outerplanar/Outerplanar/NamedHoles.lean#L92) | A |
| Lemma 32 | Assignment of cycles to top or boundary states | [`TreeDP.Problem.top_eq_or_mem_boundary`](cpap-outerplanar/Outerplanar/TreeDP.lean#L311) | A |
| Lemma 33 | Child-boundary cycle assignment | [`TreeDP.Problem.boundary_child`](cpap-outerplanar/Outerplanar/TreeDP.lean#L322) | A |
| Lemma 34 | Dynamic-programming recurrence and root optimum | [`IsPolygon.dp_root_optimal`](cpap-outerplanar/Outerplanar/DPCorrect.lean#L262); [`IsPolygon.dp_table_correct`](cpap-outerplanar/Outerplanar/DPCorrect.lean#L300) | A |
| Lemma 35 | Exact outerplanar solver running time and memory | [`outerplanar_linear_ram`](cpap-outerplanar/Outerplanar/LinearK23.lean#L113) | A |

### Algorithms

| Paper result | Formalized subject | Lean declarations (source links) | Dependencies |
| --- | --- | --- | --- |
| Algorithm 1 | Greedy path selection | [`greedy_is_assignment`](cpap-approximation/Approximation/Theorems.lean#L119); [`greedy_cost_bound`](cpap-approximation/Approximation/GreedyBound.lean#L62); [`greedy_cost_integer_bound`](cpap-approximation/Approximation/GreedyBound.lean#L76) | A |
| Algorithm 2 | Conditional-expectation rounding | [`conditional_rounding_cost_bound`](cpap-approximation/Approximation/Theorems.lean#L61); [`conditionalRounding`](cpap-approximation/Approximation/Rounding.lean#L64) | A |
| Algorithm 3 | Bounded-cost recovery and optimum search | [`cycles_kCycleCore`](cpap-bounded-cost/BoundedCost/Algorithm3Core.lean#L268); [`hasAssignment_kCycleCore_iff`](cpap-bounded-cost/BoundedCost/Algorithm3Core.lean#L274); [`deletedOverlaps_spec`](cpap-bounded-cost/BoundedCost/Algorithm3Recovery.lean#L212); [`recoverAssignment_correct`](cpap-bounded-cost/BoundedCost/Algorithm3Recovery.lean#L191); [`algorithm3_correct`](cpap-bounded-cost/BoundedCost/Algorithm3.lean#L40); [`searchOptimum_correct`](cpap-bounded-cost/BoundedCost/Algorithm3Search.lean#L182); [`Runtimes.BoundedCost.optimalCost_ram_fpt_from_citedFlow`](cpap-runtimes/Runtimes/BoundedCost/OptMain.lean#L85) **F+** | A, F+ |
| Algorithm 4 | Perfect outerplanar assignment by elimination | [`outerplanar_degenerate`](cpap-outerplanar/Outerplanar/GeneralDegenerate.lean#L157); [`outerplanar_eliminationOrder`](cpap-outerplanar/Outerplanar/GeneralDegenerate.lean#L193); [`outerplanarDrawing_subgraph`](cpap-outerplanar/Outerplanar/GeneralDegenerate.lean#L198); [`outerplanar_algorithm_perfect`](cpap-outerplanar/Outerplanar/GeneralAlgorithm.lean#L13); [`outerplanar_algorithm_assignment`](cpap-outerplanar/Outerplanar/GeneralAlgorithm.lean#L26) | A |

Appendix G of the accompanying paper explains the formalization and its dependencies.

Several distinctions matter when interpreting these results:

* The planar embedding algorithm applies to the formula-generated reduction family. It is not a general embedding algorithm for arbitrary graphs.
* Approximation algorithms require duplicate-free edge lists where their statements specify them. Other ordinary graph, model, comparison, testing, and fractional-optimum hypotheses remain explicit.
* The RAM model has unit-cost, unbounded natural-number cells. Bounds cover steps and maximum read/write address, not bit complexity. Label-dependent memory bounds are distinguished from label-independent sorted construction; output-stream exclusions must be read with the relevant bounds.
* Hardness uses explicit single-tape machines and coded words. The no-PTAS implications derive `PEqNP` from a hypothetical approximation scheme; they do not assume that P differs from NP.

## How the proof goes

The development first relates feasible assignments and their objective values to graph, flow, and Boolean encodings. Mathematical flow equivalences do not require a flow algorithm. Runtime conclusions then connect those encodings to programs with specified resource bounds and, where needed, explicitly supplied solver witnesses.

For minimum-cost flow, `Flow.MinCostFlowSolver F T` specifies program correctness and bounds both steps and read/write addresses by `T(N)` on `GoodNet`. `Flow.AlmostLinear T` requires that for every positive epsilon there is a constant `C` with `T(N) ≤ C N^(1+epsilon)` for `N ≥ 1`. These are implication premises, not new axioms. The appendix marks conclusions with explicit `T` bounds as **F** and conclusions also requiring the almost-linear bound as **F+**; the latter include the compiler, fixed-parameter, and optimum-search guarantees. Other required solver witnesses are proved in the development.

The SAT route supplies bounded-cost encodings and recovers paths from assignments. Its Almost-2-SAT algorithm includes actual iterative compression, ternary branching, and a cut-based compiler. Approximation proofs establish greedy guarantees and expected values, then conditional rounding; the continuous optimization route supplies an exact convex quadratic-program solver. Structural arguments supply the planar-triangle and outerplanar results, while explicit machine foundations support the hardness reductions. Verified implementations can meet the stated guarantees through alternatives to a publication's original algorithm; no claim is made that every published algorithm was reproduced verbatim.

Recorded release verification covered:

* 101 selected statement/proof comparison endpoints across eight packages, each accepted by six kernel checkers;
* 18,742 per-package transitive axiom guards, including 74 repeated occurrences;
* 1,448 retained Lean files, 86 passing supporting tests, and 39 supplemental dependency queries.

The axiom-guard count is not a count of distinct theorems or of independently replayed proofs. A declaration check and a proposition-valued specification with a verified witness are also different forms of evidence; the package records identify the relevant checks. These figures report retained verification evidence, not a fresh rerun for this README. Cached external dependencies were not all freshly rebuilt.

`Solution` and `Audit` libraries are delivered. Generated `Challenge` specifications contain placeholders and are omitted from delivered Lean libraries and default build targets. The generator reproduces temporary comparison statements for checking; those placeholders must not be confused with the proved libraries.

## Reused code, dependencies, and licences

The recorded toolchain is `leanprover/lean4:v4.35.0-rc2`. Project metadata and foundation ownership fields remain **ANONYMIZED**. The upstream citations below identify reused code; they do not assign authorship of this project.

### Code provenance

| Actual source | Code revision | Relationship |
|---|---|---|
| [NPCompleteness-Lean4](https://github.com/PalomarArchive/RBarish-UTokyo--NPCompleteness-Lean4--67a5f2be4177/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925) | `3e603e795b44fedcf7d6dd65b7d1e30547ead925` | Imported foundation for explicit single-tape machines, polynomial-time word functions, P/NP/SAT, Cook–Levin, SAT variants, and the planarity model. |
| [Max3SAT-MaxSNP-APX-Lean4](https://github.com/PalomarArchive/RBarish-UTokyo--Max3SAT-MaxSNP-APX-Lean4--da68bef5965e/tree/10079b2a14bd0df47d2a24364133f6008b9c207f) | `10079b2a14bd0df47d2a24364133f6008b9c207f` | Bundled derived foundation for PCP/gap results, witness recovery, optimization, and MaxSNP/APX source hardness. Duplicate NP modules are supplied by the NP dependency; additional modules are remapped to `ComplexityExt`, with imports rewritten and declaration namespaces unchanged. |
| [openai/math](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a) | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` | Transitive upstream source: the Max3SAT provenance record identifies 194 adapted Unique Games, gap, and expander modules. |
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55) | `065356127b1dc0016f66b7283ce0ce2c4055aa55` (`v4.35.0-rc2`) | Pinned proof library. |

### Upstream citations

* Robert D. Barish, *NP-completeness of SAT, 3-SAT and their variants (the Cook–Levin theorem) in Lean 4*, 2026. Palomar, [PALOMAR-2026-10-02-000013 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-02-000013&version=1).
* Robert D. Barish, *MaxSNP-completeness and APX-completeness of MAX-3-SAT and 3-OCCURRENCE MAX-3-SAT (the PCP theorem and hardness of approximation) in Lean 4*, 2026. Palomar, [PALOMAR-2026-10-09-000010 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-09-000010&version=1).

Registry entry versions identify the cited formalizations; the table separately records the code revisions actually used. No byte identity between registry versions and these snapshots is asserted. Retained manifests, `DERIVED.md`, provenance records, and bundled licence notices document file origins and applicable terms, including Apache 2.0 notices for the NP and adapted OpenAI code. These citations neither relicense this project nor introduce an unproved theorem premise: imported foundation theorems have checked proofs under the existing three-axiom boundary.

The only cited algorithm excluded from the formalization is the almost-linear minimum-cost-flow algorithm:

J. V. D. Brand *et al.*, “A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow,” *2023 IEEE 64th Annual Symposium on Foundations of Computer Science (FOCS)*, Santa Cruz, CA, USA, 2023, pp. 503–514, doi: [10.1109/FOCS57990.2023.00037](https://doi.org/10.1109/FOCS57990.2023.00037).

## AI disclosure

This formalization was developed with AI assistance under human direction. GPT-6 Astra and GPT-6.1 Sol (OpenAI), and Opus 5.5 and Fable 5.1 (Anthropic), assisted various parts of the formalization.

Appendix G of the accompanying paper was written by GPT-6.1 Sol (OpenAI).

The proof terms are checked under the permitted axiom boundary described above. AI assistance and this disclosure add no logical axioms.

## Compiling Appendix G

Keep the manuscript's `lipics-v2021` document class and its options unchanged. Add the following to the preamble, after the document-class declaration and before `\begin{document}`:

```latex
\usepackage{longtable,booktabs,array,xurl}
```

`longtable` supplies tables spanning multiple pages, `booktabs` supplies the table rules, `array` supplies the column formatting, and `xurl` allows long Lean declaration names and URLs to wrap. LIPIcs supplies `hyperref` for the links. The appendix reuses the manuscript's bibliography entries and result labels; compile it within the manuscript using the shared `sources.bib`, then rerun BibTeX and LaTeX until references resolve.

## Checking it

Fresh publication checks passed all eight package builds and all 86 supporting tests, with zero skips. All 1,448 delivered Lean files match the compiled sources byte for byte. The repository's `VERIFICATION.md` and `verification/compilation.json` record the exact versions, environment adaptation, and distinction from retained independent-checker evidence.

Use the retained toolchain and dependency manifests, with `VERIFICATION.md` and package records for exact reproduction steps. The recorded package build order is `cpap-np-hardness`, `cpap-minor-free`, `cpap-tractability`, `cpap-bounded-cost`, `cpap-approximation`, `cpap-approximation-hardness`, `cpap-outerplanar`, then `cpap-runtimes`. Obtain the Mathlib cache from the actual Mathlib package root:

```sh
lake exe cache get
```

Build each package with `lake build` in that order. Known package checking components are `scripts/check_repository.py`, `scripts/generate_challenge.py`, `scripts/generate_audit.py`, and `comparator.json`; use their documented invocation and generated-file handling. The comparison command is:

```sh
lake comparator --config comparator.json --paranoid
```

