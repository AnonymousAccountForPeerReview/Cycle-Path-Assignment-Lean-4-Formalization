# Paper map: shared model, Section 5 and Appendix C in Lean

Result numbers and appendix letters follow the accompanying paper. Names without a namespace are in
`STACS2027`; `Paper.x` is `STACS2027.Paper.x` in `NPHardness/Paper.lean`.
The model rows cover Section 2.2; the hardness and gadget rows cover Section 5 and Appendix C.
Every row is a proved theorem or a definition. **(Challenge)** marks endpoints or definitions of
the optional generated comparison specification; Challenge.lean is omitted from the distribution.

## Definitions

| Manuscript | Lean | Notes |
|---|---|---|
| Definition 1 (CPAP, objective `∑_e binom(l(e),2)`) | `HasAssignment g k B`, `cost`; `Paper.cpap_objective` | One path of `k−2` edges per simple `k`-cycle, each cycle counted once by its edge set. `cpap_objective` proves `cost` is the load objective. |
| CPAP as a decision problem | `CPAP k`, `PlanarCPAP k` **(Challenge)** | Images of `encode` on lists of graph records (edges and budget units), as the foundation's languages are images of `encode`. `cpap_iff_decode` shows malformed words are rejected. |
| Definition 7, (≤1,≤2)-SAT | `Paper.LeOneLeTwoCNF` = `BoundedOccurrence ∧ ClauseVariablesDistinct` | `BoundedOccurrence` is the foundation's `IsLeOneLeTwoCNF` (`boundedOccurrence_iff_registered`), which, like the foundation's definition, omits "on distinct variables". `Paper.leOneLeTwoCNF_iff_registered`. |
| Definition 22, edge identification | `formulaGraph` (one fixed endpoint order), `orientedFormulaGraph flips` (any order) | See "Endpoint orders" below. |
| Planar-(≤1,≤2)-SAT (Section 5: "The problem Planar-(≤1,≤2)-SAT requires this graph to be planar") | `Paper.PlanarLeOneLeTwoCNF`, `Paper.PlanarLeOneLeTwoLanguage`; foundation form `IsPlanarLeOneLeTwoCNF`, `PlanarLeOneLeTwoSAT` **(Challenge)** | The foundation form drops "on distinct variables", as `IsLeOneLeTwoCNF` does. |
| Variable–clause incidence graph | the foundation's `Complexity.SAT.incidenceGraph` | One edge per occurrence. |
| Planarity | the foundation's `Complexity.PlanarGraph` | Genus-zero hypermap (rotation system). |

## Construction (Appendix C, Steps 1–4; Figure 4)

See `docs/gadget-map.md` for vertex-by-vertex tables.

| Manuscript | Lean |
|---|---|
| Step 1, `γ_x`, `C^α_x`, `C^β_x`, `s_x`, `e_(x,True,1)`, `e_(x,False,j)` | `variableGraph k`; `Paper.alphaCycle`, `betaCycle`, `sharedEdge`, `trueEdge`, `falseEdge1`, `falseEdge2`; `Paper.step1_incidences`, `step1_lengths` |
| Step 1, "both have length exactly `k`, the only other simple cycle has length `2k−2`" | `Paper.step1_cycle_lengths`, `Paper.step1_cycles`, `Paper.step1_k_cycles` |
| Step 2, edge set and green edges of `ζ_(c,3)` | `clauseThreeLinks k`; `Paper.step2Edges`, `step2Green`, `step2_links` (all `k`), `step2_k5` |
| Step 3, `ζ_(c,2)` and its subdivision rule | `clauseTwoLinks k`; `Paper.step3Edges`, `step3Subdivisions`, `step3_links` (all `k`), `step3_k5` |
| Step 4, smallest unused `e_(c,i)` and `e_(x,False,j)` | `PlacedLiteral.port`, `clauseEndpoint`; `Paper.step4_variable_port`, `step4_port_edges`, `step4_identification` |

## Theorem 8 and its proof

| Manuscript | Lean |
|---|---|
| Theorem 8, "satisfiable iff assignment of cost at most `m`" | `Paper.gadget_reduction` (fixed endpoint order), `Paper.gadget_reduction_any_endpoints` (every order) |
| Theorem 8, "if the incidence graph is planar, `G` is planar" | `Paper.gadget_reduction_planar`: some endpoint order gives a planar graph, which is also correct. The gadget orientations (the endpoint order) are computed in linear time from a planar embedding of the incidence graph in `cpap-approximation-hardness` (`orientation_linear_ram`); the formula-only embedding is computed by the checked fixed RAM program `Embed.planarEmbedding_linear_ram` in `cpap-approximation-hardness`, with both time and accessed addresses bounded by `100000 · (|ramInput f| + variableBound f + 1)`. Theorem 6 does not need it: its reduction computes the endpoint data on its own planar source family (`SourceWord.packed_linear_word_planar`). |
| Theorem 8, "`O(n)` time" | `Paper.gadget_reduction_size` (at most `17·k·n` edges); `Paper.gadget_reduction_linear_time` and `gadget_reduction_planar_linear_time` (`(n+1)(128k+160)` transitions of a verified word machine, with the endpoint table supplied); `Paper.gadget_reduction_unit_steps_bounded` (each transition is bounded work) |
| Theorem 8 on all of the foundation's (≤1,≤2)-SAT | `Paper.gadget_reduction_full_domain`, `Paper.gadget_reduction_full_domain_any_endpoints`, `Paper.gadget_reduction_full_domain_size` |
| "All gadgets are planar" (proof sketch) | `Paper.gadgets_planar` |
| (o1), every `k`-cycle lies in one gadget | `Paper.observation_o1`, `observation_o1_any_endpoints` |
| (o1.2), variable side | `Paper.observation_o1_2_variable` |
| Second observation, truth states and normalization | `Paper.step1_truth_states`; `variableExpansion_zero_normalizes`, `variableChosen_normalizes` |
| Third and fourth observations, clause gadgets | `Paper.clause_gadget_observations` (every `k ≥ 5`); `Paper.clause_gadget_optima` (the `k = 5` and `k = 6` brute-force checks) |
| Final counting argument | `formulaGraph_sat_implies_assignment`, `formulaGraph_assignment_implies_sat` |

## Theorem 6

| Manuscript | Lean |
|---|---|
| Theorem 6, planar graphs | `planarCPAP_np_hard` **(Challenge)**, `Paper.planar_np_hard` |
| Theorem 6, last sentence, general graphs | `cpap_np_hard` **(Challenge)**, `Paper.general_np_hard` |
| Planar-(≤1,≤2)-SAT is NP-hard (cited to ANONYMIZED et al. 2008) | proved: `planarLeOneLeTwoSAT_np_complete` **(Challenge)** (foundation form, NP-complete) and `Paper.planarLeOneLeTwoCNF_np_hard` (exactly as defined in Section 5, with distinct variables) |

## Endpoint orders

Definition 22 ends with "we arbitrarily order the vertices in `e_x` and
`e_y`". Correctness does not depend on the order (`Paper.gadget_reduction_any_endpoints`),
but planarity does: `Paper.fixed_endpoints_K33` gives a Planar-(≤1,≤2)-SAT formula
(three clauses on two variables) whose gluing in one fixed order contains a
subdivision of `K_{3,3}`, while another order is planar. The proof sketch of
Theorem 8 already says to choose "the endpoint identifications consistently
with this embedding"; Definition 22's "arbitrarily" should defer to it.

## Differences from the manuscript

* Definition 7 and Planar-(≤1,≤2)-SAT require distinct variables in each clause; the
  foundation's `IsLeOneLeTwoCNF` does not. `Paper.LeOneLeTwoCNF` and
  `Paper.PlanarLeOneLeTwoCNF` include the requirement. `Paper.gadget_reduction_full_domain`
  shows Theorem 8 also holds without it: repeated literals and tautological
  clauses are removed first, and the budget stays the original `m`.
* The CPAP instance is coded as a list of records over the foundation's CNF code.
  The cost is the manuscript's objective (`cpap_objective`).
* `O(n)` is proved as an edge bound and as a transition bound of a word machine
  with a supplied endpoint table, not as a bound for a single-tape machine. The
  NP-hardness reductions are polynomial-time single-tape machines.
* This package supplies the shared Section 2.2 CPAP model and Section 5/Appendix C proofs.
  `cpap-approximation-hardness` supplies Section 6/Appendix D and also the Section 5
  linear RAM reduction, compatible planar orientation and formula-only incidence embedding.
  The runtime integration and the remaining paper results are mapped to their topic packages
  in the repository README.
