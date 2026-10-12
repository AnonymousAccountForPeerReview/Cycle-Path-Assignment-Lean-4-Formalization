# Paper map: approximation hardness and reduction algorithms in Lean

Result numbers and appendix letters follow the accompanying paper. Names without a namespace are in
`STACS2027`; `Paper.x` is `STACS2027.Paper.x` in `ApproximationHardness/Paper.lean`.
The rows cover Section 6/Appendix D, the Section 5 RAM reduction and planar embedding,
and the formalized source-hardness chain. Every row is a proved theorem or a definition.
**(Challenge)** marks endpoints or definitions of the optional generated comparison
specification; Challenge.lean is omitted from the distribution; `Complexity.x` names a
declaration of Max3SAT-MaxSNP-APX-Lean4 (or of the NP-completeness foundation).

## Definitions

| Manuscript | Lean | Notes |
|---|---|---|
| Definition 1 (CPAP, objective `∑_e binom(l(e),2)`), `c(τ)`, `C* = OPT_CPAP(G)` | `HasAssignment`, `cost` (`cpap-np-hardness` formalization, copied); `IsMinCost g k C` **(Challenge)** | `IsMinCost`: the least budget admitting an assignment. The `cpap-np-hardness` formalization proves `cost` is the load objective. |
| `s(A)`, `S* = max_A s(A)` | `satisfiedCount a f`, `IsMaxSat f S` **(Challenge)** | `satisfiedCount a f = f.countP (evalClause a)`. |
| Definition 9 (L-reduction), with `α`, `β`: "`OPT_{Π'}(f(I)) ≤ α OPT_Π(I)`", "`|OPT_Π(I) − c_Π(y)| ≤ β |OPT_{Π'}(f(I)) − c_{Π'}(x)|`" for `y = g(I, x)` | `LReductionToCPAP Source F k αn αd βn βd`, `LReductionSat Source T αn αd βn βd` **(Challenge)** | Written in the naturals: `αd·C ≤ αn·S` and `βd·S + βn·C ≤ βd·s(a) + βn·c(ps)`; `g` is the existential witness `a`. |
| MAX-(≤1,≤2)-SAT instances; Definition 7 ("`CPAP` instance from a (≤1,≤2)-SAT formula") | `LeOneLeTwoCNF f := BoundedOccurrence f ∧ ClauseVariablesDistinct f` **(Challenge)** (both copied from Section 5) | Two or three literals per clause on distinct variables, at most one positive and two negative occurrences per variable. |
| `CPAP(·, k)` as an optimization problem (minimize `c(τ)`), the setting of MaxSNP and APX | `cpapProblem k` **(Challenge)**, `cpapProblem_isOpt_iff` (on a record list writing `G`, the optimum is `C*`), `Paper.cpapProblem_optimum` | Instances: codes `encode f` of record lists in the Section 5 CPAP format with no budget record; solutions: codes `Sim.encodePaths ps` of cycle-path assignments; values: costs. |
| optimization problems, L-reductions, MaxSNP, APX, PTAS-reductions, PTAS, `P = NP` (Section 6 and the hardness notions of Theorem 11 and Corollary 12) | `Complexity.OptProblem`, `IsOpt`, `LReducible`, `NPO`, `Relations.Fits`, `QF.WellFormed`, `maxSNP0`, `InMaxSNP`, `MaxSNPHard`, `InAPX`, `PTASReducible`, `APXHard`, `HasPTAS`, `ApproximableWithin`, `PEqNP` **(Challenge)** (Max3SAT-MaxSNP-APX-Lean4, copied) | MaxSNP as the NPO problems L-reducible to a problem of the syntactic class MaxSNP₀ (ANONYMIZED–ANONYMIZED), whose instances and solutions are structures of fixed signatures on the instance's universe; PTAS-reductions in the sense of ANONYMIZED and ANONYMIZED. |
| "the gadget construction of Theorem 8", "construct `G` as in Theorem 8" | `formulaGraph k f` (`cpap-np-hardness` formalization, copied: `Link` through `formulaGraph`) | The variable gadgets `γ_x`, the clause gadgets `ζ_(c,3)`, `ζ_(c,2)`, glued at the literal ports (Appendix C, Steps 1–4). |
| 3-OCCURRENCE MAX-3-SAT: "every clause contains two or three literals and every variable occurs at most three times" | `ThreeOccurrence` **(Challenge)** | Clauses as sets: distinct literals. `occurrences` is the `cpap-np-hardness` formalization's count. |
| Lemma 10: eliminated variables, their satisfying value, deleted clauses, `r`, `ψ` | `pureThree`, `pureValue`, `deleted`, `tautological` (Section 5, copied), `deletedCount`, `kept` **(Challenge)** | One round: variables occurring three times with one polarity (see "Differences"). |
| "complementing variables that occur twice positively", `ψ'` | `complemented`, `flipLiteral`, `flipFormula` **(Challenge)** | |
| "`r` clauses `(a_j ∨ b_j)` ... each using two fresh variables", `φ'` | `padding (variableBound f) r`, `polarize` **(Challenge)** | Fresh variables `variableBound f, variableBound f + 1, …`. |

## Appendix D, proof of Theorem 11

| Manuscript | Lean |
|---|---|
| "any truth assignment `A` determines the paths in the variable gadgets" (truth states) | `placedVariable_sat_witness` (Section 5), used in `formulaGraph_cost_upper_bound` |
| "cost one for each satisfied clause and cost two for each unsatisfied clause, giving total cost `2m − s(A)`" | `placedClause_sat_witness` (Section 5), `placedClause_unsat_witness`, `formulaGraph_cost_upper_bound` (`c ≤ 2m − s(A)`), `Paper.assignment_from_truth` |
| "In particular, `C* ≤ 2m − S*`" | `minCost_add_maxSat` (first half), `Paper.optimum_relation` |
| cost of `τ` as a sum over gadgets and shared ports | `cost_formulaFamily_eq` (from `formulaGraph_cost_decomposition` of Section 5 and `crossCost_global_eq`) |
| "Normalize the variable-gadget paths without increasing the cost" | `variableSkeleton_weighted_normalizes` (finite check), `variableExpansion_weighted_normalizes`, `variableChosen_weighted_normalizes`; `portWeight_le_one` (the clause loads on a port are at most one: `clauseChosen_port_load_le_one`) |
| "Decode a variable as true when its positive attachment edge is omitted, and as false when both negative attachment edges are omitted" | the assignment `a` in `formulaFamily_cost_lower_bound` (the better truth state of each gadget); `stateLoad_eq` |
| "every satisfied clause contributes cost at least one and every unsatisfied clause contributes cost at least two" | `clause_contribution`, from `clauseChosen_cost_positive` and `clauseChosen_blocked_lower` (observation (iii) of Theorem 8, placed) |
| "Hence `c(τ) ≥ 2m − s(A) ≥ 2m − S*`" | `formulaFamily_cost_lower_bound`, `Paper.truth_from_assignment` |
| "the exact relation `C* = 2m − S*`" | `minCost_add_maxSat`, `cpap_optimum` **(Challenge)**, `Paper.optimum_relation` |
| "A uniformly random truth assignment satisfies each clause with probability at least `3/4`, so `S* ≥ 3m/4`" | `boolLists`, `count_two`, `clause_satisfied_count`, `exists_three_quarters`, `four_mul_maxSat`, `Paper.random_assignment_bound` |
| "`C* = 2m − S* ≤ (5/3) S*`" | `three_mul_minCost_le`, `Paper.alpha_condition` |
| "`S* − s(A) ≤ c(τ) − (2m − S*) = c(τ) − C*`" | `decode_error_bound`, `Paper.beta_condition` |
| "the construction is an L-reduction with `α = 5/3` and `β = 1`" | `cpap_lreduction` **(Challenge)**, `Paper.gadget_lreduction` |
| "Lemma 10 yields both hardness claims" | `threeOccurrence_cpap_lreduction` **(Challenge)** (the composition), `Paper.gadget_lreduction_from_threeOccurrence` |

## Theorem 11: MaxSNP-hardness and APX-hardness

| Manuscript | Lean |
|---|---|
| the source problem, 3-OCCURRENCE MAX-3-SAT, as cited (MaxSNP-complete) | `Complexity.max3SAT3` **(Challenge)**: clauses of at most three literals (possibly repeated, possibly fewer than two), every variable at most three times, assignments as words no longer than the instance; `Complexity.max3SAT3_maxSNPHard` (Max3SAT-MaxSNP-APX-Lean4) |
| from it to the instances of Lemma 10 | `Hardness.normalize` (`ApproximationHardness/Hardness/Normalize.lean`: repeated literals and empty clauses removed, each unit clause `(l)` replaced by `(l ∨ z)(¬z ∨ w)(¬z ∨ ¬w)` on fresh `z`, `w`), `Hardness.normalize_threeOccurrence`, `Hardness.isMaxSat_normalize` (`OPT` rises by exactly `2u`), `Hardness.satisfiedCount_normalize_le`, `Hardness.two_mul_unitCount_le` (`2u ≤ 4 OPT`), `Hardness.pt_normalize` (polynomial-time) |
| "Lemma 10 yields both hardness claims": the L-reduction of optimization problems | `Hardness.solMap`, `Hardness.pt_solMap`, `Hardness.isMaxSat_of_isOpt`, `Hardness.lReducible_max3SAT3_cpap`, `max3SAT3_lReducible_cpap` **(Challenge)**, `Paper.cpap_lReducible_paper`: normalization, `polarize_polyTime_machine`, `cpap_lreduction_polyTime` and a reversal of the records; for solutions `decoder_polyTime` and `recover` (`Hardness.PT.recover'`); `α = 9`, `β = 1` |
| "For every fixed `k ≥ 5`, `CPAP(G, k)` is MaxSNP-hard" | `cpap_maxSNPHard` **(Challenge)**, `Paper.maxSNP_hardness` (from `Complexity.MaxSNPHard.of_lReducible`) |
| "... and APX-hard" | `cpap_apxHard` **(Challenge)**, `Paper.apx_hardness` (from `Complexity.witnessGap`, `Complexity.lReducible_max3SAT_max3SAT3` and `Complexity.apxHard_of_lReducible_max3SAT`) |

## Appendix D, Lemma 10

| Manuscript | Lean |
|---|---|
| "These choices can be extended from any assignment of `ψ`, and `OPT(φ) = r + OPT(ψ)`" | `extendPure`, `satisfiedCount_extendPure_deleted` (all `r` deleted clauses satisfied), `satisfiedCount_extendPure_kept`, `satisfiedCount_split`, `satisfiedCount_deleted_le` |
| "Every remaining variable occurs with both polarities. Complementing variables that occur twice positively and once negatively therefore gives a formula `ψ'` satisfying the required occurrence bounds" | `polarize_boundedOccurrence`, `polarize_clauseVariablesDistinct`, `polarize_leOneLeTwo`, `Paper.polarize_target` |
| "without changing its objective values" | `satisfiedCount_flipFormula`, `flipAssign_flipAssign` |
| "adding `r` clauses `(a_j ∨ b_j)` to `ψ'` ... Thus `OPT(φ') = OPT(φ)`" | `satisfiedCount_padding_le`, `satisfiedCount_padTrue_padding`, `satisfiedCount_polarize_ge`, `polarize_maxSat_eq`, `Paper.polarize_optimum` |
| "undo the complementations and restore the eliminated variables. The recovered assignment satisfies all `r` deleted clauses and at least as many clauses overall" | `recover`, `satisfiedCount_recover`, `Paper.polarize_recovery` |
| "Both L-reduction conditions follow with `α = β = 1`" | `polarize_lreduction`, `leOneLeTwo_lreduction` **(Challenge)**, `Paper.leOneLeTwo_lreduction` |
| L-reductions compose (used in the proof of Theorem 11) | `LReductionSat.comp_cpap` |

## Corollary 12

| Manuscript | Lean |
|---|---|
| "Unless `P = NP`, `CPAP(G, k)` admits no PTAS for any fixed `k ≥ 5`" | `cpap_no_ptas` **(Challenge)**, `Paper.no_ptas` (from `Complexity.maxSNPHard_not_hasPTAS`); non-uniformly, one algorithm per ratio: `cpap_not_approximable` **(Challenge)**, `Paper.no_ptas_nonuniform` (from `Complexity.maxSNPHard_no_ptas`) |
| "the inapproximability of MaxSNP-hard problems implied by the PCP theorem" | the PCP theorem of Max3SAT-MaxSNP-APX-Lean4 (`Complexity.pcp_gap`), behind the two theorems above; the transfer of approximation ratios through the L-reduction, `approximation_transfer`, `Paper.ptas_transfer` |

## Definition 9, computability of the maps

| Manuscript | Lean |
|---|---|
| Definition 9: "polynomial-time maps `f` and `g`"; the instance map `f` of Theorem 11, in the foundation's single-tape model | `Registered.program`, `Registered.machine` (a 42-register program of the foundation's stack language, `ApproximationHardness/Registered/`), `Registered.machine_computes` (halts within `Registered.bound k L` steps on every input of length `L`), `Registered.polynomial_bound`, `Registered.polyTime_instanceMapWord` (`PolyTime`, through the foundation's `StackCompile.polyTime_of_stack`), `Registered.instanceMapWord_encode` (on `encode f` the output is `encode (formulaRecords k f).reverse`), `Registered.formulaRecords_output` (those records write `(formulaGraph k f).reverse` in the Section 5 record format, `GraphOutput`), `cpap_lreduction_polyTime`, `Paper.gadget_polyTime_instance_map` |
| the same, on the Section 5 word machine | `cleanFormula_leOneLeTwo`, `globalReductionGraph_leOneLeTwo` (on a Definition 7 formula the Section 5 full-domain construction is `formulaGraph k f`), `orientedFormulaGraph_trivial`, `kernel_trivial`, `instance_map_linear_time` (the Section 5 word machine reaches `(formulaGraph k f).reverse` in `≤ (n + 1)(128k + 160)` transitions), `LReductionToCPAP.of_perm`, `cpap_lreduction_computed`, `Paper.instance_map_computed`, `Paper.full_domain_is_gadget_graph` |
| the instance map of Lemma 10 (`polarize`), in linear RAM time and space | `RAM.polProgram` (`ApproximationHardness/RAM/Polarize/`: a counting pass, the deletions, the complementations, the kept clauses, the padding), `RAM.pol_computes` (space `RAM.polSpace f = N + 3n`: the input, the counts `N + 2v + s`, the table `N + 2n + v`; address conditions in `Polarize/Space.lean`), `RAM.polarize_linear_time` (output `ramInput (polarize f)` within `polLinConst · (n + 1)` steps and addresses), `polarize_linear_ram` |
| the same, in the foundation's machine model | `Sim.polX` (parse `encode f`, simulate `RAM.polProgram`, write `encode (polarize f)`), `Sim.polX_run` (within `polXConst · (|encode f| + 1)²` steps), `Sim.polarize_polyTime`, `polarize_polyTime_machine` |
| the decoding map `g` of Theorem 11, explicitly | `decodeAssign k ps` (`ApproximationHardness/Decode/Explicit.lean`: `v` true iff the paths leaving the block of `v` use its negative port edges at most as often as its positive one), `cpap_lreduction_decoder` (it satisfies `S* + C* ≤ s(A) + c(τ)` for every valid choice `τ`) |
| the decoding map, in linear RAM time and space | `RAM.decProgram k` (`ApproximationHardness/RAM/Decode/`: block and offset tables, one or two passes per path, the port loads), `RAM.dec_computes` (space `RAM.decSpace k f ps`: the input, `2(m + n)w` table cells, three counters per variable), `RAM.dec_linear`, `RAM.decSpace_le`, `RAM.decoder_linear_time` (within `decLinConst k · (n + 1)` steps and `decSpaceConst k · (n + 1)` addresses), `RAM.decoder_ram`, `decoder_linear_ram` |
| the same, in the foundation's machine model | `Sim.decX k`, `Sim.decX_run`, `Sim.decoder_polyTime`, `decoder_polyTime` |
| the simulation behind the machine-model bounds | `Sim.XStmt`, `Sim.XExec` (the RAM with bitwise input and output), `Sim.sim`, `Sim.sim_correct` (one RAM step in polynomially many stack-machine steps, binary numbers, memory as an association list, fuel-bounded loops), `Sim.xram_polyTime` (a polynomially bounded XRAM program is a `PolyTime` word function), `Sim.tr`, `Sim.tr_exec` (a RAM program as an XRAM program on the even cells, output on the odd cells). The cost of the simulation depends on the number of steps and on the bit lengths of the numbers, not on the address range (the memory is an association list), so the machine-model theorems use the RAM time bounds only (`ExecB.exec` forgets the space bound) |

## Theorem 8, "can be transformed in `O(n)` time"

| Manuscript | Lean |
|---|---|
| the machine of the time bound (unspecified in the manuscript) | the unit-cost RAM `RAM.Stmt`, `RAM.Exec`, `RAM.Computes` **(Challenge)** (`ApproximationHardness/RAM/Model.lean`); input `RAM.ramInput f`, output `f.length :: RAM.edgeWord es` |
| its memory (space): the addresses a run reads or writes | `RAM.ExecB S` (the runs whose loads and stores address only cells below `S`), `RAM.ComputesIn s input output time space` **(Challenge)** (`ApproximationHardness/RAM/Bounded.lean`, the same definitions as in the outerplanar formalization); `ExecB.congr` (the result does not depend on the memory at or above the bound); the reasoning framework `RAM.AddrOK`, `RAM.SatB` (`ApproximationHardness/RAM/SpecB.lean`, twins of `Spec.lean`'s `Sat` rules; `SatB.of_Sat` lifts proofs of memory-free code) |
| the transformation | `RAM.program k` = `passA` (the number of variables `n`), `passV` (the `n` variable gadgets), `passB` (per clause: each literal's occurrence number from a count table at `N + 2v + s`, its port endpoint from a block table, then the clause gadget) (`ApproximationHardness/RAM/Program.lean`) |
| its output is the Theorem 8 graph | `RAM.formulaRecords_pairs`, `RAM.formulaGraph_eq_pairs` (`formulaGraph k f` is the normalized list of the emitted pairs), `RAM.passBModel_out` |
| "in `O(n)` time" (and space) | `RAM.ram_computes` (within `ramConst k · (m + n + 1)` steps whenever every clause has two or three literals, accessing only the addresses below `N + 3n`: the input, the count table, the block table), `RAM.ram_linear_time` (within `ramLinConst k · (n + 1)` steps and addresses under the occurrence bounds, since they give `2m ≤ 3n`: Section 5's `BoundedOccurrence.clause_count_variableBound`) |
| Theorem 8 with its time and space bound | `gadget_reduction_linear_ram` **(Challenge)**, `Paper.gadget_reduction_linear_time_ram` (with the equivalence of Section 5's `formulaGraph_sat_iff_assignment`) |

## Theorem 8 for planar formulas: "fix a planar embedding and place each gadget accordingly"

| Manuscript | Lean |
|---|---|
| a planar embedding of the incidence graph | `IsPlanarRotation f rot` **(Challenge)** (`rot` lists the node permutation of a planar hypermap of `incidenceGraph f`, dart by dart), `planarGraph_iff_rotation` |
| the orientation of each gadget | `variableSign`, `clauseSign`, `flipBit`, `orientationBits`, `orientationChoices` (`ApproximationHardness/Planar/ExplicitOrientation.lean`); `choicesOfBits` **(Challenge)** |
| the placed gadgets form a planar graph | `orientationChoices_planar`, `orientationBits_planar`: with these bits `orientedFormulaGraph` (Section 5) is planar for every `k`; through Section 5's `chosenPieces_with_profiles` and `orientedFormulaGraph_planar_prescribed`, with `piece_explicit_profile` (variable gadgets mirrored by sign, three-literal clause gadgets mirrored by sign), `explicit_source_orders` and `NextSelected.skip`, `cyclic_skip`, `three_cycle_sign` (`ApproximationHardness/Planar/Skip.lean`) |
| in linear time | `RAM.orProgram` (`ApproximationHardness/RAM/Orient/`), `RAM.or_computes` (space `RAM.orSpace f = 2N + 2n + 4 |f.flatten|`), `RAM.orientation_linear_time` (time `orConst · (N + 1)`, space `4 (N + n + 1)`), `orientation_linear_ram` **(Challenge)** (time `C (N + 1)`, space `C (N + n + 1)`, `n = variableBound f`), `gadget_reduction_planar_orientation_ram` (with `orientedFormulaGraph_sat_iff_assignment`); in the foundation's machine model `Sim.orX`, `Sim.orientation_polyTime`, `orientation_polyTime` **(Challenge)** |

The incidence rotation is computed from the formula alone as well:

| Construction | Lean | Verified bound |
|---|---|---|
| Parse the formula, build incidence adjacency, and execute DFS | `IncidenceRAM.prepareForestPlan` | Actual `RAM.ExecB` from `RAM.initial (RAM.ramInput f)`; initialized bounded solver state and complete plan tables |
| Execute the complete linked solver | `RAMSolver.defaultSolverProgram_spec` | Exact completed solver state and records, cached default rotations, at most `45000 · (E + 1)` steps |
| Compute group orientations | `RAMSolver.orientationProgram_spec` | Actual key materialization and fold; consistency and exact finite orientation array |
| Emit the dart rotation | `RAMSolver.readoutProgram_spec` | Exact `rotOut`, `IsPlanarRotation`, at most `1000 · (E + 1)` steps |
| Uniform formula-only linear construction | `Embed.planarEmbedding_linear_ram` **(Challenge)** | `RAM.ComputesIn` and time bounded by `100000 · (|ramInput f| + variableBound f + 1)` |

The polynomial-time maps `cpap_lreduction_polyTime`, `polarize_polyTime_machine`
and `decoder_polyTime` are used by `max3SAT3_lReducible_cpap`. The linear RAM maps
and `approximation_transfer` are also library theorems with exact axiom guards.
The comparison configuration selects thirteen endpoints; the default build checks
the full library, Solution and guards.

## Logical dependencies and machine models

The PCP theorem, source MaxSNP/APX hardness and no-PTAS implications are proved in
the bundled Max3SAT-MaxSNP-APX-Lean4 dependency. The approximation-hardness
endpoints require only the standard Lean axioms and do not introduce a
cited-result hypothesis. The linear bounds are stated in the defined unit-cost
RAM model; the single-tape implementations have polynomial bounds. These are
distinct, explicitly defined machine models.

## Differences from the manuscript

* Completeness is proved as `c(τ) ≤ 2m − s(A)` (the manuscript: "giving total
  cost `2m − s(A)`"); only the inequality is used, and `C* = 2m − S*` follows.
* Lemma 10 eliminates, in one round, exactly the variables occurring three
  times with a single polarity, rather than repeatedly every variable of a
  single polarity: a variable occurring with one polarity at most twice already
  meets the bounds (after complementation if positive), and deleting clauses
  can only lower occurrence counts, so no second round is needed. The deleted
  clauses, `r`, `ψ`, `ψ'` and `φ'` are otherwise as in the manuscript.
* **Lemma 10 also deletes the tautological clauses** (`deleted` includes `tautological`,
  a clause containing a variable and its negation). The proof in the paper does not delete
  them, and then its target formula need not be an instance of
  MAX-(≤1,≤2)-SAT as Definition 7 defines it (two or three literals *on distinct variables*):
  for `φ = (x ∨ ¬x ∨ y) ∧ (¬y ∨ w) ∧ (¬w ∨ y)` (a 3-OCCURRENCE MAX-3-SAT instance: three distinct
  literals per clause where it has three, every variable at most three times) no variable has a
  single polarity, so nothing is eliminated and `r = 0`; `y` occurs twice positively and once
  negatively and is complemented, giving `ψ' = (x ∨ ¬x ∨ ¬y) ∧ (y ∨ w) ∧ (¬w ∨ ¬y)`, whose first
  clause has the variable `x` twice. The formal `polarize` deletes `(x ∨ ¬x ∨ y)` (`r = 1`) and
  pads one clause, giving a Definition 7 formula (`polarize_leOneLeTwo`), which the Theorem 8
  construction needs (`LeOneLeTwoCNF` is the hypothesis of `cpap_lreduction`). A tautological clause
  is satisfied by every assignment, so deleting it and adding a padding clause keeps both
  L-reduction conditions with `α = β = 1`, as proved (`leOneLeTwo_lreduction`). This is a deviation from
  the paper's proof text, not from its statement.
* Theorem 11 and Corollary 12 are stated for `CPAP(·, k)` as an optimization problem on words
  (`cpapProblem k`), with the notions of Max3SAT-MaxSNP-APX-Lean4 for its single-tape
  machines, which are the NP-completeness foundation's. A graph is given by its edge list (records
  of two positive literals), so isolated vertices are not represented; they change no cycle and
  no cost.
* The composed L-reduction from that formalization's 3-OCCURRENCE MAX-3-SAT has `α = 9`, not
  `5/3`: its clauses may have one literal, and the normalization gadget for unit clauses raises
  the optimum by `2u ≤ 4 OPT`. Any constant `α` gives the hardness claims; `α = 5/3` is proved
  for the manuscript's sources (`cpap_lreduction`, `threeOccurrence_cpap_lreduction`).
* MAX-(≤1,≤2)-SAT instances are Definition 7 instances (distinct variables in
  each clause), which the Theorem 8 construction requires and which Lemma 10
  always produces; the source clauses of 3-OCCURRENCE MAX-3-SAT are sets of
  two or three literals.
* `S* ≥ 3m/4` is proved by counting assignments of the variables
  `0, …, n − 1` rather than by probability.
* The L-reductions are stated as their two inequalities, with the decoding map
  as an existential witness; the decoding map is also explicit (`decodeAssign`)
  and timed, reading `τ` as a list of chosen paths and writing the bits of the
  assignment on the variables `0, …, n − 1`.
* The polynomial-time instance map lists the edges of the Theorem 8 graph in
  reverse order and writes them as Section 5 CPAP records with budget `0`
  (`GraphOutput`); an L-reduction is unchanged by reordering the edge list
  (`LReductionToCPAP.of_perm`).
* The RAM of the `O(n)` bound has structured control flow (sequencing, a branch
  on zero, a while-loop on a register) rather than jumps, charges one step per
  instruction and per test, holds unbounded naturals (the unit-cost model, with
  `+` and truncated `-` as the only arithmetic) and reads the formula as a list
  of numbers (`ramInput`) rather than as the foundation's unary word; the
  output is the budget `|f|` and the endpoint pairs. Its space, which the
  manuscript does not discuss, is stated too: every RAM theorem bounds the
  addresses a run reads or writes (input included) by the same linear term as its
  time (`RAM.ComputesIn`), so that no program relies on an unbounded memory.
* The planar orientation's RAM program is linear in time, `C (N + 1)` for an input
  of length `N`, but its space bound is `C (N + n + 1)`, `n = variableBound f`: the
  program keeps, per variable number, the count of earlier negative occurrences and
  the first positive occurrence (cells `E + 2v`, `E + 2v + 1`). For the usual
  numbering of the variables `0, …, n − 1` of an `n`-variable formula, `n` is the
  number of variables and at most `N`; for sparse variable numbers it is not
  bounded by `N` (the occurrence bounds and `IsPlanarRotation` do not exclude
  them), hence the term `n`. (Theorem 8, Lemma 10 and the decoder are stated with
  `C (n + 1)` anyway.)
* The planar orientation is one bit per literal occurrence, in the order of
  `(placeFormula [] f).flatten`, for formulas with the occurrence bounds of
  Definition 7; its input embedding is the node permutation of a planar hypermap
  of `incidenceGraph f`, listed dart by dart.


## Formula-only planar embedding

`ApproximationHardness/Embed/Computed.lean` computes merge records and orientations by finite list
traversal. `STACS2027.Embed.computedRotation_planar` proves that the computed rotation is
planar, and `computed_reduction_planar` proves that the computed gadget graph is planar
and satisfies the reduction equivalence. These results do not require an embedding as
input. Their targeted build and direct axiom checks passed with only `propext`,
`Classical.choice`, and `Quot.sound`.

`STACS2027.Embed.planarEmbedding_linear_ram` proves
`PlanarEmbeddingLinearRAM`. Its fixed program `planarEmbeddingProgram` takes exactly
`RAM.ramInput f`, computes the adjacency cache and DFS forest, compiles the complete
bounded plan, executes the linked constraint solver, computes group orientations,
and emits the planar dart rotation. No embedding, DFS forest, merge record, or solver
trace is supplied as input. For every bounded-occurrence formula with planar incidence
graph, both steps and accessed addresses are bounded by
`100000 * (|RAM.ramInput f| + variableBound f + 1)`.

The final program, time proof, space proof, and planar-output proof passed direct Lean
checks on 2026-10-12. Their direct axiom audits use only `propext`, `Classical.choice`,
and `Quot.sound`. The planarity witness verifies the deterministic solver's fork
choices; it does not become an additional machine input.
