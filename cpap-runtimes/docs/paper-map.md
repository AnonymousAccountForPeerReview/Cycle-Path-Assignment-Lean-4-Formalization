# Paper map: executed general-graph algorithms

Artifact date: 2026-10-12. Foundation owner: ANONYMIZED.

This package supplies the runtime layer for Sections 3, 4, and 7 and Appendices A and B. Structural Section 8 claims belong to `cpap-minor-free` and `cpap-outerplanar`.

Declaration names below are in `STACS2027.Runtimes`. **A** means the permitted Lean axioms only: `propext`, `Classical.choice`, and `Quot.sound`. **F** adds an explicit `Flow.MinCostFlowSolver F T` premise. **F+** also requires `Flow.AlmostLinear T`. These are theorem hypotheses, not added Lean axioms. Ordinary input, graph, and representation restrictions remain explicit.

| Paper result or required component | Checked declarations | Scope and dependencies |
| --- | --- | --- |
| Theorem 2; Appendix A | [`Flow.cpap4_flow_ram_semantic`](../Runtimes/Flow/Statement.lean#L76), [`Flow.cpap4_flow_single`](../Runtimes/Flow/Single.lean#L129) | **F**. Executed construction, flow call, and assignment extraction with an explicit T-dependent bound. The [`almost-linear single-program variant`](../Runtimes/Flow/Single.lean#L181) has dependency **F+**. |
| Sorting construction in Appendix A | [`Flow.enumeratedBuild_spec`](../Runtimes/Flow/EnumeratedConstruction.lean#L40), [`Flow.sortedNetworkConstruction`](../Runtimes/Flow/EnumeratedConstruction.lean#L83) | The builder itself has dependency **A**, deterministic sorting time, and label-independent linear memory. The full construction/solver/extraction specification has dependency **F**, including for any cycle permutation. |
| Corollary 3 | [`fourCycleAssignment_single_explicit`](../Runtimes/CpapSingle/Complete.lean#L21), [`fourCycleAssignment_single`](../Runtimes/CpapSingle/Complete.lean#L68), [`C4.fourCycles_ram_semantic`](../Runtimes/C4/Statement.lean#L40) | **F**, **F+**, and **A**, respectively. The complete program reads the graph, lists four-cycles, packs data, invokes flow, and returns an optimal assignment. Its memory bound retains a vertex-label term. |
| Theorem 4: Almost 2-SAT compiler | [`BoundedCost.actualCompilerRAM_fpt`](../Runtimes/BoundedCost/ActualCompilerRAM.lean#L56), [`BoundedCost.almostTwoSatFptSolverExists_of_citedFlow`](../Runtimes/BoundedCost/ActualCompilerRAM.lean#L89) | **F+**. A fixed program executes iterative compression, ternary scans, annotated branching, and flow-backed least-cut calls, returning normalized deletion and assignment output within C·15^Ψ·(Ψ + 1)·(N + 1)³ steps and addresses on its stated formula domain. |
| Theorem 4: bounded-cost assignment | [`BoundedCost.boundedCost_ram_fpt_from_citedFlow`](../Runtimes/BoundedCost/ActualFPT.lean#L15), [`BoundedCost.boundedCost_ram_all_from_citedFlow`](../Runtimes/BoundedCost/ActualFPT.lean#L32) | **F+**. The compiler instantiates the reduction, first for k ≥ 4, then as one program for every k ≥ 3. Its generic solver interfaces are not additional excluded algorithms. |
| Corollary 5: k ≥ 4 | [`ZeroCost.zeroCost_ram`](../Runtimes/ZeroCost.lean#L240), [`TwoSat.exists_linear_twoSat`](../Runtimes/TwoSatMain.lean#L189) | **A**. Executed prefix encoding, linear 2-SAT, and path recovery; O(k²t + m + 1) time and O(L + k²t + m + 1) addresses after cycle enumeration. |
| Section 3's triangle reduction; Corollary 5's k = 3 branch | [`Flow.triangle_single`](../Runtimes/Flow/Single.lean#L155), [`BoundedCost.boundedCost_triangle`](../Runtimes/BoundedCost/TriDecide.lean#L194), [`BoundedCost.boundedCost_triangle_almostLinear`](../Runtimes/BoundedCost/TriDecide.lean#L217) | **F**, **F**, and **F+**, respectively. The optimal triangle assignment gives a decision procedure for any budget, including zero. [`Flow.polynomialMinCostFlowSolverExists_of_almostLinear`](../Runtimes/Flow/PolynomialBound.lean#L63) has dependency **F+** and derives the ordinary polynomial flow bound from the same contract. |
| Algorithm 3: optimum search | [`BoundedCost.optimalCost_ram_fpt_from_citedFlow`](../Runtimes/BoundedCost/OptMain.lean#L85) | **F+**. One program builds the compact occurrence core once, tests increasing budgets, and outputs OPT followed by a valid assignment. Time and addresses have Theorem 4's bound evaluated at OPT. |
| Fixed-length cycle enumeration | [`generalCycleEnumerationRam`](../Runtimes/GeneralCycles/Main.lean#L78) | **A**. A uniform executed enumerator with C(m + 1)^(2k + 4) steps and addresses, independent of numeric vertex labels. |
| Algorithm 1, Lemma 15, and the executed greedy guarantee | [`Greedy.greedy_ram`](../Runtimes/Greedy/Main.lean#L120), [`Greedy.greedy_guarantee_ram`](../Runtimes/Greedy/Main.lean#L137) | **A**. O(kt + m + 1) time and O(L + kt + m + 1) addresses after enumeration. The latter proves the stated integer-form guarantee and retains its duplicate-free graph hypothesis. |
| Lemma 16 | [`QPRam.relaxSolver_ram_optimal`](../Runtimes/ConvexQP/RAM/RelaxSolver.lean#L80) | **A**. An exact optimal rational fractional solution in polynomial time and memory, with the cycle list supplied and a duplicate-free graph. The program uses an ellipsoid method and exact KKT rounding. |

The flow boundary is explicit even when hidden inside a named proposition's quantifiers: `Flow.sortedNetworkConstruction` proves a specification quantified over a correct supplied flow solver. Proving that specification does not provide the excluded solver's implementation. Likewise, the concrete Almost 2-SAT compiler's FPT theorem is conditional on both flow correctness and its almost-linear resource bound.

The repository's sole external algorithmic contract is the almost-linear minimum-cost-flow result cited below. Almost 2-SAT, cycle enumeration, sorting, 2-SAT, convex-relaxation solving, and formula-generated planar embedding are supplied by verified programs in the corresponding packages. The cited manuscript results remain cited. Some verified programs use alternative procedures meeting the required interface and bound; the source does not claim to reproduce every cited implementation verbatim.

## Machine model and inputs

The unit-cost RAM uses unbounded natural-number registers and memory, constants, addition, truncated subtraction, indirect loads and stores, output, tests, and loops. Every instruction or test costs one step. `RAM.ComputesIn` records a bounded actual execution and its output; endpoint theorems additionally bound the step count. Memory means the maximum permitted read/write address, including addressed input and scratch cells, rather than bit complexity or peak live storage.

Here m counts graph-list entries, t counts cycles, k is the cycle length, L bounds numeric labels, and Ψ is the budget. Most assignment programs take an enumerated cycle list, so general enumeration is charged separately. The complete Corollary 3 program includes enumeration itself. Label-indexed programs retain L in their memory bounds; sorting-based constructions prove their own label-independent bounds. The full four-cycle pipeline still includes its lister's label dictionary.

`Flow.MinCostFlowSolver F T` specifies correctness and bounds both steps and read/write addresses by T(N) on the admissible network class `GoodNet`. `Flow.AlmostLinear T` states that for every positive real ε there is a constant Cε such that T(N) ≤ Cε·N^(1 + ε) for N ≥ 1. This quantified premise is the flow paper's retained boundary; it is not a new Lean axiom or an unconditional theorem that the solver exists.

## Generic modular endpoints

| Intermediate theorem | Visible solver premises | Final instantiation |
| --- | --- | --- |
| `BoundedCost.boundedCost_ram` | `Almost2SatSolver F T` | The concrete compiler supplies the witness under F+. |
| `BoundedCost.boundedCost_ram_fpt` | `Almost2SatSolver F T`, `FPTBound T` | `boundedCost_ram_fpt_from_citedFlow` supplies the witness under F+. |
| `BoundedCost.boundedCost_ram_all` | A flow solver plus Almost 2-SAT and its FPT bound | `boundedCost_ram_all_from_citedFlow` supplies the Almost 2-SAT witness under F+. |
| `BoundedCost.boundedCost_ram_all_almostLinear` | The same, plus the flow almost-linear bound | `boundedCost_ram_all_from_citedFlow` leaves only F+. |

The earlier interfaces remain checked implications. Their solver arguments must not be mistaken for independent excluded algorithms: the final theorems instantiate Almost 2-SAT with `actualCompilerRAM_fpt`.

Separate-stage flow and enumeration theorems describe the stage inputs explicitly. The single-program endpoints execute the packing and relocation between stages; the complete `fourCycleAssignment_single` additionally reads the graph and lists its cycles. `comparator.json` records the 31 independently compared endpoints; other source-linked theorems in the map are covered by the library build and transitive axiom audit. Generated `Challenge` specifications are temporary and omitted from the distribution.
