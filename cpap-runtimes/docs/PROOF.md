# How the proofs work

Every running time is proved in the same way: an **abstract specification** — functions on
lists and finite maps that compute exactly what the program computes, loop by loop, with fuel
arguments where a loop's length is not known in advance — whose correctness is proved
mathematically, and a **RAM program** proved, phase by phase, to compute the specification
within a step bound **and a memory bound**, by Hoare triples with step counts and an address
bound. The two meet in the main theorem of each part. The library (`Runtimes/`)
uses the machine and verification library of `cpap-outerplanar` (`Outerplanar/RAM/Model.lean`, `Bounded*.lean`, `HT.lean`, `Frame.lean`,
`Layout.lean`, `Lib.lean`; see the module documentation in those files).

## 1. The machine and its logic

`HTB S s P Q b`: from every configuration satisfying `P`, the program `s` halts in a
configuration satisfying `Q` after at most `b` steps, by a run whose every `load` and `store`
uses an address below `S` (`RAM.ExecB S`). From the initial configuration on an input it gives
`RAM.ComputesIn s input output time S` (`HTB.computesIn`). The rules (`HTB.seq`, `HTB.ifz`,
`HTB.forUpC`, `HTB.whileCPot` with a potential, `HTB.forUpTele` and `HTB.forRangeTele` for costs
that telescope) compose triples; the frame rules (`Indep`, `Agree`, `wregs`: the registers a
program may write; `SameOn`, `ZeroFrom`: the memory it keeps) let phases be proved separately.
Loop-free blocks discharge their address obligations with `AddrOK S` and the tactic `addr_ok`;
memory-free blocks reuse their unbounded triples (`HTB.of_HT`). Each phase is specified for every
bound `S` above its layout (`hS : layoutEnd ≤ S`), and the regions of a layout are bounded once
(`fits` lemmas).

Data live in memory as arrays (`Arr m a l`), tables (`Tab`), linked lists of two-cell records,
CSR adjacency arrays, or flat matrices; memory is allocated by bumping `rFREE`. Each part owns a
block of registers (the outerplanar phases `10–69` and `100–137`, four-cycle phases `30–49`,
2-SAT `200–249`, Corollary 5 and Theorem 4 `250–299`, big-number arithmetic `400–449`, the
convex program `450–549`, the flow programs `550–599`, the merge sort `800–830`), and a phase
writes only `rT`, `rFREE`, its own block and those of the subroutines it calls.

Without multiplication, a product `x · y` is computed by a doubling table (`gCore`,
`ConvexQP/RAM/ArithCore.lean`: `O(size y)` steps and cells above `rFREE`, cleared again),
small products by repeated addition (the `mul` macro).

**Vertex labels.** A label-indexed dictionary (`labelBound g` cells, allocated and never
cleared: only cells written before are read) maps the labels of the cycles to identifiers in
`O(kt)` steps; it is used by the linear-time programs, whose memory bounds contain
`labelBound g`. The polynomial-time programs use the **sorting front end** instead
(`Sort/Front*.lean`, `Sort/Merge*.lean`): a stable merge sort of the occurrences by label
(`O(kt log(kt))` steps), first-appearance identifiers of the labels by `cpap-outerplanar`'s
`sortedLeads` and `rankIds`, and the identifiers of the edges by its `PairIds.pairIds`
(a counting sort of the identifier pairs and a timestamped scan); no memory indexed by a label,
`≤ 15kt + 1` cells above the input, and the same identifiers as the dictionary's (`eids_verts`).

## 2. Linear-time 2-SAT (`TwoSat*.lean`)

* **Abstract side.** Literal codes `2 · var + sign`, the implication graph, and the criterion
  (`criterion`): for a labelling of the `2n` nodes that does not increase along arcs and gives
  equal labels only to mutually reachable nodes, `f` is unsatisfiable iff some variable has
  both literals with the same label, and otherwise "`x` true iff its component comes after that
  of `¬x`" satisfies `f` (`twoSat_correct`).
* **Strongly connected components** (`TwoSatScc.lean`): the path-based algorithm in iterative
  form — a search stack, the stack `S` of visited vertices and the stack `B` of group
  boundaries; its invariant, the topological order (`final_spec`), and the measure `mu` that
  drops by more than the number of vertices a step pops (`mu_step`).
* **The program** (`TwoSatProg`, `TwoSatCsr`, `TwoSatSearch`, `TwoSatLoop`, `TwoSatPhase`):
  complement table, arcs, CSR out-lists, the search loop (amortized by `mu`), the answer pass;
  `exists_linear_twoSat`: `720 (n + m + 1)` steps and addresses.

## 3. Corollary 5 (`ZeroCost*.lean`)

The machine (`ZeroCostProg.lean`) reads `zeroCostInput g k`; maps the vertices of the cycles to ids
with the label dictionary and the edges to identifiers with `PairIds` (`ZeroCostInit`,
`ZeroCostEdges`: `O(kt)` steps, no table indexed by pairs); computes, per edge, the number of
cycles through it and the offsets of its prefix variables; pushes the literal codes of the
zero-cost formula — the path constraints `Γ₁` and the prefix clauses — (`ZeroCostGen`; the formula
`zcf g k` has exactly the clauses of Section 4's `zeroCostFormula g k`); runs the 2-SAT phase;
and writes `[0]`, or `1` and, per cycle, the first position whose vertex is incident to every
marked edge (`ZeroCostRec`: Algorithm 3's `omittedPosition`). Correctness is Section 4's
(`zeroCostFormula_satisfiable_iff`, `recoverAssignment_zeroCost`); `zeroCost_ram`:
`5000 (k²t + m + 1)` steps, `C (labelBound g + k²t + m + 1)` addresses.

## 4. Four-cycle listing (`C4/`)

* **The algorithm** (`Spec.lean`): a smallest-last (degeneracy) order computed with a bucket
  queue with lazy deletion (`pstep`), every edge oriented towards its later end, the 2-paths
  `x – z – y` whose centre is not the latest of the three inserted under the key
  `(min x y, max x y)` and paired with the centres already there (`reports`), each report giving
  the canonical cycle (`canon4`).
* **Correctness** (`Paths`, `Buckets`, `Canon`, `Output`): the inserted 2-paths are exactly the
  admissible ones, each once; every 4-cycle is reported exactly once (`enumOut_perm`: the output
  is a permutation of `cycles g 4`).
* **Bounds** (`Bounds`, `Supersat`, `Peel`): the number `P` of inserted 2-paths is at most
  `N² + t` for any order, and for the degeneracy order supersaturation gives
  `2 D |E| ≤ 4 X + 9 t` whenever `X³ ≥ |E|⁴` (`degen_bound`); hence
  `P ≤ 18 (t + min (N², ⌈m^{4/3}⌉))` (`numPaths_le'`).
* **The machine** (`Iface`, `PeelProg`, `PeelRAM`, `OrientRAM`, `SizeRAM`, `EnumLoops`,
  `EnumScan`, `EnumInsert`, `EnumRep`, `Grouped`, `Main`): the outerplanar R0 and R1 (relabelling
  with the label dictionary, CSR lists), PEEL, ORIENT, SIZE, then ENUM without a table indexed by
  key pairs: the inserted 2-paths are written as triples, sorted stably by their first key
  component (`P1.csort`, keys `< N`), and scanned with timestamped list heads per second key
  component, the scan reporting exactly `reports` (`scan_spec`, `Grouped.lean`); EMIT writes the
  cycles. `fourCycles_spec`: `O(m + 1 + t + min (N², ⌈m^{4/3}⌉))` steps, memory that plus
  `labelBound g`.
* `C4/Statement.lean` restates the bounds for every `X ≥ m^{4/3}` (`pow43_min`).

## 5. Min-cost flow: Theorem 2, `k = 3`, Corollary 3 (`Flow/`, `Cpap4Enum*.lean`)

* **The hypothesis** (`Solver.lean`, `docs/FOUNDATION.md`).
* **The networks for a list of cycles** (`Four`, `Tri`, `Enc4`): Section 3's layers built from
  any list `cs` of simple cycles, numbered nodes, `GoodNet` (`goodNet4`, `goodNet3`), sizes;
  Section 3's correspondence re-proved for `cs` (`flow_of_assignment4`, `assignment_of_flow4`,
  `optimal_of_minFlow4`, `optCost_of_optimal`).
* **The construction** (`EdgeSpec`, `Edges`, `Out`, `Prog`): the edge pass (Corollary 5's front
  end: label dictionary and `PairIds`) gives the identifiers `EID` and counts `CNT` of the
  occurrences; the output phases `out4`, `out3` write the network arc by arc, reading only `EID`
  and `CNT`. Their specifications `out4_specA`, `out3_specA` hold for **any** addresses of the
  two arrays (the invariant `OB cs k aE aC`); `out4_spec`, `out3_spec` instantiate them with the
  dictionary layout. `O(t + 1)` steps after reading the input, memory `C (labelBound g + t + m + 1)`.
* **Without the dictionary** (`SortTri.lean`, for Theorem 4): `build3s = ZeroCost.stepInit;
  Sort.front; out3` on `flowInput g (cycles g 3) 3`; after the front end the invariant `OB` holds
  at the front end's addresses (`ob_of_front`; its identifiers and counts are those of the flow
  construction by definition, `eid_cycles`, `cntF_cycles`, `eList_cycles`), so `out3_specA`
  applies: `build3s_spec`, `CB (t² + 1)` steps (the sort), `≤ 2m + 48t + 4` cells.
* **The extraction** (`Extract`): the position of each cycle read off two (or three) bits of the
  solver's answer, `O(t)` steps.
* **One program** (`Reloc`, `Pipe`, `Single`, `SortTri`): each stage is relocated into a residue
  class modulo 4 of registers and memory (register `r` of stage `j` becomes `4r + j`, addresses
  `4a + j`), writes being buffered into the next stage's input; `pipe3_spec` composes them
  (`tL + 12|x| + 4 (t₁ + t₂ + t₃) + 20` steps, `SL + 4 (|x| + |y| + |z| + S₁ + S₂ + S₃)`
  addresses).
* **Almost-linear bounds** (`Main`, `Single`): `split_bound` turns a time
  `s ≤ C₀ L + k T(at + 5)` into `s ≤ (C₀ + k T(5)) L + k C_ε 35^{1+ε} t^{1+ε}`: the constant of
  the linear terms does not depend on `ε`; the same for the memory bounds.
* **Corollary 3** (`cpap4_enum_of_lister`, `cpap4_enum_of_fourCycles`, `cpap4_enum_ram_explicit`,
  `cpap4_enum_ram`): a pipeline of four programs; the inputs of the later stages are formed
  outside the machine (linear glue, not charged).
* `Flow/Statement.lean`: `net4_hasAssignment_iff`, `net3_hasAssignment_iff` and the
  restatements with the network described by its properties.

## 6. Theorem 4 (`BoundedCost/`)

**`k ≥ 4`** (`Prog`, `Init`, `Form`, `Pc`, `Ov`, `Out`, `Extract`, `Zero`, `Main`, `Top`). The
programs read `boundedCostInput g k Ψ`, relabel with the sorting front end, write `Ψ + 1` copies of the
path constraints (`Pc.lean`) and the overlap clauses of every pair of cycles in Section 4's order
with a mark table (`Ov.lean`), so that the codes in memory are those of `almostFormula g k Ψ`;
then:

* `zero5` (`Ψ = 0`): the 2-SAT phase on `Γ_∅` and Corollary 5's recovery;
* `build5` (`Ψ ≥ 1`): writes `a2In (shiftF Γ') Ψ`, the variables shifted by one;
* `extract5`, on the input followed by the solver's answer: `[0]` if the answer is `[0]`
  (`noAssignment_of_shift`); otherwise the list `T` of true variables (it ends at the first zero
  cell) is turned into a bit table, which satisfies `Γ_𝓘` for the deleted overlaps,
  `|𝓘| ≤ Ψ` (`permitted_of_shift`), and Corollary 5's recovery answers
  (`answer_of_table`, Section 4's `recoverAssignment_correct`).

`boundedCost_ram`: each stage within `C5 ((Ψ+1)k²t + kt² + m + 1)` steps and addresses (the front
end's `O(kt log(kt)) ⊆ O(k²t + kt²)`, `clog_le_add`). `Top.lean`: `boundedCostTop F` reads `t` and `Ψ`,
restores the initial configuration, and runs `zero5`, outputs `[1]` (no cycle), or
`pipe3 lenP5 build5 F extract5` (`boundedCostTop_spec`, `boundedCost_single`); under `FPTBound`
(`solver_le_paper`, `bnd5_le_paper`) the total is `C P`, `P` the manuscript's bound
(`boundedCost_ram_fpt`).

**`k = 3`** (`Triangle.lean`, `TriCheck.lean`, `TriDecide.lean`), under the flow hypothesis.
`boundedCost_triangle_opt`: `triangle_sort_single` (the triangle pipeline with the sorting front
end) and `optCost_budget` (an optimal cost answers every budget). The decision machine
`triDecide Q = pipe3 lenP5 dropPsi Q triCheck` runs on `boundedCostInput g 3 Ψ`: `dropPsi` writes the
input without `Ψ`, `Q` writes the positions `pos` of an optimal assignment, and `triCheck`
(`Tri.triCheck_spec`) counts the pairs of triangles whose chosen edges are equal — the cost of
the assignment (`cost_tri`, `cost_selected_tri`) — in `O(t² + 1)` steps and writes `[0]` if the
count exceeds `Ψ`, else `1 :: pos` (`triDecide_spec`). `boundedCost_triangle`:
`C (t² + m + 1) + 16 T(21t + 5)` steps, `C (t + m + 1) + 16 T(21t + 5)` addresses.

**All `k ≥ 3`**: `boundedCostAll P3 P4` reads `k`, restores the initial configuration (`cfgK_init`) and
runs `P3` if `k ≤ 3`, `P4` otherwise (`boundedCostAll_spec`); `boundedCost_ram_all`: `C P + 16 T(21t + 5)`
steps and addresses (`tri_le_all`, `tri_le_all'`).

## 7. Lemma 15 (`Greedy/`)

`greedyProg` (`Prog.lean`): Corollary 5's front end (the identifiers `EID` of the occurrences),
a zero load table over the at most `kt` identifiers, and per cycle (`cycBody`, `O(k)` steps): the
total load of its edges, the load-sum of each option as the total minus the loads at its two
omitted positions, the first minimum (written), and the increments of the chosen path's edges.
The specification (`Spec.lean`, `Cycle.lean`) is Section 7's `greedy`, with ties broken by the
first minimizer (`zipWith_pos`). `greedy_ram`: `400 (kt + m + 1)` steps,
`400 (labelBound g + kt + m + 1)` addresses (`grSpace_le`); `greedy_guarantee_ram` adds
the proved integer-form greedy bound (`greedy_cost_integer_bound`).

## 8. Lemma 16 (`ConvexQP/`)

* **The instance** (`Inst.lean`): `t` cycles, `k` options each, loads `λ`, path loads `L`,
  `F(x) = ½ ∑ λ_e²`, the manuscript's `Φ = F − (k−2)t/2` on the product of simplices, the
  Frank–Wolfe gap, and the bridge to Section 7 (`relaxationObjective D R es = 2 D² Φ(W/D)`,
  `optimalFractional_of_min`). `the module documentation` lists the interface.
* **The quadratic program** (`QP.lean`): exact expansion of `F`, convexity, bounds, the KKT
  sufficient condition, the Frank–Wolfe step and gap, reduced coordinates.
* **Phase E** (`Loewner`, `Cut`, `Numeric`, `EllGeneric`, `EllPhase`, `EllSuccess`, `EllMag`):
  ellipsoids in support form, the central cut, rounding to `p`-bit integers, the generic
  invariant (Loewner bounds, determinant decrease per cut), so that after polynomially many cuts
  some iteration finds a feasible point with gap `≤ ε²` (`ellRun_success`), and the magnitudes of
  all integers.
* **Phases K, M, O** (`Border`, `Move`, `Exact`): from that point, the KKT system `G z ≤ h`;
  Phase M moves to a vertex, maintaining the determinant and the adjugate of a bordered square
  submatrix (exact integer division), and reaches a KKT point, hence an optimum; the output is
  `D = |Δ|` and the weights by Cramer's rule (`ConvexQP.relaxation_exact_optimal` in `EllSuccess.lean`;
  `solveExactWith_optimal`).
* **The machine** (`ConvexQP/RAM/`): signed big-number arithmetic on the add/subtract machine
  (`the module documentation`: multiplication and division by doubling tables, rounding, integer square
  roots, vectors and matrices; scratch tables above the free address, cleared again), the
  parser (the sorting front end, the overlap matrix and the constants), Phase E (`the module documentation`)
  and Phases K, M, O (`the module documentation`), each an `HTB S` triple with time and memory
  `C (tk + 2)^10`; the assembly `relaxSolver_ram_optimal_of` and `relaxSolver_ram_optimal`
  (`C (|input| + 2)^10` steps and addresses).

## 9. The compared statements

The compared forms are the library's main theorems where these mention only the problem, the
machine, the encodings, the hypotheses and `BoundedCostAnswer`; otherwise the restatements of
`Flow/Statement.lean`, `C4/Statement.lean` and `Cpap4EnumStatement.lean`, proved from them in a few
lines each, which describe the network written by its properties and replace `pow43` by every
`X ≥ m^{4/3}` (an equivalence). `scripts/compare_challenge.py` lists the constants the compared
statements depend on.


## Runtime implementation and scope (2026-10-12)

Foundation owner: ANONYMIZED. The sole cited algorithmic contract is the
almost-linear minimum-cost-flow solver (`MinCostFlowSolver` and `AlmostLinear`).

`Flow.enumeratedBuild_spec` proves the executed sorting builder without a flow hypothesis. `Flow.sortedNetworkConstruction` proves the complete construction specification, including solver and extraction runs, with an explicit correct flow-solver premise (F). Its construction and extraction bounds are label-independent. `fourCycleAssignment_single` composes the
four-cycle enumerator, input packing, and assignment solver into one actual RAM
execution. `generalCycleEnumerationRam` realizes general fixed-length cycle
enumeration in `C(m+1)^(2k+4)` time and memory.

### Actual Almost 2-SAT compiler

The semantic algorithm is proved in `Annotated`, `Exchange`, `Branching`,
`Search`, `Compression`, and `Iterative`. `FirstSuccess`, `CompressionPaths`, and
`EncodedIterative` identify the exhaustive path/vector enumeration with that
algorithm. `Contraction` and `CutNetwork` reduce least-deviation cuts to a
finite network while preserving parallel clause occurrences.

The executed implementation uses dense literal truth, forced-literal and clause
occurrence tables. `CompilerInit` copies the original codes and initializes the
all-false assignment. `PrefixCheckRAM` builds the exact prefix mask, copies the
reference, and counts false clauses. `CompressionStart` packs the compression
base and special clauses. `CompressionSeedRAM` translates each ternary vector
into its forced snapshot and deleted count. `ActualPathRAM`, `ActualInnerRAM`,
and `ActualOuterRAM` execute the annotated paths and both complete ternary scans.
`LeastCutRAM` executes contraction, the reusable flow-backed separator, and
candidate decoding; `ReusableCall` proves that each call preserves caller tables
and restores the flow-register invariant.

`ActualCompressionRAM` discharges the concrete compression callback.
`CompilerExecution` composes initialization, both budget cases, the complete
prefix loop, and normalized certificate output. `ActualCompilerRAM` then proves
`Almost2SatSolver` and `FPTBound` for that fixed program, with only the cited
flow contract. `CertificateRAM` emits sorted deleted positions and sorted
occurring true variables. `CompilerBounds` and `CompilerCostBridge` bound the
entire actual execution and memory by `C 15^Ψ(Ψ+1)(N+1)^3`.

`almostTwoSatFptSolverExists_of_citedFlow` proves the named construction claim;
`boundedCost_ram_fpt_from_citedFlow` instantiates the Theorem 4 reduction with
this executed solver; `boundedCost_ram_all_from_citedFlow` includes the triangle
branch and supplies one program for every `k≥3`. The Razgon–O’Sullivan citation remains the manuscript's
source for Almost 2-SAT.

### Computing the optimum

`OptMain.program` constructs the occurrence core once and tests budgets
`0,1,2,…` with the executed bounded-cost solver. `OptSpanRAM` computes the exact
per-budget workspace bound; `OptPowerRAM` computes `15^Ψ` by five arithmetic
instructions per iteration. `OptCall` relocates each solver call, preserves the
core and control state, and reuses the cleared workspace. `OptLoop` proves that
the first accepted budget is the optimum; `OptEmit` returns that number followed
by the successful assignment.

`OptGeometric` and `OptBounds` bound the complete executed search and memory by
`C * paper5 g k OPT`, including `OPT=0` and empty cycle lists.
`optimalCost_ram_fpt_from_citedFlow` supplies one program for every `k≥3` with
only the cited flow contract. Its `OptimumAnswer` contains the optimum and a
valid assignment of that cost.

The concrete `actualCompilerRAM_fpt`, `boundedCost_ram_fpt_from_citedFlow`, `boundedCost_ram_all_from_citedFlow`, and `optimalCost_ram_fpt_from_citedFlow` endpoints have dependency F+: both flow correctness and its almost-linear resource bound are explicit premises. Generic intermediate interfaces accepting `Almost2SatSolver` and `FPTBound` are instantiated by this compiler. They do not add a second external algorithmic contract. All delivered proof libraries contain checked proofs; temporary generated `Challenge` specifications are omitted from the distribution and default targets.
