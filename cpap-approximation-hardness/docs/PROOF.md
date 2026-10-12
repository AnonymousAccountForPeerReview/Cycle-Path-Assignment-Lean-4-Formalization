# How the proofs work

This package covers Section 6 and Appendix D, the Section 5 reduction
algorithms and formula-only planar incidence embedding, and the formalized
source-hardness chain. The shared CPAP model and gadget library are supplied
by `cpap-np-hardness`.

Throughout, `k ≥ 5`, `f` is a Definition 7 formula with `m = f.length` clauses and
variables `0, …, n − 1` (`n = variableBound f`), and `G = formulaGraph k f` is the
Theorem 8 graph of the `cpap-np-hardness` formalization. A cycle-path assignment of `G` is handled, as in
that formalization, as a choice `choose : Cycle → Nat` of omitted vertex on the family
`formulaFamily k hk f` of its `k`-cycles (`formulaGraph_assignment_iff_family`); the paths
of variable gadget `v` are `variableChosen k hk choose v`, those of clause gadget `j` are
`clauseChosen k hk f choose j`.

## The cost as a sum over gadgets and ports (`ApproximationHardness/CrossCost.lean`, `ApproximationHardness/Soundness.lean`)

The `cpap-np-hardness` formalization decomposes the cost as
`∑_v cost(V_v) + ∑_j (cost(C_j) + crossCost(V, C_j))`, the cross cost being the pairwise
overlaps between the variable paths and the paths of clause gadget `j`. A variable gadget
and a clause gadget share only the identified literal ports
(`formulaGraph_shared_edge`), and with distinct variables per clause, gadget `v` and gadget
`j` share at most one port. `crossCost_eq_ports` therefore writes the cross cost as
`∑_e load(V_v, e) · load(C_j, e)` over the shared ports, and `crossCost_global_eq` as a sum
over the literals `p` of clause `j` of `ℓV(p) · ℓC_j(p)`, the loads of the two gadgets at
the port of `p`. So

`c(τ) = ∑_v cost(V_v) + ∑_j cost(C_j) + ∑_j ∑_{p ∈ clause j} ℓV(p) ℓC_j(p)`
(`cost_formulaFamily_eq`).

## Port loads (`ApproximationHardness/PortLoads.lean`)

Each literal edge of a clause gadget lies on exactly one of its `k`-cycles, so the clause
gadget loads it at most once (`clauseFamily_port_load_le_one`, by `decide` on the
unsubdivided skeletons and the port-load transport of Section 5). `clauseChosen_local`
transports a placed clause gadget to its local copy with the same cost and port loads,
indexing the ports by the placed literals; this yields the placed forms of observation
(iii) of Theorem 8 — the cost plus the loads at all literal ports is at least two
(`clauseChosen_blocked_lower`) — and of "every clause gadget costs at least one".

## Normalization (`ApproximationHardness/Normalization.lean`)

For weights `w ≤ 1` on the three ports of a variable gadget, one of its two truth states has
weighted port load at most the gadget's own cost plus its weighted port load. This is
checked by `decide` on the skeleton (`variableSkeleton_weighted_normalizes`: every pair of
omitted vertices, every `0/1` weights), transported to every subdivision with the
Section 5 lemmas `expanded_family_normalizes` and `expanded_family_port_normalizes`
(`variableExpansion_weighted_normalizes`), and to the placed copy with the relabelling
lemmas (`variableChosen_weighted_normalizes`). The bound `w ≤ 1` is where the port loads
of the previous paragraph enter: with loads of two, a gadget could prefer a non-truth state.

## Soundness: `c(τ) ≥ 2m − s(A)` (`formulaFamily_cost_lower_bound`)

Regroup the port terms by variable and port (`regroup_by_variable_port`): the weight
`W_v(i)` of port `i` of variable `v` is the total clause load there, at most one
(`portWeight_le_one`, since no two placed literals share a port). Normalizing each variable
gadget with these weights defines `A(v)` as its better truth state, and gives
`∑_v [cost(V_v) + ∑_i ℓV_v(i) W_v(i)] ≥ ∑_v ∑_i ℓS_{A(v)}(i) W_v(i)`, where the truth state
loads port `i` iff the literal there is false under `A` (`variableState_literal_load`).
Regrouped back by clause, each clause `j` contributes
`cost(C_j) + ∑_{p false} ℓC_j(p)`, which is at least `1`, and at least `2` when every
literal is false, i.e. when clause `j` is unsatisfied (`clause_contribution`). Summing,
`c(τ) ≥ m + (m − s(A))`.

## Completeness: `c(τ) ≤ 2m − s(A)` (`formulaGraph_cost_upper_bound`)

Variable gadgets take the truth states of `A` (cost `0`, port loaded iff the literal is
false: Section 5's `placedVariable_sat_witness`). A satisfied clause gadget takes Section
5's witness of one of its true literals (cost `1`, no load at ports of false literals), so
its cross term vanishes. An unsatisfied clause gadget takes the witness of its first
literal under the assignment with that literal's variable flipped
(`placedClause_unsat_witness`): cost `1`, no load at the other ports, load at most one at
its own port, against a variable load of one; its cross term is at most `1`. The choices
are combined with Section 5's `combine_indexed_choices`.

## Theorem 11 (`ApproximationHardness/LReduction.lean`, `ApproximationHardness/RandomAssignment.lean`)

`C* + S* = 2m` from the two bounds at the optima. `S* ≥ 3m/4`: among the `2^n`
assignments of the variables below `n` (`boolLists n`), exactly `2^(n−2)` falsify a given
pair of literals on distinct variables (`count_two`, by induction on `n`), so each clause is
satisfied by at least `3 · 2^(n−2)` of them; summing over clauses and taking the best
assignment gives `4 S* ≥ 3m` (`exists_three_quarters`). Then `3 C* ≤ 5 S*`, and for every
`τ` the decoded `A` has `S* + C* ≤ s(A) + c(τ)`.

## Lemma 10 (`ApproximationHardness/Polarize.lean`, `ApproximationHardness/PolarizeLReduction.lean`)

Eliminating a variable that occurs three times with one polarity deletes every clause
containing it; with tautologies also deleted, every remaining variable has at most two
positive occurrences (three would make it pure in `f`) and, after complementing those with
two, at most one positive and two negative (`polarize_boundedOccurrence`); non-tautological
clauses of distinct literals have distinct variables (`polarize_clauseVariablesDistinct`).
Semantically, `satisfiedCount` splits over deleted and kept clauses; the extension by pure
values satisfies every deleted clause and does not touch the kept ones
(`extendPure`); complementation corresponds to flipping the assignment
(`satisfiedCount_flipFormula`); the padding adds at most, and for the all-true extension
exactly, `r` (`satisfiedCount_padding_le`, `satisfiedCount_padTrue_padding`). Hence
`s_{φ'}(b) ≤ s_φ(recover b)` and `s_φ(a) ≤ s_{φ'}(…)`, so the optima agree and the
recovery loses nothing.

## Composition and transfer (`ApproximationHardness/Composition.lean`)

Two L-reductions compose with the products of the parameters
(`LReductionSat.comp_cpap`), by adding suitable multiples of the two β-inequalities. An
L-reduction with `α = αn/αd`, `β = βn/βd` turns a target solution within `1 + εn/εd` of
`C*` into a source solution within `1 − αβ εn/εd` of `S*` (`approximation_transfer`).

## Theorem 11 and Corollary 12 (`ApproximationHardness/Hardness/`)

The hardness notions are those of Max3SAT-MaxSNP-APX-Lean4: optimization problems on
words (`Complexity.OptProblem`: a direction and a solution relation `Sol x y v`), L-reductions
with polynomial-time maps `f` on instances and `g` on `pairWords x y`, MaxSNP as the NPO problems
L-reducible to a problem of the syntactic class MaxSNP₀ (structures of fixed input and solution
signatures on the universe of the instance, a well-formed quantifier-free formula), APX-hardness
under PTAS-reductions. `CPAP(·, k)`
is `cpapProblem k` (`Problem.lean`): the instances are the codes of record lists in the
Section 5 CPAP format without budget records, the solutions the codes `Sim.encodePaths ps` of
cycle-path assignments of the written graph, the value the cost; on records writing `G` its
optimum is `C*` (`cpapProblem_isOpt_iff`).

That formalization's 3-OCCURRENCE MAX-3-SAT (`Complexity.max3SAT3`) allows clauses of at most
three literals, with repetitions, and assignments written as words no longer than the instance.
`normalize` (`Normalize.lean`) maps its formulas to Lemma 10's instances: in each clause, repeated
literals are removed (`eraseDups`); an empty clause is dropped; the `i`-th clause, if it has one
literal `l`, becomes `(l ∨ z)(¬z ∨ w)(¬z ∨ ¬w)` with `z = n + 2i`, `w = n + 2i + 1`. Every clause
of the result has two or three distinct literals (`normalize_clauses`); the original variables
occur at most as often as before (their literals form a sublist of the original ones,
`normFrom_filter_sublist`), `z` three times and `w` twice (`occurrences_normFrom_fresh`); so the
result is a `ThreeOccurrence` formula. The gadget satisfies at most `2 + [l]` of its clauses, and
exactly that many when `z` is false (`satisfiedCount_gadget_le`, `satisfiedCount_gadget_eq`), so
every assignment satisfies at most `2u` more clauses of `normalize f` than of `f`
(`satisfiedCount_normalize_le`), and the assignment that sets the fresh variables to false
exactly `2u` more (`satisfiedCount_normFrom_eq`): `OPT(normalize f) = OPT(f) + 2u`
(`isMaxSat_normalize`). An assignment or its complement satisfies every nonempty clause, so
`u ≤ 2 OPT(f)` (`two_mul_unitCount_le`).

The L-reduction (`Reduction.lean`) maps the code of `f` to `Rev (Inst (G23 (FN x)))`: `FN`
computes `normalize` (polynomial-time in the `PT` framework of Max3SAT-MaxSNP-APX-Lean4,
`pt_normalize`, by `fun_prop`), `G23` Lemma 10's transformation (`polarize_polyTime_machine`), `Inst` the
records of `(formulaGraph k ψ).reverse` (`cpap_lreduction_polyTime`), and `Rev` reverses the
record list, so that the instance writes `formulaGraph k ψ`, `ψ = polarize (normalize f)`. Its
optimum `C*` has `3 C* ≤ 5 S*(ψ) = 5 (OPT(f) + 2u) ≤ 25 OPT(f)`, so `C* ≤ 9 OPT(f)`. The solution
map (`solMap`) decodes the paths with the decoding map of Theorem 11 (`decoder_polyTime`), undoes
Lemma 10 (`recover`, polynomial-time by `PT.recover'`) and writes the values of the variables
below the length of the instance, which covers all variables of `f`. With
`S*(ψ) + C* ≤ s_ψ(A) + c(τ)`, `s_ψ(A) ≤ s_{normalize f}(recover A)` and
`s_{normalize f}(B) ≤ s_f(B) + 2u`, this gives `OPT(f) − s_f ≤ c(τ) − C*`: `β = 1`
(`lReducible_max3SAT3_cpap`). Within the proof the formula `ψ` is generalized to a variable once
its properties are recorded; otherwise the elaborator unfolds the Theorem 8 construction when it
compares types.

`Main.lean` concludes: `MaxSNPHard.of_lReducible` with `max3SAT3_maxSNPHard` gives Theorem 11's
MaxSNP-hardness; `lReducible_max3SAT_max3SAT3` composed with the reduction, and
`apxHard_of_lReducible_max3SAT` with the witness-recovering PCP theorem `witnessGap`, give its
APX-hardness; `maxSNPHard_not_hasPTAS` and `maxSNPHard_no_ptas` give Corollary 12.

## The instance map on the Section 5 word machine (`ApproximationHardness/InstanceMap.lean`)

A Definition 7 formula has no unit or empty clause, distinct literals in every clause and no
tautology, so the preprocessing of the Section 5 full-domain construction is the identity:
`normalizeClauses f = f`, `firstUnit f = none`, `unitReduce _ f = some f`, hence
`cleanFormula f = some f` and `globalReductionGraph k f = formulaGraph k (padFormula 0 f) =
formulaGraph k f`. On the word machine, the unit-propagation kernel only pops its queue
(`kernel_trivial`, `size + 1` transitions), and the stages are chained exactly as in the
Section 5 proof of `full_domain_linear` (normalization, initialization, the kernel, extraction,
padding with `r = 0`, the header and the graph constructor), with the trivial endpoint table,
under which the oriented gluing is the plain gluing (`orientedFormulaGraph_trivial`). The
transition count is bounded as there, giving `(n + 1)(128k + 160)`. Finally an L-reduction is
unchanged when each instance graph is listed in another order (`LReductionToCPAP.of_perm`,
through `hasAssignment_graph_perm`), so Theorem 11 holds for the graph as computed.

## The instance map in the foundation's machine model (`ApproximationHardness/Registered/`, `ApproximationHardness/RegisteredInstance.lean`)

The foundation's stack language has registers holding words over `{true, false}`, a
fixed instruction set (copy, append, pop, comparison of unary numbers, bounded loops)
with an exact cost for every instruction (`Complexity.StackTableauProgram.Exec`), and a
compiler theorem, `StackCompile.polyTime_of_stack`: a program halting on every input of
length `L` within `bound L` instructions, `bound` polynomial, computes a `PolyTime` word
function on the single-tape machine. The instance map is such a program
(`Registered.program`, 42 registers; numbers are unary blocks of `true`, so a vertex
`v` costs `O(v)` to write).

* `Framework.lean` gives a Hoare-style calculus with costs: `Spec c P cost m` says that
  from any register file satisfying `P`, command `c` halts within `cost` instructions in
  the state `m r`, with rules for sequencing, loops (with an invariant and an iteration
  count) and branches. `Macros.lean` builds on it the emission of a CPAP record pair for
  an edge (`emitEdge`, `emitEdges`) and the reading of unary numbers.
* `Program.lean` and `Machine.lean`: pass A reads `encode f` once and computes
  `n = variableBound f`; the variable loop writes the records of the `n` variable gadgets
  (blocks of width `gadgetWidth k`); pass B treats the clauses in order. For each literal
  of a clause, `Literal.lean` reads it, moves its code onto a register holding every
  literal read so far, and counts that literal's occurrences there by a scan, which with
  the sign gives its variable port (Section 5's `placeLiterals`, `PlacedLiteral.port`);
  `Clause.lean` then writes the
  clause gadget's edges with those ports as endpoints. The cost of each part is an
  explicit polynomial in the input length `L` (`mainCost`, roughly cubic: `L` clauses,
  each scanning `O(L)` literals at `O(L)` per comparison), and `polynomial_bound` proves
  `PolynomialBound (bound k)` compositionally.
* `Semantics.lean`, `Records.lean`, `Correct.lean`: every macro is given a functional
  model (`mainModel`), and the models are evaluated on `encode f`: the scan returns
  `past.count l`, the port endpoints are those of `placeLiterals`, the clause loop
  appends `clauseRecords`, and the final output register holds
  `encode (formulaRecords k f).reverse` (`instanceMapWord_encode`). The records are
  shown to write `(formulaGraph k f).reverse` with budget `0` (`formulaRecords_output`,
  in Section 5's `GraphOutput` format), using Section 5's `GraphOutput.reverse` and the
  description of `formulaGraph` by blocks.

`cpap_lreduction_polyTime` combines `polyTime_instanceMapWord`, the output theorem and
`cpap_lreduction_computed` (the L-reduction for the reversed graph).

## Theorem 8 in `O(n)` time and space on the unit-cost RAM (`ApproximationHardness/RAM/`, `ApproximationHardness/LinearRAM.lean`)

`Model.lean` defines the machine: `Exec s c t c'` is a big-step semantics with exact step
counts (one per instruction, one per branch test, one per loop test), deterministic
(`Exec.det`). `Spec.lean` gives, for loop-free programs, the result `run s c` and the
cost `cost s c ≤ size s` (`exec_run`, `cost_le_size`), and a `Sat` calculus with loop
invariants (`Sat.loop`, `iterate_invariant`).

Space. `Bounded.lean` (the same definitions as the outerplanar formalization's) defines `ExecB S`, the
runs whose `load` and `store` instructions address only cells below `S`, and
`ComputesIn s input output time space`; `ExecB.congr` shows that such a run does not depend on
the memory at or above `S`. `SpecB.lean` is the bounded twin of `Spec.lean`: `AddrOK S s c`
says that every load/store address along `run s c` (loop-free `s`) is below `S` and reduces to
arithmetic by `simp` (`addrOK_seqs_cons`, `addrOK_ifz`, …); `SatB S s P m b` is `Sat` over
`ExecB S` runs, with the same rules (`SatB.ofLoopFree` asks for `AddrOK` on the
configurations satisfying `P`; `SatB.of_Sat` lifts any `Sat` proof of code without
`load`/`store`); `exec_loopFree`, `exec_listPass`, `exec_countLoop` and `sat_clausePass`,
`sat_countLoop` (`Pass.lean`) produce `ExecB S` runs and ask for `AddrOK` of their bodies. The
address obligations are discharged by `simp` on the block and `omega` with the facts the time
proofs already have (the input pointer inside the input, variables below `n`, the layout
registers); for longer blocks (the decoder's port counters, `keepBody`) by composing the
`AddrOK` of their parts along frame lemmas.

`Program.lean` defines `program k = passA; passV; passB` and the reference output
`ramOutput k f = f.length :: edgeWord (formulaPairs k f)`:

* pass A (`PassA.lean`) walks over the input once, computing `n` (the largest variable
  plus one) and the end `N` of the input; cost `O(|input|) = O(m)`;
* pass V (`PassV.lean`) loops `n` times; iteration `v` stores the first vertex `vb` of
  gadget `v` in the block table at `B + v` (`B = N + 2n`) and writes the endpoints of the
  `gadgetWidth k`-wide gadget's edges (a loop-free block of constant size depending on
  `k`); cost `O(n)`;
* pass B (`PassB.lean`, `Correct.lean`) loops `m` times; for each literal `(v, s)` it reads
  the occurrence count at `N + 2v + s` (memory beyond the input starts at `0`),
  increments it, derives the port (`0` for the positive occurrence, `1 + count` for a
  negative one) and the endpoint `B[v] + offset`, then writes the clause gadget's edges
  (constant size); cost `O(m)`.

The invariants say that after `j` clauses the count table holds the occurrence counts of
the first `j` clauses and the output is `f.length :: edgeWord` of the pairs of the variable
gadgets and the first `j` clause gadgets (`clausePairsFrom`, `StateB`). Hence
`ram_computes`: output `ramOutput k f` within `ramConst k · (m + n + 1)` steps, `ramConst k`
the sum of the loop-body sizes. `formulaGraph_eq_pairs` identifies the normalized pairs with
`formulaGraph k f`, and Section 5's `2m ≤ 3n` gives `3 ramConst k · (n + 1)`
(`ram_linear_time`). Every access is to the input (pass A, the literal reads of pass B: the
pointer stays inside the input, `InvA.p_le`, `LitPre.hpN`), to the count table `[N, N + 2n)` or to
the block table `[N + 2n, N + 3n)` (variables `v < n`), so the run is an `ExecB (N + 3n)` run
(`sat_passA`, `sat_passV`, `sat_passB`, with `readLit_step` and `StateB.step` returning the
address conditions); `N ≤ 7m + 1` and `2m ≤ 3n` bound the space by `17 (n + 1)`, and
`ram_linear_time` states time and space with `ramLinConst k = 3 ramConst k + 17`.
`gadget_reduction_linear_ram` adds Section 5's `formulaGraph_sat_iff_assignment`.

## Lemma 10's map and the decoding map on the RAM (`ApproximationHardness/RAM/Polarize/`, `ApproximationHardness/RAM/Decode/`)

`polProgram` (Lemma 10) makes a counting pass (the occurrences of each literal, in a table
indexed by literal), marks the variables occurring three times with one polarity and those
occurring twice positively, then writes `ramInput (polarize f)`: the clause count, the kept
clauses with complemented literals, and the `r` padding clauses on fresh variables. The
invariants are the count table after a prefix of the clauses (`Polarize/Main.lean`,
`Keep.lean`, `Delete.lean`), and `pol_computes` bounds the steps by `polConst · (m + 1)`;
since every 3-OCCURRENCE formula has `2m ≤ 3n` clauses, `polarize_linear_time` gives
`2 polConst · (n + 1)` steps. Its memory is the input, the counts `N + 2v + s` and the table
`N + 2n + v` of positive kept occurrences, below `polSpace f = N + 3n ≤ 14 (n + 1)`
(`Polarize/Space.lean`: `SlotsBelow`, the slots of a read clause hold variables below `n`;
`cntBody_addrOK`, `keepBody_addrOK`, `outBody_addrOK`).

The decoding map is first made explicit (`ApproximationHardness/Decode/`): `decodeAssign k ps v` compares
the loads `W₀, W₁, W₂` that the chosen paths leaving the block of `v` put on its three port
edges, and `cpap_lreduction_decoder` proves that it satisfies the second L-reduction
inequality, by transporting the normalization of the soundness proof to the family of chosen
paths (`Family.lean`, `Transport.lean`, `Bound.lean`). `decProgram k` builds a block and an
offset table for all `(m + n) · gadgetWidth k` vertices, reads each path once to decide
whether it leaves a block and, if so, once more to add its port edges to counters, and writes
the bit `[W₁ + W₂ ≤ W₀]` of every variable; `dec_computes` bounds it by `decCost k f ps`, and
`decoder_linear_time` by `decLinConst k · (n + 1)` on valid choices, which have
`|ps| ≤ 2n + 10m` paths of `k − 2` edges. Its memory is the input (of length `|decInput f ps|`),
the tables `E + 2x`, `E + 2x + 1` of the vertices `x < (m + n) w` (every path vertex is below
`(m + n) w`, `PathsBelow`), and the counters `Wb + 3v + i` of the variables `v < n` (the program
tests `bx < n` before counting): `decSpace k f ps`, at most `decSpaceConst k · (n + 1)` on valid
choices (`decSpace_le`).

## The foundation's machine model (`ApproximationHardness/Sim/`)

A generic simulation turns these RAM programs into single-tape machines. `XRAM.lean` extends
the RAM by `getBit` (the next input bit) and `emit`; `Simulate.lean` runs an XRAM program in the
foundation's structured stack language (`StackTableauProgram.Command`): numbers in binary,
least significant bit first, on stack registers (`Bits.lean`, the bit-serial adder and
subtractor of `Arith.lean`), the memory as an association list of key-value numerals read and
written by linear scans (`Memory.lean`), and every loop bounded by a fuel counter. `sim_correct`
relates one XRAM run with fuel `F` to one stack run, with a cost polynomial in `F` and the
number sizes, and `xram_polyTime` (with the foundation's `StackCompile.polyTime_of_stack`)
turns an XRAM program halting within a polynomial bound into a `PolyTime` word function.
`Transform.lean` embeds a RAM program into the even memory cells of an XRAM program with its
output on the odd cells (`tr`, `tr_exec`: at most four XRAM steps per RAM step); `Parse.lean`,
`ParsePaths.lean` and `OrientRegistered.lean` read the unary codes into memory and
`Serialize.lean` writes the outputs. `polX`, `decX k` and `orX` are the three pipelines.
The simulation's cost depends on the number of steps and on the bit lengths of the numbers
(a load scans the association list, whose entries are at most the number of stores), not on
the range of the addresses, so these pipelines take the RAM runs from the bounded theorems
(`ExecB.exec`) and use only their time bounds; the space bounds are not needed and do not
change them.

## The planar orientation (`ApproximationHardness/Planar/`, `ApproximationHardness/RAM/Orient/`)

Section 5 proves `orientedFormulaGraph_planar_prescribed`: if each gadget piece has a spherical
embedding whose boundary ports appear, along the outer face, in the cyclic order of the
corresponding node of the incidence embedding (`HasSourceOrders`), and the endpoint bits are
the boundary directions of the ports, the glued graph is planar. Section 5's own source rule
needs every node to use all its ports. Here (`ExplicitOrientation.lean`):

* every piece gets a fixed profile, the signed variable profile of Section 5, and the
  three-literal clause profile or its mirror image (`piece_explicit_profile`), the direction
  given by the explicit signs; their sides give the explicit bits (`explicit_sides`);
* the source order of a node with `r` used ports among `m ∈ {2, 3}` is realized by first-hit
  walks that skip the unused ports (`NextSelected.chain`, `NextSelected.skip`): with `r = 1`
  the walk goes once around, with `r = 2` it skips at most one port, and with all three ports
  used the profile must follow the order exactly (`cyclic_skip`); the order is a 3-cycle,
  decided by the successor of one dart (`three_cycle_sign`), which is what `variableSign`
  (the successor of the positive occurrence's dart) and `clauseSign` (the successor of the
  first literal's dart) compare;
* a fixed point of a node's order means a single dart (`NodeDartIndex.order_fixed`).

`orientationChoices_planar` assembles these with Section 5's gluing theorem, and
`orientationBits_planar` restates it for a rotation list. The RAM program `orProgram` makes
one pass over the clauses (for each occurrence its port from a counter of earlier equal
negative literals, the first positive occurrence of each variable, and a record `port, v, port,
cs` at `B + 4i`) and one over the occurrences (the bit `[port = 0] ⊕ vs ⊕ cs`, the variable sign
read from the record of the dart `rot[2 i₀]` at `B + 2 rot[2 i₀]`); `or_computes` and
`orCost_le` give `orConst · (|ramInput f| + 1)` steps. Its memory (`orSpace f`) is the input, a
copy area up to `E = 2N`, the two cells `E + 2v`, `E + 2v + 1` of every variable number `v < n`
and the records `B + 4i` (`B = E + 2n`) of the occurrences; the dart read at `B + 2 rot[2 i₀]`
is in range because every entry of a planar rotation list is a dart, below
`2 |f.flatten|` (from `IsPlanarRotation`). Hence the space bound `4 (N + n + 1)` of
`orientation_linear_time`, where `n` appears because the per-variable cells are indexed by
variable number.


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


The bounded RAM proof composes the following checked stages:

1. `prepareForestPlan_spec` starts at the actual numeric formula input. It parses
   incidences, materializes adjacency, runs a bounded DFS loop, initializes the
   solver's arrays and compiles every vertex, dart and postorder plan entry.
2. `defaultSolverProgram_spec` caches both local rotation directions, then runs
   the linked solver for its proved `20E` budget. Every dispatcher branch has an
   actual constant-size RAM implementation; the final memory refines the complete
   semantic solver state and its exact consuming-group records.
3. `orientationProgram_spec` materializes the reverse postorder group keys and
   remaining dart keys, then executes the group orientation fold. The consuming
   records prove that its finite bit array is a consistent orientation.
4. `readoutProgram_spec` reads each dart's representative and encoded solver bit,
   selects the cached successor or predecessor, and writes the exact `rotOut` list.
   `rotOut_planar` proves that this output represents a planar hypermap of the
   formula's incidence graph.

Every composition uses `RAM.ExecB`; frame proofs preserve the graph and plan caches,
solver arrays, orientation array and rotation caches across the phases. The final
space inequality unfolds the allocated cache layouts and bounds their last address
linearly in the formula input length plus `variableBound f`. The proof of
`planarEmbedding_linear_ram` supplies the fixed program and common constant directly;
no separate implementation, per-step refinement premise or supplied embedding is
assumed.
