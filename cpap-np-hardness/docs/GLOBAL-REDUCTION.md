# Checked global correctness on the full Definition 7 domain

The following theorem is proved in `NPHardness/GlobalReduction.lean`:

```lean
theorem globalReduction_sat_iff_assignment {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) :
    Satisfiable f ↔ HasAssignment (globalReductionGraph k f) k f.length
```

`BoundedOccurrence` is exactly Definition 7: every clause has two or three
literal entries, each variable occurs positively at most once and negatively
at most twice, and all counts include multiplicity. The conclusion uses the
original number of clauses, including clauses removed by preprocessing.

`globalReductionGraph` is a computable function, built from the concrete
`formulaGraph` constructor. The latter allocates occurrences to variable ports
and identifies actual vertex labels. The theorem does not assume a reduction
certificate, the absence of crossing cycles, local gadget axioms, or a
cost-decomposition axiom. Those properties are proved.

## Preprocessing and the original budget

1. Remove duplicate literals within each clause, then remove tautological
   clauses. Evaluation is preserved for every assignment.
2. Propagate unit clauses. Each propagation removes at least one clause, so
   fuel equal to the initial clause count suffices. The proof preserves
   satisfiability, signed occurrence bounds, and the distinct-variable property.
3. On success, the resulting formula `g` has only two- or three-literal
   clauses with distinct variables, and `g.length ≤ f.length`. Adjoin
   `f.length - g.length` clauses of two fresh positive variables. Each added
   clause can be satisfied independently, so satisfiability is unchanged and
   the clause count is restored exactly.
4. On detecting a contradiction, construct the graph for `f.length + 1`
   disjoint fresh two-literal clauses. Every assignment to this graph costs
   at least `f.length + 1`, excluding the target budget `f.length`.

The graph map branches only on this explicit simplification procedure; it
does not decide SAT as an oracle. The raw gluing lemma
`formulaGraph_sat_iff_assignment` retains a `ClauseVariablesDistinct`
hypothesis, which the preprocessing proves before applying it. The final
theorem has no such extra hypothesis.

## Raw gluing proof

The proof includes all `k ≥ 5`, including the exceptional two-literal gadget
at `k = 6`. It proves the following chain:

1. Each local gadget embeds injectively. Distinct variable copies and distinct
   clause copies have disjoint vertex images. Shared variable/clause edges are
   exactly allocated literal ports.
2. A path crossing a variable between different ports has at least
   `floor((k-2)/2)` edges. A same-port detour has at least `k-1` edges.
3. An excursion leaving a clause and its starting variable has at least
   `2*floor((k-2)/2)+2` edges. A `k`-cycle through a private clause vertex cannot
   leave that clause. Cycles with no private clause vertex stay in one variable.
4. Every global `k`-cycle lies in one gadget. The assembled representative
   family is complete and contains each cycle edge set exactly once.
5. CPAP assignments and costs are invariant under replacing the executable
   cycle enumeration with this complete distinct family.
6. Costs inside the variable copies and clause copies add, with each cross
   overlap charged to the corresponding clause. Budget `f.length` forces each
   variable's cost to zero, each clause's cost to one, and each cross cost to zero.
7. Zero-cost variable assignments normalize to truth values. A cost-one clause
   uses a literal port; absence of cross overlap forces that literal to be true.
8. Conversely, a satisfying assignment supplies variable truth states and a
   witness using a true port in each clause. Their combined cost is the clause count.

## Output size

`globalReductionGraph_edge_bound` in `NPHardness/GlobalSize.lean` proves

```lean
(globalReductionGraph k f).length ≤
  (variableBound f + 2*(f.length+1)) * (2*k) + (f.length+1) * (10*k)
```

for every `k ≥ 5`. This counts edge-list entries, including repeated copies
of shared attachment edges; graph membership treats them as one edge.
For fixed `k` the bound is linear in the variable-label bound and clause
count. `variableBound f` is one plus the greatest variable index, or zero
for an empty formula; it is not necessarily the number of distinct variables
when labels are sparse. The `2*m ≤ 3*n` theorem applies to Definition 7
inputs whose labels lie below `n`.

## Planar assembly and runtime

`PlanarAssembly.orientedFormulaGraph_planar_exists` proves that every Definition 7
formula with planar incidence admits endpoint choices making its actual oriented
graph planar. The global hypermap uses source cyclic orders and spherical gadget
pieces, with exact edge-list and endpoint correspondence. Local planarity alone
is not used as a substitute for this gluing theorem.

`PlanarPreprocessDeletionClosure` proves edge deletion and planarity through
normalization, unit propagation, and fresh padding. Thus
`planar_full_domain_supplied_table` covers the full domain, including tautologies
and repeated literals. It combines planar output, original-budget correctness,
graph records, and at most `(variableBound f + 1) * (128*k + 160)` word transitions,
with logarithmic numeric payload bounds. This particular word-machine bound
uses a supplied endpoint table. The companion `cpap-approximation-hardness` package also
proves `Embed.planarEmbedding_linear_ram` on the formula alone and
`orientation_linear_ram` for computing endpoint bits from the resulting
rotation, with the stated RAM time and accessed-address bounds.

For the particular NP-hard ring family, `SourceWord.packed_linear_word_planar`
charges the dimension scan, sign-memory extraction, and graph construction,
requiring no supplied orientation table. It returns a planar graph within
`(variableBound input + 1) * (32*k + 28)` transitions with logarithmic numeric
payloads at every prefix. Its budget is the ring input's original clause count.

## Scope of the running-time results

The list implementation `globalReductionGraph` is not the timed algorithm.
The full-domain runtime concerns the deterministic `WordPipeline`, which charges
preprocessing, padding, and graph emission. The foundation's single-tape bounds concern
actual compiled programs and binary serialization. These are distinct claims.

Planar bounded SAT NP-completeness and compiled planar CPAP NP-hardness are
complete. `PlanarTargetHardness` supplies the latter with an actual computed
endpoint rule, exact decoded graph and budget, and a polynomial
single-tape bound. Computing a suitable orientation table for arbitrary planar
Definition 7 inputs is not part of the general supplied-table linear theorem.
