# Planar (≤1,≤2)-SAT and the graph reductions

The compared theorems are:

```lean
theorem planarLeOneLeTwoSAT_np_complete : Complexity.NPComplete PlanarLeOneLeTwoSAT
theorem cpap_np_hard {k : Nat} (hk : 5 ≤ k) : Complexity.NPHard (CPAP k)
theorem planarCPAP_np_hard {k : Nat} (hk : 5 ≤ k) :
    Complexity.NPHard (PlanarCPAP k)
```

Internally the planar source language is `PlanarBoundedSATLanguage`, stated
with the decoder and Definition 7's occurrence bounds; `planarLeOneLeTwoSAT_eq`
proves it equal to the foundation-style `PlanarLeOneLeTwoSAT`. The source
reduction's outputs also have distinct variables in every clause
(`PlanarSource.Packed.output_distinct`), which gives `Paper.planarLeOneLeTwoCNF_np_hard`
for Planar-(≤1,≤2)-SAT exactly as defined.

The planar source is one decoded CNF satisfying Definition 7's signed
multiplicity and clause-length bounds, the foundation's incidence planarity, and
satisfiability. Its hardness is an explicit reduction, not an intersection
of separately hard restrictions. It quantifies over every language in the
foundation's machine-defined NP. No literature-hardness axiom is used.

## Polynomial time

`Complexity.PolyTime f` requires a finite single-tape machine and constants
`a,b` that halt on every binary `x` within `a * (x.length + 1)^b` local
instructions with the complete output word on the tape. There is no oracle
for SAT, embeddings, or arbitrary Lean evaluation. The foundation's finite
`ClauseProgram` compiler proves stack execution/register bounds and then
simulates them on that machine. Runtime is not inferred from output size.

## Completed planar source

1. Reuse the foundation's ANONYMIZED–ANONYMIZED and its two-stage occurrence-table/grid program.
   The grid is equisatisfiable, planar, and already has only two- or three-literal
   clauses. The foundation's `unitFree` is not used; its unit gadget is not planar.
2. Assign a variable to every literal occurrence. Copied source literals are
   negative. Signed implication rings in the source incidence order equate the
   decoded original values. Each copy has exactly one positive and one negative
   ring occurrence, and at most one negative copied-clause occurrence.
3. Replace each incidence edge by an explicit six-dart hypermap block. Exact
   node/face counts and component bounds prove planarity. Injective labels,
   edge flips, and a proved edge-list permutation identify the expansion with
   the actual generated CNF incidence graph, retaining all multiplicities.
4. Remove the spine of the foundation's grid by executable dart excision. Exact
   filtered cyclic-successor lemmas identify its retained rotation with the
   top-then-bottom order used by the emitter. No noncomputable choice implements
   the source reduction.
5. `PlanarSourcePacked*` implements this order with arithmetic block addresses
   and finite guarded local candidate lists. Source coverage, distinct indices,
   signs, pages, and exact successors are proved. Loops, dimension recovery,
   and full output writing are compiled by the foundation's compiler.
6. `PlanarSource.Packed.output_ringFormula` identifies the actual program's
   output. `output_correct` proves boundedness, incidence planarity, and SAT
   equivalence on all binary inputs, including empty grids. `output_polyTime`
   supplies its single-tape execution bound.
7. `PlanarBoundedMembership` supplies a compiled verifier checking parsing,
   occurrence-index caps, truth assignment, and the foundation's embedding
   certificate. Malformed inputs fail. The certificate bound is
   `704 * (input.length + 1)^2`.

`PlanarSourceHardness.lean` concludes unconditional planar bounded SAT hardness
and completeness. `PlanarSource.Packed.output_distinct` additionally proves
distinct clause variables: each used grid variable occurs at least twice,
so this particular source has no singleton implication rings.

## The unrestricted reduction and the target encoding

The unrestricted reduction starts from a clause program of the foundation's
(≤1,≤2)-SAT development (`inNP_twoThreeEmitter`) and appends the graph
emitter, whose allocation, direct ports and running time are proved.

For each fixed `k ≥ 5`, `graphEmitter_polyTime` times the full unrestricted
graph-and-budget constructor; `cpap_np_hard` proves its hardness. The binary
word uses the foundation's unary-prefix list encoding:

| Record | Interpretation |
|---|---|
| Empty record | Add one to the cost budget |
| Two positive numbers | Add the normalized undirected edge |
| Any other record | Reject |

The target reads the actual graph and budget, without reconstructing a source
formula. Repeated edges are interpreted by membership; each simple cycle edge
set is counted once. Sparse binary labels would be a different encoding.

## Scope

Planar bounded SAT and global planar gluing are complete. The full-domain word
theorem preserves the original budget and charges preprocessing when supplied
with compatible endpoint choices. `PlanarTargetHardness` also closes the uniform
planar CPAP machine reduction. Its sign-based endpoint rule is computed inside
the finite program. `graphOutput_spec` identifies the decoded graph and exact
bounded-source clause budget, `graphOutput_planar` proves that graph planar,
and `graphOutput_planar_iff` proves both correctness directions. Together with
`graphOutput_polyTime`, this yields `planarCPAP_np_hard`.

This concrete polynomial reduction does not time the selection of orientations
for arbitrary planar Definition 7 inputs. That broader operation is outside the
general supplied-table linear word bound in this package. The sibling
`cpap-approximation-hardness` proves the actual formula-only planar embedding
and compatible orientation RAM programs for bounded-occurrence planar formulas.

On the actual hard ring family, the separate theorem
`SourceWord.packed_linear_word_planar` does charge reconstructing sign memory
and orientations. Given the already constructed ring input, it returns a
planar correct graph in at most `(variableBound input + 1) * (32*k + 28)` word
transitions, with logarithmic numeric payload width at every prefix. It is a
specialized record/pointer machine, not a primitive-ISA or binary-serialization
bound; `docs/PLANAR-AND-LINEAR.md` gives the complete distinction.

The manuscript's reference to ANONYMIZED et al., *Partition into cliques
for cubic graphs: Planar case, complexity and approximation*, is not installed
as an axiom. The additional planar source reduction is proved in Lean using
the pinned foundation's machine, grid, compiler, and planarity definitions.

The optional generated `Challenge.lean` contains the whole definition closure
of the three statements; this temporary specification is omitted from the distribution. `definition_names` is empty, so Comparator compares every machine,
encoding, planarity and language definition; `docs/VERIFICATION.md` records
the run.
