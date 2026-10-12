# Planarity and the word-machine construction

This note describes the planarity proof and the word-machine construction.
Every planarity statement uses the unchanged the foundation's
`Complexity.PlanarGraph`, whose witnesses are finite oriented hypermaps with
genus zero. The foundation's development does not prove equivalence with plane
drawings. No separate drawing predicate or assumed equivalence is used here.

## Checked geometry

`RegisteredGadgetEmbeddings` supplies concrete `EmbedTables` for the three
skeletons. Kernel `decide` verifies the tables and explicit face walks through
the ports. The tables include the actual listed edges.

`PlanarOperations` proves plain subdivision, including loops, parallel edges,
and disconnected inputs. `PlanarOperationsPrograms` connects that operation to
`subdivideOnce`, chains, and the gadget link programs. Consequently
`variableGraph_planar`, `clauseThreeGraph_planar`, and `clauseTwoGraph_planar`
hold for every natural `k`. The CPAP correctness theorems separately require
`k ≥ 5`.

`PlanarSphericalGadgets` gives each gadget, for every `k`, a spherical
embedding whose attachment edges lie on one face. `HasCofacialPorts` contains
a full the foundation's embedding and actual face-iteration witnesses for each port;
equality of arbitrary face labels is not substituted for face connectivity.
`PlanarGluingReflection` mirrors an embedding without changing its edge list,
so each gadget can be used with either cyclic order of its ports.

`PlanarGluingTransport`, `PlanarGluingLists`, and `PlanarGluingOrientation`
prove transport through dart equivalences, edge-list permutations, independent
edge endpoint reversals, and canonical undirected-edge normalization.
`PlanarGluingCycles` places permutations on disjoint dart intervals and counts
their cycles. `PlanarAssemblyEuler` proves the exact global Euler accounting
for ordered port gluing. `PlanarAssemblyQuotient` identifies the actual
endpoint quotient with `orientedFormulaGraph`, including both copies of each
attachment edge. `PlanarAssemblyInactivePieces` discharges unused-component
accounting from the actual disjoint gadget blocks and incidence endpoints.
`PlanarAssemblyComplete` closes global assembly with
`PlanarAssembly.orientedFormulaGraph_planar_exists`: every bounded formula
with planar incidence has choices making the actual oriented graph planar.
Source cyclic orders select spherical pieces, and the endpoint quotient
retains duplicate attachment-edge entries.

The `PlanarSourceEmbedding*` and `PlanarSourceComponents` modules replace each
variable rotation by an implication ring. Their explicit six-dart replacement
per original incidence edge satisfies the hypermap law, the node/face count
identities, and the component bound. `BipartiteRotation.expanded_planar` proves
planarity of this actual expansion from planarity of the original hypermap.
`PlanarSourceFormulaGraph` proves the exact correspondence with the generated
CNF, using injective vertex names, reversal of one edge per block, and a proved
edge-list permutation. `PlanarSourceComputableDelete` supplies an executable source embedding by
restricting the foundation's comb embedding. `PlanarSourcePackedReduction`
proves polynomial execution of a closed finite program. `PackedAddresses`,
`RotationTablePartition`, and `PackedSound` connect actual clause/literal
addresses and descriptor metadata to the grid. `PackedRingCorrect`, `PackedOutput`, and `PackedCorrect` complete the exact
identification of those finite successor tables with the executable embedding.
`PlanarSourceHardness` proves unconditional planar bounded SAT hardness and
NP-completeness using the verifier in `PlanarBoundedMembership`.

## Why endpoint choices matter

The original fixed endpoint convention does not preserve arbitrary planar
incidence embeddings. `GluingObstruction` records a concrete Definition 7
formula, a checked planar incidence embedding, and nine explicit paths forming
a subdivision of `K₃,₃` inside its fixed-orientation output. The paths have the
proved endpoints and pairwise disjoint interiors. This is a checked subdivision
certificate; this project does not additionally prove a Kuratowski theorem
or infer a Lean negation of `PlanarGraph` from it.

The same module supplies a checked the foundation's embedding for the repaired
orientation, including duplicate attachment edges. The general semantic
repair is `orientedGlobalReduction_sat_iff_assignment`: every choice of endpoint
bits preserves SAT/CPAP correctness on the full Definition 7 domain, with the
original clause count as budget. The global assembly uses each source node's actual cyclic order. Local
embeddings can be reflected to match that order; their selected dart sides
determine the endpoint bits. An existential choice of such embeddings is not
a running-time proof for computing the bits.

## Checked runtime

`WordPipeline.full_domain_linear` states, for `BoundedOccurrence f`, `5 ≤ k`,
and any supplied orientation table `flips`, that there are `t` and `out` with:

```lean
Runs (step flips k f.length) t (initial f) (.done out)
t ≤ (variableBound f + 1) * (128 * k + 160)
Satisfiable f ↔ HasAssignment out k f.length
```

The actual theorem uses `linearCoefficient k`; `linearCoefficient_eq` proves
the displayed coefficient. It requires no distinct-variable hypothesis, no
supplied incidence table, and no semantic preprocessing certificate.

The deterministic transition function charges all stages: bounded-clause
normalization, construction of clause cells and adjacency lists, indexed unit
propagation, extraction, fresh satisfiable padding, a dimension scan, and
emission of each graph edge. The contradiction branch emits a graph whose
minimum assignment cost exceeds the original budget. The successful branch
uses fresh satisfiable clauses to restore that budget.

Input lists are immutable linked records; random-access cells initially contain
zero or an inactive tag. The original clause count is an input header. The
postprocessing variable bound is computed by a charged scan. The three gadget
tables for fixed `k` and the orientation-bit table are read-only input data.
The graph stage reads the orientation table; it does not evaluate an arbitrary
Lean function at unit cost. The list-valued state fields denote record pointers.

Each transition is a specified local-word macro. In particular,
`LinearPreprocessUnitWork.reachable_unit_work` (restated as
`Paper.gadget_reduction_unit_steps_bounded`) proves that each reachable unit
step visits at most three incidence cells and inspects at most eighteen
literals; the recursive update is not an unbounded operation charged as one
step. The bounded normalization decision trees inspect at most three literals.
The proof counts transitions in this specialized machine. There is no compiler
from this machine to a primitive RAM instruction set or a concrete heap-pointer
encoding in this repository.

`WordPipeline.full_domain_linear_words` additionally proves one payload width
valid at every prefix of the complete execution. It covers all live memory and
adjacency addresses, queue IDs, literal values, phase registers, local gadget
labels, graph counters, and output endpoints. For `n = variableBound f`, its
bound is

```text
log₂(n+1) + log₂((4*(128*k+160)+11)*(gadgetWidth k+1)) + 2.
```

This is logarithmic in `n+1` for fixed `k`. The numeric envelope proof starts
at `n + f.length + 1` and increases by at most two per transition. Record
pointers remain abstract cell references; this payload theorem does not
silently supply a concrete pointer encoding or a primitive-ISA compiler.

Here `n` is the bound on variable labels (`variableBound f`), not the number of
distinct labels in an arbitrary sparse encoding. For inputs indexed below `n`,
Definition 7 yields at most `3n` literal occurrences and `2m ≤ 3n`. This is the
parameter used in the word bound.

## Computed orientations on the NP-hard source family

`SourceWord.packed_linear_word_planar` in `SourceWordPlanarSafety.lean`
applies to the actual `PlanarSource.Packed.output P x` used by the hardness
reduction. This machine receives no orientation table or geometric certificate.
Its only numeric input header is the formula's clause count. A charged literal
scan computes the variable bound; it skips the copied-clause prefix and scans
the implication suffix, writing each original sign to a Boolean RAM cell.
The graph phase reads that cell and compares signs for each endpoint choice.

For `input = PlanarSource.Packed.output P x` and `n = variableBound input`, the
returned graph is planar and assignment feasibility at budget `input.length`
equals satisfiability of the original emitter formula. The full run, including
dimension and sign-memory reconstruction, obeys

```text
t ≤ (n+1) * (32*k+28)
w ≤ log₂(n+1) + log₂((4*(32*k+28)+11)*(gadgetWidth k+1)) + 2.
```

`WordsFit` holds with this one width at every prefix. It covers stored literals,
sign-memory write addresses, scalar registers, occurrence counters, and output
endpoints. No arbitrary evaluation of `sourceSigns` costs a single operation:
the charged scan proves the actual memory equals that specification.

This is a record/pointer word machine with zero-initial RAM and fixed-`k`
read-only gadget tables. Linked-record pointers remain abstract references;
there is no primitive-ISA compiler or concrete heap-address encoding. The
linear bound starts with the already constructed bounded ring formula. The
separate single-tape reduction also charges creating that source and writing
the full binary output, with a polynomial bound.

## Preprocessing and executable source details

`PlanarPreprocessDeletionClosure` proves edge-sublist closure by actual dart
excision, then derives planarity of clause normalization, queue-based unit
propagation, and fresh padding. No unproved graph-minor closure is assumed.
`PlanarGlobalPreparation` fixes the prepared formula independently of the
orientation table and relates it to the actual word-machine run.

`PlanarSourceClean` proves that every variable used in the foundation's grid has
at least two occurrences. Orbit-correct occurrence rings consequently have
no fixed points, and their clauses have distinct variables. Thus this specific
source reduction needs no tautology or unit-clause preprocessing.
`PlanarSourcePlacement` identifies its exact allocated ports: copied negative
literals are first occurrences, and each implication literal uses its unique
positive port or its second negative port.

## Full-domain integration

`planar_full_domain_supplied_table` in `PlanarGlobalReduction.lean` combines
global assembly, actual planar preprocessing, and the full word-machine run.
Its `PlanarWordOutput` record contains the endpoint table, emitted graph,
instruction encoding, original budget, planarity, semantic equivalence,
transition bound, and payload bounds at every execution prefix. The companion
`planar_full_domain_graphOutput` states the guarantees directly.

This is a planar construction theorem with supplied orientation data. It does not charge finding that table, and its logical graph-record
packaging is not a charged binary serializer. The separate concrete planar
CPAP reduction is complete in `PlanarTargetHardness`: its finite program
computes a sign-based endpoint rule and writes the actual graph-and-budget
encoding in polynomial single-tape time. `graphOutput_planar` identifies its
decoded graph with the checked signed-ring assembly; `planarCPAP_np_hard`
has no orientation, embedding, or source-hardness premise.

The foundation's `unitFree` transformation must not be used as a planar step:
its unit replacement can introduce a `K₃,₄` incidence graph. The compiled
planar source uses the already unit-free the foundation's grid.

Polynomial single-tape complexity and linear word-machine complexity are
different claims. `graphEmitter_polyTime` proves the former for the existing
unrestricted reduction; `PlanarSource.Packed.graphOutput_polyTime` proves it
for the new planar reduction, including its actual endpoint rule. Neither is
a conversion of the general linear word bound into a bit-machine bound.
