module

public import NPHardness.PlanarAssemblyComplete
public import NPHardness.PlanarGlobalPreparation

/-!
Full Definition 7 planar construction, with the original clause budget,
actual emitted graph, registered GraphOutput encoding, and checked linear
word-machine execution. The planar endpoint table is existentially selected.
Its computation is not included in the supplied-table transition bound, and
this theorem alone does not assert a uniform polynomial many-one reduction.
-/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT Complexity.Planar

/-- One concrete planar output and its machine/correctness certificates.
`flips` is a read-only table supplied to the graph-construction machine.
The record deliberately makes no running-time claim for choosing this table
or serializing `instructions` into a binary word. -/
structure PlanarWordOutput (k : Nat) (f : CNF) where
  flips : EndpointChoices
  graph : Graph
  instructions : CNF
  transitions : Nat
  wordBits : Nat
  execution : WordPipeline.Runs (WordPipeline.step flips k f.length) transitions
    (WordPipeline.initial f) (.done graph)
  transition_bound : transitions≤(variableBound f+1)*(128*k+160)
  word_bound : wordBits≤(variableBound f+1).log2+
    ((4*WordPipeline.linearCoefficient k+11)*(gadgetWidth k+1)).log2+2
  words_fit : ∀ u s, u≤transitions →
    WordPipeline.Runs (WordPipeline.step flips k f.length) u (WordPipeline.initial f) s →
      WordPipeline.WordsFit k wordBits s
  graph_output : GraphOutput instructions graph f.length
  planar : PlanarGraph graph
  correct : Satisfiable f ↔ HasAssignment graph k f.length

/-- The registered planar target language uses precisely this output graph
and the original clause-count budget. -/
theorem PlanarWordOutput.encoded_correct {k : Nat} {f : CNF} (h : PlanarWordOutput k f) :
    Satisfiable f ↔ PlanarCPAP k (encode h.instructions) := by
  rw [h.graph_output.planar_encode_iff]
  exact h.correct.trans (and_iff_right h.planar).symm

/-- Every planar Definition 7 formula has a planar, semantically correct
output obtained by the verified full-domain machine in linear word time,
when supplied with the existentially selected endpoint table. Repeated
literals and tautological clauses are handled by the charged preprocessing. -/
theorem planar_full_domain_supplied_table {k : Nat} (hk : 5≤k) {f : CNF}
    (hf : BoundedOccurrence f) (hp : PlanarGraph (incidenceGraph f)) :
    Nonempty (PlanarWordOutput k f) := by
  obtain ⟨p,hpbound,_hd,hplanar,hrun⟩ := WordPipeline.planar_prepared_execution hk hf hp
  obtain ⟨flips,hflips⟩ := PlanarAssembly.orientedFormulaGraph_planar_exists k hpbound hplanar
  obtain ⟨t,w,hr,ht,hw,hs,hfit⟩ := WordPipeline.prepared_execution_linear_words hk hf flips (hrun flips)
  have hg : PlanarGraph (orientedFormulaGraph flips k p).reverse :=
    (PlanarGluing.planarGraph_perm (List.reverse_perm _)).mpr hflips
  exact ⟨⟨flips,(orientedFormulaGraph flips k p).reverse,
    graphWithBudget (orientedFormulaGraph flips k p).reverse f.length,
    t,w,hr,ht,hw,hfit,orientedGraphWithBudget_output flips k p f.length,hg,hs⟩⟩

/-- Direct submission-facing statement of the output guarantees. The
existential table is visible in the machine being timed. -/
theorem planar_full_domain_graphOutput {k : Nat} (hk : 5≤k) {f : CNF}
    (hf : BoundedOccurrence f) (hp : PlanarGraph (incidenceGraph f)) :
    ∃ flips t g instructions,
      WordPipeline.Runs (WordPipeline.step flips k f.length) t (WordPipeline.initial f) (.done g) ∧
      t≤(variableBound f+1)*(128*k+160) ∧ GraphOutput instructions g f.length ∧
      PlanarGraph g ∧ (Satisfiable f ↔ HasAssignment g k f.length) ∧
      (Satisfiable f ↔ PlanarCPAP k (encode instructions)) := by
  obtain ⟨h⟩ := planar_full_domain_supplied_table hk hf hp
  exact ⟨h.flips,h.transitions,h.graph,h.instructions,h.execution,h.transition_bound,
    h.graph_output,h.planar,h.correct,h.encoded_correct⟩

end STACS2027
