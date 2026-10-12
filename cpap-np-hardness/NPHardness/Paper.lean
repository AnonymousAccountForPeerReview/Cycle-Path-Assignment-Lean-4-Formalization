module

public import NPHardness.LocalResults
public import NPHardness.VariableExpansionCost
public import NPHardness.VariableDistances
public import NPHardness.ClauseWitnessInterface
public import NPHardness.GlobalCycles
public import NPHardness.GlobalPorts
public import NPHardness.GlobalSize
public import NPHardness.OrientedGluing
public import NPHardness.PlanarAssemblyComplete
public import NPHardness.PlanarGlobalReduction
public import NPHardness.WordPipelineCorrect
public import NPHardness.GluingObstruction
public import NPHardness.CPAPHardness
public import NPHardness.PlanarTargetHardness
public import NPHardness.PlanarSourceHardness
public import NPHardness.PlanarSourcePackedClean
public import NPHardness.PlanarOperationsGadgets
public import NPHardness.LinearPreprocessUnitWork

/-!
# Paper interface: Section 5 and Appendix C of the accompanying paper

This module restates the development in the manuscript's own terms. It adds no
construction. Each definition is either a verbatim transcription of a list
printed in Appendix C or a name for an object the proofs already use. Each
theorem is proved from the development.

Vertex numbering. In both clause gadgets, Lean vertex `v` is Appendix C vertex
`v + 1` (Steps 2 and 3 number vertices from 1). Subdivision vertices follow the
named vertices, in link order. The manuscript does not number the variable
gadget. Lean uses `0, ..., 6` for the corners of Figure 4(a): 0 top left,
1 top middle, 2 top right, 3 middle left, 4 middle, 5 bottom middle,
6 bottom right.

Endpoint identification. Definition 22 lets every edge identification order its
endpoints arbitrarily. `formulaGraph` uses one fixed order. `orientedFormulaGraph
flips` reverses the occurrences selected by `flips`. Correctness holds for every
choice, and planarity holds for a suitable choice. A fixed choice can destroy
planarity (`fixed_endpoints_K33`).
-/

set_option maxRecDepth 100000

@[expose] public section
namespace STACS2027.Paper
open Complexity Complexity.SAT

/-! ## Appendix C, Step 1: the variable gadget `γ_x` (Figure 4(a)) -/

/-- `e_(x,True,1)`, the blue edge of Figure 4(a). -/
def trueEdge : Edge := (2, 6)

/-- `e_(x,False,1)`, the red edge incident to `s_x`. -/
def falseEdge1 : Edge := (4, 5)

/-- `e_(x,False,2)`, the red edge of `C^α_x`. -/
def falseEdge2 : Edge := (0, 3)

/-- `s_x`, the edge shared by `C^α_x` and `C^β_x`. -/
def sharedEdge : Edge := (1, 4)

/-- `C^α_x` before subdivision: the left face of Figure 4(a). -/
def alphaCycle : Cycle := [0, 1, 4, 3]

/-- `C^β_x` before subdivision: the right face of Figure 4(a). -/
def betaCycle : Cycle := [1, 2, 6, 5, 4]

/-- The remaining simple cycle of the gadget: the outer face of Figure 4(a). -/
def outerCycle : Cycle := [0, 1, 2, 6, 5, 4, 3]

/-- The number of edges of the path that replaces skeleton edge `e` in
`variableGraph k`. The dashed gray edges of Figure 4(a) become such paths. -/
def variablePathLength (k : Nat) (e : Edge) : Nat :=
  (expandedEdge (linkSteps 7 (variableLinks k)) e).length

/-- The ports of `variableGraph` are `e_(x,True,1)`, `e_(x,False,1)`,
`e_(x,False,2)`, in this order. -/
theorem variablePorts_eq : variablePorts = [trueEdge, falseEdge1, falseEdge2] := rfl

theorem step1_skeleton_cycles :
    variableSkeletonInputs = [alphaCycle, betaCycle] ∧
      variableSkeletonCycles = [alphaCycle, betaCycle, outerCycle] := ⟨rfl, rfl⟩

/-- `C^α_x` traverses `e_(x,False,2)`; `C^β_x` traverses `e_(x,True,1)` and
`e_(x,False,1)`; both traverse `s_x`; and `e_(x,False,1)` is incident to
`s_x` (common endpoint 4) while `e_(x,False,2)` and `e_(x,True,1)` are not. -/
theorem step1_incidences :
    falseEdge2 ∈ cycleEdges alphaCycle ∧ sharedEdge ∈ cycleEdges alphaCycle ∧
    trueEdge ∈ cycleEdges betaCycle ∧ falseEdge1 ∈ cycleEdges betaCycle ∧
    sharedEdge ∈ cycleEdges betaCycle ∧
    trueEdge ∉ cycleEdges alphaCycle ∧ falseEdge1 ∉ cycleEdges alphaCycle ∧
    falseEdge2 ∉ cycleEdges betaCycle ∧
    falseEdge1.1 = sharedEdge.2 ∧
    falseEdge2.1 ≠ sharedEdge.1 ∧ falseEdge2.1 ≠ sharedEdge.2 ∧
    falseEdge2.2 ≠ sharedEdge.1 ∧ falseEdge2.2 ≠ sharedEdge.2 ∧
    trueEdge.1 ≠ sharedEdge.1 ∧ trueEdge.1 ≠ sharedEdge.2 ∧
    trueEdge.2 ≠ sharedEdge.1 ∧ trueEdge.2 ≠ sharedEdge.2 := by decide

/-- Step 1 subpath lengths. In `C^α_x`, skeleton edge (3,4) joins
`e_(x,False,2)` to the common endpoint 4 of `s_x` and `e_(x,False,1)`, and
(0,1) joins it to the opposite endpoint 1 of `s_x`. In `C^β_x`, (5,6) joins
`e_(x,False,1)` to `e_(x,True,1)`, and (1,2) joins `s_x` to `e_(x,True,1)`.
The three designated edges and `s_x` are not subdivided. -/
theorem step1_lengths {k : Nat} (hk : 5 ≤ k) :
    variablePathLength k (3, 4) = (k - 2) / 2 ∧ variablePathLength k (0, 1) = (k - 1) / 2 ∧
    variablePathLength k (5, 6) = (k - 2) / 2 ∧ variablePathLength k (1, 2) = (k - 3) / 2 ∧
    variablePathLength k trueEdge = 1 ∧ variablePathLength k falseEdge1 = 1 ∧
    variablePathLength k falseEdge2 = 1 ∧ variablePathLength k sharedEdge = 1 := by
  simp only [variablePathLength, trueEdge, falseEdge1, falseEdge2, sharedEdge]
  rw [variable_edge_expanded_length hk (3, 4) (by decide),
    variable_edge_expanded_length hk (0, 1) (by decide),
    variable_edge_expanded_length hk (5, 6) (by decide),
    variable_edge_expanded_length hk (1, 2) (by decide),
    variable_edge_expanded_length hk (2, 6) (by decide),
    variable_edge_expanded_length hk (4, 5) (by decide),
    variable_edge_expanded_length hk (0, 3) (by decide),
    variable_edge_expanded_length hk (1, 4) (by decide)]
  simp [variableWeight]

/-- Both `C^α_x` and `C^β_x` have length exactly `k`; the remaining simple
cycle has length `2k - 2`. -/
theorem step1_cycle_lengths {k : Nat} (hk : 5 ≤ k) :
    expandedLength (linkSteps 7 (variableLinks k)) alphaCycle = k ∧
    expandedLength (linkSteps 7 (variableLinks k)) betaCycle = k ∧
    expandedLength (linkSteps 7 (variableLinks k)) outerCycle = 2 * k - 2 :=
  ⟨variable_input_lengths hk alphaCycle (by decide),
    variable_input_lengths hk betaCycle (by decide), variable_outer_length hk⟩

/-- Every simple cycle of `γ_x` is the subdivision of `C^α_x`, `C^β_x`, or the
outer cycle, and its length is that subdivision's length. -/
theorem step1_cycles {k : Nat} {r : Nat} {c : Cycle}
    (hc : IsCycle (variableGraph k) r c) :
    ∃ d ∈ [alphaCycle, betaCycle, outerCycle],
      expandedLength (linkSteps 7 (variableLinks k)) d = r ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 7 (variableLinks k)))) := by
  obtain ⟨_, d, hd, hp⟩ := variable_cycle_projection hc
  obtain ⟨e, he, hec, hs⟩ := variableSkeleton_represents hd
  have hperm := hp.trans ((hs.edge_perm hd hec).flatMap_right
    (expandedEdge (linkSteps 7 (variableLinks k))))
  have hlen := hperm.length_eq
  simp only [hc.edge_length, List.length_flatMap] at hlen
  exact ⟨e, he, hlen.symm, hperm⟩

/-- The `k`-cycles of `γ_x` are exactly the subdivisions of `C^α_x` and `C^β_x`. -/
theorem step1_k_cycles {k : Nat} (hk : 5 ≤ k) :
    (∀ c, IsCycle (variableGraph k) k c → ∃ d ∈ [alphaCycle, betaCycle],
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 7 (variableLinks k))))) ∧
    (∀ d ∈ [alphaCycle, betaCycle], ∃ c, IsCycle (variableGraph k) k c ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 7 (variableLinks k))))) :=
  ⟨fun _ hc => variable_general_cycle_classification hk hc,
    fun d hd => variable_general_cycle_realization hk d hd⟩

/-- (o1.2), variable side: paths between endpoints of distinct designated edges
of `γ_x` have at least `⌊(k-2)/2⌋` edges. Port `p` is `variablePorts[p]`. -/
theorem observation_o1_2_variable {k p q : Nat} (hk : 5 ≤ k) (hp : p < 3) (hq : q < 3)
    (hne : p ≠ q) (a b : Bool) {vs : List Nat}
    (hpath : IsSimplePath (variableGraph k) (variableEndpoint p a) (variableEndpoint q b) vs) :
    (k - 2) / 2 ≤ (pathEdges vs).length :=
  variableGraph_port_distance hk hp hq hne a b hpath

/-- The two truth states of `γ_x`. Both use disjoint subpaths. "True" leaves
`e_(x,True,1)` unused and "False" leaves both `e_(x,False,j)` unused. -/
theorem step1_truth_states {k : Nat} (hk : 5 ≤ k) (t : Bool) :
    cost (variableExpandedState k hk t) = 0 ∧
    load (variableExpandedState k hk t) trueEdge = (if t then 0 else 1) ∧
    load (variableExpandedState k hk t) falseEdge1 = (if t then 1 else 0) ∧
    load (variableExpandedState k hk t) falseEdge2 = (if t then 1 else 0) := by
  obtain ⟨h1, h2, h3⟩ := variableExpandedState_loads hk t
  exact ⟨variableExpandedState_zero hk t, h1, h3, h2⟩

/-! ## Appendix C, Steps 2 and 3: the clause gadgets (Figure 4(b), (c)) -/

/-- Step 2, the `k = 5` edge set of `ζ_(c,3)`, verbatim and in printed order. -/
def step2Edges : List Edge :=
  [(1,2), (1,13), (1,14), (2,3), (3,4), (3,15), (4,5), (4,11), (5,6), (5,16),
   (6,7), (7,8), (7,17), (8,9), (9,10), (9,18), (10,11), (10,16), (11,12), (12,13), (12,15),
   (14,15), (16,17), (17,18)]

/-- Step 2: `e_(c,1)`, `e_(c,2)`, `e_(c,3)` (purple). -/
def step2LiteralEdges : List Edge := [(1,2), (5,6), (11,12)]

/-- Step 2: the edges subdivided `k - 5` times (dashed green). -/
def step2Green : List Edge := [(1,13), (2,3), (3,4), (6,7), (8,9), (9,10), (10,11)]

/-- Step 3: the edges added to a 3-literal clause gadget, verbatim and in printed order. -/
def step3Edges : List Edge :=
  [(11,19), (12,21), (19,20), (20,21), (20,23), (21,22), (21,24), (22,23), (22,24), (23,24)]

/-- Step 3: the edges subdivided `k - 5` times (dashed green). -/
def step3Green : List Edge := [(1,13), (2,3), (3,4), (6,7), (8,9), (9,10), (10,11), (19,20)]

/-- Step 3, dashed orange. -/
def step3Orange : List Edge := [(21,22), (21,24)]

/-- Step 3, dashed blue. -/
def step3Blue : List Edge := [(22,23), (23,24)]

/-- Step 3, dashed red. -/
def step3Red : List Edge := [(22,24)]

/-- Step 2: subdivide each green edge exactly `k - 5` times. -/
def step2Subdivisions (k : Nat) (e : Edge) : Nat :=
  if e ∈ step2Green then k - 5 else 0

/-- Step 3: green edges `k - 5` times. If `k = 6`, only the red edge, once.
Otherwise orange `⌊(k-5)/2⌋` and blue `⌈(k-5)/2⌉` times. -/
def step3Subdivisions (k : Nat) (e : Edge) : Nat :=
  if e ∈ step3Green then k - 5
  else if k = 6 then (if e ∈ step3Red then 1 else 0)
  else if e ∈ step3Orange then (k - 5) / 2
  else if e ∈ step3Blue then (k - 5 + 1) / 2
  else 0

/-- At `k = 5` the 3-literal gadget is Step 2's edge set, renumbered by `v ↦ v + 1`. -/
theorem step2_k5 : (clauseThreeGraph 5).map (fun e => (e.1 + 1, e.2 + 1)) = step2Edges := by
  decide

/-- At `k = 5` the 2-literal gadget is Step 2's edge set followed by Step 3's. -/
theorem step3_k5 :
    (clauseTwoGraph 5).map (fun e => (e.1 + 1, e.2 + 1)) = step2Edges ++ step3Edges := by
  decide

/-- For every `k`, the constructor of `ζ_(c,3)` is Step 2's list, in printed order,
with Step 2's subdivision counts, renumbered by `v ↦ v - 1`. -/
theorem step2_links (k : Nat) :
    clauseThreeLinks k = step2Edges.map fun e => ⟨e.1 - 1, e.2 - 1, step2Subdivisions k e⟩ := by
  simp [clauseThreeLinks, step2Edges, step2Subdivisions, step2Green]

/-- For every `k`, the constructor of `ζ_(c,2)` is Step 2's list followed by
Step 3's, in printed order, with Step 3's subdivision counts, renumbered by
`v ↦ v - 1`. -/
theorem step3_links (k : Nat) :
    clauseTwoLinks k = (step2Edges ++ step3Edges).map fun e =>
      ⟨e.1 - 1, e.2 - 1, step3Subdivisions k e⟩ := by
  have hblue : (k - 4) / 2 = (k - 5 + 1) / 2 := by omega
  simp [clauseTwoLinks, clauseThreeLinks, step2Edges, step3Edges, step3Subdivisions,
    step3Green, step3Orange, step3Blue, step3Red, orangeSubdivisions, blueSubdivisions,
    redSubdivisions, hblue]

/-- The literal edges `e_(c,1)`, `e_(c,2)`, `e_(c,3)`, renumbered by `v ↦ v - 1`. -/
theorem step2_literal_edges : clausePorts = step2LiteralEdges.map fun e => (e.1 - 1, e.2 - 1) := rfl

/-- Clause slot `i` is the literal edge `e_(c,i+1)`. -/
theorem clause_slot_edges :
    ∀ i : Fin 3, edge (clauseEndpoint i.val false) (clauseEndpoint i.val true) = clausePorts[i.val]! := by
  decide

/-- Observations three and four of the proof of Theorem 8, for every `k ≥ 5`.
The manuscript checks `k = 5` by brute force and covers larger `k` with
(o2.1), (o2.2), (o3.1) and (o3.2). `clauseFamily k hk c` lists each simple
`k`-cycle of the clause gadget once; a choice omits one vertex of each.
(i) Every simple `k`-cycle is listed. (ii) Every choice costs at least 1.
(iii) If every literal edge also carries load 1 from its variable gadget,
the cost is at least 2. (iv) For each literal, some choice of cost exactly 1
leaves every other literal edge unused. For a 2-literal clause, (iii) and (iv)
concern `e_(c,1)` and `e_(c,2)`; the auxiliary part supplies the load at
`e_(c,3)`. -/
theorem clause_gadget_observations {k : Nat} (hk : 5 ≤ k) (c : List PlacedLiteral)
    (hc : c.length = 2 ∨ c.length = 3) :
    (∀ d, IsCycle (clauseGraph k c) k d → ∃ e ∈ clauseFamily k hk c, SameCycle d e) ∧
    (∀ choose : Cycle → Nat, (∀ d ∈ clauseFamily k hk c, choose d ∈ d) →
      1 ≤ cost (chosenFamily (clauseFamily k hk c) choose)) ∧
    (∀ choose : Cycle → Nat, (∀ d ∈ clauseFamily k hk c, choose d ∈ d) →
      2 ≤ costWithPorts (chosenFamily (clauseFamily k hk c) choose) (activeClausePorts c)) ∧
    (∀ i, i < c.length → ∃ choose : Cycle → Nat, (∀ d ∈ clauseFamily k hk c, choose d ∈ d) ∧
      cost (chosenFamily (clauseFamily k hk c) choose) = 1 ∧
      ∀ j, j < c.length → j ≠ i → ∀ d ∈ clauseFamily k hk c,
        edge (clauseEndpoint j false) (clauseEndpoint j true) ∉ selectedAt d (choose d)) :=
  ⟨fun _ hd => clauseFamily_complete hk c hd,
    fun choose hv => clauseFamily_cost_positive hk c choose hv,
    fun choose hv => clauseFamily_blocked_lower hk c choose hv,
    fun i hi => clauseFamily_witness hk c hc i hi⟩

/-- The `k = 5` brute-force checks of observations three and four, and the
`k = 6` check of the 2-literal gadget: each gadget alone has optimum 1. -/
theorem clause_gadget_optima :
    (HasAssignment (clauseThreeGraph 5) 5 1 ∧ ¬ HasAssignment (clauseThreeGraph 5) 5 0) ∧
    (HasAssignment (clauseTwoGraph 5) 5 1 ∧ ¬ HasAssignment (clauseTwoGraph 5) 5 0) ∧
    (HasAssignment (clauseTwoGraph 6) 6 1 ∧ ¬ HasAssignment (clauseTwoGraph 6) 6 0) :=
  ⟨⟨clauseThree5_assignment_one, clauseThree5_no_assignment_zero⟩,
    ⟨clauseTwo5_assignment_one, clauseTwo5_no_assignment_zero⟩,
    ⟨clauseTwo6_assignment_one, clauseTwo6_no_assignment_zero⟩⟩

/-- All three gadgets are planar for every `k` (Theorem 8's proof sketch: "All gadgets are
planar"). -/
theorem gadgets_planar (k : Nat) :
    PlanarGraph (variableGraph k) ∧ PlanarGraph (clauseThreeGraph k) ∧
      PlanarGraph (clauseTwoGraph k) :=
  ⟨variableGraph_planar k, clauseThreeGraph_planar k, clauseTwoGraph_planar k⟩

/-! ## Appendix C, Step 4: edge identifications -/

/-- Variable ports: 0 is `e_(x,True,1)`, 1 is `e_(x,False,1)`, 2 is `e_(x,False,2)`. -/
theorem step4_port_edges :
    variablePortEdge 0 = trueEdge ∧ variablePortEdge 1 = falseEdge1 ∧
      variablePortEdge 2 = falseEdge2 := by decide

/-- Step 4, variable side. Literals are processed in formula order, and
`earlier` counts the earlier occurrences of the same literal. A positive
literal uses `e_(x,True,1)`. A negative literal uses `e_(x,False,j)`, where
`j - 1` earlier negative occurrences have already used `e_(x,False,1)`, ...,
`e_(x,False,j-1)`. This is the smallest unused index. -/
theorem step4_variable_port (past : List Literal) (l : Literal) :
    (PlacedLiteral.mk l (past.count l)).port = if l.positive then 0 else past.count l + 1 := rfl

/-- Step 4, the identification itself. The literal edge of slot `i` of a
placed clause gadget and the allocated port edge of the literal's variable
gadget are the same edge of the global graph. -/
theorem step4_identification {width n j : Nat} {c : List PlacedLiteral} {i : Nat}
    (hi : i < 3) {p : PlacedLiteral} (hp : c[i]? = some p) :
    mapEdge (clauseVertex width n j c) (edge (clauseEndpoint i false) (clauseEndpoint i true)) =
      mapEdge (blockVertex width p.literal.var) (variablePortEdge p.port) :=
  mapped_attachment_edge hi hp

/-! ## Definitions 1 and 7 and Planar-(≤1,≤2)-SAT -/

/-- The decision predicate minimizes `∑_e binom(l(e), 2)` (Definition 1). -/
theorem cpap_objective {g : Graph} {k budget : Nat} (hg : g.Nodup) :
    HasAssignment g k budget ↔
      ∃ ps : List (List Edge), ValidChoices ((cycles g k).map selectedOptions) ps ∧
        (g.map fun e => load ps e * (load ps e - 1) / 2).sum ≤ budget :=
  hasAssignment_iff_load_cost hg

/-- Definition 7. Each clause has 2 or 3 literals on distinct variables. Each
variable occurs at most once positively and at most twice negatively. -/
def LeOneLeTwoCNF (f : CNF) : Prop := BoundedOccurrence f ∧ ClauseVariablesDistinct f

/-- Planar-(≤1,≤2)-SAT: Definition 7 with a planar variable–clause incidence graph. -/
def PlanarLeOneLeTwoCNF (f : CNF) : Prop := LeOneLeTwoCNF f ∧ PlanarGraph (incidenceGraph f)

/-- Definition 7 is the registered `(≤1,≤2)`-CNF predicate plus distinct
variables in each clause. -/
theorem leOneLeTwoCNF_iff_registered (f : CNF) :
    LeOneLeTwoCNF f ↔ IsLeOneLeTwoCNF f ∧ ClauseVariablesDistinct f := by
  rw [LeOneLeTwoCNF, boundedOccurrence_iff_registered]

/-- The decision language of Planar-(≤1,≤2)-SAT, on binary words. -/
def PlanarLeOneLeTwoLanguage (input : SAT.Word) : Prop :=
  ∃ f, decode input = some f ∧ PlanarLeOneLeTwoCNF f ∧ Satisfiable f

theorem planarLeOneLeTwoLanguage_encode_iff (f : CNF) :
    PlanarLeOneLeTwoLanguage (encode f) ↔ PlanarLeOneLeTwoCNF f ∧ Satisfiable f := by
  simp [PlanarLeOneLeTwoLanguage]

/-- Planar-(≤1,≤2)-SAT is NP-hard exactly as stated, including distinct variables
in each clause. The manuscript cites this; here it is proved, by the same
reduction as `planarBoundedSAT_np_hard`. -/
theorem planarLeOneLeTwoCNF_np_hard : NPHard PlanarLeOneLeTwoLanguage := by
  intro L hL
  obtain ⟨P, hP⟩ := CookLevinEmitter.inNP_emitter hL
  refine ⟨fun x => encode (PlanarSource.Packed.output P x),
    PlanarSource.Packed.output_polyTime P, ?_⟩
  intro x
  rw [hP x, SAT_encode_iff, planarLeOneLeTwoLanguage_encode_iff]
  have h := PlanarSource.Packed.output_correct P x
  have hd := PlanarSource.Packed.output_distinct P x
  exact ⟨fun hs => ⟨⟨⟨h.1, hd⟩, h.2.1⟩, h.2.2.mpr hs⟩, fun hs => h.2.2.mp hs.2⟩

/-! ## Theorem 8 -/

/-- Theorem 8, correctness, with endpoints identified in a fixed order. -/
theorem gadget_reduction {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) :
    Satisfiable f ↔ HasAssignment (formulaGraph k f) k f.length :=
  formulaGraph_sat_iff_assignment hk hf.1 hf.2

/-- Theorem 8, correctness, for every endpoint identification permitted by
Definition 22. -/
theorem gadget_reduction_any_endpoints (flips : EndpointChoices) {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : LeOneLeTwoCNF f) :
    Satisfiable f ↔ HasAssignment (orientedFormulaGraph flips k f) k f.length :=
  orientedFormulaGraph_sat_iff_assignment flips hk hf.1 hf.2

/-- Theorem 8, both sentences, for one graph. If the incidence graph is planar,
some endpoint identification yields a planar graph, and that graph is correct. -/
theorem gadget_reduction_planar {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f)
    (hp : PlanarGraph (incidenceGraph f)) :
    ∃ flips : EndpointChoices, PlanarGraph (orientedFormulaGraph flips k f) ∧
      (Satisfiable f ↔ HasAssignment (orientedFormulaGraph flips k f) k f.length) := by
  obtain ⟨flips, h⟩ := PlanarAssembly.orientedFormulaGraph_planar_exists k hf.1 hp
  exact ⟨flips, h, orientedFormulaGraph_sat_iff_assignment flips hk hf.1 hf.2⟩

/-- Theorem 8 without the distinct-variable clause of Definition 7. Repeated
literals and tautologies are removed first, and the budget stays `m`. -/
theorem gadget_reduction_full_domain {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f) :
    Satisfiable f ↔ HasAssignment (globalReductionGraph k f) k f.length :=
  globalReduction_sat_iff_assignment hk hf

/-- Theorem 8 without the distinct-variable clause, for every endpoint identification. -/
theorem gadget_reduction_full_domain_any_endpoints (flips : EndpointChoices) {k : Nat} (hk : 5 ≤ k)
    {f : CNF} (hf : BoundedOccurrence f) :
    Satisfiable f ↔ HasAssignment (orientedGlobalReductionGraph flips k f) k f.length :=
  orientedGlobalReduction_sat_iff_assignment flips hk hf

/-- The size bound for the full-domain construction, which includes the
preprocessing and padding. -/
theorem gadget_reduction_full_domain_size {k : Nat} (hk : 5 ≤ k) (f : CNF) :
    (globalReductionGraph k f).length ≤
      (variableBound f + 2 * (f.length + 1)) * (2 * k) + (f.length + 1) * (10 * k) :=
  globalReductionGraph_edge_bound hk f

/-- Theorem 8, size: the graph has `O(n)` edges for fixed `k`, where the
variables are `0, ..., n - 1` (`n = variableBound f`). -/
theorem gadget_reduction_size {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f) :
    (formulaGraph k f).length ≤ 17 * k * variableBound f := by
  have h1 := formulaGraph_edge_bound hk f
  have h2 := hf.clause_count_variableBound
  have h3 : 2 * f.length * (5 * k) ≤ 3 * variableBound f * (5 * k) := Nat.mul_le_mul_right _ h2
  have e1 : f.length * (10 * k) = 2 * f.length * (5 * k) := by
    rw [show 10 * k = 2 * (5 * k) by omega, ← Nat.mul_assoc, Nat.mul_comm f.length 2]
  have e2 : 3 * variableBound f * (5 * k) = 15 * (k * variableBound f) := by
    rw [Nat.mul_mul_mul_comm, Nat.mul_comm (variableBound f) k]
  have e3 : variableBound f * (2 * k) = 2 * (k * variableBound f) := by
    rw [Nat.mul_comm 2 k, ← Nat.mul_assoc, Nat.mul_comm (variableBound f) k, Nat.mul_comm _ 2]
  have e4 : 17 * k * variableBound f = 17 * (k * variableBound f) := Nat.mul_assoc _ _ _
  omega

/-- Theorem 8, time: for every endpoint table, the full-domain construction runs
in `O(n)` transitions of the verified word machine. -/
theorem gadget_reduction_linear_time (flips : EndpointChoices) {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) :
    ∃ t out, WordPipeline.Runs (WordPipeline.step flips k f.length) t
        (WordPipeline.initial f) (.done out) ∧
      t ≤ (variableBound f + 1) * WordPipeline.linearCoefficient k ∧
      (Satisfiable f ↔ HasAssignment out k f.length) :=
  WordPipeline.full_domain_linear flips hk hf

/-- Theorem 8, time: each transition of the word machine is a constant amount of work. In
the unit-propagation phase of the run on a Definition 7 input, a step visits at most three
incidence entries and inspects at most eighteen literals, and the queue never holds more than
`5m` entries. -/
theorem gadget_reduction_unit_steps_bounded {f : CNF} (hf : BoundedOccurrence f) {t : Nat}
    {mem : LinearPreprocessUnits.Memory} {queue : List Nat}
    (h : LinearPreprocessUnits.Executes (LinearPreprocessInit.initialAdj (normalizeClauses f)) t
      (.running (LinearPreprocessInit.initialMemory (normalizeClauses f))
        (List.range (normalizeClauses f).length)) (.running mem queue)) :
    (∀ l : Literal, (LinearPreprocessInit.initialAdj (normalizeClauses f) l.var).length ≤ 3 ∧
      LinearPreprocessUnitWork.literalInspectionBound l
        (LinearPreprocessInit.initialAdj (normalizeClauses f) l.var) mem queue ≤ 18) ∧
    queue.length ≤ 5 * f.length := by
  obtain ⟨hv, ha⟩ := LinearPreprocessInit.normalized_initial_valid hf
  exact ⟨fun l => LinearPreprocessUnitWork.reachable_unit_work ha h hv l,
    LinearPreprocessUnitWork.normalized_reachable_queue hf h⟩

/-- Theorem 8, planar and full-domain: a planar, correct output, computed in
`O(n)` word-machine transitions from a supplied endpoint table, and its
encoding in the registered planar CPAP language. -/
theorem gadget_reduction_planar_linear_time {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hp : PlanarGraph (incidenceGraph f)) :
    ∃ flips t g instructions,
      WordPipeline.Runs (WordPipeline.step flips k f.length) t (WordPipeline.initial f) (.done g) ∧
      t ≤ (variableBound f + 1) * (128 * k + 160) ∧ GraphOutput instructions g f.length ∧
      PlanarGraph g ∧ (Satisfiable f ↔ HasAssignment g k f.length) ∧
      (Satisfiable f ↔ PlanarCPAP k (encode instructions)) :=
  planar_full_domain_graphOutput hk hf hp

/-- (o1): every `k`-cycle of the glued graph lies in a single gadget, and each
gadget's `k`-cycles survive gluing. -/
theorem observation_o1 {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) (c : Cycle) :
    IsCycle (formulaGraph k f) k c ↔
      (∃ v, v < variableBound f ∧ IsCycle (placedVariableGraph k v) k c) ∨
      (∃ j : Fin (placeFormula [] f).length,
        IsCycle (placedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]) k c) :=
  formulaGraph_cycle_local_iff hk hf.1 hf.2 c

/-- (o1) for every endpoint identification. -/
theorem observation_o1_any_endpoints (flips : EndpointChoices) {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : LeOneLeTwoCNF f) {c : Cycle} (hc : IsCycle (orientedFormulaGraph flips k f) k c) :
    (∃ v, v < variableBound f ∧ IsCycle (placedVariableGraph k v) k c) ∨
    (∃ j : Fin (placeFormula [] f).length,
      IsCycle (orientedPlacedClauseGraph flips k (variableBound f) j.val
        (placeFormula [] f)[j.val]) k c) :=
  orientedFormulaGraph_cycle_local flips hk hf.1 hf.2 hc

/-- Definition 22 needs a consistent endpoint choice for planarity. A
Planar-(≤1,≤2)-SAT formula, glued in the fixed order, contains a subdivision of
`K_{3,3}`. Another endpoint choice for the same formula is planar. -/
theorem fixed_endpoints_K33 :
    PlanarLeOneLeTwoCNF gluingObstructionFormula ∧
      Nonempty (K33Subdivision (formulaGraph 5 gluingObstructionFormula)) ∧
      PlanarGraph (orientedFormulaGraph gluingRepairFlips 5 gluingObstructionFormula) :=
  ⟨⟨⟨gluingObstruction_bounded, gluingObstruction_distinct⟩, gluingObstruction_incidence_planar⟩,
    fixed_gluing_contains_K33_subdivision, gluingRepair_planar⟩

/-! ## Theorem 6 -/

/-- Theorem 6: for every fixed `k ≥ 5`, CPAP is NP-hard on planar graphs. -/
theorem planar_np_hard {k : Nat} (hk : 5 ≤ k) : NPHard (PlanarCPAP k) :=
  planarCPAP_np_hard hk

/-- Theorem 6, last sentence: CPAP is NP-hard on general graphs. -/
theorem general_np_hard {k : Nat} (hk : 5 ≤ k) : NPHard (CPAP k) :=
  cpap_np_hard hk

/-- The source problem of Theorem 6 without the distinct-variable clause is
NP-complete. This is the language presentation of planar `(≤1,≤2)`-SAT. -/
theorem planar_source_np_complete : NPComplete PlanarBoundedSATLanguage :=
  planarBoundedSAT_np_complete

end STACS2027.Paper
