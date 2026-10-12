module

public import ApproximationHardness.Composition
public import NPHardness.WordPipelineCorrect
public import NPHardness.OrientedGluing
public import NPHardness.AssignmentRelabel

/-!
# The instance map of the L-reduction is computed by the Section 5 word machine

Section 6's definition of an L-reduction asks that the instance map `f ↦ G` and the
solution map be polynomial-time computable. Section 5 formalizes a word machine
(`WordPipeline`) that, on any (≤1,≤2)-SAT input, builds the full-domain reduction graph
in `O(n)` transitions (`Paper.gadget_reduction_linear_time`). On the Definition 7 instances of
Theorem 11 that construction performs no preprocessing and no padding: its output is
`formulaGraph k f` itself (listed in reverse), the graph of the L-reduction of Section 6.
Hence the instance map of Theorem 11 is computed in `O(n)` transitions of that machine,
and the L-reduction holds for the computed graph.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-! ## Definition 7 formulas need no preprocessing -/

theorem distinctLiterals_of_nodup {c : Clause} (hc : c.Nodup) : distinctLiterals c = c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨hl, hls⟩ := List.nodup_cons.mp hc
    simp only [distinctLiterals, hl, ↓reduceIte, ih hls]

/-- A clause on distinct variables has distinct literals and is not tautological. -/
theorem clause_distinct_vars {c : Clause} (hc : (c.map Literal.var).Nodup) :
    c.Nodup ∧ tautological c = false := by
  have hinj : ∀ l ∈ c, ∀ r ∈ c, l.var = r.var → l = r := by
    intro l hl r hr hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    have h := (hc.getElem_inj (i := i) (j := j) (hi := by simpa using hi)
      (hj := by simpa using hj)).mp (by simpa using hv)
    subst h; rfl
  constructor
  · rw [List.nodup_iff_pairwise_ne] at hc ⊢
    rw [List.pairwise_map] at hc
    exact hc.imp (fun h he => h (congrArg Literal.var he))
  · apply Bool.eq_false_iff.mpr
    intro ht
    unfold tautological at ht
    obtain ⟨l, hl, hr⟩ := List.any_eq_true.mp ht
    obtain ⟨r, hr, hlr⟩ := List.any_eq_true.mp hr
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hlr
    have := hinj l hl r hr hlr.1
    subst this
    exact hlr.2 rfl

theorem normalizeClauses_leOneLeTwo {f : CNF} (hf : ClauseVariablesDistinct f) :
    normalizeClauses f = f := by
  unfold normalizeClauses removeTautologies
  induction f with
  | nil => rfl
  | cons c f ih =>
    have hc := clause_distinct_vars (hf c (by simp))
    have ht := ih (fun d hd => hf d (by simp [hd]))
    simp only [List.map_cons, List.filter_cons, distinctLiterals_of_nodup hc.1, hc.2,
      Bool.not_false, ↓reduceIte, ht]

theorem firstUnit_eq_none {f : CNF} (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3) :
    firstUnit f = none := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    have hc := hf c (by simp)
    have ht := ih (fun d hd => hf d (by simp [hd]))
    match c, hc with
    | [a, b], _ => simpa [firstUnit] using ht
    | [a, b, d], _ => simpa [firstUnit] using ht

theorem unitReduce_leOneLeTwo (fuel : Nat) {f : CNF} (hf : BoundedOccurrence f) :
    unitReduce fuel f = some f := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hempty : [] ∉ f := by
      intro h
      have := hf.1 [] h
      simp at this
    simp only [unitReduce, hempty, ↓reduceIte, firstUnit_eq_none hf.1]

/-- On a Definition 7 formula the preprocessing of the full-domain construction is the
identity. -/
theorem cleanFormula_leOneLeTwo {f : CNF} (hf : LeOneLeTwoCNF f) : cleanFormula f = some f := by
  unfold cleanFormula
  rw [normalizeClauses_leOneLeTwo hf.2]
  exact unitReduce_leOneLeTwo _ hf.1

/-- On a Definition 7 formula the full-domain reduction graph is the Theorem 8 graph. -/
theorem globalReductionGraph_leOneLeTwo (k : Nat) {f : CNF} (hf : LeOneLeTwoCNF f) :
    globalReductionGraph k f = formulaGraph k f := by
  unfold globalReductionGraph
  rw [cleanFormula_leOneLeTwo hf]
  simp [padFormula]

/-! ## The trivial orientation is the Theorem 8 graph -/

theorem orientedClauseVertex_trivial (width n j : Nat) (c : List PlacedLiteral) :
    orientedClauseVertex (fun _ => false) width n j c = clauseVertex width n j c := by
  funext v
  letI : Oriented.Orientation := ⟨fun _ => false⟩
  simp only [orientedClauseVertex, Oriented.clauseVertex, clauseVertex, Oriented.orientSide]
  split <;> simp_all

theorem orientedPlacedClauseGraph_trivial (k n j : Nat) (c : List PlacedLiteral) :
    orientedPlacedClauseGraph (fun _ => false) k n j c = placedClauseGraph k n j c := by
  letI : Oriented.Orientation := ⟨fun _ => false⟩
  unfold orientedPlacedClauseGraph Oriented.placedClauseGraph placedClauseGraph
  have h := orientedClauseVertex_trivial (gadgetWidth k) n j c
  unfold orientedClauseVertex at h
  have h' : Oriented.clauseVertex (gadgetWidth k) n j c = clauseVertex (gadgetWidth k) n j c := h
  rw [h']

theorem orientedFormulaGraph_trivial (k : Nat) (f : CNF) :
    orientedFormulaGraph (fun _ => false) k f = formulaGraph k f := by
  letI : Oriented.Orientation := ⟨fun _ => false⟩
  unfold orientedFormulaGraph Oriented.formulaGraph formulaGraph
  have hfun : (fun j c => Oriented.placedClauseGraph k (variableBound f) j c) =
      fun j c => placedClauseGraph k (variableBound f) j c := by
    funext j c
    have h := orientedPlacedClauseGraph_trivial k (variableBound f) j c
    unfold orientedPlacedClauseGraph at h
    exact h
  rw [hfun]

/-! ## The word machine computes the instance of Theorem 11 -/

/-- On a formula without unit or empty clauses, the unit-propagation kernel only empties its
queue. -/
theorem kernel_trivial {f : CNF} (hf : ∀ c ∈ f, 2 ≤ c.length)
    (adj : LinearPreprocessUnits.Incidences) (queue : List Nat) (hq : ∀ j ∈ queue, j < f.length) :
    LinearPreprocessUnits.Executes adj (queue.length + 1)
      (.running (LinearPreprocessInit.initialMemory f) queue)
      (.done (LinearPreprocessInit.initialMemory f)) := by
  induction queue with
  | nil =>
    apply LinearPreprocessUnits.Executes.next
    exact LinearPreprocessUnits.Executes.refl _
  | cons j queue ih =>
    apply LinearPreprocessUnits.Executes.next
    have hj := hq j (by simp)
    obtain ⟨c, hc⟩ : ∃ c, f[j]? = some c := ⟨f[j], List.getElem?_eq_getElem hj⟩
    have hlen := hf c (List.mem_of_getElem? hc)
    have hstep : LinearPreprocessUnits.step adj
        (.running (LinearPreprocessInit.initialMemory f) (j :: queue)) =
        .running (LinearPreprocessInit.initialMemory f) queue := by
      simp only [LinearPreprocessUnits.step, LinearPreprocessInit.initialMemory_eq, hc]
      match c, hlen with
      | _ :: _ :: _, _ => rfl
    rw [hstep]
    exact ih (fun j' hj' => hq j' (by simp [hj']))

/-- Theorem 11's instance map is computed by the Section 5 word machine: on every Definition 7
formula `f` with `n` variables, the machine of `Paper.gadget_reduction_linear_time` (with the trivial
endpoint table) reaches `(formulaGraph k f).reverse` in at most `(n + 1) · (128 k + 160)`
transitions. -/
theorem instance_map_linear_time {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) :
    ∃ t, WordPipeline.Runs (WordPipeline.step (fun _ => false) k f.length) t
        (WordPipeline.initial f) (.done (formulaGraph k f).reverse) ∧
      t ≤ (variableBound f + 1) * (128 * k + 160) := by
  have hb := hf.1
  let flips : EndpointChoices := fun _ => false
  let norm := normalizeClauses f
  have hnorm : norm = f := normalizeClauses_leOneLeTwo hf.2
  have hflit := hb.literal_count (variableBound f)
    (fun c hc l hl => literal_lt_variableBound hc hl)
  have hfcla := hb.clause_count_variableBound
  obtain ⟨tn, htn, hrn⟩ := WordPipeline.normalize_simulation flips k f.length
    (LinearPreprocessNormalize.executes_normalizeClauses f hb.isThreeCNF)
  obtain ⟨ti, hti, hri⟩ := WordPipeline.initialize_simulation flips k f.length
    (LinearPreprocessInit.executes_initialize norm)
  have hk2 : ∀ c ∈ norm, 2 ≤ c.length := by
    intro c hc
    rw [hnorm] at hc
    rcases hb.1 c hc with h | h <;> omega
  obtain ⟨tu, htu, hru⟩ := WordPipeline.units_simulation flips k f.length norm.length
    (LinearPreprocessInit.initialAdj norm)
    (kernel_trivial hk2 (LinearPreprocessInit.initialAdj norm) (List.range norm.length)
      (fun j hj => List.mem_range.mp hj))
  obtain ⟨te, hre, hte⟩ := LinearPreprocessExtract.extraction_linear norm.length
    (LinearPreprocessInit.initialMemory norm)
  obtain ⟨tx, htx, hrx⟩ := WordPipeline.extract_simulation flips k f.length
    (LinearPreprocessInit.initialMemory norm) hre
  have hg : LinearPreprocessUnits.contents norm.length (LinearPreprocessInit.initialMemory norm) = f := by
    rw [LinearPreprocessInit.contents_initialMemory, hnorm]
  obtain ⟨tp, hrp, htp⟩ := WordPipeline.finish_padding flips hk f.length
    (f.length - (LinearPreprocessUnits.contents norm.length (LinearPreprocessInit.initialMemory norm)).length)
    (LinearPreprocessUnits.contents norm.length (LinearPreprocessInit.initialMemory norm)) (hg ▸ hb)
  have hrun := hrn.trans (hri.trans (hru.trans (hrx.trans hrp)))
  rw [hg, Nat.sub_self] at hrun
  simp only [padFormula] at hrun
  refine ⟨tn + (ti + (tu + (tx + tp))), ?_, ?_⟩
  · rw [← orientedFormulaGraph_trivial k f]
    exact hrun
  · rw [hg, Nat.sub_self] at htp
    simp only [LinearPreprocessPadding.transitionCount, Nat.mul_zero, Nat.add_zero] at htp
    have hnl : norm.length = f.length := by rw [hnorm]
    have hnf : norm.flatten.length = f.flatten.length := by rw [hnorm]
    change tn ≤ f.length + norm.length + 2 at htn
    change ti ≤ norm.flatten.length + 3 * norm.length + 2 at hti
    simp only [List.length_range] at htu
    rw [hnl] at htn hti htu hte
    rw [hnf] at hti
    have hpad : tp ≤ f.flatten.length + 3 * f.length + 3 +
        (variableBound f + 1) * (WordConstructor.linearCoefficient k + 6) := htp
    have hcoef : WordPipeline.linearCoefficient k = 128 * k + 160 :=
      WordPipeline.linearCoefficient_eq k
    unfold WordPipeline.linearCoefficient at hcoef
    -- `t ≤ tn + ti + tu + tx + tp`, each term linear in `n`.
    have hwc : 4 * WordConstructor.linearCoefficient k + 100 = 128 * k + 160 := hcoef
    have h4wc : 4 * WordConstructor.linearCoefficient k = 128 * k + 60 := by omega
    have hprod : 4 * (variableBound f * WordConstructor.linearCoefficient k) =
        variableBound f * (128 * k) + 60 * variableBound f := by
      calc 4 * (variableBound f * WordConstructor.linearCoefficient k)
          = variableBound f * (4 * WordConstructor.linearCoefficient k) := by grind
        _ = variableBound f * (128 * k + 60) := by rw [h4wc]
        _ = variableBound f * (128 * k) + 60 * variableBound f := by grind
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul] at hpad ⊢
    omega

/-! ## The L-reduction for the computed graph -/

theorem IsMinCost.of_perm {g h : Graph} (hp : g.Perm h) {k C : Nat} (hC : IsMinCost h k C) :
    IsMinCost g k C :=
  ⟨(hasAssignment_graph_perm hp k C).mpr hC.1,
    fun B hB => hC.2 B ((hasAssignment_graph_perm hp k B).mp hB)⟩

/-- An L-reduction to `CPAP` is unchanged when the instance graphs are listed in another order. -/
theorem LReductionToCPAP.of_perm {Source : CNF → Prop} {F F' : CNF → Graph} {k αn αd βn βd : Nat}
    (hp : ∀ f, Source f → (F f).Perm (F' f)) (h : LReductionToCPAP Source F k αn αd βn βd) :
    LReductionToCPAP Source F' k αn αd βn βd := by
  intro f hf S C hS hC
  obtain ⟨h1, h2⟩ := h f hf S C hS (hC.of_perm (hp f hf))
  refine ⟨h1, ?_⟩
  intro ps hps
  have hA : HasAssignment (F f) k (cost ps) :=
    (hasAssignment_graph_perm (hp f hf) k (cost ps)).mpr ⟨ps, hps, Nat.le_refl _⟩
  obtain ⟨ps', hps', hc'⟩ := hA
  obtain ⟨a, ha⟩ := h2 ps' hps'
  exact ⟨a, Nat.le_trans ha (Nat.add_le_add_left (Nat.mul_le_mul_left βn hc') _)⟩

/-- **Theorem 11 with its instance map computed**: for every `k ≥ 5`, the map
`f ↦ (formulaGraph k f).reverse`, which the Section 5 word machine computes on every
Definition 7 formula in `O(n)` transitions, is an L-reduction from MAX-(≤1,≤2)-SAT to
`CPAP(G, k)` with `α = 5/3` and `β = 1`. -/
theorem cpap_lreduction_computed {k : Nat} (hk : 5 ≤ k) :
    LReductionToCPAP LeOneLeTwoCNF (fun f => (formulaGraph k f).reverse) k 5 3 1 1 ∧
    ∀ f, LeOneLeTwoCNF f → ∃ t,
      WordPipeline.Runs (WordPipeline.step (fun _ => false) k f.length) t
        (WordPipeline.initial f) (.done (formulaGraph k f).reverse) ∧
      t ≤ (variableBound f + 1) * (128 * k + 160) :=
  ⟨(cpap_lreduction hk).of_perm (fun _ _ => List.reverse_perm _ |>.symm),
    fun _ hf => instance_map_linear_time hk hf⟩

end STACS2027
