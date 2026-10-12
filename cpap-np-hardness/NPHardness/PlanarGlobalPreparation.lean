module

public import NPHardness.WordPipelineSafety
public import NPHardness.PlanarPreprocessDeletionClosure

/-!
The actual full-domain word machine reaches a fixed prepared planar-incidence
formula before emitting any orientation-dependent graph. The prepared formula
is independent of the supplied orientation table. This makes existential
planar orientation selection compatible with the separately checked runtime
for reading that table; it does not charge or implement its selection.
-/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT Complexity.Planar

namespace WordPipeline

theorem Runs.fixed_start {S : Type} {step : S→S} {t : Nat} {s r : S}
    (h : Runs step t s r) (hs : step s=s) : s=r := by
  induction h with
  | refl => rfl
  | @next t s r h ih => exact hs.symm.trans (ih (congrArg step hs))

theorem Runs.terminal_unique {S : Type} {step : S→S} {t u : Nat} {s q r : S}
    (h : Runs step t s q) (g : Runs step u s r) (hq : step q=q) (hr : step r=r) : q=r := by
  induction h generalizing u r with
  | refl => exact g.fixed_start hq
  | @next t s q h ih =>
    cases g with
    | refl =>
      rw [hr] at h
      exact (h.fixed_start hr).symm
    | next g => exact ih g hq hr

theorem reaches_units (flips : EndpointChoices) (k : Nat) {f : CNF}
    (hf : BoundedOccurrence f) {t : Nat} {result : LinearPreprocessUnits.State}
    (h : LinearPreprocessUnits.Executes (LinearPreprocessInit.initialAdj (normalizeClauses f)) t
      (.running (LinearPreprocessInit.initialMemory (normalizeClauses f))
        (List.range (normalizeClauses f).length)) result) :
    ∃ u, Runs (step flips k f.length) u (initial f)
      (unitsState f.length (normalizeClauses f).length
        (LinearPreprocessInit.initialAdj (normalizeClauses f)) result) := by
  obtain ⟨tn,_,hn⟩ := normalize_simulation flips k f.length
    (LinearPreprocessNormalize.executes_normalizeClauses f hf.isThreeCNF)
  obtain ⟨ti,_,hi⟩ := initialize_simulation flips k f.length
    (LinearPreprocessInit.executes_initialize (normalizeClauses f))
  obtain ⟨tu,_,hu⟩ := units_simulation flips k f.length (normalizeClauses f).length
    (LinearPreprocessInit.initialAdj (normalizeClauses f)) h
  exact ⟨tn+(ti+tu),hn.trans (hi.trans hu)⟩

/-- Preprocessing and original-budget padding preserve planar incidence on
all Definition 7 inputs. The resulting formula is fixed before choosing any
endpoint orientations. Every supplied table emits the corresponding graph. -/
theorem planar_prepared_execution {k : Nat} (hk : 5≤k) {f : CNF}
    (hf : BoundedOccurrence f) (hp : PlanarGraph (incidenceGraph f)) :
    ∃ p : CNF, BoundedOccurrence p ∧ ClauseVariablesDistinct p ∧
      PlanarGraph (incidenceGraph p) ∧
      ∀ flips : EndpointChoices, ∃ t, Runs (step flips k f.length) t (initial f)
        (.done (orientedFormulaGraph flips k p).reverse) := by
  obtain ⟨tk,result,_,hr,hs⟩ := LinearPreprocessResult.normalized_kernel_correct hf
  cases result with
  | running mem queue => exact False.elim hs
  | rejected =>
    refine ⟨padFormula (f.length+1) [],padFormula_bounded _ emptyFormula_bounded,
      padFormula_distinct _ emptyFormula_distinct,
      PlanarPreprocess.contradiction_padded_planar f.length,?_⟩
    intro flips
    obtain ⟨tu,hu⟩ := reaches_units flips k hf hr
    obtain ⟨tp,hp,_⟩ := finish_padding flips hk f.length (f.length+1) [] emptyFormula_bounded
    exact ⟨tu+tp,hu.trans hp⟩
  | done mem =>
    let g := LinearPreprocessUnits.contents (normalizeClauses f).length mem
    change (Satisfiable g ↔ Satisfiable f) ∧ BoundedOccurrence g ∧
      ClauseVariablesDistinct g ∧ FormulaDeletion g f ∧
      g.length≤f.length ∧ variableBound g≤variableBound f at hs
    refine ⟨padFormula (f.length-g.length) g,padFormula_bounded _ hs.2.1,
      padFormula_distinct _ hs.2.2.1,
      PlanarPreprocess.normalized_output_padded_planar hr hp,?_⟩
    intro flips
    obtain ⟨tu,hu⟩ := reaches_units flips k hf hr
    obtain ⟨te,he,_⟩ := LinearPreprocessExtract.extraction_linear (normalizeClauses f).length mem
    obtain ⟨tx,_,hx⟩ := extract_simulation flips k f.length mem he
    obtain ⟨tp,hp,_⟩ := finish_padding flips hk f.length (f.length-g.length) g hs.2.1
    exact ⟨tu+(tx+tp),hu.trans (hx.trans hp)⟩

/-- The existing sharp transition and payload bounds apply to the exact
prepared graph, using determinism rather than an equality with the old
quadratic cleanup implementation. -/
theorem prepared_execution_linear_words {k : Nat} (hk : 5≤k) {f p : CNF}
    (hf : BoundedOccurrence f) (flips : EndpointChoices)
    (hp : ∃ u, Runs (step flips k f.length) u (initial f)
      (.done (orientedFormulaGraph flips k p).reverse)) :
    ∃ t w, Runs (step flips k f.length) t (initial f)
        (.done (orientedFormulaGraph flips k p).reverse) ∧
      t≤(variableBound f+1)*(128*k+160) ∧
      w≤(variableBound f+1).log2+
        ((4*linearCoefficient k+11)*(gadgetWidth k+1)).log2+2 ∧
      (Satisfiable f ↔ HasAssignment (orientedFormulaGraph flips k p).reverse k f.length) ∧
      ∀ u s, u≤t → Runs (step flips k f.length) u (initial f) s → WordsFit k w s := by
  obtain ⟨u,hu⟩ := hp
  obtain ⟨t,out,w,hr,ht,hw,hs,hfit⟩ := full_domain_linear_words flips hk hf
  have he := hr.terminal_unique hu rfl rfl
  have hout : out=(orientedFormulaGraph flips k p).reverse := State.done.inj he
  subst out
  exact ⟨t,w,hr,by simpa only [linearCoefficient_eq] using ht,hw,hs,hfit⟩

end WordPipeline

/-- Canonical instruction packaging of a graph with an explicit original
clause budget. The word-time theorem concerns the graph-emitting machine;
this logical packaging is not claimed to be a charged binary serializer. -/
def graphWithBudget (g : Graph) (budget : Nat) : CNF :=
  List.replicate budget [] ++ graphRecords g

theorem budgetTicks_output (budget : Nat) : GraphOutput (List.replicate budget []) [] budget := by
  induction budget with
  | zero => exact GraphOutput.nil
  | succ budget ih =>
    simpa only [List.replicate_succ,List.singleton_append,List.nil_append,Nat.add_comm] using
      GraphOutput.tick.append ih

theorem graphWithBudget_output {g : Graph} (hg : ∀ e∈g,edge e.1 e.2=e) (budget : Nat) :
    GraphOutput (graphWithBudget g budget) g budget := by
  have h := (budgetTicks_output budget).append (graphRecords_output g hg)
  simpa only [graphWithBudget,List.nil_append,Nat.add_zero] using h

theorem orientedFormulaGraph_normalized (flips : EndpointChoices) (k : Nat) (f : CNF) :
    ∀ e∈orientedFormulaGraph flips k f, edge e.1 e.2=e := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨v,_,he⟩ := List.mem_flatMap.mp he
    exact mapGraph_normalized _ _ e he
  · obtain ⟨g,hg,he⟩ := List.mem_flatten.mp he
    obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hg
    exact mapGraph_normalized _ _ e he

theorem orientedGraphWithBudget_output (flips : EndpointChoices) (k : Nat) (p : CNF) (budget : Nat) :
    GraphOutput (graphWithBudget (orientedFormulaGraph flips k p).reverse budget)
      (orientedFormulaGraph flips k p).reverse budget :=
  graphWithBudget_output (fun e he => orientedFormulaGraph_normalized flips k p e (List.mem_reverse.mp he)) budget

end STACS2027
