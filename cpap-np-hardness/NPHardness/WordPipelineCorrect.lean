module

public import NPHardness.WordPipelineMachine
public import NPHardness.LinearPreprocessResult

/-!
End-to-end runtime and correctness on the full Definition 7 domain, including
repeated literals and tautological clauses. The source incidence table is
constructed, not assumed. The original clause count is retained as CPAP's
budget. Orientation bits are supplied; computing a planar choice is separate.

Each transition is a bounded local-word macro. The queue's apparently recursive
updates are bounded by `LinearPreprocessUnitWork.reachable_unit_work`.
-/

@[expose] public section
namespace STACS2027.WordPipeline
open Complexity.SAT

theorem finish_padding (flips : EndpointChoices) {k : Nat} (hk : 5 ≤ k)
    (budget r : Nat) (g : CNF) (hg : BoundedOccurrence g) :
    ∃ t, Runs (step flips k budget) t (.padding r (.scanFormula g 0 []))
        (.done (orientedFormulaGraph flips k (padFormula r g)).reverse) ∧
      t ≤ LinearPreprocessPadding.transitionCount r g +
        (variableBound (padFormula r g)+1)*(WordConstructor.linearCoefficient k+6) := by
  let p := padFormula r g
  have hp : BoundedOccurrence p := padFormula_bounded r hg
  obtain ⟨tp,htp,hrp⟩ := padding_simulation flips k budget r
    (LinearPreprocessPadding.executes_padFormula r g)
  obtain ⟨th,hth,hrh⟩ := header_simulation flips k budget p (Header.computes_bound p)
  obtain ⟨tg,htg,hrg⟩ := graph_simulation flips k budget (variableBound p) p
    (WordConstructor.executes_graph flips k p hp.isThreeCNF)
  have htgc := WordConstructor.transitionCount_linear hk hp (variableBound p)
    (fun c hc l hl => literal_lt_variableBound hc hl)
  have hl := hp.literal_count (variableBound p)
    (fun c hc l hl => literal_lt_variableBound hc hl)
  have hc := hp.clause_count_variableBound
  refine ⟨tp+(th+tg),hrp.trans (hrh.trans hrg),?_⟩
  have hmid : th+tg ≤ (variableBound p+1)*(WordConstructor.linearCoefficient k+6) := by
    simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul] at htgc ⊢
    omega
  change tp+(th+tg) ≤ LinearPreprocessPadding.transitionCount r g +
    (variableBound p+1)*(WordConstructor.linearCoefficient k+6)
  omega

def linearCoefficient (k : Nat) : Nat := 4*WordConstructor.linearCoefficient k+100

theorem linearCoefficient_eq (k : Nat) : linearCoefficient k = 128*k+160 := by
  rw [linearCoefficient,WordConstructor.linearCoefficient_eq]
  omega

theorem rejected_output (flips : EndpointChoices) {k : Nat} (hk : 5 ≤ k) (m : Nat) :
    ¬ HasAssignment (orientedFormulaGraph flips k (padFormula (m+1) [])).reverse k m := by
  intro h
  have hh := (hasAssignment_graph_perm (List.reverse_perm _) k m).mp h
  letI : Oriented.Orientation := ⟨flips⟩
  have hb := Oriented.formulaGraph_assignment_budget_lower hk
    (padFormula_bounded (m+1) emptyFormula_bounded)
    (padFormula_distinct (m+1) emptyFormula_distinct) hh
  rw [padFormula_length] at hb
  simp only [List.length_nil,Nat.zero_add] at hb
  omega

/-- Full-domain deterministic execution with the original clause-count budget.
No clean-input, distinct-variable, or adjacency-certificate assumption remains.
The supplied orientation table is read during graph emission; this theorem
does not assert that its chosen graph is planar. -/
theorem full_domain_linear (flips : EndpointChoices) {k : Nat} (hk : 5 ≤ k)
    {f : CNF} (hf : BoundedOccurrence f) :
    ∃ t out, Runs (step flips k f.length) t (initial f) (.done out) ∧
      t ≤ (variableBound f+1)*linearCoefficient k ∧
      (Satisfiable f ↔ HasAssignment out k f.length) := by
  let norm := normalizeClauses f
  have hd : FormulaDeletion norm f := normalizeClauses_deletion f
  have hnormlen := hd.2.1
  have hnormlit := hd.1.length_le
  have hflit := hf.literal_count (variableBound f)
    (fun c hc l hl => literal_lt_variableBound hc hl)
  have hfcla := hf.clause_count_variableBound
  obtain ⟨tn,htn,hrn⟩ := normalize_simulation flips k f.length
    (LinearPreprocessNormalize.executes_normalizeClauses f hf.isThreeCNF)
  obtain ⟨ti,hti,hri⟩ := initialize_simulation flips k f.length
    (LinearPreprocessInit.executes_initialize norm)
  obtain ⟨tk,result,htk,hrk,hspec⟩ := LinearPreprocessResult.normalized_kernel_correct hf
  obtain ⟨tu,htu,hru⟩ := units_simulation flips k f.length norm.length
    (LinearPreprocessInit.initialAdj norm) hrk
  have hpre := hrn.trans (hri.trans hru)
  have hpretime : tn+(ti+tu) ≤ f.flatten.length+10*f.length+5 := by
    change tn ≤ f.length+norm.length+2 at htn
    change ti ≤ norm.flatten.length+3*norm.length+2 at hti
    change tk ≤ 5*norm.length+1 at htk
    omega
  cases result with
  | running mem queue => exact False.elim hspec
  | rejected =>
    obtain ⟨tp,hrp,htp⟩ := finish_padding flips hk f.length (f.length+1) [] emptyFormula_bounded
    have hn : variableBound (padFormula (f.length+1) [])+1 ≤ 4*(variableBound f+1) := by
      rw [padFormula_variableBound]
      simp only [variableBound]
      omega
    have hmult := Nat.mul_le_mul_right (WordConstructor.linearCoefficient k+6) hn
    have hpad : LinearPreprocessPadding.transitionCount (f.length+1) [] = 2*f.length+5 := by
      simp only [LinearPreprocessPadding.transitionCount,List.flatten_nil,List.length_nil]
      omega
    refine ⟨tn+(ti+tu)+tp,_,hpre.trans hrp,?_,?_⟩
    · rw [hpad] at htp
      unfold linearCoefficient
      simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_assoc,
        Nat.mul_comm,Nat.mul_left_comm] at hmult htp ⊢
      omega
    · exact ⟨fun h => False.elim (hspec h),fun h => False.elim (rejected_output flips hk f.length h)⟩
  | done mem =>
    let g := LinearPreprocessUnits.contents norm.length mem
    change (Satisfiable g ↔ Satisfiable f) ∧ BoundedOccurrence g ∧
      ClauseVariablesDistinct g ∧ FormulaDeletion g f ∧
      g.length ≤ f.length ∧ variableBound g ≤ variableBound f at hspec
    obtain ⟨hsat,hgb,hgd,hgdel,hgm,hgn⟩ := hspec
    obtain ⟨te,hre,hte⟩ := LinearPreprocessExtract.extraction_linear norm.length mem
    obtain ⟨tx,htx,hrx⟩ := extract_simulation flips k f.length mem hre
    obtain ⟨tp,hrp,htp⟩ := finish_padding flips hk f.length (f.length-g.length) g hgb
    have hn : variableBound (padFormula (f.length-g.length) g)+1 ≤ 4*(variableBound f+1) := by
      rw [padFormula_variableBound]
      omega
    have hmult := Nat.mul_le_mul_right (WordConstructor.linearCoefficient k+6) hn
    have hgl := hgdel.1.length_le
    have hpad : LinearPreprocessPadding.transitionCount (f.length-g.length) g ≤
        f.flatten.length+5*f.length+3 := by
      unfold LinearPreprocessPadding.transitionCount
      omega
    refine ⟨tn+(ti+tu)+(tx+tp),_,hpre.trans (hrx.trans hrp),?_,?_⟩
    · unfold linearCoefficient
      simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_assoc,
        Nat.mul_comm,Nat.mul_left_comm] at hmult htp ⊢
      omega
    · have hlen : (padFormula (f.length-g.length) g).length = f.length := by
        rw [padFormula_length]
        omega
      have hcorrect := WordConstructor.graph_correct flips hk
        (padFormula_bounded (f.length-g.length) hgb)
        (padFormula_distinct (f.length-g.length) hgd)
      rw [hlen] at hcorrect
      exact hsat.symm.trans ((padFormula_sat (f.length-g.length) g).symm.trans hcorrect)

end STACS2027.WordPipeline
