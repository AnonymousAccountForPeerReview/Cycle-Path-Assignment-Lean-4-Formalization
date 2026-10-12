module

public import Runtimes.BoundedCost.OuterSeedTransport
public import Runtimes.BoundedCost.OuterTransport
public import Runtimes.BoundedCost.OuterIndependence
public import Runtimes.BoundedCost.InnerCompilerBridge
import Mathlib.Tactic

/-! One actual outer iteration builds its selected compression seed, checks the
deleted-count budget and executes the proved inner path scan when admissible. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def outerBodyCost (F : Stmt) (layout : CompilerLayout) (nodes clauses depth special : ℕ) : ℕ :=
  12 * nodes + 44 * special + 11 + actualInnerCost F layout nodes clauses depth + 3

theorem not_mem_outerBody_word (F : Stmt) (r : ℕ) (hr : r = wordIndex ∨ r = wordCount) :
    callerRegister r ∉ wregs (Compiler.outerBody F) := by
  have hinner := Compiler.not_mem_innerScan_protected (F := F) (r := r)
    (by rcases hr with rfl | rfl <;> simp [Compiler.innerProtectedRegisters])
  rcases hr with rfl | rfl
  all_goals
    simp +decide only [Compiler.outerBody, wregs, List.mem_append, List.not_mem_nil,
      onCallerRegisters, renameRegisters_wregs, List.mem_singleton, not_or]
    simp only [not_false_eq_true, true_and, and_true]
    exact hinner

theorem outerBodyRAM_spec {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ C : ℕ, ∀ {layout : CompilerLayout} {nodes S budget depth processed : ℕ}
      {original : CNF} {τ : Assignment} {rows : List (Bool × Clause)} {special : CNF}
      {oldOutput digits : List ℕ},
      3 ≤ nodes → original.length ≤ nodes → layout.span = (C + 1) * (nodes + 1) ^ 2 →
      OuterGeometry S layout nodes original.length depth special.length →
      rows.length = original.length → rows.map Prod.snd = original →
      (∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < nodes) →
      TwoSat.IsTwoCNF nodes special → evalCNF τ (activeOccurrences rows) = true →
      digits.length = special.length → (∀ d ∈ digits, d < 3) →
      ∀ (answer : Option Assignment) (word count : ℕ),
      HTB S (Compiler.outerBody F)
        (fun c => OuterRep F layout nodes original τ rows special budget depth processed
          oldOutput answer digits c ∧ c.reg (callerRegister wordIndex) = word ∧
          c.reg (callerRegister wordCount) = count)
        (fun c => OuterRep F layout nodes original τ rows special budget depth processed oldOutput
          (outerAnswerStep (citedFlowLeastCutOperation hF hAL τ) τ depth
            (activeOccurrences rows) special budget answer digits) digits c ∧
          c.reg (callerRegister wordIndex) = word ∧ c.reg (callerRegister wordCount) = count)
        (outerBodyCost F layout nodes original.length depth special.length) := by
  obtain ⟨C, hinner⟩ := actualInnerRAM_spec hF hAL
  refine ⟨C, ?_⟩
  intro layout nodes S budget depth processed original τ rows special oldOutput digits
    hn hm hspan hgeo hlen horiginal hrows hspecial href hdlen hdvalid answer word count
  have hf : TwoSat.IsTwoCNF nodes original := by
    rw [← horiginal]
    intro clause hc
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hc
    exact hrows row hr
  intro c₀ ⟨hrep, hword, hcount⟩
  cases answer with
  | some σ =>
    exact ⟨c₀, 2, .ifzFalse (by rw [hrep.2.1]; decide) (.skip c₀),
      ⟨by simpa [outerAnswerStep] using hrep, hword, hcount⟩,
      by unfold outerBodyCost; omega⟩
  | none =>
    have hsuccess := hrep.2
    obtain ⟨branch, hv⟩ := compressionVector_total special (fun c hc => (hspecial c hc).1)
      digits hdlen hdvalid
    have hvector := seedRowsOf_vector special (fun c hc => (hspecial c hc).1) digits branch hv
    obtain ⟨c₁, t₁, he₁, hp₁, ht₁⟩ := outerSeed_spec hf hspecial hgeo hlen hdvalid c₀ hrep
    have hdeleted : c₁.reg (callerRegister seedDeleted) = branch.1 := by
      rw [hp₁.2.2]
      simpa only [hvector.1] using hvector.2.1
    let c₂ := run (onCallerRegisters (.sub Compiler.branchExcess seedDeleted Compiler.budget)) c₁
    have he₂ := execB_run (S := S)
      (onCallerRegisters (.sub Compiler.branchExcess seedDeleted Compiler.budget)) (by decide) c₁
      (AddrOK.of_memFree (by decide))
    have hrep₂ : OuterRep F layout nodes original τ rows special budget depth processed oldOutput none digits c₂ := by
      apply (outerRep_excess_indep F layout nodes original τ rows special budget depth
        processed oldOutput none digits).setReg (by simp)
      exact hp₁.1
    have hforced₂ : Arr c₂.mem layout.seedForced (forcedWords nodes
        (fun u => seedForcedValue (seedRowsOf digits special) special.length u == 1)) := hp₁.2.1
    have hdeleted₂ : c₂.reg (callerRegister PathRestore.specialDeleted) = branch.1 := by
      exact (he₂.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hdeleted
    have hexcess : c₂.reg (callerRegister Compiler.branchExcess) = branch.1 - budget := by
      have hk := hp₁.1.1.1.budget
      change c₁.reg (callerRegister Compiler.budget) = budget at hk
      simp +decide [c₂, onCallerRegisters, renameRegisters, hdeleted, hk]
    have hbranch : ∃ c₃ t₃,
        ExecB S (.ifz (callerRegister Compiler.branchExcess) (Compiler.innerScan F) .skip) c₂ t₃ c₃ ∧
        OuterRep F layout nodes original τ rows special budget depth processed oldOutput
          (if branch.1 ≤ budget then encodedPathSearch (citedFlowLeastCutOperation hF hAL τ) τ
            depth (activeOccurrences rows) branch.2 (budget - branch.1) else none) digits c₃ ∧
        t₃ ≤ actualInnerCost F layout nodes original.length depth + 1 := by
      by_cases hb : branch.1 ≤ budget
      · have hzero : c₂.reg (callerRegister Compiler.branchExcess) = 0 := by rw [hexcess]; omega
        have hrequires : ∀ σ, Requires σ (denseRequirements nodes
            (fun u => seedForcedValue (seedRowsOf digits special) special.length u == 1)) ↔
            Requires σ branch.2 := by
          intro σ
          simpa only [hvector.1] using denseSeed_vector_requirements special hspecial digits branch hv σ
        have hstart := innerStart_of_globals hrep₂.1.1 hdeleted₂ hrep₂.1.2.1 hrep₂.1.2.2.1
          hrep₂.1.2.2.2.2.2.1 hforced₂ hrep₂.1.2.2.2.1 hrep₂.1.2.2.2.2.1 hrep₂.2
          (fun _ _ => rfl)
        obtain ⟨c₃, t₃, he₃, hp₃, ht₃⟩ := hinner hn hm hspan hgeo.inner hlen horiginal hrows href
          hrequires c₂ hstart
        have hr := outerRep_after_inner hgeo (le_of_eq (TwoSat.length_codes hspecial))
          hrep₂.1 he₃ hp₃.1
        exact ⟨c₃, t₃ + 1, .ifzTrue hzero he₃, by simpa only [if_pos hb] using hr, by omega⟩
      · have hnonzero : c₂.reg (callerRegister Compiler.branchExcess) ≠ 0 := by rw [hexcess]; omega
        exact ⟨c₂, 2, .ifzFalse hnonzero (.skip c₂), by simpa only [if_neg hb] using hrep₂,
          by unfold actualInnerCost innerSearchCost; omega⟩
    obtain ⟨c₃, t₃, he₃, hp₃, ht₃⟩ := hbranch
    have he : ExecB S (Compiler.outerBody F) c₀ (t₁ + (1 + t₃) + 1) c₃ :=
      .ifzTrue hsuccess (.seq he₁ (.seq he₂ he₃))
    refine ⟨c₃, _, he, ⟨?_, ?_, ?_⟩, ?_⟩
    · simpa only [outerAnswerStep, Option.orElse_none, hv] using hp₃
    · exact (he.reg_frame (not_mem_outerBody_word F wordIndex (Or.inl rfl))).trans hword
    · exact (he.reg_frame (not_mem_outerBody_word F wordCount (Or.inr rfl))).trans hcount
    · unfold outerBodyCost
      omega

end STACS2027.Runtimes.BoundedCost
