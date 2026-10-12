module

public import Runtimes.BoundedCost.InnerRestore
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def innerPathBodyCost (F : Stmt) (layout : CompilerLayout) (nodes clauses depth : ℕ) : ℕ :=
  8 * (clauses + 2 * nodes) +
    depth * ((800 + (wregs (Flow.hornSeparator F)).length) * (layout.span + 1) + 7) + 24

theorem actualPathRep_answer {F : Stmt} {layout : CompilerLayout} {nodes : ℕ} {original : CNF}
    {τ : Assignment} {digits oldOutput : List ℕ} {state : SearchPathState} {c : Config}
    (h : ActualPathRep F layout nodes original τ digits oldOutput state c) :
    InnerAnswerRep layout nodes state.answer c := by
  cases state with
  | failed => exact h.2.2
  | answered σ => exact h.2.2
  | running f L k =>
    obtain ⟨rows, forced, hlen, horiginal, hrows, hformula, hmask, hforced, hrequired,
      href, hbudget, hlive, hsuccess⟩ := h.2
    exact hsuccess

theorem innerPathBody_spec {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ C : ℕ, ∀ {layout : CompilerLayout} {nodes S depth globalBudget deleted : ℕ}
      {original : CNF} {rows : List (Bool × Clause)} {forced : ℕ → Bool}
      {τ : Assignment} {required : List Literal} {oldOutput : List ℕ} {oldMemory : ℕ → ℕ},
      3 ≤ nodes → original.length ≤ nodes → layout.span = (C + 1) * (nodes + 1) ^ 2 →
      InnerGeometry S layout nodes original.length depth →
      rows.length = original.length → rows.map Prod.snd = original →
      (∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < nodes) →
      evalCNF τ (activeOccurrences rows) = true →
      (∀ σ, Requires σ (denseRequirements nodes forced) ↔ Requires σ required) →
      ∀ (answer : Option Assignment) (digits : List ℕ) (word count : ℕ),
      HTB S (Compiler.pathBody F)
        (fun c => InnerRep F layout nodes original τ depth globalBudget deleted
          (maskWords rows) (forcedWords nodes forced) oldOutput oldMemory answer digits c ∧
          c.reg (innerCallerRegister wordIndex) = word ∧ c.reg (innerCallerRegister wordCount) = count)
        (fun c => InnerRep F layout nodes original τ depth globalBudget deleted
          (maskWords rows) (forcedWords nodes forced) oldOutput oldMemory
          (answer.orElse fun _ => annotatedPath (citedFlowLeastCutOperation hF hAL τ) τ digits
            (activeOccurrences rows) required (globalBudget - deleted)) digits c ∧
          c.reg (innerCallerRegister wordIndex) = word ∧ c.reg (innerCallerRegister wordCount) = count)
        (innerPathBodyCost F layout nodes original.length depth) := by
  obtain ⟨C, hpath⟩ := actualPathRAM_spec hF hAL
  refine ⟨C, ?_⟩
  intro layout nodes S depth globalBudget deleted original rows forced τ required oldOutput oldMemory
    hn hm hspan hgeo hlen horiginal hrows href hrequired answer digits word count
  intro c hpre
  obtain ⟨hrep, hword, hcount⟩ := hpre
  obtain ⟨hb, hans, hmemory⟩ := hrep
  have hfn : TwoSat.IsTwoCNF nodes original := by
    rw [← horiginal]
    intro clause hc
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hc
    exact hrows row hr
  have hcodeslen : (TwoSat.codes original).length ≤ 2 * original.length := by rw [TwoSat.length_codes hfn]
  cases answer with
  | some σ =>
    have hnonzero : c.reg (callerRegister nodeSuccess) ≠ 0 := by rw [hans.1]; decide
    refine ⟨c, 2, ExecB.ifzFalse hnonzero (ExecB.skip c), ?_, ?_⟩
    · exact ⟨⟨hb, hans, hmemory⟩, hword, hcount⟩
    · unfold innerPathBodyCost; omega
  | none =>
    have hzero : c.reg (callerRegister nodeSuccess) = 0 := hans
    obtain ⟨hcut, hlabels, hbase, hseed, hdigitsOutput⟩ := hgeo
    have hcutGeometry := hcut
    obtain ⟨_, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hcut
    have hrestore := onCallerRegisters_htb (PathRestore.program_spec
      (S := S) (active := layout.active) (forced := layout.forced)
      (activeCopy := layout.baseActive) (forcedCopy := layout.seedForced) (out := c.out)
      (activeBits := maskWords rows) (forcedBits := forcedWords nodes forced)
      (budget := globalBudget) (deleted := deleted) hb.2.2.1 hb.2.2.2.1
      (Or.inl (by simp only [maskWords_length, hlen]; omega))
      (Or.inl (by simp only [forcedWords_length]; omega))
      (Or.inl (by simp only [maskWords_length, hlen]; omega))
      (by simp only [maskWords_length, forcedWords_length, hlen]; omega))
    obtain ⟨c₁, t₁, he₁, hp₁, ht₁⟩ := hrestore c
      ⟨by simpa only [maskWords_length, forcedWords_length, hlen] using hb.2.1, rfl, rfl⟩
    obtain ⟨hg₁, hm₁, ho₁, hk₁, hl₁⟩ := hp₁
    change c₁.mem = PathRestore.restoredMemory c.mem layout.active layout.forced
      (maskWords rows) (forcedWords nodes forced) at hm₁
    have hb₁ := innerBasic_after_restore ⟨hcutGeometry, hlabels, hbase, hseed, hdigitsOutput⟩ hlen
      hcodeslen hb he₁ (by simpa only [maskWords_length, forcedWords_length, hlen] using hg₁) hm₁ ho₁
    have hs₁ : c₁.reg (callerRegister nodeSuccess) = 0 :=
      (he₁.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hzero
    let initial := SearchPathState.running (activeOccurrences rows) required (globalBudget - deleted)
    have hpInitial : FramedPathRep F layout nodes original τ digits oldOutput c₁.mem initial c₁ := by
      refine ⟨⟨hb₁.1.1, rows, forced, hlen, horiginal, hrows, rfl, hb₁.2.1, hb₁.2.2.1,
        hrequired, href, hk₁, hl₁, hs₁⟩, ?_⟩
      intro a ha; rfl
    have hlenDigits : digits.length = depth := hb.2.2.2.2.2.2.2
    have hpathRun := hpath (layout := layout) (nodes := nodes) (S := S) (original := original)
      (τ := τ) (digits := digits) (oldOutput := oldOutput) (oldMemory := c₁.mem) (state := initial)
      hn hm hspan hcutGeometry (by
        intro j hj
        exact (innerGeometry_snapshot_frames ⟨hcutGeometry, hlabels, hbase, hseed, hdigitsOutput⟩).2.2 j (by omega))
      (by omega)
    obtain ⟨c₂, t₂, he₂, hp₂, ht₂⟩ := hpathRun c₁ hpInitial
    have hb₂ := innerBasic_of_path ⟨hcutGeometry, hlabels, hbase, hseed, hdigitsOutput⟩ hlen hb₁.1
      hp₂.1.1.1 he₂ hp₂.1.2
    have hans₂ := actualPathRep_answer hp₂.1.1
    rw [pathPrefix_answer] at hans₂
    have hmem₂ : SameOn (InnerMemoryFrame layout nodes original.length depth) oldMemory c₂.mem := by
      intro a ha
      exact (hp₂.1.2 a ha.1).trans ((hb₁.2.2.2 a ha.1).trans (hmemory a ha))
    have hw₁ : c₁.reg (innerCallerRegister wordIndex) = word := by
      simpa only [innerCallerRegister_index] using
        (he₁.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans
          (by simpa only [innerCallerRegister_index] using hword)
    have hc₁ : c₁.reg (innerCallerRegister wordCount) = count := by
      simpa only [innerCallerRegister_count] using
        (he₁.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans
          (by simpa only [innerCallerRegister_count] using hcount)
    have hw₂ : c₂.reg (innerCallerRegister wordIndex) = word := by
      simpa only [innerCallerRegister_index] using
        (actualPath_registerFrame he₂ (r := 580) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans (by simpa only [innerCallerRegister_index] using hw₁)
    have hc₂ : c₂.reg (innerCallerRegister wordCount) = count := by
      simpa only [innerCallerRegister_count] using
        (actualPath_registerFrame he₂ (r := 581) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans (by simpa only [innerCallerRegister_count] using hc₁)
    refine ⟨c₂, t₁ + t₂ + 1, ExecB.ifzTrue hzero (ExecB.seq he₁ he₂),
      ⟨⟨hb₂, hans₂, hmem₂⟩, hw₂, hc₂⟩, ?_⟩
    simp only [maskWords_length, forcedWords_length, hlen] at ht₁
    unfold innerPathBodyCost
    rw [hlenDigits] at ht₂
    omega

end STACS2027.Runtimes.BoundedCost
