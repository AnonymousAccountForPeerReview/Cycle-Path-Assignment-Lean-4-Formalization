module

public import Runtimes.BoundedCost.OuterBodyRAM
public import Runtimes.BoundedCost.OuterHeader
import Mathlib.Tactic

/-! The actual outer RAM scan enumerates every compression vector and retains
the first assignment returned by its flow-backed inner path scan. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def outerSearchCost (F : Stmt) (layout : CompilerLayout) (nodes clauses depth special : ℕ) : ℕ :=
  special * 25 + 8 +
    (3 ^ special * (outerBodyCost F layout nodes clauses depth special + special * 19 + 8) + 3)

theorem actualOuterRAM_spec {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ C : ℕ, ∀ {layout : CompilerLayout} {nodes S budget depth processed : ℕ}
      {original : CNF} {τ : Assignment} {rows : List (Bool × Clause)} {special : CNF}
      {oldOutput : List ℕ},
      3 ≤ nodes → original.length ≤ nodes → layout.span = (C + 1) * (nodes + 1) ^ 2 →
      OuterGeometry S layout nodes original.length depth special.length →
      rows.length = original.length → rows.map Prod.snd = original →
      (∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < nodes) →
      TwoSat.IsTwoCNF nodes special → evalCNF τ (activeOccurrences rows) = true →
      HTB S (renamedTernaryScan callerRegister (Compiler.outerBody F))
        (OuterRep F layout nodes original τ rows special budget depth processed oldOutput none
          (Poly.cfg 3 special.length 0))
        (fun c => OuterRep F layout nodes original τ rows special budget depth processed oldOutput
          (encodedCompressionSearch (citedFlowLeastCutOperation hF hAL τ) τ depth
            (activeOccurrences rows) special budget) (Poly.cfg 3 special.length 0) c ∧
          c.reg (callerRegister wordIndex) = 3 ^ special.length ∧
          c.reg (callerRegister wordCount) = 3 ^ special.length)
        (outerSearchCost F layout nodes original.length depth special.length) := by
  obtain ⟨C, hbody⟩ := outerBodyRAM_spec hF hAL
  refine ⟨C, ?_⟩
  intro layout nodes S budget depth processed original τ rows special oldOutput
    hn hm hspan hgeo hlen horiginal hrows hspecial href
  have hfn : TwoSat.IsTwoCNF nodes original := by
    rw [← horiginal]
    intro clause hc
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hc
    exact hrows row hr
  let Rep := OuterRep F layout nodes original τ rows special budget depth processed oldOutput
  let update := outerAnswerStep (citedFlowLeastCutOperation hF hAL τ) τ depth
    (activeOccurrences rows) special budget
  have hscan := renamedTernaryScan_state_spec callerRegister callerRegister_injective
    (by decide) (by decide) Rep
    (outerRep_indep F layout nodes original τ rows special budget depth processed oldOutput)
    (fun _ _ _ h => by
      obtain ⟨⟨_, _, _, _, _, _, _, hb, hl, hk, hd, _, _, _, _⟩, _⟩ := h
      exact ⟨hb, hl, hk, hd⟩)
    (fun _ _ _ _ _ h hi => outerRep_setDigit hgeo hlen
      (le_of_eq (TwoSat.length_codes hfn)) (le_of_eq (TwoSat.length_codes hspecial)) h hi)
    update none (by
      have hi := hgeo.outerInner
      have hd := hgeo.inner.digitsOutput
      have hs := hgeo.inner.cut.outputSpace
      omega)
    (fun word hw answer => hbody hn hm hspan hgeo hlen horiginal hrows hspecial href
      (Poly.length_cfg _ _ _) (Poly.cfg_lt (by decide) _ _) answer word (3 ^ special.length))
  have hfold := outerAnswerStep_fold (citedFlowLeastCutOperation hF hAL τ) τ depth
    (activeOccurrences rows) special budget
  simpa only [Rep, update, outerSearchCost, hfold] using hscan

def outerCompleteCost (F : Stmt) (layout : CompilerLayout) (nodes clauses depth special : ℕ) : ℕ :=
  6 * special + 13 + outerSearchCost F layout nodes clauses depth special

theorem completeOuterRAM_spec {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ C : ℕ, ∀ {layout : CompilerLayout} {nodes S budget depth processed : ℕ}
      {original : CNF} {τ : Assignment} {rows : List (Bool × Clause)} {special : CNF}
      {oldOutput : List ℕ},
      3 ≤ nodes → original.length ≤ nodes → layout.span = (C + 1) * (nodes + 1) ^ 2 →
      OuterGeometry S layout nodes original.length depth special.length →
      rows.length = original.length → rows.map Prod.snd = original →
      (∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < nodes) →
      TwoSat.IsTwoCNF nodes special → evalCNF τ (activeOccurrences rows) = true →
      HTB S (.seq (onCallerRegisters (LoopHeaders.program false))
          (renamedTernaryScan callerRegister (Compiler.outerBody F)))
        (OuterStart F layout nodes original τ rows special budget depth processed oldOutput)
        (fun c => OuterRep F layout nodes original τ rows special budget depth processed oldOutput
          (encodedCompressionSearch (citedFlowLeastCutOperation hF hAL τ) τ depth
            (activeOccurrences rows) special budget) (Poly.cfg 3 special.length 0) c ∧
          c.reg (callerRegister wordIndex) = 3 ^ special.length ∧
          c.reg (callerRegister wordCount) = 3 ^ special.length)
        (outerCompleteCost F layout nodes original.length depth special.length) := by
  obtain ⟨C, hscan⟩ := actualOuterRAM_spec hF hAL
  refine ⟨C, ?_⟩
  intro layout nodes S budget depth processed original τ rows special oldOutput
    hn hm hspan hgeo hlen horiginal hrows hspecial href
  have hfn : TwoSat.IsTwoCNF nodes original := by
    rw [← horiginal]
    intro clause hc
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hc
    exact hrows row hr
  exact (outerHeader_spec hgeo hlen (le_of_eq (TwoSat.length_codes hfn))
    (le_of_eq (TwoSat.length_codes hspecial))).seq
      (hscan hn hm hspan hgeo hlen horiginal hrows hspecial href)

end STACS2027.Runtimes.BoundedCost
