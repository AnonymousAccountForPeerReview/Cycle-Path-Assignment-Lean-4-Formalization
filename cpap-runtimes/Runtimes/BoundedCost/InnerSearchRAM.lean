module

public import Runtimes.BoundedCost.InnerPathBody
import Mathlib.Tactic

/-! The complete inner ternary scan tests every annotated path and retains the
first successful assignment, using the actual restored flow-backed RAM body. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def innerSearchCost (F : Stmt) (layout : CompilerLayout) (nodes clauses depth : ℕ) : ℕ :=
  depth * 25 + 8 +
    (3 ^ depth * (innerPathBodyCost F layout nodes clauses depth + depth * 19 + 8) + 3)

theorem innerSearchRAM_spec {F : Stmt} {T : ℕ → ℕ}
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
      HTB S (renamedTernaryScan innerCallerRegister (Compiler.pathBody F))
        (InnerRep F layout nodes original τ depth globalBudget deleted
          (maskWords rows) (forcedWords nodes forced) oldOutput oldMemory none (Poly.cfg 3 depth 0))
        (fun c => InnerRep F layout nodes original τ depth globalBudget deleted
          (maskWords rows) (forcedWords nodes forced) oldOutput oldMemory
          (encodedPathSearch (citedFlowLeastCutOperation hF hAL τ) τ depth
            (activeOccurrences rows) required (globalBudget - deleted)) (Poly.cfg 3 depth 0) c ∧
          c.reg (innerCallerRegister wordIndex) = 3 ^ depth ∧
          c.reg (innerCallerRegister wordCount) = 3 ^ depth)
        (innerSearchCost F layout nodes original.length depth) := by
  obtain ⟨C, hbody⟩ := innerPathBody_spec hF hAL
  refine ⟨C, ?_⟩
  intro layout nodes S depth globalBudget deleted original rows forced τ required oldOutput oldMemory
    hn hm hspan hgeo hlen horiginal hrows href hrequired
  have hfn : TwoSat.IsTwoCNF nodes original := by
    rw [← horiginal]
    intro clause hc
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hc
    exact hrows row hr
  let Rep := InnerRep F layout nodes original τ depth globalBudget deleted
    (maskWords rows) (forcedWords nodes forced) oldOutput oldMemory
  let update : Option Assignment → List ℕ → Option Assignment := fun answer digits =>
    answer.orElse fun _ => annotatedPath (citedFlowLeastCutOperation hF hAL τ) τ digits
      (activeOccurrences rows) required (globalBudget - deleted)
  have hscan := renamedTernaryScan_state_spec innerCallerRegister innerCallerRegister_injective
    (innerCallerRegister_ne_temporary (by decide)) (innerCallerRegister_ne_temporary (by decide))
    Rep (innerRep_indep F layout nodes original τ depth globalBudget deleted
      (maskWords rows) (forcedWords nodes forced) oldOutput oldMemory)
    (fun _ _ _ h => ⟨h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
      h.1.2.2.2.2.2.2.1, h.1.1.2.2.2.2.2.2.2⟩)
    (fun _ _ _ _ _ h hi => innerRep_setDigit hgeo (by rw [TwoSat.length_codes hfn])
      (by simp [hlen]) (by simp) h hi)
    update none (by
      obtain ⟨hcut, _, _, _, hdigits⟩ := hgeo
      have hs := hcut.outputSpace
      omega)
    (fun word hw answer => hbody hn hm hspan hgeo hlen horiginal hrows href hrequired
      answer (Poly.cfg 3 depth word) word (3 ^ depth))
  have hfold : ternaryFold update depth (3 ^ depth) none =
      encodedPathSearch (citedFlowLeastCutOperation hF hAL τ) τ depth
        (activeOccurrences rows) required (globalBudget - deleted) := by
    unfold ternaryFold update encodedPathSearch
    simpa only [Option.orElse_none] using
      firstSuccess_foldl (fun word => annotatedPath (citedFlowLeastCutOperation hF hAL τ) τ
        (Poly.cfg 3 depth word) (activeOccurrences rows) required (globalBudget - deleted))
        (List.range (3 ^ depth)) none
  simpa only [Rep, innerSearchCost, hfold] using hscan

end STACS2027.Runtimes.BoundedCost
