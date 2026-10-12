module

public import Runtimes.BoundedCost.InnerHeader
public import Runtimes.BoundedCost.InnerRegisterFrame
import Mathlib.Tactic

/-! The actual inner initialization and exhaustive path scan implement the
encoded annotated search, conditional only on the cited flow contract. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def actualInnerCost (F : Stmt) (layout : CompilerLayout) (nodes clauses depth : ℕ) : ℕ :=
  6 * depth + 13 + innerSearchCost F layout nodes clauses depth

theorem actualInnerRAM_spec {F : Stmt} {T : ℕ → ℕ}
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
      HTB S (Compiler.innerScan F)
        (InnerStart F layout nodes original τ depth globalBudget deleted
          (maskWords rows) (forcedWords nodes forced) oldOutput oldMemory)
        (fun c => InnerRep F layout nodes original τ depth globalBudget deleted
          (maskWords rows) (forcedWords nodes forced) oldOutput oldMemory
          (encodedPathSearch (citedFlowLeastCutOperation hF hAL τ) τ depth
            (activeOccurrences rows) required (globalBudget - deleted)) (Poly.cfg 3 depth 0) c ∧
          c.reg (innerCallerRegister wordIndex) = 3 ^ depth ∧
          c.reg (innerCallerRegister wordCount) = 3 ^ depth)
        (actualInnerCost F layout nodes original.length depth) := by
  obtain ⟨C, hscan⟩ := innerSearchRAM_spec hF hAL
  refine ⟨C, ?_⟩
  intro layout nodes S depth globalBudget deleted original rows forced τ required oldOutput oldMemory
    hn hm hspan hgeo hlen horiginal hrows href hrequired
  have hfn : TwoSat.IsTwoCNF nodes original := by
    rw [← horiginal]
    intro clause hc
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hc
    exact hrows row hr
  have hheader := innerHeader_spec (F := F) (globalBudget := globalBudget) (deleted := deleted)
    (τ := τ) (oldOutput := oldOutput) (oldMemory := oldMemory)
    (activeBits := maskWords rows) (forcedBits := forcedWords nodes forced) hgeo
    (by rw [TwoSat.length_codes hfn]) (by simp [hlen]) (by simp)
  simpa only [Compiler.innerScan, actualInnerCost] using
    hheader.seq (hscan hn hm hspan hgeo hlen horiginal hrows href hrequired)

end STACS2027.Runtimes.BoundedCost
