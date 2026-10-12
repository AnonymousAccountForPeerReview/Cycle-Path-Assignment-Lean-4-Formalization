module

public import Runtimes.BoundedCost.ActualPathNode
public import Runtimes.BoundedCost.PathLiveControl
import Mathlib.Tactic

/-! The complete bounded annotated path is executed by the actual flow-backed
RAM node and retains every cell outside its explicitly bounded work tables. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def FramedPathRep (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (digits oldOutput : List ℕ) (oldMemory : ℕ → ℕ)
    (state : SearchPathState) (c : Config) : Prop :=
  ActualPathRep F layout nodes original τ digits oldOutput state c ∧
    SameOn (SearchNodeMemoryFrame layout.span layout.active layout.candidate layout.forced
      layout.labels layout.edgeInput nodes original.length) oldMemory c.mem

theorem framedPathRep_indep (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (digits oldOutput : List ℕ) (oldMemory : ℕ → ℕ) (state : SearchPathState) :
    Indep [callerRegister pathIndex, rT, callerRegister nodeChoice]
      (FramedPathRep F layout nodes original τ digits oldOutput oldMemory state) := by
  rintro c c' ⟨hreg, hmem, hout⟩ ⟨hrep, hframe⟩
  exact ⟨actualPathRep_indep F layout nodes original τ digits oldOutput state
    c c' ⟨hreg, hmem, hout⟩ hrep, by simpa only [hmem] using hframe⟩

theorem actualPathRAM_spec {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ C : ℕ, ∀ {layout : CompilerLayout} {nodes S : ℕ} {original : CNF}
      {τ : Assignment} {digits oldOutput : List ℕ} {oldMemory : ℕ → ℕ} {state : SearchPathState},
      3 ≤ nodes → original.length ≤ nodes → layout.span = (C + 1) * (nodes + 1) ^ 2 →
      LeastCutGeometry S layout.span layout.formula layout.active layout.candidate layout.reference
        layout.forced layout.labels layout.edgeInput nodes original.length →
      (∀ j, j < digits.length → SearchNodeMemoryFrame layout.span layout.active layout.candidate
        layout.forced layout.labels layout.edgeInput nodes original.length (layout.innerDigits + j)) →
      layout.innerDigits + digits.length ≤ S →
      HTB S (renamedPathControl callerRegister (searchNode F))
        (FramedPathRep F layout nodes original τ digits oldOutput oldMemory state)
        (fun c => FramedPathRep F layout nodes original τ digits oldOutput oldMemory
            (pathPrefix SearchPathState.live
              (annotatedPathStep (citedFlowLeastCutOperation hF hAL τ) τ)
              digits digits.length state) c ∧
          c.reg (callerRegister pathIndex) = digits.length ∧
          c.reg (callerRegister pathDepth) = digits.length)
        (digits.length * ((800 + (wregs (Flow.hornSeparator F)).length) * (layout.span + 1) + 7) + 3) := by
  obtain ⟨C, hnode⟩ := actualPathNode_spec hF hAL
  refine ⟨C, ?_⟩
  intro layout nodes S original τ digits oldOutput oldMemory state hn hm hspan hgeo hdigits hspace
  have hpath := renamedLivePathControl_spec callerRegister callerRegister_injective
    (by decide) (by decide) digits SearchPathState.live
    (annotatedPathStep (citedFlowLeastCutOperation hF hAL τ) τ)
    (FramedPathRep F layout nodes original τ digits oldOutput oldMemory)
    (framedPathRep_indep F layout nodes original τ digits oldOutput oldMemory)
    (fun _ _ h => actualPathRep_control h.1) hspace
    (fun i hi current hlive => hnode hn hm hspan hgeo hdigits hlive hi) state
  intro c hc
  exact hpath c ⟨hc, (actualPathRep_control hc.1).2.2.1⟩

end STACS2027.Runtimes.BoundedCost
