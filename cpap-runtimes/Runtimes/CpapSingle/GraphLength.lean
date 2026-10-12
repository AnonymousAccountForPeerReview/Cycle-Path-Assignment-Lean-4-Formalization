module

public import Runtimes.Flow.Single
import Mathlib.Tactic

/-! # Input length for the single-program graph pipeline -/

@[expose] public section

namespace STACS2027.Runtimes.CpapSingle

open STACS2027 STACS2027.RAM

def lenGraph : Stmt := .seq (.load Flow.yM Flow.xZ)
  (.seq (.add Flow.xL Flow.yM Flow.yM) (.seq (.const Flow.yC 1)
    (.add Flow.xL Flow.xL Flow.yC)))

theorem lenGraph_spec (g : Graph) :
    HTB (graphInput g).length lenGraph (·=initial (graphInput g))
      (Flow.LenPost (graphInput g)) 4 := by
  apply HTB.run_le (by decide) (by decide)
  intro c hc
  subst c
  have h0 : (initial (graphInput g)).mem 0=g.length := by simp [initial_mem,graphInput]
  refine ⟨by addr_ok [lenGraph,initial_reg,length_graphInput],?_,?_,?_,?_⟩
  · simp [lenGraph,run,initial_reg,h0,length_graphInput];omega
  · simp [lenGraph,run]
  · simp [lenGraph,run]
  · intro r hr
    have hne : r≠Flow.xL ∧ r≠Flow.yM ∧ r≠Flow.yC := by
      simp only [Flow.xL,Flow.yM,Flow.yC,Flow.xJ,Flow.xZ] at hr ⊢
      omega
    simp [lenGraph,run,hne.1,hne.2.1,hne.2.2,initial_reg]

end STACS2027.Runtimes.CpapSingle
