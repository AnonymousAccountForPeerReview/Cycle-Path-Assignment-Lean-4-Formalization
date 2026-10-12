module

public import Runtimes.BoundedCost.LeastCutRAM
public import Runtimes.BoundedCost.CompilerLayout
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

/-- The fixed compiler layout supplies all separation and address bounds used
by the repeated least-cut backend. -/
theorem compilerLayout_leastCutGeometry (constant clauses budget : ℕ) :
    let l := compilerLayout constant clauses budget
    LeastCutGeometry l.space l.span l.formula l.active l.candidate l.reference
      l.forced l.labels l.edgeInput (2 * clauses + 1) clauses := by
  dsimp only
  constructor <;> dsimp [compilerLayout] <;> omega

end STACS2027.Runtimes.BoundedCost
