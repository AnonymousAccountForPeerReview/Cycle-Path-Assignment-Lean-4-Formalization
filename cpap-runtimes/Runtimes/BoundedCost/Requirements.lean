module

public import Runtimes.BoundedCost.Domain
import Mathlib.Tactic

/-! Least cuts depend on the satisfied literals, independently of requirement
order or repeated occurrences. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

theorem IsLeastCut.requirements_congr {τ δ : Assignment} {f : CNF} {L L' : List Literal}
    (h : IsLeastCut τ f L δ) (he : ∀ σ, Requires σ L ↔ Requires σ L') :
    IsLeastCut τ f L' δ := by
  refine ⟨(he δ).mp h.required, ?_, ?_⟩
  · intro σ hσ
    exact h.optimal σ ((he σ).mpr hσ)
  · intro σ hσ hcost
    exact h.least σ ((he σ).mpr hσ) hcost

theorem isLeastCut_requirements_iff {τ δ : Assignment} {f : CNF} {L L' : List Literal}
    (he : ∀ σ, Requires σ L ↔ Requires σ L') :
    IsLeastCut τ f L δ ↔ IsLeastCut τ f L' δ := by
  exact ⟨fun h => h.requirements_congr he,
    fun h => h.requirements_congr (fun σ => (he σ).symm)⟩

end STACS2027.Runtimes.BoundedCost
