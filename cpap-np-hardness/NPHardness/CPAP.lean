module

public import NPHardness.SelectedPaths

/-!
Finite-graph CPAP decision predicate. Each simple k-cycle edge set is represented
once, and a choice omits one of its vertices, leaving a (k-2)-edge path.
The cost counts overlaps per pair of chosen paths and per shared edge.
-/

@[expose] public section
namespace STACS2027

/-- `CPAP(g, k)` has an assignment of cost at most `budget` (Definition 1): a path of `k - 2`
edges in each simple `k`-cycle of `g`, each cycle counted once, with total cost at most `budget`. -/
def HasAssignment (g : Graph) (k budget : Nat) : Prop :=
  ∃ ps : List (List Edge),
    ValidChoices ((cycles g k).map selectedOptions) ps ∧ cost ps ≤ budget

/-- The decision predicate uses exactly the manuscript's edge-load objective. -/
theorem hasAssignment_iff_load_cost {g : Graph} {k budget : Nat} (hg : g.Nodup) :
    HasAssignment g k budget ↔
      ∃ ps : List (List Edge),
        ValidChoices ((cycles g k).map selectedOptions) ps ∧
        (g.map fun e => load ps e * (load ps e - 1) / 2).sum ≤ budget := by
  constructor
  · rintro ⟨ps, hv, hc⟩
    exact ⟨ps, hv, (enumerated_cost_eq_load_sum hg hv) ▸ hc⟩
  · rintro ⟨ps, hv, hc⟩
    exact ⟨ps, hv, (enumerated_cost_eq_load_sum hg hv).symm ▸ hc⟩

end STACS2027
