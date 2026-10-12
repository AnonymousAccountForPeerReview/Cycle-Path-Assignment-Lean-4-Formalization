module

public import Outerplanar.GeneralDegenerate
public import Outerplanar.PerfectK23

@[expose] public section

namespace STACS2027

/-- Algorithm 4 has a single global elimination order and outputs a perfect assignment
on every loop-free outerplanar graph, including graphs with cut vertices and disconnected
graphs. The drawing and graph-class premises are the manuscript's problem class. -/
theorem outerplanar_algorithm_perfect {g : Graph} (hg : OuterplanarDrawing g)
    (hloop : ∀ e ∈ g, e.1 ≠ e.2) :
    ∃ rank, EliminationOrder g rank ∧
      ValidChoices ((cycles g 4).map selectedOptions) (algorithm4 rank g) ∧
      cost (algorithm4 rank g) = 0 := by
  obtain ⟨rank, hrank⟩ := outerplanar_eliminationOrder hg
  have hminor := (outerplanarDrawing_iff_minorFree g).mp hg
  obtain ⟨hv, hc⟩ := algorithm4_perfect hrank
    (commonNeighbourBound_of_k23MinorFree hminor.2 hloop)
  exact ⟨rank, hrank, hv, hc⟩

/-- Every loop-free outerplanar graph admits a perfect four-cycle path assignment through
Algorithm 4, with no block decomposition supplied by the caller. -/
theorem outerplanar_algorithm_assignment {g : Graph} (hg : OuterplanarDrawing g)
    (hloop : ∀ e ∈ g, e.1 ≠ e.2) : HasAssignment g 4 0 := by
  obtain ⟨rank, _, hv, hc⟩ := outerplanar_algorithm_perfect hg hloop
  exact ⟨algorithm4 rank g, hv, hc.le⟩

end STACS2027
