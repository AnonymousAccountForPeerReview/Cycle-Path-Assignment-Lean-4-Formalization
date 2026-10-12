module

public import Runtimes.Flow.ReverseReach
import Mathlib.Tactic

/-!
# Sequential reverse residual scans

Each round scans each indexed arc once and marks a predecessor immediately. The proof uses
the parallel reverse closure as a lower bound and residual reachability as an upper bound.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

/-- Mark one immediate predecessor if its available residual head has already been marked. -/
def reverseEdgeStep {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (flow : IndexedFlow arcs)
    (vertices : Finset (Fin nodes)) (i : Fin arcs) : Finset (Fin nodes) :=
  if residualHead net (availableEdge flow i) ∈ vertices then
    insert (residualTail net (availableEdge flow i)) vertices else vertices

/-- One sequential scan of all original arc indices. -/
def reverseScan {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (flow : IndexedFlow arcs)
    (vertices : Finset (Fin nodes)) : Finset (Fin nodes) :=
  (List.finRange arcs).foldl (reverseEdgeStep net flow) vertices

/-- The sequential reverse scan repeated a bounded number of times. -/
def reverseScanSet {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (flow : IndexedFlow arcs) :
    ℕ → Finset (Fin nodes)
  | 0 => {net.sink}
  | rounds + 1 => reverseScan net flow (reverseScanSet net flow rounds)

private theorem subset_edgeStep {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (vertices : Finset (Fin nodes)) (i : Fin arcs) :
    vertices ⊆ reverseEdgeStep net flow vertices i := by
  unfold reverseEdgeStep
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

private theorem subset_scanList {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (indices : List (Fin arcs)) (vertices : Finset (Fin nodes)) :
    vertices ⊆ indices.foldl (reverseEdgeStep net flow) vertices := by
  induction indices generalizing vertices with
  | nil => exact Finset.Subset.refl _
  | cons i indices ih =>
    exact (subset_edgeStep net flow vertices i).trans (ih _)

private theorem predecessor_scanList {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (indices : List (Fin arcs)) (vertices : Finset (Fin nodes))
    (i : Fin arcs) (hi : i ∈ indices)
    (hh : residualHead net (availableEdge flow i) ∈ vertices) :
    residualTail net (availableEdge flow i) ∈ indices.foldl (reverseEdgeStep net flow) vertices := by
  induction indices generalizing vertices with
  | nil => simp at hi
  | cons j indices ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · apply subset_scanList net flow indices (reverseEdgeStep net flow vertices i)
      simp [reverseEdgeStep, hh]
    · apply ih _ hi
      exact subset_edgeStep net flow vertices j hh

/-- One sequential scan contains every predecessor of the region at its start. -/
theorem reverseStep_subset_reverseScan {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (vertices : Finset (Fin nodes)) :
    reverseStep net flow vertices ⊆ reverseScan net flow vertices := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact subset_scanList net flow _ vertices hv
  · obtain ⟨i, hi, hh⟩ := (Finset.mem_filter.mp hv).2
    rw [← hi]
    exact predecessor_scanList net flow _ vertices i (by simp) hh

private theorem reverseStep_mono {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) {vertices other : Finset (Fin nodes)} (h : vertices ⊆ other) :
    reverseStep net flow vertices ⊆ reverseStep net flow other := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact Finset.mem_union_left _ (h hv)
  · obtain ⟨i, hi, hh⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, hi, h hh⟩⟩)

/-- Sequential rounds contain the parallel expansion with the same round count. -/
theorem reverseReachSet_subset_reverseScanSet {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (rounds : ℕ) :
    reverseReachSet net flow rounds ⊆ reverseScanSet net flow rounds := by
  induction rounds with
  | zero => exact Finset.Subset.refl _
  | succ rounds ih =>
    exact (reverseStep_mono net flow ih).trans (reverseStep_subset_reverseScan net flow _)

private theorem scanList_sound {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (indices : List (Fin arcs)) (vertices : Finset (Fin nodes))
    (h : ∀ v ∈ vertices, ResidualReach net flow v net.sink) :
    ∀ v ∈ indices.foldl (reverseEdgeStep net flow) vertices, ResidualReach net flow v net.sink := by
  induction indices generalizing vertices with
  | nil => exact h
  | cons i indices ih =>
    apply ih
    intro v hv
    unfold reverseEdgeStep at hv
    split at hv
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · apply (h _ (by assumption)).head
        exact ⟨i, rfl, rfl⟩
      · exact h _ hv
    · exact h _ hv

/-- Sequential marking introduces no false residual-reachability witness. -/
theorem reverseScanSet_sound {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (rounds : ℕ) :
    ∀ v ∈ reverseScanSet net flow rounds, ResidualReach net flow v net.sink := by
  induction rounds with
  | zero =>
    intro v hv
    have : v = net.sink := by simpa [reverseScanSet] using hv
    subst v
    exact .refl
  | succ rounds ih => exact scanList_sound net flow _ _ ih

/-- The `nodes` sequential rounds compute exactly the proved reverse closure. -/
theorem reverseScanSet_eq_reverseReachSet {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) : reverseScanSet net flow nodes = reverseReachSet net flow nodes := by
  apply Finset.Subset.antisymm
  · intro v hv
    exact reverseReachSet_complete net flow v (reverseScanSet_sound net flow nodes v hv)
  · exact reverseReachSet_subset_reverseScanSet net flow nodes

end STACS2027.Runtimes.Flow
