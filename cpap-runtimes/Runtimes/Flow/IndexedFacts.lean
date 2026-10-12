module

public import Runtimes.Flow.Indexed
import Mathlib.Tactic

/-! # Difference identities for indexed integral flows -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

private theorem differenceIndexes {arcs : ℕ} (flow target : IndexedFlow arcs)
    (indices : List (Fin arcs)) :
    ((indices.filterMap fun i =>
      if flow i = target i then none else some (⟨i, flow i⟩ : ResidualEdge arcs)).map
      ResidualEdge.index) = indices.filter (fun i => flow i != target i) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    cases hf : flow i <;> cases ht : target i <;> simp [hf, ht, ih]

/-- Difference edges never repeat an original arc occurrence. -/
theorem residualDifference_index_nodup {arcs : ℕ} (flow target : IndexedFlow arcs) :
    ((residualDifference flow target).map ResidualEdge.index).Nodup := by
  rw [residualDifference, differenceIndexes]
  exact (List.nodup_finRange arcs).filter _

/-- Every difference edge is available in the starting residual network. -/
theorem residualDifference_available {arcs : ℕ} (flow target : IndexedFlow arcs)
    (edge : ResidualEdge arcs) (h : edge ∈ residualDifference flow target) :
    residualAvailable flow edge := by
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp h
  by_cases heq : flow i = target i
  · simp [heq] at hi
  · simp [heq] at hi
    subst edge
    rfl

private theorem differenceCostList {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow target : IndexedFlow arcs) (indices : List (Fin arcs)) :
    residualCost net (indices.filterMap fun i =>
      if flow i = target i then none else some ⟨i, flow i⟩) =
      (indices.map fun i => (if target i then (net.cost i : ℤ) else 0) -
        (if flow i then (net.cost i : ℤ) else 0)).sum := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    cases hf : flow i <;> cases ht : target i <;>
      simp [residualCost, residualEdgeCost, hf, ht, residualCost] at ih ⊢ <;>
      exact ih

private theorem differenceBalanceList {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow target : IndexedFlow arcs) (indices : List (Fin arcs)) (v : Fin nodes) :
    residualBalance net (indices.filterMap fun i =>
      if flow i = target i then none else some ⟨i, flow i⟩) v =
      (indices.map fun i =>
        (if target i then
          (if net.tail i = v then (1 : ℤ) else 0) - (if net.head i = v then (1 : ℤ) else 0)
          else 0) -
        (if flow i then
          (if net.tail i = v then (1 : ℤ) else 0) - (if net.head i = v then (1 : ℤ) else 0)
          else 0)).sum := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    cases hf : flow i <;> cases ht : target i <;>
      simp [residualBalance, residualTail, residualHead, hf, ht] at ih ⊢ <;>
      omega

private theorem sumFinRange {arcs : ℕ} (f : Fin arcs → ℤ) :
    ((List.finRange arcs).map f).sum = ∑ i : Fin arcs, f i := by
  simpa using (List.sum_toFinset f (List.nodup_finRange arcs)).symm

/-- Subtracting flow vectors gives precisely the signed residual cost difference. -/
theorem residualDifference_cost {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow target : IndexedFlow arcs) :
    residualCost net (residualDifference flow target) =
      (indexedCost net target : ℤ) - (indexedCost net flow : ℤ) := by
  rw [residualDifference, differenceCostList, sumFinRange, Finset.sum_sub_distrib]
  simp [indexedCost, Nat.cast_sum, Nat.cast_ite]

/-- Subtracting flow vectors gives precisely the residual divergence difference. -/
theorem residualDifference_balance {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow target : IndexedFlow arcs) (v : Fin nodes) :
    residualBalance net (residualDifference flow target) v =
      indexedBalance net target v - indexedBalance net flow v := by
  rw [residualDifference, differenceBalanceList, sumFinRange, Finset.sum_sub_distrib]
  rfl

/-- Equal-value feasible flows differ by a balanced residual edge set. -/
theorem residualDifference_balanced {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    {d : ℕ} {flow target : IndexedFlow arcs}
    (hf : IsIndexedFlow net d flow) (hg : IsIndexedFlow net d target) (v : Fin nodes) :
    residualBalance net (residualDifference flow target) v = 0 := by
  rw [residualDifference_balance, hf v, hg v, sub_self]

/-- Costs below the arc count bound every integral flow cost by the square of that count. -/
theorem indexedCost_le_square {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (hc : ∀ i, net.cost i < arcs) :
    indexedCost net flow ≤ arcs * arcs := by
  calc
    indexedCost net flow ≤ ∑ _i : Fin arcs, arcs := by
      apply Finset.sum_le_sum
      intro i _
      split
      · exact (hc i).le
      · exact Nat.zero_le _
    _ = arcs * arcs := by simp

end STACS2027.Runtimes.Flow
