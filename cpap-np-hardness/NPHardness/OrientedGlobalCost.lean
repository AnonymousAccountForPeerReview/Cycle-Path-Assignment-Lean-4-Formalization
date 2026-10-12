module

public import NPHardness.OrientedGlobalCycles
public import NPHardness.FamilyCost

/-! Exact cost decomposition of the concrete global gadget families. No
independence of variable/clause pairs is assumed: their interaction is kept
as an explicit nonnegative term for each clause. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

theorem formulaGraph_cost_decomposition {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    (V C : Nat → List (List Edge))
    (hV : ∀ v, v < variableBound f → ∀ p ∈ V v, p ⊆ placedVariableGraph k v)
    (hC : ∀ j, ∀ hj : j < (placeFormula [] f).length, ∀ p ∈ C j,
      p ⊆ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j]) :
    cost (globalVariablePaths f V ++ globalClausePaths f C) =
      ((List.range (variableBound f)).map fun v => cost (V v)).sum +
      ((List.range (placeFormula [] f).length).map fun j =>
        cost (C j) + crossCost (globalVariablePaths f V) (C j)).sum := by
  have hv : cost (globalVariablePaths f V) =
      ((List.range (variableBound f)).map fun v => cost (V v)).sum := by
    apply cost_flatMap_disjoint
    apply (show (List.range (variableBound f)).Nodup from List.nodup_range).imp_of_mem
    intro v w hv hw hne p hp q hq
    exact overlap_zero_of_graph_disjoint (formulaGraph_variable_edges_disjoint k hne)
      (hV v (List.mem_range.mp hv) p hp) (hV w (List.mem_range.mp hw) q hq)
  have hc : cost (globalClausePaths f C) =
      ((List.range (placeFormula [] f).length).map fun j => cost (C j)).sum := by
    apply cost_flatMap_disjoint
    apply (show (List.range (placeFormula [] f).length).Nodup from List.nodup_range).imp_of_mem
    intro i j hi hj hne p hp q hq
    exact overlap_zero_of_graph_disjoint
      (formulaGraph_clause_edges_disjoint hf (List.mem_range.mp hi) (List.mem_range.mp hj) hne)
      (hC i (List.mem_range.mp hi) p hp) (hC j (List.mem_range.mp hj) q hq)
  rw [cost_append,hv,hc,sum_map_add]
  rw [globalClausePaths,crossCost_flatMap_right]
  omega

theorem formulaGraph_budget_forces_zero_interaction {k : Nat} {f : CNF}
    (hf : BoundedOccurrence f) (V C : Nat → List (List Edge))
    (hV : ∀ v, v < variableBound f → ∀ p ∈ V v, p ⊆ placedVariableGraph k v)
    (hC : ∀ j, ∀ hj : j < (placeFormula [] f).length, ∀ p ∈ C j,
      p ⊆ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j])
    (hbase : ∀ j, j < (placeFormula [] f).length → 1 ≤ cost (C j))
    (hbudget : cost (globalVariablePaths f V ++ globalClausePaths f C) ≤ f.length) :
    (∀ v, v < variableBound f → cost (V v) = 0) ∧
    (∀ j, j < (placeFormula [] f).length →
      cost (C j) = 1 ∧ crossCost (globalVariablePaths f V) (C j) = 0) := by
  have hdec := formulaGraph_cost_decomposition hf V C hV hC
  rw [hdec] at hbudget
  let w := fun j => cost (C j) + crossCost (globalVariablePaths f V) (C j)
  have hpos : ∀ j ∈ List.range (placeFormula [] f).length, 1 ≤ w j := by
    intro j hj
    have h := hbase j (List.mem_range.mp hj)
    unfold w
    omega
  have hlen : (List.range (placeFormula [] f).length).length = f.length := by
    simp [placeFormula_length]
  have hlo := sum_map_le (List.range (placeFormula [] f).length) (fun _ => 1) w hpos
  rw [sum_map_const,Nat.mul_one,hlen] at hlo
  change f.length ≤ ((List.range (placeFormula [] f).length).map fun j =>
    cost (C j) + crossCost (globalVariablePaths f V) (C j)).sum at hlo
  have hvzero : ((List.range (variableBound f)).map fun v => cost (V v)).sum = 0 := by omega
  have hone := sum_map_eq_length_of_positive _ w hpos (by
    rw [hlen]
    change ((List.range (placeFormula [] f).length).map fun j =>
      cost (C j) + crossCost (globalVariablePaths f V) (C j)).sum ≤ f.length
    omega)
  constructor
  · intro v hv
    exact List.sum_eq_zero_iff_forall_eq_nat.mp hvzero _ (List.mem_map.mpr ⟨v,List.mem_range.mpr hv,rfl⟩)
  · intro j hj
    have h := hone j (List.mem_range.mpr hj)
    have hb := hbase j hj
    unfold w at h
    omega

end STACS2027.Oriented
