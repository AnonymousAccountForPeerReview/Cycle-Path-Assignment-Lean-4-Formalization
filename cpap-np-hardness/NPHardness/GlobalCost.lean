module

public import NPHardness.GlobalCycles
public import NPHardness.FamilyCost

/-! Exact cost decomposition of the concrete global gadget families. No
independence of variable/clause pairs is assumed: their interaction is kept
as an explicit nonnegative term for each clause. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def crossCost (ps qs : List (List Edge)) : Nat :=
  (ps.map fun p => (qs.map (overlap p)).sum).sum

theorem crossCost_nil_right (ps : List (List Edge)) : crossCost ps [] = 0 := by
  simp [crossCost]

theorem crossCost_append_right (ps qs rs : List (List Edge)) :
    crossCost ps (qs ++ rs) = crossCost ps qs + crossCost ps rs := by
  simp only [crossCost,List.map_append,List.sum_append,sum_map_add]

theorem cost_append (ps qs : List (List Edge)) :
    cost (ps ++ qs) = cost ps + cost qs + crossCost ps qs := by
  induction ps with
  | nil => simp [cost,crossCost]
  | cons p ps ih =>
    simp only [List.cons_append,cost,List.map_append,List.sum_append,ih,crossCost,List.map_cons,List.sum_cons]
    omega

theorem crossCost_zero_iff (ps qs : List (List Edge)) :
    crossCost ps qs = 0 ↔ ∀ p ∈ ps, ∀ q ∈ qs, overlap p q = 0 := by
  constructor
  · intro h p hp q hq
    have h' := List.sum_eq_zero_iff_forall_eq_nat.mp h _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
    exact List.sum_eq_zero_iff_forall_eq_nat.mp h' _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  · intro h
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro n hn
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hn
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro n hn
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hn
    exact h p hp q hq

theorem crossCost_flatMap_right {α : Type} (ps : List (List Edge))
    (xs : List α) (Q : α → List (List Edge)) :
    crossCost ps (xs.flatMap Q) = (xs.map fun x => crossCost ps (Q x)).sum := by
  induction xs with
  | nil => exact crossCost_nil_right _
  | cons x xs ih => simp only [List.flatMap_cons,crossCost_append_right,ih,List.map_cons,List.sum_cons]

theorem cost_flatMap_disjoint {α : Type} (xs : List α) (P : α → List (List Edge))
    (hd : xs.Pairwise (fun x y => ∀ p ∈ P x, ∀ q ∈ P y, overlap p q = 0)) :
    cost (xs.flatMap P) = (xs.map fun x => cost (P x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hh,ht⟩ := List.pairwise_cons.mp hd
    have hz : crossCost (P x) (xs.flatMap P) = 0 := by
      apply (crossCost_zero_iff _ _).mpr
      intro p hp q hq
      obtain ⟨y,hy,hqy⟩ := List.mem_flatMap.mp hq
      exact hh y hy p hp q hqy
    simp only [List.flatMap_cons,cost_append,hz,Nat.add_zero,ih ht,List.map_cons,List.sum_cons]

def globalVariablePaths (f : CNF) (V : Nat → List (List Edge)) : List (List Edge) :=
  (List.range (variableBound f)).flatMap V

def globalClausePaths (f : CNF) (C : Nat → List (List Edge)) : List (List Edge) :=
  (List.range (placeFormula [] f).length).flatMap C

/-- Costs inside different variable copies and inside different clause copies
add exactly. Every variable/clause interaction is charged to that clause. -/
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

theorem sum_map_eq_length_of_positive {α : Type} (xs : List α) (w : α → Nat)
    (hp : ∀ x ∈ xs, 1 ≤ w x) (hb : (xs.map w).sum ≤ xs.length) :
    ∀ x ∈ xs, w x = 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hp x (by simp)
    have hxs := sum_map_le xs (fun _ => 1) w (fun y hy => hp y (by simp [hy]))
    simp only [sum_map_const,Nat.mul_one] at hxs
    have hsum : w x + (xs.map w).sum ≤ xs.length + 1 := by simpa using hb
    have he : w x = 1 := by omega
    have ht := ih (fun y hy => hp y (by simp [hy])) (by omega)
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact he
    · exact ht y hy

/-- At budget m, the baseline cost of the m clauses leaves no cost for a
variable gadget or for a shared literal port. -/
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

end STACS2027
