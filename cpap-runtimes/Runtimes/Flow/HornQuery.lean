module

public import Runtimes.Flow.ReverseReach
public import Runtimes.TwoSatSpec
import Mathlib.Tactic

/-! # Residual cut membership decided by the verified 2-SAT phase -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open Complexity.SAT

/-- Residual closure, with one vertex forced in and the sink forced out. -/
def hornQuery {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) : CNF :=
  (List.finRange arcs).map (fun i =>
    [⟨(residualTail net (availableEdge flow i)).val, false⟩,
      ⟨(residualHead net (availableEdge flow i)).val, true⟩]) ++
    [[⟨v.val, true⟩, ⟨v.val, true⟩],
      [⟨net.sink.val, false⟩, ⟨net.sink.val, false⟩]]

theorem hornQuery_length {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) : (hornQuery net flow v).length = arcs + 2 := by
  simp [hornQuery]

theorem hornQuery_isTwoCNF {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) : TwoSat.IsTwoCNF nodes (hornQuery net flow v) := by
  intro clause hclause
  simp only [hornQuery, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hclause
  rcases hclause with ⟨i, _, rfl⟩ | rfl | rfl
  all_goals
    constructor
    · rfl
    · intro literal hliteral
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
      rcases hliteral with rfl | rfl
      all_goals exact Fin.isLt _

private theorem implication_true (a b : Bool) :
    (!a || b) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp

theorem hornQuery_semantics {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) (assignment : Assignment) :
    evalCNF assignment (hornQuery net flow v) = true ↔
      ResidualClosed net flow (fun w => assignment w.val) ∧
        assignment v.val = true ∧ assignment net.sink.val = false := by
  have himp : evalCNF assignment ((List.finRange arcs).map (fun i =>
      [⟨(residualTail net (availableEdge flow i)).val, false⟩,
       ⟨(residualHead net (availableEdge flow i)).val, true⟩])) = true ↔
      ResidualClosed net flow (fun w => assignment w.val) := by
    simp only [evalCNF, List.all_map, List.all_eq_true, List.mem_finRange, Function.comp_apply,
      evalClause, List.any_cons, List.any_nil, Bool.or_false,
      evalLiteral_negative, evalLiteral_positive, implication_true, forall_true_left]
    constructor
    · intro h edge hedge htail
      obtain ⟨i, reverse⟩ := edge
      have hreverse : reverse = flow i := hedge
      subst reverse
      exact h i htail
    · intro h i htail
      exact h (availableEdge flow i) rfl htail
  rw [hornQuery, evalCNF_append, Bool.and_eq_true, himp]
  simp [evalCNF, evalClause, evalLiteral]

/-- Extend a numbered Boolean region to the foundation's natural-number assignment. -/
def regionAssignment {nodes : ℕ} (region : Fin nodes → Bool) : Assignment :=
  fun x => if h : x < nodes then region ⟨x, h⟩ else false

@[simp] theorem regionAssignment_fin {nodes : ℕ} (region : Fin nodes → Bool) (v : Fin nodes) :
    regionAssignment region v.val = region v := by simp [regionAssignment, v.isLt]

theorem hornQuery_satisfiable_iff {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) :
    Satisfiable (hornQuery net flow v) ↔ maximalCutRegion net flow v = true := by
  constructor
  · rintro ⟨assignment, hassignment⟩
    obtain ⟨hc, hv, ht⟩ := (hornQuery_semantics net flow v assignment).mp hassignment
    exact residualClosed_subset_maximalCutRegion net flow hc ht v hv
  · intro hv
    refine ⟨regionAssignment (maximalCutRegion net flow), ?_⟩
    apply (hornQuery_semantics net flow v _).mpr
    have ht : maximalCutRegion net flow net.sink = false := by
      have hmem := reverseReachSet_complete net flow net.sink Relation.ReflTransGen.refl
      simp [maximalCutRegion, hmem]
    simpa only [regionAssignment_fin] using
      And.intro (maximalCutRegion_closed net flow) (And.intro hv ht)

/-- The verified linear-time 2-SAT decision bit is exactly maximal cut membership. -/
theorem hornQuery_decision {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) :
    TwoSat.okB nodes (TwoSat.codes (hornQuery net flow v)) = maximalCutRegion net flow v := by
  have h := (TwoSat.twoSat_correct (hornQuery_isTwoCNF net flow v)).1
  have heq : TwoSat.okB nodes (TwoSat.codes (hornQuery net flow v)) = true ↔
      maximalCutRegion net flow v = true := h.trans (hornQuery_satisfiable_iff net flow v)
  cases ha : TwoSat.okB nodes (TwoSat.codes (hornQuery net flow v)) <;>
    cases hb : maximalCutRegion net flow v <;> simp_all

end STACS2027.Runtimes.Flow
