module

public import Runtimes.BoundedCost.SearchSemantics
public import Runtimes.BoundedCost.PathState
public import Runtimes.BoundedCost.Requirements
import Mathlib.Tactic

/-! The concrete node action implements the exact annotated-path transition.
Deleting a conflict clears the first active occurrence, including duplicates. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

theorem mem_activeOccurrences_true {α : Type*} {rows : List (Bool × α)} {c : α}
    (hc : c ∈ activeOccurrences rows) : (true, c) ∈ rows := by
  induction rows with
  | nil => simp [activeOccurrences] at hc
  | cons row rows ih =>
    rcases row with ⟨active, clause⟩
    cases ha : active
    · exact List.mem_cons_of_mem _ (ih (by simpa [activeOccurrences, ha] using hc))
    · rcases List.mem_cons.mp (by simpa [activeOccurrences, ha] using hc) with he | ht
      · subst clause; simp [ha]
      · exact List.mem_cons_of_mem _ (ih ht)

theorem findCutConflict_none_of_summary_zero (τ δ : Assignment) (rows : List (Bool × Clause))
    (hrows : ∀ row ∈ rows, row.2.length = 2)
    (hz : (summarizePrefix (searchRowsOf τ δ rows) rows.length).conflict = 0) :
    findCutConflict τ δ (activeOccurrences rows) = none := by
  apply List.find?_eq_none.mpr
  intro c hc hp
  have hm := mem_activeOccurrences_true hc
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  have hzero := (summarizePrefix_conflict_zero (searchRowsOf τ δ rows) rows.length).mp hz i hi
  rw [searchRowsOf_getD τ δ rows i hi, ← List.getElem_eq_getD (h := hi) default, he,
    rowConflict_searchRow τ δ true (hrows (true, c) hm)] at hzero
  simp only [Bool.true_and] at hzero
  rw [hp] at hzero
  contradiction

def nodeActionState (action : NodeAction) (δ : Assignment) (rows : List (Bool × Clause))
    (required : List Literal) (budget : ℕ) : SearchPathState :=
  match action with
  | .accept => .answered δ
  | .prune => .failed
  | .delete i => .running (activeOccurrences (disableOccurrence rows i)) required (budget - 1)
  | .force code => .running (activeOccurrences rows) (literalOfCode code :: required) budget

theorem nodeActionState_annotatedPathStep (cut : LeastCutOperation) (τ δ : Assignment)
    (rows : List (Bool × Clause)) (required : List Literal) (budget choice : ℕ)
    (hrows : ∀ row ∈ rows, row.2.length = 2)
    (hcut : cut (activeOccurrences rows) required = some δ) :
    nodeActionState (nodeAction (summarizePrefix (searchRowsOf τ δ rows) rows.length) budget choice)
      δ rows required budget =
      annotatedPathStep cut τ (.running (activeOccurrences rows) required budget) choice := by
  let summary := summarizePrefix (searchRowsOf τ δ rows) rows.length
  have hu : summary.unsatisfied = unsatisfiedCount δ (activeOccurrences rows) :=
    summarizePrefix_unsatisfied_semantic τ δ rows hrows
  have hc : summary.cut = cutCost τ δ (activeOccurrences rows) :=
    summarizePrefix_cut_semantic τ δ rows hrows
  change nodeActionState (nodeAction summary budget choice) δ rows required budget = _
  by_cases hs : summary.unsatisfied ≤ budget
  · simp [nodeAction, annotatedPathStep, hcut, hs, ← hu, nodeActionState]
  · by_cases hcost : budget < summary.cut
    · simp [nodeAction, annotatedPathStep, hcut, hs, hcost, ← hu, ← hc, nodeActionState]
    · by_cases hz : summary.conflict = 0
      · have hf := findCutConflict_none_of_summary_zero τ δ rows hrows hz
        simp [nodeAction, annotatedPathStep, hcut, hs, hcost, hz, hf, ← hu, ← hc, nodeActionState]
      · obtain ⟨a, b, hj, hrow, hf, hfirst, hsecond, herase⟩ :=
          summarizePrefix_conflict_semantic τ δ rows hrows hz
        change summary.firstLiteral = TwoSat.code a at hfirst
        change summary.secondLiteral = TwoSat.code b at hsecond
        change activeOccurrences (disableOccurrence rows (summary.conflict - 1)) =
          (activeOccurrences rows).erase [a, b] at herase
        by_cases hzero : choice = 0
        · by_cases hk : budget = 0
          · subst budget
            have hs0 : summary.unsatisfied ≠ 0 := by omega
            simp [nodeAction, annotatedPathStep, hcut, hs, hcost, hz, hf, hzero, hs0,
              ← hu, ← hc, nodeActionState, herase]
          · simp [nodeAction, annotatedPathStep, hcut, hs, hcost, hz, hf, hzero, hk,
              ← hu, ← hc, nodeActionState, herase]
        · by_cases hone : choice = 1
          · simp [nodeAction, annotatedPathStep, hcut, hs, hcost, hz, hf, hzero, hone,
              ← hu, ← hc, nodeActionState, hfirst, literalOfCode_code]
          · by_cases htwo : choice = 2 <;>
              simp [nodeAction, annotatedPathStep, hcut, hs, hcost, hz, hf, hzero, hone, htwo,
                ← hu, ← hc, nodeActionState, hsecond, literalOfCode_code]

end STACS2027.Runtimes.BoundedCost
