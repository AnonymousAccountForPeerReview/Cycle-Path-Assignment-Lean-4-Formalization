module

public import Runtimes.BoundedCost.SearchScan
import Mathlib.Tactic

/-! Exact occurrence counts and first-conflict information obtained by the
concrete readonly search scanner. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def rowUnsatisfied (row : SearchRow) : Bool :=
  row.active && !(row.firstTruth || row.secondTruth)

def rowCut (row : SearchRow) : Bool :=
  rowUnsatisfied row && !(row.firstReference && row.secondReference)

def rowConflict (row : SearchRow) : Bool :=
  rowUnsatisfied row && row.firstReference && row.secondReference

theorem summarizeRow_unsatisfied (i : ℕ) (row : SearchRow) (state : SearchSummary) :
    (summarizeRow i row state).unsatisfied =
      state.unsatisfied + (if rowUnsatisfied row then 1 else 0) := by
  simp only [summarizeRow, rowUnsatisfied]
  split_ifs <;> simp_all

theorem summarizeRow_cut (i : ℕ) (row : SearchRow) (state : SearchSummary) :
    (summarizeRow i row state).cut = state.cut + (if rowCut row then 1 else 0) := by
  cases ha : row.active <;> cases ht : row.firstTruth <;> cases hu : row.secondTruth <;>
    cases hr : row.firstReference <;> cases hv : row.secondReference <;>
    simp [summarizeRow, rowUnsatisfied, rowCut, ha, ht, hu, hr, hv]
  split_ifs <;> rfl

theorem summarizePrefix_unsatisfied (rows : List SearchRow) (count : ℕ) :
    (summarizePrefix rows count).unsatisfied =
      (List.range count).countP (fun i => rowUnsatisfied (rows.getD i default)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [summarizePrefix_succ, summarizeRow_unsatisfied, ih]
    simp [List.range_succ]

theorem summarizePrefix_cut (rows : List SearchRow) (count : ℕ) :
    (summarizePrefix rows count).cut =
      (List.range count).countP (fun i => rowCut (rows.getD i default)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [summarizePrefix_succ, summarizeRow_cut, ih]
    simp [List.range_succ]

theorem summarizeRow_conflict (i : ℕ) (row : SearchRow) (state : SearchSummary) :
    (summarizeRow i row state).conflict =
      if state.conflict = 0 ∧ rowConflict row then i + 1 else state.conflict := by
  cases ha : row.active <;> cases ht : row.firstTruth <;> cases hu : row.secondTruth <;>
    cases hr : row.firstReference <;> cases hv : row.secondReference <;>
    simp [summarizeRow, rowUnsatisfied, rowConflict, ha, ht, hu, hr, hv]
  split_ifs <;> rfl

theorem summarizePrefix_conflict_zero (rows : List SearchRow) (count : ℕ) :
    (summarizePrefix rows count).conflict = 0 ↔
      ∀ i < count, rowConflict (rows.getD i default) = false := by
  induction count with
  | zero =>
    constructor
    · intro _ i hi; omega
    · intro _; rfl
  | succ count ih =>
    have hstep :
        (summarizeRow count (rows.getD count default) (summarizePrefix rows count)).conflict = 0 ↔
          (summarizePrefix rows count).conflict = 0 ∧
            rowConflict (rows.getD count default) = false := by
      rw [summarizeRow_conflict]
      by_cases hz : (summarizePrefix rows count).conflict = 0 <;>
        cases hr : rowConflict (rows.getD count default) <;> simp [hz, hr]
    rw [summarizePrefix_succ, hstep, ih]
    constructor
    · rintro ⟨hall, hlast⟩ i hi
      by_cases he : i = count
      · simpa [he] using hlast
      · exact hall i (by omega)
    · intro hall
      exact ⟨fun i hi => hall i (by omega), hall count (by omega)⟩

theorem summarizePrefix_conflict_le (rows : List SearchRow) (count : ℕ) :
    (summarizePrefix rows count).conflict ≤ count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [summarizePrefix_succ, summarizeRow_conflict]
    split_ifs <;> omega

theorem summarizePrefix_conflict_witness (rows : List SearchRow) (count : ℕ)
    (h : (summarizePrefix rows count).conflict ≠ 0) :
    let j := (summarizePrefix rows count).conflict - 1
    j < count ∧ rowConflict (rows.getD j default) = true ∧
      (summarizePrefix rows count).firstLiteral = (rows.getD j default).first ∧
      (summarizePrefix rows count).secondLiteral = (rows.getD j default).second ∧
      ∀ i < j, rowConflict (rows.getD i default) = false := by
  induction count with
  | zero => exact False.elim (h rfl)
  | succ count ih =>
    by_cases hz : (summarizePrefix rows count).conflict = 0
    · have hr : rowConflict (rows.getD count default) = true := by
        rw [summarizePrefix_succ, summarizeRow_conflict] at h
        simpa [hz] using h
      have hs : summarizeRow count (rows.getD count default) (summarizePrefix rows count) =
          { (summarizePrefix rows count) with
            unsatisfied := (summarizePrefix rows count).unsatisfied + 1
            conflict := count + 1
            firstLiteral := (rows.getD count default).first
            secondLiteral := (rows.getD count default).second } := by
        cases ha : (rows.getD count default).active <;>
          cases ht : (rows.getD count default).firstTruth <;>
          cases hu : (rows.getD count default).secondTruth <;>
          cases hf : (rows.getD count default).firstReference <;>
          cases hg : (rows.getD count default).secondReference <;>
          simp_all [rowConflict, rowUnsatisfied, summarizeRow]
      simp only [summarizePrefix_succ, hs, Nat.add_sub_cancel, Nat.lt_succ_self,
        true_and, hr]
      exact (summarizePrefix_conflict_zero rows count).mp hz
    · have hm := ih hz
      have hs : summarizeRow count (rows.getD count default) (summarizePrefix rows count) =
          if rowUnsatisfied (rows.getD count default) then
            if (rows.getD count default).firstReference &&
                (rows.getD count default).secondReference then
              { (summarizePrefix rows count) with
                unsatisfied := (summarizePrefix rows count).unsatisfied + 1 }
            else { (summarizePrefix rows count) with
                unsatisfied := (summarizePrefix rows count).unsatisfied + 1
                cut := (summarizePrefix rows count).cut + 1 }
          else summarizePrefix rows count := by
        simp [summarizeRow, rowUnsatisfied, hz]
      rw [summarizePrefix_succ, hs]
      split_ifs <;> simpa only using ⟨by omega, hm.2⟩

end STACS2027.Runtimes.BoundedCost
