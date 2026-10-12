module

public import Runtimes.BoundedCost.SearchRows
public import Runtimes.BoundedCost.ContractionRows
import Mathlib.Tactic

/-! The concrete readonly scanner reports the exact false-occurrence count,
cut cost, and first active conflict of the current dense occurrence mask. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def searchRowOf (τ δ : Assignment) : Bool × Clause → SearchRow
  | (active, [a, b]) =>
      ⟨TwoSat.code a, TwoSat.code b, active, evalLiteral δ a, evalLiteral δ b,
        evalLiteral τ a, evalLiteral τ b⟩
  | _ => default

def searchRowsOf (τ δ : Assignment) (rows : List (Bool × Clause)) : List SearchRow :=
  rows.map (searchRowOf τ δ)

@[simp] theorem searchRowsOf_length (τ δ : Assignment) (rows : List (Bool × Clause)) :
    (searchRowsOf τ δ rows).length = rows.length := by simp [searchRowsOf]

theorem searchRowsOf_getD (τ δ : Assignment) (rows : List (Bool × Clause)) (i : ℕ)
    (hi : i < rows.length) :
    (searchRowsOf τ δ rows).getD i default = searchRowOf τ δ (rows.getD i default) := by
  simp [searchRowsOf, List.getD_eq_getElem?_getD, hi]

theorem countP_getD_range {α : Type*} (rows : List α) (fallback : α) (p : α → Bool) :
    (List.range rows.length).countP (fun i => p (rows.getD i fallback)) = rows.countP p := by
  have h := congrArg (List.countP p) (map_getD_range rows fallback)
  simpa only [List.countP_map, Function.comp_def] using h

theorem rowConflict_searchRow (τ δ : Assignment) (active : Bool) {c : Clause}
    (hc : c.length = 2) :
    rowConflict (searchRowOf τ δ (active, c)) =
      (active && !(evalClause δ c) && c.all (evalLiteral τ)) := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hc
  simp [searchRowOf, rowConflict, rowUnsatisfied, evalClause, Bool.and_assoc]

theorem searchRows_unsatisfied (τ δ : Assignment) (rows : List (Bool × Clause))
    (hrows : ∀ row ∈ rows, row.2.length = 2) :
    (searchRowsOf τ δ rows).countP rowUnsatisfied = unsatisfiedCount δ (activeOccurrences rows) := by
  induction rows with
  | nil => simp [searchRowsOf, activeOccurrences]
  | cons row rows ih =>
    rcases row with ⟨active, c⟩
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hrows (active, c) (by simp))
    have ht : ∀ row ∈ rows, row.2.length = 2 := fun row hr => hrows row (by simp [hr])
    have hi := ih ht
    cases ha : active <;> cases hf : evalLiteral δ a <;> cases hs : evalLiteral δ b <;>
      simpa [searchRowsOf, searchRowOf, activeOccurrences, rowUnsatisfied, unsatisfiedCount_cons,
        evalClause, ha, hf, hs, Nat.add_comm] using hi

theorem searchRows_cut (τ δ : Assignment) (rows : List (Bool × Clause))
    (hrows : ∀ row ∈ rows, row.2.length = 2) :
    (searchRowsOf τ δ rows).countP rowCut = cutCost τ δ (activeOccurrences rows) := by
  induction rows with
  | nil => simp [searchRowsOf, activeOccurrences, cutCost]
  | cons row rows ih =>
    rcases row with ⟨active, c⟩
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hrows (active, c) (by simp))
    have ht : ∀ row ∈ rows, row.2.length = 2 := fun row hr => hrows row (by simp [hr])
    have hi := ih ht
    cases ha : active <;> cases hf : evalLiteral δ a <;> cases hs : evalLiteral δ b <;>
      cases hr : evalLiteral τ a <;> cases hv : evalLiteral τ b <;>
      simpa [searchRowsOf, searchRowOf, activeOccurrences, rowCut, rowUnsatisfied, cutCost,
        cutClause, evalClause, ha, hf, hs, hr, hv, Nat.add_comm] using hi

theorem summarizePrefix_unsatisfied_semantic (τ δ : Assignment) (rows : List (Bool × Clause))
    (hrows : ∀ row ∈ rows, row.2.length = 2) :
    (summarizePrefix (searchRowsOf τ δ rows) rows.length).unsatisfied =
      unsatisfiedCount δ (activeOccurrences rows) := by
  rw [summarizePrefix_unsatisfied, ← searchRowsOf_length τ δ rows,
    countP_getD_range, searchRows_unsatisfied τ δ rows hrows]

theorem summarizePrefix_cut_semantic (τ δ : Assignment) (rows : List (Bool × Clause))
    (hrows : ∀ row ∈ rows, row.2.length = 2) :
    (summarizePrefix (searchRowsOf τ δ rows) rows.length).cut =
      cutCost τ δ (activeOccurrences rows) := by
  rw [summarizePrefix_cut, ← searchRowsOf_length τ δ rows,
    countP_getD_range, searchRows_cut τ δ rows hrows]

theorem find_activeOccurrence_first {α : Type*} (rows : List (Bool × α)) (p : α → Bool)
    (i : ℕ) (value : α) (hi : i < rows.length) (hrow : rows[i] = (true, value))
    (hp : p value = true)
    (hfirst : ∀ j, (hj : j < i) → ((rows[j]'(by omega)).1 && p (rows[j]'(by omega)).2) = false) :
    (activeOccurrences rows).find? p = some value := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    rcases row with ⟨active, head⟩
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, Prod.mk.injEq] at hrow
      rcases hrow with ⟨rfl, rfl⟩
      simp [activeOccurrences, hp]
    | succ i =>
      have hi' : i < rows.length := by simpa using hi
      have hr' : rows[i] = (true, value) := by simpa using hrow
      have hf' : ∀ j, (hj : j < i) →
          ((rows[j]'(by omega)).1 && p (rows[j]'(by omega)).2) = false := by
        intro j hj
        simpa using hfirst (j + 1) (by omega)
      have hhead := hfirst 0 (by omega)
      have ht := ih i hi' hr' hf'
      cases ha : active
      · simpa [activeOccurrences, ha] using ht
      · have hfalse : p head = false := by simpa [ha] using hhead
        simpa [activeOccurrences, ha, hfalse] using ht

/-- The first concrete occurrence index matches the search's first conflict;
clearing it deletes exactly the first active occurrence of that clause. -/
theorem summarizePrefix_conflict_semantic (τ δ : Assignment) (rows : List (Bool × Clause))
    (hrows : ∀ row ∈ rows, row.2.length = 2)
    (hconflict : (summarizePrefix (searchRowsOf τ δ rows) rows.length).conflict ≠ 0) :
    let summary := summarizePrefix (searchRowsOf τ δ rows) rows.length
    let j := summary.conflict - 1
    ∃ a b : Literal, ∃ hj : j < rows.length,
      rows[j] = (true, [a, b]) ∧
      findCutConflict τ δ (activeOccurrences rows) = some [a, b] ∧
      summary.firstLiteral = TwoSat.code a ∧ summary.secondLiteral = TwoSat.code b ∧
      activeOccurrences (disableOccurrence rows j) = (activeOccurrences rows).erase [a, b] := by
  dsimp only
  let summary := summarizePrefix (searchRowsOf τ δ rows) rows.length
  let j := summary.conflict - 1
  obtain ⟨hj, hconf, hfirst, hsecond, hearlier⟩ :=
    summarizePrefix_conflict_witness (searchRowsOf τ δ rows) rows.length hconflict
  change j < rows.length at hj
  have hm := hrows rows[j] (List.getElem_mem hj)
  rcases he : rows[j] with ⟨active, clause⟩
  rw [he] at hm
  obtain ⟨a, b, hc⟩ := List.length_eq_two.mp hm
  change clause = [a, b] at hc
  subst clause
  have hget : (searchRowsOf τ δ rows).getD j default = searchRowOf τ δ (active, [a, b]) := by
    rw [searchRowsOf_getD τ δ rows j hj, ← List.getElem_eq_getD (h := hj) default, he]
  rw [hget, rowConflict_searchRow τ δ active (by simp)] at hconf
  have hactive : active = true := by cases ha : active <;> simp_all
  subst active
  have hp : (!(evalClause δ [a, b]) && [a, b].all (evalLiteral τ)) = true := by
    simpa using hconf
  have hf : ∀ i, (hi : i < j) →
      ((rows[i]'(by omega)).1 && (!(evalClause δ (rows[i]'(by omega)).2) &&
        (rows[i]'(by omega)).2.all (evalLiteral τ))) = false := by
    intro i hi
    have hil : i < rows.length := by omega
    have hc := hrows rows[i] (List.getElem_mem hil)
    have hrow := hearlier i hi
    rw [searchRowsOf_getD τ δ rows i hil, ← List.getElem_eq_getD (h := hil) default,
      rowConflict_searchRow τ δ (rows[i]).1 hc] at hrow
    simpa only [Bool.and_assoc] using hrow
  have hfind := find_activeOccurrence_first rows
    (fun c => !(evalClause δ c) && c.all (evalLiteral τ)) j [a, b] hj he hp hf
  have hsame : ∀ i, (hi : i < j) → rows[i]'(by omega) ≠ (true, [a, b]) := by
    intro i hi h
    have hfalse := hf i hi
    rw [h] at hfalse
    simp only [Bool.true_and, hp, Bool.true_eq_false] at hfalse
  have herase := activeOccurrences_disable_first rows j [a, b] hj he hsame
  refine ⟨a, b, hj, he, hfind, ?_, ?_, ?_⟩
  · rw [hget] at hfirst
    simpa only [searchRowOf] using hfirst
  · rw [hget] at hsecond
    simpa only [searchRowOf] using hsecond
  · simpa only [List.erase_eq_eraseP', beq_eq_decide] using herase

end STACS2027.Runtimes.BoundedCost
