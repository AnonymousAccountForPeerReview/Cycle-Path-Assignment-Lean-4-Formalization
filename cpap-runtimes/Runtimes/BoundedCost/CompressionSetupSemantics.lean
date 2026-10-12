module

public import Runtimes.BoundedCost.CompressionSetupRAM
public import Runtimes.BoundedCost.ContractionRows
public import Runtimes.BoundedCost.Iterative
import Mathlib.Tactic

/-! The compression setup preserves occurrence order, partitions the processed
prefix, and packs at most one additional false clause beyond the old budget. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def setupRowOf (τ : Assignment) : Clause → CompressionSetupRow
  | [a, b] => ⟨TwoSat.code a, TwoSat.code b, evalLiteral τ a, evalLiteral τ b⟩
  | _ => default

def setupRowsOf (τ : Assignment) (f : CNF) : List CompressionSetupRow := f.map (setupRowOf τ)

def clauseCodePair : Clause → ℕ × ℕ
  | [a, b] => (TwoSat.code a, TwoSat.code b)
  | _ => (0, 0)

@[simp] theorem setupRowsOf_length (τ : Assignment) (f : CNF) :
    (setupRowsOf τ f).length = f.length := by simp [setupRowsOf]

theorem setupRowOf_true (τ : Assignment) {c : Clause} (hc : c.length = 2) :
    setupRowTrue (setupRowOf τ c) = evalClause τ c := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hc
  simp [setupRowTrue, setupRowOf, evalClause]

theorem setupRowsOf_getD (τ : Assignment) (f : CNF) (i : ℕ) (hi : i < f.length) :
    (setupRowsOf τ f).getD i default = setupRowOf τ (f.getD i []) := by
  simp [setupRowsOf, List.getD_eq_getElem?_getD, hi]

theorem range_filterMap_cutoff {α : Type*} (count processed : ℕ) (g : ℕ → Option α)
    (hp : processed ≤ count) :
    (List.range count).filterMap (fun i => if i < processed then g i else none) =
      (List.range processed).filterMap g := by
  induction count generalizing processed with
  | zero =>
    have hz : processed = 0 := by omega
    subst processed
    rfl
  | succ count ih =>
    by_cases h : processed ≤ count
    · rw [List.range_succ, List.filterMap_append, ih processed h]
      simp [show ¬count < processed by omega]
    · have he : processed = count + 1 := by omega
      subst processed
      apply List.filterMap_congr
      intro i hi
      simp [List.mem_range.mp hi]

theorem map_getD_range_take {α : Type*} (rows : List α) (fallback : α) (processed : ℕ)
    (hp : processed ≤ rows.length) :
    (List.range processed).map (fun i => rows.getD i fallback) = rows.take processed := by
  have h := congrArg (List.take processed) (map_getD_range rows fallback)
  simpa only [← List.map_take, List.take_range, Nat.min_eq_left hp] using h

theorem setupSpecialPrefix_take (rows : List CompressionSetupRow) (processed : ℕ)
    (hp : processed ≤ rows.length) :
    setupSpecialPrefix rows processed rows.length =
      (rows.take processed).filterMap (fun row =>
        if setupRowTrue row = false then some (row.first, row.second) else none) := by
  let g := fun i => if setupRowTrue (rows.getD i default) = false then
    some ((rows.getD i default).first, (rows.getD i default).second) else none
  have hcut := range_filterMap_cutoff rows.length processed g hp
  have hmap := congrArg (List.filterMap (fun row : CompressionSetupRow =>
    if setupRowTrue row = false then some (row.first, row.second) else none))
    (map_getD_range_take rows default processed hp)
  rw [List.filterMap_map] at hmap
  calc
    setupSpecialPrefix rows processed rows.length =
        (List.range rows.length).filterMap (fun i => if i < processed then g i else none) := by
      apply List.filterMap_congr
      intro i hi
      simp only [setupSpecialPrefix, g]
      by_cases hp : i < processed <;> simp [hp]
    _ = (List.range processed).filterMap g := hcut
    _ = _ := hmap

theorem setupRows_filterMap_semantic (τ : Assignment) (f : CNF) (hf : Clauses2 f) :
    f.filterMap (fun c => if setupRowTrue (setupRowOf τ c) = false then
      some ((setupRowOf τ c).first, (setupRowOf τ c).second) else none) =
      (f.filter (fun c => !(evalClause τ c))).map clauseCodePair := by
  induction f with
  | nil => simp
  | cons c rest ih =>
    have hc : c.length = 2 := hf c (by simp)
    have ht : Clauses2 rest := fun c hc => hf c (by simp [hc])
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hc
    simp only [List.filterMap_cons, List.filter_cons]
    rw [ih ht]
    cases ha : evalLiteral τ a <;> cases hb : evalLiteral τ b <;>
      simp [setupRowOf, setupRowTrue, evalClause, clauseCodePair, ha, hb]

theorem setupSpecialPrefix_semantic (τ : Assignment) (f : CNF) (processed : ℕ)
    (hf : Clauses2 f) (hp : processed ≤ f.length) :
    setupSpecialPrefix (setupRowsOf τ f) processed f.length =
      ((f.take processed).filter (fun c => !(evalClause τ c))).map clauseCodePair := by
  rw [← setupRowsOf_length τ f, setupSpecialPrefix_take _ _ (by simpa using hp)]
  rw [setupRowsOf, ← List.map_take, List.filterMap_map]
  exact setupRows_filterMap_semantic τ (f.take processed)
    (fun c hc => hf c (List.mem_of_mem_take hc))

theorem setupSpecialPrefix_count (τ : Assignment) (f : CNF) (processed : ℕ)
    (hf : Clauses2 f) (hp : processed ≤ f.length) :
    (setupSpecialPrefix (setupRowsOf τ f) processed f.length).length =
      unsatisfiedCount τ (f.take processed) := by
  rw [setupSpecialPrefix_semantic τ f processed hf hp]
  simp [unsatisfiedCount, List.countP_eq_length_filter]

theorem compression_trigger_new_false (τ : Assignment) (f : CNF) (c : Clause) (k : ℕ)
    (hold : unsatisfiedCount τ f ≤ k) (hnew : k < unsatisfiedCount τ (f ++ [c])) :
    evalClause τ c = false := by
  rw [unsatisfiedCount_append, unsatisfiedCount_cons] at hnew
  cases h : evalClause τ c <;> simp [h] at hnew ⊢ <;> omega

theorem compression_trigger_false_count (τ : Assignment) (f : CNF) (c : Clause) (k : ℕ)
    (hold : unsatisfiedCount τ f ≤ k) : unsatisfiedCount τ (f ++ [c]) ≤ k + 1 := by
  rw [unsatisfiedCount_append, unsatisfiedCount_cons]
  cases h : evalClause τ c <;> simp [h] <;> omega

theorem setupSpecialPrefix_compression (τ : Assignment) (original old : CNF) (c : Clause)
    (processed k : ℕ) (hf : Clauses2 original) (hp : processed ≤ original.length)
    (hprefix : original.take processed = old ++ [c])
    (hold : unsatisfiedCount τ old ≤ k) (hnew : k < unsatisfiedCount τ (old ++ [c])) :
    setupSpecialPrefix (setupRowsOf τ original) processed original.length =
      (compressionSpecial τ old c).map clauseCodePair ∧
      (setupSpecialPrefix (setupRowsOf τ original) processed original.length).length ≤ k + 1 := by
  have hc := compression_trigger_new_false τ old c k hold hnew
  constructor
  · rw [setupSpecialPrefix_semantic τ original processed hf hp, hprefix]
    simp [compressionSpecial, List.filter_append, hc]
  · rw [setupSpecialPrefix_count τ original processed hf hp, hprefix]
    exact compression_trigger_false_count τ old c k hold

theorem activeOccurrences_map {α β : Type*} (xs : List α) (p : α → Bool) (value : α → β) :
    activeOccurrences (xs.map (fun x => (p x, value x))) =
      xs.filterMap (fun x => if p x then some (value x) else none) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [activeOccurrences, hp, ih]

def setupOccurrenceMask (τ : Assignment) (f : CNF) (processed : ℕ) : List (Bool × Clause) :=
  (List.range f.length).map fun i =>
    (decide (i < processed) && evalClause τ (f.getD i []), f.getD i [])

theorem setupOccurrenceMask_active (τ : Assignment) (f : CNF) (processed : ℕ)
    (hp : processed ≤ f.length) :
    activeOccurrences (setupOccurrenceMask τ f processed) = (f.take processed).filter (evalClause τ) := by
  rw [setupOccurrenceMask, activeOccurrences_map]
  let g := fun i => if evalClause τ (f.getD i []) then some (f.getD i []) else none
  have hcut := range_filterMap_cutoff f.length processed g hp
  have hmap := congrArg (List.filterMap (Option.guard (evalClause τ ·)))
    (map_getD_range_take f [] processed hp)
  rw [List.filterMap_map, List.filterMap_eq_filter] at hmap
  calc
    (List.range f.length).filterMap (fun i =>
      if decide (i < processed) && evalClause τ (f.getD i []) then some (f.getD i []) else none) =
        (List.range f.length).filterMap (fun i => if i < processed then g i else none) := by
      apply List.filterMap_congr
      intro i hi
      by_cases h : i < processed <;> simp [h, g]
    _ = (List.range processed).filterMap g := hcut
    _ = _ := by simpa only [Function.comp_def, Option.guard, g] using hmap

theorem setupActiveValue_semantic (τ : Assignment) (f : CNF) (processed i : ℕ)
    (hf : Clauses2 f) (hi : i < f.length) :
    setupActiveValue (setupRowsOf τ f) processed i =
      if i < processed ∧ evalClause τ (f.getD i []) = true then 1 else 0 := by
  have hc : (f.getD i []).length = 2 := by
    rw [← List.getElem_eq_getD (h := hi) []]
    exact hf f[i] (List.getElem_mem hi)
  simp only [setupActiveValue, setupRowsOf_getD τ f i hi, setupRowOf_true τ hc]

theorem setupOccurrenceMask_compressionBase (τ : Assignment) (original old : CNF) (c : Clause)
    (processed k : ℕ) (hp : processed ≤ original.length)
    (hprefix : original.take processed = old ++ [c])
    (hold : unsatisfiedCount τ old ≤ k) (hnew : k < unsatisfiedCount τ (old ++ [c])) :
    activeOccurrences (setupOccurrenceMask τ original processed) = compressionBase τ old := by
  have hc := compression_trigger_new_false τ old c k hold hnew
  rw [setupOccurrenceMask_active τ original processed hp, hprefix]
  simp [compressionBase, List.filter_append, hc]

end STACS2027.Runtimes.BoundedCost
