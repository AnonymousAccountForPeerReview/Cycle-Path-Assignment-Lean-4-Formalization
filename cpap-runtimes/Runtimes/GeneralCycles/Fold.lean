module

public import Runtimes.GeneralCycles.TupleLoop
public import Runtimes.GeneralCycles.Spec
import Mathlib.Tactic

/-! Ghost folds for the finite endpoint-index scans. Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

theorem foldTuples_eq {α : Type*} (N : ℕ) (F : α → List ℕ → α)
    (n : ℕ) (stem : List ℕ) (a : α) :
    foldTuples N F n stem a = ((tuples N n).map (stem ++ ·)).foldl F a := by
  induction n generalizing stem a with
  | zero => simp [foldTuples, tuples]
  | succ n ih =>
    simp only [foldTuples, tuples, List.map_flatMap, List.foldl_flatMap]
    congr 1
    funext a i
    rw [ih]
    simp only [List.map_map, Function.comp_def, List.foldl_map]
    congr 1
    funext a rest
    simp [List.append_assoc]

def Counterexample (g : Graph) (k : ℕ) (outer previous : List ℕ) : Prop :=
  Valid g k previous ∧ SameCycle (tupleLabels g previous) (tupleLabels g outer) ∧
    Earlier g outer previous

instance (g : Graph) (k : ℕ) (outer previous : List ℕ) :
    Decidable (Counterexample g k outer previous) := by
  unfold Counterexample
  infer_instance

def rejectStep (g : Graph) (k : ℕ) (outer : List ℕ) (b : Bool)
    (previous : List ℕ) : Bool := b && !decide (Counterexample g k outer previous)

theorem reject_fold_true (g : Graph) (k : ℕ) (outer : List ℕ)
    (previous : List (List ℕ)) (b : Bool) :
    previous.foldl (rejectStep g k outer) b = true ↔
      b = true ∧ ∀ i ∈ previous, ¬Counterexample g k outer i := by
  induction previous generalizing b with
  | nil => simp
  | cons i previous ih =>
    simp only [List.foldl_cons, ih, List.mem_cons, rejectStep,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro ⟨⟨hb, hi⟩, hall⟩
      exact ⟨hb, fun j hj => by rcases hj with rfl | hj; exact hi; exact hall j hj⟩
    · rintro ⟨hb, hall⟩
      exact ⟨⟨hb, hall i (Or.inl rfl)⟩, fun j hj => hall j (Or.inr hj)⟩

theorem rejection_result (g : Graph) (k : ℕ) (outer : List ℕ) :
    foldTuples (endpoints g).length (rejectStep g k outer) k []
      (decide (Valid g k outer)) = decide (Accepted g k outer) := by
  rw [foldTuples_eq]
  simp only [List.nil_append, List.map_id_fun']
  apply Bool.eq_iff_iff.mpr
  rw [reject_fold_true]
  simp only [decide_eq_true_eq, Accepted, Counterexample]
  constructor
  · rintro ⟨hv, hn⟩
    exact ⟨hv, fun i hi hvi hs he => hn i hi ⟨hvi, hs, he⟩⟩
  · rintro ⟨hv, hn⟩
    exact ⟨hv, fun i hi ⟨hvi, hs, he⟩ => hn i hi hvi hs he⟩

def outputStep (g : Graph) (k : ℕ) (cs : List Cycle) (indices : List ℕ) : List Cycle :=
  if Accepted g k indices then cs ++ [tupleLabels g indices] else cs

theorem output_fold (g : Graph) (k : ℕ) (indices : List (List ℕ)) (cs : List Cycle) :
    indices.foldl (outputStep g k) cs = cs ++
      (indices.filter fun i => decide (Accepted g k i)).map (tupleLabels g) := by
  induction indices generalizing cs with
  | nil => simp
  | cons i indices ih =>
    simp only [List.foldl_cons, outputStep]
    split_ifs with hi
    · rw [ih]
      simp [hi, List.append_assoc]
    · rw [ih]
      simp [hi]

theorem output_result (g : Graph) (k : ℕ) :
    foldTuples (endpoints g).length (outputStep g k) k [] [] = outputCycles g k := by
  rw [foldTuples_eq]
  simp [List.nil_append, List.map_id_fun', output_fold, outputCycles]

end STACS2027.Runtimes.GeneralCycles
