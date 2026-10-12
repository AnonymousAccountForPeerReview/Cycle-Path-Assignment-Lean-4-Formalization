module

public import Runtimes.BoundedCost.PathControl
public import Runtimes.BoundedCost.SearchPaths
import Mathlib.Tactic

/-! The state transition followed by the uniform annotated-path RAM loop. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

inductive SearchPathState where
  | failed
  | answered (assignment : Assignment)
  | running (formula : CNF) (required : List Literal) (budget : ℕ)

def SearchPathState.live : SearchPathState → Bool
  | .running .. => true
  | _ => false

def SearchPathState.answer : SearchPathState → Option Assignment
  | .answered σ => some σ
  | _ => none

def annotatedPathStep (cut : LeastCutOperation) (τ : Assignment) :
    SearchPathState → ℕ → SearchPathState
  | .running f L k, choice =>
      match cut f L with
      | none => .failed
      | some δ =>
          if unsatisfiedCount δ f ≤ k then .answered δ
          else if k < cutCost τ δ f then .failed
          else match findCutConflict τ δ f with
            | some [a, b] =>
                if choice = 0 then
                  if k = 0 then .failed else .running (f.erase [a, b]) L (k - 1)
                else if choice = 1 then .running f (a :: L) k
                else if choice = 2 then .running f (b :: L) k else .failed
            | _ => .failed
  | state, _ => state

theorem annotatedPathStep_live (cut : LeastCutOperation) (τ : Assignment)
    (state : SearchPathState) (choice : ℕ) :
    livePathStep SearchPathState.live (annotatedPathStep cut τ) state choice =
      annotatedPathStep cut τ state choice := by
  cases state <;> rfl

theorem foldPath_failed (cut : LeastCutOperation) (τ : Assignment) (choices : List ℕ) :
    choices.foldl (annotatedPathStep cut τ) .failed = .failed := by
  induction choices with
  | nil => rfl
  | cons choice choices ih => simpa [annotatedPathStep] using ih

theorem foldPath_answered (cut : LeastCutOperation) (τ : Assignment)
    (choices : List ℕ) (σ : Assignment) :
    choices.foldl (annotatedPathStep cut τ) (.answered σ) = .answered σ := by
  induction choices with
  | nil => rfl
  | cons choice choices ih => simpa [annotatedPathStep] using ih

theorem foldPath_answer (cut : LeastCutOperation) (τ : Assignment) (choices : List ℕ) :
    ∀ f L k,
      (choices.foldl (annotatedPathStep cut τ) (.running f L k)).answer =
        annotatedPath cut τ choices f L k := by
  induction choices with
  | nil => intros; rfl
  | cons choice choices ih =>
    intro f L k
    cases hd : cut f L with
    | none => simp [annotatedPath, annotatedPathStep, hd, foldPath_failed, SearchPathState.answer]
    | some δ =>
      by_cases hs : unsatisfiedCount δ f ≤ k
      · simp [annotatedPath, annotatedPathStep, hd, hs, foldPath_answered, SearchPathState.answer]
      · by_cases hc : k < cutCost τ δ f
        · simp [annotatedPath, annotatedPathStep, hd, hs, hc, foldPath_failed, SearchPathState.answer]
        · cases hf : findCutConflict τ δ f with
          | none =>
            simp [annotatedPath, annotatedPathStep, hd, hs, hc, hf, foldPath_failed, SearchPathState.answer]
          | some c =>
            cases c with
            | nil => simp [annotatedPath, annotatedPathStep, hd, hs, hc, hf,
                foldPath_failed, SearchPathState.answer]
            | cons a tail =>
              cases tail with
              | nil => simp [annotatedPath, annotatedPathStep, hd, hs, hc, hf,
                  foldPath_failed, SearchPathState.answer]
              | cons b tail =>
                cases tail with
                | cons c tail => simp [annotatedPath, annotatedPathStep, hd, hs, hc, hf,
                    foldPath_failed, SearchPathState.answer]
                | nil =>
                  by_cases hz : choice = 0
                  · by_cases hk : k = 0
                    · have hs' : unsatisfiedCount δ f ≠ 0 := by omega
                      simp [annotatedPath, annotatedPathStep, hd, hs', hc, hf, hz, hk,
                        foldPath_failed, SearchPathState.answer]
                    · simpa [annotatedPath, annotatedPathStep, hd, hs, hc, hf, hz, hk] using
                        ih (f.erase [a, b]) L (k - 1)
                  · by_cases ho : choice = 1
                    · simpa [annotatedPath, annotatedPathStep, hd, hs, hc, hf, hz, ho] using
                        ih f (a :: L) k
                    · by_cases ht : choice = 2
                      · simpa [annotatedPath, annotatedPathStep, hd, hs, hc, hf, hz, ho, ht] using
                          ih f (b :: L) k
                      · simp [annotatedPath, annotatedPathStep, hd, hs, hc, hf, hz, ho, ht,
                          foldPath_failed, SearchPathState.answer]

theorem range_map_getD (digits : List ℕ) :
    (List.range digits.length).map (fun i => digits.getD i 0) = digits := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    exact RAM.getD_eq_getElem' (by simpa using hi)

theorem pathPrefix_answer (cut : LeastCutOperation) (τ : Assignment)
    (choices : List ℕ) (f : CNF) (L : List Literal) (k : ℕ) :
    (pathPrefix SearchPathState.live (annotatedPathStep cut τ)
      choices choices.length (.running f L k)).answer = annotatedPath cut τ choices f L k := by
  have hm := range_map_getD choices
  rw [← foldPath_answer cut τ choices f L k]
  unfold pathPrefix
  simp only [annotatedPathStep_live]
  rw [← List.foldl_map, hm]

end STACS2027.Runtimes.BoundedCost
