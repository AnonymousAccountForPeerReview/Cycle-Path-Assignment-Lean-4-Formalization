module

public import Runtimes.BoundedCost.SearchPaths
public import Runtimes.BoundedCost.Compression
import Mathlib.Tactic

/-! First-success scans preserve witness correctness and test every encoded
branch path. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def firstSuccess {α β : Type*} (solve : α → Option β) : List α → Option β
  | [] => none
  | x :: xs => (solve x).orElse (fun _ => firstSuccess solve xs)

theorem firstSuccess_has {α β : Type*} (solve : α → Option β) (xs : List α) :
    (∃ answer, firstSuccess solve xs = some answer) ↔
      ∃ x ∈ xs, ∃ answer, solve x = some answer := by
  induction xs with
  | nil => simp [firstSuccess]
  | cons x xs ih =>
    cases hx : solve x <;> simp [firstSuccess, hx, ih]

theorem firstSuccess_some {α β : Type*} (solve : α → Option β) (xs : List α) (answer : β)
    (h : firstSuccess solve xs = some answer) : ∃ x ∈ xs, solve x = some answer := by
  induction xs with
  | nil => simp [firstSuccess] at h
  | cons x xs ih =>
    cases hx : solve x with
    | none =>
      have ht : firstSuccess solve xs = some answer := by simpa [firstSuccess, hx] using h
      obtain ⟨y, hy, hs⟩ := ih ht
      exact ⟨y, by simp [hy], hs⟩
    | some value =>
      have hv : value = answer := by simpa [firstSuccess, hx] using h
      exact ⟨x, by simp, by simpa [hv] using hx⟩

theorem firstSuccess_foldl {α β : Type*} (solve : α → Option β) (xs : List α) (initial : Option β) :
    xs.foldl (fun found x => found.orElse (fun _ => solve x)) initial =
      initial.orElse (fun _ => firstSuccess solve xs) := by
  induction xs generalizing initial with
  | nil => cases initial <;> rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    cases initial <;> cases hx : solve x <;> simp [firstSuccess, hx]

def encodedPathSearch (cut : LeastCutOperation) (τ : Assignment) (fuel : ℕ)
    (f : CNF) (required : List Literal) (budget : ℕ) : Option Assignment :=
  firstSuccess (fun word => annotatedPath cut τ (Poly.cfg 3 fuel word) f required budget)
    (List.range (3 ^ fuel))

theorem encodedPathSearch_has (cut : LeastCutOperation) (τ : Assignment) (fuel : ℕ)
    (f : CNF) (required : List Literal) (budget : ℕ) :
    HasSearchAnswer (encodedPathSearch cut τ fuel f required budget) ↔
      HasSearchAnswer (annotatedSearch cut τ fuel f required budget) := by
  rw [encodedPathSearch, HasSearchAnswer, firstSuccess_has,
    annotatedSearch_iff_encoded_path]
  simp only [List.mem_range, HasSearchAnswer]

theorem annotatedPath_sound (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) :
    ∀ choices f required budget, Clauses2 f → evalCNF τ f = true →
      ∀ σ, annotatedPath cut τ choices f required budget = some σ →
        unsatisfiedCount σ f ≤ budget ∧ Requires σ required := by
  intro choices
  induction choices with
  | nil => intro f required budget hf hτ σ h; simp [annotatedPath] at h
  | cons choice choices ih =>
    intro f required budget hf hτ σ h
    cases hd : cut f required with
    | none => simp [annotatedPath, hd] at h
    | some δ =>
      have hδ := (hcut f required hf hτ).2 δ hd
      by_cases hs : unsatisfiedCount δ f ≤ budget
      · simp [annotatedPath, hd, hs] at h
        subst σ
        exact ⟨hs, hδ.required⟩
      · by_cases hc : budget < cutCost τ δ f
        · simp [annotatedPath, hd, hs, hc] at h
        · cases hconf : findCutConflict τ δ f with
          | none => simp [annotatedPath, hd, hs, hc, hconf] at h
          | some clause =>
            have hm := (findCutConflict_some hconf).1
            obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf clause hm)
            simp only [annotatedPath, hd, hs, hc, hconf, ↓reduceIte] at h
            by_cases hz : choice = 0
            · by_cases hk : budget = 0
              · simp [hz, hk] at h
              · simp only [hz, hk, ↓reduceIte] at h
                have hf' : Clauses2 (f.erase [a, b]) :=
                  fun c hc => hf c (List.mem_of_mem_erase hc)
                have hτ' : evalCNF τ (f.erase [a, b]) = true :=
                  (evalCNF_iff τ _).mpr fun c hc =>
                    (evalCNF_iff τ f).mp hτ c (List.mem_of_mem_erase hc)
                obtain ⟨hcount, hrequired⟩ := ih _ required (budget - 1) hf' hτ' σ h
                refine ⟨?_, hrequired⟩
                rw [unsatisfiedCount_perm (List.perm_cons_erase hm) σ, unsatisfiedCount_cons]
                split <;> omega
            · by_cases ho : choice = 1
              · simp only [hz, ho, ↓reduceIte] at h
                obtain ⟨hcount, hrequired⟩ := ih f (a :: required) budget hf hτ σ h
                exact ⟨hcount, fun l hl => hrequired l (by simp [hl])⟩
              · by_cases ht : choice = 2
                · simp only [hz, ho, ht, ↓reduceIte] at h
                  obtain ⟨hcount, hrequired⟩ := ih f (b :: required) budget hf hτ σ h
                  exact ⟨hcount, fun l hl => hrequired l (by simp [hl])⟩
                · simp [hz, ho, ht] at h

theorem encodedPathSearch_sound (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) {f : CNF} (hf : Clauses2 f)
    (hτ : evalCNF τ f = true) (fuel : ℕ) (required : List Literal) (budget : ℕ)
    {σ : Assignment} (h : encodedPathSearch cut τ fuel f required budget = some σ) :
    unsatisfiedCount σ f ≤ budget ∧ Requires σ required := by
  obtain ⟨word, hw, hp⟩ := firstSuccess_some _ _ σ h
  exact annotatedPath_sound cut τ hcut _ f required budget hf hτ σ hp

theorem encodedPathSearch_correct (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) {f : CNF} (hf : Clauses2 f)
    (hτ : evalCNF τ f = true) (fuel : ℕ) (required : List Literal) (budget : ℕ)
    (hdepth : budget < fuel) :
    HasSearchAnswer (encodedPathSearch cut τ fuel f required budget) ↔
      AnnotatedAlmostSatisfiable f required budget := by
  rw [encodedPathSearch_has]
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨hc, hL⟩ := annotatedSearch_sound cut τ hcut fuel f required budget hf hτ σ hσ
    exact ⟨σ, hc, hL⟩
  · exact annotatedSearch_complete cut τ hcut fuel f required budget hf hτ (fun δ _ => by omega)

end STACS2027.Runtimes.BoundedCost
