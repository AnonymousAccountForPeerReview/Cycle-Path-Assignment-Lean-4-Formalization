module

public import Runtimes.BoundedCost.Search
public import Outerplanar.Algo.Digits
import Mathlib.Tactic

/-! A bounded annotated search can be performed by scanning ternary branch paths.
Each path is followed for at most its length, with early success and pruning. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def HasSearchAnswer (answer : Option Assignment) : Prop := ∃ σ, answer = some σ

theorem hasSearchAnswer_orElse (left right : Option Assignment) :
    HasSearchAnswer (left.orElse (fun _ => right)) ↔
      HasSearchAnswer left ∨ HasSearchAnswer right := by
  cases left <;> simp [HasSearchAnswer]

theorem exists_valid_choices_succ (fuel : ℕ) (P : List ℕ → Prop) :
    (∃ choices, choices.length = fuel + 1 ∧ (∀ d ∈ choices, d < 3) ∧ P choices) ↔
      ∃ choice < 3, ∃ choices, choices.length = fuel ∧
        (∀ d ∈ choices, d < 3) ∧ P (choice :: choices) := by
  constructor
  · rintro ⟨choices, hl, hv, hp⟩
    cases choices with
    | nil => simp at hl
    | cons choice choices =>
      exact ⟨choice, hv choice (by simp), choices, by simpa using hl,
        fun d hd => hv d (by simp [hd]), hp⟩
  · rintro ⟨choice, hc, choices, hl, hv, hp⟩
    refine ⟨choice :: choices, by simp [hl], ?_, hp⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hv d hd

/-- Follow one branch vector. Zero deletes the conflict occurrence, one forces its
first literal, and two forces its second literal. -/
def annotatedPath (cut : LeastCutOperation) (τ : Assignment) :
    List ℕ → CNF → List Literal → ℕ → Option Assignment
  | [], _, _, _ => none
  | choice :: choices, f, L, k =>
      match cut f L with
      | none => none
      | some δ =>
          if unsatisfiedCount δ f ≤ k then some δ
          else if k < cutCost τ δ f then none
          else match findCutConflict τ δ f with
            | some [a, b] =>
                if choice = 0 then
                  if k = 0 then none else annotatedPath cut τ choices (f.erase [a, b]) L (k - 1)
                else if choice = 1 then annotatedPath cut τ choices f (a :: L) k
                else if choice = 2 then annotatedPath cut τ choices f (b :: L) k else none
            | _ => none

theorem annotatedSearch_iff_path (cut : LeastCutOperation) (τ : Assignment) :
    ∀ fuel f L k, HasSearchAnswer (annotatedSearch cut τ fuel f L k) ↔
      ∃ choices, choices.length = fuel ∧ (∀ d ∈ choices, d < 3) ∧
        HasSearchAnswer (annotatedPath cut τ choices f L k) := by
  intro fuel
  induction fuel with
  | zero => intro f L k; simp [HasSearchAnswer, annotatedSearch, annotatedPath]
  | succ fuel ih =>
    intro f L k
    rw [exists_valid_choices_succ]
    cases hd : cut f L with
    | none => simp [annotatedSearch, hd, annotatedPath, HasSearchAnswer]
    | some δ =>
      by_cases hs : unsatisfiedCount δ f ≤ k
      · constructor
        · intro _
          refine ⟨0, by decide, List.replicate fuel 0, by simp, ?_, ?_⟩
          · intro d hd; rw [(List.mem_replicate.mp hd).2]; decide
          · simp [annotatedPath, hd, hs, HasSearchAnswer]
        · intro _; exact ⟨δ, by simp [annotatedSearch, hd, hs]⟩
      · by_cases hb : k < cutCost τ δ f
        · simp [annotatedSearch, hd, hs, hb, annotatedPath, HasSearchAnswer]
        · cases hc : findCutConflict τ δ f with
          | none => simp [annotatedSearch, hd, hs, hb, hc, annotatedPath, HasSearchAnswer]
          | some c =>
            cases c with
            | nil => simp [annotatedSearch, hd, hs, hb, hc, annotatedPath, HasSearchAnswer]
            | cons a tail =>
              cases tail with
              | nil => simp [annotatedSearch, hd, hs, hb, hc, annotatedPath, HasSearchAnswer]
              | cons b tail =>
                cases tail with
                | cons d tail =>
                  simp [annotatedSearch, hd, hs, hb, hc, annotatedPath, HasSearchAnswer]
                | nil =>
                  rw [annotatedSearch, hd]
                  simp only [hs, hb, hc, ↓reduceIte, hasSearchAnswer_orElse]
                  constructor
                  · rintro (hdelete | hfirst | hsecond)
                    · by_cases hk : k = 0
                      · simp [hk, HasSearchAnswer] at hdelete
                      · obtain ⟨choices, hl, hvalid, hanswer⟩ :=
                          (ih (f.erase [a, b]) L (k - 1)).mp (by simpa [hk] using hdelete)
                        exact ⟨0, by decide, choices, hl, hvalid,
                          by simpa [annotatedPath, hd, hs, hb, hc, hk] using hanswer⟩
                    · obtain ⟨choices, hl, hvalid, hanswer⟩ := (ih f (a :: L) k).mp hfirst
                      exact ⟨1, by decide, choices, hl, hvalid,
                        by simpa [annotatedPath, hd, hs, hb, hc] using hanswer⟩
                    · obtain ⟨choices, hl, hvalid, hanswer⟩ := (ih f (b :: L) k).mp hsecond
                      exact ⟨2, by decide, choices, hl, hvalid,
                        by simpa [annotatedPath, hd, hs, hb, hc] using hanswer⟩
                  · rintro ⟨choice, hchoiceBound, choices, ht, hv, hanswer⟩
                    have hchoice : choice = 0 ∨ choice = 1 ∨ choice = 2 := by
                      omega
                    rcases hchoice with rfl | rfl | rfl
                    · by_cases hk : k = 0
                      · simp [annotatedPath, hd, hc, hk, HasSearchAnswer] at hanswer
                        exact False.elim (hs (by omega))
                      · apply Or.inl
                        simp only [hk, ↓reduceIte]
                        apply (ih (f.erase [a, b]) L (k - 1)).mpr
                        exact ⟨choices, ht, hv,
                          by simpa [annotatedPath, hd, hs, hb, hc, hk] using hanswer⟩
                    · apply Or.inr; apply Or.inl
                      apply (ih f (a :: L) k).mpr
                      exact ⟨choices, ht, hv,
                        by simpa [annotatedPath, hd, hs, hb, hc] using hanswer⟩
                    · apply Or.inr; apply Or.inr
                      apply (ih f (b :: L) k).mpr
                      exact ⟨choices, ht, hv,
                        by simpa [annotatedPath, hd, hs, hb, hc] using hanswer⟩

/-- The path scan has exactly the same success criterion as annotated search. -/
theorem annotatedSearch_iff_encoded_path (cut : LeastCutOperation) (τ : Assignment)
    (fuel : ℕ) (f : CNF) (L : List Literal) (k : ℕ) :
    HasSearchAnswer (annotatedSearch cut τ fuel f L k) ↔
      ∃ word < 3 ^ fuel, HasSearchAnswer (annotatedPath cut τ (Poly.cfg 3 fuel word) f L k) := by
  rw [annotatedSearch_iff_path]
  constructor
  · rintro ⟨choices, hl, hv, ha⟩
    refine ⟨Poly.enc 3 choices, ?_, ?_⟩
    · simpa [hl] using Poly.enc_lt (by decide) choices hv
    · rw [← hl, Poly.cfg_enc choices hv]
      exact ha
  · rintro ⟨word, hw, ha⟩
    exact ⟨Poly.cfg 3 fuel word, Poly.length_cfg _ _ _, Poly.cfg_lt (by decide) _ _, ha⟩

end STACS2027.Runtimes.BoundedCost
