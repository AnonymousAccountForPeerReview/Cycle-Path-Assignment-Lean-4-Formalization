module

public import Runtimes.BoundedCost.Search
import Mathlib.Tactic

/-!
# Executable compression of an Almost 2-SAT deletion set

For every ternary branch on the special clauses, solve the annotated base
formula by the proved bounded-depth search.  The branch enumeration and the
search correctness together establish exact compression correctness.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

/-- Try the finite compression branches in order. -/
def tryCompressionBranches (cut : LeastCutOperation) (τ : Assignment)
    (base : CNF) (k : ℕ) : List CompressionBranch → Option Assignment
  | [] => none
  | r :: rs =>
      if r.1 ≤ k then
        (annotatedSearch cut τ (k - r.1 + 1) base r.2 (k - r.1)).orElse
          (fun _ => tryCompressionBranches cut τ base k rs)
      else tryCompressionBranches cut τ base k rs

/-- Compress a specified set of special clause occurrences. -/
def compressionSearch (cut : LeastCutOperation) (τ : Assignment)
    (base special : CNF) (k : ℕ) : Option Assignment :=
  tryCompressionBranches cut τ base k (compressionBranches special)

theorem tryCompressionBranches_sound (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) {base : CNF} (hf : Clauses2 base)
    (hτ : evalCNF τ base = true) (k : ℕ) :
    ∀ rs σ, tryCompressionBranches cut τ base k rs = some σ →
      ∃ r ∈ rs, r.1 ≤ k ∧ unsatisfiedCount σ base ≤ k - r.1 ∧ Requires σ r.2 := by
  intro rs
  induction rs with
  | nil => intro σ h; simp [tryCompressionBranches] at h
  | cons r rs ih =>
    intro σ h
    by_cases hb : r.1 ≤ k
    · simp only [tryCompressionBranches, hb, ↓reduceIte] at h
      cases hs : annotatedSearch cut τ (k - r.1 + 1) base r.2 (k - r.1) with
      | none =>
        simp only [hs, Option.orElse_none] at h
        obtain ⟨s, hs, hbudget, hσ, hL⟩ := ih σ h
        exact ⟨s, by simp [hs], hbudget, hσ, hL⟩
      | some ρ =>
        simp only [hs, Option.orElse_some, Option.some.injEq] at h
        subst σ
        obtain ⟨hσ, hL⟩ := annotatedSearch_sound cut τ hcut _ base r.2 _ hf hτ ρ hs
        exact ⟨r, by simp, hb, hσ, hL⟩
    · simp only [tryCompressionBranches, hb, ↓reduceIte] at h
      obtain ⟨s, hs, hbudget, hσ, hL⟩ := ih σ h
      exact ⟨s, by simp [hs], hbudget, hσ, hL⟩

theorem tryCompressionBranches_complete (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) {base : CNF} (hf : Clauses2 base)
    (hτ : evalCNF τ base = true) (k : ℕ) :
    ∀ rs, (∃ r ∈ rs, r.1 ≤ k ∧ AnnotatedAlmostSatisfiable base r.2 (k - r.1)) →
      ∃ σ, tryCompressionBranches cut τ base k rs = some σ := by
  intro rs
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rintro ⟨s, hs, hb, hsol⟩
    rcases List.mem_cons.mp hs with rfl | hs
    · simp only [tryCompressionBranches, hb, ↓reduceIte]
      apply orElse_exists_some_left
      exact (annotatedSearch_correct cut τ hcut hf hτ s.2 (k - s.1)).mpr hsol
    · have ht := ih ⟨s, hs, hb, hsol⟩
      by_cases hr : r.1 ≤ k
      · simp only [tryCompressionBranches, hr, ↓reduceIte]
        exact orElse_exists_some_right _ _ ht
      · simpa only [tryCompressionBranches, hr, ↓reduceIte] using ht

theorem compressionSearch_sound (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) {base special : CNF}
    (hb : Clauses2 base) (hs : Clauses2 special) (hτ : evalCNF τ base = true)
    {k : ℕ} {σ : Assignment} (h : compressionSearch cut τ base special k = some σ) :
    unsatisfiedCount σ (base ++ special) ≤ k := by
  obtain ⟨r, hr, hbudget, hbase, hL⟩ :=
    tryCompressionBranches_sound cut τ hcut hb hτ k _ σ h
  have hspecial := compressionBranches_sound hs hr hL
  rw [unsatisfiedCount_append]
  omega

/-- Compression succeeds exactly when the full formula admits the budget. -/
theorem compressionSearch_correct (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) {base special : CNF}
    (hb : Clauses2 base) (hs : Clauses2 special) (hτ : evalCNF τ base = true) (k : ℕ) :
    (∃ σ, compressionSearch cut τ base special k = some σ) ↔
      AlmostSatisfiable (base ++ special) k := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact (almostSatisfiable_iff_unsatisfiedCount _ _).mpr
      ⟨σ, compressionSearch_sound cut τ hcut hb hs hτ hσ⟩
  · intro hsol
    rw [almostSatisfiable_compression hs] at hsol
    exact tryCompressionBranches_complete cut τ hcut hb hτ k _ hsol

end STACS2027.Runtimes.BoundedCost
