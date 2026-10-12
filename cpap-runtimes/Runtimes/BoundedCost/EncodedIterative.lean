module

public import Runtimes.BoundedCost.CompressionPaths
public import Runtimes.BoundedCost.Iterative
import Mathlib.Tactic

/-! Iterative compression using the exhaustive bounded ternary path scans
realized by the physical compiler. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def encodedIterativeSearch (factory : LeastCutFactory) (fuel k : ℕ) :
    CNF → Assignment → CNF → Option Assignment
  | processed, σ, [] => some σ
  | processed, σ, c :: rest =>
      if unsatisfiedCount σ (processed ++ [c]) ≤ k then
        encodedIterativeSearch factory fuel k (processed ++ [c]) σ rest
      else
        match encodedCompressionSearch (factory σ) σ fuel (compressionBase σ processed)
            (compressionSpecial σ processed c) k with
        | none => none
        | some δ => encodedIterativeSearch factory fuel k (processed ++ [c]) δ rest

/-- The complete decision-and-assignment procedure on clause occurrences. -/
def almostTwoSatEncodedSearch (factory : LeastCutFactory) (f : CNF) (k : ℕ) : Option Assignment :=
  encodedIterativeSearch factory (k + 1) k [] (fun _ => false) f

/-- Every successful iteration returns an assignment within the budget. -/
theorem encodedIterativeSearch_sound (factory : LeastCutFactory) (hfactory : LeastCutFactoryCorrect factory)
    (fuel k : ℕ) : ∀ rest processed σ, Clauses2 (processed ++ rest) → unsatisfiedCount σ processed ≤ k →
      ∀ δ, encodedIterativeSearch factory fuel k processed σ rest = some δ →
        unsatisfiedCount δ (processed ++ rest) ≤ k := by
  intro rest
  induction rest with
  | nil =>
    intro processed σ hf hσ δ h
    simp only [encodedIterativeSearch, Option.some.injEq] at h
    subst δ
    simpa using hσ
  | cons c rest ih =>
    intro processed σ hf hσ δ h
    have hpre : Clauses2 processed := fun d hd => hf d (by simp [hd])
    have hc : c.length = 2 := hf c (by simp)
    have hnext : Clauses2 ((processed ++ [c]) ++ rest) := by
      simpa [List.append_assoc] using hf
    by_cases hs : unsatisfiedCount σ (processed ++ [c]) ≤ k
    · simp only [encodedIterativeSearch, hs, ↓reduceIte] at h
      simpa [List.append_assoc] using ih _ σ hnext hs δ h
    · simp only [encodedIterativeSearch, hs, ↓reduceIte] at h
      cases hd : encodedCompressionSearch (factory σ) σ fuel (compressionBase σ processed)
          (compressionSpecial σ processed c) k with
      | none => simp [hd] at h
      | some ρ =>
        simp only [hd] at h
        have hρ := encodedCompressionSearch_sound (factory σ) σ (hfactory σ)
          (compressionBase_clauses2 hpre σ) (compressionSpecial_clauses2 hpre hc σ)
          (compressionBase_satisfied σ processed) fuel k hd
        rw [unsatisfiedCount_perm (compression_partition_perm σ processed c) ρ] at hρ
        simpa [List.append_assoc] using ih _ ρ hnext hρ δ h

/-- Iterative compression finds every formula assignment within the budget. -/
theorem encodedIterativeSearch_complete (factory : LeastCutFactory)
    (hfactory : LeastCutFactoryCorrect factory) (fuel k : ℕ) (hdepth : k < fuel) :
    ∀ rest processed σ, Clauses2 (processed ++ rest) → unsatisfiedCount σ processed ≤ k →
      AlmostSatisfiable (processed ++ rest) k →
        ∃ δ, encodedIterativeSearch factory fuel k processed σ rest = some δ := by
  intro rest
  induction rest with
  | nil => intro processed σ _ _ _; exact ⟨σ, rfl⟩
  | cons c rest ih =>
    intro processed σ hf hσ hsol
    have hpre : Clauses2 processed := fun d hd => hf d (by simp [hd])
    have hc : c.length = 2 := hf c (by simp)
    have hnext : Clauses2 ((processed ++ [c]) ++ rest) := by
      simpa [List.append_assoc] using hf
    have hwhole : AlmostSatisfiable ((processed ++ [c]) ++ rest) k := by
      simpa [List.append_assoc] using hsol
    by_cases hs : unsatisfiedCount σ (processed ++ [c]) ≤ k
    · simpa only [encodedIterativeSearch, hs, ↓reduceIte] using ih _ σ hnext hs hwhole
    · have hprefix : AlmostSatisfiable (processed ++ [c]) k := by
        obtain ⟨ρ, hρ⟩ := (almostSatisfiable_iff_unsatisfiedCount _ _).mp hwhole
        exact (almostSatisfiable_iff_unsatisfiedCount _ _).mpr
          ⟨ρ, by rw [unsatisfiedCount_append] at hρ; omega⟩
      have hpartition : AlmostSatisfiable
          (compressionBase σ processed ++ compressionSpecial σ processed c) k := by
        rw [almostSatisfiable_iff_unsatisfiedCount] at hprefix ⊢
        simpa only [unsatisfiedCount_perm (compression_partition_perm σ processed c)] using hprefix
      obtain ⟨ρ, hρ⟩ := (encodedCompressionSearch_correct (factory σ) σ (hfactory σ)
        (compressionBase_clauses2 hpre σ) (compressionSpecial_clauses2 hpre hc σ)
        (compressionBase_satisfied σ processed) fuel k hdepth).mpr hpartition
      have hb := encodedCompressionSearch_sound (factory σ) σ (hfactory σ)
        (compressionBase_clauses2 hpre σ) (compressionSpecial_clauses2 hpre hc σ)
        (compressionBase_satisfied σ processed) fuel k hρ
      rw [unsatisfiedCount_perm (compression_partition_perm σ processed c) ρ] at hb
      simpa only [encodedIterativeSearch, hs, ↓reduceIte, hρ] using ih _ ρ hnext hb hwhole

/-- Exact correctness of the executable iterative-compression algorithm. -/
theorem almostTwoSatEncodedSearch_correct (factory : LeastCutFactory)
    (hfactory : LeastCutFactoryCorrect factory) {f : CNF} (hf : Clauses2 f) (k : ℕ) :
    (∃ σ, almostTwoSatEncodedSearch factory f k = some σ) ↔ AlmostSatisfiable f k := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact (almostSatisfiable_iff_unsatisfiedCount f k).mpr ⟨σ,
      by simpa using (encodedIterativeSearch_sound factory hfactory (k + 1) k f [] (fun _ => false)
        (by simpa using hf) (by simp) σ hσ)⟩
  · exact encodedIterativeSearch_complete factory hfactory (k + 1) k (by omega) f [] (fun _ => false)
      (by simpa using hf) (by simp)


end STACS2027.Runtimes.BoundedCost
