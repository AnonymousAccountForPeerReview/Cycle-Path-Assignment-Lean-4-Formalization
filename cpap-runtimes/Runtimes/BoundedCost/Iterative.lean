module

public import Runtimes.BoundedCost.Compression
import Mathlib.Tactic

/-!
# Executable iterative compression for Almost 2-SAT

Process clause occurrences in order.  The current assignment satisfies all
but at most the deletion budget.  When a newly appended clause exceeds that
budget, the old false clauses together with the new clause form the special
set, of size at most `k + 1`; the old true clauses form a satisfiable base.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

/-- The old clauses satisfied by the current assignment. -/
def compressionBase (σ : Assignment) (f : CNF) : CNF := f.filter (evalClause σ)

/-- The old false occurrences and the newly appended clause. -/
def compressionSpecial (σ : Assignment) (f : CNF) (c : Clause) : CNF :=
  f.filter (fun d => !(evalClause σ d)) ++ [c]

theorem compression_partition_perm (σ : Assignment) (f : CNF) (c : Clause) :
    (compressionBase σ f ++ compressionSpecial σ f c).Perm (f ++ [c]) := by
  simpa only [compressionBase, compressionSpecial, ← List.append_assoc] using
    (List.filter_append_perm (evalClause σ) f).append_right [c]

theorem compressionBase_satisfied (σ : Assignment) (f : CNF) :
    evalCNF σ (compressionBase σ f) = true := by
  apply (evalCNF_iff σ _).mpr
  intro c hc
  exact (List.mem_filter.mp hc).2

theorem compressionSpecial_length (σ : Assignment) (f : CNF) (c : Clause) :
    (compressionSpecial σ f c).length = unsatisfiedCount σ f + 1 := by
  simp [compressionSpecial, unsatisfiedCount, List.countP_eq_length_filter]

theorem compressionBase_clauses2 {f : CNF} (hf : Clauses2 f) (σ : Assignment) :
    Clauses2 (compressionBase σ f) := fun c hc => hf c (List.mem_of_mem_filter hc)

theorem compressionSpecial_clauses2 {f : CNF} {c : Clause}
    (hf : Clauses2 f) (hc : c.length = 2) (σ : Assignment) :
    Clauses2 (compressionSpecial σ f c) := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact hf d (List.mem_of_mem_filter hd)
  · simp only [List.mem_singleton] at hd
    subst d
    exact hc

/-- Construct a least-cut operation for each current reference assignment. -/
abbrev LeastCutFactory := Assignment → LeastCutOperation

/-- The factory's concrete realization must provide the proved cut contract. -/
def LeastCutFactoryCorrect (factory : LeastCutFactory) : Prop :=
  ∀ τ, LeastCutOperationCorrect τ (factory τ)

/-- Process the remaining clause occurrences, keeping the current processed and
its assignment. -/
def iterativeSearch (factory : LeastCutFactory) (k : ℕ) :
    CNF → Assignment → CNF → Option Assignment
  | processed, σ, [] => some σ
  | processed, σ, c :: rest =>
      if unsatisfiedCount σ (processed ++ [c]) ≤ k then
        iterativeSearch factory k (processed ++ [c]) σ rest
      else
        match compressionSearch (factory σ) σ (compressionBase σ processed)
            (compressionSpecial σ processed c) k with
        | none => none
        | some δ => iterativeSearch factory k (processed ++ [c]) δ rest

/-- The complete decision-and-assignment procedure on clause occurrences. -/
def almostTwoSatSearch (factory : LeastCutFactory) (f : CNF) (k : ℕ) : Option Assignment :=
  iterativeSearch factory k [] (fun _ => false) f

/-- Every successful iteration returns an assignment within the budget. -/
theorem iterativeSearch_sound (factory : LeastCutFactory) (hfactory : LeastCutFactoryCorrect factory)
    (k : ℕ) : ∀ rest processed σ, Clauses2 (processed ++ rest) → unsatisfiedCount σ processed ≤ k →
      ∀ δ, iterativeSearch factory k processed σ rest = some δ →
        unsatisfiedCount δ (processed ++ rest) ≤ k := by
  intro rest
  induction rest with
  | nil =>
    intro processed σ hf hσ δ h
    simp only [iterativeSearch, Option.some.injEq] at h
    subst δ
    simpa using hσ
  | cons c rest ih =>
    intro processed σ hf hσ δ h
    have hpre : Clauses2 processed := fun d hd => hf d (by simp [hd])
    have hc : c.length = 2 := hf c (by simp)
    have hnext : Clauses2 ((processed ++ [c]) ++ rest) := by
      simpa [List.append_assoc] using hf
    by_cases hs : unsatisfiedCount σ (processed ++ [c]) ≤ k
    · simp only [iterativeSearch, hs, ↓reduceIte] at h
      simpa [List.append_assoc] using ih _ σ hnext hs δ h
    · simp only [iterativeSearch, hs, ↓reduceIte] at h
      cases hd : compressionSearch (factory σ) σ (compressionBase σ processed)
          (compressionSpecial σ processed c) k with
      | none => simp [hd] at h
      | some ρ =>
        simp only [hd] at h
        have hρ := compressionSearch_sound (factory σ) σ (hfactory σ)
          (compressionBase_clauses2 hpre σ) (compressionSpecial_clauses2 hpre hc σ)
          (compressionBase_satisfied σ processed) hd
        rw [unsatisfiedCount_perm (compression_partition_perm σ processed c) ρ] at hρ
        simpa [List.append_assoc] using ih _ ρ hnext hρ δ h

/-- Iterative compression finds every formula assignment within the budget. -/
theorem iterativeSearch_complete (factory : LeastCutFactory)
    (hfactory : LeastCutFactoryCorrect factory) (k : ℕ) :
    ∀ rest processed σ, Clauses2 (processed ++ rest) → unsatisfiedCount σ processed ≤ k →
      AlmostSatisfiable (processed ++ rest) k →
        ∃ δ, iterativeSearch factory k processed σ rest = some δ := by
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
    · simpa only [iterativeSearch, hs, ↓reduceIte] using ih _ σ hnext hs hwhole
    · have hprefix : AlmostSatisfiable (processed ++ [c]) k := by
        obtain ⟨ρ, hρ⟩ := (almostSatisfiable_iff_unsatisfiedCount _ _).mp hwhole
        exact (almostSatisfiable_iff_unsatisfiedCount _ _).mpr
          ⟨ρ, by rw [unsatisfiedCount_append] at hρ; omega⟩
      have hpartition : AlmostSatisfiable
          (compressionBase σ processed ++ compressionSpecial σ processed c) k := by
        rw [almostSatisfiable_iff_unsatisfiedCount] at hprefix ⊢
        simpa only [unsatisfiedCount_perm (compression_partition_perm σ processed c)] using hprefix
      obtain ⟨ρ, hρ⟩ := (compressionSearch_correct (factory σ) σ (hfactory σ)
        (compressionBase_clauses2 hpre σ) (compressionSpecial_clauses2 hpre hc σ)
        (compressionBase_satisfied σ processed) k).mpr hpartition
      have hb := compressionSearch_sound (factory σ) σ (hfactory σ)
        (compressionBase_clauses2 hpre σ) (compressionSpecial_clauses2 hpre hc σ)
        (compressionBase_satisfied σ processed) hρ
      rw [unsatisfiedCount_perm (compression_partition_perm σ processed c) ρ] at hb
      simpa only [iterativeSearch, hs, ↓reduceIte, hρ] using ih _ ρ hnext hb hwhole

/-- Exact correctness of the executable iterative-compression algorithm. -/
theorem almostTwoSatSearch_correct (factory : LeastCutFactory)
    (hfactory : LeastCutFactoryCorrect factory) {f : CNF} (hf : Clauses2 f) (k : ℕ) :
    (∃ σ, almostTwoSatSearch factory f k = some σ) ↔ AlmostSatisfiable f k := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact (almostSatisfiable_iff_unsatisfiedCount f k).mpr ⟨σ,
      by simpa using (iterativeSearch_sound factory hfactory k f [] (fun _ => false)
        (by simpa using hf) (by simp) σ hσ)⟩
  · exact iterativeSearch_complete factory hfactory k f [] (fun _ => false)
      (by simpa using hf) (by simp)

end STACS2027.Runtimes.BoundedCost
