module

public import Runtimes.BoundedCost.FirstSuccess
import Mathlib.Tactic

/-! Encoded ternary compression vectors enumerate exactly the special-clause
branches.  The nested first-success scan has the same sound and complete
criterion as executable compression. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def compressionVector : List ℕ → CNF → Option CompressionBranch
  | [], [] => some (0, [])
  | choice :: choices, [a, b] :: special =>
      (compressionVector choices special).bind fun branch =>
        if choice = 0 then some (branch.1 + 1, branch.2)
        else if choice = 1 then some (branch.1, a :: branch.2)
        else if choice = 2 then some (branch.1, b :: branch.2) else none
  | _, _ => none

theorem compressionVector_mem (special : CNF) (hf : Clauses2 special)
    (choices : List ℕ) (branch : CompressionBranch)
    (h : compressionVector choices special = some branch) : branch ∈ compressionBranches special := by
  induction special generalizing choices branch with
  | nil =>
    cases choices with
    | nil => simp [compressionVector] at h; subst branch; simp [compressionBranches]
    | cons d ds => simp [compressionVector] at h
  | cons clause special ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf clause (by simp))
    have ht : Clauses2 special := fun c hc => hf c (by simp [hc])
    cases choices with
    | nil => simp [compressionVector] at h
    | cons choice choices =>
      cases hv : compressionVector choices special with
      | none => simp [compressionVector, hv] at h
      | some rest =>
        have hr := ih ht choices rest hv
        by_cases hz : choice = 0
        · simp [compressionVector, hv, hz] at h
          subst branch
          apply List.mem_append_left
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨rest, hr, rfl⟩
        · by_cases ho : choice = 1
          · simp [compressionVector, hv, hz, ho] at h
            subst branch
            apply List.mem_append_left
            apply List.mem_append_right
            exact List.mem_map.mpr ⟨rest, hr, rfl⟩
          · by_cases ht : choice = 2
            · simp [compressionVector, hv, hz, ho, ht] at h
              subst branch
              apply List.mem_append_right
              exact List.mem_map.mpr ⟨rest, hr, rfl⟩
            · simp [compressionVector, hv, hz, ho, ht] at h

theorem compressionVector_complete (special : CNF) (hf : Clauses2 special)
    (branch : CompressionBranch) (h : branch ∈ compressionBranches special) :
    ∃ choices, choices.length = special.length ∧ (∀ d ∈ choices, d < 3) ∧
      compressionVector choices special = some branch := by
  induction special generalizing branch with
  | nil =>
    simp [compressionBranches] at h
    subst branch
    exact ⟨[], rfl, by simp, rfl⟩
  | cons clause special ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf clause (by simp))
    have ht : Clauses2 special := fun c hc => hf c (by simp [hc])
    simp only [compressionBranches, List.mem_append, List.mem_map] at h
    rcases h with (⟨rest, hr, rfl⟩ | ⟨rest, hr, rfl⟩) | ⟨rest, hr, rfl⟩
    all_goals obtain ⟨choices, hl, hd, hv⟩ := ih ht rest hr
    · exact ⟨0 :: choices, by simp [hl], by simpa using hd,
        by simp [compressionVector, hv]⟩
    · exact ⟨1 :: choices, by simp [hl], by simpa using hd,
        by simp [compressionVector, hv]⟩
    · exact ⟨2 :: choices, by simp [hl], by simpa using hd,
        by simp [compressionVector, hv]⟩

theorem compressionBranches_iff_encoded (special : CNF) (hf : Clauses2 special)
    (branch : CompressionBranch) :
    branch ∈ compressionBranches special ↔
      ∃ word < 3 ^ special.length,
        compressionVector (Poly.cfg 3 special.length word) special = some branch := by
  constructor
  · intro h
    obtain ⟨choices, hl, hd, hv⟩ := compressionVector_complete special hf branch h
    refine ⟨Poly.enc 3 choices, ?_, ?_⟩
    · simpa [hl] using Poly.enc_lt (by decide) choices hd
    · rw [← hl, Poly.cfg_enc choices hd]
      exact hv
  · rintro ⟨word, hw, hv⟩
    exact compressionVector_mem special hf _ branch hv

def encodedCompressionSearch (cut : LeastCutOperation) (τ : Assignment)
    (fuel : ℕ) (base special : CNF) (budget : ℕ) : Option Assignment :=
  firstSuccess (fun word =>
    match compressionVector (Poly.cfg 3 special.length word) special with
    | none => none
    | some branch => if branch.1 ≤ budget then
        encodedPathSearch cut τ fuel base branch.2 (budget - branch.1) else none)
    (List.range (3 ^ special.length))

theorem encodedCompressionSearch_sound (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) {base special : CNF}
    (hb : Clauses2 base) (hs : Clauses2 special) (hτ : evalCNF τ base = true)
    (fuel budget : ℕ) {σ : Assignment}
    (h : encodedCompressionSearch cut τ fuel base special budget = some σ) :
    unsatisfiedCount σ (base ++ special) ≤ budget := by
  obtain ⟨word, hw, hword⟩ := firstSuccess_some _ _ σ h
  cases hv : compressionVector (Poly.cfg 3 special.length word) special with
  | none => simp [hv] at hword
  | some branch =>
    have hr := compressionVector_mem special hs _ branch hv
    by_cases hk : branch.1 ≤ budget
    · simp only [hv, hk, ↓reduceIte] at hword
      obtain ⟨hbase, hL⟩ := encodedPathSearch_sound cut τ hcut hb hτ fuel branch.2
        (budget - branch.1) hword
      have hspecial := compressionBranches_sound hs hr hL
      rw [unsatisfiedCount_append]
      omega
    · simp [hv, hk] at hword

theorem encodedCompressionSearch_correct (cut : LeastCutOperation) (τ : Assignment)
    (hcut : LeastCutOperationCorrect τ cut) {base special : CNF}
    (hb : Clauses2 base) (hs : Clauses2 special) (hτ : evalCNF τ base = true)
    (fuel budget : ℕ) (hdepth : budget < fuel) :
    HasSearchAnswer (encodedCompressionSearch cut τ fuel base special budget) ↔
      AlmostSatisfiable (base ++ special) budget := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact (almostSatisfiable_iff_unsatisfiedCount _ _).mpr
      ⟨σ, encodedCompressionSearch_sound cut τ hcut hb hs hτ fuel budget hσ⟩
  · intro h
    obtain ⟨branch, hr, hk, hsol⟩ := (almostSatisfiable_compression hs budget).mp h
    obtain ⟨word, hw, hv⟩ := (compressionBranches_iff_encoded special hs branch).mp hr
    obtain ⟨σ, hσ⟩ := (encodedPathSearch_correct cut τ hcut hb hτ fuel branch.2
      (budget - branch.1) (by omega)).mpr hsol
    unfold encodedCompressionSearch HasSearchAnswer
    apply (firstSuccess_has _ _).mpr
    exact ⟨word, List.mem_range.mpr hw, σ, by simp [hv, hk, hσ]⟩

end STACS2027.Runtimes.BoundedCost
