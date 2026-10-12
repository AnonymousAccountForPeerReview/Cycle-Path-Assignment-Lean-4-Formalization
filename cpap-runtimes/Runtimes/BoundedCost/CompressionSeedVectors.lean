module

public import Runtimes.BoundedCost.CompressionSeedSemantics
public import Runtimes.BoundedCost.CompressionPaths
public import Runtimes.BoundedCost.SearchSemantics
import Mathlib.Tactic

/-! The concrete seed rows encode the exact deleted-count and requirement-list
of a ternary compression vector. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def seedRowsOf : List ℕ → CNF → List CompressionSeedRow
  | choice :: choices, [a, b] :: special =>
      ⟨TwoSat.code a, TwoSat.code b, choice⟩ :: seedRowsOf choices special
  | _, _ => []

theorem seedRequirementCodes_all (rows : List CompressionSeedRow) :
    seedRequirementCodes rows rows.length = rows.filterMap seedChosenCode := by
  have h := congrArg (List.filterMap seedChosenCode) (map_getD_range rows default)
  simpa only [seedRequirementCodes, List.filterMap_map, Function.comp_def] using h

theorem seedDeletedCount_all (rows : List CompressionSeedRow) :
    seedDeletedCount rows rows.length = rows.countP (fun row => row.choice == 0) :=
  countP_getD_range rows default (fun row => row.choice == 0)

theorem seedRowsOf_vector (special : CNF) (hf : Clauses2 special)
    (choices : List ℕ) (branch : CompressionBranch)
    (h : compressionVector choices special = some branch) :
    let rows := seedRowsOf choices special
    rows.length = special.length ∧ seedDeletedCount rows rows.length = branch.1 ∧
      seedRequirements rows rows.length = branch.2 := by
  induction special generalizing choices branch with
  | nil =>
    cases choices with
    | nil =>
      simp [compressionVector] at h
      subst branch
      simp [seedRowsOf, seedDeletedCount, seedRequirements, seedRequirementCodes]
    | cons choice choices => simp [compressionVector] at h
  | cons clause special ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf clause (by simp))
    have ht : Clauses2 special := fun c hc => hf c (by simp [hc])
    cases choices with
    | nil => simp [compressionVector] at h
    | cons choice choices =>
      cases hv : compressionVector choices special with
      | none => simp [compressionVector, hv] at h
      | some rest =>
        obtain ⟨hlen, hdeleted, hrequired⟩ := ih ht choices rest hv
        by_cases hz : choice = 0
        · simp [compressionVector, hv, hz] at h
          subst branch
          simp only [seedRequirements, seedRequirementCodes_all] at hrequired
          simp only [seedDeletedCount_all] at hdeleted
          simp only [seedRowsOf, seedDeletedCount_all, seedRequirements, seedRequirementCodes_all]
          simp [hz, hlen, seedChosenCode, hdeleted, hrequired, Nat.add_comm]
        · by_cases ho : choice = 1
          · simp [compressionVector, hv, hz, ho] at h
            subst branch
            simp only [seedRequirements, seedRequirementCodes_all] at hrequired
            simp only [seedDeletedCount_all] at hdeleted
            simp only [seedRowsOf, seedDeletedCount_all, seedRequirements, seedRequirementCodes_all]
            simp [ho, hlen, seedChosenCode, hdeleted, hrequired, literalOfCode_code]
          · by_cases ht : choice = 2
            · simp [compressionVector, hv, hz, ho, ht] at h
              subst branch
              simp only [seedRequirements, seedRequirementCodes_all] at hrequired
              simp only [seedDeletedCount_all] at hdeleted
              simp only [seedRowsOf, seedDeletedCount_all, seedRequirements, seedRequirementCodes_all]
              simp [ht, hlen, seedChosenCode, hdeleted, hrequired, literalOfCode_code]
            · simp [compressionVector, hv, hz, ho, ht] at h

theorem seedRowsOf_bounded {nodes : ℕ} (special : CNF) (hf : TwoSat.IsTwoCNF nodes special)
    (choices : List ℕ) :
    ∀ row ∈ seedRowsOf choices special, row.first < 2 * nodes ∧ row.second < 2 * nodes := by
  induction special generalizing choices with
  | nil => simp [seedRowsOf]
  | cons clause special ih =>
    obtain ⟨hc, hb⟩ := hf clause (by simp)
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hc
    have ht : TwoSat.IsTwoCNF nodes special := fun c hc => hf c (by simp [hc])
    cases choices with
    | nil => simp [seedRowsOf]
    | cons choice choices =>
      intro row hr
      rcases List.mem_cons.mp hr with he | hr
      · subst row
        exact ⟨TwoSat.code_lt (hb a (by simp)), TwoSat.code_lt (hb b (by simp))⟩
      · exact ih ht choices row hr

theorem denseSeed_vector_requirements {nodes : ℕ} (special : CNF)
    (hf : TwoSat.IsTwoCNF nodes special) (choices : List ℕ) (branch : CompressionBranch)
    (h : compressionVector choices special = some branch) (σ : Assignment) :
    let rows := seedRowsOf choices special
    Requires σ (denseRequirements nodes (fun code => seedForcedValue rows rows.length code == 1)) ↔
      Requires σ branch.2 := by
  dsimp only
  have hc : Clauses2 special := fun c hc => (hf c hc).1
  have hv := seedRowsOf_vector special hc choices branch h
  rw [requires_dense_seed]
  · rw [hv.2.2]
  · intro i hi
    rw [← List.getElem_eq_getD (h := hi) default]
    exact seedRowsOf_bounded special hf choices _ (List.getElem_mem hi)

end STACS2027.Runtimes.BoundedCost
