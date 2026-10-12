module

public import Runtimes.BoundedCost.CompressionSeedRAM
public import Runtimes.BoundedCost.DenseState
public import Runtimes.BoundedCost.Requirements
import Mathlib.Tactic

/-! The forced-bit seed has exactly the requirements selected by the ternary
compression choices, with repeated literals represented by one dense bit. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def seedChosenCode (row : CompressionSeedRow) : Option ℕ :=
  if row.choice = 1 then some row.first else if row.choice = 2 then some row.second else none

def seedRequirementCodes (rows : List CompressionSeedRow) (count : ℕ) : List ℕ :=
  (List.range count).filterMap (fun i => seedChosenCode (rows.getD i default))

def seedRequirements (rows : List CompressionSeedRow) (count : ℕ) : List Literal :=
  (seedRequirementCodes rows count).map literalOfCode

theorem seedSelected_iff_chosenCode (row : CompressionSeedRow) (code : ℕ) :
    seedSelected row code = true ↔ seedChosenCode row = some code := by
  by_cases hfirst : row.choice = 1
  · simp [seedSelected, seedChosenCode, hfirst]
  · by_cases hsecond : row.choice = 2
    · simp [seedSelected, seedChosenCode, hfirst, hsecond]
    · simp [seedSelected, seedChosenCode, hfirst, hsecond]

theorem seedForcedValue_eq_one (rows : List CompressionSeedRow) (count code : ℕ) :
    seedForcedValue rows count code = 1 ↔ code ∈ seedRequirementCodes rows count := by
  simp [seedForcedValue, seedRequirementCodes, List.any_eq_true, seedSelected_iff_chosenCode]

theorem requires_seedRequirements (σ : Assignment) (rows : List CompressionSeedRow) (count : ℕ) :
    Requires σ (seedRequirements rows count) ↔
      ∀ code ∈ seedRequirementCodes rows count, TwoSat.nodeVal σ code = true := by
  simp only [Requires, seedRequirements, List.mem_map]
  constructor
  · intro h code hc
    simpa [evalLiteral_literalOfCode] using h (literalOfCode code) ⟨code, hc, rfl⟩
  · rintro h l ⟨code, hc, rfl⟩
    simpa [evalLiteral_literalOfCode] using h code hc

theorem seedRequirementCodes_bounded (rows : List CompressionSeedRow) (count nodes : ℕ)
    (hbound : ∀ i < count, (rows.getD i default).first < 2 * nodes ∧
      (rows.getD i default).second < 2 * nodes) :
    ∀ code ∈ seedRequirementCodes rows count, code < 2 * nodes := by
  intro code hc
  obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp hc
  have hib := List.mem_range.mp hi
  obtain ⟨hf, hs⟩ := hbound i hib
  unfold seedChosenCode at he
  split_ifs at he <;> simp_all
  all_goals obtain ⟨hf, hs⟩ := hbound i hib; omega

theorem requires_dense_seed (σ : Assignment) (rows : List CompressionSeedRow) (count nodes : ℕ)
    (hbound : ∀ i < count, (rows.getD i default).first < 2 * nodes ∧
      (rows.getD i default).second < 2 * nodes) :
    Requires σ (denseRequirements nodes (fun code => seedForcedValue rows count code == 1)) ↔
      Requires σ (seedRequirements rows count) := by
  rw [requires_denseRequirements, requires_seedRequirements]
  constructor
  · intro h code hc
    exact h code (seedRequirementCodes_bounded rows count nodes hbound code hc)
      (by simpa [seedForcedValue_eq_one] using hc)
  · intro h code hcode hf
    exact h code ((seedForcedValue_eq_one rows count code).mp (by simpa using hf))

end STACS2027.Runtimes.BoundedCost
