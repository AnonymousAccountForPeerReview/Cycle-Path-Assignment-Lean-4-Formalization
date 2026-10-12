module

public import Runtimes.BoundedCost.Out
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: the answer and the recovery

`BoundedCostAnswer g k Ψ out`: `[0]` and no assignment of cost at most `Ψ`, or `1` followed by one
position `pos_i < k` per cycle such that the paths `selected C_i pos_i` form a cycle-path
assignment of cost at most `Ψ`.

`answer_of_table`: Corollary 5's recovery (`stepRec`, which writes
`1 :: (range t).map (recPos g k σ)` for the truth table `σ = memAsg m A`) answers correctly
whenever the table satisfies `Γ_𝓘` for a list `𝓘` of at most `Ψ` overlaps
(`recoverAssignment_correct`: the recovered paths form an assignment of cost at most `|𝓘|`).
`stepRec_zero`: with the flag `0`, `stepRec` writes `[0]`.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost Complexity.SAT

variable {S : ℕ}

/-- The answer of the machine of Theorem 4. -/
def BoundedCostAnswer (g : Graph) (k Ψ : ℕ) (out : List ℕ) : Prop :=
  (¬ HasAssignment g k Ψ ∧ out = [0]) ∨
    (∃ pos : List ℕ, out = 1 :: pos ∧ pos.length = (cycles g k).length ∧ (∀ p ∈ pos, p < k) ∧
      ValidChoices ((cycles g k).map selectedOptions) (List.zipWith selected (cycles g k) pos) ∧
      cost (List.zipWith selected (cycles g k) pos) ≤ Ψ)

/-- `Γ_𝓘` is a 2-CNF over the `kt` variables `b_{C,e}`. -/
theorem permitted_two (g : Graph) (k : ℕ) (I : List (ℕ × ℕ × Edge)) :
    TwoSat.IsTwoCNF (k * (cycles g k).length) (permittedFormula g k I) := fun cl hcl =>
  almost_two g k 0 cl (by
    rw [mem_almostFormula]
    simp only [permittedFormula, List.mem_append, List.mem_map, List.mem_filter] at hcl
    rcases hcl with h | ⟨u, ⟨hu, _⟩, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨u, hu, rfl⟩)

/-- **The recovery answers correctly** from a truth table satisfying `Γ_𝓘`, `|𝓘| ≤ Ψ`. -/
theorem answer_of_table {g : Graph} {k Ψ : ℕ} (hk : 4 ≤ k) (σ : Assignment)
    {I : List (ℕ × ℕ × Edge)} (hI : I.length ≤ Ψ)
    (hσ : evalCNF σ (permittedFormula g k I) = true) :
    BoundedCostAnswer g k Ψ (1 :: (List.range (cycles g k).length).map (recPos g k σ)) := by
  right
  obtain ⟨hvalid, hcost⟩ := recoverAssignment_correct hk g I σ hσ
  have hpos : (List.range (cycles g k).length).map (recPos g k σ) =
      (List.range (cycles g k).length).map (omittedPosition g k σ) :=
    List.map_congr_left fun i hi => (omittedPosition_eq σ (List.mem_range.mp hi)).symm
  refine ⟨(List.range (cycles g k).length).map (omittedPosition g k σ), by rw [hpos],
    by simp, ?_, ?_, ?_⟩
  · simp only [List.mem_map, List.mem_range]
    rintro p ⟨i, -, rfl⟩
    exact omittedPosition_lt g (by omega) σ i
  · rw [zipWith_recover]; exact hvalid
  · rw [zipWith_recover]; omega

/-- With the flag `0`, the recovery writes `[0]`. -/
theorem stepRec_zero :
    HTB S stepRec (fun c => c.reg TwoSat.tOK = 0 ∧ c.out = []) (fun c => c.out = [0]) 4 := by
  refine HTB.ifz (b := 3) ?_ ?_
  · refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨_, ho⟩, _⟩ => ?_
    simp [ho]
  · exact HTB.of_false fun c ⟨⟨h0, _⟩, hne⟩ => hne h0

end STACS2027.Runtimes.BoundedCost
