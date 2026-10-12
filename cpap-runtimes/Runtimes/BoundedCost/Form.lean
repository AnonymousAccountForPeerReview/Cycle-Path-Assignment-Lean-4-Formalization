module

public import Runtimes.BoundedCost.Init
public import Runtimes.BoundedCost.Ov
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: the formula `Γ'` in memory

`form5_spec`: from the input `boundedCostInput g k Ψ`, the program `form5` (phase 1, the sorting front
end, the mark table, `nCopies g k Ψ` copies of the path constraints, the overlap clauses)
reaches `HS g k 0 Γ'` — the codes of `Γ' = almostFormula g k Ψ` at `bC5 g k`, `gNC = |Γ'|`,
`Ψ` in `gPSI` — within `formCost g k Ψ` steps, accessing only the addresses below any
`S ≥ bC5 g k + 2|Γ'|`. No memory is indexed by a vertex label.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost Complexity.SAT

variable {S : ℕ}

/-- `Γ'` is a 2-CNF over the `kt` variables `b_{C,e}`. -/
theorem almost_two (g : Graph) (k Ψ : ℕ) :
    TwoSat.IsTwoCNF (k * (cycles g k).length) (almostFormula g k Ψ) :=
  (almostFormula_size g k Ψ).1

theorem length_codes_almost (g : Graph) (k Ψ : ℕ) :
    (TwoSat.codes (almostFormula g k Ψ)).length = 2 * (almostFormula g k Ψ).length :=
  TwoSat.length_codes (almost_two g k Ψ)

/-- Without cycles there is no path constraint. -/
theorem pathConstraints_nil {g : Graph} {k : ℕ} (h : (cycles g k).length = 0) :
    pathConstraints g k = [] := by
  have := (almostFormula_size g k 0).2.1
  rw [h, Nat.mul_zero] at this
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem pcs_nCopies (g : Graph) (k Ψ : ℕ) : pcs g k (nCopies g k Ψ) = pcs g k (Ψ + 1) := by
  unfold nCopies
  split_ifs with h
  · simp [pcs, pathConstraints_nil h]
  · rfl

theorem psiR_front (Ψ N : ℕ) : RegIndep (wregs Sort.front) (PsiR Ψ N) := by
  intro c c' h ⟨h1, h2⟩
  have n : ∀ r, r = gPSI ∨ r = gPS1 → r ∉ wregs Sort.front := by
    intro r hr hm
    rcases Sort.front_wregs r hm with e | e | e | e | e | e | e <;> rcases hr with rfl | rfl <;>
      revert e <;> decide
  exact ⟨by rw [h _ (n _ (Or.inl rfl)), h1], by rw [h _ (n _ (Or.inr rfl)), h2]⟩

/-- The cost of the front end. -/
def frontCost (g : Graph) (k : ℕ) : ℕ :=
  Sort.CF * (Sort.fL g k * (Nat.clog 2 (Sort.fL g k) + 1) + 1)

/-- **Phase 2**: the sorting front end, from phase 1 (free address `bD g k`). -/
theorem front5_spec (g : Graph) (k Ψ N : ℕ) (hS : bS5 g k ≤ S) :
    HTB S Sort.front (fun c => InitPost g k c ∧ PsiR Ψ N c)
      (fun c => (Sort.FrontPost g k (bD g k) c ∧ c.out = []) ∧ PsiR Ψ N c) (frontCost g k) := by
  refine HTB.frameReg ?_ (psiR_front Ψ N)
  exact HTB.of_forall fun c₀ hI => (Sort.front_spec g k c₀ (Sort.frontIn_of_initPost hI)
    (by rw [hI.rfree]; exact hS)).post fun c ⟨hP, _, ho⟩ => by
      rw [hI.rfree] at hP
      exact ⟨hP, by rw [ho, hI.rout]⟩

/-- **Phase 3**: the mark table. -/
theorem allocSeen_spec (g : Graph) (k Ψ N : ℕ) :
    HTB S allocSeen (fun c => (Sort.FrontPost g k (bD g k) c ∧ c.out = []) ∧ PsiR Ψ N c)
      (fun c => SeenPost g k c ∧ PsiR Ψ N c) 3 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hP, ho⟩, h1, h2⟩ => ?_
  have hag : Agree [rT, gSEEN, rFREE] c (run allocSeen c) :=
    agree_run (by decide) rfl rfl (by decide) c
  refine ⟨⟨(show RegIndep [rT, gSEEN, rFREE] (GA g k) by indep [gA_iff]).indep c _ hag hP.ga,
    ?_, ?_, ?_, by rw [hag.mem]; exact hP.mverts, by rw [hag.mem]; exact hP.meid,
    by rw [hag.mem]; exact hP.mzero, by rw [hag.out]; exact ho⟩,
    by rw [hag.reg gPSI (by decide), h1], by rw [hag.reg gPS1 (by decide), h2]⟩
  · rw [hag.reg gEID (by decide)]; exact hP.reid
  · simp +decide [allocSeen, run_mov, hP.rfree, bS5]
  · simp +decide [allocSeen, run_mov, hP.rfree, hP.rne, bC5, bS5]

/-- The cost of the formula. -/
def formCost (g : Graph) (k Ψ : ℕ) : ℕ :=
  5 * (cycles g k).length + 24 + (frontCost g k + (3 + (nCopies g k Ψ * ((cycles g k).length *
    (k * (k * 65 + 7) + 8) + 8) + 7 + ((cycles g k).length * ((cycles g k).length *
    (k * 44 + 16) + 9) + 4))))

/-- **The formula `Γ'` in memory.** -/
theorem form5_spec (g : Graph) (k Ψ : ℕ)
    (hS : bC5 g k + (TwoSat.codes (almostFormula g k Ψ)).length ≤ S) :
    HTB S form5 (fun c => c = initial (boundedCostInput g k Ψ))
      (fun c => HS g k (fun _ => 0) (almostFormula g k Ψ) c ∧ c.reg gPSI = Ψ) (formCost g k Ψ) := by
  have hl := lay5 g k
  have hF := almostFormula_eq (g := g) (k := k) Ψ
  rw [← pcs_nCopies] at hF
  have hc := length_codes_append (pcs g k (nCopies g k Ψ)) (ovI g k (cycles g k).length)
  rw [← hF] at hc
  have h1 := stepInit5_spec (S := S) g k Ψ (by omega)
  have h2 := front5_spec (S := S) g k Ψ (nCopies g k Ψ) (by omega)
  have h3 := allocSeen_spec (S := S) g k Ψ (nCopies g k Ψ)
  have h4 := (stepPcs_spec (S := S) g k (nCopies g k Ψ) (by omega)).frameReg
    (F := fun c => c.reg gPSI = Ψ) (by indep)
  have h5 := (stepOv_spec (S := S) g k (pcs g k (nCopies g k Ψ)) (by rw [← hF]; exact hS)).frameReg
    (F := fun c => c.reg gPSI = Ψ) (by indep)
  refine (h1.seq (h2.seq (h3.seq ((h4.pre fun c ⟨hP, h1, h2⟩ => ⟨⟨hP, h2⟩, h1⟩).seq
    (h5.post fun c ⟨h, hp⟩ => ⟨by rw [hF]; exact h, hp⟩))))).weaken (le_of_eq ?_)
  rfl

end STACS2027.Runtimes.BoundedCost
