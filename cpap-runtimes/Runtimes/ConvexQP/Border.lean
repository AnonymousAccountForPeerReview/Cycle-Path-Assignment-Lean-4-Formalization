module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# Lemma 16, Part C: bordered determinants and adjugates

Phase M of the exact algorithm maintains the
determinant `Δ = det B` and the adjugate `Aj = adj B` of a square submatrix `B` of the KKT
matrix, and borders `B` by one row and one column per step. This file proves the two update
formulas, for the bordered matrix `border B col ρ δ = [[B, col], [ρᵀ, δ]]`:

* **C1** (`det_border_field`, `det_border`): `det [[B, col], [ρᵀ, δ]] = δ·det B − ρ·(adj B col)`
  when `det B ≠ 0` (Schur complement, Mathlib `det_fromBlocks₁₁`, after reindexing
  `Fin r ⊕ Fin 1 ≃ Fin (r+1)`).
* **C2** (`adjugate_border_field`, `adjugate_border`): with `Δ = det B ≠ 0`, `Aj = adj B` and
  `Δ' = δΔ − ρ·(Aj col) ≠ 0`,
  `adj [[B, col], [ρᵀ, δ]] = [[(Δ'·Aj + (Aj col)(ρᵀ Aj))/Δ, −Aj col], [−ρᵀ Aj, Δ]]`;
  over `ℤ` the division is exact (`Int.ediv`), which is how the algorithm computes it.
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Matrix Finset

section Def

variable {R : Type*}

/-- The bordered matrix `[[B, col], [ρᵀ, δ]]` (`B` in the top-left `r × r` block, `col` the last
column, `ρ` the last row, `δ` the corner). -/
def border {r : ℕ} (B : Matrix (Fin r) (Fin r) R) (col ρ : Fin r → R) (δ : R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of fun a b =>
    Fin.lastCases (Fin.lastCases δ ρ b) (fun a => Fin.lastCases (col a) (B a) b) a

variable {r : ℕ} (B : Matrix (Fin r) (Fin r) R) (col ρ : Fin r → R) (δ : R)

@[simp] theorem border_cc (a b : Fin r) : border B col ρ δ a.castSucc b.castSucc = B a b := by
  simp [border]

@[simp] theorem border_cl (a : Fin r) : border B col ρ δ a.castSucc (Fin.last r) = col a := by
  simp [border]

@[simp] theorem border_lc (b : Fin r) : border B col ρ δ (Fin.last r) b.castSucc = ρ b := by
  simp [border]

@[simp] theorem border_ll : border B col ρ δ (Fin.last r) (Fin.last r) = δ := by
  simp [border]

theorem border_map [CommRing R] {S : Type*} [CommRing S] (f : R →+* S) :
    f.mapMatrix (border B col ρ δ) = border (f.mapMatrix B) (fun a => f (col a))
      (fun a => f (ρ a)) (f δ) := by
  ext a b
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;> simp

theorem border_eq_reindex [Zero R] :
    border B col ρ δ = reindex finSumFinEquiv finSumFinEquiv
      (fromBlocks B (replicateCol (Fin 1) col) (replicateRow (Fin 1) ρ) (Matrix.of fun _ _ => δ)) := by
  ext a b
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp [reindex_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

/-- Matrix multiplication of a bordered matrix, entry by entry. -/
theorem border_mul_apply [CommRing R] (B' : Matrix (Fin r) (Fin r) R) (col' ρ' : Fin r → R) (δ' : R)
    (a b : Fin (r + 1)) :
    (border B col ρ δ * border B' col' ρ' δ') a b =
      ∑ c : Fin r, border B col ρ δ a c.castSucc * border B' col' ρ' δ' c.castSucc b +
        border B col ρ δ a (Fin.last r) * border B' col' ρ' δ' (Fin.last r) b := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]

end Def

section Field

variable {K : Type*} [Field K] {r : ℕ} (B : Matrix (Fin r) (Fin r) K) (col ρ : Fin r → K) (δ : K)

/-- **C1** over a field: `det [[B, col], [ρᵀ, δ]] = δ·det B − ρ·(adj B col)` when `det B ≠ 0`. -/
theorem det_border_field (hB : B.det ≠ 0) :
    (border B col ρ δ).det = δ * B.det - ρ ⬝ᵥ (B.adjugate *ᵥ col) := by
  have : Invertible B := invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hB)
  rw [border_eq_reindex, det_reindex_self, det_fromBlocks₁₁, invOf_eq_nonsing_inv,
    Matrix.det_fin_one, Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.sub_apply, of_apply, Matrix.mul_apply, Matrix.smul_apply, replicateRow_apply,
    replicateCol_apply, smul_eq_mul, dotProduct, mulVec]
  have h1 : ∑ j, (∑ i, ρ i * (B.det⁻¹ * B.adjugate i j)) * col j =
      B.det⁻¹ * ∑ i, ρ i * ∑ j, B.adjugate i j * col j := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1]
  field_simp

/-- **C2** over a field: the adjugate of the bordered matrix. -/
theorem adjugate_border_field (hB : B.det ≠ 0)
    (hB' : δ * B.det - ρ ⬝ᵥ (B.adjugate *ᵥ col) ≠ 0) :
    (border B col ρ δ).adjugate =
      border (Matrix.of fun a b => ((δ * B.det - ρ ⬝ᵥ (B.adjugate *ᵥ col)) * B.adjugate a b +
          (B.adjugate *ᵥ col) a * (ρ ᵥ* B.adjugate) b) / B.det)
        (-(B.adjugate *ᵥ col)) (-(ρ ᵥ* B.adjugate)) B.det := by
  set Δ := B.det with hΔ
  set Aj := B.adjugate with hAj
  set Δ' := δ * Δ - ρ ⬝ᵥ (Aj *ᵥ col) with hΔ'
  set X := border (Matrix.of fun a b => (Δ' * Aj a b + (Aj *ᵥ col) a * (ρ ᵥ* Aj) b) / Δ)
    (-(Aj *ᵥ col)) (-(ρ ᵥ* Aj)) Δ with hX
  have hdet : (border B col ρ δ).det = Δ' := det_border_field B col ρ δ hB
  -- `B Aj = Δ I`, entry by entry, and its consequences
  have hBA : ∀ a b, ∑ c, B a c * Aj c b = if a = b then Δ else 0 := by
    intro a b
    have := congrFun (congrFun (mul_adjugate B) a) b
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [hΔ]
  have hBu : ∀ a, ∑ c, B a c * (Aj *ᵥ col) c = Δ * col a := by
    intro a
    have := congrFun (mulVec_mulVec col B Aj) a
    rw [hAj, mul_adjugate, smul_mulVec, one_mulVec] at this
    simpa [mulVec, dotProduct] using this
  have hρA : ∀ b, ∑ c, ρ c * Aj c b = (ρ ᵥ* Aj) b := fun b => by simp [vecMul, dotProduct]
  have hρu : ∑ c, ρ c * (Aj *ᵥ col) c = ρ ⬝ᵥ (Aj *ᵥ col) := rfl
  -- `B' X = Δ' I`
  have hmul : border B col ρ δ * X = Δ' • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) := by
    ext a b
    rw [hX, border_mul_apply]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases
    · simp only [border_ll, border_lc, border_cl, Pi.neg_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
        mul_one]
      simp only [mul_neg, Finset.sum_neg_distrib, hρu]
      rw [hΔ']; ring
    · rename_i b
      simp only [border_lc, border_cc, of_apply, border_ll, Pi.neg_apply, Matrix.smul_apply,
        smul_eq_mul]
      rw [one_apply_ne (Fin.castSucc_lt_last b).ne', mul_zero]
      have : ∀ c, ρ c * ((Δ' * Aj c b + (Aj *ᵥ col) c * (ρ ᵥ* Aj) b) / Δ) =
          (Δ' / Δ) * (ρ c * Aj c b) + ((ρ ᵥ* Aj) b / Δ) * (ρ c * (Aj *ᵥ col) c) :=
        fun c => by ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hρA, hρu]
      rw [hΔ']
      field_simp
      ring
    · rename_i a
      simp only [border_cl, border_cc, border_ll, Pi.neg_apply, Matrix.smul_apply,
        smul_eq_mul]
      rw [one_apply_ne (Fin.castSucc_lt_last a).ne, mul_zero]
      have : ∀ c, B a c * -(Aj *ᵥ col) c = -(B a c * (Aj *ᵥ col) c) := fun c => by ring
      simp only [this, Finset.sum_neg_distrib, hBu]
      ring
    · rename_i a b
      simp only [border_cc, border_cl, of_apply, border_lc, Pi.neg_apply, Matrix.smul_apply,
        smul_eq_mul]
      have : ∀ c, B a c * ((Δ' * Aj c b + (Aj *ᵥ col) c * (ρ ᵥ* Aj) b) / Δ) =
          (Δ' / Δ) * (B a c * Aj c b) + ((ρ ᵥ* Aj) b / Δ) * (B a c * (Aj *ᵥ col) c) :=
        fun c => by ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hBA, hBu]
      by_cases hab : a = b
      · subst hab
        simp only [↓reduceIte, one_apply_eq]
        field_simp
        ring
      · rw [one_apply_ne (fun h => hab (Fin.castSucc_injective _ h))]
        simp only [hab, ↓reduceIte]
        field_simp
        ring
  have hunit : IsUnit (border B col ρ δ) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hdet ▸ hB'))
  apply hunit.mul_left_cancel
  rw [mul_adjugate, hdet, hmul]

end Field

section Int

variable {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) (col ρ : Fin r → ℤ) (δ : ℤ)

/-- **C1** over `ℤ`: `det [[B, col], [ρᵀ, δ]] = δ·det B − ρ·(adj B col)` when `det B ≠ 0`. -/
theorem det_border (hB : B.det ≠ 0) :
    (border B col ρ δ).det = δ * B.det - ρ ⬝ᵥ (B.adjugate *ᵥ col) := by
  set f := Int.castRingHom ℚ with hf
  apply Int.cast_injective (α := ℚ)
  have hB' : (f.mapMatrix B).det ≠ 0 := by
    rw [← RingHom.map_det]; simpa [f] using hB
  have h := det_border_field (f.mapMatrix B) (fun a => f (col a)) (fun a => f (ρ a)) (f δ) hB'
  rw [← border_map, ← RingHom.map_det, ← RingHom.map_adjugate, ← RingHom.map_det] at h
  simp only [f, eq_intCast] at h
  rw [h]
  simp [dotProduct, mulVec]

/-- **C2** over `ℤ`: the adjugate of the bordered matrix, with the exact integer division by `Δ`
(as computed by the algorithm). -/
theorem adjugate_border (hB : B.det ≠ 0) (hB' : δ * B.det - ρ ⬝ᵥ (B.adjugate *ᵥ col) ≠ 0) :
    (border B col ρ δ).adjugate =
      border (Matrix.of fun a b => ((δ * B.det - ρ ⬝ᵥ (B.adjugate *ᵥ col)) * B.adjugate a b +
          (B.adjugate *ᵥ col) a * (ρ ᵥ* B.adjugate) b) / B.det)
        (-(B.adjugate *ᵥ col)) (-(ρ ᵥ* B.adjugate)) B.det := by
  set f := Int.castRingHom ℚ with hf
  have hBq : (f.mapMatrix B).det ≠ 0 := by
    rw [← RingHom.map_det]; simpa [f] using hB
  have hΔ'q : f δ * (f.mapMatrix B).det -
      (fun a => f (ρ a)) ⬝ᵥ ((f.mapMatrix B).adjugate *ᵥ fun a => f (col a)) ≠ 0 := by
    rw [← RingHom.map_adjugate, ← RingHom.map_det]
    have : ((δ * B.det - ρ ⬝ᵥ (B.adjugate *ᵥ col) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hB'
    simpa [f, dotProduct, mulVec] using this
  have hq := adjugate_border_field (f.mapMatrix B) (fun a => f (col a)) (fun a => f (ρ a))
    (f δ) hBq hΔ'q
  rw [← border_map, ← RingHom.map_adjugate, ← RingHom.map_adjugate, ← RingHom.map_det] at hq
  have hBq' : (B.det : ℚ) ≠ 0 := by exact_mod_cast hB
  ext a b
  have hab := congrFun (congrFun hq a) b
  simp only [RingHom.mapMatrix_apply, map_apply, f, eq_intCast] at hab
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · simp only [border_ll] at hab ⊢
    exact_mod_cast hab
  · rename_i b
    simp only [border_lc, Pi.neg_apply] at hab ⊢
    apply Int.cast_injective (α := ℚ)
    rw [hab]
    simp [vecMul, dotProduct]
  · rename_i a
    simp only [border_cl, Pi.neg_apply] at hab ⊢
    apply Int.cast_injective (α := ℚ)
    rw [hab]
    simp [mulVec, dotProduct]
  · rename_i a b
    simp only [border_cc, of_apply] at hab ⊢
    -- `Δ · adj B' a b = Δ' Aj + u v` in `ℤ`, so the division is exact
    have hnum : B.det * (border B col ρ δ).adjugate a.castSucc b.castSucc =
        (δ * B.det - ρ ⬝ᵥ (B.adjugate *ᵥ col)) * B.adjugate a b +
          (B.adjugate *ᵥ col) a * (ρ ᵥ* B.adjugate) b := by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_mul, hab]
      field_simp
      simp [dotProduct, mulVec, vecMul, mul_comm]
    rw [← hnum, Int.mul_ediv_cancel_left _ hB]

end Int

end STACS2027.Runtimes.ConvexQP
