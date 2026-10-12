module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

/-!
# Lemma 16, Part B: quadratic forms, ellipsoids and determinant monotonicity (B1–B5)

Vectors are `ι → ℝ` for a finite index type `ι`,
matrices `Matrix ι ι ℝ`; `qf Q v = v·Qv` is the quadratic form, `FormGe Q ℓ` (`Q ⪰ ℓI`) and
`FormLe Q u` (`Q ⪯ uI`) are the Loewner bounds against multiples of the identity.

* **Ellipsoids in support form** (`InEll Q a x`): `(v·(x − a))² ≤ v·Qv` for all `v`. No inverse is
  needed in the definition; monotonicity in the Loewner order (B3, `inEll_mono`) is immediate.
* **B1** (`sq_dot_le`): Cauchy–Schwarz for positive semidefinite symmetric forms,
  `(u·Qw)² ≤ (u·Qu)(w·Qw)` (non-positive discriminant).
* **B2** in the image form used by the update lemma: `x ∈ E(Q,a)` iff `x − a = Qz` for some `z`
  with `z·Qz ≤ 1` (`inEll_of_image`, and `image_of_inEll` for positive definite `Q`, the only place
  where an inverse matrix appears).
* **B4** (`formGe_of_ball`): an inner ball of radius `ρ` forces `Q ⪰ ρ²I`.
* **B5** (`det_le_det_of_le`): determinant monotonicity in the Loewner order;
  corollaries `pow_le_det` (`Q ⪰ ℓI ⟹ det Q ≥ ℓⁿ`) and `det_le_det_of_form`.
* Entry bounds for the magnitude analysis (`abs_entry_le`, `sq_mulVec_le`).
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Matrix
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι]

/-- The quadratic form `v·Qv`. -/
def qf (Q : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (Q *ᵥ v)

/-- `Q ⪰ ℓ I`: `ℓ ‖v‖² ≤ v·Qv` for all `v`. -/
def FormGe (Q : Matrix ι ι ℝ) (ℓ : ℝ) : Prop := ∀ v, ℓ * (v ⬝ᵥ v) ≤ qf Q v

/-- `Q ⪯ u I`: `v·Qv ≤ u ‖v‖²` for all `v`. -/
def FormLe (Q : Matrix ι ι ℝ) (u : ℝ) : Prop := ∀ v, qf Q v ≤ u * (v ⬝ᵥ v)

/-- The ellipsoid `E(Q, a)` in support form: `(v·(x − a))² ≤ v·Qv` for all `v`. -/
def InEll (Q : Matrix ι ι ℝ) (a x : ι → ℝ) : Prop := ∀ v, (v ⬝ᵥ (x - a)) ^ 2 ≤ qf Q v

theorem dot_self_nonneg (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem dot_self_pos {v : ι → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have h := (dotProduct_star_self_pos_iff (v := v)).mpr hv
  simpa using h

omit [Fintype ι] in
theorem isHermitian_of_isSymm {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) : Q.IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]
  exact hQ

/-- For symmetric `Q`, `u·Qw = w·Qu`. -/
theorem dot_mulVec_comm {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (u w : ι → ℝ) :
    u ⬝ᵥ (Q *ᵥ w) = w ⬝ᵥ (Q *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hQ.eq, dotProduct_comm]

theorem qf_add_smul {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (u w : ι → ℝ) (τ : ℝ) :
    qf Q (u + τ • w) = qf Q u + 2 * τ * (u ⬝ᵥ (Q *ᵥ w)) + τ ^ 2 * qf Q w := by
  simp only [qf, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [dot_mulVec_comm hQ w u]
  ring

theorem qf_smul (Q : Matrix ι ι ℝ) (c : ℝ) (v : ι → ℝ) : qf (c • Q) v = c * qf Q v := by
  simp [qf, smul_mulVec, dotProduct_smul]

theorem qf_sub (Q M : Matrix ι ι ℝ) (v : ι → ℝ) : qf (Q - M) v = qf Q v - qf M v := by
  simp [qf, sub_mulVec, dotProduct_sub]

theorem qf_add (Q M : Matrix ι ι ℝ) (v : ι → ℝ) : qf (Q + M) v = qf Q v + qf M v := by
  simp [qf, add_mulVec, dotProduct_add]


theorem qf_vecMulVec (b v : ι → ℝ) : qf (vecMulVec b b) v = (v ⬝ᵥ b) ^ 2 := by
  simp only [qf, mulVec, dotProduct, vecMulVec_apply]
  rw [sq, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


section DecEq

variable [DecidableEq ι]

theorem qf_one (v : ι → ℝ) : qf (1 : Matrix ι ι ℝ) v = v ⬝ᵥ v := by
  simp [qf]

theorem qf_neg_smul_self_le {Q : Matrix ι ι ℝ} {ℓ : ℝ} (h : FormGe Q ℓ) (v : ι → ℝ) :
    0 ≤ qf (Q - ℓ • 1) v := by
  rw [qf_sub, qf_smul, qf_one]
  linarith [h v]

end DecEq

/-! ### B1: Cauchy–Schwarz for positive semidefinite forms -/

/-- **B1.** For symmetric `Q` with `v·Qv ≥ 0`: `(u·Qw)² ≤ (u·Qu)(w·Qw)`. -/
theorem sq_dot_le {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hpsd : ∀ v, 0 ≤ qf Q v) (u w : ι → ℝ) :
    (u ⬝ᵥ (Q *ᵥ w)) ^ 2 ≤ qf Q u * qf Q w := by
  have h := discrim_le_zero (a := qf Q w) (b := 2 * (u ⬝ᵥ (Q *ᵥ w))) (c := qf Q u) fun τ => by
    have := hpsd (u + τ • w)
    rw [qf_add_smul hQ] at this
    nlinarith [this]
  unfold discrim at h
  nlinarith [h]

/-! ### Ellipsoids: monotonicity (B3) and the image form (B2) -/

/-- **B3.** `Q ⪯ Q'` implies `E(Q, a) ⊆ E(Q', a)`. -/
theorem inEll_mono {Q Q' : Matrix ι ι ℝ} {a x : ι → ℝ} (hle : ∀ v, qf Q v ≤ qf Q' v)
    (hx : InEll Q a x) : InEll Q' a x :=
  fun v => (hx v).trans (hle v)

/-- **B2 (⇐).** If `x − a = Qz` with `z·Qz ≤ 1`, then `x ∈ E(Q, a)`. -/
theorem inEll_of_image {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hpsd : ∀ v, 0 ≤ qf Q v)
    {a x z : ι → ℝ} (hx : x - a = Q *ᵥ z) (hz : qf Q z ≤ 1) : InEll Q a x := by
  intro v
  rw [hx]
  have h := sq_dot_le hQ hpsd v z
  nlinarith [hpsd v, hpsd z]

/-- **B2 (⇒)** for positive definite `Q`: a point of `E(Q, a)` is `a + Qz` with `z·Qz ≤ 1`. -/
theorem image_of_inEll [DecidableEq ι] {Q : Matrix ι ι ℝ} (hpd : Q.PosDef) {a x : ι → ℝ} (hx : InEll Q a x) :
    ∃ z, x - a = Q *ᵥ z ∧ qf Q z ≤ 1 := by
  have hdet : IsUnit Q.det := (ne_of_gt hpd.det_pos).isUnit
  refine ⟨Q⁻¹ *ᵥ (x - a), ?_, ?_⟩
  · rw [mulVec_mulVec, mul_nonsing_inv Q hdet, one_mulVec]
  · have hw : Q *ᵥ (Q⁻¹ *ᵥ (x - a)) = x - a := by
      rw [mulVec_mulVec, mul_nonsing_inv Q hdet, one_mulVec]
    have h := hx (Q⁻¹ *ᵥ (x - a))
    unfold qf at h ⊢
    rw [hw] at h ⊢
    nlinarith [h]

/-! ### B4: an inner ball forces a Loewner lower bound -/

/-- **B4.** If the ball of radius `ρ` around `z` lies in `E(Q, a)`, then `Q ⪰ ρ² I`. -/
theorem formGe_of_ball {Q : Matrix ι ι ℝ} {a z : ι → ℝ} {ρ : ℝ}
    (hball : ∀ y, (y - z) ⬝ᵥ (y - z) ≤ ρ ^ 2 → InEll Q a y) : FormGe Q (ρ ^ 2) := by
  intro v
  by_cases hv : v = 0
  · subst hv
    simp [qf]
  · have hpos := dot_self_pos hv
    set r := Real.sqrt (v ⬝ᵥ v) with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
    have hrr : r * r = v ⬝ᵥ v := Real.mul_self_sqrt hpos.le
    have hy : ∀ σ : ℝ, σ ^ 2 = 1 →
        (v ⬝ᵥ (z - a) + σ * ρ * r) ^ 2 ≤ qf Q v := by
      intro σ hσ
      have hmem := hball (z + (σ * ρ / r) • v) (by
        rw [add_sub_cancel_left, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          ← hrr]
        field_simp
        nlinarith [hσ])
      have h := hmem v
      have e : v ⬝ᵥ (z + (σ * ρ / r) • v - a) = v ⬝ᵥ (z - a) + σ * ρ * r := by
        rw [show z + (σ * ρ / r) • v - a = (z - a) + (σ * ρ / r) • v by abel, dotProduct_add,
          dotProduct_smul, smul_eq_mul, ← hrr]
        field_simp
      rwa [e] at h
    have h1 := hy 1 (by norm_num)
    have h2 := hy (-1) (by norm_num)
    rw [← hrr]
    nlinarith [h1, h2, sq_nonneg (v ⬝ᵥ (z - a))]

/-! ### B5: determinant monotonicity -/

/-- Positive semidefiniteness from the quadratic form. -/
theorem posSemidef_of_form {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (h : ∀ v, 0 ≤ qf Q v) :
    Q.PosSemidef :=
  .of_dotProduct_mulVec_nonneg (isHermitian_of_isSymm hQ) fun x => by simpa [qf] using h x

/-- Positive definiteness from a Loewner lower bound `Q ⪰ ℓ I`, `ℓ > 0`. -/
theorem posDef_of_formGe {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : FormGe Q ℓ) : Q.PosDef :=
  .of_dotProduct_mulVec_pos (isHermitian_of_isSymm hQ) fun x hx => by
    have := h x
    have := dot_self_pos hx
    have : 0 < qf Q x := by nlinarith
    simpa [qf] using this

theorem formGe_nonneg {Q : Matrix ι ι ℝ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (h : FormGe Q ℓ) (v : ι → ℝ) :
    0 ≤ qf Q v :=
  le_trans (mul_nonneg hℓ (dot_self_nonneg v)) (h v)


section DecEq

variable [DecidableEq ι]

/-- If `B − 1` is positive semidefinite then `1 ≤ det B` (every eigenvalue of `B` is a Rayleigh
quotient at a unit eigenvector, hence `≥ 1`). -/
theorem one_le_det_of_one_le {B : Matrix ι ι ℝ} (hB : (B - 1).PosSemidef) : 1 ≤ B.det := by
  have hH : B.IsHermitian := by
    have : B = (B - 1) + 1 := by abel
    rw [this]; exact hB.1.add isHermitian_one
  rw [hH.det_eq_prod_eigenvalues]
  have key : ∀ i, 1 ≤ hH.eigenvalues i := by
    intro i
    have he := hH.eigenvalues_eq i
    set v := ⇑(hH.eigenvectorBasis i) with hv
    have hnorm : star v ⬝ᵥ v = 1 := by
      have h1 := hH.eigenvectorBasis.orthonormal.1 i
      have h2 := EuclideanSpace.inner_eq_star_dotProduct (hH.eigenvectorBasis i)
        (hH.eigenvectorBasis i)
      rw [real_inner_self_eq_norm_sq, h1] at h2
      rw [dotProduct_comm]; simpa [v] using h2.symm
    have hpsd := hB.re_dotProduct_nonneg v
    have hsplit : star v ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((B - 1) *ᵥ v) + star v ⬝ᵥ v := by
      rw [sub_mulVec, one_mulVec, dotProduct_sub]; ring
    rw [he, hsplit, hnorm]
    simp only [RCLike.re_to_real] at hpsd ⊢
    linarith
  exact Finset.one_le_prod₀ (fun i _ => key i)

/-- **B5.** Determinant monotonicity in the Loewner order: `0 < A ⪯ B` implies
`det A ≤ det B`. -/
theorem det_le_det_of_le {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hAB : (B - A).PosSemidef) :
    A.det ≤ B.det := by
  set S := CFC.sqrt A with hS
  have hSnn : 0 ≤ S := CFC.sqrt_nonneg A
  have hSH : S.IsHermitian := (nonneg_iff_posSemidef.mp hSnn).1
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hdetA : 0 < A.det := hA.det_pos
  have hdetS : S.det ≠ 0 := by
    intro h0; rw [← hSS, det_mul, h0, zero_mul] at hdetA; exact lt_irrefl _ hdetA
  have hSu : IsUnit S := (isUnit_iff_isUnit_det S).mpr (Ne.isUnit hdetS)
  set T := S⁻¹ with hT
  have hTS : T * S = 1 := nonsing_inv_mul S ((isUnit_iff_isUnit_det S).mp hSu)
  have hST : S * T = 1 := mul_nonsing_inv S ((isUnit_iff_isUnit_det S).mp hSu)
  have hTH : Tᴴ = T := by
    rw [hT, conjTranspose_nonsing_inv, hSH.eq]
  set M := T * (B - A) * T with hM
  have hMpsd : M.PosSemidef := by
    have := hAB.mul_mul_conjTranspose_same T
    rwa [hTH] at this
  have hB : B = S * (1 + M) * S := by
    rw [hM, mul_add, add_mul, mul_one, hSS, ← mul_assoc, ← mul_assoc, hST, one_mul,
      mul_assoc, hTS, mul_one]; abel
  have h1M : ((1 + M) - 1).PosSemidef := by simpa using hMpsd
  have hdet1M := one_le_det_of_one_le h1M
  rw [hB, det_mul, det_mul, ← hSS, det_mul]
  have hSd : 0 < S.det * S.det := mul_self_pos.mpr hdetS
  nlinarith

/-- **B5, corollary.** `Q ⪰ ℓ I` with `ℓ > 0` implies `det Q ≥ ℓⁿ`. -/
theorem pow_le_det {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) {ℓ : ℝ} (hℓ : 0 < ℓ) (h : FormGe Q ℓ) :
    ℓ ^ Fintype.card ι ≤ Q.det := by
  have hA : (ℓ • (1 : Matrix ι ι ℝ)).PosDef := by
    refine posDef_of_formGe ?_ hℓ fun v => ?_
    · exact (isSymm_one).smul ℓ
    · rw [qf_smul, qf_one]
  have hAB : (Q - ℓ • (1 : Matrix ι ι ℝ)).PosSemidef :=
    posSemidef_of_form (hQ.sub ((isSymm_one).smul ℓ)) (qf_neg_smul_self_le h)
  have := det_le_det_of_le hA hAB
  rwa [det_smul, det_one, mul_one] at this

/-- **B5, corollary.** For positive definite `Q` and symmetric `M` with `Q ⪯ M`:
`det Q ≤ det M`. -/
theorem det_le_det_of_form {Q M : Matrix ι ι ℝ} (hpd : Q.PosDef) (hM : M.IsSymm)
    (hQ : Q.IsSymm) (h : ∀ v, qf Q v ≤ qf M v) : Q.det ≤ M.det :=
  det_le_det_of_le hpd (posSemidef_of_form (hM.sub hQ) fun v => by
    rw [qf_sub]; linarith [h v])

/-! ### Entry bounds (for the magnitude analysis) -/

theorem qf_single (Q : Matrix ι ι ℝ) (i : ι) : qf Q (Pi.single i 1) = Q i i := by
  simp [qf]

theorem dot_single_mulVec (Q : Matrix ι ι ℝ) (i j : ι) :
    Pi.single i 1 ⬝ᵥ (Q *ᵥ Pi.single j 1) = Q i j := by
  simp

/-- `(Qg)_i² ≤ Q_ii · g·Qg` for positive semidefinite symmetric `Q`. -/
theorem sq_mulVec_le {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hpsd : ∀ v, 0 ≤ qf Q v)
    (g : ι → ℝ) (i : ι) : (Q *ᵥ g) i ^ 2 ≤ Q i i * qf Q g := by
  have h := sq_dot_le hQ hpsd (Pi.single i 1) g
  rw [qf_single] at h
  simpa using h

theorem diag_le {Q : Matrix ι ι ℝ} {u : ℝ} (h : FormLe Q u) (i : ι) : Q i i ≤ u := by
  have := h (Pi.single i 1)
  rw [qf_single] at this
  simpa using this

/-- Entries of a positive semidefinite symmetric `Q ⪯ uI` are at most `u` in absolute value. -/
theorem abs_entry_le {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hpsd : ∀ v, 0 ≤ qf Q v) {u : ℝ}
    (h : FormLe Q u) (i j : ι) : |Q i j| ≤ u := by
  have h1 := sq_dot_le hQ hpsd (Pi.single i 1) (Pi.single j 1)
  rw [dot_single_mulVec, qf_single, qf_single] at h1
  have hi := diag_le h i
  have hj := diag_le h j
  have hi0 : 0 ≤ Q i i := by have := hpsd (Pi.single i 1); rwa [qf_single] at this
  have hj0 : 0 ≤ Q j j := by have := hpsd (Pi.single j 1); rwa [qf_single] at this
  have hu : 0 ≤ u := hi0.trans hi
  apply abs_le_of_sq_le_sq _ hu
  nlinarith [mul_le_mul hi hj hj0 hu]

end DecEq

end STACS2027.Runtimes.ConvexQP
