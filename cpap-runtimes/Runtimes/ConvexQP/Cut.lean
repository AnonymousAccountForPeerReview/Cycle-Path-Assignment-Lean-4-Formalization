module

public import Runtimes.ConvexQP.Loewner
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Lemma 16, Part B: the central cut, exact (B6) and rounded (B7)

`n = |ι| ≥ 2` is the dimension. For a symmetric
positive definite `Q`, a center `a` and a cut vector `g ≠ 0` with `γ = g·Qg`:

* `cutMat n Q g = Q⁺ = κ (Q − (2/(n+1)) (Qg)(Qg)ᵀ / γ)` with `κ = n²/(n²−1)` (`kap`; no square
  root), and `cutCenter n Q a g s = a − Qg / ((n+1) s)` (the exact center `a⁺` is `s = √γ`).
* **B6** (`cutMat_ge`, `cutMat_le`, `det_cutMat`, `inEll_cut`):
  (i) `(n/(n+1))² Q ⪯ Q⁺ ⪯ κ Q`; (ii) `det Q⁺ = κⁿ (n−1)/(n+1) det Q` (matrix determinant
  lemma); (iii) `E(Q, a) ∩ {g·(x − a) ≤ 0} ⊆ E(Q⁺, a⁺)`, proved in the image form of B2 with the
  explicit preimage `z⁺ = κ⁻¹ (y + (τ m/γ) g)` (`τ = 2/(n−1)`), so that no inverse of `Q⁺` is
  needed.
* **B7** (`cut_rounded`): if `Q ⪰ ℓI`, `0 < η ≤ 1/8`, `|s − √γ| ≤ (η/4)√γ`, and `(Q', a')` is an
  `ϵ`-rounding (`RoundOf`) of `((1+η)³Q⁺, a − Qg/((n+1)s))` with `nϵ ≤ ηℓ⁺` and
  `nϵ² ≤ (η/4)²ℓ⁺` (`ℓ⁺ = (n/(n+1))²ℓ`), then `(1+η)²Q⁺ ⪯ Q' ⪯ (1+η)⁴Q⁺` (so `Q' ⪰ ℓ⁺I`), the
  half-ellipsoid lies in `E(Q', a')`, and `det Q' ≤ (1+η)^{4n} κⁿ (n−1)/(n+1) det Q`.
  For the magnitude analysis: `Q ⪯ uI ⟹ Q' ⪯ (1+η)⁴κu I`, and the center moves by at most `√u`
  per coordinate before rounding (`abs_cutCenter_sub_le`).
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Matrix

variable {ι : Type*} [Fintype ι]

/-- `κ = n²/(n²−1)`. -/
noncomputable def kap (n : ℝ) : ℝ := n ^ 2 / (n ^ 2 - 1)

/-- The exact cut matrix `Q⁺ = κ (Q − (2/((n+1)γ)) (Qg)(Qg)ᵀ)`, `γ = g·Qg`. -/
noncomputable def cutMat (n : ℝ) (Q : Matrix ι ι ℝ) (g : ι → ℝ) : Matrix ι ι ℝ :=
  kap n • (Q - (2 / ((n + 1) * qf Q g)) • vecMulVec (Q *ᵥ g) (Q *ᵥ g))

/-- The cut center `a − Qg/((n+1)s)`; the exact center `a⁺` has `s = √γ`. -/
noncomputable def cutCenter (n : ℝ) (Q : Matrix ι ι ℝ) (a g : ι → ℝ) (s : ℝ) : ι → ℝ :=
  a - (1 / ((n + 1) * s)) • (Q *ᵥ g)

/-- `(Q', a')` is an `ϵ`-rounding of `(M, b)`: `Q'` symmetric, entries within `ϵ`. -/
structure RoundOf (ϵ : ℝ) (Q' : Matrix ι ι ℝ) (a' : ι → ℝ) (M : Matrix ι ι ℝ) (b : ι → ℝ) :
    Prop where
  symm : Q'.IsSymm
  center : ∀ i, |a' i - b i| ≤ ϵ
  mat : ∀ i j, |Q' i j - M i j| ≤ ϵ

theorem kap_pos {n : ℝ} (hn : 1 < n) : 0 < kap n := by
  unfold kap
  have : 0 < n ^ 2 - 1 := by nlinarith
  positivity

theorem vecMulVec_mulVec' (u v w : ι → ℝ) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cutMat_symm {n : ℝ} {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (g : ι → ℝ) :
    (cutMat n Q g).IsSymm := by
  unfold cutMat
  refine IsSymm.smul (hQ.sub (IsSymm.smul ?_ _)) _
  unfold IsSymm
  rw [transpose_vecMulVec]

theorem qf_cutMat (n : ℝ) (Q : Matrix ι ι ℝ) (g v : ι → ℝ) :
    qf (cutMat n Q g) v =
      kap n * (qf Q v - 2 / ((n + 1) * qf Q g) * (v ⬝ᵥ (Q *ᵥ g)) ^ 2) := by
  unfold cutMat
  rw [qf_smul, qf_sub, qf_smul, qf_vecMulVec]

/-- **B6(i)**, lower bound: `(n/(n+1))² Q ⪯ Q⁺`. -/
theorem cutMat_ge {n : ℝ} (hn : 1 < n) {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (hpsd : ∀ v, 0 ≤ qf Q v) {g : ι → ℝ} (hγ : 0 < qf Q g) (v : ι → ℝ) :
    (n / (n + 1)) ^ 2 * qf Q v ≤ qf (cutMat n Q g) v := by
  rw [qf_cutMat]
  have hcs := sq_dot_le hQ hpsd v g
  have hv := hpsd v
  have hn1 : 0 < n + 1 := by linarith
  have h1 : 2 / ((n + 1) * qf Q g) * (v ⬝ᵥ (Q *ᵥ g)) ^ 2 ≤ 2 / (n + 1) * qf Q v := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : 2 / (n + 1) * qf Q v * ((n + 1) * qf Q g) = 2 * (qf Q v * qf Q g) := by
      field_simp
    rw [this]
    linarith
  have hk : kap n * (1 - 2 / (n + 1)) = (n / (n + 1)) ^ 2 := by
    unfold kap
    have : n ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  have hkp := kap_pos hn
  calc (n / (n + 1)) ^ 2 * qf Q v = kap n * (qf Q v - 2 / (n + 1) * qf Q v) := by
        rw [← hk]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hkp.le

/-- **B6(i)**, upper bound: `Q⁺ ⪯ κ Q`. -/
theorem cutMat_le {n : ℝ} (hn : 1 < n) (Q : Matrix ι ι ℝ) {g : ι → ℝ} (hγ : 0 < qf Q g)
    (v : ι → ℝ) : qf (cutMat n Q g) v ≤ kap n * qf Q v := by
  rw [qf_cutMat]
  have : 0 ≤ 2 / ((n + 1) * qf Q g) * (v ⬝ᵥ (Q *ᵥ g)) ^ 2 := by
    have : 0 < n + 1 := by linarith
    positivity
  have := kap_pos hn
  nlinarith

/-- **B6(ii)** (matrix determinant lemma): `det Q⁺ = κⁿ (n−1)/(n+1) det Q`. -/
theorem det_cutMat [DecidableEq ι] {n : ℝ} (hn : 1 < n) {Q : Matrix ι ι ℝ} {g : ι → ℝ} (hγ : 0 < qf Q g) :
    (cutMat n Q g).det = kap n ^ Fintype.card ι * ((n - 1) / (n + 1)) * Q.det := by
  set c := 2 / ((n + 1) * qf Q g) with hc
  have hfac : Q - c • vecMulVec (Q *ᵥ g) (Q *ᵥ g) =
      Q * (1 + vecMulVec ((-c) • g) (Q *ᵥ g)) := by
    rw [mul_add, mul_one, mul_vecMulVec, mulVec_smul, smul_vecMulVec, neg_smul,
      sub_eq_add_neg]
  have hdet1 : (1 + vecMulVec ((-c) • g) (Q *ᵥ g)).det = (n - 1) / (n + 1) := by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
      dotProduct_comm, ← qf, hc, smul_eq_mul]
    have : n + 1 ≠ 0 := by linarith
    field_simp
    ring
  unfold cutMat
  rw [det_smul, ← hc, hfac, det_mul, hdet1]
  ring

/-- The scalar inequality behind **B6(iii)**: for `σ ∈ [−1, 0]` with `σ² ≤ q ≤ 1`,
`q + 2σ/(n+1) + 1/(n+1)² + τ(σ + 1/(n+1))² = q − 1 + κ + τσ(σ+1) ≤ κ`. -/
theorem cut_scalar {n q σ : ℝ} (hn : 1 < n) (hq : q ≤ 1) (hσ0 : σ ≤ 0) (hσq : σ ^ 2 ≤ q) :
    q + 2 * σ / (n + 1) + 1 / (n + 1) ^ 2 + 2 / (n - 1) * (σ + 1 / (n + 1)) ^ 2 ≤ kap n := by
  have hn1 : n - 1 ≠ 0 := by linarith
  have hn2 : n + 1 ≠ 0 := by linarith
  have hn3 : n ^ 2 - 1 ≠ 0 := by nlinarith
  have key : q + 2 * σ / (n + 1) + 1 / (n + 1) ^ 2 + 2 / (n - 1) * (σ + 1 / (n + 1)) ^ 2 =
      q - 1 + kap n + 2 / (n - 1) * (σ * (σ + 1)) := by
    unfold kap
    field_simp
    ring
  have hσ1 : -1 ≤ σ := by nlinarith
  have h1 : σ * (σ + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hσ0 (by linarith)
  have h2 : 0 < 2 / (n - 1) := div_pos two_pos (by linarith)
  rw [key]
  nlinarith

/-- **B6(iii).** The exact central cut: `E(Q, a) ∩ {x : g·(x − a) ≤ 0} ⊆ E(Q⁺, a⁺)`. -/
theorem inEll_cut [DecidableEq ι] {n : ℝ} (hn : 1 < n) {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (hpd : Q.PosDef) {a g x : ι → ℝ} (hγ : 0 < qf Q g) (hx : InEll Q a x)
    (hcut : g ⬝ᵥ (x - a) ≤ 0) :
    InEll (cutMat n Q g) (cutCenter n Q a g (Real.sqrt (qf Q g))) x := by
  have hpsd : ∀ v, 0 ≤ qf Q v := fun v => by
    have := hpd.posSemidef.dotProduct_mulVec_nonneg v
    simpa [qf] using this
  obtain ⟨z, hz, hzq⟩ := image_of_inEll hpd hx
  set γ := qf Q g with hγdef
  set r := Real.sqrt γ with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hγ
  have hrr : r * r = γ := Real.mul_self_sqrt hγ.le
  have hn1 : 0 < n + 1 := by linarith
  set c' := 1 / ((n + 1) * r) with hc'
  set y := z + c' • g with hy
  have hxy : x - cutCenter n Q a g r = Q *ᵥ y := by
    unfold cutCenter
    rw [hy, mulVec_add, mulVec_smul, ← hz]
    abel
  set m := g ⬝ᵥ (Q *ᵥ y) with hm
  set τ := 2 / (n - 1) with hτ
  set z' := (kap n)⁻¹ • (y + (τ * m / γ) • g) with hz'
  have hκ := kap_pos hn
  have hdot1 : (Q *ᵥ g) ⬝ᵥ y = m := by rw [dotProduct_comm, dot_mulVec_comm hQ]
  have hdot2 : (Q *ᵥ g) ⬝ᵥ g = γ := by rw [dotProduct_comm]; rfl
  have hQz' : cutMat n Q g *ᵥ z' = Q *ᵥ y := by
    have h1 : cutMat n Q g *ᵥ z' = kap n • (Q *ᵥ z' -
        (2 / ((n + 1) * γ) * ((Q *ᵥ g) ⬝ᵥ z')) • (Q *ᵥ g)) := by
      unfold cutMat
      rw [smul_mulVec, sub_mulVec, smul_mulVec, vecMulVec_mulVec', smul_smul]
    have h2 : (Q *ᵥ g) ⬝ᵥ z' = (kap n)⁻¹ * (m + τ * m) := by
      rw [hz', dotProduct_smul, dotProduct_add, dotProduct_smul, hdot1, hdot2, smul_eq_mul,
        smul_eq_mul]
      field_simp
    rw [h1, h2, hz', mulVec_smul, mulVec_add, mulVec_smul]
    have hn3 : n - 1 ≠ 0 := by linarith
    have hcoef : τ * m / γ - 2 / ((n + 1) * γ) * (m + τ * m) = 0 := by
      rw [hτ]
      field_simp
      ring
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    have : kap n * ((kap n)⁻¹ * ((Q *ᵥ y) i + τ * m / γ * (Q *ᵥ g) i) -
        2 / ((n + 1) * γ) * ((kap n)⁻¹ * (m + τ * m)) * (Q *ᵥ g) i) =
        (Q *ᵥ y) i + (τ * m / γ - 2 / ((n + 1) * γ) * (m + τ * m)) * (Q *ᵥ g) i := by
      field_simp
      ring
    rw [this, hcoef, zero_mul, add_zero]
  -- the value of the form at `z'`
  set gw := g ⬝ᵥ (x - a) with hgw
  have hzg : z ⬝ᵥ (Q *ᵥ g) = gw := by rw [dot_mulVec_comm hQ, ← hz]
  have hmval : m = gw + c' * γ := by
    rw [hm, hy, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, ← hz, smul_eq_mul]
    rfl
  have hqy : qf Q y = qf Q z + 2 * c' * gw + c' ^ 2 * γ := by
    rw [hy, qf_add_smul hQ, hzg]
  have hval : qf (cutMat n Q g) z' = (kap n)⁻¹ * (qf Q y + τ * m ^ 2 / γ) := by
    unfold qf
    rw [hQz', hz', smul_dotProduct, add_dotProduct, smul_dotProduct, ← hm, smul_eq_mul,
      smul_eq_mul]
    ring
  have hcs : gw ^ 2 ≤ γ * qf Q z := by
    have := sq_dot_le hQ hpsd g z
    rwa [← hz] at this
  -- reduce to the scalar inequality with `σ = gw / r`
  have hσ : (gw / r) ^ 2 ≤ qf Q z := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have hσ0 : gw / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcut hr.le
  have hsc := cut_scalar hn hzq hσ0 hσ
  have hle : qf (cutMat n Q g) z' ≤ 1 := by
    rw [hval]
    have e : qf Q y + τ * m ^ 2 / γ = qf Q z + 2 * (gw / r) / (n + 1) + 1 / (n + 1) ^ 2 +
        2 / (n - 1) * (gw / r + 1 / (n + 1)) ^ 2 := by
      rw [hqy, hmval, hc', hτ, ← hrr]
      field_simp
    rw [e, inv_mul_le_iff₀ hκ, mul_one]
    exact hsc
  have hpsd' : ∀ v, 0 ≤ qf (cutMat n Q g) v := fun v =>
    le_trans (mul_nonneg (by positivity) (hpsd v)) (cutMat_ge hn hQ hpsd hγ v)
  exact inEll_of_image (cutMat_symm hQ g) hpsd' (hxy.trans hQz'.symm) hle

/-! ### B7: the rounded central cut -/

/-- `|t| ≤ c √A` from `t² ≤ c² A`. -/
theorem abs_le_mul_sqrt {t c A : ℝ} (hc : 0 ≤ c) (h : t ^ 2 ≤ c ^ 2 * A) :
    |t| ≤ c * Real.sqrt A := by
  have h1 := Real.abs_le_sqrt h
  rwa [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc] at h1

theorem sum_abs_sq_le (v : ι → ℝ) : (∑ i, |v i|) ^ 2 ≤ Fintype.card ι * (v ⬝ᵥ v) := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |v i|)
  simp only [Finset.card_univ, sq_abs] at h
  simpa [dotProduct, sq] using h

/-- `|v·Rv| ≤ n ϵ ‖v‖²` for a matrix `R` with entries at most `ϵ` in absolute value. -/
theorem abs_qf_le {R : Matrix ι ι ℝ} {ϵ : ℝ} (hϵ : 0 ≤ ϵ) (h : ∀ i j, |R i j| ≤ ϵ)
    (v : ι → ℝ) : |qf R v| ≤ Fintype.card ι * ϵ * (v ⬝ᵥ v) := by
  have h1 : |qf R v| ≤ ϵ * (∑ i, |v i|) ^ 2 := by
    unfold qf
    simp only [dotProduct, mulVec]
    calc |∑ i, v i * ∑ j, R i j * v j| ≤ ∑ i, |v i * ∑ j, R i j * v j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |v i| * ∑ j, ϵ * |v j| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (h i j) (abs_nonneg _)
      _ = ϵ * (∑ i, |v i|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have h2 := sum_abs_sq_le v
  nlinarith [mul_le_mul_of_nonneg_left h2 hϵ]

/-- `(v·w)² ≤ n ϵ² ‖v‖²` for a vector `w` with entries at most `ϵ` in absolute value. -/
theorem sq_dot_le_of_abs {w : ι → ℝ} {ϵ : ℝ} (h : ∀ i, |w i| ≤ ϵ) (v : ι → ℝ) :
    (v ⬝ᵥ w) ^ 2 ≤ Fintype.card ι * ϵ ^ 2 * (v ⬝ᵥ v) := by
  have h1 : |v ⬝ᵥ w| ≤ ϵ * ∑ i, |v i| := by
    unfold dotProduct
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_comm ϵ]
    exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
  have h2 := sum_abs_sq_le v
  have h3 : (v ⬝ᵥ w) ^ 2 ≤ (ϵ * ∑ i, |v i|) ^ 2 := by
    rw [← sq_abs (v ⬝ᵥ w)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ϵ)]

/-- Scalar part of term 2 in **B7(b)**: `|1/s − 1/r|² r² ≤ (η/3)²` up to the factor
`1/(n+1)²`, for `|r − s| ≤ (η/4) r`. -/
theorem scalar_d {n r s η : ℝ} (hn : 2 ≤ n) (hr : 0 < r) (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    (hs : |r - s| ≤ η / 4 * r) :
    (1 / ((n + 1) * s) - 1 / ((n + 1) * r)) ^ 2 * (r * r) ≤ η ^ 2 / (9 * (n + 1) ^ 2) := by
  have hslo : (1 - η / 4) * r ≤ s := by
    have := (abs_le.mp hs).2
    linarith
  have hs0 : 0 < s := lt_of_lt_of_le (by nlinarith) hslo
  have hn1 : 0 < n + 1 := by linarith
  have e : (1 / ((n + 1) * s) - 1 / ((n + 1) * r)) ^ 2 * (r * r) =
      (r - s) ^ 2 / ((n + 1) ^ 2 * s ^ 2) := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (r - s) ^ 2 ≤ (η / 4 * r) ^ 2 := by
    rw [← sq_abs (r - s)]
    exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  have h2 : (1 - η / 4) ^ 2 * r ^ 2 ≤ s ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by nlinarith) hslo 2
  have h3 : 9 * (r - s) ^ 2 ≤ η ^ 2 * s ^ 2 := by
    have h4 : 9 * (η / 4 * r) ^ 2 ≤ η ^ 2 * ((1 - η / 4) ^ 2 * r ^ 2) := by
      have : (9 : ℝ) / 16 ≤ (1 - η / 4) ^ 2 := by nlinarith
      have h5 := mul_le_mul_of_nonneg_left this (mul_nonneg (sq_nonneg η) (sq_nonneg r))
      nlinarith [h5]
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg η)]
  have := mul_le_mul_of_nonneg_right h3 (sq_nonneg (n + 1))
  nlinarith [this]

/-- Scalar step in **B7(b)**: from `(n/(n+1))² q ≤ P` and `(1+η)² P ≤ A`,
`q ≤ ((n+1)/n)² A / (1+η)²`. -/
theorem scalar_qv {n η P A q : ℝ} (hn : 1 < n) (hη : 0 < η) (h1 : (n / (n + 1)) ^ 2 * q ≤ P)
    (h2 : (1 + η) ^ 2 * P ≤ A) : q ≤ ((n + 1) / n) ^ 2 / (1 + η) ^ 2 * A := by
  have hn0 : 0 < n := by linarith
  have hP : q ≤ ((n + 1) / n) ^ 2 * P := by
    have e : ((n + 1) / n) ^ 2 * ((n / (n + 1)) ^ 2 * q) = q := by
      field_simp
    calc q = ((n + 1) / n) ^ 2 * ((n / (n + 1)) ^ 2 * q) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hA : P ≤ A / (1 + η) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc q ≤ ((n + 1) / n) ^ 2 * P := hP
    _ ≤ ((n + 1) / n) ^ 2 * (A / (1 + η) ^ 2) := mul_le_mul_of_nonneg_left hA (sq_nonneg _)
    _ = _ := by ring

section Rounded

variable {Q Q' : Matrix ι ι ℝ} {a a' g : ι → ℝ} {ℓ η ϵ s : ℝ}

theorem qf_pos_of_formGe (hℓ : 0 < ℓ) (hQℓ : FormGe Q ℓ) (hg : g ≠ 0) : 0 < qf Q g :=
  lt_of_lt_of_le (mul_pos hℓ (dot_self_pos hg)) (hQℓ g)

/-- **B7(a).** `(1+η)² Q⁺ ⪯ Q' ⪯ (1+η)⁴ Q⁺` for an `ϵ`-rounding `Q'` of `(1+η)³ Q⁺`. -/
theorem rounded_form_bounds (hn : 2 ≤ Fintype.card ι) (hQ : Q.IsSymm) (hℓ : 0 < ℓ)
    (hQℓ : FormGe Q ℓ) (hη : 0 < η) (hg : g ≠ 0) (hϵ0 : 0 ≤ ϵ)
    (hϵ1 : (Fintype.card ι : ℝ) * ϵ ≤
      η * (((Fintype.card ι : ℝ) / (Fintype.card ι + 1)) ^ 2 * ℓ))
    (hmat : ∀ i j, |Q' i j - ((1 + η) ^ 3 • cutMat (Fintype.card ι) Q g) i j| ≤ ϵ)
    (v : ι → ℝ) :
    (1 + η) ^ 2 * qf (cutMat (Fintype.card ι) Q g) v ≤ qf Q' v ∧
      qf Q' v ≤ (1 + η) ^ 4 * qf (cutMat (Fintype.card ι) Q g) v := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn'
  have hn1 : 1 < n := by rw [hn']; exact_mod_cast hn
  have hγ := qf_pos_of_formGe hℓ hQℓ hg
  have hpsd := formGe_nonneg hℓ.le hQℓ
  set P := cutMat n Q g
  have hR := abs_qf_le hϵ0 (R := Q' - (1 + η) ^ 3 • P) (fun i j => hmat i j) v
  rw [qf_sub, qf_smul] at hR
  have hP : (n / (n + 1)) ^ 2 * ℓ * (v ⬝ᵥ v) ≤ qf P v := by
    have := cutMat_ge hn1 hQ hpsd hγ v
    have h2 := hQℓ v
    have h3 : 0 ≤ (n / (n + 1)) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hvv := dot_self_nonneg v
  have hE : |qf Q' v - (1 + η) ^ 3 * qf P v| ≤ η * qf P v := by
    refine hR.trans ?_
    have := mul_le_mul_of_nonneg_right hϵ1 hvv
    nlinarith
  have hP0 : 0 ≤ qf P v := le_trans (by positivity) hP
  rw [abs_le] at hE
  have k1 : (1 + η) ^ 2 ≤ (1 + η) ^ 3 - η := by nlinarith [sq_nonneg η]
  have k2 : (1 + η) ^ 3 + η ≤ (1 + η) ^ 4 := by nlinarith [sq_nonneg η, pow_pos hη 3]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right k1 hP0]
  · nlinarith [mul_le_mul_of_nonneg_right k2 hP0]

/-- **B7(a).** `Q' ⪰ ℓ⁺ I` with `ℓ⁺ = (n/(n+1))² ℓ`. -/
theorem rounded_formGe (hn : 2 ≤ Fintype.card ι) (hQ : Q.IsSymm) (hℓ : 0 < ℓ)
    (hQℓ : FormGe Q ℓ) (hη : 0 < η) (hg : g ≠ 0) (hϵ0 : 0 ≤ ϵ)
    (hϵ1 : (Fintype.card ι : ℝ) * ϵ ≤
      η * (((Fintype.card ι : ℝ) / (Fintype.card ι + 1)) ^ 2 * ℓ))
    (hmat : ∀ i j, |Q' i j - ((1 + η) ^ 3 • cutMat (Fintype.card ι) Q g) i j| ≤ ϵ) :
    FormGe Q' (((Fintype.card ι : ℝ) / (Fintype.card ι + 1)) ^ 2 * ℓ) := by
  intro v
  have hn1 : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := (rounded_form_bounds hn hQ hℓ hQℓ hη hg hϵ0 hϵ1 hmat v).1
  have h2 := cutMat_ge hn1 hQ (formGe_nonneg hℓ.le hQℓ) (qf_pos_of_formGe hℓ hQℓ hg) v
  have h3 := hQℓ v
  have h4 : (1 : ℝ) ≤ (1 + η) ^ 2 := by nlinarith
  have h5 : 0 ≤ qf (cutMat (Fintype.card ι) Q g) v :=
    le_trans (mul_nonneg (sq_nonneg _) (formGe_nonneg hℓ.le hQℓ v)) h2
  have h6 := mul_le_mul_of_nonneg_left h3
    (sq_nonneg ((Fintype.card ι : ℝ) / (Fintype.card ι + 1)))
  nlinarith

/-- **B7** for the magnitude analysis: `Q ⪯ uI` implies `Q' ⪯ (1+η)⁴ κ u I`. -/
theorem rounded_formLe (hn : 2 ≤ Fintype.card ι) (hQ : Q.IsSymm) (hℓ : 0 < ℓ)
    (hQℓ : FormGe Q ℓ) (hη : 0 < η) (hg : g ≠ 0) (hϵ0 : 0 ≤ ϵ)
    (hϵ1 : (Fintype.card ι : ℝ) * ϵ ≤
      η * (((Fintype.card ι : ℝ) / (Fintype.card ι + 1)) ^ 2 * ℓ))
    (hmat : ∀ i j, |Q' i j - ((1 + η) ^ 3 • cutMat (Fintype.card ι) Q g) i j| ≤ ϵ)
    {u : ℝ} (hu : FormLe Q u) : FormLe Q' ((1 + η) ^ 4 * kap (Fintype.card ι) * u) := by
  intro v
  have hn1 : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := (rounded_form_bounds hn hQ hℓ hQℓ hη hg hϵ0 hϵ1 hmat v).2
  have h2 := cutMat_le hn1 Q (qf_pos_of_formGe hℓ hQℓ hg) v
  have h3 := hu v
  have h4 : 0 ≤ (1 + η) ^ 4 := by positivity
  have h5 := kap_pos hn1
  calc qf Q' v ≤ (1 + η) ^ 4 * qf (cutMat (Fintype.card ι) Q g) v := h
    _ ≤ (1 + η) ^ 4 * (kap (Fintype.card ι) * (u * (v ⬝ᵥ v))) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 h5.le)) h4
    _ = _ := by ring

/-- **B7(c).** `det Q' ≤ (1+η)^{4n} κⁿ (n−1)/(n+1) det Q`. -/
theorem rounded_det [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) (hQ : Q.IsSymm) (hℓ : 0 < ℓ)
    (hQℓ : FormGe Q ℓ) (hη : 0 < η) (hg : g ≠ 0) (hϵ0 : 0 ≤ ϵ)
    (hϵ1 : (Fintype.card ι : ℝ) * ϵ ≤
      η * (((Fintype.card ι : ℝ) / (Fintype.card ι + 1)) ^ 2 * ℓ))
    (hQ' : Q'.IsSymm)
    (hmat : ∀ i j, |Q' i j - ((1 + η) ^ 3 • cutMat (Fintype.card ι) Q g) i j| ≤ ϵ) :
    Q'.det ≤ (1 + η) ^ (4 * Fintype.card ι) * (kap (Fintype.card ι) ^ Fintype.card ι *
      ((Fintype.card ι - 1) / (Fintype.card ι + 1))) * Q.det := by
  have hn1 : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hℓ' : 0 < ((Fintype.card ι : ℝ) / (Fintype.card ι + 1)) ^ 2 * ℓ := by positivity
  have hpd' := posDef_of_formGe hQ' hℓ' (rounded_formGe hn hQ hℓ hQℓ hη hg hϵ0 hϵ1 hmat)
  have hM : ((1 + η) ^ 4 • cutMat (Fintype.card ι) Q g).IsSymm := (cutMat_symm hQ g).smul _
  have h := det_le_det_of_form hpd' hM hQ' fun v => by
    rw [qf_smul]
    exact (rounded_form_bounds hn hQ hℓ hQℓ hη hg hϵ0 hϵ1 hmat v).2
  rw [det_smul, det_cutMat hn1 (qf_pos_of_formGe hℓ hQℓ hg)] at h
  calc Q'.det ≤ _ := h
    _ = _ := by rw [← pow_mul]; ring

/-- **B7(b).** The half-ellipsoid `E(Q, a) ∩ {g·(x − a) ≤ 0}` lies in the rounded ellipsoid
`E(Q', a')`. -/
theorem rounded_inEll [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) (hQ : Q.IsSymm) (hℓ : 0 < ℓ)
    (hQℓ : FormGe Q ℓ) (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hg : g ≠ 0)
    (hs : |s - Real.sqrt (qf Q g)| ≤ η / 4 * Real.sqrt (qf Q g)) (hϵ0 : 0 ≤ ϵ)
    (hϵ1 : (Fintype.card ι : ℝ) * ϵ ≤
      η * (((Fintype.card ι : ℝ) / (Fintype.card ι + 1)) ^ 2 * ℓ))
    (hϵ2 : (Fintype.card ι : ℝ) * ϵ ^ 2 ≤
      (η / 4) ^ 2 * (((Fintype.card ι : ℝ) / (Fintype.card ι + 1)) ^ 2 * ℓ))
    (hr : RoundOf ϵ Q' a' ((1 + η) ^ 3 • cutMat (Fintype.card ι) Q g)
      (cutCenter (Fintype.card ι) Q a g s))
    {x : ι → ℝ} (hx : InEll Q a x) (hcut : g ⬝ᵥ (x - a) ≤ 0) : InEll Q' a' x := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn'
  have hn1 : 1 < n := by rw [hn']; exact_mod_cast hn
  have hn2 : (2 : ℝ) ≤ n := by rw [hn']; exact_mod_cast hn
  set γ := qf Q g with hγdef
  have hγ : 0 < γ := qf_pos_of_formGe hℓ hQℓ hg
  set r := Real.sqrt γ with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hγ
  have hrr : r * r = γ := Real.mul_self_sqrt hγ.le
  have hpd : Q.PosDef := posDef_of_formGe hQ hℓ hQℓ
  have hpsd := formGe_nonneg hℓ.le hQℓ
  have hxp := inEll_cut hn1 hQ hpd hγ hx hcut
  set P := cutMat n Q g with hPdef
  set ap := cutCenter n Q a g r with hap
  set at' := cutCenter n Q a g s with hat
  have hslo : (1 - η / 4) * r ≤ s := by
    have := (abs_le.mp hs).1
    linarith
  have hs0 : 0 < s := lt_of_lt_of_le (by nlinarith) hslo
  set ℓp := (n / (n + 1)) ^ 2 * ℓ with hℓp
  have hge' := rounded_formGe hn hQ hℓ hQℓ hη hg hϵ0 hϵ1 hr.mat
  intro v
  set A := qf Q' v with hA
  have hbounds := rounded_form_bounds hn hQ hℓ hQℓ hη hg hϵ0 hϵ1 hr.mat v
  have hP0 : 0 ≤ qf P v := le_trans (mul_nonneg (sq_nonneg _) (hpsd v)) (cutMat_ge hn1 hQ hpsd hγ v)
  have hA0 : 0 ≤ A := le_trans (mul_nonneg (sq_nonneg _) hP0) hbounds.1
  have hη1 : 0 < 1 + η := by linarith
  -- the three terms
  have hdec : v ⬝ᵥ (x - a') = v ⬝ᵥ (x - ap) + v ⬝ᵥ (ap - at') + v ⬝ᵥ (at' - a') := by
    rw [← dotProduct_add, ← dotProduct_add]
    congr 1
    abel
  have hT1 : (v ⬝ᵥ (x - ap)) ^ 2 ≤ (1 / (1 + η)) ^ 2 * A := by
    have h1 := hxp v
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith [hbounds.1, mul_le_mul_of_nonneg_right h1 (sq_nonneg (1 + η))]
  have hT2 : (v ⬝ᵥ (ap - at')) ^ 2 ≤ (η / (6 * (1 + η))) ^ 2 * A := by
    have hdiff : ap - at' = (1 / ((n + 1) * s) - 1 / ((n + 1) * r)) • (Q *ᵥ g) := by
      rw [hap, hat]
      unfold cutCenter
      rw [sub_smul]
      abel
    rw [hdiff, dotProduct_smul, smul_eq_mul]
    have hcs : (v ⬝ᵥ (Q *ᵥ g)) ^ 2 ≤ qf Q v * γ := sq_dot_le hQ hpsd v g
    have hd : (1 / ((n + 1) * s) - 1 / ((n + 1) * r)) ^ 2 * γ ≤ η ^ 2 / (9 * (n + 1) ^ 2) := by
      rw [← hrr]
      exact scalar_d hn2 hr0 hη hη8 (by rw [abs_sub_comm]; exact hs)
    have hQv : qf Q v ≤ ((n + 1) / n) ^ 2 / (1 + η) ^ 2 * A :=
      scalar_qv hn1 hη (cutMat_ge hn1 hQ hpsd hγ v) hbounds.1
    calc ((1 / ((n + 1) * s) - 1 / ((n + 1) * r)) * (v ⬝ᵥ (Q *ᵥ g))) ^ 2
        = (1 / ((n + 1) * s) - 1 / ((n + 1) * r)) ^ 2 * (v ⬝ᵥ (Q *ᵥ g)) ^ 2 := by ring
      _ ≤ (1 / ((n + 1) * s) - 1 / ((n + 1) * r)) ^ 2 * (qf Q v * γ) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = ((1 / ((n + 1) * s) - 1 / ((n + 1) * r)) ^ 2 * γ) * qf Q v := by ring
      _ ≤ η ^ 2 / (9 * (n + 1) ^ 2) * (((n + 1) / n) ^ 2 / (1 + η) ^ 2 * A) :=
          mul_le_mul hd hQv (hpsd v) (by positivity)
      _ = (η / (3 * n * (1 + η))) ^ 2 * A := by
          field_simp
          ring
      _ ≤ (η / (6 * (1 + η))) ^ 2 * A := by
          refine mul_le_mul_of_nonneg_right ?_ hA0
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hT3 : (v ⬝ᵥ (at' - a')) ^ 2 ≤ (η / 4) ^ 2 * A := by
    have h1 := sq_dot_le_of_abs (w := at' - a') (fun i => by
      rw [Pi.sub_apply, abs_sub_comm]; exact hr.center i) v
    have h2 := hge' v
    have h3 := mul_le_mul_of_nonneg_right hϵ2 (dot_self_nonneg v)
    calc (v ⬝ᵥ (at' - a')) ^ 2 ≤ n * ϵ ^ 2 * (v ⬝ᵥ v) := h1
      _ ≤ (η / 4) ^ 2 * (ℓp * (v ⬝ᵥ v)) := by rw [← mul_assoc]; exact h3
      _ ≤ (η / 4) ^ 2 * A := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have h1 := abs_le_mul_sqrt (by positivity) hT1
  have h2 := abs_le_mul_sqrt (by positivity) hT2
  have h3 := abs_le_mul_sqrt (by positivity) hT3
  have hcoef : 1 / (1 + η) + η / (6 * (1 + η)) + η / 4 ≤ 1 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity)
      (by positivity), div_le_one (by positivity)]
    nlinarith
  have htot : |v ⬝ᵥ (x - a')| ≤ Real.sqrt A := by
    rw [hdec]
    calc |v ⬝ᵥ (x - ap) + v ⬝ᵥ (ap - at') + v ⬝ᵥ (at' - a')|
        ≤ |v ⬝ᵥ (x - ap)| + |v ⬝ᵥ (ap - at')| + |v ⬝ᵥ (at' - a')| := abs_add_three _ _ _
      _ ≤ (1 / (1 + η) + η / (6 * (1 + η)) + η / 4) * Real.sqrt A := by linarith
      _ ≤ 1 * Real.sqrt A := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg A)
      _ = Real.sqrt A := one_mul _
  calc (v ⬝ᵥ (x - a')) ^ 2 = |v ⬝ᵥ (x - a')| ^ 2 := (sq_abs _).symm
    _ ≤ Real.sqrt A ^ 2 := pow_le_pow_left₀ (abs_nonneg _) htot 2
    _ = A := Real.sq_sqrt hA0

/-- For the magnitude analysis: with `Q ⪯ uI` and `s ≥ √γ/2`, the unrounded center moves by at
most `√u` per coordinate. -/
theorem abs_cutCenter_sub_le [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) (hQ : Q.IsSymm)
    (hpsd : ∀ v, 0 ≤ qf Q v) {u : ℝ} (hu : FormLe Q u) (hγ : 0 < qf Q g)
    (hs : Real.sqrt (qf Q g) / 2 ≤ s) (i : ι) :
    |cutCenter (Fintype.card ι) Q a g s i - a i| ≤ Real.sqrt u := by
  have hn2 : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  set r := Real.sqrt (qf Q g)
  have hr0 : 0 < r := Real.sqrt_pos.mpr hγ
  have hrr : r * r = qf Q g := Real.mul_self_sqrt hγ.le
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have h1 := sq_mulVec_le hQ hpsd g i
  have h2 := diag_le hu i
  have hii : 0 ≤ Q i i := by have := hpsd (Pi.single i 1); rwa [qf_single] at this
  have hu0 : 0 ≤ u := hii.trans h2
  have h3 : (Q *ᵥ g) i ^ 2 ≤ u * (r * r) := by
    rw [hrr]; nlinarith [mul_le_mul_of_nonneg_right h2 hγ.le]
  have e : cutCenter (Fintype.card ι) Q a g s i - a i =
      -((Q *ᵥ g) i / ((Fintype.card ι + 1) * s)) := by
    unfold cutCenter
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [e, abs_neg]
  apply Real.abs_le_sqrt
  rw [div_pow, div_le_iff₀ (by positivity)]
  have h4 : r * r ≤ 4 * s ^ 2 := by nlinarith
  have h5 : (4 : ℝ) ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 := by nlinarith
  calc (Q *ᵥ g) i ^ 2 ≤ u * (r * r) := h3
    _ ≤ u * (4 * s ^ 2) := mul_le_mul_of_nonneg_left h4 hu0
    _ ≤ u * (((Fintype.card ι : ℝ) + 1) ^ 2 * s ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hu0
        nlinarith [sq_nonneg s]
    _ = _ := by ring

end Rounded

end STACS2027.Runtimes.ConvexQP
