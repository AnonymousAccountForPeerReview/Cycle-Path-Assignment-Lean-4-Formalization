module

public import Runtimes.ConvexQP.Numeric
import Mathlib.Tactic

/-!
# Lemma 16, Part B: the generic run of the rounded ellipsoid method (B9)

Dimension `n = |ι| ≥ 2`, `η = etaOf n`,
`ℓ_i = ellOf n i`, `θ = thetaOf n` and the upper bound `u_i = (n/4)·growOf n ^ i`.

A sequence of ellipsoids `(Q i, a i)` with `Q 0 = (n/4) I` and `|a 0| ≤ ½`, in which each
`(Q (i+1), a (i+1))` is an `ϵ`-rounding (`RoundOf`) of the rounded central cut
`((1+η)³ Q⁺, a − Qg/((n+1)s))` along an integral-size cut `g` (`g·g ≥ 1`) with a square root
`s` accurate to `δ`, satisfies the invariant `EllInv` (`ell_invariant`): after `i` cuts,
`Q i` is symmetric, `ℓ_i I ⪯ Q i ⪯ u_i I`, `det (Q i) ≤ (n/4)ⁿ θ^i`, the set `K` (valid for all
cuts) lies in `E(Q i, a i)`, and the center satisfies `|a i| ≤ ½ + i(√u_i + 1)`. The hypotheses
on the precision are those of E0: `nϵ ≤ ηℓ_N`, `nϵ² ≤ (η/4)²ℓ_N`, `δ² ≤ (η/4)²ℓ_N`.

If `K` also contains a ball of radius `r` with `(n/4)ⁿ θ^N < r^{2n}`, such a sequence of `N` cuts
cannot exist (`ell_contradiction`, by B4 and B5).
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The upper Loewner bound after `i` cuts: `u_i = (n/4)·((1+η)⁴κ)^i`. -/
noncomputable def upperOf (n i : ℕ) : ℝ := n / 4 * growOf n ^ i

/-- The invariant of the generic ellipsoid run after `i` cuts. -/
structure EllInv (K : Set (ι → ℝ)) (i : ℕ) (Q : Matrix ι ι ℝ) (a : ι → ℝ) : Prop where
  symm : Q.IsSymm
  ge : FormGe Q (ellOf (Fintype.card ι) i)
  le : FormLe Q (upperOf (Fintype.card ι) i)
  det : Q.det ≤ ((Fintype.card ι : ℝ) / 4) ^ Fintype.card ι * thetaOf (Fintype.card ι) ^ i
  cont : ∀ x ∈ K, InEll Q a x
  ctr : ∀ j, |a j| ≤ 1 / 2 + i * (Real.sqrt (upperOf (Fintype.card ι) i) + 1)

/-- One step of the generic run: an `ϵ`-rounded central cut along `g` with square root `s`. -/
def CutStep (ϵ δ : ℝ) (K : Set (ι → ℝ)) (Q : Matrix ι ι ℝ) (a : ι → ℝ) (Q' : Matrix ι ι ℝ)
    (a' : ι → ℝ) : Prop :=
  ∃ g s, 1 ≤ g ⬝ᵥ g ∧ |s - Real.sqrt (qf Q g)| ≤ δ ∧ (∀ x ∈ K, g ⬝ᵥ (x - a) ≤ 0) ∧
    RoundOf ϵ Q' a' ((1 + etaOf (Fintype.card ι)) ^ 3 • cutMat (Fintype.card ι) Q g)
      (cutCenter (Fintype.card ι) Q a g s)

theorem one_le_growOf {n : ℕ} (hn : 2 ≤ n) : 1 ≤ growOf n := by
  unfold growOf
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hη := etaOf_pos (n := n) (by omega)
  have hk : 1 ≤ kap n := by
    unfold kap
    rw [le_div_iff₀ (by nlinarith)]
    linarith
  have : 1 ≤ (1 + etaOf n) ^ 4 := one_le_pow₀ (by linarith)
  nlinarith

theorem upperOf_mono {n : ℕ} (hn : 2 ≤ n) (i : ℕ) : upperOf n i ≤ upperOf n (i + 1) := by
  unfold upperOf
  have h0 : (0 : ℝ) ≤ n / 4 := by positivity
  rw [pow_succ]
  have := one_le_growOf hn
  have : 0 ≤ growOf n ^ i := pow_nonneg (growOf_pos hn).le i
  nlinarith [mul_le_mul_of_nonneg_left (one_le_growOf hn) this]

/-- The invariant at the start: `Q 0 = (n/4) I`, `|a 0| ≤ ½`, `K ⊆ E(Q 0, a 0)`. -/
theorem ellInv_zero {K : Set (ι → ℝ)} {a : ι → ℝ} (ha : ∀ j, |a j| ≤ 1 / 2)
    (hK : ∀ x ∈ K, InEll (((Fintype.card ι : ℝ) / 4) • (1 : Matrix ι ι ℝ)) a x) :
    EllInv K 0 (((Fintype.card ι : ℝ) / 4) • (1 : Matrix ι ι ℝ)) a where
  symm := isSymm_one.smul _
  ge v := by rw [ellOf_zero, qf_smul, qf_one]
  le v := by rw [upperOf, qf_smul, qf_one, pow_zero, mul_one]
  det := by rw [det_smul, det_one, pow_zero, mul_one]
  cont := hK
  ctr j := by simpa using ha j

/-- **B9, induction step.** -/
theorem ellInv_succ (hn : 2 ≤ Fintype.card ι) {K : Set (ι → ℝ)} {N i : ℕ} (hi : i < N)
    {ϵ δ : ℝ} (hϵ0 : 0 ≤ ϵ) (hϵ1 : ϵ ≤ 1)
    (hϵη : (Fintype.card ι : ℝ) * ϵ ≤ etaOf (Fintype.card ι) * ellOf (Fintype.card ι) N)
    (hϵ2 : (Fintype.card ι : ℝ) * ϵ ^ 2 ≤
      (etaOf (Fintype.card ι) / 4) ^ 2 * ellOf (Fintype.card ι) N)
    (hδ0 : 0 ≤ δ) (hδ : δ ^ 2 ≤ (etaOf (Fintype.card ι) / 4) ^ 2 * ellOf (Fintype.card ι) N)
    {Q Q' : Matrix ι ι ℝ} {a a' : ι → ℝ} (hinv : EllInv K i Q a)
    (hstep : CutStep ϵ δ K Q a Q' a') : EllInv K (i + 1) Q' a' := by
  obtain ⟨g, s, hgg, hs, hcut, hr⟩ := hstep
  set n := Fintype.card ι with hndef
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set η := etaOf n with hηdef
  have hη := etaOf_pos hn1
  have hη8 := etaOf_le hn1
  have hg : g ≠ 0 := by
    intro h; rw [h, dotProduct_zero] at hgg; norm_num at hgg
  have hℓi := ellOf_pos hn1 i
  have hℓN := ellOf_pos hn1 N
  have hℓiN : ellOf n N ≤ ellOf n i := ellOf_anti hn1 hi.le
  have hℓsN : ellOf n N ≤ ellOf n (i + 1) := ellOf_anti hn1 hi
  have hsucc := ellOf_succ n i
  -- the square root is accurate
  have hγ : ellOf n N ≤ qf Q g := by
    have := hinv.ge g
    nlinarith
  have hγ0 : 0 < qf Q g := lt_of_lt_of_le hℓN hγ
  have hs' : |s - Real.sqrt (qf Q g)| ≤ η / 4 * Real.sqrt (qf Q g) := by
    refine hs.trans ?_
    have h1 : δ ^ 2 ≤ (η / 4) ^ 2 * qf Q g :=
      hδ.trans (mul_le_mul_of_nonneg_left hγ (sq_nonneg _))
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hδ0, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at this
  -- the precision at level `i + 1`
  have hϵ1' : (n : ℝ) * ϵ ≤ η * (((n : ℝ) / (n + 1)) ^ 2 * ellOf n i) := by
    rw [← hsucc]
    exact hϵη.trans (mul_le_mul_of_nonneg_left hℓsN hη.le)
  have hϵ2' : (n : ℝ) * ϵ ^ 2 ≤ (η / 4) ^ 2 * (((n : ℝ) / (n + 1)) ^ 2 * ellOf n i) := by
    rw [← hsucc]
    exact hϵ2.trans (mul_le_mul_of_nonneg_left hℓsN (sq_nonneg _))
  refine ⟨hr.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsucc]
    exact rounded_formGe hn hinv.symm hℓi hinv.ge hη hg hϵ0 hϵ1' hr.mat
  · have h := rounded_formLe hn hinv.symm hℓi hinv.ge hη hg hϵ0 hϵ1' hr.mat hinv.le
    intro v
    refine (h v).trans (le_of_eq ?_)
    unfold upperOf growOf
    rw [pow_succ]
    ring
  · have h := rounded_det hn hinv.symm hℓi hinv.ge hη hg hϵ0 hϵ1' hr.symm hr.mat
    have hθ := thetaOf_pos hn
    calc Q'.det ≤ thetaOf n * Q.det := by unfold thetaOf; exact h
      _ ≤ thetaOf n * (((n : ℝ) / 4) ^ n * thetaOf n ^ i) :=
          mul_le_mul_of_nonneg_left hinv.det hθ.le
      _ = _ := by rw [pow_succ]; ring
  · intro x hx
    exact rounded_inEll hn hinv.symm hℓi hinv.ge hη hη8 hg hs' hϵ0 hϵ1' hϵ2' hr
      (hinv.cont x hx) (hcut x hx)
  · intro j
    have hpsd := formGe_nonneg hℓi.le hinv.ge
    have hsr : Real.sqrt (qf Q g) / 2 ≤ s := by
      have := (abs_le.mp hs').1
      have : 0 ≤ Real.sqrt (qf Q g) := Real.sqrt_nonneg _
      nlinarith
    have h1 := abs_cutCenter_sub_le hn hinv.symm hpsd hinv.le hγ0 hsr (a := a) j
    have h2 := hr.center j
    have h3 := hinv.ctr j
    have hmono : Real.sqrt (upperOf n i) ≤ Real.sqrt (upperOf n (i + 1)) :=
      Real.sqrt_le_sqrt (upperOf_mono hn i)
    have htri : |a' j| ≤ |a j| + |cutCenter n Q a g s j - a j| +
        |a' j - cutCenter n Q a g s j| := by
      calc |a' j| = |a j + (cutCenter n Q a g s j - a j) + (a' j - cutCenter n Q a g s j)| := by
            ring_nf
        _ ≤ _ := abs_add_three _ _ _
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hmono hi0]

/-- **B9.** The invariant holds along every generic run of `N` cuts. -/
theorem ell_invariant (hn : 2 ≤ Fintype.card ι) (K : Set (ι → ℝ)) (N : ℕ)
    (Q : ℕ → Matrix ι ι ℝ) (a : ℕ → ι → ℝ) {ϵ δ : ℝ} (hϵ0 : 0 ≤ ϵ) (hϵ1 : ϵ ≤ 1)
    (hϵη : (Fintype.card ι : ℝ) * ϵ ≤ etaOf (Fintype.card ι) * ellOf (Fintype.card ι) N)
    (hϵ2 : (Fintype.card ι : ℝ) * ϵ ^ 2 ≤
      (etaOf (Fintype.card ι) / 4) ^ 2 * ellOf (Fintype.card ι) N)
    (hδ0 : 0 ≤ δ) (hδ : δ ^ 2 ≤ (etaOf (Fintype.card ι) / 4) ^ 2 * ellOf (Fintype.card ι) N)
    (h0 : Q 0 = ((Fintype.card ι : ℝ) / 4) • (1 : Matrix ι ι ℝ)) (ha0 : ∀ j, |a 0 j| ≤ 1 / 2)
    (hK0 : ∀ x ∈ K, InEll (Q 0) (a 0) x)
    (hstep : ∀ i < N, EllInv K i (Q i) (a i) → CutStep ϵ δ K (Q i) (a i) (Q (i + 1)) (a (i + 1))) :
    ∀ i ≤ N, EllInv K i (Q i) (a i) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [h0] at hK0 ⊢
    exact ellInv_zero ha0 hK0
  | succ i ih =>
    intro hi
    have hinv := ih (by omega)
    exact ellInv_succ hn (by omega : i < N) hϵ0 hϵ1 hϵη hϵ2 hδ0 hδ hinv (hstep i (by omega) hinv)

/-- **B9, conclusion.** If `K` contains a ball of radius `r > 0` and `(n/4)ⁿ θ^N < r^{2n}`, the
invariant cannot hold after `N` cuts. -/
theorem ell_contradiction {K : Set (ι → ℝ)} {N : ℕ} {Q : Matrix ι ι ℝ} {a : ι → ℝ}
    (hinv : EllInv K N Q a) {r : ℝ} (hr : 0 < r) {z : ι → ℝ}
    (hball : ∀ y, (y - z) ⬝ᵥ (y - z) ≤ r ^ 2 → y ∈ K)
    (hfin : ((Fintype.card ι : ℝ) / 4) ^ Fintype.card ι * thetaOf (Fintype.card ι) ^ N <
      r ^ (2 * Fintype.card ι)) : False := by
  have hge : FormGe Q (r ^ 2) := formGe_of_ball (z := z) (a := a) fun y hy =>
    hinv.cont y (hball y hy)
  have h1 := pow_le_det hinv.symm (by positivity) hge
  rw [← pow_mul] at h1
  linarith [hinv.det]

end STACS2027.Runtimes.ConvexQP
