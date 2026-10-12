module

public import Runtimes.ConvexQP.Inst
import Mathlib.Tactic

/-!
# Lemma 16, Part A: the quadratic program

The facts about `F(x) = ½ ∑_e λ(x)_e²` on the product of simplices `𝒳` used by the exact
algorithm.

* **A1** (`F_add`, exact expansion): `F(x + w) = F(x) + ⟨L(x), w⟩ + F(w)`, hence the gradient
  inequality `F_ge`, the quadratic step formula `F_add_smul` and convexity `F_convex`.
* **A2** (on `𝒳` of a valid instance): `∑_e λ_e = (k−2)t` (`sum_lam`), `Φ = F − (k−2)t/2`
  (`Phi_eq_F`), `0 ≤ λ_e ≤ t`, `0 ≤ F ≤ Φ₀` (`F_le_Phi0`), and the curvature bound
  `2F(x' − x) ≤ C₀` (`two_F_sub_le`).
* **A3** (`F_le_of_kkt`, `Phi_le_of_kkt`): a feasible point with multipliers `π` satisfying
  `L(x) ≥ π` and complementarity `x (L(x) − π) = 0` minimizes `F` and `Φ` over `𝒳`.
* **A4** (Frank–Wolfe gap): `⟨L(x), x − v(x)⟩ = gap(x) ≥ 0`, `F(x) − F(x') ≤ gap(x)`
  (`F_sub_le_gap`; this is the stopping criterion of Phase E), the Frank–Wolfe step
  (`fw_inX`, `F_fw_step`) and its decrease when `gap(x) > g₀` (`F_fw_step_decrease`).
* **A5** (reduced coordinates for the ellipsoid): `xiq q y` completes `y ∈ ℝ^{t×(k−1)}` with
  last coordinate `q − ∑_j y_{c,j}`; `xi = xiq 1` maps `Y` onto `𝒳` (`xi_inX`, `red_inY`,
  `xi_red`, `red_xi`); `f = F ∘ xi` satisfies the gradient inequality with
  `gradRed x c j = L(x)_{c,j} − L(x)_{c,k}` (`f_ge`) and is convex (`f_convex`); a ball lies in
  `Y` (`ball_subset_Y`) and `Y ⊆ [0,1]^n` (`InY_le_one`).
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Finset

namespace Inst

variable (I : Inst)

/-! ### A1: exact expansion -/

theorem lam_add' (x w : Fin I.t → Fin I.k → ℝ) (e : Fin I.m) :
    I.lam (x + w) e = I.lam x e + I.lam w e :=
  I.lam_add x w e

theorem lam_sub' (x w : Fin I.t → Fin I.k → ℝ) (e : Fin I.m) :
    I.lam (x - w) e = I.lam x e - I.lam w e :=
  I.lam_sub x w e

theorem lam_smul' (a : ℝ) (x : Fin I.t → Fin I.k → ℝ) (e : Fin I.m) :
    I.lam (a • x) e = a * I.lam x e :=
  I.lam_smul a x e

theorem L_sub' (x w : Fin I.t → Fin I.k → ℝ) (c : Fin I.t) (j : Fin I.k) :
    I.L (x - w) c j = I.L x c j - I.L w c j :=
  I.L_sub x w c j

/-- `⟨L(x), w⟩ = ∑_e λ(x)_e λ(w)_e` (exchange of finite sums). -/
theorem inner_L_eq (x w : Fin I.t → Fin I.k → ℝ) :
    I.inner (I.L x) w = ∑ e, I.lam x e * I.lam w e := by
  unfold inner L
  calc ∑ c, ∑ j, (∑ e, (I.cnt c j e : ℝ) * I.lam x e) * w c j
      = ∑ c, ∑ j, ∑ e, I.lam x e * ((I.cnt c j e : ℝ) * w c j) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ = ∑ c, ∑ e, ∑ j, I.lam x e * ((I.cnt c j e : ℝ) * w c j) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ e, ∑ c, ∑ j, I.lam x e * ((I.cnt c j e : ℝ) * w c j) := Finset.sum_comm
    _ = ∑ e, I.lam x e * I.lam w e := by
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [lam, Finset.mul_sum]

theorem inner_add (u v w : Fin I.t → Fin I.k → ℝ) :
    I.inner u (v + w) = I.inner u v + I.inner u w := by
  simp only [inner, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem inner_sub (u v w : Fin I.t → Fin I.k → ℝ) :
    I.inner u (v - w) = I.inner u v - I.inner u w := by
  simp only [inner, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem inner_smul (u w : Fin I.t → Fin I.k → ℝ) (a : ℝ) :
    I.inner u (a • w) = a * I.inner u w := by
  simp only [inner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem F_nonneg' (x : Fin I.t → Fin I.k → ℝ) : 0 ≤ I.F x := by
  unfold F
  have : 0 ≤ ∑ e, I.lam x e ^ 2 := Finset.sum_nonneg fun e _ => sq_nonneg _
  linarith

/-- **A1.** `F(x + w) = F(x) + ⟨L(x), w⟩ + F(w)`. -/
theorem F_add (x w : Fin I.t → Fin I.k → ℝ) :
    I.F (x + w) = I.F x + I.inner (I.L x) w + I.F w := by
  have h : ∀ e, I.lam (x + w) e ^ 2 =
      I.lam x e ^ 2 + 2 * (I.lam x e * I.lam w e) + I.lam w e ^ 2 := fun e => by
    rw [lam_add']; ring
  simp only [F, h, Finset.sum_add_distrib, ← Finset.mul_sum, inner_L_eq]
  ring

/-- **A1(a).** The gradient inequality `F(x') ≥ F(x) + ⟨L(x), x' − x⟩`. -/
theorem F_ge (x x' : Fin I.t → Fin I.k → ℝ) :
    I.F x + I.inner (I.L x) (x' - x) ≤ I.F x' := by
  have h := I.F_add x (x' - x)
  rw [add_sub_cancel] at h
  rw [h]
  linarith [I.F_nonneg' (x' - x)]

theorem F_smul (a : ℝ) (w : Fin I.t → Fin I.k → ℝ) : I.F (a • w) = a ^ 2 * I.F w := by
  simp only [F, lam_smul', mul_pow, ← Finset.mul_sum]
  ring

/-- **A1(b).** `F(x + γw) = F(x) + γ⟨L(x), w⟩ + γ²F(w)`. -/
theorem F_add_smul (x w : Fin I.t → Fin I.k → ℝ) (γ : ℝ) :
    I.F (x + γ • w) = I.F x + γ * I.inner (I.L x) w + γ ^ 2 * I.F w := by
  rw [F_add, F_smul, inner_smul]

/-- **A1(c).** Convexity of `F`. -/
theorem F_convex (x x' : Fin I.t → Fin I.k → ℝ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    I.F ((1 - ρ) • x + ρ • x') ≤ (1 - ρ) * I.F x + ρ * I.F x' := by
  have hx : (1 - ρ) • x + ρ • x' = x + ρ • (x' - x) := by
    funext c j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have h2 := I.F_add x (x' - x)
  rw [add_sub_cancel] at h2
  rw [hx, F_add_smul, h2]
  have hF := I.F_nonneg' (x' - x)
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

/-! ### A2: the polytope -/

variable {I}

/-- The weight of the options of cycle `c` through `e`: `p_c(x)_e = ∑_j cnt c j e · x_{c,j}`. -/
theorem lam_eq_sum_p (x : Fin I.t → Fin I.k → ℝ) (e : Fin I.m) :
    I.lam x e = ∑ c, ∑ j, (I.cnt c j e : ℝ) * x c j := rfl

theorem p_nonneg {x : Fin I.t → Fin I.k → ℝ} (hx : ∀ c j, 0 ≤ x c j) (c : Fin I.t)
    (e : Fin I.m) : 0 ≤ ∑ j, (I.cnt c j e : ℝ) * x c j :=
  Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hx c j)

theorem p_le_one (hI : I.Valid) {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) (c : Fin I.t)
    (e : Fin I.m) : ∑ j, (I.cnt c j e : ℝ) * x c j ≤ 1 := by
  rw [← hx.2 c]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : (I.cnt c j e : ℝ) ≤ 1 := by exact_mod_cast cnt_le_one hI c j e
  nlinarith [hx.1 c j]

theorem lam_nonneg {x : Fin I.t → Fin I.k → ℝ} (hx : ∀ c j, 0 ≤ x c j) (e : Fin I.m) :
    0 ≤ I.lam x e :=
  Finset.sum_nonneg fun c _ => p_nonneg hx c e

/-- **A2(b).** `λ_e ≤ t` on `𝒳`. -/
theorem lam_le_t (hI : I.Valid) {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) (e : Fin I.m) :
    I.lam x e ≤ I.t := by
  calc I.lam x e ≤ ∑ _c : Fin I.t, (1 : ℝ) := Finset.sum_le_sum fun c _ => p_le_one hI hx c e
    _ = I.t := by simp

/-- **A2(a).** `∑_e λ_e = (k − 2) t` on `𝒳`. -/
theorem sum_lam (hI : I.Valid) {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) :
    ∑ e, I.lam x e = ((I.k - 2 : ℕ) : ℝ) * I.t := by
  unfold lam
  rw [Finset.sum_comm]
  have : ∀ c, ∑ e, ∑ j, (I.cnt c j e : ℝ) * x c j = (I.k - 2 : ℕ) := by
    intro c
    rw [Finset.sum_comm]
    have h2 : ∀ j, ∑ e, (I.cnt c j e : ℝ) * x c j = ((I.k - 2 : ℕ) : ℝ) * x c j := by
      intro j
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast sum_cnt_valid hI c j
    simp only [h2, ← Finset.mul_sum, hx.2 c, mul_one]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **A2(a).** `Φ = F − (k − 2) t / 2` on `𝒳`. -/
theorem Phi_eq_F (hI : I.Valid) {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) :
    I.Phi x = I.F x - ((I.k - 2 : ℕ) : ℝ) * I.t / 2 := by
  unfold Phi F
  rw [← sum_lam hI hx]
  simp only [sub_div, Finset.sum_sub_distrib, Finset.sum_div]

theorem F_nonneg (x : Fin I.t → Fin I.k → ℝ) : 0 ≤ I.F x := I.F_nonneg' x

/-- **A2(b).** `F ≤ Φ₀ = ½ (k − 2)² t²` on `𝒳`. -/
theorem F_le_Phi0 (hI : I.Valid) {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) :
    I.F x ≤ Phi0 I.t I.k := by
  unfold F Phi0
  have hs := sum_lam hI hx
  have hle : ∑ e, I.lam x e ^ 2 ≤ (∑ e, I.lam x e) * ∑ e, I.lam x e := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun e _ => lam_nonneg hx.1 e) (Finset.mem_univ e))
      (lam_nonneg hx.1 e)
  rw [hs] at hle
  have : ((I.k - 2 : ℕ) : ℝ) * I.t * (((I.k - 2 : ℕ) : ℝ) * I.t) =
      ((I.k - 2 : ℕ) : ℝ) ^ 2 * (I.t : ℝ) ^ 2 := by ring
  linarith

/-- **A2(c).** The curvature bound `2 F(x' − x) = ‖λ(x') − λ(x)‖² ≤ C₀ = 2 (k − 2) t²`. -/
theorem two_F_sub_le (hI : I.Valid) {x x' : Fin I.t → Fin I.k → ℝ} (hx : I.InX x)
    (hx' : I.InX x') : 2 * I.F (x' - x) ≤ curv I.t I.k := by
  set μ : Fin I.m → ℝ := fun e => I.lam (x' - x) e with hμ
  have hμe : ∀ e, μ e = ∑ c, ∑ j, (I.cnt c j e : ℝ) * (x' c j - x c j) := fun e => rfl
  -- `|μ_e| ≤ t`
  have hμt : ∀ e, |μ e| ≤ I.t := by
    intro e
    rw [hμe]
    calc |∑ c, ∑ j, (I.cnt c j e : ℝ) * (x' c j - x c j)|
        ≤ ∑ c, |∑ j, (I.cnt c j e : ℝ) * (x' c j - x c j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _c : Fin I.t, (1 : ℝ) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 := p_le_one hI hx' c e
        have h2 := p_le_one hI hx c e
        have h3 := p_nonneg hx'.1 c e
        have h4 := p_nonneg hx.1 c e
        have hsplit : ∑ j, (I.cnt c j e : ℝ) * (x' c j - x c j) =
            ∑ j, (I.cnt c j e : ℝ) * x' c j - ∑ j, (I.cnt c j e : ℝ) * x c j := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hsplit, abs_le]
        constructor <;> linarith
      _ = I.t := by simp
  -- `∑_e |μ_e| ≤ 2 (k − 2) t`
  have hμsum : ∑ e, |μ e| ≤ 2 * ((I.k - 2 : ℕ) : ℝ) * I.t := by
    calc ∑ e, |μ e| ≤ ∑ e, ∑ c, ∑ j, (I.cnt c j e : ℝ) * |x' c j - x c j| := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [hμe]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      _ = ∑ c, ∑ j, ((I.k - 2 : ℕ) : ℝ) * |x' c j - x c j| := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast sum_cnt_valid hI c j
      _ ≤ ∑ c, ∑ j, ((I.k - 2 : ℕ) : ℝ) * (x' c j + x c j) := by
          refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun j _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rw [abs_le]
          constructor <;> linarith [hx.1 c j, hx'.1 c j]
      _ = 2 * ((I.k - 2 : ℕ) : ℝ) * I.t := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib, hx.2, hx'.2, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hF : 2 * I.F (x' - x) = ∑ e, μ e ^ 2 := by
    unfold F; ring
  rw [hF]
  calc ∑ e, μ e ^ 2 ≤ ∑ e, (I.t : ℝ) * |μ e| := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [← sq_abs, sq]
        exact mul_le_mul_of_nonneg_right (hμt e) (abs_nonneg _)
    _ = I.t * ∑ e, |μ e| := by rw [Finset.mul_sum]
    _ ≤ I.t * (2 * ((I.k - 2 : ℕ) : ℝ) * I.t) :=
        mul_le_mul_of_nonneg_left hμsum (Nat.cast_nonneg _)
    _ = curv I.t I.k := by
        unfold curv
        push_cast
        ring

/-! ### A3: KKT sufficiency -/

/-- **A3.** A feasible point with multipliers `π`, `L(x) ≥ π` and complementarity
`x_{c,j} (L(x)_{c,j} − π_c) = 0`, minimizes `F` over `𝒳`. -/
theorem F_le_of_kkt {x : Fin I.t → Fin I.k → ℝ} {π : Fin I.t → ℝ} (hx : I.InX x)
    (hge : ∀ c j, π c ≤ I.L x c j) (hcomp : ∀ c j, x c j * (I.L x c j - π c) = 0)
    {x' : Fin I.t → Fin I.k → ℝ} (hx' : I.InX x') : I.F x ≤ I.F x' := by
  have h := I.F_ge x x'
  have hin : I.inner (I.L x) (x' - x) = ∑ c, ∑ j, (I.L x c j - π c) * x' c j := by
    have e1 : I.inner (I.L x) (x' - x) =
        ∑ c, ∑ j, ((I.L x c j - π c) * x' c j - x c j * (I.L x c j - π c)
          + π c * (x' c j - x c j)) := by
      unfold inner
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.sub_apply]
      ring
    rw [e1]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hx.2 c, hx'.2 c]
    simp [hcomp]
  have hnn : 0 ≤ ∑ c, ∑ j, (I.L x c j - π c) * x' c j :=
    Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hge c j)) (hx'.1 c j)
  linarith

/-- **A3** for the manuscript's objective `Φ`. -/
theorem Phi_le_of_kkt (hI : I.Valid) {x : Fin I.t → Fin I.k → ℝ} {π : Fin I.t → ℝ}
    (hx : I.InX x) (hge : ∀ c j, π c ≤ I.L x c j)
    (hcomp : ∀ c j, x c j * (I.L x c j - π c) = 0)
    {x' : Fin I.t → Fin I.k → ℝ} (hx' : I.InX x') : I.Phi x ≤ I.Phi x' := by
  rw [Phi_eq_F hI hx, Phi_eq_F hI hx']
  linarith [F_le_of_kkt hx hge hcomp hx']

/-! ### A4: the Frank–Wolfe gap -/

theorem k_pos_of_inX {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) (c : Fin I.t) : 0 < I.k := by
  rcases Nat.eq_zero_or_pos I.k with h | h
  · have h1 := hx.2 c
    have : ∑ j : Fin I.k, x c j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact absurd j.2 (by omega)
    rw [this] at h1
    exact absurd h1 zero_ne_one
  · exact h

/-- The selected option of `v(x)` in cycle `c`: the least `j` with `L(x)_{c,j} = π(x)_c`. -/
theorem vtx_eq (x : Fin I.t → Fin I.k → ℝ) (c : Fin I.t) (hk : 0 < I.k) :
    ∃ j₀, I.L x c j₀ = I.pi x c ∧ ∀ j, I.vtx x c j = if j = j₀ then 1 else 0 := by
  classical
  set S := Finset.univ.filter fun j => I.L x c j = I.pi x c with hS
  have hne : S.Nonempty := by
    obtain ⟨j, hj⟩ := I.exists_L_eq_pi x c hk
    exact ⟨j, by simp [S, hj]⟩
  refine ⟨S.min' hne, (Finset.mem_filter.mp (S.min'_mem hne)).2, fun j => ?_⟩
  unfold vtx
  by_cases hj : j = S.min' hne
  · subst hj
    have hcond : I.L x c (S.min' hne) = I.pi x c ∧
        ∀ j' : Fin I.k, j' < S.min' hne → I.L x c j' ≠ I.pi x c :=
      ⟨(Finset.mem_filter.mp (S.min'_mem hne)).2, fun j' hj' hL =>
        absurd (S.min'_le j' (by simp [S, hL])) (not_le.mpr hj')⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · have hcond : ¬ (I.L x c j = I.pi x c ∧ ∀ j' : Fin I.k, j' < j → I.L x c j' ≠ I.pi x c) := by
      intro ⟨hL, hmin⟩
      have hjS : j ∈ S := by simp [S, hL]
      rcases lt_or_eq_of_le (S.min'_le j hjS) with hlt | heq
      · exact hmin _ hlt (Finset.mem_filter.mp (S.min'_mem hne)).2
      · exact hj heq.symm
    simp only [hcond, hj, ↓reduceIte]

/-- `v(x) ∈ 𝒳`. -/
theorem vtx_inX {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) : I.InX (I.vtx x) := by
  refine ⟨fun c j => ?_, fun c => ?_⟩
  · unfold vtx; split_ifs <;> norm_num
  · obtain ⟨j₀, _, h⟩ := I.vtx_eq x c (k_pos_of_inX hx c)
    simp [h]

theorem sum_vtx_mul_L {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) (c : Fin I.t) :
    ∑ j, I.L x c j * I.vtx x c j = I.pi x c := by
  obtain ⟨j₀, hj₀, h⟩ := I.vtx_eq x c (k_pos_of_inX hx c)
  simp [h, hj₀]

theorem inner_L_vtx {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) :
    I.inner (I.L x) (I.vtx x) = ∑ c, I.pi x c := by
  unfold inner
  exact Finset.sum_congr rfl fun c _ => sum_vtx_mul_L hx c

/-- `⟨L(x), x'⟩ ≥ ∑_c π_c` for `x' ∈ 𝒳`. -/
theorem inner_L_ge {x x' : Fin I.t → Fin I.k → ℝ} (hx' : I.InX x') :
    ∑ c, I.pi x c ≤ I.inner (I.L x) x' := by
  unfold inner
  refine Finset.sum_le_sum fun c _ => ?_
  calc I.pi x c = ∑ j, I.pi x c * x' c j := by rw [← Finset.mul_sum, hx'.2 c, mul_one]
    _ ≤ ∑ j, I.L x c j * x' c j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (I.pi_le x c j) (hx'.1 c j)

theorem gap_eq {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) :
    I.gap x = I.inner (I.L x) x - ∑ c, I.pi x c := by
  unfold gap inner
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ∑ j, x c j * (I.L x c j - I.pi x c) =
      ∑ j, I.L x c j * x c j - I.pi x c * ∑ j, x c j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hx.2 c, mul_one]

/-- **A4(a).** `⟨L(x), x − v(x)⟩ = gap(x)`. -/
theorem inner_L_sub_vtx {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) :
    I.inner (I.L x) (x - I.vtx x) = I.gap x := by
  rw [inner_sub, inner_L_vtx hx, gap_eq hx]

/-- **A4(a).** `gap(x) ≥ 0` for `x ≥ 0`. -/
theorem gap_nonneg {x : Fin I.t → Fin I.k → ℝ} (hx : ∀ c j, 0 ≤ x c j) : 0 ≤ I.gap x :=
  Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (hx c j) (sub_nonneg.mpr (I.pi_le x c j))

/-- **A4(b).** `F(x) − F(x') ≤ gap(x)` for `x, x' ∈ 𝒳`: a point with gap `≤ g` is `g`-optimal. -/
theorem F_sub_le_gap {x x' : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) (hx' : I.InX x') :
    I.F x - I.F x' ≤ I.gap x := by
  have h1 := I.F_ge x x'
  rw [inner_sub] at h1
  have h2 := inner_L_ge (x := x) hx'
  rw [gap_eq hx]
  linarith

/-- **A4(c).** The Frank–Wolfe step stays in `𝒳`. -/
theorem fw_inX {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    I.InX (x + γ • (I.vtx x - x)) := by
  have hv := vtx_inX hx
  refine ⟨fun c j => ?_, fun c => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    nlinarith [hx.1 c j, hv.1 c j]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, hx.2 c, hv.2 c]
    ring

/-- **A4(c).** `F(x + γ (v(x) − x)) ≤ F(x) − γ gap(x) + γ² C₀ / 2`. -/
theorem F_fw_step (hI : I.Valid) {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) (γ : ℝ) :
    I.F (x + γ • (I.vtx x - x)) ≤ I.F x - γ * I.gap x + γ ^ 2 * (curv I.t I.k : ℝ) / 2 := by
  rw [F_add_smul]
  have h1 : I.inner (I.L x) (I.vtx x - x) = -I.gap x := by
    rw [← inner_L_sub_vtx hx, inner_sub, inner_sub]; ring
  have h2 := two_F_sub_le hI hx (vtx_inX hx)
  rw [h1]
  nlinarith [sq_nonneg γ]

/-- **A4(d).** If `0 < g₀ ≤ C₀` and `gap(x) > g₀`, the Frank–Wolfe step of length `g₀/C₀`
decreases `F` by more than `δ₀ = g₀² / (2 C₀)`. -/
theorem F_fw_step_decrease (hI : I.Valid) {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) {g₀ : ℝ}
    (hg0 : 0 < g₀) (hg0C : g₀ ≤ curv I.t I.k) (hgap : g₀ < I.gap x) :
    I.InX (x + (g₀ / curv I.t I.k) • (I.vtx x - x)) ∧
      I.F (x + (g₀ / curv I.t I.k) • (I.vtx x - x)) < I.F x - g₀ ^ 2 / (2 * curv I.t I.k) := by
  have hC : (0 : ℝ) < curv I.t I.k := lt_of_lt_of_le hg0 hg0C
  have hγ0 : 0 ≤ g₀ / curv I.t I.k := div_nonneg hg0.le hC.le
  have hγ1 : g₀ / curv I.t I.k ≤ 1 := (div_le_one hC).mpr hg0C
  refine ⟨fw_inX hx hγ0 hγ1, ?_⟩
  have h := F_fw_step hI hx (g₀ / curv I.t I.k)
  have hγpos : 0 < g₀ / curv I.t I.k := div_pos hg0 hC
  have key : g₀ / curv I.t I.k * g₀ < g₀ / curv I.t I.k * I.gap x :=
    mul_lt_mul_of_pos_left hgap hγpos
  have e1 : g₀ / curv I.t I.k * g₀ - (g₀ / curv I.t I.k) ^ 2 * (curv I.t I.k : ℝ) / 2 =
      g₀ ^ 2 / (2 * curv I.t I.k) := by
    field_simp
    ring
  linarith

/-! ### A5: reduced coordinates -/

section Reduced

variable (I)
variable {R : Type*} [CommRing R]

/-- Completion of reduced coordinates `y ∈ R^{t×(k−1)}`: the last option of cycle `c` gets
`q − ∑_j y_{c,j}` (with `q = 1` for points, `q = 2^p` for the fixed-point data of Phase E). -/
def xiq (q : R) (y : Fin I.t → Fin (I.k - 1) → R) : Fin I.t → Fin I.k → R :=
  fun c j => if h : (j : ℕ) < I.k - 1 then y c ⟨j, h⟩ else q - ∑ j', y c j'

/-- Dropping the last option. -/
def red (x : Fin I.t → Fin I.k → R) : Fin I.t → Fin (I.k - 1) → R :=
  fun c j => x c (Fin.castLE (Nat.sub_le _ _) j)

/-- The path load of the last option `k` of cycle `c` (`0` if `k = 0`). -/
def lastL (x : Fin I.t → Fin I.k → R) (c : Fin I.t) : R :=
  if h : 0 < I.k then I.L x c ⟨I.k - 1, by omega⟩ else 0

/-- The reduced gradient `L(x)_{c,j} − L(x)_{c,k}` (`j < k`): `∇f` at `y` is `gradRed (xi y)`. -/
def gradRed (x : Fin I.t → Fin I.k → R) (c : Fin I.t) (j : Fin (I.k - 1)) : R :=
  I.L x c (Fin.castLE (Nat.sub_le _ _) j) - I.lastL x c

/-- `ξ = xiq 1`. -/
def xi (y : Fin I.t → Fin (I.k - 1) → ℝ) : Fin I.t → Fin I.k → ℝ := I.xiq 1 y

/-- The reduced polytope `Y = {y ≥ 0, ∑_j y_{c,j} ≤ 1}`. -/
def InY (y : Fin I.t → Fin (I.k - 1) → ℝ) : Prop :=
  (∀ c j, 0 ≤ y c j) ∧ ∀ c, ∑ j, y c j ≤ 1

/-- `f = F ∘ ξ`, the objective of the ellipsoid phase. -/
noncomputable def f (y : Fin I.t → Fin (I.k - 1) → ℝ) : ℝ := I.F (I.xi y)

variable {I}

theorem sum_fin_split {M : Type*} [AddCommMonoid M] :
    ∀ (K : ℕ) (hK : 0 < K) (g : Fin K → M),
      ∑ j, g j = ∑ j : Fin (K - 1), g (Fin.castLE (Nat.sub_le K 1) j) + g ⟨K - 1, by omega⟩
  | 0, hK, _ => absurd hK (Nat.lt_irrefl 0)
  | n + 1, _, g => by
    rw [Fin.sum_univ_castSucc]
    rfl

theorem xiq_castLE (q : R) (y : Fin I.t → Fin (I.k - 1) → R) (c : Fin I.t)
    (j : Fin (I.k - 1)) : I.xiq q y c (Fin.castLE (Nat.sub_le _ _) j) = y c j := by
  simp [xiq, j.2]

theorem xiq_last (q : R) (y : Fin I.t → Fin (I.k - 1) → R) (c : Fin I.t) (hk : 0 < I.k) :
    I.xiq q y c ⟨I.k - 1, by omega⟩ = q - ∑ j', y c j' := by
  simp [xiq]

theorem sum_xiq (q : R) (y : Fin I.t → Fin (I.k - 1) → R) (c : Fin I.t) (hk : 0 < I.k) :
    ∑ j, I.xiq q y c j = q := by
  rw [sum_fin_split I.k hk, xiq_last q y c hk]
  simp only [xiq_castLE]
  ring

/-- **A5(a).** `ξ(Y) ⊆ 𝒳` (for `k ≥ 1`). -/
theorem xi_inX (hk : 0 < I.k) {y : Fin I.t → Fin (I.k - 1) → ℝ} (hy : I.InY y) :
    I.InX (I.xi y) := by
  refine ⟨fun c j => ?_, fun c => sum_xiq 1 y c hk⟩
  unfold xi xiq
  split_ifs
  · exact hy.1 c _
  · linarith [hy.2 c]

theorem sum_red (x : Fin I.t → Fin I.k → R) (c : Fin I.t) (hk : 0 < I.k) :
    ∑ j, I.red x c j = ∑ j, x c j - x c ⟨I.k - 1, by omega⟩ := by
  rw [sum_fin_split I.k hk (x c)]
  simp [red]

/-- **A5(a).** Dropping the last coordinate maps `𝒳` into `Y`. -/
theorem red_inY {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) : I.InY (I.red x) := by
  refine ⟨fun c j => hx.1 c _, fun c => ?_⟩
  rw [sum_red x c (k_pos_of_inX hx c), hx.2 c]
  linarith [hx.1 c ⟨I.k - 1, by have := k_pos_of_inX hx c; omega⟩]

/-- **A5(a).** `ξ ∘ red = id` on `𝒳`. -/
theorem xi_red {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) : I.xi (I.red x) = x := by
  funext c j
  unfold xi xiq
  split_ifs with h
  · rfl
  · have hk := k_pos_of_inX hx c
    have hj : j = ⟨I.k - 1, by omega⟩ := Fin.ext (by have := j.2; simp only; omega)
    rw [sum_red x c hk, hx.2 c, hj]
    ring

/-- **A5(a).** `red ∘ ξ = id`. -/
theorem red_xiq (q : R) (y : Fin I.t → Fin (I.k - 1) → R) : I.red (I.xiq q y) = y := by
  funext c j
  exact xiq_castLE q y c j

theorem red_xi (y : Fin I.t → Fin (I.k - 1) → ℝ) : I.red (I.xi y) = y := red_xiq 1 y

/-- The fixed-point data of Phase E: completing integer data with `q` and dividing by `q` is
completing the real point. -/
theorem xiq_div (y : Fin I.t → Fin (I.k - 1) → ℤ) {q : ℕ} (hq : 0 < q) :
    ptOf (I.xiq (q : ℤ) y) q = I.xi (fun c j => (y c j : ℝ) / q) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  funext c j
  unfold ptOf xi xiq
  split_ifs
  · rfl
  · push_cast
    rw [← Finset.sum_div]
    field_simp

/-- The reduced gradient commutes with the scaling of integer data. -/
theorem gradRed_div (x : Fin I.t → Fin I.k → ℤ) {q : ℝ} (c : Fin I.t) (j : Fin (I.k - 1)) :
    I.gradRed (fun c j => (x c j : ℝ) / q) c j = ((I.gradRed x c j : ℤ) : ℝ) / q := by
  unfold gradRed lastL
  split_ifs <;> simp [L_div, sub_div]

/-- `⟨L(ξ y), ξ y' − ξ y⟩ = ⟨∇f(y), y' − y⟩`. -/
theorem inner_L_xi (hk : 0 < I.k) (y y' : Fin I.t → Fin (I.k - 1) → ℝ) :
    I.inner (I.L (I.xi y)) (I.xi y' - I.xi y) =
      ∑ c, ∑ j, I.gradRed (I.xi y) c j * (y' c j - y c j) := by
  unfold inner
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_fin_split I.k hk]
  simp only [Pi.sub_apply, xi, xiq_castLE, xiq_last (1 : ℝ) _ c hk, gradRed, lastL, hk,
    ↓reduceDIte, sub_mul, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- **A5(b).** The gradient inequality for `f`: `f(y') ≥ f(y) + ⟨∇f(y), y' − y⟩` for all
`y, y'` (with `∇f(y) = gradRed (ξ y)`). -/
theorem f_ge (hk : 0 < I.k) (y y' : Fin I.t → Fin (I.k - 1) → ℝ) :
    I.f y + ∑ c, ∑ j, I.gradRed (I.xi y) c j * (y' c j - y c j) ≤ I.f y' := by
  have h := I.F_ge (I.xi y) (I.xi y')
  rw [inner_L_xi hk] at h
  exact h

theorem xi_affine (y y' : Fin I.t → Fin (I.k - 1) → ℝ) (ρ : ℝ) :
    I.xi ((1 - ρ) • y + ρ • y') = (1 - ρ) • I.xi y + ρ • I.xi y' := by
  funext c j
  simp only [xi, xiq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rfl
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring

/-- **A5(c).** Convexity of `f`. -/
theorem f_convex (y y' : Fin I.t → Fin (I.k - 1) → ℝ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    I.f ((1 - ρ) • y + ρ • y') ≤ (1 - ρ) * I.f y + ρ * I.f y' := by
  unfold f
  rw [xi_affine]
  exact I.F_convex _ _ h0 h1

theorem f_nonneg (y : Fin I.t → Fin (I.k - 1) → ℝ) : 0 ≤ I.f y := F_nonneg _

/-- **A2(b)** in reduced coordinates: `f ≤ Φ₀` on `Y`. -/
theorem f_le_Phi0 (hI : I.Valid) {y : Fin I.t → Fin (I.k - 1) → ℝ} (hy : I.InY y) :
    I.f y ≤ Phi0 I.t I.k :=
  F_le_Phi0 hI (xi_inX (by have := hI.1; omega) hy)

/-- **A5(e).** `Y ⊆ [0,1]^n`. -/
theorem InY_le_one {y : Fin I.t → Fin (I.k - 1) → ℝ} (hy : I.InY y) (c : Fin I.t)
    (j : Fin (I.k - 1)) : 0 ≤ y c j ∧ y c j ≤ 1 :=
  ⟨hy.1 c j, (Finset.single_le_sum (fun j _ => hy.1 c j) (Finset.mem_univ j)).trans (hy.2 c)⟩

/-- **A5(d).** The ball of radius `r_Y = 1/(2(k−1))` around `c_Y = r_Y 𝟙` lies in `Y`
(`k ≥ 2`). -/
theorem ball_subset_Y (hk : 2 ≤ I.k) {y : Fin I.t → Fin (I.k - 1) → ℝ}
    (hy : ∑ c, ∑ j, (y c j - 1 / (2 * ((I.k - 1 : ℕ) : ℝ))) ^ 2 ≤
      (1 / (2 * ((I.k - 1 : ℕ) : ℝ))) ^ 2) : I.InY y := by
  set r : ℝ := 1 / (2 * ((I.k - 1 : ℕ) : ℝ)) with hr
  have hK : (1 : ℝ) ≤ ((I.k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ I.k - 1)
  have hrpos : 0 < r := by rw [hr]; positivity
  have hcj : ∀ c j, (y c j - r) ^ 2 ≤ ∑ j', (y c j' - r) ^ 2 := fun c j =>
    Finset.single_le_sum (fun j _ => sq_nonneg (y c j - r)) (Finset.mem_univ j)
  have hc : ∀ c, ∑ j', (y c j' - r) ^ 2 ≤ r ^ 2 := fun c =>
    (Finset.single_le_sum (f := fun c => ∑ j', (y c j' - r) ^ 2)
      (fun c _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ c)).trans hy
  refine ⟨fun c j => ?_, fun c => ?_⟩
  · have h1 := (hcj c j).trans (hc c)
    nlinarith
  · -- `∑_j y = (k−1) r + ∑_j (y − r)` and `(∑_j (y − r))² ≤ (k−1) ∑_j (y − r)²`
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin (I.k - 1) => (1 : ℝ))
      (fun j => y c j - r)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hcs
    have hsum : ∑ j, y c j = ((I.k - 1 : ℕ) : ℝ) * r + ∑ j, (y c j - r) := by
      rw [Finset.sum_sub_distrib]
      simp
    have hkr : ((I.k - 1 : ℕ) : ℝ) * r = 1 / 2 := by
      rw [hr]; field_simp
    have hkr2 : ((I.k - 1 : ℕ) : ℝ) * r ^ 2 ≤ 1 / 4 := by
      rw [hr]
      field_simp
      nlinarith
    have hS : (∑ j, (y c j - r)) ^ 2 ≤ 1 / 4 := by
      calc (∑ j, (y c j - r)) ^ 2 ≤ ((I.k - 1 : ℕ) : ℝ) * ∑ j, (y c j - r) ^ 2 := hcs
        _ ≤ ((I.k - 1 : ℕ) : ℝ) * r ^ 2 := mul_le_mul_of_nonneg_left (hc c) (by positivity)
        _ ≤ 1 / 4 := hkr2
    have : ∑ j, (y c j - r) ≤ 1 / 2 := by nlinarith [sq_nonneg (∑ j, (y c j - r) - 1 / 2)]
    rw [hsum, hkr]
    linarith

end Reduced

end Inst

end STACS2027.Runtimes.ConvexQP
