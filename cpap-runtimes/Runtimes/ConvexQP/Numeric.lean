module

public import Runtimes.ConvexQP.Cut
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# Lemma 16, Part B: numeric helpers (rounding, square root, B8, E0)

* `roundDiv u v = ⌊(2u + v)/(2v)⌋` (the nearest integer to `u/v` for `v > 0`, ties up;
  `roundDiv_err`: error `≤ ½`) and the integer square root `Nat.sqrt`: `isqrt_approx` says that
  `S = ⌊√(G·2^{3p})⌋` gives `s = S/2^{2p} ∈ (√γ − 2^{−2p}, √γ]` for `γ = G/2^p`.
* The parameters of the ellipsoid in dimension `n`: `etaOf n = η = 1/(32n(n+1))`,
  `ellOf n i = ℓ_i = (n/4)(n/(n+1))^{2i}` (the Loewner lower bound after `i` cuts),
  `thetaOf n = θ = (1+η)^{4n} κⁿ (n−1)/(n+1)` (the determinant factor per cut) and
  `growOf n = (1+η)⁴ κ` (the growth factor of the Loewner upper bound).
* **B8** (`thetaOf_le`): `θ ≤ exp(−1/(8(n+1)))` for `n ≥ 2`.
* **E0** (`prec_main`, `prec_bounds`): if `p ≥ 4⌈N/n⌉ + 2⌈log₂(n+1)⌉ + 9` then
  `4n ≤ η ℓ_N 2^p`; hence, with `ϵ = 2^{−p−1}` and `δ = 2^{−2p}`: `nϵ ≤ ηℓ_N`,
  `nϵ² ≤ (η/4)²ℓ_N` and `δ² ≤ (η/4)²ℓ_N`.
* The final count (`final_lt`): for `N = 16n(n+1)L + 1` and `2^L ≥ n/r`,
  `(n/4)ⁿ θ^N < r^{2n}`.
* Magnitudes (`grow_pow_le`): `growOf n ^ N ≤ 2^p` when `p ≥ 4⌈N/n⌉`.
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

/-! ### Integer rounding and the integer square root -/

/-- `roundDiv u v = ⌊(2u + v)/(2v)⌋`: the nearest integer to `u/v` (for `v > 0`), ties up. -/
def roundDiv (u v : ℤ) : ℤ := (2 * u + v) / (2 * v)

/-- `roundDiv` errs by at most `½`. -/
theorem roundDiv_err (u : ℤ) {v : ℤ} (hv : 0 < v) :
    |(roundDiv u v : ℝ) - (u : ℝ) / v| ≤ 1 / 2 := by
  unfold roundDiv
  have h2v : 0 < 2 * v := by omega
  have hmod := Int.emod_add_ediv_mul (2 * u + v) (2 * v)
  have hr0 := Int.emod_nonneg (2 * u + v) h2v.ne'
  have hr1 := Int.emod_lt_of_pos (2 * u + v) h2v
  set q := (2 * u + v) / (2 * v)
  set r := (2 * u + v) % (2 * v)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hmodR : (r : ℝ) + q * (2 * v) = 2 * u + v := by exact_mod_cast hmod
  have hr0R : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr1R : (r : ℝ) < 2 * v := by exact_mod_cast hr1
  have e : (q : ℝ) - u / v = 1 / 2 - r / (2 * v) := by
    field_simp
    linarith
  rw [e, abs_le]
  have h1 : (r : ℝ) / (2 * v) < 1 := by rw [div_lt_one (by positivity)]; exact hr1R
  have h2 : 0 ≤ (r : ℝ) / (2 * v) := by positivity
  constructor <;> linarith

/-- The rounded square root: `S = ⌊√(G·2^{3p})⌋` satisfies
`S/2^{2p} ≤ √(G/2^p) < (S+1)/2^{2p}`. -/
theorem isqrt_approx (G p : ℕ) :
    (Nat.sqrt (G * 2 ^ (3 * p)) : ℝ) / 2 ^ (2 * p) ≤ Real.sqrt ((G : ℝ) / 2 ^ p) ∧
      Real.sqrt ((G : ℝ) / 2 ^ p) < ((Nat.sqrt (G * 2 ^ (3 * p)) : ℝ) + 1) / 2 ^ (2 * p) := by
  set S := Nat.sqrt (G * 2 ^ (3 * p))
  have h1 : S * S ≤ G * 2 ^ (3 * p) := Nat.sqrt_le (G * 2 ^ (3 * p))
  have h2 : G * 2 ^ (3 * p) < (S + 1) * (S + 1) := Nat.lt_succ_sqrt (G * 2 ^ (3 * p))
  have hP : (0 : ℝ) < 2 ^ (2 * p) := by positivity
  have e : Real.sqrt ((G : ℝ) / 2 ^ p) = Real.sqrt ((G : ℝ) * 2 ^ (3 * p)) / 2 ^ (2 * p) := by
    rw [eq_div_iff hP.ne', ← Real.sqrt_sq hP.le, ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [← pow_mul, show 2 * p * 2 = p + 3 * p by ring, pow_add]
    field_simp
  rw [e]
  have h1R : (S : ℝ) * S ≤ (G : ℝ) * 2 ^ (3 * p) := by exact_mod_cast h1
  have h2R : (G : ℝ) * 2 ^ (3 * p) < ((S : ℝ) + 1) * ((S : ℝ) + 1) := by exact_mod_cast h2
  constructor
  · rw [div_le_div_iff_of_pos_right hP]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  · rw [div_lt_div_iff_of_pos_right hP]
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith

/-- `|S/2^{2p} − √(G/2^p)| ≤ 2^{−2p}`. -/
theorem isqrt_err (G p : ℕ) :
    |(Nat.sqrt (G * 2 ^ (3 * p)) : ℝ) / 2 ^ (2 * p) - Real.sqrt ((G : ℝ) / 2 ^ p)| ≤
      1 / 2 ^ (2 * p) := by
  obtain ⟨h1, h2⟩ := isqrt_approx G p
  have h3 : (0 : ℝ) ≤ 1 / 2 ^ (2 * p) := by positivity
  rw [abs_le]
  constructor
  · rw [add_div] at h2
    linarith
  · linarith

/-! ### The parameters in dimension `n` -/

/-- `η = 1/(32 n (n+1))`. -/
noncomputable def etaOf (n : ℕ) : ℝ := 1 / (32 * n * (n + 1))

/-- `ℓ_i = (n/4)(n/(n+1))^{2i}`: the Loewner lower bound after `i` cuts. -/
noncomputable def ellOf (n i : ℕ) : ℝ := n / 4 * ((n : ℝ) / (n + 1)) ^ (2 * i)

/-- `θ = (1+η)^{4n} κⁿ (n−1)/(n+1)`: the determinant factor of one rounded cut. -/
noncomputable def thetaOf (n : ℕ) : ℝ :=
  (1 + etaOf n) ^ (4 * n) * (kap n ^ n * (((n : ℝ) - 1) / (n + 1)))

/-- `(1+η)⁴ κ`: the growth factor of the Loewner upper bound per cut. -/
noncomputable def growOf (n : ℕ) : ℝ := (1 + etaOf n) ^ 4 * kap n

theorem etaOf_pos {n : ℕ} (hn : 1 ≤ n) : 0 < etaOf n := by
  unfold etaOf
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem etaOf_le {n : ℕ} (hn : 1 ≤ n) : etaOf n ≤ 1 / 8 := by
  unfold etaOf
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem ellOf_pos {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : 0 < ellOf n i := by
  unfold ellOf
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem ellOf_succ (n i : ℕ) : ellOf n (i + 1) = ((n : ℝ) / (n + 1)) ^ 2 * ellOf n i := by
  unfold ellOf
  rw [show 2 * (i + 1) = 2 * i + 2 by ring, pow_add]
  ring

theorem ellOf_zero (n : ℕ) : ellOf n 0 = n / 4 := by simp [ellOf]

theorem ellOf_anti {n : ℕ} (hn : 1 ≤ n) {i j : ℕ} (hij : i ≤ j) : ellOf n j ≤ ellOf n i := by
  unfold ellOf
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_of_le_one (by positivity) (by rw [div_le_one (by positivity)]; linarith)
    (by omega)

theorem ellOf_le {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : ellOf n i ≤ n / 4 := by
  have := ellOf_anti hn (Nat.zero_le i)
  rwa [ellOf_zero] at this

theorem thetaOf_pos {n : ℕ} (hn : 2 ≤ n) : 0 < thetaOf n := by
  unfold thetaOf
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  have := kap_pos h1
  have := etaOf_pos (n := n) (by omega)
  have : (0 : ℝ) < (n - 1) / (n + 1) := div_pos (by linarith) (by linarith)
  positivity

theorem growOf_pos {n : ℕ} (hn : 2 ≤ n) : 0 < growOf n := by
  unfold growOf
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  have := kap_pos h1
  have := etaOf_pos (n := n) (by omega)
  positivity

/-! ### B8 -/

theorem one_add_le_exp (x : ℝ) : 1 + x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

theorem pow_le_exp_mul {x : ℝ} (hx : 0 ≤ 1 + x) (m : ℕ) : (1 + x) ^ m ≤ Real.exp (m * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hx (one_add_le_exp x) m

/-- `κⁿ (n−1)/(n+1) ≤ exp(−1/(4(n+1)))` for `n ≥ 2`. -/
theorem kap_part_le {n : ℕ} (hn : 2 ≤ n) :
    kap n ^ n * (((n : ℝ) - 1) / (n + 1)) ≤ Real.exp (-(1 / (4 * ((n : ℝ) + 1)))) := by
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · -- `n = 2`: `16/27 ≤ 11/12 ≤ exp(−1/12)`
    obtain rfl : n = 2 := by omega
    have h := one_add_le_exp (-(1 / (4 * ((2 : ℕ) + 1 : ℝ))))
    unfold kap
    norm_num at h ⊢
    linarith
  · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h3
    have hk : kap n = 1 + 1 / ((n : ℝ) ^ 2 - 1) := by
      unfold kap
      have : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp
      ring
    have hpos : 0 ≤ 1 + 1 / ((n : ℝ) ^ 2 - 1) := by
      have : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
      positivity
    have h1 := pow_le_exp_mul hpos n
    have h2 : ((n : ℝ) - 1) / (n + 1) ≤ Real.exp (-(2 / ((n : ℝ) + 1))) := by
      have := one_add_le_exp (-(2 / ((n : ℝ) + 1)))
      have e : ((n : ℝ) - 1) / (n + 1) = 1 + -(2 / ((n : ℝ) + 1)) := by
        field_simp
        ring
      rw [e]
      exact this
    rw [hk]
    calc (1 + 1 / ((n : ℝ) ^ 2 - 1)) ^ n * (((n : ℝ) - 1) / (n + 1))
        ≤ Real.exp (n * (1 / ((n : ℝ) ^ 2 - 1))) * Real.exp (-(2 / ((n : ℝ) + 1))) :=
          mul_le_mul h1 h2 (div_nonneg (by linarith) (by linarith)) (Real.exp_pos _).le
      _ = Real.exp (n * (1 / ((n : ℝ) ^ 2 - 1)) + -(2 / ((n : ℝ) + 1))) := by
          rw [Real.exp_add]
      _ ≤ Real.exp (-(1 / (4 * ((n : ℝ) + 1)))) := by
          rw [Real.exp_le_exp]
          have : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
          have e : (n : ℝ) * (1 / ((n : ℝ) ^ 2 - 1)) + -(2 / ((n : ℝ) + 1)) =
              -(((n : ℝ) - 2) / ((n : ℝ) ^ 2 - 1)) := by
            field_simp
            ring
          rw [e, neg_le_neg_iff, div_le_div_iff₀ (by positivity) this]
          nlinarith

/-- **B8.** `θ = (1+η)^{4n} κⁿ (n−1)/(n+1) ≤ exp(−1/(8(n+1)))` for `n ≥ 2`. -/
theorem thetaOf_le {n : ℕ} (hn : 2 ≤ n) : thetaOf n ≤ Real.exp (-(1 / (8 * ((n : ℝ) + 1)))) := by
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hη := etaOf_pos (n := n) (by omega)
  have h1 : (1 + etaOf n) ^ (4 * n) ≤ Real.exp (1 / (8 * ((n : ℝ) + 1))) := by
    have := pow_le_exp_mul (by linarith : (0 : ℝ) ≤ 1 + etaOf n) (4 * n)
    refine this.trans (le_of_eq ?_)
    congr 1
    unfold etaOf
    push_cast
    field_simp
    ring
  have h2 := kap_part_le hn
  unfold thetaOf
  have h3 : 0 ≤ kap n ^ n * (((n : ℝ) - 1) / (n + 1)) := by
    have := kap_pos (by linarith : (1 : ℝ) < n)
    have : (0 : ℝ) ≤ (n - 1) / (n + 1) := div_nonneg (by linarith) (by linarith)
    positivity
  calc (1 + etaOf n) ^ (4 * n) * (kap n ^ n * (((n : ℝ) - 1) / (n + 1)))
      ≤ Real.exp (1 / (8 * ((n : ℝ) + 1))) * Real.exp (-(1 / (4 * ((n : ℝ) + 1)))) :=
        mul_le_mul h1 h2 h3 (Real.exp_pos _).le
    _ = Real.exp (-(1 / (8 * ((n : ℝ) + 1)))) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring

/-- The growth factor of the upper Loewner bound: `(1+η)⁴ κ ≤ exp(2/n²)` for `n ≥ 2`. -/
theorem growOf_le {n : ℕ} (hn : 2 ≤ n) : growOf n ≤ Real.exp (2 / (n : ℝ) ^ 2) := by
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hη := etaOf_pos (n := n) (by omega)
  have h1 := pow_le_exp_mul (by linarith : (0 : ℝ) ≤ 1 + etaOf n) 4
  have hk : kap n = 1 + 1 / ((n : ℝ) ^ 2 - 1) := by
    unfold kap
    have : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  have hpos : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have h2 : kap n ≤ Real.exp (1 / ((n : ℝ) ^ 2 - 1)) := by
    rw [hk]; exact one_add_le_exp _
  unfold growOf
  calc (1 + etaOf n) ^ 4 * kap n
      ≤ Real.exp ((4 : ℕ) * etaOf n) * Real.exp (1 / ((n : ℝ) ^ 2 - 1)) :=
        mul_le_mul h1 h2 (kap_pos (by linarith)).le (Real.exp_pos _).le
    _ = Real.exp ((4 : ℕ) * etaOf n + 1 / ((n : ℝ) ^ 2 - 1)) := by rw [Real.exp_add]
    _ ≤ Real.exp (2 / (n : ℝ) ^ 2) := by
        rw [Real.exp_le_exp]
        unfold etaOf
        have e1 : ((4 : ℕ) : ℝ) * (1 / (32 * (n : ℝ) * (n + 1))) ≤ 1 / (8 * (n : ℝ) ^ 2) := by
          have e0 : ((4 : ℕ) : ℝ) * (1 / (32 * (n : ℝ) * (n + 1))) = 1 / (8 * ((n : ℝ) * (n + 1))) := by
            push_cast
            field_simp
            ring
          rw [e0]
          exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
        have e2 : 1 / ((n : ℝ) ^ 2 - 1) ≤ 4 / (3 * (n : ℝ) ^ 2) := by
          rw [div_le_div_iff₀ hpos (by positivity)]
          nlinarith
        have e3 : 1 / (8 * (n : ℝ) ^ 2) + 4 / (3 * (n : ℝ) ^ 2) ≤ 2 / (n : ℝ) ^ 2 := by
          rw [div_add_div _ _ (by positivity) (by positivity),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_pos (by positivity : (0 : ℝ) < n) 4]
        linarith

/-! ### E0: the precision -/

theorem le_mul_ceil (N n : ℕ) (hn : 0 < n) : N ≤ n * ((N + n - 1) / n) := by
  have h1 := Nat.div_add_mod (N + n - 1) n
  have h2 := Nat.mod_lt (N + n - 1) hn
  generalize n * ((N + n - 1) / n) = A at *
  omega

theorem exp_one_le_four : Real.exp 1 ≤ 4 := by
  have h := one_add_le_exp (-(1 / 2))
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    rw [Real.exp_neg] at h
    have hp := Real.exp_pos (1 / 2)
    rw [le_inv_comm₀ (by norm_num) hp] at h
    linarith
  have e : Real.exp 1 = Real.exp (1 / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  nlinarith [Real.exp_pos (1 / 2)]

/-- `((n+1)/n)^{2N} ≤ 16^{⌈N/n⌉}`. -/
theorem ratio_pow_le {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    (((n : ℝ) + 1) / n) ^ (2 * N) ≤ 16 ^ ((N + n - 1) / n) := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  set c := (N + n - 1) / n
  have hc : N ≤ n * c := le_mul_ceil N n (by omega)
  have hge : (1 : ℝ) ≤ ((n : ℝ) + 1) / n := by rw [le_div_iff₀ h0]; linarith
  have hb : (((n : ℝ) + 1) / n) ^ n ≤ 4 := by
    have e : ((n : ℝ) + 1) / n = 1 + 1 / n := by field_simp
    rw [e]
    refine (pow_le_exp_mul (by positivity) n).trans ?_
    rw [mul_one_div_cancel h0.ne']
    exact exp_one_le_four
  calc (((n : ℝ) + 1) / n) ^ (2 * N) ≤ (((n : ℝ) + 1) / n) ^ (n * (2 * c)) :=
        pow_le_pow_right₀ hge (by nlinarith)
    _ = ((((n : ℝ) + 1) / n) ^ n) ^ (2 * c) := by rw [pow_mul]
    _ ≤ 4 ^ (2 * c) := pow_le_pow_left₀ (by positivity) hb _
    _ = 16 ^ c := by rw [pow_mul]; norm_num

/-- **E0.** If `p ≥ 4⌈N/n⌉ + 2⌈log₂(n+1)⌉ + 9`, then `4n ≤ η ℓ_N 2^p`. -/
theorem prec_main {n N p : ℕ} (hn : 1 ≤ n)
    (hp : 4 * ((N + n - 1) / n) + 2 * Nat.clog 2 (n + 1) + 9 ≤ p) :
    (4 * n : ℝ) ≤ etaOf n * ellOf n N * 2 ^ p := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  set c := (N + n - 1) / n
  set L := Nat.clog 2 (n + 1)
  have hL : n + 1 ≤ 2 ^ L := Nat.le_pow_clog (by norm_num) _
  have hLR : (n : ℝ) + 1 ≤ 2 ^ L := by exact_mod_cast hL
  have hr := ratio_pow_le hn N
  have e : etaOf n * ellOf n N = 1 / (128 * ((n : ℝ) + 1) * (((n : ℝ) + 1) / n) ^ (2 * N)) := by
    unfold etaOf ellOf
    rw [div_pow, div_pow]
    field_simp
    ring
  rw [e, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  have h2p : (2 : ℝ) ^ (4 * c + 2 * L + 9) ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have hsplit : (2 : ℝ) ^ (4 * c + 2 * L + 9) = 16 ^ c * (2 ^ L) ^ 2 * 512 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, show (512 : ℝ) = 2 ^ 9 by norm_num, ← pow_mul,
      ← pow_mul, ← pow_add, ← pow_add]
    ring_nf
  rw [hsplit] at h2p
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ (2 ^ L) ^ 2 := pow_le_pow_left₀ (by positivity) hLR 2
  have hA : 0 ≤ (((n : ℝ) + 1) / n) ^ (2 * N) := by positivity
  calc 4 * (n : ℝ) * (128 * ((n : ℝ) + 1) * (((n : ℝ) + 1) / n) ^ (2 * N))
      = 512 * ((n : ℝ) * (n + 1)) * (((n : ℝ) + 1) / n) ^ (2 * N) := by ring
    _ ≤ 512 * ((n : ℝ) + 1) ^ 2 * 16 ^ c := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (by nlinarith) (by norm_num)) hr hA
          (by positivity)
    _ ≤ 512 * (2 ^ L) ^ 2 * 16 ^ c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)
    _ = 16 ^ c * (2 ^ L) ^ 2 * 512 := by ring
    _ ≤ 2 ^ p := h2p

/-- **E0, consequences.** With `ϵ = 2^{−p−1}` and `δ = 2^{−2p}`: `nϵ ≤ ηℓ_N`,
`nϵ² ≤ (η/4)²ℓ_N` and `δ² ≤ (η/4)²ℓ_N`. -/
theorem prec_bounds {n N p : ℕ} (hn : 1 ≤ n)
    (hmain : (4 * n : ℝ) ≤ etaOf n * ellOf n N * 2 ^ p) :
    (n : ℝ) * (1 / 2 ^ (p + 1)) ≤ etaOf n * ellOf n N ∧
      (n : ℝ) * (1 / 2 ^ (p + 1)) ^ 2 ≤ (etaOf n / 4) ^ 2 * ellOf n N ∧
      (1 / (2 : ℝ) ^ (2 * p)) ^ 2 ≤ (etaOf n / 4) ^ 2 * ellOf n N := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hη := etaOf_pos hn
  have hℓ := ellOf_pos hn N
  have hℓle := ellOf_le hn N
  set x : ℝ := 1 / 2 ^ p with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hm : 4 * n * x ≤ etaOf n * ellOf n N := by
    rw [hx, ← mul_div_assoc, mul_one, div_le_iff₀ (by positivity)]
    exact hmain
  have e1 : (1 : ℝ) / 2 ^ (p + 1) = x / 2 := by rw [hx, pow_succ]; field_simp
  have e2 : (1 : ℝ) / 2 ^ (2 * p) = x ^ 2 := by rw [hx, pow_mul']; field_simp
  rw [e1, e2]
  set ηℓ := etaOf n * ellOf n N
  refine ⟨by nlinarith, ?_, ?_⟩
  · -- `n x²/4 ≤ η²ℓ/16`: from `4 n x ≤ ηℓ` and `ℓ ≤ n/4`
    have hsq : (4 * n * x) ^ 2 ≤ ηℓ ^ 2 := pow_le_pow_left₀ (by positivity) hm 2
    have h3 : ηℓ ^ 2 = etaOf n ^ 2 * ellOf n N * ellOf n N := by ring
    have h4 : etaOf n ^ 2 * ellOf n N * ellOf n N ≤ etaOf n ^ 2 * ellOf n N * (4 * n) := by
      refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : 16 * n ^ 2 * x ^ 2 ≤ etaOf n ^ 2 * ellOf n N * (4 * n) := by nlinarith
    have h6 : 4 * n * x ^ 2 ≤ etaOf n ^ 2 * ellOf n N := by
      have h7 : (4 * (n : ℝ)) * (4 * n * x ^ 2) ≤ (4 * n) * (etaOf n ^ 2 * ellOf n N) := by
        nlinarith
      exact le_of_mul_le_mul_left h7 (by positivity)
    nlinarith
  · -- `x⁴ ≤ x² ≤ (ηℓ/(4n))² ≤ η²ℓ/16`
    have hsq : (4 * n * x) ^ 2 ≤ ηℓ ^ 2 := pow_le_pow_left₀ (by positivity) hm 2
    have hx4 : (x ^ 2) ^ 2 ≤ x ^ 2 := by nlinarith [pow_le_one₀ hx0.le hx1 (n := 2)]
    have h3 : ηℓ ^ 2 = etaOf n ^ 2 * ellOf n N * ellOf n N := by ring
    have h4 : ellOf n N ≤ (n : ℝ) ^ 2 := by nlinarith
    have h5 : 16 * n ^ 2 * x ^ 2 ≤ etaOf n ^ 2 * ellOf n N * n ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg (sq_nonneg (etaOf n)) hℓ.le)]
    have h6 : 16 * x ^ 2 ≤ etaOf n ^ 2 * ellOf n N := by
      have h7 : (n : ℝ) ^ 2 * (16 * x ^ 2) ≤ (n : ℝ) ^ 2 * (etaOf n ^ 2 * ellOf n N) := by
        nlinarith
      exact le_of_mul_le_mul_left h7 (by positivity)
    nlinarith

/-! ### The final count -/

/-- For `N = 16n(n+1)L + 1` and `2^L ≥ n/r` (`r > 0`), the determinant bound after `N` cuts is
below the volume bound of a ball of radius `r`: `(n/4)ⁿ θ^N < r^{2n}`. -/
theorem final_lt {n L : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) (hL : (n : ℝ) / r ≤ 2 ^ L) :
    ((n : ℝ) / 4) ^ n * thetaOf n ^ (16 * n * (n + 1) * L + 1) < r ^ (2 * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set N := 16 * n * (n + 1) * L + 1
  have hθ := thetaOf_le hn
  have hθ0 := thetaOf_pos hn
  have h1 : thetaOf n ^ N ≤ Real.exp (-(N / (8 * ((n : ℝ) + 1)))) := by
    calc thetaOf n ^ N ≤ Real.exp (-(1 / (8 * ((n : ℝ) + 1)))) ^ N :=
          pow_le_pow_left₀ hθ0.le hθ N
      _ = _ := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have h2 : Real.exp (-(N / (8 * ((n : ℝ) + 1)))) < Real.exp (-(2 * n * L)) := by
    rw [Real.exp_lt_exp, neg_lt_neg_iff, lt_div_iff₀ (by positivity)]
    simp only [N]
    push_cast
    nlinarith
  have h3 : (n : ℝ) / r ≤ Real.exp L := by
    refine hL.trans ?_
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) L
  have h4 : (n : ℝ) / 4 * Real.exp (-(2 * L)) ≤ r ^ 2 := by
    have hexp : Real.exp (-(2 * L)) = 1 / Real.exp L ^ 2 := by
      rw [Real.exp_neg, one_div, ← Real.exp_nat_mul]
      norm_num
    rw [hexp]
    have hE : 0 < Real.exp L := Real.exp_pos _
    have h5 : (n : ℝ) ^ 2 ≤ r ^ 2 * Real.exp L ^ 2 := by
      have := (div_le_iff₀ hr).mp h3
      nlinarith [pow_le_pow_left₀ (by positivity) this 2]
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h7 : (n : ℝ) / 4 ≤ (n : ℝ) ^ 2 := by nlinarith
    linarith
  have h6 : ((n : ℝ) / 4) ^ n * Real.exp (-(2 * n * L)) =
      ((n : ℝ) / 4 * Real.exp (-(2 * L))) ^ n := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  calc ((n : ℝ) / 4) ^ n * thetaOf n ^ N
      ≤ ((n : ℝ) / 4) ^ n * Real.exp (-(N / (8 * ((n : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ < ((n : ℝ) / 4) ^ n * Real.exp (-(2 * n * L)) :=
        mul_lt_mul_of_pos_left h2 (by positivity)
    _ = ((n : ℝ) / 4 * Real.exp (-(2 * L))) ^ n := h6
    _ ≤ (r ^ 2) ^ n := pow_le_pow_left₀ (by positivity) h4 n
    _ = r ^ (2 * n) := by rw [← pow_mul]

/-! ### Magnitudes -/

/-- The upper Loewner bound after `N` cuts: `growOf n ^ N ≤ 2^p` when `p ≥ 4⌈N/n⌉`. -/
theorem grow_pow_le {n N p : ℕ} (hn : 2 ≤ n) (hp : 4 * ((N + n - 1) / n) ≤ p) :
    growOf n ^ N ≤ 2 ^ p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set c := (N + n - 1) / n
  have hc : N ≤ n * c := le_mul_ceil N n (by omega)
  have hcR : (N : ℝ) ≤ n * c := by exact_mod_cast hc
  calc growOf n ^ N ≤ Real.exp (2 / (n : ℝ) ^ 2) ^ N :=
        pow_le_pow_left₀ (growOf_pos hn).le (growOf_le hn) N
    _ = Real.exp (N * (2 / (n : ℝ) ^ 2)) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp (c : ℕ) := by
        rw [Real.exp_le_exp, mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
    _ = Real.exp 1 ^ c := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ 4 ^ c := pow_le_pow_left₀ (Real.exp_pos _).le exp_one_le_four c
    _ = 2 ^ (2 * c) := by rw [pow_mul]; norm_num
    _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) (by omega)

end STACS2027.Runtimes.ConvexQP
