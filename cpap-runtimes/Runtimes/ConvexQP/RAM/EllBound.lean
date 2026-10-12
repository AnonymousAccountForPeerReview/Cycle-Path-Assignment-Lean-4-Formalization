module

public import Runtimes.ConvexQP.RAM.EllLoop
public import Runtimes.ConvexQP.RAM.EllInit
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: the polynomial step bound

With `X = t k + 2`: `⌈log₂(n/r_K)⌉ ≤ 76 X²` (from `logRad_le`, `⌈log₂ D⌉ ≤ D`, `D ≤ 2X`),
`N ≤ 1217 X⁴`, `p ≤ 4882 X³`; an iteration costs at most `10⁴ ((tk+1)² (p+1) + (p+1)²)`
(`iterCost_le`, monotonicity by `gcongr`), hence `O(X⁶)`, and the whole phase (setup plus at
most `N` iterations) costs at most `ellC · X^10` (`total_le`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### The constants in terms of `X = t k + 2` -/

theorem clog_le_self (x : ℕ) : Nat.clog 2 x ≤ x :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

theorem nDim_le_tk {t k : ℕ} : nDim t k ≤ t * k := by
  unfold nDim; rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

theorem logRad_le_X {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) :
    logRad t k ≤ 76 * (t * k + 2) ^ 2 := by
  have h0 := logRad_le ht hk
  have hD : dimKKT t k + 2 ≤ 2 * (t * k + 2) := by
    unfold dimKKT
    have : t ≤ t * k := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  have hc := clog_le_self (dimKKT t k + 2)
  have h1 : (8 * (dimKKT t k + 2) + 22) * Nat.clog 2 (dimKKT t k + 2) ≤
      (8 * (2 * (t * k + 2)) + 22) * (2 * (t * k + 2)) :=
    Nat.mul_le_mul (by omega) (hc.trans hD)
  nlinarith

theorem iters_le_X {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) :
    iters t k ≤ 1217 * (t * k + 2) ^ 4 := by
  have hL := logRad_le_X ht hk
  have hn := nDim_le_tk (t := t) (k := k)
  rw [iters_eq]
  set X := t * k + 2
  have h1 : 16 * nDim t k * (nDim t k + 1) * logRad t k ≤ 16 * X * X * (76 * X ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)) hL
  have h2 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem prec_le_X {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) :
    prec t k ≤ 4882 * (t * k + 2) ^ 3 := by
  have hL := logRad_le_X ht hk
  have hn := nDim_le_tk (t := t) (k := k)
  have hn2 := nDim_ge_two ht hk
  rw [prec_eq (by omega)]
  have hc := clog_le_self (nDim t k + 1)
  set X := t * k + 2
  have h1 : 64 * (nDim t k + 1) * logRad t k ≤ 64 * X * (76 * X ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hL
  have h2 : 1 ≤ X := by omega
  have h3 : X ≤ X ^ 3 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 3 := Nat.pow_le_pow_right h2 (by norm_num)
  have h4 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h5 : 64 * X * (76 * X ^ 2) = 4864 * X ^ 3 := by ring
  omega

/-! ### One iteration -/

/-- `iterCost` with every size replaced by an upper bound `Y` and `p` by `P`. -/
def iterPoly (Y P : ℕ) : ℕ :=
  2 + (Y * (Y * 56 + 38) + 10 + (Y * (Y * 58 + 61) + 7 +
  (Y * (Y * (31 * (P + 1) + 87) + 19) + 17 +
  (Y * (Y * (31 * (P + 1) + 130) + 49) + 31 * P + 147 +
  (93 * (P + 1) + 8 * P + 165))) + 2 +
  (Y * (Y * 66 + 11) + 8 + (Y * Y * (300 * (8 * P + 8) + 400) + Y * (220 * (8 * P + 8) + 500) +
    40 * (8 * P + 8 + 1) ^ 2 + 250 * (8 * P + 8) + 600) + 1)))

theorem iterCost_le_poly (I : Inst) (Y P : ℕ) (ht : I.t ≤ Y) (hk : I.k ≤ Y)
    (hk1 : I.k - 1 ≤ Y) (htk : I.t * I.k ≤ Y) (hn : nDim I.t I.k ≤ Y) (hp : prec I.t I.k ≤ P) :
    iterCost I ≤ iterPoly Y P := by
  unfold iterCost scanC feasC gC updCost bitB iterPoly
  gcongr

theorem iterPoly_le (Y P : ℕ) (hY : 1 ≤ Y) :
    iterPoly Y P ≤ 10000 * (Y * Y * (P + 1) + (P + 1) * (P + 1)) := by
  unfold iterPoly
  have h1 : Y ≤ Y * Y := Nat.le_mul_self Y
  have h2 : Y * Y ≤ Y * Y * (P + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : Y * P ≤ Y * Y * (P + 1) := by nlinarith
  have h4 : 1 ≤ Y * Y := by nlinarith
  nlinarith

/-- **The cost of an iteration** is `O((tk)² p + p²)`. -/
theorem iterCost_le (I : Inst) (hk : 3 ≤ I.k) (ht : 0 < I.t) :
    iterCost I ≤ 10000 * ((I.t * I.k + 1) * (I.t * I.k + 1) * (prec I.t I.k + 1) +
      (prec I.t I.k + 1) * (prec I.t I.k + 1)) := by
  have h1 : I.t ≤ I.t * I.k := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : I.k ≤ I.t * I.k := Nat.le_mul_of_pos_left _ ht
  exact (iterCost_le_poly I (I.t * I.k + 1) (prec I.t I.k) (by omega) (by omega) (by omega)
    (by omega) (by have := nDim_le_tk (t := I.t) (k := I.k); omega) le_rfl).trans
    (iterPoly_le _ _ (by omega))

/-! ### The whole phase -/

/-- The constant of the step bound. -/
def ellC : ℕ := 1217 * (10000 * 4883 + 10000 * 4883 ^ 2 + 1) + 200000 + 1

theorem setupCost_le (I : Inst) (hk : 3 ≤ I.k) (ht : 0 < I.t) :
    setupCost I ≤ 200000 * (I.t * I.k + 2) ^ 3 := by
  have hn := nDim_le_tk (t := I.t) (k := I.k)
  have hp := prec_le_X ht hk
  set X := I.t * I.k + 2
  have hmc : mulCost (nDim I.t I.k) ≤ 31 * X + 22 := by
    unfold mulCost
    have : Nat.size (nDim I.t I.k) ≤ nDim I.t I.k := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hn2 : nDim I.t I.k * (nDim I.t I.k * 14 + 7) ≤ X * (X * 14 + 7) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h1 : 1 ≤ X := by omega
  have h3 : X ≤ X ^ 3 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
  have h4 : X * X ≤ X ^ 3 := by
    calc X * X = X ^ 2 := (sq X).symm
      _ ≤ X ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
  have h5 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
  unfold setupCost
  nlinarith

/-- **The step bound of Phase E**: the setup and at most `N` iterations cost at most
`ellC · (t k + 2)^10`. -/
theorem total_le (I : Inst) (hk : 3 ≤ I.k) (ht : 0 < I.t) :
    setupCost I + (iters I.t I.k * (iterCost I + 1) + 1) ≤ ellC * (I.t * I.k + 2) ^ 10 := by
  have hit := iterCost_le I hk ht
  have hN := iters_le_X ht hk
  have hp := prec_le_X ht hk
  have hs := setupCost_le I hk ht
  set X := I.t * I.k + 2 with hX
  set P := prec I.t I.k
  set Y := I.t * I.k + 1
  have hX1 : 1 ≤ X := by omega
  have hYX : Y ≤ X := by omega
  have hP1 : P + 1 ≤ 4883 * X ^ 3 := by
    have : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have hmono : ∀ a b : ℕ, a ≤ b → X ^ a ≤ X ^ b := fun a b h => Nat.pow_le_pow_right hX1 h
  have e1 : Y * Y * (P + 1) ≤ 4883 * X ^ 6 := by
    calc Y * Y * (P + 1) ≤ X * X * (4883 * X ^ 3) := Nat.mul_le_mul (Nat.mul_le_mul hYX hYX) hP1
      _ = 4883 * X ^ 5 := by ring
      _ ≤ 4883 * X ^ 6 := Nat.mul_le_mul_left _ (hmono 5 6 (by norm_num))
  have e2 : (P + 1) * (P + 1) ≤ 4883 ^ 2 * X ^ 6 := by
    calc (P + 1) * (P + 1) ≤ (4883 * X ^ 3) * (4883 * X ^ 3) := Nat.mul_le_mul hP1 hP1
      _ = 4883 ^ 2 * X ^ 6 := by ring
  have e3 : iterCost I + 1 ≤ (10000 * 4883 + 10000 * 4883 ^ 2 + 1) * X ^ 6 := by
    have : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have e4 : iters I.t I.k * (iterCost I + 1) ≤
      1217 * (10000 * 4883 + 10000 * 4883 ^ 2 + 1) * X ^ 10 := by
    calc iters I.t I.k * (iterCost I + 1)
        ≤ (1217 * X ^ 4) * ((10000 * 4883 + 10000 * 4883 ^ 2 + 1) * X ^ 6) :=
          Nat.mul_le_mul hN e3
      _ = 1217 * (10000 * 4883 + 10000 * 4883 ^ 2 + 1) * X ^ 10 := by ring
  have e5 : 200000 * X ^ 3 ≤ 200000 * X ^ 10 := Nat.mul_le_mul_left _ (hmono 3 10 (by norm_num))
  have e6 : 1 ≤ X ^ 10 := Nat.one_le_pow _ _ (by omega)
  unfold ellC
  nlinarith

/-- **The memory of Phase E**: the layout (from the initial free address `F0`) and the scratch
allowance `ellSc` above it fit in `ellC · (t k + 2)^10` cells. -/
theorem ellSpace_le (I : Inst) (hk : 3 ≤ I.k) (ht : 0 < I.t) (bh F0 : ℕ) :
    (layOf I bh F0).F + ellSc I.t I.k ≤ F0 + ellC * (I.t * I.k + 2) ^ 10 := by
  have hn := nDim_le_tk (t := I.t) (k := I.k)
  have hp := prec_le_X ht hk
  set X := I.t * I.k + 2 with hX
  have hX1 : 1 ≤ X := by omega
  have hmono : ∀ a b : ℕ, a ≤ b → X ^ a ≤ X ^ b := fun a b h => Nat.pow_le_pow_right hX1 h
  have e1 : nDim I.t I.k * (2 * nDim I.t I.k) ≤ 2 * X ^ 10 := by
    calc nDim I.t I.k * (2 * nDim I.t I.k) ≤ X * (2 * X) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * X ^ 2 := by ring
      _ ≤ 2 * X ^ 10 := Nat.mul_le_mul_left _ (hmono 2 10 (by norm_num))
  have e2 : X ≤ X ^ 10 := by simpa using hmono 1 10 (by norm_num)
  have e3 : X ^ 3 ≤ X ^ 10 := hmono 3 10 (by norm_num)
  have e4 : 1 ≤ X ^ 10 := Nat.one_le_pow _ _ (by omega)
  have hC : 625042 ≤ ellC := by unfold ellC; norm_num
  have hC2 : 625042 * X ^ 10 ≤ ellC * X ^ 10 := Nat.mul_le_mul_right _ hC
  simp only [layOf, ellSc, bitB]
  omega

end STACS2027.Runtimes.QPRam
