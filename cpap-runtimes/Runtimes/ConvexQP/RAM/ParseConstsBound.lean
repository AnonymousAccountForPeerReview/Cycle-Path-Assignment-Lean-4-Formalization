module

public import Runtimes.ConvexQP.RAM.ParseConsts
import Mathlib.Tactic

/-!
# Lemma 16 on the RAM, the constants: the step bound

`constCost_le`: for `t ≥ 1`, `k ≥ 3`, the constants phase costs at most `3000 D³` steps with
`D = (k+1)t + 2`. Crude bounds: `size x ≤ x` for the small factors; the bit lengths of `E` and
`E²` from `bigE_le` (`E ≤ 2 D^{2D+2}`); `L = ⌈log₂(n/r_K)⌉ ≤ (8D + 22) ⌈log₂ D⌉ ≤ (8D+22) D`
(`logRad_le`); `C₀ = 2(k−2)t² ≤ 2D³`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Parse

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP

theorem size_le_self (n : ℕ) : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

theorem mulCost_le (x : ℕ) : Arith.mulCost x ≤ 31 * x + 22 := by
  unfold Arith.mulCost; have := size_le_self x; omega

theorem mulCost_le_of {x s : ℕ} (h : x < 2 ^ s) : Arith.mulCost x ≤ 31 * s + 22 := by
  unfold Arith.mulCost; have := Nat.size_le.mpr h; omega

/-- The bit length of `E`. -/
theorem bigE_lt {t k : ℕ} (ht : 0 < t) :
    bigE t k < 2 ^ ((dimKKT t k + 2) * (2 * (dimKKT t k + 2) + 2) + 2) := by
  have h := bigE_le (k := k) ht
  set D := dimKKT t k + 2
  have h1 : D ^ (2 * D + 2) ≤ (2 ^ D) ^ (2 * D + 2) :=
    Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  rw [← pow_mul] at h1
  have h2 : 0 < 2 ^ (D * (2 * D + 2)) := by positivity
  calc bigE t k ≤ 2 * 2 ^ (D * (2 * D + 2)) := h.trans (by omega)
    _ < 2 ^ (D * (2 * D + 2) + 2) := by rw [pow_add]; omega

theorem clog_le_self (x : ℕ) : Nat.clog 2 x ≤ x :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

/-- **The cost of the constants phase** is `O(D³)`. -/
theorem constCost_le {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) :
    constCost t k ≤ 3000 * (dimKKT t k + 2) ^ 3 := by
  have htd : t ≤ dimKKT t k := by unfold dimKKT; nlinarith
  have hkd := k_le_dimKKT (k := k) ht
  have hnd : nDim t k ≤ dimKKT t k := by
    unfold nDim dimKKT; exact Nat.mul_le_mul_right _ (by omega)
  have hd4 : 4 ≤ dimKKT t k := by unfold dimKKT; nlinarith
  have hE := bigE_lt (k := k) ht
  have hL0 := logRad_le (k := k) ht hk
  set D := dimKKT t k + 2 with hDdef
  set d := dimKKT t k with hd
  set n := nDim t k with hn
  have htD : t ≤ D := by omega
  have hkD : k ≤ D := by omega
  have hnD : n ≤ D := by omega
  have hD6 : 6 ≤ D := by omega
  set X := D * D with hX
  set Y := D * D * D with hY
  have hDX : 6 * D ≤ X := by simp only [hX]; nlinarith
  have hXY : 6 * X ≤ Y := by simp only [hX, hY]; nlinarith
  have hY3 : D ^ 3 = Y := by simp only [hY]; ring
  -- the small multipliers
  have mt := mulCost_le t
  have md := mulCost_le d
  have mk2 := mulCost_le (k - 2)
  have mk1 := mulCost_le (k - 1)
  have mn := mulCost_le n
  have mn1 := mulCost_le (n + 1)
  have mdd := mulCost_le (d * d + 1)
  have hdd : d * d ≤ X := Nat.mul_le_mul (by omega) (by omega)
  -- `E` and `E²`
  have mE := mulCost_le_of hE
  have hEE : bigE t k * bigE t k < 2 ^ (D * (2 * D + 2) + 2 + (D * (2 * D + 2) + 2)) := by
    have := Nat.mul_lt_mul'' hE hE
    rwa [← pow_add] at this
  have mEE := mulCost_le_of hEE
  have hsE : D * (2 * D + 2) + 2 = 2 * X + 2 * D + 2 := by simp only [hX]; ring
  -- `C₀`
  have hC : curv t k ≤ 2 * Y := by
    simp only [curv, hY]
    have : (k - 2) * t ^ 2 ≤ D * D * D := by
      rw [pow_two, ← Nat.mul_assoc]
      exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) htD) htD
    rw [Nat.mul_assoc]; omega
  have mC := (mulCost_le (curv t k)).trans (show 31 * curv t k + 22 ≤ 31 * (2 * Y) + 22 by omega)
  -- `L`
  have hL : logRad t k ≤ 8 * X + 22 * D := by
    have h1 := hL0
    have h2 : (8 * D + 22) * Nat.clog 2 D ≤ (8 * D + 22) * D :=
      Nat.mul_le_mul_left _ (clog_le_self D)
    have h3 : (8 * D + 22) * D = 8 * X + 22 * D := by simp only [hX]; ring
    omega
  have mL := mulCost_le (logRad t k)
  have hcl1 := clog_le_self (n + 1)
  -- `32 n (n + 1)`
  have hA : 32 * n * (n + 1) ≤ 32 * X + 32 * D := by
    have : n * (n + 1) ≤ D * (D + 1) := Nat.mul_le_mul hnD (by omega)
    have e : D * (D + 1) = X + D := by simp only [hX]; ring
    rw [Nat.mul_assoc]; omega
  have mA := mulCost_le (32 * n * (n + 1))
  have mA1 := mulCost_le (32 * n * (n + 1) + 1)
  -- the two loops of stage 2
  have hf : d * (2 + Arith.mulCost d + 4) ≤ 31 * X + 28 * D := by
    have : d * (2 + Arith.mulCost d + 4) ≤ D * (31 * D + 28) := Nat.mul_le_mul (by omega) (by omega)
    have e : D * (31 * D + 28) = 31 * X + 28 * D := by simp only [hX]; ring
    omega
  have hp : (d + 1) * (Arith.mulCost (k - 2) + 4) ≤ 31 * X + 26 * D := by
    have : (d + 1) * (Arith.mulCost (k - 2) + 4) ≤ D * (31 * D + 26) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : D * (31 * D + 26) = 31 * X + 26 * D := by simp only [hX]; ring
    omega
  have hclR : clogCost (radInv t k) = 4 + 5 * logRad t k := by
    unfold clogCost logRad; ring
  have hcl : clogCost (n + 1) = 4 + 5 * Nat.clog 2 (n + 1) := by unfold clogCost; ring
  rw [hY3]
  simp only [constCost, cost1, cost2, cost3, cost4, cost5, cost6, ← hd, ← hn, hclR, hcl]
  omega

end STACS2027.Runtimes.QPRam.Parse
