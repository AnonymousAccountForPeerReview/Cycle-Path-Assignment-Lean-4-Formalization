module

public import Runtimes.ConvexQP.RAM.KmoBits
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: the polynomial step bound

With `X = t k + 2`: `d ≤ 2X`, `M ≤ 5X`, `k, t ≤ X`, `p ≤ 4882 X³` (`prec_le_X`, from `prec_eq`,
`logRad_le`), hence `bitM ≤ 40000 X⁴` (`bitM_le`). A step of Phase M costs
`Tstep d M B ≤ 2·10⁸ X⁶` (`tstep_le`), Phase M (`d` steps) at most `5·10⁸ X⁷` (`phaseM_le`),
Phase K at most `2·10⁵ X⁵` (`TK_le`), Phase O at most `1000 X²` (`TO_le`); in total
`kmoC · X^10` (`kmo_total_le`). Space: the layout and the scratch tables of the arithmetic fit in
`kmoC · X^10` cells above the initial free address (`kmoSpace_le`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {I : Inst}

/-- The sizes in terms of `X = t k + 2`. -/
theorem kmo_sizes (ht : 0 < I.t) (hk : 3 ≤ I.k) :
    I.t ≤ I.t * I.k + 2 ∧ I.k ≤ I.t * I.k + 2 ∧ dd I ≤ 2 * (I.t * I.k + 2) ∧
      MM I ≤ 5 * (I.t * I.k + 2) := by
  have h1 : I.t ≤ I.t * I.k := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : I.k ≤ I.t * I.k := Nat.le_mul_of_pos_left _ ht
  have hd : dd I = I.t * I.k + I.t := dimKKT_eq I.t I.k
  have hM : MM I = 2 * I.t + 3 * (I.t * I.k) := nRows_eq I.t I.k
  omega

theorem pow_le_pow_X {X : ℕ} (hX : 1 ≤ X) {a b : ℕ} (h : a ≤ b) : X ^ a ≤ X ^ b :=
  Nat.pow_le_pow_right hX h

/-- **The bit bound of Phase M** is `O(X⁴)`. -/
theorem bitM_le (ht : 0 < I.t) (hk : 3 ≤ I.k) : bitM I ≤ 40000 * (I.t * I.k + 2) ^ 4 := by
  obtain ⟨-, hkX, hdX, -⟩ := kmo_sizes ht hk
  have hp := prec_le_X ht hk
  set X := I.t * I.k + 2 with hXdef
  have hX : 1 ≤ X := by omega
  have e1 : eD I ≤ 6 * X ^ 2 := by
    have h1 : dd I * dd I ≤ (2 * X) * (2 * X) := Nat.mul_le_mul hdX hdX
    have h2 : I.k * dd I ≤ X * (2 * X) := Nat.mul_le_mul hkX hdX
    have : (2 * X) * (2 * X) + X * (2 * X) = 6 * X ^ 2 := by ring
    unfold eD; omega
  have e2 : eQ I ≤ 15000 * X ^ 4 := by
    have h1 : (prec I.t I.k + eD I) * dd I ≤ (4882 * X ^ 3 + 6 * X ^ 2) * (2 * X) :=
      Nat.mul_le_mul (by omega) hdX
    have h2 : (4882 * X ^ 3 + 6 * X ^ 2) * (2 * X) = 9764 * X ^ 4 + 12 * X ^ 3 := by ring
    have h3 : X ^ 3 ≤ X ^ 4 := pow_le_pow_X hX (by norm_num)
    unfold eQ; omega
  have h3 : X ^ 3 ≤ X ^ 4 := pow_le_pow_X hX (by norm_num)
  have h2 : X ^ 2 ≤ X ^ 4 := pow_le_pow_X hX (by norm_num)
  have h1 : X ^ 1 ≤ X ^ 4 := pow_le_pow_X hX (by norm_num)
  have h0 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ (by omega)
  rw [pow_one] at h1
  unfold bitM eZ eU
  omega

/-- **One step of Phase M** costs `O(X⁶)`. -/
theorem tstep_le (ht : 0 < I.t) (hk : 3 ≤ I.k) :
    Tstep (dd I) (MM I) (bitM I) ≤ 200000000 * (I.t * I.k + 2) ^ 6 := by
  obtain ⟨-, -, hdX, hMX⟩ := kmo_sizes ht hk
  have hB := bitM_le ht hk
  set X := I.t * I.k + 2 with hXdef
  have hX : 1 ≤ X := by omega
  have h1 : Tstep (dd I) (MM I) (bitM I) ≤ Tstep (2 * X) (5 * X) (40000 * X ^ 4) := by
    unfold Tstep; gcongr
  refine h1.trans ?_
  have q5 : X ^ 5 ≤ X ^ 6 := pow_le_pow_X hX (by norm_num)
  have q4 : X ^ 4 ≤ X ^ 6 := pow_le_pow_X hX (by norm_num)
  have q3 : X ^ 3 ≤ X ^ 6 := pow_le_pow_X hX (by norm_num)
  have q2 : X ^ 2 ≤ X ^ 6 := pow_le_pow_X hX (by norm_num)
  have q1 : X ^ 1 ≤ X ^ 6 := pow_le_pow_X hX (by norm_num)
  have q0 : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ (by omega)
  rw [pow_one] at q1
  unfold Tstep
  ring_nf
  omega

/-- **Phase M** (`d` steps) costs `O(X⁷)`. -/
theorem phaseM_le (ht : 0 < I.t) (hk : 3 ≤ I.k) :
    dd I * (Tstep (dd I) (MM I) (bitM I) + 4) + 3 ≤ 500000000 * (I.t * I.k + 2) ^ 7 := by
  obtain ⟨-, -, hdX, -⟩ := kmo_sizes ht hk
  have hT := tstep_le ht hk
  set X := I.t * I.k + 2 with hXdef
  have hX : 1 ≤ X := by omega
  have h1 : dd I * (Tstep (dd I) (MM I) (bitM I) + 4) ≤ (2 * X) * (200000000 * X ^ 6 + 4) :=
    Nat.mul_le_mul hdX (by omega)
  have h2 : (2 * X) * (200000000 * X ^ 6 + 4) = 400000000 * X ^ 7 + 8 * X := by ring
  have q1 : X ^ 1 ≤ X ^ 7 := pow_le_pow_X hX (by norm_num)
  have q0 : 1 ≤ X ^ 7 := Nat.one_le_pow _ _ (by omega)
  rw [pow_one] at q1
  omega

/-- **Phase K** costs `O(X⁵)`. -/
theorem TK_le (ht : 0 < I.t) (hk : 3 ≤ I.k) :
    TK I (prec I.t I.k + 1) ≤ 200000 * (I.t * I.k + 2) ^ 5 := by
  obtain ⟨htX, hkX, hdX, -⟩ := kmo_sizes ht hk
  have hp := prec_le_X ht hk
  set X := I.t * I.k + 2 with hXdef
  have hX : 1 ≤ X := by omega
  have htk : I.t * I.k ≤ X := by omega
  have h1 : TK I (prec I.t I.k + 1) ≤
      (5 * (2 * (2 * X) + 2) + 5 * (2 * (2 * X)) + 50 + 6 + (9 + (X * 27 + 3)) +
        (17 + (X * (X * (31 * (4882 * X ^ 3 + 1) + 87) + 19) + 1))) +
      ((X * (X * 38 + 17) + 7) + ((90 + (X * (X * 54 + 47 + 4) + 3)) +
      ((8 + (X * (X * (77 + (X * 54 + 66 + 1) + 5 + 4) + 3 + 2 + 4) + 3)) +
      (2 + (4 * (4882 * X ^ 3) + 6) + 3)))) := by
    unfold TK gsz asz; gcongr
  refine h1.trans ?_
  have q4 : X ^ 4 ≤ X ^ 5 := pow_le_pow_X hX (by norm_num)
  have q3 : X ^ 3 ≤ X ^ 5 := pow_le_pow_X hX (by norm_num)
  have q2 : X ^ 2 ≤ X ^ 5 := pow_le_pow_X hX (by norm_num)
  have q1 : X ^ 1 ≤ X ^ 5 := pow_le_pow_X hX (by norm_num)
  have q0 : 1 ≤ X ^ 5 := Nat.one_le_pow _ _ (by omega)
  rw [pow_one] at q1
  ring_nf
  omega

/-- **Phase O** costs `O(X²)`. -/
theorem TO_le (ht : 0 < I.t) (hk : 3 ≤ I.k) :
    TO (dd I) (I.t * I.k) ≤ 1000 * (I.t * I.k + 2) ^ 2 := by
  obtain ⟨-, -, hdX, -⟩ := kmo_sizes ht hk
  set X := I.t * I.k + 2 with hXdef
  have hX : 1 ≤ X := by omega
  have htk : I.t * I.k ≤ X := by omega
  have h1 : TO (dd I) (I.t * I.k) ≤ TO (2 * X) X := by unfold TO; gcongr
  refine h1.trans ?_
  have q1 : X ^ 1 ≤ X ^ 2 := pow_le_pow_X hX (by norm_num)
  have q0 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [pow_one] at q1
  unfold TO
  ring_nf
  omega

/-- The constant of the step bound of Phases K, M, O. -/
def kmoC : ℕ := 500000000 + 200000 + 1000

/-- **The step bound of Phases K, M, O**: `kmoC · (t k + 2)^10`. -/
theorem kmo_total_le (ht : 0 < I.t) (hk : 3 ≤ I.k) :
    TK I (prec I.t I.k + 1) + ((dd I * (Tstep (dd I) (MM I) (bitM I) + 4) + 3) +
      TO (dd I) (I.t * I.k)) ≤ kmoC * (I.t * I.k + 2) ^ 10 := by
  have h1 := TK_le ht hk
  have h2 := phaseM_le ht hk
  have h3 := TO_le ht hk
  set X := I.t * I.k + 2 with hXdef
  have hX : 1 ≤ X := by omega
  have q7 : X ^ 7 ≤ X ^ 10 := pow_le_pow_X hX (by norm_num)
  have q5 : X ^ 5 ≤ X ^ 10 := pow_le_pow_X hX (by norm_num)
  have q2 : X ^ 2 ≤ X ^ 10 := pow_le_pow_X hX (by norm_num)
  unfold kmoC
  omega

/-- **The space of Phases K, M, O**: the layout `lay I F₀` above the initial free address `F₀`
(`O(X²)` cells) and the scratch tables of the arithmetic above its end `fe` (at most
`16 · bitM + 6` cells, the largest being the rank-one update's) fit in `kmoC · X^10` cells. -/
theorem kmoSpace_le (ht : 0 < I.t) (hk : 3 ≤ I.k) (F₀ : ℕ) :
    (lay I F₀).fe + 16 * bitM I + 6 ≤ F₀ + kmoC * (I.t * I.k + 2) ^ 10 := by
  obtain ⟨-, -, hdX, hMX⟩ := kmo_sizes ht hk
  have hB := bitM_le ht hk
  have hfe : (lay I F₀).fe = F₀ + MM I * gsz I + dd I * asz I + 5 * asz I + 6 * MM I + dd I +
      2 * (I.t * I.k) + 2 := rfl
  have hgs : gsz I = 2 * dd I + 2 := rfl
  have has : asz I = 2 * dd I := rfl
  set X := I.t * I.k + 2 with hXdef
  have hX : 1 ≤ X := by omega
  have h1 : MM I * gsz I ≤ (5 * X) * (2 * (2 * X) + 2) := Nat.mul_le_mul hMX (by omega)
  have h2 : dd I * asz I ≤ (2 * X) * (2 * (2 * X)) := Nat.mul_le_mul hdX (by omega)
  have e1 : (5 * X) * (2 * (2 * X) + 2) = 20 * X ^ 2 + 10 * X := by ring
  have e2 : (2 * X) * (2 * (2 * X)) = 8 * X ^ 2 := by ring
  have q4 : X ^ 4 ≤ X ^ 10 := pow_le_pow_X hX (by norm_num)
  have q2 : X ^ 2 ≤ X ^ 10 := pow_le_pow_X hX (by norm_num)
  have q1 : X ^ 1 ≤ X ^ 10 := pow_le_pow_X hX (by norm_num)
  have q0 : 1 ≤ X ^ 10 := Nat.one_le_pow _ _ (by omega)
  rw [pow_one] at q1
  unfold kmoC
  omega

/-- The scratch of Phase K (`L = H Xs`, `2 (p + 1)` cells) is within that of Phase M. -/
theorem kScratch_le (I : Inst) : 2 * (prec I.t I.k + 1) ≤ 16 * bitM I + 6 := by
  unfold bitM; omega

end STACS2027.Runtimes.QPRam.Kmo
