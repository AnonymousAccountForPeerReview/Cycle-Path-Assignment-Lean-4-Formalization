module

public import Runtimes.ConvexQP.RAM.EllUpd3
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: bit lengths

With `p = prec t k` (`prec_eq`: `p = 64 (n+1) L + 3 ⌈log₂(n+1)⌉ + 15`, `L = ⌈log₂(n/r_K)⌉ ≥ 1`),
every polynomial in `n` of degree at most 9 with small coefficients is at most `2^p`
(`poly_le`), and `E ≤ 2^p` (`bigE_le_pow`). With the magnitudes of `EllMag.lean`
(`ellIter_state_bounds`, `feas_bounds`, `cut_bound`, `update_bounds`) all numbers of an iteration
have at most `bitB = 8p + 8` bits (`updBits_of`, `xs_bits`, `bigE_bits`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-- The bit bound of an iteration. -/
def bitB (t k : ℕ) : ℕ := 8 * prec t k + 8

/-- The scratch allowance of Phase E above its free address `Ly.F`: the largest table of the
arithmetic library in an iteration (the rank-one update, `16 B + 6` cells for `B = bitB`). -/
def ellSc (t k : ℕ) : ℕ := 16 * bitB t k + 6

/-! ### The constants -/

theorem radInv_ge_two {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : 2 ≤ radInv t k := by
  have hn := nDim_ge_two ht hk
  have hE := bigE_pos t hk
  unfold radInv curv
  have h1 : 0 < 4 * (2 * (k - 2) * t ^ 2) * bigE t k ^ 4 * (k - 2) ^ 2 * t ^ 2 * (k - 1) := by
    have : 0 < k - 2 := by omega
    have : 0 < k - 1 := by omega
    positivity
  nlinarith

theorem logRad_pos {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : 1 ≤ logRad t k :=
  Nat.clog_pos (by norm_num) (by have := radInv_ge_two ht hk; omega)

theorem prec_ge {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : 64 * (nDim t k + 1) + 15 ≤ prec t k := by
  have hn := nDim_ge_two ht hk
  rw [prec_eq (by omega)]
  have := logRad_pos ht hk
  have : 64 * (nDim t k + 1) * 1 ≤ 64 * (nDim t k + 1) * logRad t k := Nat.mul_le_mul_left _ this
  omega

theorem poly_le {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) :
    2 ^ 20 * (nDim t k + 1) ^ 9 ≤ 2 ^ prec t k := by
  have hp := prec_ge ht hk
  have h1 : (nDim t k + 1) ^ 9 ≤ (2 ^ (nDim t k + 1)) ^ 9 :=
    Nat.pow_le_pow_left Nat.lt_two_pow_self.le 9
  rw [← pow_mul] at h1
  calc 2 ^ 20 * (nDim t k + 1) ^ 9 ≤ 2 ^ 20 * 2 ^ ((nDim t k + 1) * 9) := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (20 + (nDim t k + 1) * 9) := by rw [pow_add]
    _ ≤ 2 ^ prec t k := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem kt_le {t k : ℕ} (hk : 3 ≤ k) : t * k ≤ 2 * nDim t k := by
  unfold nDim
  have : k ≤ 2 * (k - 1) := by omega
  nlinarith

theorem bigE_le_pow {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : bigE t k ≤ 2 ^ prec t k := by
  have hE := bigE_pos t hk
  have h1 : bigE t k ≤ radInv t k := by
    have hn := nDim_ge_two ht hk
    unfold radInv curv
    have h2 : bigE t k ≤ bigE t k ^ 4 := by
      calc bigE t k = bigE t k ^ 1 := (pow_one _).symm
        _ ≤ bigE t k ^ 4 := Nat.pow_le_pow_right hE (by norm_num)
    have h3 : 0 < 4 * (2 * (k - 2) * t ^ 2) := by
      have : 0 < k - 2 := by omega
      positivity
    have h4 : 0 < (k - 2) ^ 2 * t ^ 2 * (k - 1) := by
      have : 0 < k - 2 := by omega
      have : 0 < k - 1 := by omega
      positivity
    calc bigE t k ≤ bigE t k ^ 4 := h2
      _ ≤ 4 * (2 * (k - 2) * t ^ 2) * bigE t k ^ 4 := Nat.le_mul_of_pos_left _ h3
      _ ≤ 4 * (2 * (k - 2) * t ^ 2) * bigE t k ^ 4 * ((k - 2) ^ 2 * t ^ 2 * (k - 1)) :=
          Nat.le_mul_of_pos_right _ h4
      _ = 4 * (2 * (k - 2) * t ^ 2) * bigE t k ^ 4 * (k - 2) ^ 2 * t ^ 2 * (k - 1) := by ring
      _ ≤ nDim t k * (4 * (2 * (k - 2) * t ^ 2) * bigE t k ^ 4 * (k - 2) ^ 2 * t ^ 2 * (k - 1)) :=
          Nat.le_mul_of_pos_left _ (by omega)
  have h2 : radInv t k ≤ 2 ^ logRad t k := Nat.le_pow_clog (by norm_num) _
  have h3 : logRad t k ≤ prec t k := by
    have hn := nDim_ge_two ht hk
    rw [prec_eq (by omega)]
    have : logRad t k ≤ 64 * (nDim t k + 1) * logRad t k :=
      Nat.le_mul_of_pos_left _ (by positivity)
    omega
  exact h1.trans (h2.trans (Nat.pow_le_pow_right (by norm_num) h3))

/-! ### From absolute values to bit lengths -/

theorem abs_le_two_pow {x : ℤ} {C e p : ℕ} (h : |x| ≤ (C : ℤ) * 2 ^ e) (hC : C ≤ 2 ^ p) :
    |x| ≤ 2 ^ (p + e) := by
  have hC' : (C : ℤ) ≤ 2 ^ p := by exact_mod_cast hC
  calc |x| ≤ (C : ℤ) * 2 ^ e := h
    _ ≤ 2 ^ p * 2 ^ e := mul_le_mul_of_nonneg_right hC' (by positivity)
    _ = 2 ^ (p + e) := by rw [pow_add]

theorem flatR_bits {I : Inst} (y : Idx I → ℤ) (e : ℕ) (h : ∀ i, |y i| ≤ 2 ^ e) (j : ℕ) :
    Nat.size (flatR y j).natAbs ≤ e + 1 := by
  by_cases hj : j < I.t * (I.k - 1)
  · obtain ⟨c, j', rfl⟩ := flat_decomp hj
    rw [flatR_apply]
    exact size_le_of_abs_le (h _)
  · rw [show flatR y j = 0 from flat_of_ge _ (by omega)]
    simp

theorem flatM_bits {I : Inst} (Q : Matrix (Idx I) (Idx I) ℤ) (e : ℕ) (h : ∀ i i', |Q i i'| ≤ 2 ^ e)
    (a b : ℕ) : Nat.size (flatM Q a b).natAbs ≤ e + 1 := by
  by_cases ha : a < I.t * (I.k - 1)
  · obtain ⟨c, j', rfl⟩ := flat_decomp ha
    rw [flatM_apply]
    exact flatR_bits _ e (h _) b
  · rw [show flatM Q a b = 0 from flat_of_ge _ (by omega)]
    simp

/-! ### The numbers of an iteration -/

theorem two_pow_mul_eq (a b : ℕ) : (2 : ℤ) ^ a * 2 ^ b = 2 ^ (a + b) := (pow_add 2 a b).symm

theorem four_pow (p : ℕ) : (4 : ℤ) ^ p = 2 ^ (2 * p) := by rw [pow_mul]; norm_num
theorem eight_pow (p : ℕ) : (8 : ℤ) ^ p = 2 ^ (3 * p) := by rw [pow_mul]; norm_num
theorem sixteen_pow (p : ℕ) : (16 : ℤ) ^ p = 2 ^ (4 * p) := by rw [pow_mul]; norm_num

/-- The bit lengths of the update at an iteration `i < N` that cuts along `g`. -/
theorem updBits_of {I : Inst} (hI : I.Valid) (ht : 0 < I.t) {i : ℕ} (hi : i < iters I.t I.k)
    {st : EllState I} (h : ellIter I (consts I.t I.k) i = .inl st) {g : Idx I → ℤ}
    (hg : ellCut I (consts I.t I.k) st.As = .inl g) :
    UpdBits I st g (bitB I.t I.k) := by
  have hk := hI.1
  obtain ⟨-, hQ, -⟩ := ellIter_state_bounds hI ht hi.le h
  obtain ⟨hu, hG0, hG, -, -⟩ := update_bounds hI ht hi h hg
  have hgb := cut_bound hI ht hg
  have hpoly := poly_le ht hk
  have hkt := kt_le (t := I.t) hk
  have hn2 := nDim_ge_two ht hk
  have hcNd : cNum I.t I.k = nDim I.t I.k ^ 2 * (32 * nDim I.t I.k * (nDim I.t I.k + 1) + 1) ^ 3 :=
    rfl
  change ∀ i, |g i| ≤ ((I.k - 2 : ℕ) : ℤ) * I.t * 2 ^ prec I.t I.k at hgb
  set p := prec I.t I.k with hp
  set n := nDim I.t I.k with hn
  clear_value p n
  have hBd : bitB I.t I.k = 8 * p + 8 := by rw [hp]; rfl
  -- polynomial factors
  have hP : ∀ x : ℕ, x ≤ 2 ^ 20 * (n + 1) ^ 9 → x ≤ 2 ^ p := fun x hx => hx.trans hpoly
  have hk2t : (I.k - 2) * I.t ≤ 2 * n := by
    have : (I.k - 2) * I.t ≤ I.t * I.k := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hn9 : ∀ x : ℕ, x ≤ 2 * (n + 1) ^ 9 → x ≤ 2 ^ p := fun x hx => hP x (hx.trans
    (Nat.mul_le_mul_right _ (by norm_num)))
  have hpow : ∀ a b : ℕ, a ≤ b → (n + 1) ^ a ≤ (n + 1) ^ b := fun a b hab =>
    Nat.pow_le_pow_right (by omega) hab
  -- `G`
  have hGabs : |updG I st g| ≤ 2 ^ (p + 4 * p) := by
    refine abs_le_two_pow (C := n ^ 3 * (I.k - 2) ^ 2 * I.t ^ 2) ?_ (hP _ ?_)
    · rw [abs_of_pos hG0, ← sixteen_pow]; push_cast; exact hG
    · have h1 : n ^ 3 * (I.k - 2) ^ 2 * I.t ^ 2 = n ^ 3 * ((I.k - 2) * I.t) ^ 2 := by ring
      have h2 : ((I.k - 2) * I.t) ^ 2 ≤ (2 * n) ^ 2 := Nat.pow_le_pow_left hk2t 2
      have h3 : n ^ 3 * (2 * n) ^ 2 = 4 * n ^ 5 := by ring
      have h4 : n ^ 5 ≤ (n + 1) ^ 9 :=
        (Nat.pow_le_pow_left (by omega) 5).trans (hpow 5 9 (by norm_num))
      have h5 : n ^ 3 * ((I.k - 2) * I.t) ^ 2 ≤ n ^ 3 * (2 * n) ^ 2 := Nat.mul_le_mul_left _ h2
      omega
  -- `cN`
  have hcN : 2 * cNum I.t I.k * (n + 1) ≤ 2 ^ p := by
    refine hP _ ?_
    rw [hcNd]
    have h1 : 32 * n * (n + 1) + 1 ≤ 33 * (n + 1) ^ 2 := by nlinarith
    have h2 : (32 * n * (n + 1) + 1) ^ 3 ≤ (33 * (n + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
    have h3 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : 2 * (n ^ 2 * (32 * n * (n + 1) + 1) ^ 3) * (n + 1) ≤
        2 * ((n + 1) ^ 2 * (33 * (n + 1) ^ 2) ^ 3) * (n + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul h3 h2))
    have h5 : 2 * ((n + 1) ^ 2 * (33 * (n + 1) ^ 2) ^ 3) * (n + 1) = 71874 * (n + 1) ^ 9 := by
      ring
    have h6 : 71874 * (n + 1) ^ 9 ≤ 2 ^ 20 * (n + 1) ^ 9 := Nat.mul_le_mul_right _ (by norm_num)
    omega
  have hcN1 : cNum I.t I.k * (n + 1) ≤ 2 ^ p := by
    have : cNum I.t I.k * (n + 1) ≤ 2 * cNum I.t I.k * (n + 1) := by
      rw [Nat.mul_assoc 2]; omega
    omega
  have hcN2 : cNum I.t I.k + cNum I.t I.k ≤ 2 ^ p := by
    have : cNum I.t I.k * 1 ≤ cNum I.t I.k * (n + 1) := Nat.mul_le_mul_left _ (by omega)
    have : 2 * cNum I.t I.k * (n + 1) = 2 * (cNum I.t I.k * (n + 1)) := by ring
    omega
  refine ⟨by rw [hBd]; omega, by rw [hBd, ← hp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hBd] <;> try simp only [← hn, ← hp]
  · -- `g`
    intro j _
    have hC : (I.k - 2) * I.t ≤ 2 ^ p := hn9 _ (by
      have := hpow 1 9 (by norm_num); simp only [pow_one] at this; omega)
    have := flatR_bits g (p + p) (fun i => abs_le_two_pow (C := (I.k - 2) * I.t)
      (by push_cast; exact hgb i) hC) j
    omega
  · -- `u`
    intro j _
    have hC : n ^ 2 * (I.k - 2) * I.t ≤ 2 ^ p := hn9 _ (by
      have h1 : n ^ 2 * (I.k - 2) * I.t ≤ n ^ 2 * (2 * n) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hk2t
      have h2 : n ^ 2 * (2 * n) ≤ 2 * (n + 1) ^ 3 := by
        have : n ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        nlinarith
      have h3 := hpow 3 9 (by norm_num)
      omega)
    have := flatR_bits (updU I st g) (p + 3 * p) (fun a => abs_le_two_pow
      (C := n ^ 2 * (I.k - 2) * I.t) (by push_cast; rw [← eight_pow]; exact hu a) hC) j
    omega
  · -- `Qs`
    intro a _ b _
    have hC : n ≤ 2 ^ p := hn9 _ (by
      have := hpow 1 9 (by norm_num); simp only [pow_one] at this; omega)
    have := flatM_bits st.Qs (p + 2 * p) (fun a b => abs_le_two_pow (C := n)
      (by rw [← four_pow]; exact hQ a b) hC) a b
    omega
  · -- `G`
    have := size_le_of_abs_le (hGabs)
    omega
  · -- `α`
    have := size_le_of_abs_le (z := (cNum I.t I.k : ℤ) * ((n + 1 : ℕ) : ℤ) * updG I st g)
      (e := p + (p + 4 * p)) (by
        rw [abs_mul, show |((cNum I.t I.k : ℤ) * ((n + 1 : ℕ) : ℤ))| =
          ((cNum I.t I.k * (n + 1) : ℕ) : ℤ) by push_cast; rw [abs_of_nonneg (by positivity)]]
        have hc : ((cNum I.t I.k * (n + 1) : ℕ) : ℤ) ≤ 2 ^ p := by exact_mod_cast hcN1
        calc ((cNum I.t I.k * (n + 1) : ℕ) : ℤ) * |updG I st g|
            ≤ 2 ^ p * 2 ^ (p + 4 * p) := mul_le_mul hc hGabs (abs_nonneg _) (by positivity)
          _ = 2 ^ (p + (p + 4 * p)) := by rw [← pow_add])
    omega
  · -- `β`
    have := size_le_of_le_pow (x := (-((cNum I.t I.k : ℤ) + cNum I.t I.k)).natAbs) (e := p)
      (by rw [Int.natAbs_neg]; omega)
    omega
  · -- `n + 1`
    have := size_le_of_le_pow (x := n + 1) (e := p) (hP _ (by
      have := hpow 1 9 (by norm_num); simp only [pow_one] at this; omega))
    omega
  · -- `G 2^{3p}`
    have hGn : (updG I st g).toNat ≤ 2 ^ (5 * p) := by
      have h1 : ((updG I st g).toNat : ℤ) = updG I st g := Int.toNat_of_nonneg hG0.le
      have h2 := hGabs
      rw [abs_of_pos hG0, ← h1] at h2
      have : p + 4 * p = 5 * p := by ring
      rw [this] at h2
      exact_mod_cast h2
    have : (updG I st g).toNat * 2 ^ (3 * p) ≤ 2 ^ (8 * p) := by
      calc (updG I st g).toNat * 2 ^ (3 * p) ≤ 2 ^ (5 * p) * 2 ^ (3 * p) :=
            Nat.mul_le_mul_right _ hGn
        _ = 2 ^ (8 * p) := by rw [← pow_add]; ring_nf
    have := size_le_of_le_pow this
    omega

/-! ### The numbers of E2 -/

theorem flat_bits {t k : ℕ} (X : Fin t → Fin k → ℤ) (e : ℕ) (h : ∀ c j, |X c j| ≤ 2 ^ e)
    (b : ℕ) : Nat.size (flat X b).natAbs ≤ e + 1 := by
  by_cases hb : b < t * k
  · obtain ⟨c, j, rfl⟩ := flat_decomp hb
    rw [flat_apply]
    exact size_le_of_abs_le (h c j)
  · rw [flat_of_ge X (by omega)]
    simp

/-- The completion of a feasible center has entries of at most `p + 1` bits. -/
theorem xs_bits {I : Inst} (hI : I.Valid) {p : ℕ} {As : Idx I → ℤ} (hneg : ∀ i, 0 ≤ As i)
    (hblk : ∀ c, blockSum I As c ≤ 2 ^ p) (b : ℕ) :
    Nat.size (flat (feasPt I p As) b).natAbs ≤ p + 1 := by
  obtain ⟨hX, -⟩ := feas_bounds hI hneg hblk
  refine flat_bits _ p (fun c j => abs_le.mpr ⟨?_, (hX c j).2⟩) b
  have h1 := (hX c j).1
  have h2 : (0 : ℤ) ≤ 2 ^ p := by positivity
  linarith

theorem bigE_bits {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : Nat.size (bigE t k) ≤ prec t k + 1 :=
  size_le_of_le_pow (bigE_le_pow ht hk)

end STACS2027.Runtimes.QPRam
