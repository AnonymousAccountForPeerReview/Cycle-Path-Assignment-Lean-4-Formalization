module

public import Runtimes.ConvexQP.EllSuccess
import Mathlib.Tactic

/-!
# Lemma 16, Phase E: magnitudes of the integers

Bounds on every integer that Phase E computes, for the step count of the RAM implementation
(`n = (k−1)t`, `N`, `p` as in `consts t k`; a valid instance with `t ≥ 1`):

* **States** (`ellIter_state_bounds`): every state reached within `N` iterations has a symmetric
  `Qs` with `|Qs_{ij}| ≤ n·4^p` and a center with `|As_i| ≤ (N+1)(n+2)·4^p`
  (from B9's Loewner upper bound `Q ⪯ (n/4)((1+η)⁴κ)^i I` and `((1+η)⁴κ)^N ≤ 2^p`).
* **Feasible centers** (`feas_bounds`): `0 ≤ Xs_{c,j} ≤ 2^p`, `0 ≤ λ(Xs)_e ≤ t·2^p`,
  `0 ≤ L(Xs)_{c,j} ≤ (k−2)t·2^p` and `0 ≤ GAP = gap(Xs) ≤ (k−2)t²·4^p`.
* **The output** (`ellRun_output_bounds`): `0 ≤ Xs_{c,j} ≤ 2^p`, `0 ≤ gap(Xs) ≤ (k−2)t²·4^p`.
* **Cuts** (`cut_bound`): `|g_i| ≤ (k−2)t·2^p`.
* **Update** (`update_bounds`, at an iteration `i < N` that cuts): `|u_i| ≤ n²(k−2)t·8^p`,
  `0 < G ≤ n³(k−2)²t²·16^p`, `1 ≤ S` and `S² ≤ G·8^p`.

* **Constants** (`bigE_le`, `logRad_le`, `iters_eq`, `prec_eq`): with `D = (k+1)t + 2`,
  `E ≤ 2D^{2D+2}`, `⌈log₂(n/r_K)⌉ ≤ (8D+24)⌈log₂ D⌉`, `N = 16n(n+1)L + 1` and
  `p = 64(n+1)L + 3⌈log₂(n+1)⌉ + 15` for `L = ⌈log₂(n/r_K)⌉` (so `N = O(D³ log D)` and
  `p = O(D² log D)`).

All Phase E integers therefore have `O(p + log(nkt))` bits; the RAM analysis bounds the
numerators and denominators of E4 by products of these.
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Matrix Finset

variable {I : Inst}

/-! ### Feasible centers -/

theorem L_nonneg_of_inX {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) (c : Fin I.t) (j : Fin I.k) :
    0 ≤ I.L x c j :=
  Finset.sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) (Inst.lam_nonneg hx.1 e)

theorem L_le_of_inX (hI : I.Valid) {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) (c : Fin I.t)
    (j : Fin I.k) : I.L x c j ≤ ((I.k - 2 : ℕ) : ℝ) * I.t := by
  unfold Inst.L
  calc ∑ e, (I.cnt c j e : ℝ) * I.lam x e ≤ ∑ e, (I.cnt c j e : ℝ) * I.t :=
        Finset.sum_le_sum fun e _ =>
          mul_le_mul_of_nonneg_left (Inst.lam_le_t hI hx e) (Nat.cast_nonneg _)
    _ = ((I.k - 2 : ℕ) : ℝ) * I.t := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Inst.sum_cnt_valid hI c j

theorem gap_le_of_inX (hI : I.Valid) {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) :
    I.gap x ≤ ((I.k - 2 : ℕ) : ℝ) * I.t ^ 2 := by
  have hk : 0 < I.k := by have := hI.1; omega
  unfold Inst.gap
  calc ∑ c, ∑ j, x c j * (I.L x c j - I.pi x c)
      ≤ ∑ c, ∑ j, x c j * (((I.k - 2 : ℕ) : ℝ) * I.t) := by
        refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (hx.1 c j)
        obtain ⟨j', hj'⟩ := I.exists_L_eq_pi x c hk
        have := L_nonneg_of_inX hx c j'
        have := L_le_of_inX hI hx c j
        linarith
    _ = ((I.k - 2 : ℕ) : ℝ) * I.t ^ 2 := by
        simp only [← Finset.sum_mul, hx.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

/-- **Magnitudes at a feasible center** (E2): `0 ≤ Xs ≤ 2^p`, `0 ≤ λ(Xs) ≤ t·2^p`,
`0 ≤ L(Xs) ≤ (k−2)t·2^p`, `0 ≤ GAP ≤ (k−2)t²·4^p`. -/
theorem feas_bounds (hI : I.Valid) {p : ℕ} {As : Idx I → ℤ} (hneg : ∀ i, 0 ≤ As i)
    (hblk : ∀ c, blockSum I As c ≤ 2 ^ p) :
    (∀ c j, 0 ≤ feasPt I p As c j ∧ feasPt I p As c j ≤ 2 ^ p) ∧
    (∀ e, 0 ≤ I.lam (feasPt I p As) e ∧ I.lam (feasPt I p As) e ≤ (I.t : ℤ) * 2 ^ p) ∧
    (∀ c j, 0 ≤ I.L (feasPt I p As) c j ∧
      I.L (feasPt I p As) c j ≤ ((I.k - 2 : ℕ) : ℤ) * I.t * 2 ^ p) ∧
    0 ≤ I.gap (feasPt I p As) ∧ I.gap (feasPt I p As) ≤ ((I.k - 2 : ℕ) : ℤ) * I.t ^ 2 * 4 ^ p := by
  have hk : 0 < I.k := by have := hI.1; omega
  have hP : (0 : ℝ) < 2 ^ p := by positivity
  set Xs := feasPt I p As
  have hx : I.InX (ptOf Xs (2 ^ p)) := by
    rw [ptOf_feasPt]
    exact Inst.xi_inX hk (feas_inY hneg hblk)
  have hxv : ∀ c j, (ptOf Xs (2 ^ p)) c j = (Xs c j : ℝ) / 2 ^ p := fun c j => by
    simp [ptOf]
  refine ⟨fun c j => ?_, fun e => ?_, fun c j => ?_, ?_, ?_⟩
  · have h0 := hx.1 c j
    have h1 : ptOf Xs (2 ^ p) c j ≤ 1 := by
      rw [← hx.2 c]
      exact Finset.single_le_sum (fun j _ => hx.1 c j) (Finset.mem_univ j)
    rw [hxv] at h0 h1
    rw [div_le_one hP] at h1
    constructor
    · have : (0 : ℝ) ≤ Xs c j := by
        by_contra hneg'
        exact absurd h0 (not_le.mpr (div_neg_of_neg_of_pos (lt_of_not_ge hneg') hP))
      exact_mod_cast this
    · exact_mod_cast h1
  · have h1 := Inst.lam_le_t hI hx e
    have h0 := Inst.lam_nonneg hx.1 e
    have e1 : I.lam (ptOf Xs (2 ^ p)) e = ((I.lam Xs e : ℤ) : ℝ) / 2 ^ p := by
      unfold ptOf; push_cast; exact I.lam_div Xs _ e
    rw [e1] at h0 h1
    rw [div_le_iff₀ hP] at h1
    constructor
    · exact_mod_cast (div_nonneg_iff.mp h0).elim (fun h => h.1) (fun h => by linarith [h.2])
    · exact_mod_cast h1
  · have h1 := L_le_of_inX hI hx c j
    have h0 := L_nonneg_of_inX hx c j
    have e1 : I.L (ptOf Xs (2 ^ p)) c j = ((I.L Xs c j : ℤ) : ℝ) / 2 ^ p := by
      unfold ptOf; push_cast; exact I.L_div Xs _ c j
    rw [e1] at h0 h1
    rw [div_le_iff₀ hP] at h1
    constructor
    · exact_mod_cast (div_nonneg_iff.mp h0).elim (fun h => h.1) (fun h => by linarith [h.2])
    · exact_mod_cast h1
  · have h0 := Inst.gap_nonneg (I := I) hx.1
    rw [gap_ptOf] at h0
    have h4 : (0 : ℝ) < 4 ^ p := by positivity
    exact_mod_cast (div_nonneg_iff.mp h0).elim (fun h => h.1) (fun h => by linarith [h.2])
  · have h1 := gap_le_of_inX hI hx
    rw [gap_ptOf, div_le_iff₀ (by positivity)] at h1
    exact_mod_cast h1

/-- A successful iteration outputs the completion of a feasible center. -/
theorem ellCut_inr_feas {K : Consts} {As : Idx I → ℤ} {Xs : Fin I.t → Fin I.k → ℤ}
    (h : ellCut I K As = .inr Xs) :
    (∀ i, 0 ≤ As i) ∧ (∀ c, blockSum I As c ≤ 2 ^ K.p) ∧ Xs = feasPt I K.p As := by
  unfold ellCut at h
  split at h
  · exact absurd h (by simp)
  · rename_i hneg
    split at h
    · exact absurd h (by simp)
    · rename_i hover
      split at h
      · exact ⟨firstNeg_none hneg, firstOver_none hover, (Sum.inr.inj h).symm⟩
      · exact absurd h (by simp)

/-- **The output of Phase E** has entries in `[0, 2^p]` (and `0 ≤ GAP ≤ (k−2)t²·4^p`). -/
theorem ellRun_output_bounds (hI : I.Valid) {Xs : Fin I.t → Fin I.k → ℤ}
    (h : ellRun I (consts I.t I.k) = some Xs) :
    (∀ c j, 0 ≤ Xs c j ∧ Xs c j ≤ 2 ^ prec I.t I.k) ∧
      0 ≤ I.gap Xs ∧ I.gap Xs ≤ ((I.k - 2 : ℕ) : ℤ) * I.t ^ 2 * 4 ^ prec I.t I.k := by
  have hN : ellIter I (consts I.t I.k) (consts I.t I.k).N = .inr Xs := by
    unfold ellRun at h
    split at h
    · exact absurd h (by simp)
    · rename_i Xs' hX
      rw [hX, Option.some_inj.mp h]
  obtain ⟨As, hc⟩ := ellIter_inr hN
  obtain ⟨hneg, hblk, rfl⟩ := ellCut_inr_feas hc
  obtain ⟨hX, -, -, hg0, hg1⟩ := feas_bounds hI hneg hblk
  exact ⟨hX, hg0, hg1⟩

/-! ### Cuts -/

/-- **Magnitude of the cut vectors**: `|g_i| ≤ (k−2)t·2^p`. -/
theorem cut_bound (hI : I.Valid) (ht : 0 < I.t) {K : Consts} {As : Idx I → ℤ} {g : Idx I → ℤ}
    (h : ellCut I K As = .inl g) (i : Idx I) :
    |g i| ≤ ((I.k - 2 : ℕ) : ℤ) * I.t * 2 ^ K.p := by
  have hone : (1 : ℤ) ≤ ((I.k - 2 : ℕ) : ℤ) * I.t * 2 ^ K.p := by
    have h1 : (1 : ℤ) ≤ ((I.k - 2 : ℕ) : ℤ) := by exact_mod_cast (by have := hI.1; omega)
    have h2 : (1 : ℤ) ≤ (I.t : ℤ) := by exact_mod_cast ht
    have h3 : (1 : ℤ) ≤ 2 ^ K.p := one_le_pow₀ (by norm_num)
    have := one_le_mul_of_one_le_of_one_le h1 h2
    exact one_le_mul_of_one_le_of_one_le this h3
  unfold ellCut at h
  split at h
  · rename_i j _
    obtain rfl : negCut I j = g := Sum.inl.inj h
    unfold negCut
    split_ifs <;> simp only [abs_neg, abs_one, abs_zero] <;> first | exact hone | positivity
  · rename_i hneg
    split at h
    · rename_i c _
      obtain rfl : blockCut I c = g := Sum.inl.inj h
      unfold blockCut
      split_ifs <;> simp only [abs_one, abs_zero] <;> first | exact hone | positivity
    · rename_i hover
      split at h
      · exact absurd h (by simp)
      · obtain rfl : gradCut I (feasPt I K.p As) = g := Sum.inl.inj h
        obtain ⟨-, -, hL, -⟩ := feas_bounds hI (firstNeg_none hneg) (firstOver_none hover)
        have hk : 0 < I.k := by have := hI.1; omega
        unfold gradCut Inst.gradRed Inst.lastL
        simp only [hk, ↓reduceDIte]
        have h1 := hL i.1 (Fin.castLE (Nat.sub_le _ _) i.2)
        have h2 := hL i.1 ⟨I.k - 1, by omega⟩
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### States -/

theorem sqrt_le_add_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ x + 1 := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- **Magnitudes of the states**: within `N` iterations, `Qs` is symmetric with
`|Qs_{ij}| ≤ n·4^p`, and `|As_i| ≤ (N+1)(n+2)·4^p`. -/
theorem ellIter_state_bounds (hI : I.Valid) (ht : 0 < I.t) {i : ℕ} (hi : i ≤ iters I.t I.k)
    {st : EllState I} (h : ellIter I (consts I.t I.k) i = .inl st) :
    st.Qs.IsSymm ∧ (∀ a b, |st.Qs a b| ≤ (nDim I.t I.k : ℤ) * 4 ^ prec I.t I.k) ∧
      ∀ a, |st.As a| ≤ ((iters I.t I.k : ℤ) + 1) * ((nDim I.t I.k : ℤ) + 2) * 4 ^ prec I.t I.k := by
  have hinv := ellIter_inv hI ht hi h
  have hn := nDim_ge_two ht hI.1
  have hcard := card_idx I
  have hge := hinv.ge
  have hle := hinv.le
  have hctr := hinv.ctr
  have hsymm := hinv.symm
  rw [hcard] at hge hle hctr
  set p := prec I.t I.k with hp
  set n := nDim I.t I.k with hndef
  set N := iters I.t I.k with hN
  have hpN : 4 * ((N + n - 1) / n) ≤ p := by rw [hp, hN, hndef]; unfold prec; omega
  clear_value p n N
  have hP : (0 : ℝ) < 2 ^ p := by positivity
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  -- the Loewner upper bound
  have hu : upperOf n i ≤ n / 4 * 2 ^ p := by
    have h1 : upperOf n i ≤ upperOf n N := by
      unfold upperOf
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact pow_le_pow_right₀ (one_le_growOf hn) hi
    refine h1.trans ?_
    unfold upperOf
    exact mul_le_mul_of_nonneg_left (grow_pow_le hn hpN) (by positivity)
  have hℓ := ellOf_pos (n := n) (by omega) i
  have hpsd := formGe_nonneg hℓ.le hge
  refine ⟨isSymm_of_QR hsymm, fun a b => ?_, fun a => ?_⟩
  · have h1 := abs_entry_le hsymm hpsd hle a b
    simp only [QR, abs_div, abs_of_pos hP] at h1
    rw [div_le_iff₀ hP] at h1
    have h2 : (|st.Qs a b| : ℝ) ≤ n * 4 ^ p := by
      have : (4 : ℝ) ^ p = 2 ^ p * 2 ^ p := by rw [← mul_pow]; norm_num
      rw [this]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) p]
    exact_mod_cast h2
  · have h1 := hctr a
    simp only [aR, abs_div, abs_of_pos hP] at h1
    rw [div_le_iff₀ hP] at h1
    have hu0 : 0 ≤ upperOf n i := by
      unfold upperOf; have := growOf_pos hn; positivity
    have hs : Real.sqrt (upperOf n i) ≤ n / 4 * 2 ^ p + 1 :=
      (sqrt_le_add_one hu0).trans (by linarith)
    have hiN : (i : ℝ) ≤ N := by exact_mod_cast hi
    have h4 : (4 : ℝ) ^ p = 2 ^ p * 2 ^ p := by rw [← mul_pow]; norm_num
    have h2p : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    have hb : (1 / 2 + i * (Real.sqrt (upperOf n i) + 1)) * 2 ^ p ≤
        ((N : ℝ) + 1) * ((n : ℝ) + 2) * 4 ^ p := by
      have h5 : 1 / 2 + (i : ℝ) * (Real.sqrt (upperOf n i) + 1) ≤
          1 / 2 + (N : ℝ) * (n / 4 * 2 ^ p + 2) := by
        have : (i : ℝ) * (Real.sqrt (upperOf n i) + 1) ≤ (N : ℝ) * (n / 4 * 2 ^ p + 2) :=
          mul_le_mul hiN (by linarith) (by positivity) (by positivity)
        linarith
      have h6 : (1 / 2 + (N : ℝ) * (n / 4 * 2 ^ p + 2)) * 2 ^ p ≤
          ((N : ℝ) + 1) * ((n : ℝ) + 2) * 4 ^ p := by
        rw [h4]
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left h2p hN0, mul_nonneg hN0 (by positivity : (0 : ℝ) ≤ n),
          mul_le_mul_of_nonneg_left h2p (mul_nonneg hN0 (by positivity : (0 : ℝ) ≤ 2 ^ p)),
          mul_le_mul_of_nonneg_left h2p (by positivity : (0 : ℝ) ≤ 2 ^ p)]
      exact (mul_le_mul_of_nonneg_right h5 hP.le).trans h6
    have h2 : (|st.As a| : ℝ) ≤ ((N : ℝ) + 1) * ((n : ℝ) + 2) * 4 ^ p := h1.trans hb
    exact_mod_cast h2

/-! ### The update -/

/-- **Magnitudes of the update** (E4) at an iteration `i < N` that cuts along `g`:
`|u_a| ≤ n²(k−2)t·8^p`, `0 < G ≤ n³(k−2)²t²·16^p`, `1 ≤ S`, `S² ≤ G·8^p`. -/
theorem update_bounds (hI : I.Valid) (ht : 0 < I.t) {i : ℕ} (hi : i < iters I.t I.k)
    {st : EllState I} (h : ellIter I (consts I.t I.k) i = .inl st) {g : Idx I → ℤ}
    (hg : ellCut I (consts I.t I.k) st.As = .inl g) :
    (∀ a, |updU I st g a| ≤ (nDim I.t I.k : ℤ) ^ 2 * ((I.k - 2 : ℕ) : ℤ) * I.t *
        8 ^ prec I.t I.k) ∧
      0 < updG I st g ∧
      updG I st g ≤ (nDim I.t I.k : ℤ) ^ 3 * ((I.k - 2 : ℕ) : ℤ) ^ 2 * (I.t : ℤ) ^ 2 *
        16 ^ prec I.t I.k ∧
      1 ≤ updS I (consts I.t I.k) st g ∧
      ((updS I (consts I.t I.k) st g : ℤ)) ^ 2 ≤ updG I st g * 8 ^ prec I.t I.k := by
  obtain ⟨-, hQ, -⟩ := ellIter_state_bounds hI ht hi.le h
  have hgb := cut_bound hI ht hg
  have hKp : (consts I.t I.k).p = prec I.t I.k := rfl
  rw [hKp] at hgb
  have hinv := ellIter_inv hI ht hi.le h
  have hℓ := ellOf_pos (n := Fintype.card (Idx I))
    (by rw [card_idx]; have := nDim_ge_two ht hI.1; omega) i
  have hGpos : 0 < updG I st g := by
    obtain ⟨y0, hy0, hf0⟩ := exists_near_fstar I (delta0_pos ht hI.1)
    have hvalid := ellCut_valid hI ht rfl hg
    have hg0 : gR g ≠ 0 := by
      intro h0
      have := hvalid _ (show (fun i : Idx I => y0 i.1 i.2) ∈ Kset I from ⟨hy0, hf0.le⟩)
      rw [h0, zero_dotProduct] at this
      exact lt_irrefl 0 this
    have hgg := one_le_dot_gR hg0
    have h1 := hinv.ge (gR g)
    have h2 : 0 < qf (QR (prec I.t I.k) st.Qs) (gR g) := by nlinarith
    rw [qf_QR] at h2
    have hP : (0 : ℝ) < 2 ^ prec I.t I.k := by positivity
    have : (0 : ℝ) < (updG I st g : ℝ) := (div_pos_iff_of_pos_right hP).mp h2
    exact_mod_cast this
  have hS : (updS I (consts I.t I.k) st g) = Nat.sqrt ((updG I st g).toNat * 2 ^ (3 * prec I.t I.k)) :=
    rfl
  rw [hS]
  clear hinv hℓ hS hKp h hg
  set p := prec I.t I.k with hp
  set n := nDim I.t I.k with hndef
  clear_value p n
  set B : ℤ := ((I.k - 2 : ℕ) : ℤ) * I.t * 2 ^ p with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hcard : (Finset.univ : Finset (Idx I)).card = n := by
    rw [Finset.card_univ, card_idx, hndef]
  -- `u`
  have hu : ∀ a, |updU I st g a| ≤ (n : ℤ) * ((n : ℤ) * 4 ^ p * B) := by
    intro a
    unfold updU mulVec dotProduct
    calc |∑ b, st.Qs a b * g b| ≤ ∑ b, |st.Qs a b * g b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b : Idx I, (n : ℤ) * 4 ^ p * B := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hQ a b) (hgb b) (abs_nonneg _) (by positivity)
      _ = (n : ℤ) * ((n : ℤ) * 4 ^ p * B) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hu' : ∀ a, |updU I st g a| ≤ (n : ℤ) ^ 2 * ((I.k - 2 : ℕ) : ℤ) * I.t * 8 ^ p := by
    intro a
    refine (hu a).trans (le_of_eq ?_)
    rw [hB, show (8 : ℤ) ^ p = 4 ^ p * 2 ^ p by rw [← mul_pow]; norm_num]
    ring
  refine ⟨hu', hGpos, ?_, ?_, ?_⟩
  · -- `G ≤ n · B · |u|`
    unfold updG dotProduct
    calc ∑ a, g a * updU I st g a ≤ ∑ a, |g a * updU I st g a| :=
          Finset.sum_le_sum fun a _ => le_abs_self _
      _ ≤ ∑ _a : Idx I, B * ((n : ℤ) * ((n : ℤ) * 4 ^ p * B)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hgb a) (hu a) (abs_nonneg _) hB0
      _ = (n : ℤ) * (B * ((n : ℤ) * ((n : ℤ) * 4 ^ p * B))) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ = _ := by
          rw [hB, show (16 : ℤ) ^ p = 4 ^ p * 2 ^ p * 2 ^ p by
            rw [← mul_pow, ← mul_pow]; norm_num]
          ring
  · -- `S ≥ 1`
    apply Nat.sqrt_pos.mpr
    have : 0 < (updG I st g).toNat := by omega
    positivity
  · -- `S² ≤ G · 8^p`
    have h1 := Nat.sqrt_le' ((updG I st g).toNat * 2 ^ (3 * p))
    have h2 : (((updG I st g).toNat * 2 ^ (3 * p) : ℕ) : ℤ) = updG I st g * 8 ^ p := by
      push_cast
      rw [Int.toNat_of_nonneg hGpos.le, pow_mul]
      norm_num
    rw [← h2]
    exact_mod_cast h1

/-! ### Sizes of the constants -/

theorem k_le_dimKKT {t k : ℕ} (ht : 0 < t) : k ≤ dimKKT t k := by
  unfold dimKKT; nlinarith

/-- `E = 2(d²+1)·d!·(k−2)^{d+1} ≤ 2·D^{2D+2}` with `D = d + 2 = (k+1)t + 2`. -/
theorem bigE_le {t k : ℕ} (ht : 0 < t) :
    bigE t k ≤ 2 * (dimKKT t k + 2) ^ (2 * (dimKKT t k + 2) + 2) := by
  unfold bigE entryBound
  have hkd := k_le_dimKKT (k := k) ht
  set d := dimKKT t k
  have h1 : d ^ 2 + 1 ≤ (d + 2) ^ 2 := by nlinarith
  have h2 : d.factorial ≤ (d + 2) ^ (d + 2) :=
    (Nat.factorial_le_pow d).trans ((Nat.pow_le_pow_left (by omega) d).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have h3 : (k - 2) ^ (d + 1) ≤ (d + 2) ^ (d + 2) :=
    (Nat.pow_le_pow_left (by omega) (d + 1)).trans (Nat.pow_le_pow_right (by omega) (by omega))
  calc 2 * (d ^ 2 + 1) * d.factorial * (k - 2) ^ (d + 1)
      ≤ 2 * (d + 2) ^ 2 * (d + 2) ^ (d + 2) * (d + 2) ^ (d + 2) := by
        gcongr
    _ = 2 * (d + 2) ^ (2 * (d + 2) + 2) := by ring

/-- `n / r_K ≤ D^{8D+22}` with `D = (k+1)t + 2`. -/
theorem radInv_le {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) :
    radInv t k ≤ (dimKKT t k + 2) ^ (8 * (dimKKT t k + 2) + 22) := by
  have hkd : k + 1 ≤ dimKKT t k := by unfold dimKKT; nlinarith
  have hE := bigE_le (k := k) ht
  have htd : t ≤ dimKKT t k := by unfold dimKKT; nlinarith
  have hnd : nDim t k ≤ dimKKT t k := by unfold nDim dimKKT; gcongr; omega
  unfold radInv curv
  generalize bigE t k = E at hE ⊢
  generalize nDim t k = n at hnd ⊢
  generalize dimKKT t k = d at hkd hE htd hnd ⊢
  have hD6 : 6 ≤ d + 2 := by omega
  have hE4 : E ^ 4 ≤ (d + 2) ^ (8 * (d + 2) + 10) := by
    calc E ^ 4 ≤ (2 * (d + 2) ^ (2 * (d + 2) + 2)) ^ 4 := Nat.pow_le_pow_left hE 4
      _ = 16 * (d + 2) ^ (8 * (d + 2) + 8) := by ring
      _ ≤ (d + 2) ^ 2 * (d + 2) ^ (8 * (d + 2) + 8) := by
          apply Nat.mul_le_mul_right; nlinarith
      _ = (d + 2) ^ (8 * (d + 2) + 10) := by ring
  have hC : 2 * (k - 2) * t ^ 2 ≤ (d + 2) ^ 4 := by
    calc 2 * (k - 2) * t ^ 2 ≤ (d + 2) * (d + 2) * (d + 2) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.pow_le_pow_left (by omega) 2)
      _ = (d + 2) ^ 4 := by ring
  have h4 : 4 ≤ (d + 2) ^ 2 := by nlinarith
  have hk2 : (k - 2) ^ 2 ≤ (d + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have ht2 : t ^ 2 ≤ (d + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  calc n * (4 * (2 * (k - 2) * t ^ 2) * E ^ 4 * (k - 2) ^ 2 * t ^ 2 * (k - 1))
      ≤ (d + 2) * ((d + 2) ^ 2 * (d + 2) ^ 4 * (d + 2) ^ (8 * (d + 2) + 10) * (d + 2) ^ 2 *
          (d + 2) ^ 2 * (d + 2)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul h4 hC) hE4) hk2) ht2) (by omega))
    _ = (d + 2) ^ (8 * (d + 2) + 22) := by ring

/-- `⌈log₂(n/r_K)⌉ ≤ (8D + 22)⌈log₂ D⌉` with `D = (k+1)t + 2`: the iteration count is
`N = O(n² D log D)`. -/
theorem logRad_le {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) :
    logRad t k ≤ (8 * (dimKKT t k + 2) + 22) * Nat.clog 2 (dimKKT t k + 2) := by
  have h0 := radInv_le ht hk
  unfold logRad
  apply Nat.clog_le_of_le_pow
  generalize dimKKT t k + 2 = D at h0 ⊢
  generalize radInv t k = R at h0 ⊢
  have h1 : D ^ (8 * D + 22) ≤ (2 ^ Nat.clog 2 D) ^ (8 * D + 22) :=
    Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
  rw [← pow_mul, Nat.mul_comm (Nat.clog 2 D)] at h1
  exact h0.trans h1

/-- `N = 16 n (n+1) L + 1` with `L = ⌈log₂(n/r_K)⌉`. -/
theorem iters_eq (t k : ℕ) :
    iters t k = 16 * nDim t k * (nDim t k + 1) * logRad t k + 1 := rfl

/-- `p = 64 (n+1) L + 3 ⌈log₂(n+1)⌉ + 15` with `L = ⌈log₂(n/r_K)⌉` (for `n ≥ 1`). -/
theorem prec_eq {t k : ℕ} (hn : 1 ≤ nDim t k) :
    prec t k = 64 * (nDim t k + 1) * logRad t k + 3 * Nat.clog 2 (nDim t k + 1) + 15 := by
  unfold prec iters
  generalize nDim t k = n at hn ⊢
  generalize logRad t k = L
  have e : 16 * n * (n + 1) * L + 1 + n - 1 = n * (16 * (n + 1) * L + 1) := by
    have e1 : 16 * n * (n + 1) * L + 1 + n - 1 = 16 * n * (n + 1) * L + n := by
      generalize 16 * n * (n + 1) * L = A
      omega
    rw [e1]
    ring
  rw [e, Nat.mul_div_cancel_left _ (by omega)]
  ring

end STACS2027.Runtimes.ConvexQP
