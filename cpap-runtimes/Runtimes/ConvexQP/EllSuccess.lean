module

public import Runtimes.ConvexQP.EllPhase
public import Runtimes.ConvexQP.Exact
import Mathlib.Tactic

/-!
# Lemma 16, Phase E succeeds (B10), and Lemma 16

For a valid instance with `t ≥ 1`:

* The sublevel set `Kset I = {y ∈ Y : f(y) ≤ f* + δ₀}` (`f* = inf_Y f`, `δ₀ = g₀²/(2C₀)`,
  `g₀ = ε²`) satisfies every cut of the run (`ellCut_valid`): E1 cuts by `y ≥ 0` and
  `∑_j y_{c,j} ≤ 1`; E3 cuts since `f(a) > f* + δ₀` at a feasible center with gap `> g₀`
  (Frank–Wolfe decrease, A4(d)) and the gradient inequality of `f` (A5(b)).
* `Kset I` lies in the initial ellipsoid `E((n/4)I, ½𝟙)` (`Kset_init`) and contains a ball of
  radius `r_K = (δ₀/(2Φ₀))·1/(2(k−1))` (`ball_in_Kset`), with `n / r_K = radInv t k`.
* Every state reached within `N` iterations satisfies the invariant of the generic run
  (`ellIter_inv`, via B9 `ell_invariant`, `ellUpdate_round`, the square-root bound `isqrt_err`
  and E0 `prec_bounds`); after `N` cut iterations, B9's contradiction (`ell_contradiction`) with
  the count `final_lt` shows that some iteration succeeds.
* **B10** (`ellRun_success`): `ellRun I (consts I.t I.k) = some Xs` with `Xs/2^p ∈ 𝒳` and
  `gap(Xs/2^p) ≤ ε²`. Hence `phaseE` meets `PhaseESpec` (`phaseE_spec`), and **Lemma 16**
  (`relaxation_exact_optimal`): `solveExact = solveExactWith phaseE` returns an optimal fractional
  solution of the relaxation on the `k`-cycles of every duplicate-free graph.
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Matrix Finset

variable {I : Inst}

/-! ### The sublevel set -/

/-- `f* = inf_Y f`. -/
noncomputable def fstar (I : Inst) : ℝ := sInf ((fun y => I.f y) '' {y | I.InY y})

/-- `δ₀ = g₀² / (2 C₀)` with `g₀ = ε²`. -/
noncomputable def delta0 (t k : ℕ) : ℝ := (eps t k ^ 2) ^ 2 / (2 * curv t k)

/-- The sublevel set `K = {y ∈ Y : f(y) ≤ f* + δ₀}` (in coordinates `Idx I`). -/
def Kset (I : Inst) : Set (Idx I → ℝ) :=
  {y | I.InY (cur y) ∧ I.f (cur y) ≤ fstar I + delta0 I.t I.k}

theorem fstar_bdd (I : Inst) : BddBelow ((fun y => I.f y) '' {y | I.InY y}) :=
  ⟨0, fun _ ⟨y, _, hy⟩ => hy ▸ Inst.f_nonneg y⟩

theorem fstar_le {y : Fin I.t → Fin (I.k - 1) → ℝ} (hy : I.InY y) : fstar I ≤ I.f y :=
  csInf_le (fstar_bdd I) ⟨y, hy, rfl⟩

theorem inY_zero (I : Inst) : I.InY (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun _ => by simp⟩

theorem exists_near_fstar (I : Inst) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y, I.InY y ∧ I.f y < fstar I + δ := by
  have hne : ((fun y => I.f y) '' {y | I.InY y}).Nonempty := ⟨_, ⟨_, inY_zero I, rfl⟩⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (by linarith : fstar I < fstar I + δ)
  exact ⟨y, hy, hlt⟩

theorem curv_ge_one {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : (1 : ℝ) ≤ curv t k := by
  unfold curv
  have : 1 ≤ 2 * (k - 2) * t ^ 2 := by
    have : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ ht
    have : 1 ≤ k - 2 := by omega
    nlinarith
  exact_mod_cast this

theorem eps_le_one (t : ℕ) {k : ℕ} (hk : 3 ≤ k) : eps t k ≤ 1 := by
  unfold eps
  have : (1 : ℝ) ≤ bigE t k := by exact_mod_cast bigE_pos t hk
  rw [div_le_one (by linarith)]
  exact this

theorem delta0_pos {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : 0 < delta0 t k := by
  unfold delta0
  have := eps_pos t hk
  have := curv_ge_one ht hk
  positivity

/-! ### Validity of the cuts -/

theorem dot_negCut (i : Idx I) (w : Idx I → ℝ) : gR (negCut I i) ⬝ᵥ w = -w i := by
  simp [dotProduct, gR, negCut]

theorem dot_blockCut (c : Fin I.t) (w : Idx I → ℝ) :
    gR (blockCut I c) ⬝ᵥ w = ∑ j, w (c, j) := by
  simp only [dotProduct, gR, blockCut, Fintype.sum_prod_type]
  push_cast
  simp

theorem dot_gradCut (Xs : Fin I.t → Fin I.k → ℤ) (w : Idx I → ℝ) :
    gR (gradCut I Xs) ⬝ᵥ w = ∑ c, ∑ j, ((I.gradRed Xs c j : ℤ) : ℝ) * w (c, j) := by
  simp only [dotProduct, gR, gradCut, Fintype.sum_prod_type]

theorem cur_sub (y a : Idx I → ℝ) : cur (y - a) = cur y - cur a := rfl

/-- The reduced center of a feasible state lies in `Y`, and its completion is `Xs/2^p`. -/
theorem feas_inY {p : ℕ} {As : Idx I → ℤ} (hneg : ∀ i, 0 ≤ As i)
    (hblk : ∀ c, blockSum I As c ≤ 2 ^ p) : I.InY (cur (aR p As)) := by
  have hP : (0 : ℝ) < 2 ^ p := by positivity
  refine ⟨fun c j => ?_, fun c => ?_⟩
  · simp only [cur, aR]
    have : (0 : ℝ) ≤ As (c, j) := by exact_mod_cast hneg (c, j)
    positivity
  · simp only [cur, aR]
    rw [← Finset.sum_div, div_le_one hP]
    have := hblk c
    unfold blockSum at this
    exact_mod_cast this

theorem ptOf_feasPt (p : ℕ) (As : Idx I → ℤ) :
    ptOf (feasPt I p As) (2 ^ p) = I.xi (cur (aR p As)) := by
  have h := Inst.xiq_div (I := I) (fun c j => As (c, j)) (q := 2 ^ p) (by positivity)
  unfold feasPt
  push_cast at h
  rw [h]
  rfl

theorem gap_ptOf (Xs : Fin I.t → Fin I.k → ℤ) (p : ℕ) :
    I.gap (ptOf Xs (2 ^ p)) = ((I.gap Xs : ℤ) : ℝ) / 4 ^ p := by
  have h := I.gap_div Xs (q := (2 : ℝ) ^ p) (by positivity)
  unfold ptOf
  push_cast
  rw [h, ← pow_mul, mul_comm, pow_mul]
  norm_num

/-- At a feasible center with gap `> g₀` the value of `f` exceeds `f* + δ₀`. -/
theorem f_gt_of_gap (hI : I.Valid) (ht : 0 < I.t) {y : Fin I.t → Fin (I.k - 1) → ℝ}
    (hy : I.InY y) (hgap : eps I.t I.k ^ 2 < I.gap (I.xi y)) :
    fstar I + delta0 I.t I.k < I.f y := by
  have hk : 0 < I.k := by have := hI.1; omega
  have hx := Inst.xi_inX hk hy
  have he := eps_pos I.t hI.1
  have he1 := eps_le_one I.t hI.1
  have hC := curv_ge_one ht hI.1
  obtain ⟨hx', hlt⟩ := Inst.F_fw_step_decrease hI hx (g₀ := eps I.t I.k ^ 2) (by positivity)
    (by nlinarith) hgap
  set x' := I.xi y + (eps I.t I.k ^ 2 / curv I.t I.k) • (I.vtx (I.xi y) - I.xi y)
  have h1 : fstar I ≤ I.F x' := by
    have := fstar_le (Inst.red_inY hx')
    rwa [Inst.f, Inst.xi_red hx'] at this
  unfold delta0
  unfold Inst.f
  linarith

/-- **The cuts are valid** for the sublevel set: every point of `Kset I` lies strictly on the
negative side of the cut through the current center. -/
theorem ellCut_valid (hI : I.Valid) (ht : 0 < I.t) {K : Consts} (hKE : K.E = bigE I.t I.k)
    {As : Idx I → ℤ} {g : Idx I → ℤ} (h : ellCut I K As = .inl g) :
    ∀ y ∈ Kset I, gR g ⬝ᵥ (y - aR K.p As) < 0 := by
  intro y hy
  have hP : (0 : ℝ) < 2 ^ K.p := by positivity
  unfold ellCut at h
  split at h
  · -- a negative coordinate
    rename_i i hi
    obtain rfl : negCut I i = g := Sum.inl.inj h
    rw [dot_negCut]
    have h1 := firstNeg_some hi
    have h2 : 0 ≤ y i := hy.1.1 i.1 i.2
    have h3 : (As i : ℝ) / 2 ^ K.p < 0 := div_neg_of_neg_of_pos (by exact_mod_cast h1) hP
    simp only [Pi.sub_apply, aR]
    linarith
  · rename_i hneg
    split at h
    · -- a block sum above `2^p`
      rename_i c hc
      obtain rfl : blockCut I c = g := Sum.inl.inj h
      rw [dot_blockCut]
      have h1 := firstOver_some hc
      have h2 : ∑ j, y (c, j) ≤ 1 := hy.1.2 c
      have h3 : 1 < blockSum I As c / (2 : ℝ) ^ K.p := by
        rw [one_lt_div hP]
        exact_mod_cast h1
      simp only [Pi.sub_apply, aR, Finset.sum_sub_distrib]
      rw [← Finset.sum_div]
      unfold blockSum at h3
      push_cast at h3
      linarith
    · -- the gradient cut at a feasible center
      rename_i hover
      split at h
      · exact absurd h (by simp)
      · rename_i hgap
        obtain rfl : gradCut I (feasPt I K.p As) = g := Sum.inl.inj h
        have hneg' := firstNeg_none hneg
        have hover' := firstOver_none hover
        have hY := feas_inY hneg' hover'
        have hk : 0 < I.k := by have := hI.1; omega
        -- the gap exceeds `g₀ = ε² = 1/E²`
        have hgapR : eps I.t I.k ^ 2 < I.gap (I.xi (cur (aR K.p As))) := by
          rw [← ptOf_feasPt, gap_ptOf]
          have hE : (0 : ℝ) < bigE I.t I.k := by exact_mod_cast bigE_pos I.t hI.1
          rw [hKE] at hgap
          have h4 : (4 : ℤ) ^ K.p < I.gap (feasPt I K.p As) * (bigE I.t I.k : ℤ) ^ 2 :=
            lt_of_not_ge hgap
          have h4R : (4 : ℝ) ^ K.p <
              ((I.gap (feasPt I K.p As) : ℤ) : ℝ) * (bigE I.t I.k : ℝ) ^ 2 := by
            exact_mod_cast h4
          unfold eps
          rw [div_pow, one_pow, div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
          linarith
        have hf := f_gt_of_gap hI ht hY hgapR
        have hfy := hy.2
        have hge := Inst.f_ge hk (cur (aR K.p As)) (cur y)
        -- `g = 2^p ∇f(a)`
        rw [dot_gradCut]
        have hgr : ∀ c j, ((I.gradRed (feasPt I K.p As) c j : ℤ) : ℝ) =
            2 ^ K.p * I.gradRed (I.xi (cur (aR K.p As))) c j := by
          intro c j
          rw [← ptOf_feasPt]
          unfold ptOf
          rw [Inst.gradRed_div]
          push_cast
          field_simp
        have hsum : ∑ c, ∑ j, ((I.gradRed (feasPt I K.p As) c j : ℤ) : ℝ) *
            (y - aR K.p As) (c, j) =
            2 ^ K.p * ∑ c, ∑ j, I.gradRed (I.xi (cur (aR K.p As))) c j *
              (cur y c j - cur (aR K.p As) c j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hgr]
          simp only [Pi.sub_apply, cur]
          ring
        rw [hsum]
        have : ∑ c, ∑ j, I.gradRed (I.xi (cur (aR K.p As))) c j *
            (cur y c j - cur (aR K.p As) c j) < 0 := by
          unfold Inst.f at hf hge hfy
          linarith
        exact mul_neg_of_pos_of_neg hP this

/-- A successful iteration outputs `Xs` with `Xs/2^p ∈ 𝒳` and `gap(Xs/2^p) ≤ ε²`. -/
theorem ellCut_inr (hI : I.Valid) {K : Consts} (hKE : K.E = bigE I.t I.k)
    {As : Idx I → ℤ} {Xs : Fin I.t → Fin I.k → ℤ} (h : ellCut I K As = .inr Xs) :
    I.InX (ptOf Xs (2 ^ K.p)) ∧ I.gap (ptOf Xs (2 ^ K.p)) ≤ eps I.t I.k ^ 2 := by
  unfold ellCut at h
  split at h
  · exact absurd h (by simp)
  · rename_i hneg
    split at h
    · exact absurd h (by simp)
    · rename_i hover
      split at h
      · rename_i hgap
        obtain rfl : feasPt I K.p As = Xs := Sum.inr.inj h
        have hk : 0 < I.k := by have := hI.1; omega
        refine ⟨?_, ?_⟩
        · rw [ptOf_feasPt]
          exact Inst.xi_inX hk (feas_inY (firstNeg_none hneg) (firstOver_none hover))
        · rw [gap_ptOf]
          have hE : (0 : ℝ) < bigE I.t I.k := by exact_mod_cast bigE_pos I.t hI.1
          rw [hKE] at hgap
          have hR : ((I.gap (feasPt I K.p As) : ℤ) : ℝ) * (bigE I.t I.k : ℝ) ^ 2 ≤ 4 ^ K.p := by
            exact_mod_cast hgap
          unfold eps
          rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
          linarith
      · exact absurd h (by simp)

/-! ### The initial ellipsoid and the inner ball -/

theorem QR_init {K : Consts} (hp : 2 ≤ K.p) :
    QR K.p (ellInit I K).Qs = ((K.n : ℝ) / 4) • (1 : Matrix (Idx I) (Idx I) ℝ) := by
  ext i j
  simp only [QR, ellInit, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · push_cast
    rw [show K.p = K.p - 2 + 2 by omega, pow_add]
    field_simp
    norm_num
  · simp

theorem aR_init {K : Consts} (hp : 1 ≤ K.p) : aR K.p (ellInit I K).As = fun _ => 1 / 2 := by
  funext i
  simp only [aR, ellInit]
  push_cast
  rw [show K.p = K.p - 1 + 1 by omega, pow_add]
  field_simp
  norm_num

/-- `K ⊆ Y ⊆ [0,1]^n ⊆ E((n/4) I, ½𝟙)`. -/
theorem Kset_init {y : Idx I → ℝ} (hy : y ∈ Kset I) :
    InEll (((Fintype.card (Idx I) : ℝ) / 4) • (1 : Matrix (Idx I) (Idx I) ℝ))
      (fun _ => 1 / 2) y := by
  intro v
  rw [qf_smul, qf_one]
  have h := sq_dot_le_of_abs (ϵ := 1 / 2) (w := y - fun _ => 1 / 2) (fun i => by
    have := Inst.InY_le_one hy.1 i.1 i.2
    simp only [cur] at this
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;> linarith) v
  calc (v ⬝ᵥ (y - fun _ => 1 / 2)) ^ 2 ≤ Fintype.card (Idx I) * (1 / 2) ^ 2 * (v ⬝ᵥ v) := h
    _ = _ := by ring

/-- The radius of the inner ball: `r_K = (δ₀/(2Φ₀)) · 1/(2(k−1))`. -/
noncomputable def rK (t k : ℕ) : ℝ := delta0 t k / (2 * Phi0 t k) * (1 / (2 * ((k - 1 : ℕ) : ℝ)))

theorem Phi0_pos {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : 0 < Phi0 t k := by
  unfold Phi0
  have : (0 : ℝ) < ((k - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 2)
  have : (0 : ℝ) < t := by exact_mod_cast ht
  positivity

theorem rK_pos {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : 0 < rK t k := by
  unfold rK
  have := delta0_pos ht hk
  have := Phi0_pos ht hk
  have : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
  positivity

/-- `n / r_K = radInv t k`. -/
theorem div_rK {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : (nDim t k : ℝ) / rK t k = radInv t k := by
  unfold rK delta0 Phi0 radInv eps
  have hE : (0 : ℝ) < bigE t k := by exact_mod_cast bigE_pos t hk
  have hC : (0 : ℝ) < curv t k := lt_of_lt_of_le one_pos (curv_ge_one ht hk)
  have h2 : (0 : ℝ) < ((k - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 2)
  have h1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  push_cast
  field_simp
  ring

theorem inY_convex {y w : Fin I.t → Fin (I.k - 1) → ℝ} (hy : I.InY y) (hw : I.InY w) {ρ : ℝ}
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : I.InY ((1 - ρ) • y + ρ • w) := by
  refine ⟨fun c j => ?_, fun c => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hy.1 c j, hw.1 c j]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith [hy.2 c, hw.2 c]

/-- **A ball in `K`**: `K` contains a ball of radius `r_K`. -/
theorem ball_in_Kset (hI : I.Valid) (ht : 0 < I.t) :
    ∃ z : Idx I → ℝ, ∀ y, (y - z) ⬝ᵥ (y - z) ≤ rK I.t I.k ^ 2 → y ∈ Kset I := by
  have hk2 : 2 ≤ I.k := by have := hI.1; omega
  have hδ := delta0_pos ht hI.1
  have hΦ := Phi0_pos ht hI.1
  obtain ⟨y0, hy0, hf0⟩ := exists_near_fstar I (half_pos hδ)
  set ρ := delta0 I.t I.k / (2 * Phi0 I.t I.k) with hρ
  set rY : ℝ := 1 / (2 * ((I.k - 1 : ℕ) : ℝ)) with hrY
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one (by positivity)]
    have he := eps_le_one I.t hI.1
    have he0 := eps_pos I.t hI.1
    have hC := curv_ge_one ht hI.1
    have h1 : delta0 I.t I.k ≤ 1 := by
      unfold delta0
      rw [div_le_one (by positivity)]
      have : (eps I.t I.k ^ 2) ^ 2 ≤ 1 := by
        have : eps I.t I.k ^ 2 ≤ 1 := pow_le_one₀ he0.le he
        exact pow_le_one₀ (by positivity) this
      linarith
    have h2 : (1 : ℝ) ≤ 2 * Phi0 I.t I.k := by
      unfold Phi0
      have h3 : (1 : ℝ) ≤ ((I.k - 2 : ℕ) : ℝ) := by exact_mod_cast (by have := hI.1; omega)
      have h4 : (1 : ℝ) ≤ (I.t : ℝ) := by exact_mod_cast ht
      have h5 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ h3 (n := 2)) (one_le_pow₀ h4 (n := 2))
      linarith
    linarith
  have hrK : rK I.t I.k = ρ * rY := rfl
  refine ⟨fun i => y0 i.1 i.2 + ρ * (rY - y0 i.1 i.2), fun y hy => ?_⟩
  set w : Fin I.t → Fin (I.k - 1) → ℝ := fun c j => y0 c j + (y (c, j) - y0 c j) / ρ with hw
  have hwY : I.InY w := by
    apply Inst.ball_subset_Y hk2
    rw [← hrY]
    have e : ∀ c j, w c j - rY = (y (c, j) - (y0 c j + ρ * (rY - y0 c j))) / ρ := by
      intro c j
      rw [hw]
      field_simp
      ring
    simp only [e, div_pow, ← Finset.sum_div]
    rw [div_le_iff₀ (by positivity)]
    have h1 : (y - fun i => y0 i.1 i.2 + ρ * (rY - y0 i.1 i.2)) ⬝ᵥ
        (y - fun i => y0 i.1 i.2 + ρ * (rY - y0 i.1 i.2)) =
        ∑ c, ∑ j, (y (c, j) - (y0 c j + ρ * (rY - y0 c j))) ^ 2 := by
      simp only [dotProduct, Fintype.sum_prod_type, Pi.sub_apply, sq]
    rw [← h1]
    calc _ ≤ rK I.t I.k ^ 2 := hy
      _ = rY ^ 2 * ρ ^ 2 := by rw [hrK]; ring
  have hcy : cur y = (1 - ρ) • y0 + ρ • w := by
    funext c j
    simp only [cur, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw]
    field_simp
    ring
  have hYy : I.InY (cur y) := by
    rw [hcy]; exact inY_convex hy0 hwY hρ0.le hρ1
  refine ⟨hYy, ?_⟩
  have hconv := Inst.f_convex y0 w hρ0.le hρ1
  have hfw := Inst.f_le_Phi0 hI hwY
  have hf0' := Inst.f_nonneg y0
  rw [hcy]
  have e : ρ * Phi0 I.t I.k = delta0 I.t I.k / 2 := by
    rw [hρ]; field_simp
  nlinarith [mul_le_mul_of_nonneg_left hfw hρ0.le]

/-! ### The run -/

/-- The state after `i` iterations (the initial state if the run has already succeeded). -/
def stOf (I : Inst) (K : Consts) (i : ℕ) : EllState I :=
  match ellIter I K i with
  | .inl st => st
  | .inr _ => ellInit I K

theorem ellIter_inr_succ {K : Consts} {i : ℕ} {Xs : Fin I.t → Fin I.k → ℤ}
    (h : ellIter I K i = .inr Xs) : ellIter I K (i + 1) = .inr Xs := by
  simp [ellIter, h]

theorem ellIter_inr_le {K : Consts} {i j : ℕ} (hij : i ≤ j) {Xs : Fin I.t → Fin I.k → ℤ}
    (h : ellIter I K i = .inr Xs) : ellIter I K j = .inr Xs := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ j _ ih => exact ellIter_inr_succ ih

theorem ellIter_inl_le {K : Consts} {i j : ℕ} (hij : i ≤ j) {st : EllState I}
    (h : ellIter I K j = .inl st) : ellIter I K i = .inl (stOf I K i) := by
  unfold stOf
  rcases hi : ellIter I K i with st' | Xs
  · rfl
  · rw [ellIter_inr_le hij hi] at h
    exact absurd h (by simp)

theorem ellIter_succ_inl {K : Consts} {i : ℕ} {st : EllState I} (h : ellIter I K i = .inl st) :
    ellIter I K (i + 1) = ellStep I K st := by
  simp [ellIter, h]

/-- A successful output comes from a successful cut. -/
theorem ellIter_inr {K : Consts} {i : ℕ} {Xs : Fin I.t → Fin I.k → ℤ}
    (h : ellIter I K i = .inr Xs) : ∃ As, ellCut I K As = .inr Xs := by
  induction i with
  | zero => simp [ellIter] at h
  | succ i ih =>
    rcases hi : ellIter I K i with st | Xs'
    · rw [ellIter_succ_inl hi] at h
      unfold ellStep at h
      split at h
      · exact absurd h (by simp)
      · rename_i Xs'' hc
        obtain rfl : Xs'' = Xs := Sum.inr.inj h
        exact ⟨st.As, hc⟩
    · rw [ellIter_inr_succ hi] at h
      obtain rfl : Xs' = Xs := Sum.inr.inj h
      exact ih hi

/-- A cut iteration: the cut of the state and the next state. -/
theorem ellIter_cut {K : Consts} {i : ℕ} {st st' : EllState I}
    (h : ellIter I K i = .inl st) (h' : ellIter I K (i + 1) = .inl st') :
    ∃ g, ellCut I K st.As = .inl g ∧ st' = ellUpdate I K st g := by
  rw [ellIter_succ_inl h] at h'
  unfold ellStep at h'
  split at h'
  · rename_i g hg
    exact ⟨g, hg, (Sum.inl.inj h').symm⟩
  · exact absurd h' (by simp)

theorem isSymm_of_QR {p : ℕ} {Qs : Matrix (Idx I) (Idx I) ℤ} (h : (QR p Qs).IsSymm) :
    Qs.IsSymm := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [transpose_apply, QR] at this
  have hP : (2 : ℝ) ^ p ≠ 0 := by positivity
  rw [div_left_inj' hP] at this
  exact_mod_cast this

/-- The precision facts of E0 for the constants `consts` at level `i ≤ N`. -/
theorem prec_facts (hI : I.Valid) (ht : 0 < I.t) {i : ℕ} (hi : i ≤ iters I.t I.k) :
    (Fintype.card (Idx I) : ℝ) * (1 / 2 ^ (prec I.t I.k + 1)) ≤
        etaOf (Fintype.card (Idx I)) * ellOf (Fintype.card (Idx I)) i ∧
      (Fintype.card (Idx I) : ℝ) * (1 / 2 ^ (prec I.t I.k + 1)) ^ 2 ≤
        (etaOf (Fintype.card (Idx I)) / 4) ^ 2 * ellOf (Fintype.card (Idx I)) i ∧
      (1 / (2 : ℝ) ^ (2 * prec I.t I.k)) ^ 2 ≤
        (etaOf (Fintype.card (Idx I)) / 4) ^ 2 * ellOf (Fintype.card (Idx I)) i := by
  rw [card_idx]
  have hn := nDim_ge_two ht hI.1
  have hmain := prec_main (n := nDim I.t I.k) (N := iters I.t I.k) (p := prec I.t I.k)
    (by omega) prec_ge
  obtain ⟨h1, h2, h3⟩ := prec_bounds (by omega) hmain
  have hmono := ellOf_anti (n := nDim I.t I.k) (by omega) hi
  have hη := etaOf_pos (n := nDim I.t I.k) (by omega)
  exact ⟨h1.trans (mul_le_mul_of_nonneg_left hmono hη.le),
    h2.trans (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)),
    h3.trans (mul_le_mul_of_nonneg_left hmono (sq_nonneg _))⟩

/-- **Every state reached within `N` iterations satisfies the invariant** of the generic run
(B9) for the sublevel set `K`. -/
theorem ellIter_inv (hI : I.Valid) (ht : 0 < I.t) {i : ℕ} (hi : i ≤ iters I.t I.k)
    {st : EllState I} (h : ellIter I (consts I.t I.k) i = .inl st) :
    EllInv (Kset I) i (QR (prec I.t I.k) st.Qs) (aR (prec I.t I.k) st.As) := by
  set K := consts I.t I.k with hK
  have hn := nDim_ge_two ht hI.1
  have hcard := card_idx I
  have hn' : 2 ≤ Fintype.card (Idx I) := hcard ▸ hn
  obtain ⟨hϵ1, hϵ2, hδ⟩ := prec_facts hI ht hi
  obtain ⟨y0, hy0, hf0⟩ := exists_near_fstar I (delta0_pos ht hI.1)
  have hy0K : (fun i : Idx I => y0 i.1 i.2) ∈ Kset I := ⟨hy0, hf0.le⟩
  have hp2 := prec_ge_two I.t I.k
  have key := ell_invariant hn' (Kset I) i (fun j => QR K.p (stOf I K j).Qs)
    (fun j => aR K.p (stOf I K j).As) (ϵ := 1 / 2 ^ (prec I.t I.k + 1))
    (δ := 1 / 2 ^ (2 * prec I.t I.k)) (by positivity)
    (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)) hϵ1 hϵ2
    (by positivity) hδ ?h0 ?ha0 ?hK0 ?hstep i le_rfl
  · have := ellIter_inl_le le_rfl h
    rw [h] at this
    obtain rfl : stOf I K i = st := (Sum.inl.inj this).symm
    exact key
  case h0 =>
    have h0 : ellIter I K 0 = .inl (ellInit I K) := rfl
    show QR K.p (stOf I K 0).Qs = _
    simp only [stOf, h0]
    rw [QR_init hp2, hcard]
    rfl
  case ha0 =>
    have h0 : ellIter I K 0 = .inl (ellInit I K) := rfl
    intro j
    simp only [stOf, h0]
    rw [aR_init (by show 1 ≤ prec I.t I.k; omega)]
    norm_num
  case hK0 =>
    have h0 : ellIter I K 0 = .inl (ellInit I K) := rfl
    intro x hx
    simp only [stOf, h0]
    rw [QR_init hp2, aR_init (by show 1 ≤ prec I.t I.k; omega)]
    have := Kset_init hx
    rw [hcard] at this
    exact this
  case hstep =>
    intro j hj hinv
    have hj1 := ellIter_inl_le (by omega : j ≤ i) h
    have hj2 := ellIter_inl_le (by omega : j + 1 ≤ i) h
    obtain ⟨g, hg, hupd⟩ := ellIter_cut hj1 hj2
    have hvalid := ellCut_valid hI ht rfl hg
    have hg0 : gR g ≠ 0 := by
      intro h0
      have := hvalid _ hy0K
      rw [h0, zero_dotProduct] at this
      exact lt_irrefl 0 this
    have hgg := one_le_dot_gR hg0
    have hℓ := ellOf_pos (n := Fintype.card (Idx I)) (by omega) j
    have hpsd := formGe_nonneg hℓ.le hinv.ge
    have hqf := qf_QR K.p (stOf I K j).Qs g
    have hGpos : 0 < updG I (stOf I K j) g := by
      have h1 := hinv.ge (gR g)
      have h2 : 0 < qf (QR K.p (stOf I K j).Qs) (gR g) := by nlinarith
      rw [hqf] at h2
      have : (0 : ℝ) < (updG I (stOf I K j) g : ℝ) := by
        have hP : (0 : ℝ) < 2 ^ K.p := by positivity
        have := (div_pos_iff_of_pos_right hP).mp h2
        exact this
      exact_mod_cast this
    refine ⟨gR g, (updS I K (stOf I K j) g : ℝ) / 2 ^ (2 * K.p), hgg, ?_,
      fun x hx => (hvalid x hx).le, ?_⟩
    · -- the square root
      have herr := isqrt_err (updG I (stOf I K j) g).toNat K.p
      have hG : ((updG I (stOf I K j) g).toNat : ℝ) = (updG I (stOf I K j) g : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hGpos.le
      rw [hG] at herr
      rw [hqf]
      exact herr
    · -- the rounding
      have hround := ellUpdate_round K (cDen_pos hn) (cNum_div_cDen hn) (stOf I K j)
        (isSymm_of_QR hinv.symm) g hGpos
      have hst : stOf I K (j + 1) = ellUpdate I K (stOf I K j) g := hupd
      rw [hst]
      have hKn : (K.n : ℝ) = (Fintype.card (Idx I) : ℝ) := by rw [hcard]; rfl
      have hKn' : K.n = Fintype.card (Idx I) := by rw [hcard]; rfl
      rw [hKn'] at hround
      exact hround

/-! ### B10 -/

/-- **B10 (Phase E succeeds).** On every valid instance with `t ≥ 1`, Phase E stops with
success within `N` iterations, and its output `Xs` satisfies `Xs/2^p ∈ 𝒳` and
`gap(Xs/2^p) ≤ g₀ = ε²`. -/
theorem ellRun_success (hI : I.Valid) (ht : 0 < I.t) :
    ∃ Xs, ellRun I (consts I.t I.k) = some Xs ∧
      I.InX (ptOf Xs (2 ^ (consts I.t I.k).p)) ∧
      I.gap (ptOf Xs (2 ^ (consts I.t I.k).p)) ≤ eps I.t I.k ^ 2 := by
  set K := consts I.t I.k with hK
  rcases hN : ellIter I K K.N with st | Xs
  · -- no success within `N` iterations: contradiction
    exfalso
    have hinv := ellIter_inv hI ht le_rfl hN
    obtain ⟨z, hz⟩ := ball_in_Kset hI ht
    have hn := nDim_ge_two ht hI.1
    have hfin := final_lt (n := nDim I.t I.k) (L := logRad I.t I.k) hn (rK_pos ht hI.1)
      (by rw [div_rK ht hI.1]; exact_mod_cast Nat.le_pow_clog (by norm_num) _)
    have hcard := card_idx I
    exact ell_contradiction hinv (rK_pos ht hI.1) hz (by rw [hcard]; exact hfin)
  · obtain ⟨As, hc⟩ := ellIter_inr hN
    refine ⟨Xs, ?_, ellCut_inr hI rfl hc⟩
    simp only [ellRun, hN]

/-! ### Phase E and Lemma 16 -/

/-- **Phase E**: the ellipsoid run with the constants `consts`; the output is `(Xs, 2^p)`. -/
def phaseE (I : Inst) : Option ((Fin I.t → Fin I.k → ℤ) × ℕ) :=
  (ellRun I (consts I.t I.k)).map fun Xs => (Xs, 2 ^ (consts I.t I.k).p)

/-- **B10 as the interface of Part D**: `phaseE` meets `PhaseESpec`. -/
theorem phaseE_spec : PhaseESpec phaseE := by
  intro I hI ht
  obtain ⟨Xs, hrun, hX, hgap⟩ := ellRun_success hI ht
  exact ⟨Xs, 2 ^ (consts I.t I.k).p, by simp [phaseE, hrun], by positivity, hX, hgap⟩

/-- **EXACT**: Phase E (the rational central-cut ellipsoid method), then the exact rounding of
Part D, on the option lists `opts` over the edge list `es`. -/
def solveExact (es : List Edge) (k : ℕ) (opts : List (List (List Edge))) : ℕ × List (List ℕ) :=
  solveExactWith phaseE es k opts

/-- **Lemma 16** (as mathematics). The algorithm EXACT returns an exactly optimal fractional
solution of the convex relaxation of Section 7.2 on the `k`-cycles of every duplicate-free graph:
the hypothesis `hopt : OptimalFractional g D R` of Theorems 16 and 17. -/
theorem relaxation_exact_optimal {g : Graph} (hg : g.Nodup) (k : ℕ) :
    let opts := (cycles g k).map selectedOptions
    OptimalFractional g (solveExact g k opts).1 (opts.zip (solveExact g k opts).2) :=
  solveExactWith_optimal phaseE phaseE_spec hg k

/-- The output of `solveExact` keeps the option lists of the cycles (hypothesis `hR` of
Theorems 16 and 17). -/
theorem solveExact_map_fst {g : Graph} (hg : g.Nodup) (k : ℕ) :
    let opts := (cycles g k).map selectedOptions
    (opts.zip (solveExact g k opts).2).map Prod.fst = opts :=
  solveExactWith_map_fst phaseE phaseE_spec hg k

end STACS2027.Runtimes.ConvexQP
