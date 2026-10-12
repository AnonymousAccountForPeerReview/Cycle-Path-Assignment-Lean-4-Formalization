module

public import Runtimes.ConvexQP.RAM.KmoK7
public import Runtimes.ConvexQP.RAM.EllBound
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: the bit lengths

With `d = (k+1)t`, `p = prec`, `E = bigE ≤ 2^p` (`bigE_le_pow`) and the magnitudes of Phase M
(`exactFrom_magnitudes`: `|Δ|, |Aj| ≤ d!·A₀^d`, `q ≤ 2^p (E·d!·A₀^d)^r`,
`|Zn| ≤ (2k²t + 2) q`) and of `G` (`kktG_entry_le`: `|G_{iv}| ≤ A₀ = k − 2`): every number of
a step of Phase M is at most `2^e` for an exponent `e` below `bitM I` (`stepBits_of`), with
`d!·A₀^d ≤ 2^{eD}`, `eD = d² + kd`, `q ≤ 2^{eQ}`, `eQ = p + (p + eD) d`. The entries of `Xs` have
at most `p + 1` bits (`xs_bits_kmo`, from `I.InX`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### Powers of two -/

theorem abs_mul_le_pow {x y : ℤ} {a b : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ b) :
    |x * y| ≤ 2 ^ (a + b) := by
  rw [abs_mul, pow_add]
  exact mul_le_mul hx hy (abs_nonneg _) (by positivity)

theorem abs_le_pow_mono {x : ℤ} {a b : ℕ} (h : |x| ≤ 2 ^ a) (hab : a ≤ b) : |x| ≤ 2 ^ b :=
  h.trans (pow_le_pow_right₀ (by norm_num) hab)

theorem pow_add_pow_le (a b : ℕ) : (2 : ℤ) ^ a + 2 ^ b ≤ 2 ^ (a + b + 1) := by
  have h1 : (2 : ℤ) ^ a ≤ 2 ^ (a + b) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℤ) ^ b ≤ 2 ^ (a + b) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ]; linarith

theorem mulVec_abs_le {M : ℕ → ℕ → ℤ} {x : ℕ → ℤ} {n i a b c : ℕ}
    (hM : ∀ j < n, |M i j| ≤ 2 ^ a) (hx : ∀ j < n, |x j| ≤ 2 ^ b) (hn : n ≤ 2 ^ c) :
    |mulVec M x n i| ≤ 2 ^ (c + (a + b)) := by
  unfold mulVec
  calc |∑ j ∈ Finset.range n, M i j * x j| ≤ ∑ j ∈ Finset.range n, |M i j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range n, (2 : ℤ) ^ (a + b) :=
        Finset.sum_le_sum fun j hj =>
          abs_mul_le_pow (hM j (Finset.mem_range.mp hj)) (hx j (Finset.mem_range.mp hj))
    _ = (n : ℤ) * 2 ^ (a + b) := by simp
    _ ≤ 2 ^ c * 2 ^ (a + b) := by
        gcongr
        exact_mod_cast hn
    _ = 2 ^ (c + (a + b)) := by rw [← pow_add]

/-! ### The exponents -/

/-- `d!·A₀^d ≤ 2^{eD}`. -/
def eD (I : Inst) : ℕ := dd I * dd I + I.k * dd I
/-- `q ≤ 2^{eQ}` along Phase M. -/
def eQ (I : Inst) : ℕ := prec I.t I.k + (prec I.t I.k + eD I) * dd I
/-- `|Zn| ≤ 2^{eZ}` along Phase M. -/
def eZ (I : Inst) : ℕ := 3 * dd I + 2 + eQ I
/-- `|u|, |w|, |v| ≤ 2^{eU}`. -/
def eU (I : Inst) : ℕ := dd I + (eD I + I.k)
/-- **The bit bound of a step of Phase M.** -/
def bitM (I : Inst) : ℕ :=
  2 * prec I.t I.k + (dd I + (I.k + eZ I)) + eQ I + (dd I + (I.k + eU I)) + 10

variable {I : Inst} {Xs : Fin I.t → Fin I.k → ℤ}

theorem dd_le_pow (I : Inst) : dd I ≤ 2 ^ dd I := Nat.lt_two_pow_self.le

theorem Ad_le (I : Inst) :
    (dd I).factorial * entryBound I.k ^ dd I ≤ 2 ^ eD I := by
  have h1 : (dd I).factorial ≤ 2 ^ (dd I * dd I) :=
    (Nat.factorial_le_pow _).trans ((Nat.pow_le_pow_left (dd_le_pow I) _).trans
      (by rw [← pow_mul]))
  have h2 : entryBound I.k ^ dd I ≤ 2 ^ (I.k * dd I) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left ((Nat.sub_le _ _).trans Nat.lt_two_pow_self.le) _
  calc (dd I).factorial * entryBound I.k ^ dd I ≤ 2 ^ (dd I * dd I) * 2 ^ (I.k * dd I) :=
        Nat.mul_le_mul h1 h2
    _ = 2 ^ eD I := by rw [← pow_add]; rfl

theorem kz_le (I : Inst) (ht : 0 < I.t) : 2 * I.k ^ 2 * I.t + 2 ≤ 2 ^ (3 * dd I + 2) := by
  have hk : I.k ≤ dd I := k_le_dimKKT (k := I.k) ht
  have htd : I.t ≤ dd I := by have := dimKKT_eq I.t I.k; simp only [dd]; omega
  have h3 : dd I ^ 3 ≤ 2 ^ (3 * dd I) := by
    rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left (dd_le_pow I) 3
  have h4 : I.k ^ 2 * I.t ≤ dd I ^ 3 := by
    calc I.k ^ 2 * I.t ≤ dd I ^ 2 * dd I := Nat.mul_le_mul (Nat.pow_le_pow_left hk 2) htd
      _ = dd I ^ 3 := by ring
  have h5 : 1 ≤ 2 ^ (3 * dd I) := Nat.one_le_two_pow
  have h6 : 2 * I.k ^ 2 * I.t = 2 * (I.k ^ 2 * I.t) := by ring
  rw [pow_add, h6]
  omega

/-- `|G_{iv}| ≤ 2^k` on the columns `v < d`. -/
theorem Gx_abs_le (hI : I.Valid) (i : ℕ) {v : ℕ} (hv : v < dd I) : |Gx I Xs i v| ≤ 2 ^ I.k := by
  have hk : ((I.k - 2 : ℕ) : ℤ) ≤ 2 ^ I.k := by
    exact_mod_cast ((Nat.sub_le _ _).trans Nat.lt_two_pow_self.le)
  unfold Gx Gf
  simp only [show v < dimKKT I.t I.k from hv, ↓reduceIte]
  split_ifs with h
  · exact (kktG_entry_le hI (kktZ I Xs) _ _).trans hk
  · simp

theorem hf_abs_le (I : Inst) (i : ℕ) : |hf I i| ≤ 1 := by
  unfold hf
  split_ifs with h
  · rcases rowEquiv_cases (I := I) ⟨i, h⟩ with ⟨c, s', e⟩ | ⟨c, j', b, e⟩
    · rw [e, kktH_S, sgnS_val]; split_ifs <;> simp
    · rw [e, kktH_X]; simp
  · simp

/-- The entries of `Xs` have at most `p + 1` bits. -/
theorem xs_bits_kmo (hX : I.InX (ptOf Xs (2 ^ prec I.t I.k))) (b : ℕ) :
    Nat.size (flat Xs b).natAbs ≤ prec I.t I.k + 1 := by
  refine flat_bits Xs _ (fun c j => ?_) b
  have hP : (0 : ℝ) < 2 ^ prec I.t I.k := by positivity
  have h0 := hX.1 c j
  have h1 : ptOf Xs (2 ^ prec I.t I.k) c j ≤ 1 := by
    rw [← hX.2 c]
    exact Finset.single_le_sum (fun j _ => hX.1 c j) (Finset.mem_univ j)
  have e : ptOf Xs (2 ^ prec I.t I.k) c j = (Xs c j : ℝ) / 2 ^ prec I.t I.k := by simp [ptOf]
  rw [e] at h0 h1
  rw [div_le_one hP] at h1
  have h0' : (0 : ℝ) ≤ Xs c j := by
    by_contra hn
    exact absurd h0 (not_le.mpr (div_neg_of_neg_of_pos (lt_of_not_ge hn) hP))
  have a0 : (0 : ℤ) ≤ Xs c j := by exact_mod_cast h0'
  have a1 : Xs c j ≤ 2 ^ prec I.t I.k := by exact_mod_cast h1
  rw [abs_of_nonneg a0]; exact a1

/-! ### The numbers of a step of Phase M -/

/-- **The bit lengths of a step of Phase M** are at most `bitM I`. -/
theorem stepBits_of (hI : I.Valid) (ht : 0 < I.t) (hX : I.InX (ptOf Xs (2 ^ prec I.t I.k)))
    (hgap : I.gap (ptOf Xs (2 ^ prec I.t I.k)) ≤ eps I.t I.k ^ 2) {r : ℕ} (hr : r < dd I)
    (s : MState (MM I) (dd I) r)
    (hs : moveAux (KG I Xs) (kktH I) (bigE I.t I.k) (kktZn I Xs) (2 ^ prec I.t I.k) r hr.le =
      some s) : StepBits (Xs := Xs) s (bitM I) := by
  have hk3 := hI.1
  obtain ⟨hΔ, hAj, hq, hZn⟩ := exactFrom_magnitudes hI ht (q₀ := 2 ^ prec I.t I.k)
    (by positivity) hX hgap r hr.le s hs
  have hE : bigE I.t I.k ≤ 2 ^ prec I.t I.k := bigE_le_pow ht hk3
  have hAd := Ad_le I
  have hAdZ : ((dd I).factorial : ℤ) * (entryBound I.k : ℤ) ^ dd I ≤ 2 ^ eD I := by
    exact_mod_cast hAd
  -- the state
  have bΔ : |s.Δ| ≤ 2 ^ eD I := hΔ.trans hAdZ
  have bAj : ∀ a b, |AjF s a b| ≤ 2 ^ eD I := fun a b => by
    unfold AjF
    split_ifs
    · exact (hAj _ _).trans hAdZ
    · simp
  have bq : s.q ≤ 2 ^ eQ I := by
    have h1 : bigE I.t I.k * (dimKKT I.t I.k).factorial * entryBound I.k ^ dimKKT I.t I.k ≤
        2 ^ (prec I.t I.k + eD I) := by
      rw [mul_assoc, pow_add]; exact Nat.mul_le_mul hE hAd
    have h2 : (bigE I.t I.k * (dimKKT I.t I.k).factorial * entryBound I.k ^ dimKKT I.t I.k) ^ r ≤
        (2 ^ (prec I.t I.k + eD I)) ^ dd I :=
      (Nat.pow_le_pow_left h1 r).trans (Nat.pow_le_pow_right Nat.one_le_two_pow hr.le)
    calc s.q ≤ 2 ^ prec I.t I.k * (bigE I.t I.k * (dimKKT I.t I.k).factorial *
          entryBound I.k ^ dimKKT I.t I.k) ^ r := hq
      _ ≤ 2 ^ prec I.t I.k * (2 ^ (prec I.t I.k + eD I)) ^ dd I := Nat.mul_le_mul_left _ h2
      _ = 2 ^ eQ I := by rw [← pow_mul, ← pow_add]; rfl
  have bZn : ∀ v, |ZnF s v| ≤ 2 ^ eZ I := fun v => by
    unfold ZnF
    split_ifs with hv
    · have h1 : |s.Zn ⟨v, hv⟩| ≤ ((2 * I.k ^ 2 * I.t + 2) * s.q : ℕ) := by
        have := hZn ⟨v, hv⟩
        have h2 : ((|s.Zn ⟨v, hv⟩| : ℤ) : ℝ) ≤ (((2 * I.k ^ 2 * I.t + 2) * s.q : ℕ) : ℝ) := by
          push_cast; exact this
        exact_mod_cast h2
      have h3 : (2 * I.k ^ 2 * I.t + 2) * s.q ≤ 2 ^ (3 * dd I + 2) * 2 ^ eQ I :=
        Nat.mul_le_mul (kz_le I ht) bq
      refine h1.trans ?_
      rw [show eZ I = 3 * dd I + 2 + eQ I from rfl, pow_add]
      exact_mod_cast h3
    · simp
  -- `G`, `h`
  have bG : ∀ i, ∀ v < dd I, |Gx I Xs i v| ≤ 2 ^ I.k := fun i v hv => Gx_abs_le hI i hv
  have bhp : ∀ i, |hpf I i| ≤ 2 ^ (prec I.t I.k + 1) := fun i => by
    have h1 := hf_abs_le I i
    have hE' : ((bigE I.t I.k : ℕ) : ℤ) ≤ 2 ^ prec I.t I.k := by exact_mod_cast hE
    have hE0 : (0 : ℤ) ≤ bigE I.t I.k := Nat.cast_nonneg _
    have h2 : |(bigE I.t I.k : ℤ) * hf I i| ≤ (bigE I.t I.k : ℤ) := by
      rw [abs_mul, abs_of_nonneg hE0]
      calc (bigE I.t I.k : ℤ) * |hf I i| ≤ (bigE I.t I.k : ℤ) * 1 :=
            mul_le_mul_of_nonneg_left h1 hE0
        _ = _ := mul_one _
    have h3 : (1 : ℤ) ≤ 2 ^ prec I.t I.k := one_le_pow₀ (by norm_num)
    unfold hpf
    calc |(bigE I.t I.k : ℤ) * hf I i + 1| ≤ |(bigE I.t I.k : ℤ) * hf I i| + |1| := abs_add_le _ _
      _ ≤ 2 ^ prec I.t I.k + 2 ^ prec I.t I.k := by rw [abs_one]; linarith
      _ = 2 ^ (prec I.t I.k + 1) := by ring
  -- the derived vectors
  have bcol : ∀ j, |colf I Xs s j| ≤ 2 ^ I.k := fun j => bG _ r hr
  have bu : ∀ a, |uf I Xs s a| ≤ 2 ^ (dd I + (eD I + I.k)) := fun a =>
    mulVec_abs_le (fun j _ => bAj a j) (fun j _ => bcol j) (hr.le.trans (dd_le_pow I))
  have bw : ∀ b, |wf I Xs s b| ≤ 2 ^ (dd I + (eD I + I.k)) := fun b => by
    unfold wf
    split_ifs
    · rw [abs_neg]; exact bu b
    · exact abs_le_pow_mono bΔ (by omega)
    · simp
  have bom : ∀ i, |omf I Xs s i| ≤ 2 ^ (dd I + (I.k + (dd I + (eD I + I.k)))) := fun i =>
    mulVec_abs_le (fun j hj => bG i j hj) (fun j _ => bw j) (dd_le_pow I)
  have bgz : ∀ i, |gzf I Xs s i| ≤ 2 ^ (dd I + (I.k + eZ I)) := fun i =>
    mulVec_abs_le (fun j hj => bG i j hj) (fun j _ => bZn j) (dd_le_pow I)
  have bv : ∀ ib b, |vf I Xs s ib b| ≤ 2 ^ (dd I + (eD I + I.k)) := fun ib b =>
    mulVec_abs_le (M := fun i j => AjF s j i) (fun j _ => bAj j b)
      (fun j hj => bG ib j (by omega)) (hr.le.trans (dd_le_pow I))
  have bEZ : |(bigE I.t I.k : ℤ)| ≤ 2 ^ prec I.t I.k := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast hE
  have bqZ : |(s.q : ℤ)| ≤ 2 ^ eQ I := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast bq
  have bsg : ∀ i, |sgf I Xs s i| ≤
      2 ^ (prec I.t I.k + (dd I + (I.k + eZ I)) + (eQ I + (prec I.t I.k + 1)) + 1) := fun i => by
    have e1 : sgf I Xs s i = (-(bigE I.t I.k : ℤ)) * gzf I Xs s i + (s.q : ℤ) * hpf I i := by
      simp [sgf, linNew, rnd]
    rw [e1]
    refine (abs_add_le _ _).trans ((add_le_add (abs_mul_le_pow (by rwa [abs_neg]) (bgz i))
      (abs_mul_le_pow bqZ (bhp i))).trans (pow_add_pow_le _ _))
  have beom : ∀ i, |(bigE I.t I.k : ℤ) * omf I Xs s i| ≤
      2 ^ (prec I.t I.k + (dd I + (I.k + (dd I + (eD I + I.k))))) :=
    fun i => abs_mul_le_pow bEZ (bom i)
  -- the bit lengths
  have hB : ∀ {x : ℤ} {e : ℕ}, |x| ≤ 2 ^ e → e + 1 ≤ bitM I → Nat.size x.natAbs ≤ bitM I :=
    fun h he => (size_le_of_abs_le h).trans he
  have hBn : ∀ {x e : ℕ}, x ≤ 2 ^ e → e + 1 ≤ bitM I → Nat.size x ≤ bitM I :=
    fun h he => (size_le_of_le_pow h).trans he
  have hbit : bitM I = 2 * prec I.t I.k + (dd I + (I.k + eZ I)) + eQ I +
      (dd I + (I.k + (dd I + (eD I + I.k)))) + 10 := rfl
  refine ⟨by omega, hBn hE (by omega), hBn bq (by omega), fun j _ => hB (bcol j) (by omega),
    fun j _ => hB (bw j) (by omega), fun j _ => hB (bZn j) (by omega),
    fun i _ => hB (bgz i) (by omega), fun i _ => hB (bhp i) (by omega),
    fun i _ => hB (bom i) (by omega), fun i _ j hj => hB (bG i j hj) (by omega),
    fun a _ b _ => hB (bAj a b) (by omega),
    fun a _ => hB (bu a) (by omega), fun i _ b _ => hB (bv i b) (by omega),
    fun i _ => hB (bsg i) (by omega), fun i _ => hB (beom i) (by omega)⟩

end STACS2027.Runtimes.QPRam.Kmo
