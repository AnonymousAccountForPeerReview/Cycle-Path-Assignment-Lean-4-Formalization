module

public import Runtimes.ConvexQP.RAM.QPIface
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: registers, flat specification functions, memory helpers

Layout: `NOTE-kmo.md`. This file fixes the registers of Phases K, M, O (`500–539`),
the KKT data on natural indices (`Gf`, the matrix `G` of `kktG`; `hf`, the right-hand side;
`Gx`, `G` with `h` as an extra column `d`; `hpf = E h + 1`; `ZnF₀`, the start point `kktZn`), the
row contents of `G` (`Gx_S`: the rows `S_{c,s}`, `Gx_X`: the three rows of `(c, j)`), the
states of Phase M on natural indices (`TF`, `AjF`, `ZnF`), and memory helpers (`SArr` transport,
reads of strided writes).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### Registers -/

/-- Base of `G` (`M` rows of `d + 1` signed entries). -/
abbrev kPG : ℕ := 500
/-- Row stride of `G`: `2d + 2`. -/
abbrev kGS : ℕ := 501
/-- Base of `Aj` (`d` rows of `d` signed entries). -/
abbrev kPAJ : ℕ := 502
/-- Row stride of `Aj`: `2d`. -/
abbrev kAS : ℕ := 503
/-- Base of `Zn`. -/
abbrev kPZN : ℕ := 504
/-- Base of `col`. -/
abbrev kPCOL : ℕ := 505
/-- Base of `u = Aj col`. -/
abbrev kPU : ℕ := 506
/-- Base of `v = ρᵀ Aj`. -/
abbrev kPV : ℕ := 507
/-- Base of `w`. -/
abbrev kPW : ℕ := 508
/-- Base of `ω`. -/
abbrev kPOM : ℕ := 509
/-- Base of `G Zn`, then `σ`. -/
abbrev kPSG : ℕ := 510
/-- Base of `h' = E h + 1`. -/
abbrev kPHP : ℕ := 511
/-- Base of `T` (row pointers). -/
abbrev kPT : ℕ := 512
/-- `E` (pair `513, 514`). -/
abbrev kE : ℕ := 513
/-- The step counter `r` of Phase M. -/
abbrev kR : ℕ := 515
/-- `Δ` (pair `516, 517`). -/
abbrev kDL : ℕ := 516
/-- `q` (pair `518, 519`). -/
abbrev kQ : ℕ := 518
/-- `pAj + r · 2d`, the row `r` of `Aj`. -/
abbrev kROW : ℕ := 520
/-- `2r`. -/
abbrev kOFF : ℕ := 521
/-- `σ` of the best row (pair `522, 523`). -/
abbrev kSB : ℕ := 522
/-- `ω` of the best row (pair `524, 525`). -/
abbrev kOB : ℕ := 524
/-- The row pointer of the best row. -/
abbrev kBP : ℕ := 526
/-- The flag of the scan (`0`: no row yet). -/
abbrev kFL : ℕ := 527
/-- Scratch pointer. -/
abbrev kP1 : ℕ := 528
/-- Scratch pointer. -/
abbrev kP2 : ℕ := 529
/-- Loop counter of the copy and gather loops. -/
abbrev kJ : ℕ := 530
/-- Length of the copy and gather loops. -/
abbrev kN : ℕ := 531
/-- Source pointer of the copy loop / table base of the gather loop. -/
abbrev kPS : ℕ := 532
/-- Source stride of the copy loop / offset of the gather loop. -/
abbrev kSS : ℕ := 533
/-- Destination pointer. -/
abbrev kPD : ℕ := 534
/-- Destination stride. -/
abbrev kSD : ℕ := 535
/-- Negation flag of the copy loop. -/
abbrev kNG : ℕ := 536
/-- Scratch pair `537, 538`. -/
abbrev kX : ℕ := 537
/-- Scratch register. -/
abbrev kA : ℕ := 539

/-! ### Index lemmas -/

theorem rowS_val (t k : ℕ) (c : Fin t) (s : Fin 2) :
    (((rowEquiv t k).symm (.inl (c, s)) : Fin (nRows t k)) : ℕ) = 2 * c + s := by
  have : (((rowEquiv t k).symm (.inl (c, s)) : Fin (nRows t k)) : ℕ) = s + 2 * c := rfl
  omega

theorem rowX_val (t k : ℕ) (c : Fin t) (j : Fin k) (b : Fin 3) :
    (((rowEquiv t k).symm (.inr ((c, j), b)) : Fin (nRows t k)) : ℕ) =
      2 * t + 3 * (c * k + j) + b := by
  have : (((rowEquiv t k).symm (.inr ((c, j), b)) : Fin (nRows t k)) : ℕ) =
      t * 2 + (b + 3 * (j + k * c)) := rfl
  rw [this]; ring

theorem colX_val (t k : ℕ) (c : Fin t) (j : Fin k) :
    (((colEquiv t k).symm (.inl (c, j)) : Fin (dimKKT t k)) : ℕ) = c * k + j := by
  have : (((colEquiv t k).symm (.inl (c, j)) : Fin (dimKKT t k)) : ℕ) = j + k * c := rfl
  rw [this]; ring

theorem colP_val (t k : ℕ) (c : Fin t) :
    (((colEquiv t k).symm (.inr c) : Fin (dimKKT t k)) : ℕ) = t * k + c := rfl

theorem dimKKT_eq (t k : ℕ) : dimKKT t k = t * k + t := by unfold dimKKT; ring

theorem nRows_eq (t k : ℕ) : nRows t k = 2 * t + 3 * (t * k) := by unfold nRows; ring

theorem div_mul_add_mod' (k a : ℕ) : a / k * k + a % k = a := Nat.div_add_mod' a k

/-- The row `2c + s` is `S_{c,s}`. -/
theorem finRow_S {t k c s : ℕ} (hc : c < t) (hs : s < 2) (h : 2 * c + s < nRows t k) :
    (⟨2 * c + s, h⟩ : Fin (nRows t k)) = (rowEquiv t k).symm (.inl (⟨c, hc⟩, ⟨s, hs⟩)) :=
  Fin.ext (rowS_val t k ⟨c, hc⟩ ⟨s, hs⟩).symm

/-- The row `2t + 3a + b` is the row `b` of `(a / k, a % k)`. -/
theorem finRow_X {t k a b : ℕ} (ha : a < t * k) (hb : b < 3) (h : 2 * t + 3 * a + b < nRows t k) :
    (⟨2 * t + 3 * a + b, h⟩ : Fin (nRows t k)) = (rowEquiv t k).symm
      (.inr ((⟨a / k, div_lt_of_lt_tk ha⟩, ⟨a % k, mod_lt_of_lt_tk ha⟩), ⟨b, hb⟩)) := by
  refine Fin.ext ?_
  rw [rowX_val]
  simp only
  rw [div_mul_add_mod']

/-- The column `v < tk` is `x_{v / k, v % k}`. -/
theorem finCol_X {t k v : ℕ} (hv : v < t * k) (h : v < dimKKT t k) :
    (⟨v, h⟩ : Fin (dimKKT t k)) = (colEquiv t k).symm
      (.inl (⟨v / k, div_lt_of_lt_tk hv⟩, ⟨v % k, mod_lt_of_lt_tk hv⟩)) := by
  refine Fin.ext ?_
  rw [colX_val]
  simp only
  rw [div_mul_add_mod']

/-- The column `tk + c` is `π_c`. -/
theorem finCol_P {t k v : ℕ} (hv : t * k ≤ v) (h : v < dimKKT t k) :
    (⟨v, h⟩ : Fin (dimKKT t k)) = (colEquiv t k).symm
      (.inr ⟨v - t * k, by rw [dimKKT_eq] at h; omega⟩) := by
  refine Fin.ext ?_
  rw [colP_val]
  simp only
  omega

/-! ### The KKT data on natural indices -/

variable (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ)

/-- The pattern on flat indices. -/
def Zf (a : ℕ) : Bool :=
  if h : a < I.t * I.k then kktZ I Xs ⟨a / I.k, div_lt_of_lt_tk h⟩ ⟨a % I.k, mod_lt_of_lt_tk h⟩
  else false

/-- The KKT matrix `G` on natural indices (`0` outside). -/
def Gf (i v : ℕ) : ℤ :=
  if h : i < nRows I.t I.k ∧ v < dimKKT I.t I.k then kktG I (kktZ I Xs) ⟨i, h.1⟩ ⟨v, h.2⟩ else 0

/-- The right-hand side `h` on natural indices. -/
def hf (i : ℕ) : ℤ := if h : i < nRows I.t I.k then kktH I ⟨i, h⟩ else 0

/-- `G` with `h` as the extra column `d`, as stored in memory. -/
def Gx (i v : ℕ) : ℤ :=
  if v < dimKKT I.t I.k then Gf I Xs i v else if v = dimKKT I.t I.k then hf I i else 0

/-- `h' = E h + 1`. -/
def hpf (i : ℕ) : ℤ := (bigE I.t I.k : ℤ) * hf I i + 1

/-- The start point `kktZn` on natural indices. -/
def ZnF₀ (v : ℕ) : ℤ := if h : v < dimKKT I.t I.k then kktZn I Xs ⟨v, h⟩ else 0

theorem Gf_fin (i : Fin (nRows I.t I.k)) (v : Fin (dimKKT I.t I.k)) :
    Gf I Xs i v = kktG I (kktZ I Xs) i v := by
  simp [Gf, i.2, v.2]

theorem hf_fin (i : Fin (nRows I.t I.k)) : hf I i = kktH I i := by simp [hf, i.2]

theorem ZnF₀_fin (v : Fin (dimKKT I.t I.k)) : ZnF₀ I Xs v = kktZn I Xs v := by simp [ZnF₀, v.2]

/-- The sign of the rows `S_{c,s}`. -/
theorem sgnS_val (s : Fin 2) : sgnS s = if (s : ℕ) = 0 then 1 else -1 := by
  fin_cases s <;> rfl

/-- **The rows `S_{c,s}`** (`2c + s`): `sgn_s` on the columns `x_{c,j}` and on the column `h`. -/
theorem Gx_S {c s : ℕ} (hc : c < I.t) (hs : s < 2) (v : ℕ) :
    Gx I Xs (2 * c + s) v =
      if c * I.k ≤ v ∧ v < c * I.k + I.k then (if s = 0 then 1 else -1)
      else if v = dimKKT I.t I.k then (if s = 0 then 1 else -1) else 0 := by
  have hM : 2 * c + s < nRows I.t I.k := by rw [nRows_eq]; omega
  have hd := dimKKT_eq I.t I.k
  have hck : c * I.k + I.k ≤ I.t * I.k := by
    have := Nat.mul_le_mul_right I.k (show c + 1 ≤ I.t by omega); rw [Nat.add_mul] at this; omega
  unfold Gx
  by_cases hv : v < dimKKT I.t I.k
  · simp only [hv, ↓reduceIte]
    unfold Gf
    rw [dite_eq_left_of_eq_true (eq_true ⟨hM, hv⟩), finRow_S hc hs hM]
    by_cases hvx : v < I.t * I.k
    · rw [finCol_X hvx hv]
      simp only [kktG, Matrix.of_apply, Equiv.apply_symm_apply, kktEntry, sgnS_val]
      have hk : 0 < I.k := Nat.pos_of_ne_zero fun h => by simp [h] at hvx
      have e : (⟨v / I.k, div_lt_of_lt_tk hvx⟩ : Fin I.t) = ⟨c, hc⟩ ↔
          c * I.k ≤ v ∧ v < c * I.k + I.k := by
        rw [Fin.ext_iff]
        simp only
        constructor
        · intro h; rw [← h]
          exact ⟨Nat.div_mul_le_self v I.k, by
            have := Nat.lt_div_mul_add (a := v) hk; linarith⟩
        · rintro ⟨h1, h2⟩
          exact le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hk).mpr (by
            rw [Nat.succ_mul]; omega))) ((Nat.le_div_iff_mul_le hk).mpr h1)
      by_cases hin : c * I.k ≤ v ∧ v < c * I.k + I.k
      · simp [e.mpr hin, hin]
      · simp [mt e.mp hin, hin, hv.ne]
    · rw [finCol_P (not_lt.mp hvx) hv]
      simp only [kktG, Matrix.of_apply, Equiv.apply_symm_apply, kktEntry]
      have : ¬ (c * I.k ≤ v ∧ v < c * I.k + I.k) := fun h => hvx (by omega)
      simp [this, hv.ne]
  · simp only [hv, ↓reduceIte]
    have : ¬ (c * I.k ≤ v ∧ v < c * I.k + I.k) := fun h => hv (by omega)
    simp only [this, ↓reduceIte]
    by_cases hvd : v = dimKKT I.t I.k
    · simp only [hvd, ↓reduceIte, hf, hM, ↓reduceDIte]
      rw [finRow_S hc hs hM]
      simp [kktH, kktRhs, sgnS_val]
    · simp [hvd]

/-- **The rows of `(c, j)`** (`2t + 3a + b`, `a = c k + j`):
`coefX · x_a + coefL · ((H x)_a − π_c) ≤ 0`, and `h = 0`. -/
theorem Gx_X {a b : ℕ} (ha : a < I.t * I.k) (hb : b < 3) (v : ℕ) :
    Gx I Xs (2 * I.t + 3 * a + b) v =
      if v < I.t * I.k then
        coefX (Zf I Xs a) ⟨b, hb⟩ * (if v = a then 1 else 0) +
          coefL (Zf I Xs a) ⟨b, hb⟩ * Hflat I a v
      else if v < dimKKT I.t I.k then
        -(coefL (Zf I Xs a) ⟨b, hb⟩ * if v = I.t * I.k + a / I.k then 1 else 0)
      else 0 := by
  have hM : 2 * I.t + 3 * a + b < nRows I.t I.k := by rw [nRows_eq]; omega
  have hd := dimKKT_eq I.t I.k
  have hk : 0 < I.k := Nat.pos_of_ne_zero fun h => by simp [h] at ha
  have hZ : Zf I Xs a = kktZ I Xs ⟨a / I.k, div_lt_of_lt_tk ha⟩ ⟨a % I.k, mod_lt_of_lt_tk ha⟩ := by
    simp [Zf, ha]
  unfold Gx
  by_cases hv : v < dimKKT I.t I.k
  · simp only [hv, ↓reduceIte]
    unfold Gf
    rw [dite_eq_left_of_eq_true (eq_true ⟨hM, hv⟩), finRow_X ha hb hM]
    by_cases hvx : v < I.t * I.k
    · rw [finCol_X hvx hv]
      simp only [kktG, Matrix.of_apply, Equiv.apply_symm_apply, kktEntry, hvx, ↓reduceIte, hZ]
      congr 1
      · congr 1
        have e : ((⟨v / I.k, div_lt_of_lt_tk hvx⟩ : Fin I.t) = ⟨a / I.k, div_lt_of_lt_tk ha⟩ ∧
            (⟨v % I.k, mod_lt_of_lt_tk hvx⟩ : Fin I.k) = ⟨a % I.k, mod_lt_of_lt_tk ha⟩) ↔ v = a := by
          simp only [Fin.ext_iff]
          constructor
          · rintro ⟨h1, h2⟩
            rw [← Nat.div_add_mod v I.k, ← Nat.div_add_mod a I.k, h1, h2]
          · rintro rfl; exact ⟨rfl, rfl⟩
        by_cases hva : v = a
        · simp [hva]
        · have := mt e.mp hva
          simp only [hva, ↓reduceIte]
          by_cases h1 : (⟨v / I.k, div_lt_of_lt_tk hvx⟩ : Fin I.t) = ⟨a / I.k, div_lt_of_lt_tk ha⟩
          · simp only [h1, ↓reduceIte]
            have h2 : ¬ ((⟨v % I.k, mod_lt_of_lt_tk hvx⟩ : Fin I.k) = ⟨a % I.k, mod_lt_of_lt_tk ha⟩) :=
              fun h2 => this ⟨h1, h2⟩
            simp [h2]
          · simp [h1]
      · congr 1
        simp only [Hflat, ha, hvx, and_self, ↓reduceDIte]
    · rw [finCol_P (not_lt.mp hvx) hv]
      simp only [kktG, Matrix.of_apply, Equiv.apply_symm_apply, kktEntry, hvx, ↓reduceIte, hZ]
      congr 2
      have e : ((⟨v - I.t * I.k, by omega⟩ : Fin I.t) = ⟨a / I.k, div_lt_of_lt_tk ha⟩) ↔
          v = I.t * I.k + a / I.k := by
        simp only [Fin.ext_iff]; omega
      by_cases h : v = I.t * I.k + a / I.k
      · simp [h]
      · simp [mt e.mp h, h]
  · simp only [hv, ↓reduceIte]
    have h1 : ¬ v < I.t * I.k := by omega
    simp only [h1, ↓reduceIte]
    by_cases hvd : v = dimKKT I.t I.k
    · simp only [hvd, ↓reduceIte, hf, hM, ↓reduceDIte]
      rw [finRow_X ha hb hM]
      simp [kktH, kktRhs]
    · simp [hvd]

/-- `h' = E h + 1` on the rows `S_{c,s}`. -/
theorem hpf_S {c s : ℕ} (hc : c < I.t) (hs : s < 2) :
    hpf I (2 * c + s) = (bigE I.t I.k : ℤ) * (if s = 0 then 1 else -1) + 1 := by
  have h := Gx_S I (fun _ _ => 0) hc hs (dimKKT I.t I.k)
  have hd := dimKKT_eq I.t I.k
  have hn : ¬ (c * I.k ≤ dimKKT I.t I.k ∧ dimKKT I.t I.k < c * I.k + I.k) := by
    have := Nat.mul_le_mul_right I.k (show c + 1 ≤ I.t by omega); rw [Nat.add_mul] at this
    omega
  simp only [Gx, lt_irrefl, ↓reduceIte, hn] at h
  simp only [hpf, h]

/-- `h' = 1` on the rows of `(c, j)`. -/
theorem hpf_X {a b : ℕ} (ha : a < I.t * I.k) (hb : b < 3) : hpf I (2 * I.t + 3 * a + b) = 1 := by
  have h := Gx_X I (fun _ _ => 0) ha hb (dimKKT I.t I.k)
  have hd := dimKKT_eq I.t I.k
  have h1 : ¬ dimKKT I.t I.k < I.t * I.k := by omega
  simp only [Gx, lt_irrefl, ↓reduceIte, h1] at h
  simp [hpf, h]

/-- The start point: `x = Xs` on the first `tk` coordinates, `π = I.pi Xs` after them. -/
theorem ZnF₀_x {v : ℕ} (hv : v < I.t * I.k) : ZnF₀ I Xs v = flat Xs v := by
  have hd := dimKKT_eq I.t I.k
  have hv' : v < dimKKT I.t I.k := by omega
  simp only [ZnF₀, hv', ↓reduceDIte, flat, hv]
  rw [finCol_X hv hv']
  simp [kktZn]

theorem ZnF₀_p {c : ℕ} (hc : c < I.t) : ZnF₀ I Xs (I.t * I.k + c) = I.pi Xs ⟨c, hc⟩ := by
  have hd := dimKKT_eq I.t I.k
  have hv' : I.t * I.k + c < dimKKT I.t I.k := by omega
  simp only [ZnF₀, hv', ↓reduceDIte]
  rw [finCol_P (Nat.le_add_right _ _) hv']
  simp [kktZn]

end STACS2027.Runtimes.QPRam.Kmo

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### Memory helpers -/

theorem smem_zero {m : ℕ → ℕ} {a : ℕ} (h0 : m a = 0) (h1 : m (a + 1) = 0) : SMem m a 0 := by
  simp [SMem, sgnBit, h0, h1]

theorem sarr_of_eq {m m' : ℕ → ℕ} {b s n : ℕ} {f : ℕ → ℤ} (h : SArr m b s n f)
    (hm : ∀ j < n, m' (b + j * s) = m (b + j * s) ∧ m' (b + j * s + 1) = m (b + j * s + 1)) :
    SArr m' b s n f := fun j hj => ⟨(hm j hj).1.trans (h j hj).1, (hm j hj).2.trans (h j hj).2⟩

theorem entry_lt {b s n j : ℕ} (hs : 2 ≤ s) (hj : j < n) : b + j * s + 1 < b + n * s := by
  have := Nat.mul_le_mul_right s (show j + 1 ≤ n by omega)
  rw [Nat.add_mul] at this; omega

/-- An array survives a memory change that keeps the cells of `[lo, hi) ⊇` its block. -/
theorem sarr_of_on {m m' : ℕ → ℕ} {b s n lo hi : ℕ} {f : ℕ → ℤ} (h : SArr m b s n f) (hs : 2 ≤ s)
    (hlo : lo ≤ b) (hhi : b + n * s ≤ hi) (hm : ∀ a, lo ≤ a → a < hi → m' a = m a) :
    SArr m' b s n f :=
  sarr_of_eq h fun j hj => by
    have := entry_lt (b := b) hs hj
    exact ⟨hm _ (by omega) (by omega), hm _ (by omega) (by omega)⟩

theorem sarr_congr {m : ℕ → ℕ} {b s n : ℕ} {f g : ℕ → ℤ} (h : SArr m b s n f)
    (hfg : ∀ j < n, f j = g j) : SArr m b s n g := fun j hj => hfg j hj ▸ h j hj

theorem sarr_mono {m : ℕ → ℕ} {b s n n' : ℕ} {f : ℕ → ℤ} (h : SArr m b s n f) (hn : n' ≤ n) :
    SArr m b s n' f := fun j hj => h j (by omega)

/-- A zero region holds the zero array. -/
theorem sarr_zero {m : ℕ → ℕ} {b s n lo hi : ℕ} (hs : 2 ≤ s) (hlo : lo ≤ b) (hhi : b + n * s ≤ hi)
    (hz : ∀ a, lo ≤ a → a < hi → m a = 0) : SArr m b s n (fun _ => 0) := fun j hj => by
  have := entry_lt (b := b) hs hj
  exact smem_zero (hz _ (by omega) (by omega)) (hz _ (by omega) (by omega))

/-- Cells that are not entries of a (strided) write keep their values. -/
theorem wrArr_of_ne {m₀ : ℕ → ℕ} {b s : ℕ} {f : ℕ → ℤ} :
    ∀ {n i : ℕ}, (∀ j < n, i ≠ b + j * s ∧ i ≠ b + j * s + 1) → wrArr m₀ b s f n i = m₀ i
  | 0, _, _ => rfl
  | n + 1, i, h => by
    rw [wrArr_succ, sw_apply_of_ne _ (h n (by omega)).1 (h n (by omega)).2]
    exact wrArr_of_ne fun j hj => h j (by omega)

/-- Cells outside `[lo, hi) ⊇` the block of a write keep their values. -/
theorem wrArr_of_out' {m₀ : ℕ → ℕ} {b s n i : ℕ} {f : ℕ → ℤ} (hs : 2 ≤ s)
    (hi : i < b ∨ b + n * s ≤ i) : wrArr m₀ b s f n i = m₀ i := wrArr_of_out hs hi

/-- A store of a pair keeps the cells `≠ a, a + 1`. -/
theorem sw_of_out {m : ℕ → ℕ} {a i : ℕ} (z : ℤ) (h : i < a ∨ a + 2 ≤ i) : sw m a z i = m i :=
  sw_apply_of_ne _ (by omega) (by omega)

/-- `(i + 1) s ≤ n s` for `i < n`. -/
theorem succ_mul_le {i n : ℕ} (s : ℕ) (h : i < n) : i * s + s ≤ n * s := by
  have := Nat.mul_le_mul_right s (show i + 1 ≤ n by omega); rw [Nat.add_mul] at this; omega

/-! ### The states of Phase M on natural indices -/

section States

variable {M d r : ℕ}

/-- The tight rows on natural indices. -/
def TF (s : MState M d r) (a : ℕ) : ℕ := if h : a < r then (s.T ⟨a, h⟩ : ℕ) else 0

/-- The adjugate on natural indices. -/
def AjF (s : MState M d r) (a b : ℕ) : ℤ := if h : a < r ∧ b < r then s.Aj ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

/-- The numerators of the point on natural indices. -/
def ZnF (s : MState M d r) (v : ℕ) : ℤ := if h : v < d then s.Zn ⟨v, h⟩ else 0

theorem TF_fin (s : MState M d r) (a : Fin r) : TF s a = s.T a := by simp [TF, a.2]

theorem AjF_fin (s : MState M d r) (a b : Fin r) : AjF s a b = s.Aj a b := by
  simp [AjF, a.2, b.2]

theorem ZnF_fin (s : MState M d r) (v : Fin d) : ZnF s v = s.Zn v := by simp [ZnF, v.2]

theorem TF_lt (s : MState M d r) {a : ℕ} (ha : a < r) : TF s a < M := by
  simp only [TF, ha, ↓reduceDIte]; exact (s.T _).2

end States

/-! ### Sums over `Fin` and `range` -/

theorem sum_fin_range {n : ℕ} (f : ℕ → ℤ) : ∑ j : Fin n, f j = ∑ j ∈ Finset.range n, f j :=
  Fin.sum_univ_eq_sum_range f n

theorem mulVec_eq_fin {n : ℕ} (A : ℕ → ℕ → ℤ) (x : ℕ → ℤ) (i : ℕ) :
    mulVec A x n i = ∑ j : Fin n, A i j * x j := by
  rw [mulVec, sum_fin_range (fun j => A i j * x j)]

end STACS2027.Runtimes.QPRam.Kmo
