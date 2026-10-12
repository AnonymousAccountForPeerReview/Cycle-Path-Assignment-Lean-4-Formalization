module

public import Runtimes.ConvexQP.RAM.KmoInv
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: one step of Phase M on natural indices

For a state `s` after `r` steps (`r + 1 ≤ d`) and the blocking row `i*`, the vectors the RAM
computes (`colf`, `uf = Aj col`, `wf`, `omf = G w`, `gzf = G Zn`, `sgf = σ`, `vf = ρᵀ Aj`) agree
with `mDir`, `mOmega`, `mSigma` and the parts of `mNext` (`Move.lean`), and the new state
`mNext … i*` is described entry by entry (`AjF_next_*`, `ZnF_next`, `TF_next_*`, `q_next`,
`Δ_next`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP
open scoped Matrix

variable (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) {r : ℕ} (s : MState (MM I) (dd I) r)

/-- The column `r` of `G` on the rows `T`. -/
def colf (a : ℕ) : ℤ := Gx I Xs (TF s a) r

/-- `u = Aj col`. -/
def uf (a : ℕ) : ℤ := mulVec (AjF s) (colf I Xs s) r a

/-- The direction `w`: `−u` below `r`, `Δ` at `r`, `0` above. -/
def wf (b : ℕ) : ℤ := if b < r then -uf I Xs s b else if b = r then s.Δ else 0

/-- `ω = G w`. -/
def omf (i : ℕ) : ℤ := mulVec (Gx I Xs) (wf I Xs s) (dd I) i

/-- `G Zn`. -/
def gzf (i : ℕ) : ℤ := mulVec (Gx I Xs) (ZnF s) (dd I) i

/-- `σ` as `linCore false` computes it: `(−E) (G Zn)_i + q h'_i`, divided by `1`. -/
def sgf (i : ℕ) : ℤ := linNew false (-(bigE I.t I.k : ℤ)) (s.q : ℤ) 1 (gzf I Xs s) (hpf I) i

/-- `v = ρᵀ Aj` for the row `ib` (the transposed product of `mvCore`). -/
def vf (ib : ℕ) (b : ℕ) : ℤ := mulVec (fun i j => AjF s j i) (fun j => Gx I Xs ib j) r b

variable {I Xs s}

theorem Gx_lt {i v : ℕ} (hi : i < MM I) (hv : v < dd I) :
    Gx I Xs i v = KG I Xs ⟨i, hi⟩ ⟨v, hv⟩ := by
  simp [Gx, Gf, hv, hi]

theorem castLE_last_val {r d : ℕ} (hr : r + 1 ≤ d) : (Fin.castLE hr (Fin.last r) : ℕ) = r := rfl

theorem colf_eq (hr : r + 1 ≤ dd I) {a : ℕ} (ha : a < r) :
    colf I Xs s a = KG I Xs (s.T ⟨a, ha⟩) (Fin.castLE hr (Fin.last r)) := by
  have h1 := TF_lt s ha
  rw [colf, Gx_lt h1 (by omega)]
  congr 1
  exact Fin.ext (by simp [TF, ha])

theorem uf_eq (hr : r + 1 ≤ dd I) {a : ℕ} (ha : a < r) :
    uf I Xs s a = (s.Aj *ᵥ fun a => KG I Xs (s.T a) (Fin.castLE hr (Fin.last r))) ⟨a, ha⟩ := by
  rw [uf, mulVec_eq_fin, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [colf_eq hr j.2]
  simp [AjF, ha, j.2]

theorem wf_eq (hr : r + 1 ≤ dd I) {b : ℕ} (hb : b < dd I) :
    wf I Xs s b = mDir (KG I Xs) hr s ⟨b, hb⟩ := by
  unfold wf mDir extend
  by_cases hbr : b < r
  · have e : (⟨b, by omega⟩ : Fin (r + 1)) = Fin.castSucc ⟨b, hbr⟩ := rfl
    simp only [hbr, ↓reduceIte, show b < r + 1 by omega, ↓reduceDIte, e, Fin.lastCases_castSucc]
    rw [uf_eq hr hbr]
  · by_cases hbe : b = r
    · subst hbe
      have e : (⟨b, by omega⟩ : Fin (b + 1)) = Fin.last b := rfl
      simp only [lt_irrefl, ↓reduceIte, Nat.lt_succ_self, ↓reduceDIte, e, Fin.lastCases_last]
    · simp only [hbr, hbe, ↓reduceIte, show ¬ b < r + 1 by omega, ↓reduceDIte]

theorem omf_eq (hr : r + 1 ≤ dd I) {i : ℕ} (hi : i < MM I) :
    omf I Xs s i = mOmega (KG I Xs) hr s ⟨i, hi⟩ := by
  rw [omf, mulVec_eq_fin, mOmega, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Gx_lt hi v.2, wf_eq hr v.2]

theorem gzf_eq {i : ℕ} (hi : i < MM I) : gzf I Xs s i = (KG I Xs *ᵥ s.Zn) ⟨i, hi⟩ := by
  rw [gzf, mulVec_eq_fin, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Gx_lt hi v.2, ZnF_fin]

theorem sgf_eq {i : ℕ} (hi : i < MM I) :
    sgf I Xs s i = mSigma (KG I Xs) (kktH I) (bigE I.t I.k) s ⟨i, hi⟩ := by
  rw [sgf, linNew, rnd, gzf_eq hi, mSigma, hpf]
  simp only [Bool.false_eq_true, ↓reduceIte, Int.ediv_one]
  rw [show hf I i = kktH I ⟨i, hi⟩ by simp [hf, hi]]
  ring

theorem vf_eq (hr : r + 1 ≤ dd I) {ib : ℕ} (hib : ib < MM I) {b : ℕ} (hb : b < r) :
    vf I Xs s ib b =
      ((fun b => KG I Xs ⟨ib, hib⟩ (Fin.castLE (Nat.le_of_succ_le hr) b)) ᵥ* s.Aj) ⟨b, hb⟩ := by
  rw [vf, mulVec_eq_fin, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Gx_lt hib (by have := j.2; omega)]
  simp only [AjF, j.2, hb, and_self, ↓reduceDIte]
  rw [mul_comm]
  rfl

/-! ### The new state -/

variable (I Xs s)

/-- The new state `mNext … i*`. -/
abbrev nxt (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) : MState (MM I) (dd I) (r + 1) :=
  mNext (KG I Xs) (kktH I) (bigE I.t I.k) hr s ib

variable {I Xs s}

theorem Δ_next (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) :
    (nxt I Xs s hr ib).Δ = mOmega (KG I Xs) hr s ib := by
  rw [mOmega_apply]; simp only [nxt, mNext, mul_comm]

theorem q_next (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) (hω : 0 < mOmega (KG I Xs) hr s ib) :
    ((nxt I Xs s hr ib).q : ℤ) = (bigE I.t I.k : ℤ) * s.q * mOmega (KG I Xs) hr s ib := by
  simp only [nxt, mNext]
  push_cast
  rw [Int.toNat_of_nonneg hω.le]

theorem TF_next_lt (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) {a : ℕ} (ha : a < r) :
    TF (nxt I Xs s hr ib) a = TF s a := by
  have e : (⟨a, by omega⟩ : Fin (r + 1)) = Fin.castSucc ⟨a, ha⟩ := rfl
  simp only [TF, ha, show a < r + 1 by omega, ↓reduceDIte, nxt, mNext, e, Fin.lastCases_castSucc]

theorem TF_next_r (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) : TF (nxt I Xs s hr ib) r = ib := by
  have e : (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r := rfl
  simp only [TF, Nat.lt_succ_self, ↓reduceDIte, nxt, mNext, e, Fin.lastCases_last]

theorem ZnF_next (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) {v : ℕ} (hv : v < dd I) :
    ZnF (nxt I Xs s hr ib) v = axNew false ((bigE I.t I.k : ℤ) * omf I Xs s ib) (sgf I Xs s ib) 1 1
      (ZnF s) (wf I Xs s) v := by
  rw [axNew, rnd, omf_eq hr ib.2, sgf_eq ib.2, wf_eq hr hv]
  simp only [ZnF, hv, ↓reduceDIte, nxt, mNext, Bool.false_eq_true, ↓reduceIte, one_mul,
    Int.ediv_one]

theorem AjF_next_cc (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) {a b : ℕ} (ha : a < r) (hb : b < r) :
    AjF (nxt I Xs s hr ib) a b =
      r1New false (omf I Xs s ib) 1 s.Δ (AjF s) (uf I Xs s) (vf I Xs s ib) a b := by
  have ea : (⟨a, by omega⟩ : Fin (r + 1)) = Fin.castSucc ⟨a, ha⟩ := rfl
  have eb : (⟨b, by omega⟩ : Fin (r + 1)) = Fin.castSucc ⟨b, hb⟩ := rfl
  rw [r1New, rnd, omf_eq hr ib.2, uf_eq hr ha, vf_eq hr ib.2 hb, ← Δ_next hr ib]
  simp only [AjF, ha, hb, show a < r + 1 by omega, show b < r + 1 by omega, and_self,
    ↓reduceDIte, ea, eb, nxt, mNext, border_cc, Matrix.of_apply, Bool.false_eq_true, ↓reduceIte]
  ring_nf

theorem AjF_next_cl (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) {a : ℕ} (ha : a < r) :
    AjF (nxt I Xs s hr ib) a r = -uf I Xs s a := by
  have ea : (⟨a, by omega⟩ : Fin (r + 1)) = Fin.castSucc ⟨a, ha⟩ := rfl
  have eb : (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r := rfl
  rw [uf_eq hr ha]
  simp only [AjF, show a < r + 1 by omega, Nat.lt_succ_self, and_self, ↓reduceDIte, ea, eb, nxt,
    mNext, border_cl, Pi.neg_apply]

theorem AjF_next_lc (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) {b : ℕ} (hb : b < r) :
    AjF (nxt I Xs s hr ib) r b = -vf I Xs s ib b := by
  have ea : (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r := rfl
  have eb : (⟨b, by omega⟩ : Fin (r + 1)) = Fin.castSucc ⟨b, hb⟩ := rfl
  rw [vf_eq hr ib.2 hb]
  simp only [AjF, show b < r + 1 by omega, Nat.lt_succ_self, and_self, ↓reduceDIte, ea, eb, nxt,
    mNext, border_lc, Pi.neg_apply]

theorem AjF_next_ll (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) :
    AjF (nxt I Xs s hr ib) r r = s.Δ := by
  have ea : (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r := rfl
  simp only [AjF, Nat.lt_succ_self, and_self, ↓reduceDIte, ea, nxt, mNext, border_ll]

end STACS2027.Runtimes.QPRam.Kmo
