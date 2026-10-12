module

public import Runtimes.ConvexQP.Border
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic

/-!
# Lemma 16, Part C: moving to a vertex (Phase M)

Setting: an integer system `G z ≤ h`
(`G : Matrix (Fin M) (Fin d) ℤ`), a scale `E` (`ε = 1/E`) and an approximate solution
`z̃ = Zn₀/q₀` of the relaxed system `G z ≤ h + ε`. Phase M moves the point inside
`{G z ≤ h + ε}` along kernel directions until `d` linearly independent rows are tight, keeping
the rows `T`, the determinant `Δ = det B_T` and the adjugate `Aj = adj B_T` of the square
submatrix `B_T` (rows `T`, columns `0, …, r−1`), updated by the bordered formulas of
`Border.lean`; at the end `z* = Aj h_T / Δ`.

* `argMinRatio ω σ`: the least index minimizing `σ_i/ω_i` over the rows with `ω_i > 0`
  (`argMinRatio_some`).
* `moveStep`/`moveAux`/`moveRun`: the steps (M1)–(M4), exactly as the RAM computes them
  (integers only; the new adjugate by exact division).
* `Inv`: the invariant (I1)–(I3), stated for the real point `Zn/q`.
* **C3** (`moveStep_inv`, `moveStep_isSome`): one step preserves the invariant, and under
  boundedness (`Bdd G`: `G w ≤ 0 → w = 0`) a step is always possible.
* **C4** (`moveRun_exact`): if `|G_{ab}| ≤ A₀` (`A₀ ≥ 1`), `E ≥ 2(d²+1)·d!·A₀^{d+1}`, `Bdd G`
  and `G z̃ ≤ h + 1/E`, then Phase M ends with `Δ ≠ 0` and `G z* ≤ h` (Cramer, `Matrix.det_le`).
* **Magnitudes** (Phase M; `moveAux_bounds`, `moveAux_Zn_bound`): `|Δ|`, `|Aj_{ab}|`
  `≤ r!·A₀^r`, `q_r ≤ q₀ (E·d!·A₀^d)^r`, and `|Zn_v| ≤ B·q` whenever `B` bounds the coordinates
  on `{G z ≤ h + ε}`.
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Matrix Finset

variable {M d : ℕ}

/-! ### The blocking row: least index minimizing `σ_i / ω_i` over `ω_i > 0` -/

/-- One step of the scan for the blocking row (ties keep the earlier row). -/
def amStep (ω σ : Fin M → ℤ) (acc : Option (Fin M)) (i : Fin M) : Option (Fin M) :=
  if 0 < ω i then
    match acc with
    | none => some i
    | some b => if σ i * ω b < σ b * ω i then some i else some b
  else acc

/-- The least row index minimizing `σ_i / ω_i` among the rows with `ω_i > 0` (`none` if there is
no such row); ratios are compared by cross-multiplication. -/
def argMinRatio (ω σ : Fin M → ℤ) : Option (Fin M) :=
  (List.finRange M).foldl (amStep ω σ) none

/-- The invariant of the scan over the rows in `S`. -/
def AmInv (ω σ : Fin M → ℤ) (acc : Option (Fin M)) (S : Fin M → Prop) : Prop :=
  (acc = none → ∀ i, S i → ω i ≤ 0) ∧
    ∀ b, acc = some b → 0 < ω b ∧ ∀ j, S j → 0 < ω j → σ b * ω j ≤ σ j * ω b

theorem amStep_inv {ω σ : Fin M → ℤ} {acc : Option (Fin M)} {S : Fin M → Prop}
    (h : AmInv ω σ acc S) (x : Fin M) :
    AmInv ω σ (amStep ω σ acc x) (fun i => S i ∨ i = x) := by
  unfold amStep
  by_cases hx : 0 < ω x
  · simp only [hx, ↓reduceIte]
    cases acc with
    | none =>
      refine ⟨fun h' => by simp at h', fun b hb => ?_⟩
      simp only [Option.some.injEq] at hb
      subst hb
      refine ⟨hx, fun j hj hjpos => ?_⟩
      rcases hj with hj | rfl
      · exact absurd (h.1 rfl j hj) (not_le.mpr hjpos)
      · exact le_refl _
    | some b =>
      obtain ⟨hb0, hbmin⟩ := h.2 b rfl
      by_cases hlt : σ x * ω b < σ b * ω x
      · simp only [hlt, ↓reduceIte]
        refine ⟨fun h' => by simp at h', fun b' hb' => ?_⟩
        simp only [Option.some.injEq] at hb'
        subst hb'
        refine ⟨hx, fun j hj hjpos => ?_⟩
        rcases hj with hj | rfl
        · have h1 := hbmin j hj hjpos
          have h2 : σ x * ω b * ω j < σ b * ω x * ω j := mul_lt_mul_of_pos_right hlt hjpos
          have h3 : σ b * ω j * ω x ≤ σ j * ω b * ω x := mul_le_mul_of_nonneg_right h1 hx.le
          have h4 : σ x * ω j * ω b < σ j * ω x * ω b := by nlinarith
          exact (lt_of_mul_lt_mul_right h4 hb0.le).le
        · exact le_refl _
      · simp only [hlt, ↓reduceIte]
        refine ⟨fun h' => by simp at h', fun b' hb' => ?_⟩
        simp only [Option.some.injEq] at hb'
        subst hb'
        refine ⟨hb0, fun j hj hjpos => ?_⟩
        rcases hj with hj | rfl
        · exact hbmin j hj hjpos
        · exact not_lt.mp hlt
  · simp only [hx, ↓reduceIte]
    refine ⟨fun h' i hi => ?_, fun b hb => ?_⟩
    · rcases hi with hi | rfl
      · exact h.1 h' i hi
      · exact not_lt.mp hx
    · obtain ⟨hb0, hbmin⟩ := h.2 b hb
      refine ⟨hb0, fun j hj hjpos => ?_⟩
      rcases hj with hj | rfl
      · exact hbmin j hj hjpos
      · exact absurd hjpos hx

theorem foldl_amInv (ω σ : Fin M → ℤ) :
    ∀ (l : List (Fin M)) (acc : Option (Fin M)) (S : Fin M → Prop), AmInv ω σ acc S →
      AmInv ω σ (l.foldl (amStep ω σ) acc) (fun i => S i ∨ i ∈ l)
  | [], acc, S, h => by
    simp only [List.foldl_nil, List.not_mem_nil, or_false]
    exact h
  | x :: l, acc, S, h => by
    have h' := foldl_amInv ω σ l _ _ (amStep_inv h x)
    simp only [List.foldl_cons]
    refine ⟨fun hn i hi => h'.1 hn i ?_, fun b hb => ?_⟩
    · simp only [List.mem_cons] at hi
      rcases hi with hi | hi | hi
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · obtain ⟨hb0, hbmin⟩ := h'.2 b hb
      refine ⟨hb0, fun j hj hjpos => hbmin j ?_ hjpos⟩
      simp only [List.mem_cons] at hj
      rcases hj with hj | hj | hj
      · exact Or.inl (Or.inl hj)
      · exact Or.inl (Or.inr hj)
      · exact Or.inr hj

/-- If some `ω_i > 0`, the scan returns a row `i` with `ω_i > 0` minimizing `σ_i/ω_i`. -/
theorem argMinRatio_some (ω σ : Fin M → ℤ) (hpos : ∃ i, 0 < ω i) :
    ∃ i, argMinRatio ω σ = some i ∧ 0 < ω i ∧ ∀ j, 0 < ω j → σ i * ω j ≤ σ j * ω i := by
  have h := foldl_amInv ω σ (List.finRange M) none (fun _ => False)
    ⟨fun _ _ hi => hi.elim, fun _ hb => by simp at hb⟩
  unfold argMinRatio
  cases hr : (List.finRange M).foldl (amStep ω σ) none with
  | none =>
    rw [hr] at h
    obtain ⟨i, hi⟩ := hpos
    exact absurd hi (not_lt.mpr (h.1 rfl i (Or.inr (List.mem_finRange i))))
  | some i =>
    rw [hr] at h
    obtain ⟨hi0, himin⟩ := h.2 i rfl
    exact ⟨i, rfl, hi0, fun j hj => himin j (Or.inr (List.mem_finRange j)) hj⟩

/-- Any row returned by the scan has `ω_i > 0` and minimizes `σ_i/ω_i`. -/
theorem argMinRatio_spec {ω σ : Fin M → ℤ} {i : Fin M} (h : argMinRatio ω σ = some i) :
    0 < ω i ∧ ∀ j, 0 < ω j → σ i * ω j ≤ σ j * ω i := by
  have h' := foldl_amInv ω σ (List.finRange M) none (fun _ => False)
    ⟨fun _ _ hi => hi.elim, fun _ hb => by simp at hb⟩
  unfold argMinRatio at h
  rw [h] at h'
  obtain ⟨hi0, himin⟩ := h'.2 i rfl
  exact ⟨hi0, fun j hj => himin j (Or.inr (List.mem_finRange j)) hj⟩

/-! ### Vectors on the first `r` coordinates and square submatrices -/

/-- Extension by zero of a vector on the first `r` coordinates of `Fin d`. -/
def extend {R : Type*} [Zero R] {r : ℕ} (y : Fin r → R) : Fin d → R :=
  fun v => if h : (v : ℕ) < r then y ⟨v, h⟩ else 0

theorem sum_mul_extend {R : Type*} [CommSemiring R] {r : ℕ} (hr : r ≤ d) (g : Fin d → R)
    (y : Fin r → R) : ∑ v, g v * extend y v = ∑ b, g (Fin.castLE hr b) * y b := by
  have hsub : (Finset.univ.map (Fin.castLEEmb hr)) ⊆ (Finset.univ : Finset (Fin d)) :=
    Finset.subset_univ _
  rw [← Finset.sum_subset hsub (fun v _ hv => ?_), Finset.sum_map]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [extend, Fin.castLEEmb]
  · have : ¬ (v : ℕ) < r := by
      intro hlt
      exact hv (Finset.mem_map.mpr ⟨⟨v, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    simp [extend, this]

/-- The square submatrix `B_T` of `G`: rows `T`, columns `0, …, r − 1`. -/
def subB (G : Matrix (Fin M) (Fin d) ℤ) {r : ℕ} (hr : r ≤ d) (T : Fin r → Fin M) :
    Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun a b => G (T a) (Fin.castLE hr b)

/-- Appending a row and the next column borders the submatrix. -/
theorem subB_snoc (G : Matrix (Fin M) (Fin d) ℤ) {r : ℕ} (hr : r + 1 ≤ d) (T : Fin r → Fin M)
    (i : Fin M) :
    subB G hr (Fin.lastCases (motive := fun _ => Fin M) i T) =
      border (subB G (Nat.le_of_succ_le hr) T) (fun a => G (T a) (Fin.castLE hr (Fin.last r)))
        (fun b => G i (Fin.castLE (Nat.le_of_succ_le hr) b)) (G i (Fin.castLE hr (Fin.last r))) := by
  ext a b
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;> simp [subB]

/-! ### The state and the steps (M1)–(M4) -/

/-- The state of Phase M after `r` steps: the tight rows `T`, the adjugate `Aj` and the
determinant `Δ` of `B_T`, and the current point `Zn / q`. -/
structure MState (M d r : ℕ) where
  /-- The rows made tight so far. -/
  T : Fin r → Fin M
  /-- The adjugate of `B_T`. -/
  Aj : Matrix (Fin r) (Fin r) ℤ
  /-- The determinant of `B_T`. -/
  Δ : ℤ
  /-- The numerators of the current point. -/
  Zn : Fin d → ℤ
  /-- The common denominator of the current point. -/
  q : ℕ

/-- The initial state: no tight rows, `Δ = 1`, the point `Zn₀ / q₀`. -/
def MState.init (Zn₀ : Fin d → ℤ) (q₀ : ℕ) : MState M d 0 :=
  ⟨Fin.elim0, 0, 1, Zn₀, q₀⟩

variable (G : Matrix (Fin M) (Fin d) ℤ) (h : Fin M → ℤ) (E : ℕ)

/-- (M1) The kernel direction: `w_l = Δ`, `w_{J_b} = −(Aj col)_b`, `0` elsewhere, with `l = r`
the next column and `col = (G_{T_a, l})_a`. -/
def mDir {r : ℕ} (hr : r + 1 ≤ d) (s : MState M d r) : Fin d → ℤ :=
  extend (Fin.lastCases (motive := fun _ => ℤ) s.Δ
    fun b => -(s.Aj *ᵥ fun a => G (s.T a) (Fin.castLE hr (Fin.last r))) b)

/-- (M2) `ω = G w`. -/
def mOmega {r : ℕ} (hr : r + 1 ≤ d) (s : MState M d r) : Fin M → ℤ := G *ᵥ mDir G hr s

/-- (M2) `σ_i = (E h_i + 1) q − E (G Zn)_i` (`= E q (h_i + ε − (G z)_i)`). -/
def mSigma {r : ℕ} (s : MState M d r) : Fin M → ℤ :=
  fun i => ((E : ℤ) * h i + 1) * s.q - E * (G *ᵥ s.Zn) i

/-- (M3), (M4) The next state when the blocking row is `i`. -/
def mNext {r : ℕ} (hr : r + 1 ≤ d) (s : MState M d r) (i : Fin M) : MState M d (r + 1) :=
  let col : Fin r → ℤ := fun a => G (s.T a) (Fin.castLE hr (Fin.last r))
  let ρ : Fin r → ℤ := fun b => G i (Fin.castLE (Nat.le_of_succ_le hr) b)
  let δ : ℤ := G i (Fin.castLE hr (Fin.last r))
  let Δ' : ℤ := δ * s.Δ - ρ ⬝ᵥ (s.Aj *ᵥ col)
  { T := Fin.lastCases (motive := fun _ => Fin M) i s.T
    Aj := border (Matrix.of fun a b => (Δ' * s.Aj a b + (s.Aj *ᵥ col) a * (ρ ᵥ* s.Aj) b) / s.Δ)
      (-(s.Aj *ᵥ col)) (-(ρ ᵥ* s.Aj)) s.Δ
    Δ := Δ'
    Zn := fun v => (E : ℤ) * mOmega G hr s i * s.Zn v + mSigma G h E s i * mDir G hr s v
    q := E * s.q * (mOmega G hr s i).toNat }

/-- One step of Phase M (`none` if no row blocks the direction, impossible under `Bdd`). -/
def moveStep {r : ℕ} (hr : r + 1 ≤ d) (s : MState M d r) : Option (MState M d (r + 1)) :=
  (argMinRatio (mOmega G hr s) (mSigma G h E s)).map (mNext G h E hr s)

/-- The first `r` steps of Phase M from `Zn₀ / q₀`. -/
def moveAux (Zn₀ : Fin d → ℤ) (q₀ : ℕ) : (r : ℕ) → r ≤ d → Option (MState M d r)
  | 0, _ => some (MState.init Zn₀ q₀)
  | r + 1, hr => (moveAux Zn₀ q₀ r (Nat.le_of_succ_le hr)).bind (moveStep G h E hr)

/-- Phase M: `d` steps. -/
def moveRun (Zn₀ : Fin d → ℤ) (q₀ : ℕ) : Option (MState M d d) :=
  moveAux G h E Zn₀ q₀ d le_rfl

/-- The numerators `Aj h_T` of the final vertex `z* = Aj h_T / Δ`. -/
def zNum (s : MState M d d) : Fin d → ℤ := s.Aj *ᵥ fun a => h (s.T a)

/-! ### Real values -/

/-- The real point `Zn / q`. -/
noncomputable def ptZ (Zn : Fin d → ℤ) (q : ℕ) : Fin d → ℝ := fun v => (Zn v : ℝ) / q

/-- `(G z)_i` for a real point `z`. -/
noncomputable def rowVal (i : Fin M) (z : Fin d → ℝ) : ℝ := ∑ v, (G i v : ℝ) * z v

/-- The final vertex `z* = Aj h_T / Δ`. -/
noncomputable def zStar (s : MState M d d) : Fin d → ℝ := fun v => (zNum h s v : ℝ) / s.Δ

/-- Boundedness of `{G z ≤ h}`: `G w ≤ 0` forces `w = 0`. -/
def Bdd : Prop := ∀ w : Fin d → ℤ, (∀ i, (G *ᵥ w) i ≤ 0) → w = 0

/-- The invariant (I1)–(I3) of Phase M after `r` steps, for `ε`. -/
structure Inv (ε : ℝ) {r : ℕ} (hr : r ≤ d) (s : MState M d r) : Prop where
  q_pos : 0 < s.q
  det_eq : (subB G hr s.T).det = s.Δ
  det_ne : s.Δ ≠ 0
  adj_eq : (subB G hr s.T).adjugate = s.Aj
  feas : ∀ i, rowVal G i (ptZ s.Zn s.q) ≤ h i + ε
  tight : ∀ a, rowVal G (s.T a) (ptZ s.Zn s.q) = h (s.T a) + ε

variable {G h E}

theorem rowVal_ptZ (i : Fin M) (Zn : Fin d → ℤ) (q : ℕ) :
    rowVal G i (ptZ Zn q) = ((G *ᵥ Zn) i : ℝ) / q := by
  simp [rowVal, ptZ, mulVec, dotProduct, Finset.sum_div, mul_div_assoc]

/-- `ω_i = G_{i,l} Δ − ρ_i · (Aj col)`. -/
theorem mOmega_apply {r : ℕ} (hr : r + 1 ≤ d) (s : MState M d r) (i : Fin M) :
    mOmega G hr s i = G i (Fin.castLE hr (Fin.last r)) * s.Δ -
      (fun b => G i (Fin.castLE (Nat.le_of_succ_le hr) b)) ⬝ᵥ
        (s.Aj *ᵥ fun a => G (s.T a) (Fin.castLE hr (Fin.last r))) := by
  unfold mOmega mDir
  rw [mulVec, dotProduct, sum_mul_extend hr, Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, mul_neg, Finset.sum_neg_distrib]
  rw [dotProduct]
  have : ∀ b : Fin r, Fin.castLE hr b.castSucc = Fin.castLE (Nat.le_of_succ_le hr) b :=
    fun b => Fin.ext rfl
  simp only [this]
  ring

theorem mDir_last {r : ℕ} (hr : r + 1 ≤ d) (s : MState M d r) :
    mDir G hr s (Fin.castLE hr (Fin.last r)) = s.Δ := by
  simp only [mDir, extend, Fin.val_castLE, Fin.val_last, Nat.lt_succ_self, ↓reduceDIte]
  exact Fin.lastCases_last

/-- **C3(a).** The rows of `T` are orthogonal to the direction: `G_T w = 0`. -/
theorem mOmega_T {ε : ℝ} {r : ℕ} (hr : r + 1 ≤ d) {s : MState M d r}
    (hs : Inv G h ε (Nat.le_of_succ_le hr) s) (a : Fin r) : mOmega G hr s (s.T a) = 0 := by
  rw [mOmega_apply]
  have hρ : (fun b => G (s.T a) (Fin.castLE (Nat.le_of_succ_le hr) b)) =
      fun b => subB G (Nat.le_of_succ_le hr) s.T a b := rfl
  rw [hρ, ← hs.adj_eq]
  have key := congrFun (mulVec_mulVec (fun a => G (s.T a) (Fin.castLE hr (Fin.last r)))
    (subB G (Nat.le_of_succ_le hr) s.T) (subB G (Nat.le_of_succ_le hr) s.T).adjugate) a
  rw [mul_adjugate, hs.det_eq, smul_mulVec, one_mulVec] at key
  change (subB G (Nat.le_of_succ_le hr) s.T *ᵥ _) a = _ at key
  rw [mulVec] at key
  rw [key]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **C3(b).** Under `Bdd`, some row blocks the direction. -/
theorem exists_mOmega_pos (hb : Bdd G) {ε : ℝ} {r : ℕ} (hr : r + 1 ≤ d) {s : MState M d r}
    (hs : Inv G h ε (Nat.le_of_succ_le hr) s) : ∃ i, 0 < mOmega G hr s i := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hw := hb (mDir G hr s) hcon
  have := mDir_last (G := G) hr s
  rw [hw] at this
  exact hs.det_ne (by simpa using this.symm)

/-- `(G z)_i` after the step: `z' = z + α w` with `α = σ_{i*} / (E q ω_{i*})`. -/
theorem rowVal_mNext (hE : 0 < E) {r : ℕ} (hr : r + 1 ≤ d) (s : MState M d r) (hq : 0 < s.q)
    {i : Fin M} (hi : 0 < mOmega G hr s i) (j : Fin M) :
    rowVal G j (ptZ (mNext G h E hr s i).Zn (mNext G h E hr s i).q) =
      rowVal G j (ptZ s.Zn s.q) +
        (mSigma G h E s i : ℝ) / ((E : ℝ) * s.q * mOmega G hr s i) * mOmega G hr s j := by
  rw [rowVal_ptZ, rowVal_ptZ]
  have hq' : (s.q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hE' : (E : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  have hω : (mOmega G hr s i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  have hZ : (G *ᵥ (mNext G h E hr s i).Zn) j =
      (E : ℤ) * mOmega G hr s i * (G *ᵥ s.Zn) j + mSigma G h E s i * mOmega G hr s j := by
    simp only [mNext, mulVec, dotProduct, mOmega, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun v _ => by ring
  have hqn : ((mNext G h E hr s i).q : ℝ) = (E : ℝ) * s.q * mOmega G hr s i := by
    have : ((mOmega G hr s i).toNat : ℝ) = (mOmega G hr s i : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hi.le]
    simp only [mNext]
    push_cast
    rw [this]
  rw [hZ, hqn]
  push_cast
  field_simp

/-- `σ_i / (E q) = h_i + ε − (G z)_i`. -/
theorem mSigma_div (hE : 0 < E) {r : ℕ} (s : MState M d r) (hq : 0 < s.q) (i : Fin M) :
    (mSigma G h E s i : ℝ) / ((E : ℝ) * s.q) = h i + 1 / E - rowVal G i (ptZ s.Zn s.q) := by
  rw [rowVal_ptZ]
  have hq' : (s.q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hE' : (E : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  simp only [mSigma]
  push_cast
  field_simp

/-- **C3(c).** One step preserves the invariant (for `ε = 1/E`). -/
theorem moveStep_inv (hE : 0 < E) {r : ℕ} (hr : r + 1 ≤ d) {s : MState M d r}
    (hs : Inv G h (1 / E) (Nat.le_of_succ_le hr) s) {s' : MState M d (r + 1)}
    (hs' : moveStep G h E hr s = some s') : Inv G h (1 / E) hr s' := by
  unfold moveStep at hs'
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hs'
  obtain ⟨hω, hmin⟩ := argMinRatio_spec hi
  have hq := hs.q_pos
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  have hqr : (0 : ℝ) < s.q := by exact_mod_cast hq
  have hωr : (0 : ℝ) < mOmega G hr s i := by exact_mod_cast hω
  -- `σ_i ≥ 0` for every row
  have hσ : ∀ j, (0 : ℝ) ≤ mSigma G h E s j := by
    intro j
    have h1 := mSigma_div (G := G) (h := h) hE s hq j
    have h2 := hs.feas j
    have h3 : (0 : ℝ) ≤ (mSigma G h E s j : ℝ) / ((E : ℝ) * s.q) := by rw [h1]; linarith
    have h4 : (0 : ℝ) < (E : ℝ) * s.q := by positivity
    exact (div_nonneg_iff.mp h3).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr h4))
  -- the determinant of the bordered submatrix is `ω_i`
  have hdet' : (subB G hr (Fin.lastCases (motive := fun _ => Fin M) i s.T)).det =
      mOmega G hr s i := by
    rw [subB_snoc, det_border _ _ _ _ (hs.det_eq ▸ hs.det_ne), hs.det_eq, hs.adj_eq,
      mOmega_apply]
  have hΔ' : (mNext G h E hr s i).Δ = mOmega G hr s i := by
    rw [mOmega_apply]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `q' > 0`
    change 0 < E * s.q * (mOmega G hr s i).toNat
    have : 0 < (mOmega G hr s i).toNat := by omega
    positivity
  · change (subB G hr (Fin.lastCases (motive := fun _ => Fin M) i s.T)).det = _
    rw [hdet', hΔ']
  · rw [hΔ']
    exact hω.ne'
  · change (subB G hr (Fin.lastCases (motive := fun _ => Fin M) i s.T)).adjugate = _
    rw [subB_snoc, adjugate_border _ _ _ _ (hs.det_eq ▸ hs.det_ne)]
    · simp only [mNext, hs.det_eq, hs.adj_eq]
    · rw [hs.det_eq, hs.adj_eq, ← mOmega_apply]; exact hω.ne'
  · -- feasibility
    intro j
    rw [rowVal_mNext hE hr s hq hω j]
    have hα : 0 ≤ (mSigma G h E s i : ℝ) / ((E : ℝ) * s.q * mOmega G hr s i) := by
      have := hσ i
      positivity
    by_cases hj : 0 < mOmega G hr s j
    · -- `α ω_j ≤ σ_j / (E q)` by minimality of `i`
      have hm : (mSigma G h E s i : ℝ) * mOmega G hr s j ≤
          (mSigma G h E s j : ℝ) * mOmega G hr s i := by exact_mod_cast hmin j hj
      have h1 := mSigma_div (G := G) (h := h) hE s hq j
      have key : (mSigma G h E s i : ℝ) / ((E : ℝ) * s.q * mOmega G hr s i) *
          mOmega G hr s j ≤ (mSigma G h E s j : ℝ) / ((E : ℝ) * s.q) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hEq : (0 : ℝ) ≤ (E : ℝ) * s.q := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hm hEq]
      linarith [hs.feas j]
    · have hj' : (mOmega G hr s j : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hj
      have : (mSigma G h E s i : ℝ) / ((E : ℝ) * s.q * mOmega G hr s i) *
          mOmega G hr s j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα hj'
      linarith [hs.feas j]
  · -- tightness
    intro a
    have hT : (mNext G h E hr s i).T = Fin.lastCases (motive := fun _ => Fin M) i s.T := rfl
    rw [hT]
    induction a using Fin.lastCases with
    | last =>
      rw [Fin.lastCases_last, rowVal_mNext hE hr s hq hω i]
      have h1 := mSigma_div (G := G) (h := h) hE s hq i
      have : (mSigma G h E s i : ℝ) / ((E : ℝ) * s.q * mOmega G hr s i) * mOmega G hr s i =
          (mSigma G h E s i : ℝ) / ((E : ℝ) * s.q) := by
        field_simp
      rw [this, h1]
      ring
    | cast a =>
      rw [Fin.lastCases_castSucc, rowVal_mNext hE hr s hq hω (s.T a), mOmega_T hr hs a]
      simp only [Int.cast_zero, mul_zero, add_zero]
      exact hs.tight a

/-- **C3(b).** Under `Bdd`, a step is always possible from a state satisfying the invariant. -/
theorem moveStep_isSome (hb : Bdd G) {ε : ℝ} {r : ℕ} (hr : r + 1 ≤ d) {s : MState M d r}
    (hs : Inv G h ε (Nat.le_of_succ_le hr) s) : ∃ s', moveStep G h E hr s = some s' := by
  obtain ⟨i, hi, _⟩ := argMinRatio_some (mOmega G hr s) (mSigma G h E s)
    (exists_mOmega_pos hb hr hs)
  exact ⟨_, by rw [moveStep, hi, Option.map_some]⟩

theorem init_inv {Zn₀ : Fin d → ℤ} {q₀ : ℕ} (hq₀ : 0 < q₀) {ε : ℝ}
    (hz : ∀ i, rowVal G i (ptZ Zn₀ q₀) ≤ h i + ε) :
    Inv G h ε (Nat.zero_le d) (MState.init Zn₀ q₀ : MState M d 0) := by
  refine ⟨hq₀, ?_, one_ne_zero, ?_, hz, fun a => a.elim0⟩
  · simp [MState.init]
  · exact Subsingleton.elim _ _

/-- The invariant holds along Phase M, which never gets stuck under `Bdd`. -/
theorem moveAux_inv (hE : 0 < E) (hb : Bdd G) {Zn₀ : Fin d → ℤ} {q₀ : ℕ} (hq₀ : 0 < q₀)
    (hz : ∀ i, rowVal G i (ptZ Zn₀ q₀) ≤ h i + 1 / E) :
    ∀ (r : ℕ) (hr : r ≤ d), ∃ s, moveAux G h E Zn₀ q₀ r hr = some s ∧ Inv G h (1 / E) hr s
  | 0, _ => ⟨_, rfl, init_inv hq₀ hz⟩
  | r + 1, hr => by
    obtain ⟨s, hs, hinv⟩ := moveAux_inv hE hb hq₀ hz r (Nat.le_of_succ_le hr)
    obtain ⟨s', hs'⟩ := moveStep_isSome (E := E) hb hr hinv
    exact ⟨s', by rw [moveAux, hs, Option.bind_some, hs'], moveStep_inv hE hr hinv hs'⟩

/-! ### Magnitudes (Cramer and `Matrix.det_le`) -/

theorem abs_det_subB_le {A₀ : ℕ} (hG : ∀ i v, |G i v| ≤ A₀) {r : ℕ} (hr : r ≤ d)
    (T : Fin r → Fin M) : |(subB G hr T).det| ≤ r.factorial * (A₀ : ℤ) ^ r := by
  have := Matrix.det_le (abv := AbsoluteValue.abs) (A := subB G hr T) (x := (A₀ : ℤ))
    (fun a b => by simpa [subB] using hG (T a) (Fin.castLE hr b))
  simpa [Fintype.card_fin, nsmul_eq_mul] using this

theorem abs_adjugate_subB_le {A₀ : ℕ} (hA₀ : 1 ≤ A₀) (hG : ∀ i v, |G i v| ≤ A₀) {r : ℕ}
    (hr : r ≤ d) (T : Fin r → Fin M) (a b : Fin r) :
    |(subB G hr T).adjugate a b| ≤ r.factorial * (A₀ : ℤ) ^ r := by
  rw [adjugate_apply]
  have := Matrix.det_le (abv := AbsoluteValue.abs)
    (A := (subB G hr T).updateRow b (Pi.single a 1)) (x := (A₀ : ℤ)) (fun a' b' => by
      rw [updateRow_apply]
      split_ifs
      · rw [Pi.single_apply]
        split_ifs
        · simpa using hA₀
        · simp
      · simpa [subB] using hG (T a') (Fin.castLE hr b'))
  simpa [Fintype.card_fin, nsmul_eq_mul] using this

theorem factorial_pow_mono {A₀ : ℕ} (hA₀ : 1 ≤ A₀) {r : ℕ} (hr : r ≤ d) :
    (r.factorial : ℤ) * (A₀ : ℤ) ^ r ≤ d.factorial * (A₀ : ℤ) ^ d := by
  have h1 : (r.factorial : ℤ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hr
  have h2 : (A₀ : ℤ) ^ r ≤ (A₀ : ℤ) ^ d := pow_le_pow_right₀ (by exact_mod_cast hA₀) hr
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **Magnitudes of Phase M**: along the run, `|Δ|` and the entries of `Aj` are at most
`r!·A₀^r`, and the denominator satisfies `q_r ≤ q₀ (E·d!·A₀^d)^r`. -/
theorem moveAux_bounds (hE : 0 < E) {A₀ : ℕ} (hA₀ : 1 ≤ A₀) (hG : ∀ i v, |G i v| ≤ A₀)
    {Zn₀ : Fin d → ℤ} {q₀ : ℕ} (hq₀ : 0 < q₀)
    (hz : ∀ i, rowVal G i (ptZ Zn₀ q₀) ≤ h i + 1 / E) :
    ∀ (r : ℕ) (hr : r ≤ d) (s : MState M d r), moveAux G h E Zn₀ q₀ r hr = some s →
      Inv G h (1 / E) hr s ∧ |s.Δ| ≤ r.factorial * (A₀ : ℤ) ^ r ∧
        (∀ a b, |s.Aj a b| ≤ r.factorial * (A₀ : ℤ) ^ r) ∧
        s.q ≤ q₀ * (E * d.factorial * A₀ ^ d) ^ r
  | 0, hr, s, hs => by
    simp only [moveAux, Option.some.injEq] at hs
    subst hs
    refine ⟨init_inv hq₀ hz, by simp [MState.init], fun a => a.elim0, by simp [MState.init]⟩
  | r + 1, hr, s', hs' => by
    simp only [moveAux] at hs'
    obtain ⟨s, hs, hstep⟩ := Option.bind_eq_some_iff.mp hs'
    obtain ⟨hinv, -, -, hq⟩ := moveAux_bounds hE hA₀ hG hq₀ hz r (Nat.le_of_succ_le hr) s hs
    have hinv' := moveStep_inv hE hr hinv hstep
    refine ⟨hinv', ?_, ?_, ?_⟩
    · rw [← hinv'.det_eq]; exact abs_det_subB_le hG hr _
    · intro a b; rw [← hinv'.adj_eq]; exact abs_adjugate_subB_le hA₀ hG hr _ a b
    · unfold moveStep at hstep
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hstep
      obtain ⟨hω, -⟩ := argMinRatio_spec hi
      -- `ω_i` is the new determinant, hence `≤ d!·A₀^d`
      have hωΔ : (mNext G h E hr s i).Δ = mOmega G hr s i := by
        simp only [mNext]; rw [mOmega_apply]
      have hωle : mOmega G hr s i ≤ d.factorial * (A₀ : ℤ) ^ d := by
        rw [← hωΔ, ← hinv'.det_eq]
        exact (le_abs_self _).trans ((abs_det_subB_le hG hr _).trans (factorial_pow_mono hA₀ hr))
      have hωn : (mOmega G hr s i).toNat ≤ d.factorial * A₀ ^ d := by
        have : ((mOmega G hr s i).toNat : ℤ) ≤ ((d.factorial * A₀ ^ d : ℕ) : ℤ) := by
          rw [Int.toNat_of_nonneg hω.le]; push_cast; exact hωle
        exact_mod_cast this
      simp only [mNext]
      calc E * s.q * (mOmega G hr s i).toNat
          ≤ E * (q₀ * (E * d.factorial * A₀ ^ d) ^ r) * (d.factorial * A₀ ^ d) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hq) hωn
        _ = q₀ * (E * d.factorial * A₀ ^ d) ^ (r + 1) := by ring

/-- **Magnitudes of Phase M**: if every point of `{G z ≤ h + ε}` has `|z_v| ≤ B`, the
numerators satisfy `|Zn_v| ≤ B q`. -/
theorem Inv.Zn_bound {ε : ℝ} {r : ℕ} {hr : r ≤ d} {s : MState M d r} (hs : Inv G h ε hr s)
    {B : ℝ} (hbox : ∀ z : Fin d → ℝ, (∀ i, rowVal G i z ≤ h i + ε) → ∀ v, |z v| ≤ B)
    (v : Fin d) : |(s.Zn v : ℝ)| ≤ B * s.q := by
  have h1 := hbox _ hs.feas v
  have hq : (0 : ℝ) < s.q := by exact_mod_cast hs.q_pos
  simp only [ptZ, abs_div, Nat.abs_cast] at h1
  rwa [div_le_iff₀ hq] at h1

/-! ### C4: the output of Phase M is an exact solution -/

/-- **C4.** If `|G_{ab}| ≤ A₀` (`A₀ ≥ 1`), `E ≥ 2(d²+1)·d!·A₀^{d+1}`, `{G z ≤ h}` is bounded in
the sense of `Bdd`, and `z̃ = Zn₀ / q₀` satisfies `G z̃ ≤ h + 1/E`, then Phase M ends in a state
with `Δ ≠ 0` whose vertex `z* = Aj h_T / Δ` satisfies `G z* ≤ h` exactly. -/
theorem moveRun_exact (hb : Bdd G) {A₀ : ℕ} (hA₀ : 1 ≤ A₀) (hG : ∀ i v, |G i v| ≤ A₀)
    (hE : 2 * (d ^ 2 + 1) * d.factorial * A₀ ^ (d + 1) ≤ E) {Zn₀ : Fin d → ℤ} {q₀ : ℕ}
    (hq₀ : 0 < q₀) (hz : ∀ i, rowVal G i (ptZ Zn₀ q₀) ≤ h i + 1 / E) :
    ∃ s, moveRun G h E Zn₀ q₀ = some s ∧ Inv G h (1 / E) le_rfl s ∧
      ∀ i, rowVal G i (zStar h s) ≤ h i := by
  have hEpos : 0 < E := lt_of_lt_of_le (by positivity) hE
  obtain ⟨s, hs, hinv⟩ := moveAux_inv hEpos hb hq₀ hz d le_rfl
  refine ⟨s, hs, hinv, fun i => ?_⟩
  have hBG : ∀ a v, subB G le_rfl s.T a v = G (s.T a) v := fun a v => by simp [subB]
  have hΔne : (s.Δ : ℝ) ≠ 0 := by exact_mod_cast hinv.det_ne
  have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
  have hAB : s.Aj * subB G le_rfl s.T = s.Δ • 1 := by
    rw [← hinv.adj_eq, adjugate_mul, hinv.det_eq]
  have hBA : subB G le_rfl s.T * s.Aj = s.Δ • 1 := by
    rw [← hinv.adj_eq, mul_adjugate, hinv.det_eq]
  -- (I3): `B z = h_T + ε 𝟙`
  have htight : ∀ a, ∑ v, (G (s.T a) v : ℝ) * ptZ s.Zn s.q v = h (s.T a) + 1 / E :=
    fun a => hinv.tight a
  -- `B z* = h_T` (Cramer)
  have hBz : ∀ a, ∑ v, (G (s.T a) v : ℝ) * zStar h s v = h (s.T a) := by
    intro a
    have e1 := congrFun (mulVec_mulVec (fun a => h (s.T a)) (subB G le_rfl s.T) s.Aj) a
    rw [hBA, smul_mulVec, one_mulVec] at e1
    have e2 : ∑ v, (G (s.T a) v : ℝ) * (zNum h s v : ℝ) = (s.Δ : ℝ) * h (s.T a) := by
      have := congrArg (fun x : ℤ => (x : ℝ)) e1
      simpa [mulVec, dotProduct, hBG, zNum] using this
    calc ∑ v, (G (s.T a) v : ℝ) * zStar h s v
        = (∑ v, (G (s.T a) v : ℝ) * (zNum h s v : ℝ)) / s.Δ := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun v _ => by rw [zStar, mul_div_assoc]
      _ = h (s.T a) := by rw [e2]; field_simp
  -- the defect `z − z* = (ε/Δ) Aj 𝟙`
  have hdz : ∀ b, ptZ s.Zn s.q b - zStar h s b = (1 / E) / s.Δ * ∑ a, (s.Aj b a : ℝ) := by
    intro b
    have e1 : ∀ a, ∑ v, (G (s.T a) v : ℝ) * (ptZ s.Zn s.q v - zStar h s v) = 1 / E := by
      intro a
      simp only [mul_sub, Finset.sum_sub_distrib, htight, hBz]
      ring
    have hAB' : ∀ v, ∑ a, (s.Aj b a : ℝ) * (G (s.T a) v : ℝ) =
        if b = v then (s.Δ : ℝ) else 0 := by
      intro v
      have h1 := congrFun (congrFun hAB b) v
      rw [Matrix.mul_apply] at h1
      have h2 := congrArg (fun x : ℤ => (x : ℝ)) h1
      simp only [hBG, Int.cast_sum, Int.cast_mul, Matrix.smul_apply, one_apply,
        smul_eq_mul] at h2
      rw [h2]
      split_ifs <;> simp
    have e2 : ∑ a, (s.Aj b a : ℝ) * ∑ v, (G (s.T a) v : ℝ) * (ptZ s.Zn s.q v - zStar h s v) =
        (s.Δ : ℝ) * (ptZ s.Zn s.q b - zStar h s b) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ v, ∑ a, (s.Aj b a : ℝ) * ((G (s.T a) v : ℝ) * (ptZ s.Zn s.q v - zStar h s v)) =
          (if b = v then (s.Δ : ℝ) else 0) * (ptZ s.Zn s.q v - zStar h s v) := by
        intro v
        rw [← hAB' v, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [this, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    simp only [e1] at e2
    rw [← Finset.sum_mul] at e2
    field_simp at e2 ⊢
    linarith
  -- `(G z*)_i = (G z)_i − (ε/Δ) S` with `S = Σ_v G_{iv} (Aj 𝟙)_v`
  obtain ⟨S, hS⟩ : ∃ S : ℤ, S = ∑ v, G i v * ∑ a, s.Aj v a := ⟨_, rfl⟩
  have hGz : rowVal G i (zStar h s) = rowVal G i (ptZ s.Zn s.q) - (1 / E) / s.Δ * (S : ℝ) := by
    have : ∀ v, (G i v : ℝ) * zStar h s v = (G i v : ℝ) * ptZ s.Zn s.q v -
        (1 / E) / s.Δ * ((G i v : ℝ) * ∑ a, (s.Aj v a : ℝ)) := by
      intro v
      have e : zStar h s v = ptZ s.Zn s.q v - (1 / E) / s.Δ * ∑ a, (s.Aj v a : ℝ) := by
        linarith [hdz v]
      rw [e]; ring
    rw [hS]
    push_cast
    simp only [rowVal, this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- bounds: `|S| ≤ d² d! A₀^{d+1}`, `|Δ| ≤ d! A₀^d`
  have hAjb : ∀ v a, |s.Aj v a| ≤ d.factorial * (A₀ : ℤ) ^ d := by
    intro v a
    rw [← hinv.adj_eq]
    exact abs_adjugate_subB_le hA₀ hG le_rfl _ v a
  have hSb : |S| ≤ d ^ 2 * d.factorial * (A₀ : ℤ) ^ (d + 1) := by
    rw [hS]
    calc |∑ v, G i v * ∑ a, s.Aj v a| ≤ ∑ v, |G i v * ∑ a, s.Aj v a| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : Fin d, (A₀ : ℤ) * (d * (d.factorial * (A₀ : ℤ) ^ d)) := by
          refine Finset.sum_le_sum fun v _ => ?_
          rw [abs_mul]
          refine mul_le_mul (hG i v) ?_ (abs_nonneg _) (by positivity)
          calc |∑ a, s.Aj v a| ≤ ∑ a, |s.Aj v a| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _a : Fin d, (d.factorial * (A₀ : ℤ) ^ d) :=
                Finset.sum_le_sum fun a _ => hAjb v a
            _ = d * (d.factorial * (A₀ : ℤ) ^ d) := by simp
      _ = d ^ 2 * d.factorial * (A₀ : ℤ) ^ (d + 1) := by simp; ring
  have hΔb : |s.Δ| ≤ d.factorial * (A₀ : ℤ) ^ d := by
    rw [← hinv.det_eq]
    exact abs_det_subB_le hG le_rfl _
  -- integrality: `Δ ((G z*)_i − h_i) = N ∈ ℤ`
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = ∑ v, G i v * zNum h s v - s.Δ * h i := ⟨_, rfl⟩
  have hNz : rowVal G i (zStar h s) - h i = (N : ℝ) / s.Δ := by
    rw [hN]
    push_cast
    rw [sub_div, Finset.sum_div]
    simp only [rowVal, zStar]
    congr 1
    · exact Finset.sum_congr rfl fun v _ => by ring
    · field_simp
  by_contra hcon
  have hpos : 0 < (N : ℝ) / s.Δ := by rw [← hNz]; linarith [not_le.mp hcon]
  have hN0 : N ≠ 0 := by
    intro h0; rw [h0] at hpos; simp at hpos
  have hNabs : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hN0
  have hΔabs : (0 : ℝ) < |(s.Δ : ℝ)| := abs_pos.mpr hΔne
  -- `1/|Δ| ≤ (G z*)_i − h_i ≤ ε (1 + |S|/|Δ|)`
  have hlow : 1 / |(s.Δ : ℝ)| ≤ (N : ℝ) / s.Δ := by
    rw [← abs_of_pos hpos, abs_div]
    exact div_le_div_of_nonneg_right hNabs hΔabs.le
  have hup : (N : ℝ) / s.Δ ≤ 1 / E + 1 / E * |(S : ℝ)| / |(s.Δ : ℝ)| := by
    rw [← hNz, hGz]
    have h1 := hinv.feas i
    have h2 : -((1 / E) / s.Δ * (S : ℝ)) ≤ 1 / E * |(S : ℝ)| / |(s.Δ : ℝ)| := by
      have : |(1 / E) / s.Δ * (S : ℝ)| = 1 / E * |(S : ℝ)| / |(s.Δ : ℝ)| := by
        rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 / E)]
        ring
      rw [← this]
      exact neg_le_abs _
    linarith
  have hkey : (1 : ℝ) ≤ 1 / E * (|(s.Δ : ℝ)| + |(S : ℝ)|) := by
    have := hlow.trans hup
    rw [div_le_iff₀ hΔabs] at this
    calc (1 : ℝ) ≤ (1 / E + 1 / E * |(S : ℝ)| / |(s.Δ : ℝ)|) * |(s.Δ : ℝ)| := this
      _ = 1 / E * (|(s.Δ : ℝ)| + |(S : ℝ)|) := by field_simp
  have hΔb' : |(s.Δ : ℝ)| ≤ d.factorial * (A₀ : ℝ) ^ (d + 1) := by
    have h1 : |(s.Δ : ℝ)| ≤ d.factorial * (A₀ : ℝ) ^ d := by exact_mod_cast hΔb
    have h2 : (A₀ : ℝ) ^ d ≤ (A₀ : ℝ) ^ (d + 1) :=
      pow_le_pow_right₀ (by exact_mod_cast hA₀) (Nat.le_succ d)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hSb' : |(S : ℝ)| ≤ d ^ 2 * d.factorial * (A₀ : ℝ) ^ (d + 1) := by exact_mod_cast hSb
  have hEb : (2 : ℝ) * (d ^ 2 + 1) * d.factorial * (A₀ : ℝ) ^ (d + 1) ≤ E := by
    exact_mod_cast hE
  have : 1 / (E : ℝ) * (|(s.Δ : ℝ)| + |(S : ℝ)|) ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hEr]
    nlinarith
  linarith

end STACS2027.Runtimes.ConvexQP
