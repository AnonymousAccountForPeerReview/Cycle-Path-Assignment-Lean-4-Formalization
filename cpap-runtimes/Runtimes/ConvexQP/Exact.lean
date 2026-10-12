module

public import Runtimes.ConvexQP.QP
public import Runtimes.ConvexQP.Move
import Mathlib.Tactic

/-!
# Lemma 16, Part D: the exact rounding and the main theorem

From integer data `Xs` with a
denominator `q₀` (the output of Phase E: `x̂ = Xs/q₀ ∈ 𝒳` with `gap(x̂) ≤ ε²`):

* **Phase K** (`kktZ`, `kktG`, `kktH`, `kktZn`): the pattern `Z = {(c,j) : x̂_{c,j} ≤ ŝ_{c,j}}`
  (`ŝ = L(x̂) − π(x̂)`, computed on the integers) and the KKT system `G z ≤ h` in
  `z = (x, π) ∈ ℚ^{(k+1)t}` with `2t + 3kt` rows, in this order: `S⁺_c, S⁻_c` for every
  cycle, then three rows for every `(c,j)` (`[Z1, Z2, Z3]` if `(c,j) ∈ Z`, else `[N1, N2, N3]`).
  Rows `S_{c,s}` read `±∑_j x_{c,j} ≤ ±1`; the rows of `(c,j)` read
  `coefX · x_{c,j} + coefL · (L(x)_{c,j} − π_c) ≤ 0` (`rowVal_S`, `rowVal_X`).
* **D1** (`kkt_approx`): `G z̃ ≤ h + ε 𝟙` at `z̃ = (x̂, π̂)`.
* **D2** (`exists_not_Z`, `kkt_bdd`): every cycle has an option outside `Z`, and `G w ≤ 0`
  forces `w = 0`; the entries of `G` are at most `A₀ = k − 2` (`kktG_entry_le`).
* Phase M (`Move.lean`) then yields a vertex `z*` with `G z* ≤ h` (C4).
* **D3** (`kkt_optimal`): such a `z* = (x*, π*)` gives a KKT point, so `x*` minimizes `F` and `Φ`.
* **D4**, Phase O (`exactFrom`): `D = |Δ|`, `W_{c,j} = sgn(Δ)(Aj h_T)_{(c,j)} = D x*_{c,j} ∈ ℕ`,
  `∑_j W_{c,j} = D`.
* **D5** (`exactFrom_optimal`): if `x̂ = Xs/q₀ ∈ 𝒳` and `gap(x̂) ≤ ε²` then `W/D` is optimal.
  **Lemma 16** (`solveExactWith_optimal`): for any Phase E procedure meeting `PhaseESpec`
  (Part B), `solveExactWith` returns an `OptimalFractional` solution on the `k`-cycles of every
  duplicate-free graph; with `solveExactWith_map_fst` it discharges the hypotheses `hR`, `hopt`
  of Theorems 16 and 17 (`rounding_solveExactWith`).
* **Magnitudes** (Phase M on the KKT system; `kkt_box`, `exactFrom_magnitudes`).
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Matrix Finset

/-! ### Index sets of the KKT system -/

/-- The number of rows `2t + 3kt`. -/
def nRows (t k : ℕ) : ℕ := t * 2 + t * k * 3

/-- Columns: `x_{c,j}` at `j + k c`, then `π_c` at `kt + c`. -/
def colEquiv (t k : ℕ) : Fin (dimKKT t k) ≃ (Fin t × Fin k) ⊕ Fin t :=
  (finCongr (show dimKKT t k = t * k + t by unfold dimKKT; ring)).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _)))

/-- Rows: `S_{c,s}` at `s + 2c` (`s = 0`: `S⁺`, `s = 1`: `S⁻`), then the three rows of `(c,j)` at
`2t + b + 3(j + k c)`. -/
def rowEquiv (t k : ℕ) : Fin (nRows t k) ≃ (Fin t × Fin 2) ⊕ ((Fin t × Fin k) × Fin 3) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm
    (finProdFinEquiv.symm.trans (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))))

/-- The sign of the row `S_{c,s}`. -/
def sgnS (s : Fin 2) : ℤ := if s = 0 then 1 else -1

/-- The coefficient of `x_{c,j}` in the row `b` of `(c,j)` (`zc`: whether `(c,j) ∈ Z`):
`Z1: x ≤ 0`, `Z2: −x ≤ 0`, `Z3: −(L − π) ≤ 0`; `N1: L − π ≤ 0`, `N2: −(L − π) ≤ 0`, `N3: −x ≤ 0`. -/
def coefX (zc : Bool) (b : Fin 3) : ℤ :=
  if zc then (if b = 0 then 1 else if b = 1 then -1 else 0) else (if b = 2 then -1 else 0)

/-- The coefficient of `L(x)_{c,j} − π_c` in the row `b` of `(c,j)`. -/
def coefL (zc : Bool) (b : Fin 3) : ℤ :=
  if zc then (if b = 2 then -1 else 0) else (if b = 0 then 1 else if b = 1 then -1 else 0)

variable (I : Inst)

/-- The entries of the KKT matrix on the structured index sets. -/
def kktEntry (Z : Fin I.t → Fin I.k → Bool) :
    (Fin I.t × Fin 2) ⊕ ((Fin I.t × Fin I.k) × Fin 3) → (Fin I.t × Fin I.k) ⊕ Fin I.t → ℤ
  | .inl (c, s), .inl (c', _) => if c' = c then sgnS s else 0
  | .inl _, .inr _ => 0
  | .inr ((c, j), b), .inl (c', j') =>
      coefX (Z c j) b * (if c' = c then (if j' = j then 1 else 0) else 0) +
        coefL (Z c j) b * I.H c j c' j'
  | .inr ((c, j), b), .inr c' => -(coefL (Z c j) b * (if c' = c then 1 else 0))

/-- The right-hand sides: `±1` for `S_{c,s}`, `0` otherwise. -/
def kktRhs : (Fin I.t × Fin 2) ⊕ ((Fin I.t × Fin I.k) × Fin 3) → ℤ
  | .inl (_, s) => sgnS s
  | .inr _ => 0

/-- The KKT matrix `G` of the pattern `Z`. -/
def kktG (Z : Fin I.t → Fin I.k → Bool) : Matrix (Fin (nRows I.t I.k)) (Fin (dimKKT I.t I.k)) ℤ :=
  Matrix.of fun i v => kktEntry I Z (rowEquiv I.t I.k i) (colEquiv I.t I.k v)

/-- The right-hand side `h`. -/
def kktH : Fin (nRows I.t I.k) → ℤ := fun i => kktRhs I (rowEquiv I.t I.k i)

/-- Phase K: the pattern `Z = {(c,j) : Xs_{c,j} ≤ L(Xs)_{c,j} − π(Xs)_c}`. -/
def kktZ (Xs : Fin I.t → Fin I.k → ℤ) : Fin I.t → Fin I.k → Bool :=
  fun c j => decide (Xs c j ≤ I.L Xs c j - I.pi Xs c)

/-- Phase K: the numerators `(Xs, πs)` of the approximate solution `z̃ = (x̂, π̂)`. -/
def kktZn (Xs : Fin I.t → Fin I.k → ℤ) : Fin (dimKKT I.t I.k) → ℤ :=
  fun v => Sum.elim (fun p => Xs p.1 p.2) (I.pi Xs) (colEquiv I.t I.k v)

namespace Inst

/-- The column of `x_{c,j}`. -/
def colX (c : Fin I.t) (j : Fin I.k) : Fin (dimKKT I.t I.k) := (colEquiv I.t I.k).symm (.inl (c, j))

/-- The column of `π_c`. -/
def colP (c : Fin I.t) : Fin (dimKKT I.t I.k) := (colEquiv I.t I.k).symm (.inr c)

/-- The `x`-part of a vector of the KKT variables. -/
def xOf {R : Type*} (z : Fin (dimKKT I.t I.k) → R) : Fin I.t → Fin I.k → R :=
  fun c j => z (I.colX c j)

/-- The `π`-part of a vector of the KKT variables. -/
def piOf {R : Type*} (z : Fin (dimKKT I.t I.k) → R) : Fin I.t → R := fun c => z (I.colP c)

/-- **Phases K, M, O**: from integer data `Xs` with denominator `q₀`, the common
denominator `D = |Δ|` and the weights `W_{c,j} = sgn(Δ) (Aj h_T)_{(c,j)}` (`(1, 0)` if Phase M
gets stuck, which Theorem `exactFrom_optimal` excludes). -/
def exactFrom (Xs : Fin I.t → Fin I.k → ℤ) (q₀ : ℕ) : ℕ × (Fin I.t → Fin I.k → ℕ) :=
  match moveRun (kktG I (kktZ I Xs)) (kktH I) (bigE I.t I.k) (kktZn I Xs) q₀ with
  | some s => (s.Δ.natAbs, fun c j => (s.Δ.sign * zNum (kktH I) s (I.colX c j)).toNat)
  | none => (1, fun _ _ => 0)

end Inst

/-! ### Row values -/

variable {I}

theorem rowVal_kkt (Z : Fin I.t → Fin I.k → Bool) (i : Fin (nRows I.t I.k))
    (z : Fin (dimKKT I.t I.k) → ℝ) :
    rowVal (kktG I Z) i z =
      ∑ w, (kktEntry I Z (rowEquiv I.t I.k i) w : ℝ) * z ((colEquiv I.t I.k).symm w) := by
  unfold rowVal kktG
  rw [← Equiv.sum_comp (colEquiv I.t I.k)]
  simp [Equiv.symm_apply_apply]

/-- The row `S_{c,s}` reads `sgn_s · ∑_j x_{c,j}`. -/
theorem rowVal_S (Z : Fin I.t → Fin I.k → Bool) (c : Fin I.t) (s : Fin 2)
    (z : Fin (dimKKT I.t I.k) → ℝ) :
    rowVal (kktG I Z) ((rowEquiv I.t I.k).symm (.inl (c, s))) z =
      (sgnS s : ℝ) * ∑ j, I.xOf z c j := by
  rw [rowVal_kkt, Equiv.apply_symm_apply, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [kktEntry]
  simp [Finset.mul_sum, Inst.xOf, Inst.colX]

theorem sum_delta {R : Type*} [CommSemiring R] (A : Fin I.t → Fin I.k → R) (c : Fin I.t)
    (j : Fin I.k) :
    ∑ x, ∑ y, (if x = c then (if y = j then (1 : R) else 0) else 0) * A x y = A c j := by
  rw [Finset.sum_eq_single c, Finset.sum_eq_single j]
  · simp
  · intro y _ hy; simp [hy]
  · simp
  · intro x _ hx; simp [hx]
  · simp

/-- The row `b` of `(c,j)` reads `coefX · x_{c,j} + coefL · (L(x)_{c,j} − π_c)`. -/
theorem rowVal_X (Z : Fin I.t → Fin I.k → Bool) (c : Fin I.t) (j : Fin I.k) (b : Fin 3)
    (z : Fin (dimKKT I.t I.k) → ℝ) :
    rowVal (kktG I Z) ((rowEquiv I.t I.k).symm (.inr ((c, j), b))) z =
      (coefX (Z c j) b : ℝ) * I.xOf z c j +
        (coefL (Z c j) b : ℝ) * (I.L (I.xOf z) c j - I.piOf z c) := by
  rw [rowVal_kkt, Equiv.apply_symm_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
    I.L_eq_H]
  have ex : ∀ x y, (kktEntry I Z (.inr ((c, j), b)) (.inl (x, y)) : ℝ) =
      (coefX (Z c j) b : ℝ) * (if x = c then (if y = j then 1 else 0) else 0) +
        (coefL (Z c j) b : ℝ) * (I.H c j x y : ℝ) := by
    intro x y
    simp only [kktEntry]
    push_cast
    rfl
  have ep : ∀ x, (kktEntry I Z (.inr ((c, j), b)) (.inr x) : ℝ) =
      -((coefL (Z c j) b : ℝ) * (if x = c then 1 else 0)) := by
    intro x
    simp only [kktEntry]
    push_cast
    rfl
  simp only [ex, ep, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, neg_mul,
    Finset.sum_neg_distrib, sum_delta]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Inst.xOf, Inst.piOf, Inst.colX, Inst.colP]
  ring

theorem kktH_S (c : Fin I.t) (s : Fin 2) :
    kktH I ((rowEquiv I.t I.k).symm (.inl (c, s))) = sgnS s := by
  simp [kktH, kktRhs]

theorem kktH_X (c : Fin I.t) (j : Fin I.k) (b : Fin 3) :
    kktH I ((rowEquiv I.t I.k).symm (.inr ((c, j), b))) = 0 := by
  simp [kktH, kktRhs]

/-- A property of all rows follows from the structured rows. -/
theorem forall_rows {P : Fin (nRows I.t I.k) → Prop}
    (hS : ∀ c s, P ((rowEquiv I.t I.k).symm (.inl (c, s))))
    (hX : ∀ c j b, P ((rowEquiv I.t I.k).symm (.inr ((c, j), b)))) : ∀ i, P i := by
  intro i
  have := (rowEquiv I.t I.k).symm_apply_apply i
  rcases hr : rowEquiv I.t I.k i with ⟨c, s⟩ | ⟨⟨c, j⟩, b⟩
  · rw [hr] at this; rw [← this]; exact hS c s
  · rw [hr] at this; rw [← this]; exact hX c j b

/-- A vector of the KKT variables is determined by its `x`- and `π`-parts. -/
theorem vec_ext {R : Type*} {z z' : Fin (dimKKT I.t I.k) → R}
    (hx : I.xOf z = I.xOf z') (hp : I.piOf z = I.piOf z') : z = z' := by
  funext v
  have := (colEquiv I.t I.k).symm_apply_apply v
  rcases hv : colEquiv I.t I.k v with ⟨c, j⟩ | c
  · rw [hv] at this; rw [← this]; exact congrFun (congrFun hx c) j
  · rw [hv] at this; rw [← this]; exact congrFun hp c

/-! ### The entries of `G` (D2) -/

theorem coef_cases (zc : Bool) (b : Fin 3) :
    (coefX zc b = 0 ∨ coefL zc b = 0) ∧ |coefX zc b| ≤ 1 ∧ |coefL zc b| ≤ 1 := by
  cases zc <;> fin_cases b <;> simp [coefX, coefL]

/-- The entries of the KKT matrix are bounded by `A₀ = k − 2`. -/
theorem kktG_entry_le (hI : I.Valid) (Z : Fin I.t → Fin I.k → Bool) (i v) :
    |kktG I Z i v| ≤ (entryBound I.k : ℤ) := by
  have hA : (1 : ℤ) ≤ entryBound I.k := by
    unfold entryBound; have := hI.1; omega
  unfold kktG
  simp only [of_apply]
  rcases rowEquiv I.t I.k i with ⟨c, s⟩ | ⟨⟨c, j⟩, b⟩ <;>
    rcases colEquiv I.t I.k v with ⟨c', j'⟩ | c'
  · simp only [kktEntry, sgnS]
    split_ifs <;> simp [hA]
  · simp [kktEntry]
  · simp only [kktEntry]
    obtain ⟨h0, hx, hl⟩ := coef_cases (Z c j) b
    have hH : (I.H c j c' j' : ℤ) ≤ entryBound I.k := by
      unfold entryBound; exact_mod_cast Inst.H_le hI c j c' j'
    rcases h0 with h0 | h0 <;> rw [h0] <;> simp only [zero_mul, add_zero, zero_add, abs_mul]
    · calc |coefL (Z c j) b| * |(I.H c j c' j' : ℤ)| ≤ 1 * entryBound I.k := by
            refine mul_le_mul hl ?_ (abs_nonneg _) zero_le_one
            rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hH
        _ = entryBound I.k := one_mul _
    · calc |coefX (Z c j) b| * |(if c' = c then (if j' = j then (1 : ℤ) else 0) else 0)|
          ≤ 1 * 1 := by
            refine mul_le_mul hx ?_ (abs_nonneg _) zero_le_one
            split_ifs <;> simp
        _ ≤ entryBound I.k := by simpa using hA
  · simp only [kktEntry, abs_neg, abs_mul]
    obtain ⟨-, -, hl⟩ := coef_cases (Z c j) b
    calc |coefL (Z c j) b| * |(if c' = c then (1 : ℤ) else 0)| ≤ 1 * 1 := by
          refine mul_le_mul hl ?_ (abs_nonneg _) zero_le_one
          split_ifs <;> simp
      _ ≤ entryBound I.k := by simpa using hA

/-! ### D2: boundedness -/

/-- **D2(Bdd).** If every cycle has an option outside `Z`, then `G w ≤ 0` forces `w = 0`. -/
theorem kkt_bdd (Z : Fin I.t → Fin I.k → Bool) (hZ : ∀ c, ∃ j, Z c j = false) :
    Bdd (kktG I Z) := by
  intro w hw
  set z : Fin (dimKKT I.t I.k) → ℝ := fun v => (w v : ℝ) with hz
  have hrow : ∀ i, rowVal (kktG I Z) i z ≤ 0 := by
    intro i
    have := hw i
    have h2 : rowVal (kktG I Z) i z = ((kktG I Z *ᵥ w) i : ℝ) := by
      simp [rowVal, z, mulVec, dotProduct]
    rw [h2]; exact_mod_cast this
  -- the `x`-part vanishes
  have hsum : ∀ c, ∑ j, I.xOf z c j = 0 := by
    intro c
    have h0 := hrow ((rowEquiv I.t I.k).symm (.inl (c, 0)))
    have h1 := hrow ((rowEquiv I.t I.k).symm (.inl (c, 1)))
    rw [rowVal_S] at h0 h1
    simp only [sgnS] at h0 h1
    norm_num at h0 h1
    linarith
  have hnn : ∀ c j, 0 ≤ I.xOf z c j := by
    intro c j
    cases hzc : Z c j
    · have := hrow ((rowEquiv I.t I.k).symm (.inr ((c, j), 2)))
      rw [rowVal_X, hzc] at this
      simp [coefX, coefL] at this
      linarith
    · have := hrow ((rowEquiv I.t I.k).symm (.inr ((c, j), 1)))
      rw [rowVal_X, hzc] at this
      simp [coefX, coefL] at this
      linarith
  have hx0 : ∀ c j, I.xOf z c j = 0 := by
    intro c j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn c j)).mp (hsum c) j (mem_univ j)
  have hxz : I.xOf z = fun _ _ => 0 := by funext c j; exact hx0 c j
  have hL : ∀ c j, I.L (I.xOf z) c j = 0 := by
    intro c j; rw [hxz]; simp [Inst.L, Inst.lam]
  -- the `π`-part vanishes
  have hp0 : ∀ c, I.piOf z c = 0 := by
    intro c
    obtain ⟨j, hj⟩ := hZ c
    have h0 := hrow ((rowEquiv I.t I.k).symm (.inr ((c, j), 0)))
    have h1 := hrow ((rowEquiv I.t I.k).symm (.inr ((c, j), 1)))
    rw [rowVal_X, hj, hL] at h0 h1
    simp [coefX, coefL] at h0 h1
    linarith
  have hz0 : z = fun _ => 0 := vec_ext hxz (by funext c; exact hp0 c)
  funext v
  have := congrFun hz0 v
  simp only [z] at this
  exact_mod_cast this

/-! ### D1, D2: the approximate point -/

section Approx

variable (I) in
/-- The approximate point `x̂ = Xs / q₀`. -/
noncomputable abbrev xhat (Xs : Fin I.t → Fin I.k → ℤ) (q₀ : ℕ) : Fin I.t → Fin I.k → ℝ :=
  ptOf Xs q₀

theorem ptOf_eq (Xs : Fin I.t → Fin I.k → ℤ) (q₀ : ℕ) :
    ptOf Xs q₀ = fun c j => (Xs c j : ℝ) / q₀ := rfl

theorem xOf_ptZ (Xs : Fin I.t → Fin I.k → ℤ) (q₀ : ℕ) :
    I.xOf (ptZ (kktZn I Xs) q₀) = ptOf Xs q₀ := by
  funext c j
  simp [Inst.xOf, Inst.colX, ptZ, kktZn, ptOf]

theorem piOf_ptZ (Xs : Fin I.t → Fin I.k → ℤ) {q₀ : ℕ} (hq : 0 < q₀) :
    I.piOf (ptZ (kktZn I Xs) q₀) = I.pi (ptOf Xs q₀) := by
  funext c
  rw [ptOf_eq, I.pi_div Xs (by exact_mod_cast hq)]
  simp [Inst.piOf, Inst.colP, ptZ, kktZn]

theorem kktZ_iff (Xs : Fin I.t → Fin I.k → ℤ) {q₀ : ℕ} (hq : 0 < q₀) (c : Fin I.t)
    (j : Fin I.k) :
    kktZ I Xs c j = true ↔
      ptOf Xs q₀ c j ≤ I.L (ptOf Xs q₀) c j - I.pi (ptOf Xs q₀) c := by
  have hq' : (0 : ℝ) < q₀ := by exact_mod_cast hq
  simp only [kktZ, decide_eq_true_eq, ptOf_eq]
  rw [I.L_div, I.pi_div Xs hq', ← sub_div, div_le_div_iff_of_pos_right hq']
  exact_mod_cast Iff.rfl

/-- Each term of the gap is at most the gap. -/
theorem term_le_gap {x : Fin I.t → Fin I.k → ℝ} (hx : I.InX x) (c : Fin I.t) (j : Fin I.k) :
    x c j * (I.L x c j - I.pi x c) ≤ I.gap x := by
  have hnn : ∀ c j, 0 ≤ x c j * (I.L x c j - I.pi x c) := fun c j =>
    mul_nonneg (hx.1 c j) (sub_nonneg.mpr (I.pi_le x c j))
  calc x c j * (I.L x c j - I.pi x c) ≤ ∑ j, x c j * (I.L x c j - I.pi x c) :=
        Finset.single_le_sum (fun j _ => hnn c j) (mem_univ j)
    _ ≤ I.gap x := Finset.single_le_sum (f := fun c => ∑ j, x c j * (I.L x c j - I.pi x c))
        (fun c _ => Finset.sum_nonneg fun j _ => hnn c j) (mem_univ c)

theorem le_of_sq_le_sq {a e : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) (h : a ^ 2 ≤ e ^ 2) : a ≤ e :=
  (pow_le_pow_iff_left₀ ha he two_ne_zero).mp h

theorem eps_lt_inv_k (hI : I.Valid) (ht : 0 < I.t) : eps I.t I.k < 1 / I.k := by
  have hk : 3 ≤ I.k := hI.1
  have hd : I.k < dimKKT I.t I.k := by
    unfold dimKKT; nlinarith
  have hE : I.k < bigE I.t I.k := by
    unfold bigE
    have h1 : 1 ≤ (dimKKT I.t I.k).factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : 1 ≤ entryBound I.k ^ (dimKKT I.t I.k + 1) :=
      Nat.one_le_pow _ _ (entryBound_pos hk)
    have h3 : I.k < 2 * (dimKKT I.t I.k ^ 2 + 1) := by nlinarith
    calc I.k < 2 * (dimKKT I.t I.k ^ 2 + 1) := h3
      _ ≤ 2 * (dimKKT I.t I.k ^ 2 + 1) * (dimKKT I.t I.k).factorial := Nat.le_mul_of_pos_right _ h1
      _ ≤ _ := Nat.le_mul_of_pos_right _ h2
  unfold eps
  have hk0 : (0 : ℝ) < I.k := by exact_mod_cast (by omega : 0 < I.k)
  rw [div_lt_div_iff₀ (by exact_mod_cast bigE_pos I.t hk) hk0]
  simp only [one_mul]
  exact_mod_cast hE

/-- **D2.** Every cycle has an option outside the pattern `Z`. -/
theorem exists_not_Z (hI : I.Valid) (ht : 0 < I.t) {Xs : Fin I.t → Fin I.k → ℤ} {q₀ : ℕ}
    (hq : 0 < q₀) (hX : I.InX (ptOf Xs q₀)) (hgap : I.gap (ptOf Xs q₀) ≤ eps I.t I.k ^ 2)
    (c : Fin I.t) : ∃ j, kktZ I Xs c j = false := by
  by_contra hcon
  simp only [not_exists, Bool.not_eq_false] at hcon
  set x := ptOf Xs q₀ with hxdef
  have hk3 := hI.1
  have hk0 : (0 : ℝ) < I.k := by exact_mod_cast (by omega : 0 < I.k)
  -- some option has weight `≥ 1/k`
  obtain ⟨j, hj⟩ : ∃ j, 1 / (I.k : ℝ) ≤ x c j := by
    by_contra hall
    simp only [not_exists, not_le] at hall
    have : ∑ j, x c j < ∑ _j : Fin I.k, 1 / (I.k : ℝ) :=
      Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, mem_univ _⟩ fun j _ => hall j
    rw [hX.2 c] at this
    simp at this
    rw [mul_inv_cancel₀ hk0.ne'] at this
    exact lt_irrefl _ this
  have hZ := (kktZ_iff Xs hq c j).mp (hcon j)
  have h1 := term_le_gap hX c j
  have hsq : x c j ^ 2 ≤ eps I.t I.k ^ 2 := by
    have : x c j * x c j ≤ x c j * (I.L x c j - I.pi x c) :=
      mul_le_mul_of_nonneg_left hZ (hX.1 c j)
    nlinarith
  have hle := le_of_sq_le_sq (hX.1 c j) (eps_pos I.t hI.1).le hsq
  linarith [eps_lt_inv_k hI ht]

/-- **D1.** The approximate point `z̃ = (x̂, π̂)` satisfies `G z̃ ≤ h + ε 𝟙`. -/
theorem kkt_approx {Xs : Fin I.t → Fin I.k → ℤ} {q₀ : ℕ} (hq : 0 < q₀)
    (hX : I.InX (ptOf Xs q₀)) (hgap : I.gap (ptOf Xs q₀) ≤ eps I.t I.k ^ 2)
    (hε : 0 ≤ eps I.t I.k) :
    ∀ i, rowVal (kktG I (kktZ I Xs)) i (ptZ (kktZn I Xs) q₀) ≤ kktH I i + eps I.t I.k := by
  set x := ptOf Xs q₀ with hxdef
  apply forall_rows
  · intro c s
    rw [rowVal_S, kktH_S, xOf_ptZ, hX.2 c]
    fin_cases s <;> simp [sgnS] <;> linarith
  · intro c j b
    rw [rowVal_X, kktH_X, xOf_ptZ, piOf_ptZ Xs hq]
    have hxn := hX.1 c j
    have hsn : 0 ≤ I.L x c j - I.pi x c := sub_nonneg.mpr (I.pi_le x c j)
    have hterm := term_le_gap hX c j
    cases hzc : kktZ I Xs c j
    · -- `(c,j) ∉ Z`: `ŝ < x̂`, hence `ŝ ≤ ε`
      have hlt : I.L x c j - I.pi x c < x c j := by
        have := (kktZ_iff Xs hq c j).not.mp (by simp [hzc])
        exact not_le.mp this
      have hsq : (I.L x c j - I.pi x c) ^ 2 ≤ eps I.t I.k ^ 2 := by nlinarith
      have hs := le_of_sq_le_sq hsn hε hsq
      fin_cases b <;> simp [coefX, coefL] <;> linarith
    · -- `(c,j) ∈ Z`: `x̂ ≤ ŝ`, hence `x̂ ≤ ε`
      have hle := (kktZ_iff Xs hq c j).mp hzc
      have hsq : x c j ^ 2 ≤ eps I.t I.k ^ 2 := by nlinarith
      have hx := le_of_sq_le_sq hxn hε hsq
      fin_cases b <;> simp [coefX, coefL] <;> linarith

end Approx

/-! ### D3: a solution of the KKT system is optimal -/

/-- **D3.** If `z* = (x*, π*)` satisfies `G z* ≤ h`, then `x* ∈ 𝒳`, and `x*` minimizes `F` (and,
for a valid instance, `Φ`) over `𝒳`. -/
theorem kkt_optimal (Z : Fin I.t → Fin I.k → Bool) {z : Fin (dimKKT I.t I.k) → ℝ}
    (hz : ∀ i, rowVal (kktG I Z) i z ≤ kktH I i) :
    I.InX (I.xOf z) ∧ ∀ x, I.InX x → I.F (I.xOf z) ≤ I.F x ∧ (I.Valid → I.Phi (I.xOf z) ≤ I.Phi x) := by
  have hrowS : ∀ c s, (sgnS s : ℝ) * ∑ j, I.xOf z c j ≤ sgnS s := by
    intro c s
    have := hz ((rowEquiv I.t I.k).symm (.inl (c, s)))
    rwa [rowVal_S, kktH_S] at this
  have hrowX : ∀ c j b, (coefX (Z c j) b : ℝ) * I.xOf z c j +
      (coefL (Z c j) b : ℝ) * (I.L (I.xOf z) c j - I.piOf z c) ≤ 0 := by
    intro c j b
    have := hz ((rowEquiv I.t I.k).symm (.inr ((c, j), b)))
    rwa [rowVal_X, kktH_X, Int.cast_zero] at this
  have hsum : ∀ c, ∑ j, I.xOf z c j = 1 := by
    intro c
    have h0 := hrowS c 0
    have h1 := hrowS c 1
    simp [sgnS] at h0 h1
    linarith
  have hcases : ∀ c j, 0 ≤ I.xOf z c j ∧ I.piOf z c ≤ I.L (I.xOf z) c j ∧
      I.xOf z c j * (I.L (I.xOf z) c j - I.piOf z c) = 0 := by
    intro c j
    have h0 := hrowX c j 0
    have h1 := hrowX c j 1
    have h2 := hrowX c j 2
    cases hzc : Z c j <;> simp [coefX, coefL, hzc] at h0 h1 h2
    · refine ⟨by linarith, by linarith, ?_⟩
      have : I.L (I.xOf z) c j - I.piOf z c = 0 := by linarith
      rw [this, mul_zero]
    · refine ⟨by linarith, by linarith, ?_⟩
      have : I.xOf z c j = 0 := by linarith
      rw [this, zero_mul]
  have hX : I.InX (I.xOf z) := ⟨fun c j => (hcases c j).1, hsum⟩
  refine ⟨hX, fun x hx => ⟨?_, fun hI => ?_⟩⟩
  · exact Inst.F_le_of_kkt hX (fun c j => (hcases c j).2.1) (fun c j => (hcases c j).2.2) hx
  · exact Inst.Phi_le_of_kkt hI hX (fun c j => (hcases c j).2.1) (fun c j => (hcases c j).2.2) hx

/-! ### Magnitudes on the KKT system -/

/-- Every point of `{G z ≤ h + ε}` (`k ε ≤ 1`, every cycle with an option outside `Z`) has
`|x_{c,j}| ≤ 2` and `|π_c| ≤ 2k²t + 1`, hence all coordinates at most `2k²t + 2`. -/
theorem kkt_box (hI : I.Valid) (Z : Fin I.t → Fin I.k → Bool) (hZ : ∀ c, ∃ j, Z c j = false)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεk : (I.k : ℝ) * ε ≤ 1) {z : Fin (dimKKT I.t I.k) → ℝ}
    (hz : ∀ i, rowVal (kktG I Z) i z ≤ kktH I i + ε) (v : Fin (dimKKT I.t I.k)) :
    |z v| ≤ 2 * (I.k : ℝ) ^ 2 * I.t + 2 := by
  have hk : 3 ≤ I.k := hI.1
  have hε1 : ε ≤ 1 := by
    have : (1 : ℝ) ≤ I.k := by exact_mod_cast (by omega : 1 ≤ I.k)
    nlinarith
  -- lower bounds `x ≥ −ε` and the cycle sums
  have hlow : ∀ c j, -ε ≤ I.xOf z c j := by
    intro c j
    cases hzc : Z c j
    · have := hz ((rowEquiv I.t I.k).symm (.inr ((c, j), 2)))
      rw [rowVal_X, kktH_X, hzc] at this
      simp [coefX, coefL] at this
      linarith
    · have := hz ((rowEquiv I.t I.k).symm (.inr ((c, j), 1)))
      rw [rowVal_X, kktH_X, hzc] at this
      simp [coefX, coefL] at this
      linarith
  have hup : ∀ c, ∑ j, I.xOf z c j ≤ 1 + ε := by
    intro c
    have := hz ((rowEquiv I.t I.k).symm (.inl (c, 0)))
    rw [rowVal_S, kktH_S] at this
    simpa [sgnS] using this
  have hxb : ∀ c j, |I.xOf z c j| ≤ 2 := by
    intro c j
    rw [abs_le]
    refine ⟨by linarith [hlow c j], ?_⟩
    have hrest : -(((I.k : ℝ) - 1) * ε) ≤ ∑ j' ∈ Finset.univ.erase j, I.xOf z c j' := by
      calc -(((I.k : ℝ) - 1) * ε) = ∑ _j' ∈ Finset.univ.erase j, -ε := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ j), Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast [Nat.cast_sub (by omega : 1 ≤ I.k)]
            ring
        _ ≤ _ := Finset.sum_le_sum fun j' _ => hlow c j'
    have hsplit := Finset.add_sum_erase Finset.univ (I.xOf z c) (mem_univ j)
    have := hup c
    nlinarith
  -- `π_c` is within `ε` of a path load `L(x)_{c,j}`, `|L(x)_{c,j}| ≤ 2(k − 2) k t`
  have hLb : ∀ c j, |I.L (I.xOf z) c j| ≤ 2 * ((I.k - 2 : ℕ) : ℝ) * I.k * I.t := by
    intro c j
    rw [I.L_eq_H]
    calc |∑ c', ∑ j', (I.H c j c' j' : ℝ) * I.xOf z c' j'|
        ≤ ∑ c', ∑ j', |(I.H c j c' j' : ℝ) * I.xOf z c' j'| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun c' _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _c' : Fin I.t, ∑ _j' : Fin I.k, ((I.k - 2 : ℕ) : ℝ) * 2 := by
          refine Finset.sum_le_sum fun c' _ => Finset.sum_le_sum fun j' _ => ?_
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_mul (by exact_mod_cast Inst.H_le hI c j c' j') (hxb c' j') (abs_nonneg _)
            (Nat.cast_nonneg _)
      _ = 2 * ((I.k - 2 : ℕ) : ℝ) * I.k * I.t := by simp; ring
  have hpb : ∀ c, |I.piOf z c| ≤ 2 * (I.k : ℝ) ^ 2 * I.t + 1 := by
    intro c
    obtain ⟨j, hj⟩ := hZ c
    have h0 := hz ((rowEquiv I.t I.k).symm (.inr ((c, j), 0)))
    have h1 := hz ((rowEquiv I.t I.k).symm (.inr ((c, j), 1)))
    rw [rowVal_X, kktH_X, hj] at h0 h1
    simp [coefX, coefL] at h0 h1
    have hL := hLb c j
    have hk2 : ((I.k - 2 : ℕ) : ℝ) ≤ I.k := by exact_mod_cast Nat.sub_le _ _
    have hkt : 2 * ((I.k - 2 : ℕ) : ℝ) * I.k * I.t ≤ 2 * (I.k : ℝ) ^ 2 * I.t := by
      have : (0 : ℝ) ≤ I.k * I.t := by positivity
      nlinarith
    rw [abs_le] at hL ⊢
    constructor <;> linarith
  have hbig : (0 : ℝ) ≤ 2 * (I.k : ℝ) ^ 2 * I.t := by positivity
  have := (colEquiv I.t I.k).symm_apply_apply v
  rcases hv : colEquiv I.t I.k v with ⟨c, j⟩ | c
  · rw [hv] at this
    rw [← this]
    have := hxb c j
    simp only [Inst.xOf, Inst.colX] at this
    linarith
  · rw [hv] at this
    rw [← this]
    have := hpb c
    simp only [Inst.piOf, Inst.colP] at this
    linarith

/-! ### D4, D5: the output -/

/-- **D5** (the exact rounding). If `x̂ = Xs/q₀ ∈ 𝒳` and `gap(x̂) ≤ ε²` (`ε = 1/E`),
then `exactFrom` returns `(D, W)` with `D > 0`, `∑_j W_{c,j} = D` and `W/D` minimizing `F` and
`Φ` over `𝒳`. -/
theorem exactFrom_optimal (hI : I.Valid) (ht : 0 < I.t) {Xs : Fin I.t → Fin I.k → ℤ} {q₀ : ℕ}
    (hq : 0 < q₀) (hX : I.InX (ptOf Xs q₀)) (hgap : I.gap (ptOf Xs q₀) ≤ eps I.t I.k ^ 2) :
    0 < (I.exactFrom Xs q₀).1 ∧ (∀ c, ∑ j, (I.exactFrom Xs q₀).2 c j = (I.exactFrom Xs q₀).1) ∧
      ∀ x, I.InX x →
        I.F (fun c j => ((I.exactFrom Xs q₀).2 c j : ℝ) / (I.exactFrom Xs q₀).1) ≤ I.F x ∧
        I.Phi (fun c j => ((I.exactFrom Xs q₀).2 c j : ℝ) / (I.exactFrom Xs q₀).1) ≤ I.Phi x := by
  have hZ := exists_not_Z hI ht hq hX hgap
  have hb := kkt_bdd (kktZ I Xs) hZ
  have hA₀ : 1 ≤ entryBound I.k := entryBound_pos hI.1
  have hz := kkt_approx hq hX hgap (eps_pos I.t hI.1).le
  have hz' : ∀ i, rowVal (kktG I (kktZ I Xs)) i (ptZ (kktZn I Xs) q₀) ≤
      kktH I i + 1 / (bigE I.t I.k : ℝ) := hz
  obtain ⟨s, hs, hinv, hstar⟩ :=
    moveRun_exact hb hA₀ (kktG_entry_le hI _) (E := bigE I.t I.k) le_rfl hq hz'
  have hΔ := hinv.det_ne
  obtain ⟨hXs, hmin⟩ := kkt_optimal (kktZ I Xs) hstar
  -- `D x*_{c,j} = sgn(Δ) (Aj h_T)_{(c,j)} ≥ 0`
  have hW : ∀ c j, ((s.Δ.sign * zNum (kktH I) s (I.colX c j)).toNat : ℝ) =
      |(s.Δ : ℝ)| * I.xOf (zStar (kktH I) s) c j := by
    intro c j
    have hΔr : (s.Δ : ℝ) ≠ 0 := by exact_mod_cast hΔ
    have hsg : ((s.Δ.sign : ℤ) : ℝ) * (s.Δ : ℝ) = |(s.Δ : ℝ)| := by
      rw [← Int.cast_mul, Int.sign_mul_self_eq_abs, Int.cast_abs]
    have hval : ((s.Δ.sign * zNum (kktH I) s (I.colX c j) : ℤ) : ℝ) =
        |(s.Δ : ℝ)| * I.xOf (zStar (kktH I) s) c j := by
      simp only [Inst.xOf, zStar, Int.cast_mul]
      rw [← hsg]
      field_simp
    have hnn : 0 ≤ s.Δ.sign * zNum (kktH I) s (I.colX c j) := by
      have : (0 : ℝ) ≤ ((s.Δ.sign * zNum (kktH I) s (I.colX c j) : ℤ) : ℝ) := by
        rw [hval]; exact mul_nonneg (abs_nonneg _) (hXs.1 c j)
      exact_mod_cast this
    rw [← hval, ← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  have hD : ((s.Δ.natAbs : ℕ) : ℝ) = |(s.Δ : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hDpos : (0 : ℝ) < |(s.Δ : ℝ)| := abs_pos.mpr (by exact_mod_cast hΔ)
  have hpt : (fun c j => ((s.Δ.sign * zNum (kktH I) s (I.colX c j)).toNat : ℝ) /
      ((s.Δ.natAbs : ℕ) : ℝ)) = I.xOf (zStar (kktH I) s) := by
    funext c j
    rw [hW, hD]
    field_simp
  unfold Inst.exactFrom
  rw [hs]
  simp only
  refine ⟨Int.natAbs_pos.mpr hΔ, fun c => ?_, fun x hx => ?_⟩
  · have : ((∑ j, (s.Δ.sign * zNum (kktH I) s (I.colX c j)).toNat : ℕ) : ℝ) =
        ((s.Δ.natAbs : ℕ) : ℝ) := by
      push_cast
      simp only [hW, ← Finset.mul_sum, hXs.2 c, mul_one, hD]
    exact_mod_cast this
  · rw [hpt]
    exact ⟨(hmin x hx).1, (hmin x hx).2 hI⟩

/-- **Magnitudes of Phase M on the KKT system**: under the hypotheses of
`exactFrom_optimal`, every state of Phase M after `r` steps has `|Δ|, |Aj_{ab}| ≤ d!·A₀^d`,
`q_r ≤ q₀ (E·d!·A₀^d)^r` and `|Zn_v| ≤ (2k²t + 2) q_r` (`d = (k+1)t`, `A₀ = k − 2`,
`E = bigE t k`). -/
theorem exactFrom_magnitudes (hI : I.Valid) (ht : 0 < I.t) {Xs : Fin I.t → Fin I.k → ℤ}
    {q₀ : ℕ} (hq : 0 < q₀) (hX : I.InX (ptOf Xs q₀))
    (hgap : I.gap (ptOf Xs q₀) ≤ eps I.t I.k ^ 2) (r : ℕ) (hr : r ≤ dimKKT I.t I.k)
    (s : MState (nRows I.t I.k) (dimKKT I.t I.k) r)
    (hs : moveAux (kktG I (kktZ I Xs)) (kktH I) (bigE I.t I.k) (kktZn I Xs) q₀ r hr = some s) :
    |s.Δ| ≤ (dimKKT I.t I.k).factorial * (entryBound I.k : ℤ) ^ dimKKT I.t I.k ∧
      (∀ a b, |s.Aj a b| ≤ (dimKKT I.t I.k).factorial * (entryBound I.k : ℤ) ^ dimKKT I.t I.k) ∧
      s.q ≤ q₀ * (bigE I.t I.k * (dimKKT I.t I.k).factorial *
        entryBound I.k ^ dimKKT I.t I.k) ^ r ∧
      ∀ v, |(s.Zn v : ℝ)| ≤ (2 * (I.k : ℝ) ^ 2 * I.t + 2) * s.q := by
  have hA₀ : 1 ≤ entryBound I.k := entryBound_pos hI.1
  have hEpos : 0 < bigE I.t I.k := bigE_pos I.t hI.1
  have hz := kkt_approx hq hX hgap (eps_pos I.t hI.1).le
  have hz' : ∀ i, rowVal (kktG I (kktZ I Xs)) i (ptZ (kktZn I Xs) q₀) ≤
      kktH I i + 1 / (bigE I.t I.k : ℝ) := hz
  obtain ⟨hinv, hΔ, hAj, hqb⟩ :=
    moveAux_bounds hEpos hA₀ (kktG_entry_le hI _) hq hz' r hr s hs
  refine ⟨hΔ.trans (factorial_pow_mono hA₀ hr), fun a b => (hAj a b).trans
    (factorial_pow_mono hA₀ hr), hqb, fun v => hinv.Zn_bound (fun z hz v => ?_) v⟩
  have hεk : (I.k : ℝ) * (1 / (bigE I.t I.k : ℝ)) ≤ 1 := by
    have := (eps_lt_inv_k hI ht).le
    unfold eps at this
    have hk0 : (0 : ℝ) < I.k := by exact_mod_cast (by have := hI.1; omega : 0 < I.k)
    rw [le_div_iff₀ hk0] at this
    linarith
  exact kkt_box hI _ (exists_not_Z hI ht hq hX hgap) (by positivity) hεk hz v

/-! ### Lemma 16 -/

/-- **EXACT** on the option lists `opts` (`k` options per cycle) over the edge list `es`, with
Phase E given as a parameter: Phase E on the instance `ofOpts es k opts`, then the exact
rounding `exactFrom`; `(1, [])` when there is no cycle. -/
def solveExactWith (phaseE : (I : Inst) → Option ((Fin I.t → Fin I.k → ℤ) × ℕ))
    (es : List Edge) (k : ℕ) (opts : List (List (List Edge))) : ℕ × List (List ℕ) :=
  if opts.length = 0 then (1, []) else
    match phaseE (ofOpts es k opts) with
    | some (Xs, q) =>
      (((ofOpts es k opts).exactFrom Xs q).1, wlists ((ofOpts es k opts).exactFrom Xs q).2)
    | none => (1, [])

/-- **Lemma 16** (exact optimality, modulo Phase E). For any Phase E procedure meeting
`PhaseESpec` (Part B, Theorem B10), `solveExactWith` returns an optimal fractional solution of
the relaxation of Section 7.2 on the `k`-cycles of every duplicate-free graph: exactly the
hypothesis `hopt : OptimalFractional g D R` of Theorems 16 and 17, with
`R.map Prod.fst = (cycles g k).map selectedOptions`. -/
theorem solveExactWith_optimal (phaseE : (I : Inst) → Option ((Fin I.t → Fin I.k → ℤ) × ℕ))
    (hE : PhaseESpec phaseE) {g : Graph} (hg : g.Nodup) (k : ℕ) :
    let opts := (cycles g k).map selectedOptions
    OptimalFractional g (solveExactWith phaseE g k opts).1
      (opts.zip (solveExactWith phaseE g k opts).2) := by
  intro opts
  have hk : ∀ o ∈ opts, o.length = k ∧ ∀ p ∈ o, p.Nodup := fun o ho =>
    ⟨(cycles_opts g k o ho).1, fun p hp => ((cycles_opts g k o ho).2 p hp).1⟩
  by_cases ht : opts.length = 0
  · -- no cycle
    have hsol : solveExactWith phaseE g k opts = (1, wlists (fun (c : Fin opts.length)
        (_ : Fin k) => (0 : ℕ))) := by
      have hnil : opts = [] := List.eq_nil_of_length_eq_zero ht
      simp only [solveExactWith, ht, ↓reduceIte, Prod.mk.injEq, true_and]
      unfold wlists
      rw [List.ofFn_eq_nil_iff.mpr ht]
    rw [hsol]
    refine optimalFractional_of_min hk one_pos _ (fun c => absurd c.2 (by omega)) fun x _ => ?_
    have hl : ∀ y : Fin (ofOpts g k opts).t → Fin (ofOpts g k opts).k → ℝ,
        ∀ e, (ofOpts g k opts).lam y e = 0 := by
      intro y e
      unfold Inst.lam
      exact Finset.sum_eq_zero fun c _ => absurd c.2 (by simp [ofOpts, ht])
    simp [Inst.Phi, hl]
  · have hne : cycles g k ≠ [] := by
      intro h; apply ht; simp [opts, h]
    have hI := ofOpts_valid_cycles hg hne
    have htpos : 0 < (ofOpts g k opts).t := Nat.pos_of_ne_zero ht
    obtain ⟨Xs, q, hphase, hq, hX, hgap⟩ := hE _ hI htpos
    obtain ⟨hD, hW, hmin⟩ := exactFrom_optimal hI htpos hq hX hgap
    have hphase' : phaseE (ofOpts g k opts) = some (Xs, q) := hphase
    have hsol : solveExactWith phaseE g k opts =
        (((ofOpts g k opts).exactFrom Xs q).1, wlists ((ofOpts g k opts).exactFrom Xs q).2) := by
      simp only [solveExactWith, ht, ↓reduceIte, hphase']
    rw [hsol]
    exact optimalFractional_of_min hk hD _ hW fun x hx => (hmin x hx).2

/-- The output of `solveExactWith` keeps the option lists of the cycles (`R.map Prod.fst = opts`,
the hypothesis `hR` of Theorems 16 and 17). -/
theorem solveExactWith_map_fst (phaseE : (I : Inst) → Option ((Fin I.t → Fin I.k → ℤ) × ℕ))
    (hE : PhaseESpec phaseE) {g : Graph} (hg : g.Nodup) (k : ℕ) :
    let opts := (cycles g k).map selectedOptions
    (opts.zip (solveExactWith phaseE g k opts).2).map Prod.fst = opts := by
  intro opts
  by_cases ht : opts.length = 0
  · have hnil : opts = [] := List.eq_nil_of_length_eq_zero ht
    rw [hnil]
    simp
  · have hne : cycles g k ≠ [] := by
      intro h; apply ht; simp [opts, h]
    obtain ⟨Xs, q, hphase, -⟩ := hE _ (ofOpts_valid_cycles hg hne) (Nat.pos_of_ne_zero ht)
    have hphase' : phaseE (ofOpts g k opts) = some (Xs, q) := hphase
    simp only [solveExactWith, ht, ↓reduceIte, hphase']
    exact map_fst_zip_wlists opts _

/-- The interface to Section 7 in use: Algorithm 2 run on the solution computed by
`solveExactWith` satisfies Theorem 18's bound `k c(ps) ≤ k c(qs) + (k − 2) t`. -/
theorem rounding_solveExactWith (phaseE : (I : Inst) → Option ((Fin I.t → Fin I.k → ℤ) × ℕ))
    (hE : PhaseESpec phaseE) {g : Graph} (hg : g.Nodup) (k : ℕ) {ps qs : List (List Edge)}
    (hrun : RoundingRun (solveExactWith phaseE g k ((cycles g k).map selectedOptions)).1 []
      (((cycles g k).map selectedOptions).zip
        (solveExactWith phaseE g k ((cycles g k).map selectedOptions)).2) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    k * cost ps ≤ k * cost qs + (k - 2) * (cycles g k).length :=
  conditional_rounding_cost_bound hg (solveExactWith_map_fst phaseE hE hg k)
    (solveExactWith_optimal phaseE hE hg k) hrun hq

end STACS2027.Runtimes.ConvexQP
