module

public import Runtimes.ConvexQP.EllGeneric
public import Runtimes.ConvexQP.QP
import Mathlib.Tactic

/-!
# Lemma 16, Phase E: the rational central-cut ellipsoid method on integers

Everything here is computed on integers, exactly
as the RAM will compute it.

* **Constants** (`consts t k`): `n = (k−1)t` (`nDim`), `n/r_K = n·4C₀E⁴(k−2)²t²(k−1)`
  (`radInv`, an integer), `N = 16n(n+1)⌈log₂(n/r_K)⌉ + 1` (`iters`),
  `p = 4⌈N/n⌉ + 3⌈log₂(n+1)⌉ + 11` (`prec`), `E = bigE t k` (so `g₀ = ε² = 1/E²`) and
  `c₁ = (n²/(n²−1))(1+η)³ = cN/cD` with `cN = n²(32n(n+1)+1)³`, `cD = (n²−1)(32n(n+1))³`
  (not reduced; `roundDiv` only depends on the quotient). `⌈a/b⌉ = (a+b−1)/b`,
  `⌈log₂ x⌉ = Nat.clog 2 x`.
* **State** (`EllState`): `As : Idx I → ℤ`, `Qs : Matrix (Idx I) (Idx I) ℤ` over the reduced
  coordinates `Idx I = Fin t × Fin (k−1)` (lexicographic `idxList`), standing for the center
  `As/2^p` and the matrix `Qs/2^p`. Initially `As = 2^{p−1}`, `Qs = n·2^{p−2}·I` (`ellInit`).
* **One iteration** (`ellCut`, `ellUpdate`, `ellStep`): E1 the first negative coordinate (cut
  `−e_i`), else the first cycle with block sum `> 2^p` (cut `∑_j e_{(c,j)}`); E2 at a feasible
  center, `Xs = xiq 2^p As` (`feasPt`), success iff `gap(Xs)·E² ≤ 4^p`; E3 the gradient cut
  `g_{(c,j)} = L(Xs)_{c,j} − L(Xs)_{c,k}` (`gradRed`); E4 `u = Qs g`, `G = g·u`,
  `S = ⌊√(G·2^{3p})⌋`, `As_i ← As_i − roundDiv(u_i 2^{2p}, (n+1)S)`,
  `Qs_{ij} ← roundDiv(cN(Qs_{ij}(n+1)G − 2u_iu_j), cD(n+1)G)`.
* **The run** (`ellIter`, `ellRun`): at most `N` iterations; `ellRun` is the first success.

The real view (`QR`, `aR`: division by `2^p`) and the first fact used by B10: the update E4 is
an `ϵ`-rounding (`ϵ = 2^{−p−1}`) of the rounded central cut `((1+η)³Q⁺, a − Qg/((n+1)s))` with
`s = S/2^{2p}` (`ellUpdate_round`). The validity of the cuts, the success output and B10 itself
are in `EllSuccess.lean`; the magnitudes in `EllMag.lean`.
-/

@[expose] public section

namespace STACS2027.Runtimes.ConvexQP

open Matrix Finset

/-! ### Constants -/

/-- `n = (k − 1) t`: the dimension of the ellipsoid. -/
def nDim (t k : ℕ) : ℕ := (k - 1) * t

/-- `n / r_K = n · 4 C₀ E⁴ (k−2)² t² (k−1)` (an integer). -/
def radInv (t k : ℕ) : ℕ :=
  nDim t k * (4 * curv t k * bigE t k ^ 4 * (k - 2) ^ 2 * t ^ 2 * (k - 1))

/-- `⌈log₂ (n / r_K)⌉`. -/
def logRad (t k : ℕ) : ℕ := Nat.clog 2 (radInv t k)

/-- `N = 16 n (n+1) ⌈log₂ (n/r_K)⌉ + 1`: the number of iterations. -/
def iters (t k : ℕ) : ℕ := 16 * nDim t k * (nDim t k + 1) * logRad t k + 1

/-- `p = 4 ⌈N/n⌉ + 3 ⌈log₂ (n+1)⌉ + 11`: the number of fraction bits. -/
def prec (t k : ℕ) : ℕ :=
  4 * ((iters t k + nDim t k - 1) / nDim t k) + 3 * Nat.clog 2 (nDim t k + 1) + 11

/-- The numerator of `c₁ = (n²/(n²−1))(1+η)³`: `n² (32n(n+1) + 1)³`. -/
def cNum (t k : ℕ) : ℕ := nDim t k ^ 2 * (32 * nDim t k * (nDim t k + 1) + 1) ^ 3

/-- The denominator of `c₁`: `(n² − 1) (32n(n+1))³`. -/
def cDen (t k : ℕ) : ℕ := (nDim t k ^ 2 - 1) * (32 * nDim t k * (nDim t k + 1)) ^ 3

/-- The constants of Phase E. -/
structure Consts where
  /-- The dimension `n`. -/
  n : ℕ
  /-- The iteration bound `N`. -/
  N : ℕ
  /-- The precision `p` (fraction bits). -/
  p : ℕ
  /-- `E = 1/ε` (the success test is `gap·E² ≤ 4^p`). -/
  E : ℕ
  /-- Numerator of `c₁`. -/
  cN : ℕ
  /-- Denominator of `c₁`. -/
  cD : ℕ

/-- The constants for `t` cycles of length `k`. -/
def consts (t k : ℕ) : Consts := ⟨nDim t k, iters t k, prec t k, bigE t k, cNum t k, cDen t k⟩

/-! ### The state and one iteration -/

/-- The reduced coordinates `(c, j)`, `j < k − 1`. -/
abbrev Idx (I : Inst) := Fin I.t × Fin (I.k - 1)

/-- The state of Phase E: center `As/2^p` and matrix `Qs/2^p`. -/
structure EllState (I : Inst) where
  /-- The scaled center. -/
  As : Idx I → ℤ
  /-- The scaled matrix (symmetric). -/
  Qs : Matrix (Idx I) (Idx I) ℤ

/-- The reduced coordinates in lexicographic order. -/
def idxList (I : Inst) : List (Idx I) :=
  (List.finRange I.t).flatMap fun c => (List.finRange (I.k - 1)).map fun j => (c, j)

/-- E1: the first (lexicographic) negative coordinate of the center. -/
def firstNeg (I : Inst) (As : Idx I → ℤ) : Option (Idx I) :=
  (idxList I).find? fun i => decide (As i < 0)

/-- The block sum `∑_{j<k} As_{(c,j)}` of cycle `c`. -/
def blockSum (I : Inst) (As : Idx I → ℤ) (c : Fin I.t) : ℤ := ∑ j, As (c, j)

/-- E1: the first cycle whose block sum exceeds `2^p`. -/
def firstOver (I : Inst) (p : ℕ) (As : Idx I → ℤ) : Option (Fin I.t) :=
  (List.finRange I.t).find? fun c => decide ((2 : ℤ) ^ p < blockSum I As c)

/-- E2: the completed point `Xs` (`Xs_{c,k} = 2^p − ∑_{j<k} As_{(c,j)}`). -/
def feasPt (I : Inst) (p : ℕ) (As : Idx I → ℤ) : Fin I.t → Fin I.k → ℤ :=
  I.xiq ((2 : ℤ) ^ p) fun c j => As (c, j)

/-- The cut `−e_i` (E1, negative coordinate). -/
def negCut (I : Inst) (i : Idx I) : Idx I → ℤ := fun i' => if i' = i then -1 else 0

/-- The cut `∑_{j<k} e_{(c,j)}` (E1, block sum too large). -/
def blockCut (I : Inst) (c : Fin I.t) : Idx I → ℤ := fun i' => if i'.1 = c then 1 else 0

/-- The gradient cut `g_{(c,j)} = L(Xs)_{c,j} − L(Xs)_{c,k}` (E3). -/
def gradCut (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) : Idx I → ℤ :=
  fun i => I.gradRed Xs i.1 i.2

/-- E1–E3: the cut vector of the iteration (`inl`) or the successful output `Xs` (`inr`). -/
def ellCut (I : Inst) (K : Consts) (As : Idx I → ℤ) :
    (Idx I → ℤ) ⊕ (Fin I.t → Fin I.k → ℤ) :=
  match firstNeg I As with
  | some i => .inl (negCut I i)
  | none =>
    match firstOver I K.p As with
    | some c => .inl (blockCut I c)
    | none =>
      if I.gap (feasPt I K.p As) * (K.E : ℤ) ^ 2 ≤ 4 ^ K.p then .inr (feasPt I K.p As)
      else .inl (gradCut I (feasPt I K.p As))

/-- E4: `u = Qs g`. -/
def updU (I : Inst) (st : EllState I) (g : Idx I → ℤ) : Idx I → ℤ := st.Qs *ᵥ g

/-- E4: `G = g·u`. -/
def updG (I : Inst) (st : EllState I) (g : Idx I → ℤ) : ℤ := g ⬝ᵥ updU I st g

/-- E4: `S = ⌊√(G·2^{3p})⌋`. -/
def updS (I : Inst) (K : Consts) (st : EllState I) (g : Idx I → ℤ) : ℕ :=
  Nat.sqrt ((updG I st g).toNat * 2 ^ (3 * K.p))

/-- E4: the update of center and matrix. -/
def ellUpdate (I : Inst) (K : Consts) (st : EllState I) (g : Idx I → ℤ) : EllState I where
  As i := st.As i -
    roundDiv (updU I st g i * 2 ^ (2 * K.p)) (((K.n : ℤ) + 1) * (updS I K st g : ℤ))
  Qs i j := roundDiv ((K.cN : ℤ) * (st.Qs i j * ((K.n : ℤ) + 1) * updG I st g -
      2 * updU I st g i * updU I st g j)) ((K.cD : ℤ) * ((K.n : ℤ) + 1) * updG I st g)

/-- One iteration E1–E4: the new state (`inl`) or the successful output (`inr`). -/
def ellStep (I : Inst) (K : Consts) (st : EllState I) :
    EllState I ⊕ (Fin I.t → Fin I.k → ℤ) :=
  match ellCut I K st.As with
  | .inl g => .inl (ellUpdate I K st g)
  | .inr Xs => .inr Xs

/-- The initial state: `As_i = 2^{p−1}`, `Qs = n 2^{p−2} I`. -/
def ellInit (I : Inst) (K : Consts) : EllState I where
  As _ := 2 ^ (K.p - 1)
  Qs i j := if i = j then (K.n : ℤ) * 2 ^ (K.p - 2) else 0

/-- The state after `i` iterations, or the first successful output. -/
def ellIter (I : Inst) (K : Consts) : ℕ → EllState I ⊕ (Fin I.t → Fin I.k → ℤ)
  | 0 => .inl (ellInit I K)
  | i + 1 =>
    match ellIter I K i with
    | .inl st => ellStep I K st
    | .inr Xs => .inr Xs

/-- **Phase E**: the output of the first successful iteration among the first `N`. -/
def ellRun (I : Inst) (K : Consts) : Option (Fin I.t → Fin I.k → ℤ) :=
  match ellIter I K K.N with
  | .inl _ => none
  | .inr Xs => some Xs

/-! ### Basic facts about the constants -/

theorem card_idx (I : Inst) : Fintype.card (Idx I) = nDim I.t I.k := by
  simp [Idx, nDim, Nat.mul_comm]

theorem nDim_ge_two {t k : ℕ} (ht : 0 < t) (hk : 3 ≤ k) : 2 ≤ nDim t k := by
  unfold nDim
  calc 2 ≤ k - 1 := by omega
    _ ≤ (k - 1) * t := Nat.le_mul_of_pos_right _ ht

theorem cNum_div_cDen {t k : ℕ} (hn : 2 ≤ nDim t k) :
    (cNum t k : ℝ) / cDen t k = (1 + etaOf (nDim t k)) ^ 3 * kap (nDim t k) := by
  unfold cNum cDen etaOf kap
  have h2 : (2 : ℝ) ≤ nDim t k := by exact_mod_cast hn
  have hsq : 1 ≤ nDim t k ^ 2 := by nlinarith
  push_cast [Nat.cast_sub hsq]
  have : (nDim t k : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp

theorem cDen_pos {t k : ℕ} (hn : 2 ≤ nDim t k) : 0 < cDen t k := by
  unfold cDen
  have : 1 < nDim t k ^ 2 := by nlinarith
  have : 0 < nDim t k ^ 2 - 1 := by omega
  positivity

theorem prec_ge {t k : ℕ} :
    4 * ((iters t k + nDim t k - 1) / nDim t k) + 2 * Nat.clog 2 (nDim t k + 1) + 9 ≤
      prec t k := by
  unfold prec; omega

theorem prec_ge_two (t k : ℕ) : 2 ≤ prec t k := by unfold prec; omega

/-! ### The list searches of E1 -/

theorem mem_idxList (I : Inst) (i : Idx I) : i ∈ idxList I := by
  simp [idxList]

theorem firstNeg_some {I : Inst} {As : Idx I → ℤ} {i : Idx I} (h : firstNeg I As = some i) :
    As i < 0 := by
  have := List.find?_some h
  simpa using this

theorem firstNeg_none {I : Inst} {As : Idx I → ℤ} (h : firstNeg I As = none) (i : Idx I) :
    0 ≤ As i := by
  have := List.find?_eq_none.mp h i (mem_idxList I i)
  simpa using this

theorem firstOver_some {I : Inst} {p : ℕ} {As : Idx I → ℤ} {c : Fin I.t}
    (h : firstOver I p As = some c) : (2 : ℤ) ^ p < blockSum I As c := by
  have := List.find?_some h
  simpa using this

theorem firstOver_none {I : Inst} {p : ℕ} {As : Idx I → ℤ} (h : firstOver I p As = none)
    (c : Fin I.t) : blockSum I As c ≤ 2 ^ p := by
  have := List.find?_eq_none.mp h c (List.mem_finRange c)
  simpa using this

/-! ### The real view -/

/-- The real matrix `Qs / 2^p`. -/
noncomputable def QR (p : ℕ) {I : Inst} (Qs : Matrix (Idx I) (Idx I) ℤ) :
    Matrix (Idx I) (Idx I) ℝ :=
  fun i j => (Qs i j : ℝ) / 2 ^ p

/-- The real vector `As / 2^p`. -/
noncomputable def aR (p : ℕ) {I : Inst} (As : Idx I → ℤ) : Idx I → ℝ :=
  fun i => (As i : ℝ) / 2 ^ p

/-- The real vector of an integer vector. -/
def gR {I : Inst} (g : Idx I → ℤ) : Idx I → ℝ := fun i => (g i : ℝ)

/-- The curried form of a vector over `Idx I`. -/
def cur {I : Inst} (y : Idx I → ℝ) : Fin I.t → Fin (I.k - 1) → ℝ := fun c j => y (c, j)

theorem mulVec_QR (p : ℕ) {I : Inst} (Qs : Matrix (Idx I) (Idx I) ℤ) (g : Idx I → ℤ)
    (i : Idx I) : (QR p Qs *ᵥ gR g) i = ((Qs *ᵥ g) i : ℝ) / 2 ^ p := by
  simp only [mulVec, dotProduct, QR, gR, Int.cast_sum, Int.cast_mul, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem qf_QR (p : ℕ) {I : Inst} (Qs : Matrix (Idx I) (Idx I) ℤ) (g : Idx I → ℤ) :
    qf (QR p Qs) (gR g) = ((g ⬝ᵥ (Qs *ᵥ g) : ℤ) : ℝ) / 2 ^ p := by
  unfold qf
  simp only [dotProduct, mulVec_QR, Int.cast_sum, Int.cast_mul, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by simp only [gR]; ring

theorem dot_gR {I : Inst} (g : Idx I → ℤ) (w : Idx I → ℤ) :
    gR g ⬝ᵥ gR w = ((g ⬝ᵥ w : ℤ) : ℝ) := by
  simp [dotProduct, gR]

/-- A nonzero integer vector has `g·g ≥ 1`. -/
theorem one_le_dot_gR {I : Inst} {g : Idx I → ℤ} (hg : gR g ≠ 0) : 1 ≤ gR g ⬝ᵥ gR g := by
  obtain ⟨i, hi⟩ : ∃ i, g i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hg (funext fun i => by simp [gR, h i])
  rw [dot_gR]
  have h1 : 1 ≤ g i * g i := by
    rcases lt_or_gt_of_ne hi with h | h <;> nlinarith
  have h2 : g i * g i ≤ g ⬝ᵥ g :=
    Finset.single_le_sum (f := fun j => g j * g j) (fun j _ => mul_self_nonneg (g j))
      (Finset.mem_univ i)
  exact_mod_cast h1.trans h2

theorem abs_div_pow_le {X : ℝ} (p : ℕ) (h : |X| ≤ 1 / 2) : |X / 2 ^ p| ≤ 1 / 2 ^ (p + 1) := by
  have hP : (0 : ℝ) < 2 ^ p := by positivity
  rw [abs_div, abs_of_pos hP, pow_succ, div_le_iff₀ hP]
  calc |X| ≤ 1 / 2 := h
    _ = 1 / (2 ^ p * 2) * 2 ^ p := by field_simp

/-- **E4 realizes the rounded central cut.** If `G > 0`, the update is a `2^{−p−1}`-rounding of
`((1+η)³ Q⁺, a − Qg/((n+1)s))` for the real data `Q = Qs/2^p`, `a = As/2^p`, `s = S/2^{2p}`
(for any constants with `c₁ = cN/cD = (1+η)³κ`). -/
theorem ellUpdate_round {I : Inst} (K : Consts) (hcD : 0 < K.cD)
    (hc : (K.cN : ℝ) / K.cD = (1 + etaOf K.n) ^ 3 * kap K.n) (st : EllState I)
    (hsymm : st.Qs.IsSymm) (g : Idx I → ℤ) (hG : 0 < updG I st g) :
    RoundOf (1 / 2 ^ (K.p + 1)) (QR K.p (ellUpdate I K st g).Qs) (aR K.p (ellUpdate I K st g).As)
      ((1 + etaOf K.n) ^ 3 • cutMat K.n (QR K.p st.Qs) (gR g))
      (cutCenter K.n (QR K.p st.Qs) (aR K.p st.As) (gR g)
        ((updS I K st g : ℝ) / 2 ^ (2 * K.p))) := by
  have hP : (0 : ℝ) < 2 ^ K.p := by positivity
  have hGR : (0 : ℝ) < updG I st g := by exact_mod_cast hG
  have hSpos : 0 < updS I K st g := by
    unfold updS
    apply Nat.sqrt_pos.mpr
    have : 0 < (updG I st g).toNat := by omega
    positivity
  have hSR : (0 : ℝ) < updS I K st g := by exact_mod_cast hSpos
  have hqf : qf (QR K.p st.Qs) (gR g) = (updG I st g : ℝ) / 2 ^ K.p := qf_QR K.p st.Qs g
  have hmv : ∀ i, (QR K.p st.Qs *ᵥ gR g) i = (updU I st g i : ℝ) / 2 ^ K.p :=
    fun i => mulVec_QR K.p st.Qs g i
  refine ⟨?_, ?_, ?_⟩
  · -- symmetry
    ext i j
    simp only [transpose_apply, QR, ellUpdate]
    congr 3
    rw [show st.Qs j i = st.Qs i j from by
      have := congrFun (congrFun hsymm i) j; simpa using this]
    ring
  · -- the center
    intro i
    have hv : (0 : ℤ) < ((K.n : ℤ) + 1) * (updS I K st g : ℤ) := by positivity
    have herr := roundDiv_err (updU I st g i * 2 ^ (2 * K.p)) hv
    simp only [aR, ellUpdate, cutCenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hmv]
    generalize roundDiv (updU I st g i * 2 ^ (2 * K.p)) (((K.n : ℤ) + 1) * (updS I K st g : ℤ))
      = R at herr ⊢
    push_cast at herr ⊢
    have e : ((st.As i : ℝ) - R) / 2 ^ K.p - ((st.As i : ℝ) / 2 ^ K.p -
        1 / ((K.n + 1) * ((updS I K st g : ℝ) / 2 ^ (2 * K.p))) *
          ((updU I st g i : ℝ) / 2 ^ K.p)) =
        -(((R : ℝ) - (updU I st g i : ℝ) * 2 ^ (2 * K.p) /
          ((K.n + 1) * (updS I K st g : ℝ))) / 2 ^ K.p) := by
      field_simp
      ring
    rw [e, abs_neg]
    exact abs_div_pow_le K.p herr
  · -- the matrix
    intro i j
    have hv : (0 : ℤ) < (K.cD : ℤ) * ((K.n : ℤ) + 1) * updG I st g := by
      have : (0 : ℤ) < K.cD := by exact_mod_cast hcD
      positivity
    have herr := roundDiv_err ((K.cN : ℤ) * (st.Qs i j * ((K.n : ℤ) + 1) * updG I st g -
      2 * updU I st g i * updU I st g j)) hv
    have hcDR : (0 : ℝ) < K.cD := by exact_mod_cast hcD
    simp only [QR, ellUpdate, Matrix.smul_apply, smul_eq_mul, cutMat, Matrix.sub_apply,
      vecMulVec_apply, hmv, hqf]
    generalize roundDiv ((K.cN : ℤ) * (st.Qs i j * ((K.n : ℤ) + 1) * updG I st g -
      2 * updU I st g i * updU I st g j)) ((K.cD : ℤ) * ((K.n : ℤ) + 1) * updG I st g)
      = R at herr ⊢
    push_cast at herr ⊢
    have e : (R : ℝ) / 2 ^ K.p - (1 + etaOf K.n) ^ 3 * (kap K.n * ((st.Qs i j : ℝ) / 2 ^ K.p -
        2 / ((K.n + 1) * ((updG I st g : ℝ) / 2 ^ K.p)) *
          ((updU I st g i : ℝ) / 2 ^ K.p * ((updU I st g j : ℝ) / 2 ^ K.p)))) =
        ((R : ℝ) - (K.cN : ℝ) * ((st.Qs i j : ℝ) * (K.n + 1) * updG I st g -
          2 * updU I st g i * updU I st g j) / (K.cD * (K.n + 1) * updG I st g)) / 2 ^ K.p := by
      rw [← mul_assoc, ← hc]
      field_simp
    rw [e]
    exact abs_div_pow_le K.p herr

end STACS2027.Runtimes.ConvexQP
