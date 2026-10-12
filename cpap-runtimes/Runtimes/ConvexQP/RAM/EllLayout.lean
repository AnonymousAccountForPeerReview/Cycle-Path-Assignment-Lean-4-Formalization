module

public import Runtimes.ConvexQP.RAM.QPIface
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: layout, flat indices, the state in memory

Phase E (the rational central-cut ellipsoid method, `EllPhase.lean`) on the add/subtract RAM.
This file fixes the registers (`470–499`), the flat layouts of the reduced vectors and matrices
(entry `(c, j) : Idx I` at the flat index `c (k−1) + j`, `flatR`, `flatM`), the searches of E1 as
searches over `List.range` (`negFind`, `overFind`), the memory layout of Phase E (`Lay`) and its
global registers (`EG`), and the transport of signed arrays through writes elsewhere.
See `NOTE-ell.md` for the layout.

**Space**: every block of Phase E is an `HTB S` triple (`*_specB`); its accesses lie in the layout
below `Ly.F` (`Lay.Ok.fits`: one inequality per region below `S ≥ Ly.F`) or in the scratch tables
of the arithmetic above `Ly.F` (`ellSc`, `EllCost.lean`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### Registers of Phase E (`470–499`) -/

/-- Base of the center `As` (`n` signed entries). -/
abbrev eA : ℕ := 470
/-- Base of the matrix `Qs` (`n × n`, row-major). -/
abbrev eQ : ℕ := 471
/-- Base of the path loads `L = H Xs` (`t k` entries). -/
abbrev eL : ℕ := 472
/-- Base of the cut vector `g` (`n` entries). -/
abbrev eG : ℕ := 473
/-- Base of `u = Qs g` (`n` entries). -/
abbrev eU : ℕ := 474
/-- `2 n` (the row stride of `Qs`). -/
abbrev e2N : ℕ := 475
/-- `k − 1`. -/
abbrev eK1 : ℕ := 476
/-- The number of iterations still allowed. -/
abbrev eCnt : ℕ := 477
/-- `2^p` (signed pair `478, 479`). -/
abbrev eP2 : ℕ := 478
/-- Outer counter. -/
abbrev eC : ℕ := 480
/-- Inner counter. -/
abbrev eJ : ℕ := 481
/-- Pointer. -/
abbrev ePa : ℕ := 482
/-- Pointer / flat index. -/
abbrev ePx : ℕ := 483
/-- Pointer. -/
abbrev ePy : ℕ := 484
/-- Result of the negativity search (`0` or index `+ 1`); mode of the cut. -/
abbrev eF1 : ℕ := 485
/-- Result of the block-sum search (`0` or cycle `+ 1`); mode of the cut. -/
abbrev eF2 : ℕ := 486
/-- Success flag of E2. -/
abbrev eDn : ℕ := 487
/-- Signed pair `488, 489`. -/
abbrev eV : ℕ := 488
/-- Signed pair `490, 491`. -/
abbrev eW : ℕ := 490
/-- Signed pair `492, 493`. -/
abbrev eS1 : ℕ := 492
/-- Signed pair `494, 495`. -/
abbrev eS2 : ℕ := 494
/-- Signed pair `496, 497`. -/
abbrev eS3 : ℕ := 496
/-- Temporary. -/
abbrev eT1 : ℕ := 498
/-- Temporary. -/
abbrev eT2 : ℕ := 499

/-- The registers written inside an iteration of Phase E: `rT`, the arithmetic library's block
`400–449` and the working registers `480–499`. -/
def ellW : List ℕ := rT :: (List.range' 400 50 ++ List.range' 480 20)

theorem arithW_sub_ellW : ∀ r ∈ arithW, r ∈ ellW := by decide

/-! ### Flat reduced vectors and matrices -/

/-- A reduced vector `y : Idx I → ℤ` flattened: entry `(c, j)` at `c (k − 1) + j` (`0` outside). -/
def flatR {I : Inst} (y : Idx I → ℤ) : ℕ → ℤ :=
  flat (fun (c : Fin I.t) (j : Fin (I.k - 1)) => y (c, j))

/-- A matrix over the reduced coordinates flattened: row `c (k−1) + j` is `flatR (Q (c, j))`. -/
def flatM {I : Inst} (Q : Matrix (Idx I) (Idx I) ℤ) (a b : ℕ) : ℤ :=
  flat (fun (c : Fin I.t) (j : Fin (I.k - 1)) => flatR (Q (c, j)) b) a

/-- The flat index of a reduced coordinate. -/
def fIdx {I : Inst} (i : Idx I) : ℕ := (i.1 : ℕ) * (I.k - 1) + i.2

theorem flatR_apply {I : Inst} (y : Idx I → ℤ) (c : Fin I.t) (j : Fin (I.k - 1)) :
    flatR y (c * (I.k - 1) + j) = y (c, j) :=
  flat_apply (fun (c : Fin I.t) (j : Fin (I.k - 1)) => y (c, j)) c j

theorem flatR_fIdx {I : Inst} (y : Idx I → ℤ) (i : Idx I) : flatR y (fIdx i) = y i :=
  flatR_apply y i.1 i.2

theorem flatM_apply {I : Inst} (Q : Matrix (Idx I) (Idx I) ℤ) (c : Fin I.t) (j : Fin (I.k - 1))
    (b : ℕ) : flatM Q (c * (I.k - 1) + j) b = flatR (Q (c, j)) b :=
  flat_apply (fun (c : Fin I.t) (j : Fin (I.k - 1)) => flatR (Q (c, j)) b) c j

theorem flat_of_ge {t k : ℕ} (X : Fin t → Fin k → ℤ) {a : ℕ} (h : t * k ≤ a) : flat X a = 0 := by
  unfold flat; exact dite_eq_right_iff.mpr fun h' => absurd h' (by omega)

/-- Every flat index below `t k` decomposes as `c k + j`. -/
theorem flat_decomp {t k a : ℕ} (h : a < t * k) :
    ∃ (c : Fin t) (j : Fin k), a = c * k + j := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun hk => by simp [hk] at h
  exact ⟨⟨a / k, div_lt_of_lt_tk h⟩, ⟨a % k, Nat.mod_lt _ hk⟩, (Nat.div_add_mod' a k).symm⟩

theorem fIdx_lt {I : Inst} (i : Idx I) : fIdx i < I.t * (I.k - 1) := by
  have := i.1.2; have := i.2.2
  unfold fIdx; nlinarith

theorem fIdx_inj {I : Inst} {i i' : Idx I} (h : fIdx i = fIdx i') : i = i' := by
  obtain ⟨⟨c, hc⟩, ⟨j, hj⟩⟩ := i
  obtain ⟨⟨c', hc'⟩, ⟨j', hj'⟩⟩ := i'
  simp only [fIdx] at h
  have hk : 0 < I.k - 1 := by omega
  have e1 : (c * (I.k - 1) + j) / (I.k - 1) = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (c' * (I.k - 1) + j') / (I.k - 1) = c' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hj', Nat.zero_add]
  have e3 : (c * (I.k - 1) + j) % (I.k - 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have e4 : (c' * (I.k - 1) + j') % (I.k - 1) = j' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj']
  have hcc : c = c' := by rw [← e1, ← e2, h]
  have hjj : j = j' := by rw [← e3, ← e4, h]
  subst hcc hjj
  rfl

theorem fIdx_mk {I : Inst} (c : Fin I.t) (j : Fin (I.k - 1)) : fIdx (c, j) = c * (I.k - 1) + j :=
  rfl

theorem fIdx_surj {I : Inst} {a : ℕ} (ha : a < I.t * (I.k - 1)) : ∃ i : Idx I, fIdx i = a := by
  obtain ⟨c, j, rfl⟩ := flat_decomp ha
  exact ⟨(c, j), rfl⟩

theorem flatM_fIdx {I : Inst} (Q : Matrix (Idx I) (Idx I) ℤ) (i : Idx I) (b : ℕ) :
    flatM Q (fIdx i) b = flatR (Q i) b :=
  flatM_apply Q i.1 i.2 b

theorem flat_idx_lt {t k c j : ℕ} (hc : c < t) (hj : j < k) : c * k + j < t * k := by
  have : (c + 1) * k ≤ t * k := Nat.mul_le_mul_right _ hc
  rw [Nat.add_mul] at this; omega

theorem nDim_eq (t k : ℕ) : nDim t k = t * (k - 1) := by unfold nDim; ring

/-! ### Sums and products over flat indices -/

theorem flatR_mul {I : Inst} (y z : Idx I → ℤ) (a : ℕ) :
    flatR (fun i => y i * z i) a = flatR y a * flatR z a := by
  unfold flatR flat
  split_ifs <;> simp

theorem sum_flatR {I : Inst} (y : Idx I → ℤ) :
    ∑ a ∈ Finset.range (I.t * (I.k - 1)), flatR y a = ∑ i, y i := by
  rw [flatR, sum_range_flat, ← Fintype.sum_prod_type']

/-- `Qs · g` on flat indices. -/
theorem mulVec_flatM {I : Inst} (Q : Matrix (Idx I) (Idx I) ℤ) (g : Idx I → ℤ) (a : ℕ) :
    Arith.mulVec (flatM Q) (flatR g) (I.t * (I.k - 1)) a = flatR (Matrix.mulVec Q g) a := by
  by_cases ha : a < I.t * (I.k - 1)
  · obtain ⟨c, j, rfl⟩ := flat_decomp ha
    rw [flatR_apply, Arith.mulVec]
    simp only [flatM_apply]
    rw [show (∑ b ∈ Finset.range (I.t * (I.k - 1)), flatR (Q (c, j)) b * flatR g b) =
      ∑ b ∈ Finset.range (I.t * (I.k - 1)), flatR (fun i => Q (c, j) i * g i) b from
        Finset.sum_congr rfl fun b _ => (flatR_mul _ _ b).symm, sum_flatR]
    rfl
  · have h1 : flatR (Matrix.mulVec Q g) a = 0 := flat_of_ge _ (by omega)
    rw [h1, Arith.mulVec]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : flatM Q a b = 0 := flat_of_ge _ (by omega)
    rw [this, zero_mul]

/-- `g · u` on flat indices. -/
theorem dot_flatR {I : Inst} (u g : Idx I → ℤ) :
    ∑ a ∈ Finset.range (I.t * (I.k - 1)), flatR u a * flatR g a = g ⬝ᵥ u := by
  rw [show (∑ a ∈ Finset.range (I.t * (I.k - 1)), flatR u a * flatR g a) =
    ∑ a ∈ Finset.range (I.t * (I.k - 1)), flatR (fun i => u i * g i) a from
      Finset.sum_congr rfl fun b _ => (flatR_mul _ _ b).symm, sum_flatR]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The block sum of cycle `c` as a sum over the flat indices. -/
def bsum {I : Inst} (As : Idx I → ℤ) (c : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (I.k - 1), flatR As (c * (I.k - 1) + j)

theorem bsum_eq {I : Inst} (As : Idx I → ℤ) (c : Fin I.t) : bsum As c = blockSum I As c := by
  unfold bsum blockSum
  rw [← Fin.sum_univ_eq_sum_range (fun j => flatR As (c * (I.k - 1) + j))]
  exact Finset.sum_congr rfl fun j _ => flatR_apply As c j

/-! ### The searches of E1 over `List.range` -/

theorem range_mul_flatMap (t m : ℕ) :
    (List.range t).flatMap (fun c => (List.range m).map (fun j => c * m + j)) =
      List.range (t * m) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add]
    simp

theorem map_val_finRange (t : ℕ) : (List.finRange t).map Fin.val = List.range t := by
  simp

theorem idxList_map_fIdx (I : Inst) :
    (idxList I).map fIdx = List.range (I.t * (I.k - 1)) := by
  rw [← range_mul_flatMap, idxList, List.map_flatMap, ← map_val_finRange I.t, List.flatMap_map]
  congr 1
  funext c
  rw [List.map_map, ← map_val_finRange (I.k - 1), List.map_map]
  rfl

/-- The first negative entry of the flat center (an index below `n`). -/
def negFind {I : Inst} (As : Idx I → ℤ) : Option ℕ :=
  (List.range (I.t * (I.k - 1))).find? fun a => decide (flatR As a < 0)

/-- The first cycle whose block sum exceeds `2^p`. -/
def overFind {I : Inst} (p : ℕ) (As : Idx I → ℤ) : Option ℕ :=
  (List.range I.t).find? fun c => decide ((2 : ℤ) ^ p < bsum As c)

theorem negFind_eq {I : Inst} (As : Idx I → ℤ) : negFind As = (firstNeg I As).map fIdx := by
  unfold negFind firstNeg
  rw [← idxList_map_fIdx, List.find?_map]
  congr 2
  funext i
  simp only [Function.comp, flatR_fIdx]

theorem overFind_eq {I : Inst} (p : ℕ) (As : Idx I → ℤ) :
    overFind p As = (firstOver I p As).map Fin.val := by
  unfold overFind firstOver
  rw [← map_val_finRange, List.find?_map]
  congr 2
  funext c
  simp only [Function.comp, bsum_eq]

/-- `none ↦ 0`, `some a ↦ a + 1`. -/
def enc : Option ℕ → ℕ
  | none => 0
  | some a => a + 1

/-- One more step of a search over `List.range`. -/
theorem find_range_succ (q : ℕ → Bool) (a : ℕ) :
    enc ((List.range (a + 1)).find? q) =
      if enc ((List.range a).find? q) = 0 then (if q a then a + 1 else 0)
      else enc ((List.range a).find? q) := by
  rw [List.range_succ, List.find?_append]
  rcases h : (List.range a).find? q with _ | b
  · simp only [enc, Option.none_or, ↓reduceIte]
    by_cases hq : q a <;> simp [List.find?, hq]
  · simp [enc]

theorem find_range_zero (q : ℕ → Bool) : enc ((List.range 0).find? q) = 0 := by
  simp [enc]

/-! ### The memory layout and the global registers of Phase E -/

/-- The addresses of Phase E: `H`, then (from the initial `rFREE`) `As`, `Qs`, `Xs`, `L`, `g`, `u`,
and the final `rFREE`. -/
structure Lay where
  /-- `H`. -/
  bh : ℕ
  /-- `As` (`n` entries). -/
  pA : ℕ
  /-- `Qs` (`n × n`). -/
  pQ : ℕ
  /-- `Xs` (`t k` entries). -/
  pX : ℕ
  /-- `L` (`t k` entries). -/
  pL : ℕ
  /-- `g` (`n` entries). -/
  pG : ℕ
  /-- `u` (`n` entries). -/
  pU : ℕ
  /-- The free memory. -/
  F : ℕ

/-- The layout of `I`: the blocks are contiguous, after `H` (and `k ≥ 3`, `t ≥ 1`). -/
structure Lay.Ok (I : Inst) (Ly : Lay) : Prop where
  k3 : 3 ≤ I.k
  t0 : 0 < I.t
  h : Ly.bh + hCells I ≤ Ly.pA
  q : Ly.pQ = Ly.pA + nDim I.t I.k * 2
  x : Ly.pX = Ly.pQ + nDim I.t I.k * (2 * nDim I.t I.k)
  l : Ly.pL = Ly.pX + I.t * I.k * 2
  g : Ly.pG = Ly.pL + I.t * I.k * 2
  u : Ly.pU = Ly.pG + nDim I.t I.k * 2
  f : Ly.F = Ly.pU + nDim I.t I.k * 2

/-- The registers that stay fixed during the iterations of Phase E. -/
@[mk_iff] structure EG (I : Inst) (Ly : Lay) (c : Config) : Prop where
  q : QRegs I c
  bh : c.reg qBH = Ly.bh
  x : c.reg qBX = Ly.pX
  free : c.reg rFREE = Ly.F
  a : c.reg eA = Ly.pA
  qs : c.reg eQ = Ly.pQ
  l : c.reg eL = Ly.pL
  g : c.reg eG = Ly.pG
  u : c.reg eU = Ly.pU
  n2 : c.reg e2N = 2 * nDim I.t I.k
  k1 : c.reg eK1 = I.k - 1
  p0 : c.reg eP2 = 0
  p1 : c.reg (eP2 + 1) = 2 ^ prec I.t I.k

/-- **The layout fits below `S`** (`Ly.F ≤ S`): one inequality per region, for address proofs. -/
theorem Lay.Ok.fits {I : Inst} {Ly : Lay} (hL : Ly.Ok I) {S : ℕ} (hS : Ly.F ≤ S) :
    Ly.bh + hCells I ≤ S ∧ Ly.pA + nDim I.t I.k * 2 ≤ S ∧
      Ly.pQ + nDim I.t I.k * (2 * nDim I.t I.k) ≤ S ∧ Ly.pX + I.t * I.k * 2 ≤ S ∧
      Ly.pL + I.t * I.k * 2 ≤ S ∧ Ly.pG + nDim I.t I.k * 2 ≤ S ∧
      Ly.pU + nDim I.t I.k * 2 ≤ S := by
  have := hL.h; have := hL.q; have := hL.x; have := hL.l; have := hL.g; have := hL.u
  have := hL.f
  omega

theorem EG.regIndep (I : Inst) (Ly : Lay) : RegIndep ellW (EG I Ly) := by
  indep [eG_iff, QRegs]

theorem EG.indep {I : Inst} {Ly : Lay} {W : List ℕ} (hW : ∀ r ∈ W, r ∈ ellW) :
    Indep W (EG I Ly) :=
  ((EG.regIndep I Ly).mono hW).indep

theorem EG.p2 {I : Inst} {Ly : Lay} {c : Config} (h : EG I Ly c) :
    SReg c eP2 ((2 : ℤ) ^ prec I.t I.k) := by
  refine ⟨?_, ?_⟩
  · rw [h.p0]; unfold sgnBit
    have : ¬ ((2 : ℤ) ^ prec I.t I.k < 0) := not_lt.mpr (by positivity)
    simp [this]
  · rw [h.p1]; simp

theorem EG.t {I : Inst} {Ly : Lay} {c : Config} (h : EG I Ly c) : c.reg qT = I.t := h.q.1
theorem EG.k {I : Inst} {Ly : Lay} {c : Config} (h : EG I Ly c) : c.reg qK = I.k := h.q.2.1
theorem EG.kt {I : Inst} {Ly : Lay} {c : Config} (h : EG I Ly c) : c.reg qKT = I.t * I.k :=
  h.q.2.2.1
theorem EG.n {I : Inst} {Ly : Lay} {c : Config} (h : EG I Ly c) : c.reg qN = nDim I.t I.k :=
  h.q.2.2.2.1
theorem EG.it {I : Inst} {Ly : Lay} {c : Config} (h : EG I Ly c) :
    c.reg qIt = iters I.t I.k := h.q.2.2.2.2.2.2.1
theorem EG.p {I : Inst} {Ly : Lay} {c : Config} (h : EG I Ly c) : c.reg qP = prec I.t I.k :=
  h.q.2.2.2.2.2.2.2.1
theorem EG.e {I : Inst} {Ly : Lay} {c : Config} (h : EG I Ly c) : c.reg qE = bigE I.t I.k :=
  h.q.2.2.2.2.2.2.2.2.1
theorem EG.cn {I : Inst} {Ly : Lay} {c : Config} (h : EG I Ly c) : c.reg qCN = cNum I.t I.k :=
  h.q.2.2.2.2.2.2.2.2.2.1
theorem EG.cd {I : Inst} {Ly : Lay} {c : Config} (h : EG I Ly c) : c.reg qCD = cDen I.t I.k :=
  h.q.2.2.2.2.2.2.2.2.2.2

/-! ### Signed arrays in memory: transport -/

/-- `Qs` in memory: row `a < n` (`n` contiguous signed entries) at `pQ + a · 2n`. -/
def QsMem (m : ℕ → ℕ) (pQ n : ℕ) (M : ℕ → ℕ → ℤ) : Prop :=
  ∀ a < n, SArr m (pQ + a * (2 * n)) 2 n (M a)

/-- The state `st` of the ellipsoid method in memory. -/
structure StMem (I : Inst) (Ly : Lay) (st : EllState I) (m : ℕ → ℕ) : Prop where
  a : SArr m Ly.pA 2 (nDim I.t I.k) (flatR st.As)
  q : QsMem m Ly.pQ (nDim I.t I.k) (flatM st.Qs)

theorem cell_le {j n s : ℕ} (hj : j < n) (hs : 2 ≤ s) : j * s + 2 ≤ n * s := by
  have : (j + 1) * s ≤ n * s := Nat.mul_le_mul_right s hj
  rw [Nat.add_mul] at this; omega

/-- A signed array survives a change of the memory outside `[lo, hi)` when it lies outside. -/
theorem SArr.out {m m' : ℕ → ℕ} {b s n lo hi : ℕ} {f : ℕ → ℤ} (h : SArr m b s n f) (hs : 2 ≤ s)
    (hm : ∀ x, (x < lo ∨ hi ≤ x) → m' x = m x) (hd : b + n * s ≤ lo ∨ hi ≤ b) :
    SArr m' b s n f := fun j hj => by
  have := cell_le hj hs
  obtain ⟨h0, h1⟩ := h j hj
  exact ⟨(hm _ (by omega)).trans h0, (hm _ (by omega)).trans h1⟩

theorem row_le {a n : ℕ} (ha : a < n) : a * (2 * n) + n * 2 ≤ n * (2 * n) := by
  have := cell_le (s := 2 * n) ha (by omega)
  have : (a + 1) * (2 * n) ≤ n * (2 * n) := Nat.mul_le_mul_right _ ha
  rw [Nat.add_mul] at this; omega

theorem QsMem.out {m m' : ℕ → ℕ} {pQ n lo hi : ℕ} {M : ℕ → ℕ → ℤ} (h : QsMem m pQ n M)
    (hm : ∀ x, (x < lo ∨ hi ≤ x) → m' x = m x) (hd : pQ + n * (2 * n) ≤ lo ∨ hi ≤ pQ) :
    QsMem m' pQ n M := fun a ha =>
  SArr.out (h a ha) (le_refl 2) hm (by have := row_le ha; omega)

theorem hrow_le {I : Inst} {a : ℕ} (ha : a < I.t * I.k) :
    a * (2 * (I.t * I.k)) + I.t * I.k * 2 ≤ hCells I := by
  unfold hCells; exact row_le ha

theorem HMem.out {I : Inst} {m m' : ℕ → ℕ} {b lo hi : ℕ} (h : HMem I m b)
    (hm : ∀ x, (x < lo ∨ hi ≤ x) → m' x = m x) (hd : b + hCells I ≤ lo ∨ hi ≤ b) :
    HMem I m' b := fun a ha =>
  SArr.out (h a ha) (le_refl 2) hm (by have := hrow_le ha; omega)

theorem StMem.out {I : Inst} {Ly : Lay} {st : EllState I} {m m' : ℕ → ℕ} {lo hi : ℕ}
    (h : StMem I Ly st m) (hL : Ly.Ok I) (hm : ∀ x, (x < lo ∨ hi ≤ x) → m' x = m x)
    (hd : Ly.pX ≤ lo ∨ hi ≤ Ly.pA) : StMem I Ly st m' :=
  ⟨SArr.out h.a (le_refl 2) hm (by have := hL.q; have := hL.x; omega),
    QsMem.out h.q hm (by have := hL.q; have := hL.x; omega)⟩

/-- Reading entry `j` of a signed array. -/
theorem SArr.get {m : ℕ → ℕ} {b s n : ℕ} {f : ℕ → ℤ} (h : SArr m b s n f) {j : ℕ} (hj : j < n) :
    SMem m (b + j * s) (f j) := h j hj

theorem SArr.congr_fun {m : ℕ → ℕ} {b s n : ℕ} {f g : ℕ → ℤ} (h : SArr m b s n f)
    (hfg : ∀ j < n, f j = g j) : SArr m b s n g := fun j hj => by rw [← hfg j hj]; exact h j hj

/-! ### Bit lengths -/

theorem size_le_of_abs_le {z : ℤ} {e : ℕ} (h : |z| ≤ 2 ^ e) : Nat.size z.natAbs ≤ e + 1 := by
  rw [Nat.size_le]
  have h1 : (z.natAbs : ℤ) ≤ 2 ^ e := by rw [Int.natCast_natAbs]; exact h
  have h2 : z.natAbs ≤ 2 ^ e := by exact_mod_cast h1
  have : 2 ^ e < 2 ^ (e + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem size_le_of_le_pow {x e : ℕ} (h : x ≤ 2 ^ e) : Nat.size x ≤ e + 1 := by
  rw [Nat.size_le]
  have : 2 ^ e < 2 ^ (e + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem size_mono {x y : ℕ} (h : x ≤ y) : Nat.size x ≤ Nat.size y := Nat.size_le_size h

theorem smulCost_le {v : ℤ} {B : ℕ} (h : Nat.size v.natAbs ≤ B) : smulCost v ≤ 31 * B + 35 := by
  unfold smulCost gCost; omega

end STACS2027.Runtimes.QPRam
