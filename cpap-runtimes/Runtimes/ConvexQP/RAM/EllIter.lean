module

public import Runtimes.ConvexQP.RAM.EllScan
public import Runtimes.ConvexQP.RAM.EllGap
public import Runtimes.ConvexQP.RAM.EllGrad
public import Runtimes.ConvexQP.RAM.EllCost
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: one iteration

`iterB = dec eCnt; scan; feasOpt; if eDn = 0 then (gLoop; upd) else eCnt := 0`, where `feasOpt`
runs E2 (`feas`) only at a feasible center. Against the state `st = ellIter i` in memory,
`iter_specB` (below every `S ≥ F + ellSc`) establishes the state of iteration `i + 1` (`MSt`): the
updated state with `eCnt = N − (i+1)`, or the successful output `Xs` at `qBX` with `eCnt = 0`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

/-! ### E2 -/

/-- **E2**: `Xs`, `L`, the gap and the test. -/
def feas : Stmt := .seq feasXs (.seq mvL (.seq gapB testB))

/-- The cost of E2. -/
def feasC (I : Inst) : ℕ :=
  I.t * ((I.k - 1) * 58 + 61) + 7 +
  (I.t * I.k * (I.t * I.k * (31 * (prec I.t I.k + 1) + 87) + 19) + 17 +
  (I.t * (I.k * (31 * (prec I.t I.k + 1) + 130) + 49) + 31 * prec I.t I.k + 147 +
  (93 * (prec I.t I.k + 1) + 8 * prec I.t I.k + 165)))

/-- The memory after E2. -/
def feasMem (I : Inst) (Ly : Lay) (As : Idx I → ℤ) (m : ℕ → ℕ) : ℕ → ℕ :=
  wrArr (wrArr m Ly.pX 2 (flat (feasPt I (prec I.t I.k) As)) (I.t * I.k)) Ly.pL 2
    (Arith.mulVec (Hflat I) (flat (feasPt I (prec I.t I.k) As)) (I.t * I.k)) (I.t * I.k)

theorem feas_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (hI : I.Valid) (As : Idx I → ℤ)
    (m : ℕ → ℕ) (hA : SArr m Ly.pA 2 (nDim I.t I.k) (flatR As)) (hH : HMem I m Ly.bh)
    (hz : ZeroFrom m Ly.F) (hneg : ∀ i, 0 ≤ As i)
    (hblk : ∀ c, blockSum I As c ≤ 2 ^ prec I.t I.k) (hS : Ly.F + ellSc I.t I.k ≤ S) :
    HTB S feas (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => EG I Ly cfg ∧ cfg.mem = feasMem I Ly As m ∧
        cfg.reg eDn = if I.gap (feasPt I (prec I.t I.k) As) * (bigE I.t I.k : ℤ) ^ 2 ≤
          4 ^ prec I.t I.k then 1 else 0)
      (feasC I) := by
  have hLh := hL.h; have hLq := hL.q; have hLx := hL.x; have hLl := hL.l; have hLg := hL.g
  have hLu := hL.u; have hLf := hL.f
  have hk : 0 < I.k := by have := hL.k3; omega
  have hSp : Ly.F + 128 * prec I.t I.k + 134 ≤ S := by unfold ellSc bitB at hS; omega
  set Xs := feasPt I (prec I.t I.k) As with hXs
  have hXb := xs_bits hI hneg hblk
  have h1 := feasXs_specB (S := S) I Ly hL As m hA (by omega)
  set m1 := wrArr m Ly.pX 2 (flat Xs) (I.t * I.k) with hm1
  have hm1o : ∀ x, (x < Ly.pX ∨ Ly.pX + I.t * I.k * 2 ≤ x) → m1 x = m x :=
    fun x hx => wrArr_of_out (le_refl 2) hx
  have hX1 : SArr m1 Ly.pX 2 (I.t * I.k) (flat Xs) := sarr_wrArr (le_refl 2) _
  have hH1 : HMem I m1 Ly.bh := HMem.out hH hm1o (by omega)
  have hz1 : ZeroFrom m1 Ly.F := zeroFrom_wrArr (le_refl 2) hz (by omega)
  have h2 := mvL_specB (S := S) I Ly hL Xs m1 hH1 hX1 hz1 (prec I.t I.k + 1) (fun j _ => hXb j)
    (by omega)
  set m2 := wrArr m1 Ly.pL 2 (Arith.mulVec (Hflat I) (flat Xs) (I.t * I.k)) (I.t * I.k)
    with hm2
  have hm2o : ∀ x, (x < Ly.pL ∨ Ly.pL + I.t * I.k * 2 ≤ x) → m2 x = m1 x :=
    fun x hx => wrArr_of_out (le_refl 2) hx
  have hX2 : SArr m2 Ly.pX 2 (I.t * I.k) (flat Xs) := SArr.out hX1 (le_refl 2) hm2o (by omega)
  have hL2 : SArr m2 Ly.pL 2 (I.t * I.k) (flat (I.L Xs)) :=
    SArr.congr_fun (sarr_wrArr (le_refl 2) _) fun b hb => mulVec_Hflat_flat I Xs hb
  have hz2 : ZeroFrom m2 Ly.F := zeroFrom_wrArr (le_refl 2) hz1 (by omega)
  have h3 := gapB_specB (S := S) I Ly m2 (flat Xs) (flat (I.L Xs)) hX2 hL2 hz2 (prec I.t I.k + 1)
    (fun j _ => hXb j) hk hL (by omega)
  have hgap : gapN (flat Xs) (flat (I.L Xs)) I.t I.k (prec I.t I.k) = I.gap Xs :=
    gapN_eq I Xs (prec I.t I.k) hk fun c => Inst.sum_xiq _ _ c hk
  have h4 := testB_specB (S := S) I Ly m2 hz2 (gapN (flat Xs) (flat (I.L Xs)) I.t I.k (prec I.t
      I.k))
    (prec I.t I.k + 1) (bigE_bits hL.t0 hL.k3) (by omega)
  refine (h1.seq (h2.seq (h3.seq (h4.pre fun cfg h => h)))).post fun cfg ⟨hE, hm, hd⟩ =>
    ⟨hE, hm, by rw [hd, hgap]⟩

/-! ### The iteration -/

/-- Run E2 only at a feasible center (`eF1 = eF2 = 0`); otherwise `eDn := 0`. -/
def feasOpt : Stmt := .ifz eF1 (.ifz eF2 feas (.const eDn 0)) (.const eDn 0)

/-- The part of an iteration after the scan. -/
def tailB : Stmt := .seq feasOpt (.ifz eDn (.seq gLoop upd) (.const eCnt 0))

/-- **One iteration** of Phase E. -/
def iterB : Stmt := .seq (dec eCnt) (.seq scan tailB)

theorem feasOpt_wregs : ∀ r ∈ wregs feasOpt, r ∈ ellW := by decide +kernel

theorem iterB_wregs : ∀ r ∈ wregs iterB, r = eCnt ∨ r ∈ ellW := by decide +kernel

/-- The state of the machine after `j` iterations. -/
def MSt (I : Inst) (Ly : Lay) (j : ℕ) (c : Config) : Prop :=
  match ellIter I (consts I.t I.k) j with
  | .inl st => c.reg eCnt = iters I.t I.k - j ∧ StMem I Ly st c.mem
  | .inr Xs => c.reg eCnt = 0 ∧ SArr c.mem Ly.pX 2 (I.t * I.k) (flat Xs)

/-! ### The cuts of E1 and E3 on flat indices -/

theorem negFind_some {I : Inst} {As : Idx I → ℤ} {a : ℕ} (h : negFind As = some a) :
    ∃ i, firstNeg I As = some i ∧ fIdx i = a := by
  rw [negFind_eq, Option.map_eq_some_iff] at h
  exact h

theorem negFind_none {I : Inst} {As : Idx I → ℤ} (h : negFind As = none) :
    firstNeg I As = none := by
  rw [negFind_eq, Option.map_eq_none_iff] at h
  exact h

theorem overFind_some {I : Inst} {p : ℕ} {As : Idx I → ℤ} {c : ℕ} (h : overFind p As = some c) :
    ∃ c' : Fin I.t, firstOver I p As = some c' ∧ (c' : ℕ) = c := by
  rw [overFind_eq, Option.map_eq_some_iff] at h
  exact h

theorem overFind_none {I : Inst} {p : ℕ} {As : Idx I → ℤ} (h : overFind p As = none) :
    firstOver I p As = none := by
  rw [overFind_eq, Option.map_eq_none_iff] at h
  exact h

theorem gMode_neg {I : Inst} (i : Idx I) (f2 : ℕ) (Lf : ℕ → ℤ) {c j : ℕ} (hc : c < I.t)
    (hj : j < I.k - 1) :
    flatR (negCut I i) (c * (I.k - 1) + j) = gMode (fIdx i + 1) f2 Lf I.k c j := by
  have e := flatR_apply (negCut I i) ⟨c, hc⟩ ⟨j, hj⟩
  simp only at e
  have hne : fIdx i + 1 ≠ 0 := by omega
  simp only [gMode, ne_eq, hne, not_false_eq_true, ↓reduceIte] at e ⊢
  rw [e, negCut]
  by_cases h : ((⟨c, hc⟩, ⟨j, hj⟩) : Idx I) = i
  · subst h; simp [fIdx]
  · have : ¬ c * (I.k - 1) + j = fIdx i := fun h' => h (fIdx_inj (by
      rw [fIdx_mk]; simp only; omega))
    simp [h, this]

theorem gMode_block {I : Inst} (c0 : Fin I.t) (Lf : ℕ → ℤ) {c j : ℕ} (hc : c < I.t)
    (hj : j < I.k - 1) :
    flatR (blockCut I c0) (c * (I.k - 1) + j) = gMode 0 (c0 + 1) Lf I.k c j := by
  have e := flatR_apply (blockCut I c0) ⟨c, hc⟩ ⟨j, hj⟩
  simp only at e
  rw [e, gMode, blockCut]
  by_cases h : c = c0
  · subst h; simp
  · have h' : (⟨c, hc⟩ : Fin I.t) ≠ c0 := fun h'' => h (by rw [← h''])
    simp [h, h']

theorem gMode_grad {I : Inst} (Xs : Fin I.t → Fin I.k → ℤ) {c j : ℕ} (hc : c < I.t)
    (hj : j < I.k - 1) :
    flatR (gradCut I Xs) (c * (I.k - 1) + j) = gMode 0 0 (flat (I.L Xs)) I.k c j := by
  have hk : 0 < I.k := by omega
  have e := flatR_apply (gradCut I Xs) ⟨c, hc⟩ ⟨j, hj⟩
  simp only at e
  have e1 := flat_apply (I.L Xs) ⟨c, hc⟩ ⟨j, by omega⟩
  have e2 := flat_apply (I.L Xs) ⟨c, hc⟩ ⟨I.k - 1, by omega⟩
  simp only at e1 e2
  rw [e, gMode]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, e1, e2, gradCut, Inst.gradRed, Inst.lastL, hk,
    ↓reduceDIte]
  rfl

/-! ### Cut and update -/

/-- The cost of the scan. -/
def scanC (I : Inst) : ℕ := I.t * ((I.k - 1) * 56 + 38) + 10

/-- The cost of the cut vector. -/
def gC (I : Inst) : ℕ := I.t * ((I.k - 1) * 66 + 11) + 8

/-- The cost of one iteration. -/
def iterCost (I : Inst) : ℕ :=
  2 + (scanC I + (feasC I + 2 + (gC I + updCost (nDim I.t I.k) (bitB I.t I.k) + 1)))

theorem HT.of_false {s : Stmt} {P Q : Config → Prop} {b : ℕ} (h : ∀ c, P c → False) :
    HT s P Q b := fun c hc => absurd hc (h c)

/-- **E1/E3 and E4**: write the cut `g` (given by the mode `f1, f2`), then update the state. -/
theorem cutUpd_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (hI : I.Valid) {i : ℕ}
    (hi : i < iters I.t I.k) {st : EllState I} (hst : ellIter I (consts I.t I.k) i = .inl st)
    {g : Idx I → ℤ} (hcut : ellCut I (consts I.t I.k) st.As = .inl g) (f1 f2 : ℕ) (Lf : ℕ → ℤ)
    (m : ℕ → ℕ) (hSt : StMem I Ly st m) (hH : HMem I m Ly.bh) (hz : ZeroFrom m Ly.F)
    (hLf : f1 = 0 → f2 = 0 → SArr m Ly.pL 2 (I.t * I.k) Lf)
    (hgm : ∀ c < I.t, ∀ j < I.k - 1, flatR g (c * (I.k - 1) + j) = gMode f1 f2 Lf I.k c j)
    (hS : Ly.F + ellSc I.t I.k ≤ S) :
    HTB S (.seq gLoop upd)
      (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg eF1 = f1 ∧ cfg.reg eF2 = f2)
      (fun cfg => EG I Ly cfg ∧ StMem I Ly (ellUpdate I (consts I.t I.k) st g) cfg.mem ∧
        HMem I cfg.mem Ly.bh ∧ ZeroFrom cfg.mem Ly.F)
      (gC I + updCost (nDim I.t I.k) (bitB I.t I.k)) := by
  have hLh := hL.h; have hLq := hL.q; have hLx := hL.x; have hLl := hL.l; have hLg := hL.g
  have hLu := hL.u; have hLF := hL.f
  have h1 := gLoop_specB (S := S) I Ly hL m (flatR g) Lf f1 f2 hLf hgm (by omega)
  set m1 := wrArr m Ly.pG 2 (flatR g) (I.t * (I.k - 1)) with hm1
  have hn : nDim I.t I.k = I.t * (I.k - 1) := nDim_eq _ _
  have hm1o : ∀ x, (x < Ly.pG ∨ Ly.pG + nDim I.t I.k * 2 ≤ x) → m1 x = m x :=
    fun x hx => wrArr_of_out (le_refl 2) (by rw [← hn]; exact hx)
  have hSt1 : StMem I Ly st m1 := hSt.out hL hm1o (by omega)
  have hg1 : SArr m1 Ly.pG 2 (nDim I.t I.k) (flatR g) := by rw [hn]; exact sarr_wrArr (le_refl 2) _
  have hH1 : HMem I m1 Ly.bh := HMem.out hH hm1o (by omega)
  have hz1 : ZeroFrom m1 Ly.F := zeroFrom_wrArr (le_refl 2) hz (by rw [← hn]; omega)
  obtain ⟨-, hG, -⟩ := update_bounds hI hL.t0 hi hst hcut
  have h2 := upd_specB (S := S) I Ly hL st g m1 hSt1 hg1 hH1 hz1 hG (bitB I.t I.k)
    (updBits_of hI hL.t0 hi hst hcut) (by unfold ellSc at hS; omega)
  exact h1.seq (h2.pre fun cfg ⟨hE, hm, _⟩ => ⟨hE, hm⟩)

/-! ### Frames -/

theorem regIndep_cnt {s : Stmt} (hs : ∀ r ∈ wregs s, r ∈ ellW) (v : ℕ) :
    RegIndep (wregs s) (fun c => c.reg eCnt = v) :=
  RegIndep.reg (r := eCnt) (fun h => by have := hs _ h; revert this; decide) (· = v)

theorem feas_wregs : ∀ r ∈ wregs feas, r ≠ eF1 ∧ r ≠ eF2 ∧ r ∈ ellW := by decide +kernel

theorem gu_wregs : ∀ r ∈ wregs (.seq gLoop upd), r ∈ ellW := by
  intro r hr
  simp only [wregs_seq, List.mem_append] at hr
  rcases hr with h | h
  · exact gLoop_wregs r h
  · exact upd_wregs r h

/-- The state after iteration `i`. -/
def IterPost (I : Inst) (Ly : Lay) (i : ℕ) (cfg : Config) : Prop :=
  EG I Ly cfg ∧ HMem I cfg.mem Ly.bh ∧ ZeroFrom cfg.mem Ly.F ∧ MSt I Ly (i + 1) cfg

/-! ### The tail of an iteration -/

/-- `eDn := 0`. -/
theorem constDn_specB {P : Config → Prop} (hP : Indep [eDn] P) :
    HTB S (.const eDn 0) P (fun c => P c ∧ c.reg eDn = 0) 1 :=
  HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => ⟨hP.setReg (by simp) _ hc, by simp⟩

/-- The tail at a cut of E1 (`eF1 ≠ 0` or `eF2 ≠ 0`). -/
theorem tail_cutB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (hI : I.Valid) {i : ℕ}
    (hi : i < iters I.t I.k) {st : EllState I} (hst : ellIter I (consts I.t I.k) i = .inl st)
    {g : Idx I → ℤ} (hcut : ellCut I (consts I.t I.k) st.As = .inl g) (f1 f2 : ℕ)
    (hf : f1 ≠ 0 ∨ f2 ≠ 0) (m : ℕ → ℕ) (hSt : StMem I Ly st m) (hH : HMem I m Ly.bh)
    (hz : ZeroFrom m Ly.F)
    (hgm : ∀ c < I.t, ∀ j < I.k - 1, flatR g (c * (I.k - 1) + j) =
      gMode f1 f2 (fun _ => 0) I.k c j) (hS : Ly.F + ellSc I.t I.k ≤ S) :
    HTB S tailB (fun cfg => (EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg eF1 = f1 ∧ cfg.reg eF2 = f2) ∧
        cfg.reg eCnt = iters I.t I.k - (i + 1))
      (IterPost I Ly i) (feasC I + 2 + (gC I + updCost (nDim I.t I.k) (bitB I.t I.k) + 1)) := by
  set P : Config → Prop := fun cfg => (EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg eF1 = f1 ∧
    cfg.reg eF2 = f2) ∧ cfg.reg eCnt = iters I.t I.k - (i + 1) with hP
  have hPi : Indep [eDn] P := by indep [hP, eG_iff, QRegs]
  have h1 : HTB S feasOpt P (fun cfg => P cfg ∧ cfg.reg eDn = 0) (feasC I + 2) := by
    have hb : 1 ≤ feasC I := by unfold feasC; omega
    refine HTB.ifz (HTB.ifz (HTB.of_false fun c h => ?_) ?_) ?_
    · obtain ⟨⟨⟨⟨_, _, h1, h2⟩, _⟩, h1'⟩, h2'⟩ := h
      rw [h1] at h1'; rw [h2] at h2'
      rcases hf with h | h <;> contradiction
    · exact ((constDn_specB hPi).pre fun c h => h.1.1).weaken hb
    · exact ((constDn_specB hPi).pre fun c h => h.1).weaken (by omega)
  have h2 := (cutUpd_specB I Ly hL hI hi hst hcut f1 f2 (fun _ => 0) m hSt hH hz
    (fun h1 h2 => absurd hf (by simp [h1, h2])) hgm hS).frameReg
    (regIndep_cnt gu_wregs (iters I.t I.k - (i + 1)))
  have hnext : ellIter I (consts I.t I.k) (i + 1) = .inl (ellUpdate I (consts I.t I.k) st g) := by
    rw [ellIter_succ_inl hst, ellStep, hcut]
  have h3 : HTB S (.seq gLoop upd) (fun c => (P c ∧ c.reg eDn = 0) ∧ c.reg eDn = 0)
      (IterPost I Ly i) (gC I + updCost (nDim I.t I.k) (bitB I.t I.k)) := by
    refine (h2.pre fun c h => ⟨⟨h.1.1.1.1, h.1.1.1.2⟩, h.1.1.2⟩).post fun c h => ?_
    obtain ⟨⟨hE, hS, hH', hz'⟩, hc⟩ := h
    refine ⟨hE, hH', hz', ?_⟩
    unfold MSt
    rw [hnext]
    exact ⟨hc, hS⟩
  have h4 : HTB S (.const eCnt 0) (fun c => (P c ∧ c.reg eDn = 0) ∧ c.reg eDn ≠ 0)
      (IterPost I Ly i) (gC I + updCost (nDim I.t I.k) (bitB I.t I.k)) :=
    HTB.of_false fun c h => h.2 h.1.2
  exact h1.seq (HTB.ifz h3 h4)

theorem feasMem_facts (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (st : EllState I) (m : ℕ → ℕ)
    (hSt : StMem I Ly st m) (hH : HMem I m Ly.bh) (hz : ZeroFrom m Ly.F) :
    StMem I Ly st (feasMem I Ly st.As m) ∧ HMem I (feasMem I Ly st.As m) Ly.bh ∧
      ZeroFrom (feasMem I Ly st.As m) Ly.F ∧
      SArr (feasMem I Ly st.As m) Ly.pX 2 (I.t * I.k) (flat (feasPt I (prec I.t I.k) st.As)) ∧
      SArr (feasMem I Ly st.As m) Ly.pL 2 (I.t * I.k)
        (flat (I.L (feasPt I (prec I.t I.k) st.As))) := by
  have hLh := hL.h; have hLq := hL.q; have hLx := hL.x; have hLl := hL.l; have hLg := hL.g
  have hLu := hL.u; have hLf := hL.f
  set Xs := feasPt I (prec I.t I.k) st.As
  set m1 := wrArr m Ly.pX 2 (flat Xs) (I.t * I.k) with hm1
  have hm1o : ∀ x, (x < Ly.pX ∨ Ly.pX + I.t * I.k * 2 ≤ x) → m1 x = m x :=
    fun x hx => wrArr_of_out (le_refl 2) hx
  have hm2o : ∀ x, (x < Ly.pL ∨ Ly.pL + I.t * I.k * 2 ≤ x) → feasMem I Ly st.As m x = m1 x :=
    fun x hx => wrArr_of_out (le_refl 2) hx
  refine ⟨(hSt.out hL hm1o (by omega)).out hL hm2o (by omega),
    HMem.out (HMem.out hH hm1o (by omega)) hm2o (by omega),
    zeroFrom_wrArr (le_refl 2) (zeroFrom_wrArr (le_refl 2) hz (by omega)) (by omega),
    SArr.out (sarr_wrArr (le_refl 2) _) (le_refl 2) hm2o (by omega),
    SArr.congr_fun (sarr_wrArr (le_refl 2) _) fun b hb => mulVec_Hflat_flat I Xs hb⟩

/-- The tail at a feasible center: E2, then success or the gradient cut and E4. -/
theorem tail_feasB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (hI : I.Valid) {i : ℕ}
    (hi : i < iters I.t I.k) {st : EllState I} (hst : ellIter I (consts I.t I.k) i = .inl st)
    (hneg0 : firstNeg I st.As = none) (hover0 : firstOver I (prec I.t I.k) st.As = none)
    (m : ℕ → ℕ) (hSt : StMem I Ly st m) (hH : HMem I m Ly.bh) (hz : ZeroFrom m Ly.F)
    (hS : Ly.F + ellSc I.t I.k ≤ S) :
    HTB S tailB (fun cfg => (EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg eF1 = 0 ∧ cfg.reg eF2 = 0) ∧
        cfg.reg eCnt = iters I.t I.k - (i + 1))
      (IterPost I Ly i) (feasC I + 2 + (gC I + updCost (nDim I.t I.k) (bitB I.t I.k) + 1)) := by
  set Xs := feasPt I (prec I.t I.k) st.As with hXs
  set v := iters I.t I.k - (i + 1) with hv
  set P : Config → Prop := fun cfg => (EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg eF1 = 0 ∧
    cfg.reg eF2 = 0) ∧ cfg.reg eCnt = v with hP
  set Q : Config → Prop := fun cfg => (EG I Ly cfg ∧ cfg.mem = feasMem I Ly st.As m ∧
    cfg.reg eDn = if I.gap Xs * (bigE I.t I.k : ℤ) ^ 2 ≤ 4 ^ prec I.t I.k then 1 else 0) ∧
    cfg.reg eF1 = 0 ∧ cfg.reg eF2 = 0 ∧ cfg.reg eCnt = v with hQ
  obtain ⟨hSt2, hH2, hz2, hX2, hL2⟩ := feasMem_facts I Ly hL st m hSt hH hz
  have hcut0 : ellCut I (consts I.t I.k) st.As =
      if I.gap Xs * (bigE I.t I.k : ℤ) ^ 2 ≤ 4 ^ prec I.t I.k then .inr Xs
      else .inl (gradCut I Xs) := by
    have hover0' : firstOver I (consts I.t I.k).p st.As = none := hover0
    unfold ellCut; rw [hneg0, hover0']; rfl
  have hF : RegIndep (wregs feas) (fun c => c.reg eF1 = 0 ∧ c.reg eF2 = 0 ∧ c.reg eCnt = v) :=
    (RegIndep.reg (r := eF1) (fun h => (feas_wregs _ h).1 rfl) (· = 0)).and
      ((RegIndep.reg (r := eF2) (fun h => (feas_wregs _ h).2.1 rfl) (· = 0)).and
      (RegIndep.reg (r := eCnt) (fun h => by have := (feas_wregs _ h).2.2; revert this; decide)
        (· = v)))
  have h0 := (feas_specB I Ly hL hI st.As m hSt.a hH hz (firstNeg_none hneg0)
    (firstOver_none hover0) hS).frameReg hF
  have hA : HTB S feas (fun c => (P c ∧ c.reg eF1 = 0) ∧ c.reg eF2 = 0) Q (feasC I) :=
    h0.pre fun c h => ⟨⟨h.1.1.1.1, h.1.1.1.2.1⟩, h.1.1.1.2.2.1, h.1.1.1.2.2.2, h.1.1.2⟩
  have hB : HTB S (.const eDn 0) (fun c => (P c ∧ c.reg eF1 = 0) ∧ c.reg eF2 ≠ 0) Q (feasC I) :=
    HTB.of_false fun c h => h.2 h.1.1.1.2.2.2
  have hin : HTB S (.ifz eF2 feas (.const eDn 0)) (fun c => P c ∧ c.reg eF1 = 0) Q (feasC I + 1) :=
    HTB.ifz hA hB
  have hC : HTB S (.const eDn 0) (fun c => P c ∧ c.reg eF1 ≠ 0) Q (feasC I + 1) :=
    HTB.of_false fun c h => h.2 h.1.1.2.2.1
  have h1 : HTB S feasOpt P Q (feasC I + 1 + 1) := HTB.ifz hin hC
  by_cases hok : I.gap Xs * (bigE I.t I.k : ℤ) ^ 2 ≤ 4 ^ prec I.t I.k
  · -- success: `eCnt := 0`
    have hnext : ellIter I (consts I.t I.k) (i + 1) = .inr Xs := by
      rw [ellIter_succ_inl hst, ellStep, hcut0]; simp [hok]
    have h2 : HTB S (.const eCnt 0) (fun c => Q c ∧ c.reg eDn ≠ 0) (IterPost I Ly i) 1 :=
      HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hE, hm, _⟩, _⟩, _⟩ => by
        have hEi : RegIndep (wregs (.const eCnt 0)) (EG I Ly) := by indep [eG_iff, QRegs]
        refine ⟨hEi.run (by decide) hE, ?_, ?_, ?_⟩
        · rw [run_mem_of_stores (by decide) rfl c, hm]; exact hH2
        · rw [run_mem_of_stores (by decide) rfl c, hm]; exact hz2
        · unfold MSt
          rw [hnext]
          refine ⟨by simp, ?_⟩
          rw [run_mem_of_stores (by decide) rfl c, hm]; exact hX2
    have h3 : HTB S (.seq gLoop upd) (fun c => Q c ∧ c.reg eDn = 0) (IterPost I Ly i)
        (gC I + updCost (nDim I.t I.k) (bitB I.t I.k)) := HTB.of_false fun c h => by
      have := h.1.1.2.2
      simp only [hok, ↓reduceIte] at this
      omega
    have h4 : HTB S (.const eCnt 0) (fun c => Q c ∧ c.reg eDn ≠ 0) (IterPost I Ly i)
        (gC I + updCost (nDim I.t I.k) (bitB I.t I.k)) := h2.weaken (by unfold gC; omega)
    refine (h1.seq (HTB.ifz h3 h4)).weaken ?_
    omega
  · -- the gradient cut
    have hcut : ellCut I (consts I.t I.k) st.As = .inl (gradCut I Xs) := by
      rw [hcut0]; simp [hok]
    have h2 := (cutUpd_specB I Ly hL hI hi hst hcut 0 0 (flat (I.L Xs)) (feasMem I Ly st.As m)
      hSt2 hH2 hz2 (fun _ _ => hL2) (fun c hc j hj => gMode_grad Xs hc hj) hS).frameReg
      (regIndep_cnt gu_wregs v)
    have hnext : ellIter I (consts I.t I.k) (i + 1) =
        .inl (ellUpdate I (consts I.t I.k) st (gradCut I Xs)) := by
      rw [ellIter_succ_inl hst, ellStep, hcut]
    have h3 : HTB S (.seq gLoop upd) (fun c => Q c ∧ c.reg eDn = 0)
        (IterPost I Ly i) (gC I + updCost (nDim I.t I.k) (bitB I.t I.k)) := by
      refine (h2.pre fun c h => ⟨⟨h.1.1.1, h.1.1.2.1, h.1.2.1, h.1.2.2.1⟩, h.1.2.2.2⟩).post
        fun c h => ?_
      obtain ⟨⟨hE, hS, hH', hz'⟩, hc⟩ := h
      refine ⟨hE, hH', hz', ?_⟩
      unfold MSt
      rw [hnext]
      exact ⟨hc, hS⟩
    have h4 : HTB S (.const eCnt 0) (fun c => Q c ∧ c.reg eDn ≠ 0) (IterPost I Ly i)
        (gC I + updCost (nDim I.t I.k) (bitB I.t I.k)) := HTB.of_false fun c h => h.2 (by
      have := h.1.1.2.2
      simp only [hok, ↓reduceIte] at this
      exact this)
    refine (h1.seq (HTB.ifz h3 h4)).weaken ?_
    omega

/-! ### One iteration -/

/-- **One iteration**: from the state `st = ellIter i` (`i < N`) in memory and `eCnt = N − i`,
`iterB` reaches the state of iteration `i + 1` (`MSt`), keeping `H` and the free memory. -/
theorem iter_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (hI : I.Valid) {i : ℕ}
    (hi : i < iters I.t I.k) {st : EllState I} (hst : ellIter I (consts I.t I.k) i = .inl st)
    (m : ℕ → ℕ) (hSt : StMem I Ly st m) (hH : HMem I m Ly.bh) (hz : ZeroFrom m Ly.F)
    (hS : Ly.F + ellSc I.t I.k ≤ S) :
    HTB S iterB (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg eCnt = iters I.t I.k - i)
      (IterPost I Ly i) (iterCost I) := by
  set v := iters I.t I.k - (i + 1) with hv
  have h0 : HTB S (dec eCnt) (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg eCnt = iters I.t
      I.k - i)
      (fun cfg => (EG I Ly cfg ∧ cfg.mem = m) ∧ cfg.reg eCnt = v) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hE, hm, hc⟩ => by
      have hEi : RegIndep (wregs (dec eCnt)) (EG I Ly) := by indep [eG_iff, QRegs]
      refine ⟨⟨hEi.run (by decide) hE, by rw [run_mem_of_stores (by decide) rfl c, hm]⟩, ?_⟩
      simp +decide [run_dec, hc, hv]
      omega
  have h1 := (scan_specB I Ly st.As m hSt.a (hL.fits (S := S) (by omega)).2.1).frameReg
    (regIndep_cnt scan_wregs v)
  have htail : HTB S tailB (fun cfg => (EG I Ly cfg ∧ cfg.mem = m ∧
      cfg.reg eF1 = enc (negFind st.As) ∧ cfg.reg eF2 = enc (overFind (prec I.t I.k) st.As)) ∧
      cfg.reg eCnt = v) (IterPost I Ly i)
      (feasC I + 2 + (gC I + updCost (nDim I.t I.k) (bitB I.t I.k) + 1)) := by
    rcases hnf : negFind st.As with _ | a
    · rcases hof : overFind (prec I.t I.k) st.As with _ | c0
      · exact tail_feasB I Ly hL hI hi hst (negFind_none hnf) (overFind_none hof) m hSt hH hz hS
      · obtain ⟨c', hfo, hc'⟩ := overFind_some hof
        have hcut : ellCut I (consts I.t I.k) st.As = .inl (blockCut I c') := by
          have hfo' : firstOver I (consts I.t I.k).p st.As = some c' := hfo
          unfold ellCut; rw [negFind_none hnf, hfo']
        refine tail_cutB I Ly hL hI hi hst hcut (enc none) (enc (some c0)) (Or.inr (by simp [enc]))
          m hSt hH hz (fun c hc j hj => ?_) hS
        rw [gMode_block c' _ hc hj, ← hc']
        rfl
    · obtain ⟨i0, hfn, hia⟩ := negFind_some hnf
      have hcut : ellCut I (consts I.t I.k) st.As = .inl (negCut I i0) := by
        unfold ellCut; rw [hfn]
      refine tail_cutB I Ly hL hI hi hst hcut (enc (some a)) (enc (overFind (prec I.t I.k) st.As))
        (Or.inl (by simp [enc])) m hSt hH hz (fun c hc j hj => ?_) hS
      rw [gMode_neg i0 _ _ hc hj, hia]
      rfl
  refine (h0.seq (h1.seq htail)).weaken ?_
  unfold iterCost scanC
  omega

end STACS2027.Runtimes.QPRam
