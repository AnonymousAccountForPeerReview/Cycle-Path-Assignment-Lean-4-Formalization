module

public import Runtimes.ConvexQP.RAM.KmoK4
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: Phase K, part 5 (the row writers of the rows of `(c, j)`)

The rows of `(c, j)` (`a = c k + j`, `Gx_X`) are of two kinds:
* type A (`rowA ng pr`): the `x`-part is `±H_a` (`cpLoop` from the row `a` of `H`, sign `−` iff
  `ng ≠ 0`), the entry `π_c` is the pair in `pr`; `rowA_of` identifies `Gx` with it when
  `coefX = 0`;
* type B (`rowB pr`): the single entry `x_a` is the pair in `pr`; `rowB_of` when `coefL = 0`.
Both write `h'_R = 1` and advance the row pointers (`rowA_spec`, `rowB_spec`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### The contents of the rows of `(c, j)` -/

theorem coef_values :
    coefX false ⟨0, by norm_num⟩ = 0 ∧ coefL false ⟨0, by norm_num⟩ = 1 ∧
    coefX false ⟨1, by norm_num⟩ = 0 ∧ coefL false ⟨1, by norm_num⟩ = -1 ∧
    coefX false ⟨2, by norm_num⟩ = -1 ∧ coefL false ⟨2, by norm_num⟩ = 0 ∧
    coefX true ⟨0, by norm_num⟩ = 1 ∧ coefL true ⟨0, by norm_num⟩ = 0 ∧
    coefX true ⟨1, by norm_num⟩ = -1 ∧ coefL true ⟨1, by norm_num⟩ = 0 ∧
    coefX true ⟨2, by norm_num⟩ = 0 ∧ coefL true ⟨2, by norm_num⟩ = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

variable {I : Inst} {Xs : Fin I.t → Fin I.k → ℤ}

/-- A row of type A: `coefX = 0`, `coefL = sgnMul ng 1`. -/
theorem rowA_of {a b : ℕ} (ha : a < I.t * I.k) (hb : b < 3) (ng : ℕ)
    (hX : coefX (Zf I Xs a) ⟨b, hb⟩ = 0) (hL : coefL (Zf I Xs a) ⟨b, hb⟩ = sgnMul ng 1) :
    ∀ v < dd I + 1, Gx I Xs (2 * I.t + 3 * a + b) v =
      if v < I.t * I.k then sgnMul ng (Hflat I a v)
      else if v = I.t * I.k + a / I.k then -sgnMul ng 1 else 0 := by
  intro v hv
  have hd := dimKKT_eq I.t I.k
  have hc : a / I.k < I.t := div_lt_of_lt_tk ha
  rw [Gx_X I Xs ha hb v, hX, hL]
  by_cases hvx : v < I.t * I.k
  · simp only [hvx, ↓reduceIte, zero_mul, zero_add, sgnMul]
    split_ifs <;> ring
  · simp only [hvx, ↓reduceIte]
    by_cases hvd : v < dimKKT I.t I.k
    · simp only [hvd, ↓reduceIte]
      split_ifs <;> ring
    · have : v ≠ I.t * I.k + a / I.k := by omega
      simp [hvd, this]

/-- A row of type B: `coefX = σ`, `coefL = 0`. -/
theorem rowB_of {a b : ℕ} (ha : a < I.t * I.k) (hb : b < 3) (σ : ℤ)
    (hX : coefX (Zf I Xs a) ⟨b, hb⟩ = σ) (hL : coefL (Zf I Xs a) ⟨b, hb⟩ = 0) :
    ∀ v < dd I + 1, Gx I Xs (2 * I.t + 3 * a + b) v = if v = a then σ else 0 := by
  intro v hv
  have hd := dimKKT_eq I.t I.k
  rw [Gx_X I Xs ha hb v, hX, hL]
  by_cases hvx : v < I.t * I.k
  · simp only [hvx, ↓reduceIte, zero_mul, add_zero]
    split_ifs <;> ring
  · have : v ≠ a := by omega
    simp [hvx, this]

/-! ### The registers of the rows of `(c, j)` -/

variable {S : ℕ}

section XRows

variable (I) (F₀ bh bx : ℕ)

/-- The registers before row `R`, option `a`, cycle `c`. -/
def XG (a c R : ℕ) (cfg : Config) : Prop :=
  KGl I F₀ bh bx cfg ∧ cfg.reg kRP = (lay I F₀).pG + R * gsz I ∧
    cfg.reg kHP = (lay I F₀).php + R * 2 ∧ cfg.reg kXP = (lay I F₀).pZn + a * 2 ∧
    cfg.reg kLP = (lay I F₀).pL + a * 2 ∧
    cfg.reg kPP = (lay I F₀).pZn + 2 * (I.t * I.k) + c * 2 ∧
    cfg.reg kHR = bh + a * (2 * (I.t * I.k)) ∧ cfg.reg kTK2 = 2 * (I.t * I.k) ∧
    SReg cfg kONE 1 ∧ SReg cfg kMONE (-1)

theorem XG_regIndep (a c R : ℕ) :
    RegIndep (rT :: kC :: kJJ :: (List.range' 400 50 ++ List.range' 530 10)) (XG I F₀ bh bx a c R) :=
  (KGl.regIndep' I F₀ bh bx (by decide)).and (by indep [SReg])

/-- The last part of a row: `h'_R := 1`, `kRP += gs`, `kHP += 2`. -/
def rowEnd (pr : ℕ) : Stmt :=
  .seq (sstore kA pr) (.seq (sstore kHP kONE) (.seq (.add kRP kRP kGS) (addc kHP kHP 2)))

/-- A row of type B: the entry `x_a := pr`. -/
def rowB (pr : ℕ) : Stmt := .seq (.seq (.add kA kRP kXP) (.sub kA kA kPZN)) (rowEnd pr)

/-- Inputs of the copy `x`-part `:= ±H_a`. -/
def rowASet (ng : ℕ) : Stmt :=
  .seq (mov kN qKT) (.seq (mov kPS kHR) (.seq (.const kSS 2) (.seq (mov kPD kRP)
    (.seq (.const kSD 2) (.const kNG ng)))))

/-- A row of type A: `x`-part `:= ±H_a`, the entry `π_c := pr`. -/
def rowA (ng pr : ℕ) : Stmt :=
  .seq (rowASet ng) (.seq cpLoop (.seq (.seq (.add kA kRP kPP) (.sub kA kA kPZN)) (rowEnd pr)))

variable {I F₀ bh bx}

/-- The end of a row: from the memory `m` with the row at `rb` written, `h'_R := 1` and the
pointers advanced. -/
theorem rowEnd_spec {a c R : ℕ} (pr : ℕ) (σ : ℤ) (addr : ℕ) (m : ℕ → ℕ)
    (hne : pr ≠ kA ∧ pr + 1 ≠ kA ∧ pr ≠ rT ∧ pr + 1 ≠ rT)
    (hσr : ∀ cfg, XG I F₀ bh bx a c R cfg → SReg cfg pr σ) (hSa : addr + 1 < S)
    (hSh : (lay I F₀).php + R * 2 + 1 < S) :
    HTB S (rowEnd pr) (fun cfg => XG I F₀ bh bx a c R cfg ∧ cfg.reg kA = addr ∧ cfg.mem = m)
      (fun cfg => XG I F₀ bh bx a c (R + 1) cfg ∧
        cfg.mem = sw (sw m addr σ) ((lay I F₀).php + R * 2) 1) 12 :=
  HTB.of_HT_addrOK (by simp [rowEnd, LoopFree, sstore]) (fun cfg ⟨hcfg, hA, _⟩ => by
    obtain ⟨_, _, hhp', _⟩ := hcfg
    addr_ok [rowEnd, sstore, hA, hhp']) <| HT.run_le (by simp [rowEnd, LoopFree, sstore]) (by simp [rowEnd, size, sstore])
    fun cfg ⟨hcfg, hA, hm⟩ => by
      have hs0 := hσr cfg hcfg
      obtain ⟨hk, hrp, hhp', hxp, hlp, hpp, hhr, htk, hone1, hmone⟩ := hcfg
      obtain ⟨hn1, hn2, hn3, hn4⟩ := hne
      have hW : ∀ r ∈ wregs (rowEnd pr), r ∈ [rT, kA, kRP, kHP] := by
        simp +decide [rowEnd, wregs, sstore]
      have hrun : ∀ {P : Config → Prop}, RegIndep [rT, kA, kRP, kHP] P → P cfg →
          P (RAM.run (rowEnd pr) cfg) := fun hP hc =>
        (hP.mono hW).run (by simp [rowEnd, LoopFree, sstore]) hc
      have hmem : (RAM.run (rowEnd pr) cfg).mem = sw (sw m addr σ) ((lay I F₀).php + R * 2) 1 := by
        simp +decide only [rowEnd, sstore, run_seq', run_add, run_addc, run_store, setReg_reg,
          setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hhp', hm, hA, hn4]
        rw [hs0.1, hs0.2, hone1.1, hone1.2]
        rfl
      refine ⟨⟨hrun (KGl.regIndep' I F₀ bh bx (by decide)) hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        hmem⟩
      all_goals first
        | exact (regIndep_sreg (W := wregs (rowEnd pr)) (by simp +decide [rowEnd, wregs, sstore])
            (by simp +decide [rowEnd, wregs, sstore]) _).run (by simp [rowEnd, LoopFree, sstore])
            (by assumption)
        | (simp +decide only [rowEnd, sstore, run_seq', run_add, run_addc, run_store, setReg_reg,
            setMem_reg, ↓reduceIte, hrp, hhp', hxp, hlp, hpp, hhr, htk, hk.glob.gs]; try ring)

/-- The memory of a finished row: the rows up to `R` are written. -/
theorem rowsK_after {R : ℕ} (hR : R < MM I) {m : ℕ → ℕ} (hRm : RowsK I Xs F₀ m R)
    {mπ : ℕ → ℕ} (hO : OutGH I F₀ mπ m) {m₁ : ℕ → ℕ} (σ : ℤ) (addr : ℕ)
    (hm₁ : ∀ x, (x < (lay I F₀).pG + R * gsz I ∨ (lay I F₀).pG + R * gsz I + gsz I ≤ x) →
      m₁ x = m x)
    (haddr : (lay I F₀).pG + R * gsz I ≤ addr ∧ addr + 2 ≤ (lay I F₀).pG + R * gsz I + gsz I)
    (hrow : SArr (sw m₁ addr σ) ((lay I F₀).pG + R * gsz I) 2 (dd I + 1) (Gx I Xs R))
    (hhp : hpf I R = 1) :
    RowsK I Xs F₀ (sw (sw m₁ addr σ) ((lay I F₀).php + R * 2) 1) (R + 1) ∧
      OutGH I F₀ mπ (sw (sw m₁ addr σ) ((lay I F₀).php + R * 2) 1) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  have hRg := succ_mul_le (gsz I) hR
  have hst := hRm.step hR (m' := sw (sw m₁ addr σ) ((lay I F₀).php + R * 2) 1)
    (fun x hx hy => by
      rw [sw_of_out _ (by omega), sw_of_out _ (by omega)]
      exact hm₁ x hx)
    (sarr_of_eq hrow fun j hj => by
      have := entry_lt (b := (lay I F₀).pG + R * gsz I) (s := 2) (le_refl 2) hj
      exact ⟨sw_of_out _ (by omega), sw_of_out _ (by omega)⟩)
    (by rw [hhp]; exact smem_sw _ _ _)
  exact ⟨hst.1, hO.trans hst.2⟩

/-- **A row of type B.** -/
theorem rowB_spec {a c R : ℕ} (hR : R < MM I) (ha : a < I.t * I.k) (pr : ℕ) (σ : ℤ)
    (hne : pr ≠ kA ∧ pr + 1 ≠ kA ∧ pr ≠ rT ∧ pr + 1 ≠ rT)
    (hσr : ∀ cfg, XG I F₀ bh bx a c R cfg → SReg cfg pr σ)
    (hrow : ∀ v < dd I + 1, Gx I Xs R v = if v = a then σ else 0)
    (hhp : hpf I R = 1) (mπ : ℕ → ℕ) (hS : (lay I F₀).fe ≤ S) :
    HTB S (rowB pr)
      (fun cfg => XG I F₀ bh bx a c R cfg ∧ RowsK I Xs F₀ cfg.mem R ∧ OutGH I F₀ mπ cfg.mem)
      (fun cfg => XG I F₀ bh bx a c (R + 1) cfg ∧ RowsK I Xs F₀ cfg.mem (R + 1) ∧
        OutGH I F₀ mπ cfg.mem) 14 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hR₀, hO₀⟩ => ?_
  have hRg := succ_mul_le (gsz I) hR
  set rb := (lay I F₀).pG + R * gsz I with hrb
  have b1 : HTB S (.seq (.add kA kRP kXP) (.sub kA kA kPZN)) (fun cfg => cfg = c₀)
      (fun cfg => XG I F₀ bh bx a c R cfg ∧ cfg.reg kA = rb + 2 * a ∧ cfg.mem = c₀.mem) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg hcfg => by
      subst hcfg
      refine ⟨(XG_regIndep I F₀ bh bx a c R).run_of_sub (by decide) (by decide) hc₀, ?_, ?_⟩
      · simp +decide only [run_seq', run_add, run_sub, setReg_reg, ↓reduceIte, hc₀.2.1, hc₀.2.2.2.1,
          hc₀.1.glob.pZn]
        omega
      · simp only [run_seq', run_add, run_sub, setReg_mem]
  have b2 := rowEnd_spec (S := S) (F₀ := F₀) (bh := bh) (bx := bx) (a := a) (c := c) (R := R) pr σ
    (rb + 2 * a) c₀.mem hne hσr (by omega) (by omega)
  refine (b1.seq b2).mono (fun cfg h => h) (fun cfg ⟨hx, hm⟩ => ?_) (by omega)
  refine ⟨hx, ?_⟩
  rw [hm]
  have hzr : ∀ x, rb ≤ x → x < rb + (dd I + 1) * 2 → c₀.mem x = 0 := fun x hx1 hx2 =>
    hR₀.zg x hx1 (by omega)
  exact rowsK_after hR hR₀ hO₀ σ (rb + 2 * a) (fun x _ => rfl) ⟨by omega, by omega⟩
    (sarr_congr (rowB_content (d := dd I) σ hzr) fun v hv => (hrow v hv).symm) hhp

/-- **A row of type A.** -/
theorem rowA_spec {a c R : ℕ} (hR : R < MM I) (ha : a < I.t * I.k) (hc : c < I.t) (ng pr : ℕ)
    (σ : ℤ) (hne : pr ≠ kA ∧ pr + 1 ≠ kA ∧ pr ≠ rT ∧ pr + 1 ≠ rT)
    (hσr : ∀ cfg, XG I F₀ bh bx a c R cfg → SReg cfg pr σ)
    (hrow : ∀ v < dd I + 1, Gx I Xs R v =
      if v < I.t * I.k then sgnMul ng (Hflat I a v) else if v = I.t * I.k + c then σ else 0)
    (hhp : hpf I R = 1) (mπ : ℕ → ℕ) (hH : HMem I mπ bh) (hbh : bh + hCells I ≤ F₀)
    (hS : (lay I F₀).fe ≤ S) :
    HTB S (rowA ng pr)
      (fun cfg => XG I F₀ bh bx a c R cfg ∧ RowsK I Xs F₀ cfg.mem R ∧ OutGH I F₀ mπ cfg.mem)
      (fun cfg => XG I F₀ bh bx a c (R + 1) cfg ∧ RowsK I Xs F₀ cfg.mem (R + 1) ∧
        OutGH I F₀ mπ cfg.mem) (I.t * I.k * 27 + 26) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  have hC : hCells I = I.t * I.k * (2 * (I.t * I.k)) := rfl
  refine HTB.of_forall fun c₀ ⟨hc₀, hR₀, hO₀⟩ => ?_
  have hRg := succ_mul_le (gsz I) hR
  have hag := succ_mul_le (2 * (I.t * I.k)) ha
  set rb := (lay I F₀).pG + R * gsz I with hrb
  have hXG := XG_regIndep I F₀ bh bx a c R
  have b1 : HTB S (rowASet ng) (fun cfg => cfg = c₀)
      (fun cfg => XG I F₀ bh bx a c R cfg ∧ cfg.mem = c₀.mem ∧ cfg.reg kN = I.t * I.k ∧
        cfg.reg kPS = bh + a * (2 * (I.t * I.k)) ∧ cfg.reg kSS = 2 ∧ cfg.reg kPD = rb ∧
        cfg.reg kSD = 2 ∧ cfg.reg kNG = ng) 9 :=
    HTB.of_HT (by simp [rowASet, memFree]) <| HT.run_le (by simp [rowASet, LoopFree]) (by simp [rowASet, size]) fun cfg hcfg => by
      subst hcfg
      have hq := hc₀.1.glob.qregs
      rw [qregs_iff] at hq
      refine ⟨hXG.run_of_sub (by simp [rowASet, LoopFree]) (by simp +decide [rowASet, wregs]) hc₀,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [rowASet, run_seq', run_mov, run_const, setReg_reg, setReg_mem,
        ↓reduceIte, hq.2.2.1, hc₀.2.1, hc₀.2.2.2.2.2.2.1, hrb]
  have hH₀ : HMem I c₀.mem bh := fun i hi => sarr_of_eq (hH i hi) fun j hj => by
    have := entry_lt (b := bh + i * (2 * (I.t * I.k))) (s := 2) (le_refl 2) hj
    have := succ_mul_le (2 * (I.t * I.k)) hi
    exact ⟨hO₀ _ (Or.inl (by omega)) (Or.inl (by omega)),
      hO₀ _ (Or.inl (by omega)) (Or.inl (by omega))⟩
  have b2 := cpLoop_spec (S := S) (R := XG I F₀ bh bx a c R) (hXG.mono (by decide)) c₀.mem (I.t * I.k)
    (bh + a * (2 * (I.t * I.k))) 2 rb 2 ng (Hflat I a) (le_refl 2) (fun m hm j hj => by
      have ho := out_of_sameOn hm
      have hS := hH₀ a ha j hj
      have := entry_lt (b := bh + a * (2 * (I.t * I.k))) (s := 2) (le_refl 2) hj
      exact ⟨(ho _ (Or.inl (by omega))).trans hS.1, (ho _ (Or.inl (by omega))).trans hS.2⟩)
    (fun j hj => addr_lt_of_stride (le_refl 2)
      (show bh + a * (2 * (I.t * I.k)) + I.t * I.k * 2 ≤ S by omega) hj) (by omega)
  set m₁ := wrArr c₀.mem rb 2 (fun j => sgnMul ng (Hflat I a j)) (I.t * I.k) with hm₁
  have b3 : HTB S (.seq (.add kA kRP kPP) (.sub kA kA kPZN))
      (fun cfg => XG I F₀ bh bx a c R cfg ∧ cfg.mem = m₁)
      (fun cfg => XG I F₀ bh bx a c R cfg ∧ cfg.reg kA = rb + (2 * (I.t * I.k) + 2 * c) ∧
        cfg.mem = m₁) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨hcfg, hm⟩ => by
      refine ⟨hXG.run_of_sub (by decide) (by decide) hcfg, ?_, ?_⟩
      · simp +decide only [run_seq', run_add, run_sub, setReg_reg, ↓reduceIte, hcfg.2.1,
          hcfg.2.2.2.2.2.1, hcfg.1.glob.pZn]
        omega
      · simp only [run_seq', run_add, run_sub, setReg_mem, hm]
  have b4 := rowEnd_spec (S := S) (F₀ := F₀) (bh := bh) (bx := bx) (a := a) (c := c) (R := R) pr σ
    (rb + (2 * (I.t * I.k) + 2 * c)) m₁ hne hσr (by omega) (by omega)
  refine (b1.seq (b2.seq (b3.seq b4))).mono (fun cfg h => h) (fun cfg ⟨hx, hm⟩ => ?_)
    (by omega)
  refine ⟨hx, ?_⟩
  rw [hm]
  have hzr : ∀ x, rb ≤ x → x < rb + (dd I + 1) * 2 → c₀.mem x = 0 := fun x hx1 hx2 =>
    hR₀.zg x hx1 (by omega)
  refine rowsK_after hR hR₀ hO₀ σ (rb + (2 * (I.t * I.k) + 2 * c))
    (fun x hx => wrArr_of_out (le_refl 2) (by omega)) ⟨by omega, by omega⟩
    (sarr_congr (rowA_content (d := dd I) (n := I.t * I.k) (c := c)
      (fun j => sgnMul ng (Hflat I a j)) σ hzr) fun v hv => (hrow v hv).symm) hhp

end XRows

end STACS2027.Runtimes.QPRam.Kmo
