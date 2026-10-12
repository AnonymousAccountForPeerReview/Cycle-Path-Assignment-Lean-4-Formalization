module

public import Runtimes.ConvexQP.RAM.KmoOut
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: Phase K, part 1 (layout, `1`, `Zn[0, tk) := Xs`, `L = H Xs`)

* `kAlloc`: the strides `gs = 2d + 2`, `as = 2d`, the region pointers of `lay I F₀`, `E`, and
  `rFREE := fe` (two `mul` for `M · gs` and `d · as`);
* `kOne`: the constant `1` at `pOne`;
* `kCopy`: `Zn[0, tk) := Xs` (`cpLoop`);
* `kLBlk`: `L := H Xs` (`mvCore`; `mulVec_Hflat` identifies it with `I.L Xs`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### Registers of Phase K -/

/-- Phase K: `pL`. -/
abbrev kKL : ℕ := 515
/-- Phase K: `pOne`. -/
abbrev kKO : ℕ := 516
/-- Phase K: the outer counter (cycles). -/
abbrev kC : ℕ := 517
/-- Phase K: the inner counter (options) / the fill offset `2kc`. -/
abbrev kJJ : ℕ := 518
/-- Phase K: the row pointer `pG + R gs`. -/
abbrev kRP : ℕ := 519
/-- Phase K: the pointer `php + 2R`. -/
abbrev kHP : ℕ := 520
/-- Phase K: the pointer `pZn + 2a` / `2k`. -/
abbrev kXP : ℕ := 521
/-- Phase K: the pointer `pL + 2a` / the pair `E + 1`. -/
abbrev kLP : ℕ := 522
/-- Phase K: the pointer `pZn + 2tk + 2c`. -/
abbrev kPP : ℕ := 523
/-- Phase K: the row pointer of `H` / the pair `1 − E` / the accumulator of the minimum. -/
abbrev kHR : ℕ := 524
/-- Phase K: `2tk`. -/
abbrev kTK2 : ℕ := 525
/-- Phase K: the pair `1`. -/
abbrev kONE : ℕ := 526
/-- Phase K: the pair `−1`. -/
abbrev kMONE : ℕ := 528

/-- The registers Phase K uses as scratch (besides the library): `517–539`. -/
def kW : List ℕ := rT :: (List.range' 400 50 ++ List.range' 517 23)

/-! ### The constant registers of Phase K -/

/-- The registers that stay constant during Phase K (after `kAlloc`). -/
@[mk_iff]
structure KGl (I : Inst) (F₀ bh bx : ℕ) (c : Config) : Prop where
  glob : Glob I F₀ c
  bh : c.reg qBH = bh
  bx : c.reg qBX = bx
  pL : c.reg kKL = (lay I F₀).pL
  pOne : c.reg kKO = (lay I F₀).pOne

theorem KGl.regIndep (I : Inst) (F₀ bh bx : ℕ) : RegIndep kW (KGl I F₀ bh bx) :=
  fun c c' hc hk => ⟨(Glob.regIndep' I F₀ (by decide)) c c' hc hk.glob,
    by rw [hc qBH (by decide)]; exact hk.bh, by rw [hc qBX (by decide)]; exact hk.bx,
    by rw [hc kKL (by decide)]; exact hk.pL, by rw [hc kKO (by decide)]; exact hk.pOne⟩

theorem KGl.regIndep' (I : Inst) (F₀ bh bx : ℕ) {W : List ℕ} (hW : ∀ r ∈ W, r ∈ kW) :
    RegIndep W (KGl I F₀ bh bx) := (KGl.regIndep I F₀ bh bx).mono hW

/-! ### The layout -/

/-- The strides. -/
def kA1 : Stmt := .seq (.add kGS qD qD) (.seq (addc kGS kGS 2) (.add kAS qD qD))

/-- The region pointers (after `kP1 = M gs`, `kP2 = d as`), `E`, and `rFREE`. -/
def kA2 : Stmt :=
  .seq (mov kPG rFREE) (.seq (.add kPAJ kPG kP1) (.seq (.add kPZN kPAJ kP2)
  (.seq (.add kPCOL kPZN kAS) (.seq (.add kPU kPCOL kAS) (.seq (.add kPV kPU kAS)
  (.seq (.add kPW kPV kAS) (.seq (.add kPOM kPW kAS) (.seq (.add kP1 qM qM)
  (.seq (.add kPSG kPOM kP1) (.seq (.add kPHP kPSG kP1) (.seq (.add kPT kPHP kP1)
  (.seq (.add kKL kPT qD) (.seq (.add kP2 qKT qKT) (.seq (.add kKO kKL kP2)
  (.seq (addc rFREE kKO 2) (sofNat kE qE))))))))))))))))

/-- The layout of Phases K, M, O. -/
def kAlloc : Stmt := .seq kA1 (.seq (mul kP1 qM kGS kJ) (.seq (mul kP2 qD kAS kJ) kA2))

theorem kAlloc_spec (I : Inst) (F₀ bh bx : ℕ) (m₀ : ℕ → ℕ) :
    HT kAlloc (fun c => QRegs I c ∧ c.reg qBH = bh ∧ c.reg qBX = bx ∧ c.reg rFREE = F₀ ∧
        c.mem = m₀)
      (fun c => KGl I F₀ bh bx c ∧ c.mem = m₀) (5 * gsz I + 5 * asz I + 50) := by
  let P1 : Config → Prop := fun c => (QRegs I c ∧ c.reg qBH = bh ∧ c.reg qBX = bx ∧
    c.reg rFREE = F₀ ∧ c.mem = m₀) ∧ c.reg kGS = gsz I ∧ c.reg kAS = asz I
  have hP1 : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ [kP1, kP2, kJ, rT]) → Indep W P1 := by
    intro W hW
    have hQ : Indep W (QRegs I) :=
      ((show RegIndep [kP1, kP2, kJ, rT] (QRegs I) by indep [qregs_iff]).mono hW).indep
    have h0 : ∀ r ∈ [qBH, qBX, rFREE, kGS, kAS], r ∉ [kP1, kP2, kJ, rT] := by decide
    have hn : ∀ r ∈ [qBH, qBX, rFREE, kGS, kAS], r ∉ W := fun r hr h => h0 r hr (hW r h)
    exact (hQ.and ((Indep.reg (hn qBH (by decide)) (· = bh)).and
      ((Indep.reg (hn qBX (by decide)) (· = bx)).and ((Indep.reg (hn rFREE (by decide)) (· = F₀)).and
      (Indep.mem (· = m₀)))))).and ((Indep.reg (hn kGS (by decide)) (· = gsz I)).and
      (Indep.reg (hn kAS (by decide)) (· = asz I)))
  have b1 : HT kA1 (fun c => QRegs I c ∧ c.reg qBH = bh ∧ c.reg qBX = bx ∧ c.reg rFREE = F₀ ∧
      c.mem = m₀) P1 4 :=
    HT.run_le (by decide) (by decide) fun c ⟨hq, hbh, hbx, hF, hm⟩ => by
      have hq' := hq
      rw [qregs_iff] at hq'
      refine ⟨⟨(show RegIndep (wregs kA1) (QRegs I) by indep [qregs_iff]).run (by decide) hq,
        ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp +decide only [kA1, run_seq', run_add, run_addc, setReg_reg, setReg_mem, ↓reduceIte,
        hbh, hbx, hF, hm, hq'.2.2.2.2.1, gsz, asz, dd] <;> omega
  have b2 := HT.mul (P := P1) (d := kP1) (a := qM) (b := kGS) (k := kJ) (x := MM I) (y := gsz I)
    (by decide) (hP1 (by decide)) (fun c hc => by
      have := hc.1.1; rw [qregs_iff] at this; exact this.2.2.2.2.2.1) (fun c hc => hc.2.1)
  have b3 := HT.mul (P := fun c => P1 c ∧ c.reg kP1 = MM I * gsz I) (d := kP2) (a := qD)
    (b := kAS) (k := kJ) (x := dd I) (y := asz I) (by decide)
    ((hP1 (by decide)).and (Indep.reg (W := [kP2, kJ, rT]) (r := kP1) (by decide)
      (· = MM I * gsz I))) (fun c hc => by
      have := hc.1.1.1; rw [qregs_iff] at this; exact this.2.2.2.2.1) (fun c hc => hc.1.2.2)
  have b4 : HT kA2 (fun c => (P1 c ∧ c.reg kP1 = MM I * gsz I) ∧ c.reg kP2 = dd I * asz I)
      (fun c => KGl I F₀ bh bx c ∧ c.mem = m₀) 35 :=
    HT.run_le (by decide) (by decide) fun c ⟨⟨⟨⟨hq, hbh, hbx, hF, hm⟩, hgs, has⟩, hp1⟩, hp2⟩ => by
      have hq' := hq
      rw [qregs_iff] at hq'
      obtain ⟨_, _, hkt, _, hd, hM, _, _, hE, _, _⟩ := hq'
      have hQ : QRegs I (RAM.run kA2 c) :=
        (show RegIndep (wregs kA2) (QRegs I) by indep [qregs_iff]).run (by decide) hq
      refine ⟨⟨⟨hQ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_,
        ?_⟩, ?_⟩ <;>
      simp +decide only [kA2, sofNat, run_seq', run_add, run_addc, run_mov, run_const, setReg_reg,
        setReg_mem, ↓reduceIte, hbh, hbx, hF, hm, hgs, has, hp1, hp2, hkt, hd, hM, hE, lay,
        sgnBit, gsz, asz, dd, MM] <;> first | rfl | omega
  exact (b1.seq (b2.seq (b3.seq b4))).weaken (by omega)

/-! ### `1`, `Zn[0, tk) := Xs`, `L := H Xs` -/

/-- The constant `1` at `pOne`. -/
def kOne : Stmt := .seq (sconst kX 1) (sstore kKO kX)

/-- Inputs of the copy `Zn[0, tk) := Xs`. -/
def kCSet : Stmt :=
  .seq (mov kN qKT) (.seq (mov kPS qBX) (.seq (.const kSS 2) (.seq (mov kPD kPZN)
    (.seq (.const kSD 2) (.const kNG 0)))))

/-- Inputs of `mvCore` for `L = H Xs`. -/
def kLSet : Stmt :=
  .seq (.add kP2 qKT qKT) (.seq (mov vR qKT) (.seq (mov vRow qBH) (.seq (mov vSI kP2)
    (.seq (mov vN qKT) (.seq (.const vSA 2) (.seq (mov vX0 kPZN) (.seq (.const vSX 2)
    (mov vPU kKL))))))))

/-- Phase K, part 1. -/
def kPart1 : Stmt := .seq kAlloc (.seq kOne (.seq (.seq kCSet cpLoop) (.seq kLSet mvCore)))

/-- `L = H Xs` on flat indices. -/
def Lf (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (a : ℕ) : ℤ :=
  mulVec (Hflat I) (flat Xs) (I.t * I.k) a

/-- `m` is zero on `[x, y)`. -/
def ZeroOn (m : ℕ → ℕ) (x y : ℕ) : Prop := ∀ a, x ≤ a → a < y → m a = 0

/-- The memory after part 1 of Phase K. -/
structure KM1 (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ bh : ℕ) (m : ℕ → ℕ) : Prop where
  hmem : HMem I m bh
  one : SMem m (lay I F₀).pOne 1
  xs : SArr m (lay I F₀).pZn 2 (I.t * I.k) (flat Xs)
  l : SArr m (lay I F₀).pL 2 (I.t * I.k) (Lf I Xs)
  z1 : ZeroOn m F₀ (lay I F₀).pZn
  z2 : ZeroOn m ((lay I F₀).pZn + 2 * (I.t * I.k)) (lay I F₀).pL
  zero : ZeroFrom m (lay I F₀).fe

variable {S : ℕ}

/-- **Phase K, part 1** (space: the layout and the table of `mvCore`, `2 B` cells from `fe`). -/
theorem kPart1_spec (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ bh bx : ℕ) (m₀ : ℕ → ℕ)
    (hH : HMem I m₀ bh) (hX : SArr m₀ bx 2 (I.t * I.k) (flat Xs)) (hbh : bh + hCells I ≤ F₀)
    (hbx : bx + I.t * I.k * 2 ≤ F₀) (hZ : ZeroFrom m₀ F₀) (B : ℕ)
    (hB : ∀ j < I.t * I.k, Nat.size (flat Xs j).natAbs ≤ B) (hS : (lay I F₀).fe + 2 * B ≤ S) :
    HTB S kPart1 (fun c => QRegs I c ∧ c.reg qBH = bh ∧ c.reg qBX = bx ∧ c.reg rFREE = F₀ ∧
        c.mem = m₀)
      (fun c => KGl I F₀ bh bx c ∧ KM1 I Xs F₀ bh c.mem)
      (5 * gsz I + 5 * asz I + 50 + 6 + (9 + (I.t * I.k * 27 + 3)) +
        (17 + (I.t * I.k * (I.t * I.k * (31 * B + 87) + 19) + 1))) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  have hK := KGl.regIndep I F₀ bh bx
  have hC : hCells I = I.t * I.k * (2 * (I.t * I.k)) := rfl
  -- `1`
  set m₁ := sw m₀ (lay I F₀).pOne 1 with hm₁
  have b1 : HTB S kOne (fun c => KGl I F₀ bh bx c ∧ c.mem = m₀)
      (fun c => KGl I F₀ bh bx c ∧ c.mem = m₁) 6 :=
    HTB.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      refine ⟨by addr_ok [kOne, sconst, sstore, hc.pOne], (hK.mono (by decide)).run (by decide) hc, ?_⟩
      simp +decide only [kOne, sconst, sstore, run_seq', run_const, run_addc, run_store, setReg_reg,
        setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hm, hc.pOne]
      rfl
  -- `Zn[0, tk) := Xs`
  have b2 : HTB S kCSet (fun c => KGl I F₀ bh bx c ∧ c.mem = m₁)
      (fun c => KGl I F₀ bh bx c ∧ c.mem = m₁ ∧ c.reg kN = I.t * I.k ∧ c.reg kPS = bx ∧
        c.reg kSS = 2 ∧ c.reg kPD = (lay I F₀).pZn ∧ c.reg kSD = 2 ∧ c.reg kNG = 0) 9 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      have hq := hc.glob.qregs
      rw [qregs_iff] at hq
      refine ⟨(hK.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [kCSet, run_seq', run_mov, run_const, setReg_reg, setReg_mem, ↓reduceIte,
        hm, hq.2.2.1, hc.bx, hc.glob.pZn]
  have ho₁ : Out (lay I F₀).pOne ((lay I F₀).pOne + 2) m₀ m₁ := out_sw le_rfl le_rfl
  have b3 := cpLoop_spec (S := S) (R := KGl I F₀ bh bx) (hK.mono (by decide)) m₁ (I.t * I.k) bx 2
    (lay I F₀).pZn 2 0 (flat Xs) (le_refl 2) (fun m hm j hj => by
      have := sarr_of_out (sarr_of_out hX (le_refl 2) ho₁ (Or.inl (by omega))) (le_refl 2)
        (out_of_sameOn hm) (Or.inl (by omega)) j hj
      exact this)
    (fun j hj => addr_lt_of_stride (le_refl 2) (show bx + I.t * I.k * 2 ≤ S by omega) hj)
    (by omega)
  set m₂ := wrArr m₁ (lay I F₀).pZn 2 (fun j => sgnMul 0 (flat Xs j)) (I.t * I.k) with hm₂
  have ho₂ : Out (lay I F₀).pZn ((lay I F₀).pZn + I.t * I.k * 2) m₁ m₂ :=
    out_wrArr (le_refl 2) le_rfl le_rfl
  have hxs : SArr m₂ (lay I F₀).pZn 2 (I.t * I.k) (flat Xs) :=
    sarr_congr (sarr_wrArr (le_refl 2) _) fun j _ => by simp [sgnMul]
  -- `L := H Xs`
  have b4 : HTB S kLSet (fun c => KGl I F₀ bh bx c ∧ c.mem = m₂)
      (fun c => KGl I F₀ bh bx c ∧ c.mem = m₂ ∧ c.reg vR = I.t * I.k ∧ c.reg vRow = bh ∧
        c.reg vSI = 2 * (I.t * I.k) ∧ c.reg vN = I.t * I.k ∧ c.reg vSA = 2 ∧
        c.reg vX0 = (lay I F₀).pZn ∧ c.reg vSX = 2 ∧ c.reg vPU = (lay I F₀).pL) 17 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      have hq := hc.glob.qregs
      rw [qregs_iff] at hq
      refine ⟨(hK.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [kLSet, run_seq', run_mov, run_const, run_add, setReg_reg, setReg_mem,
        ↓reduceIte, hm, hq.2.2.1, hc.bh, hc.glob.pZn, hc.pL]
      omega
  have hz₂ : ZeroFrom m₂ (lay I F₀).fe :=
    ho₂.zeroFrom (ho₁.zeroFrom (hZ.mono (by omega)) (by omega)) (by omega)
  have b5 := mvCore_specB (S := S) (R := KGl I F₀ bh bx) (hK.mono (by decide)) m₂ (lay I F₀).fe
    (I.t * I.k) bh (2 * (I.t * I.k)) (I.t * I.k) 2 (lay I F₀).pZn 2 (lay I F₀).pL B (Hflat I)
    (flat Xs) hz₂ (fun c hc => hc.glob.free) (by omega)
    (fun m hm i hi => by
      have hlt := succ_mul_le (2 * (I.t * I.k)) hi
      exact sarr_of_out (sarr_of_out (sarr_of_out (hH i hi) (le_refl 2) ho₁ (Or.inl (by omega)))
        (le_refl 2) ho₂ (Or.inl (by omega))) (le_refl 2) (out_of_sameOn hm) (Or.inl (by omega)))
    (fun m hm => sarr_of_out hxs (le_refl 2) (out_of_sameOn hm) (Or.inl (by omega))) hB
    (by omega) (fun i hi j hj => addr_lt_rows (by omega)
      (show bh + I.t * I.k * (2 * (I.t * I.k)) ≤ S by omega) hi hj)
    (fun j hj => addr_lt_of_stride (le_refl 2) (show (lay I F₀).pZn + I.t * I.k * 2 ≤ S by omega)
      hj)
  refine ((HTB.of_HT rfl (kAlloc_spec I F₀ bh bx m₀)).seq (b1.seq ((b2.seq b3).seq (b4.seq b5)))).mono
    (fun c h => h) (fun c ⟨⟨hc, _, hm, _⟩, hv⟩ => ⟨hc, ?_⟩) (le_of_eq (by ring))
  rw [hv, Nat.sub_zero] at hm
  have ho₃ : Out (lay I F₀).pL ((lay I F₀).pL + I.t * I.k * 2) m₂ c.mem :=
    hm ▸ out_wrArr (le_refl 2) le_rfl le_rfl
  have ho : Out F₀ (lay I F₀).fe m₀ c.mem :=
    ((ho₁.mono (by omega) (by omega)).trans (ho₂.mono (by omega) (by omega))).trans
      (ho₃.mono (by omega) (by omega))
  refine ⟨fun i hi => sarr_of_out (hH i hi) (le_refl 2) ho (Or.inl (by
      have := succ_mul_le (2 * (I.t * I.k)) hi; omega)),
    ?_, sarr_of_out hxs (le_refl 2) ho₃ (Or.inl (by omega)), ?_, fun a ha1 ha2 => ?_,
    fun a ha1 ha2 => ?_, ho₃.zeroFrom hz₂ (by omega)⟩
  · have h1 := smem_sw m₀ (lay I F₀).pOne 1
    exact ⟨(ho₃ _ (Or.inr (by omega))).trans ((ho₂ _ (Or.inr (by omega))).trans h1.1),
      (ho₃ _ (Or.inr (by omega))).trans ((ho₂ _ (Or.inr (by omega))).trans h1.2)⟩
  · rw [hm]; exact sarr_wrArr (le_refl 2) _
  · rw [ho₃ a (Or.inl (by omega)), ho₂ a (Or.inl (by omega)), ho₁ a (Or.inl (by omega))]
    exact hZ a ha1
  · rw [ho₃ a (Or.inl (by omega)), ho₂ a (Or.inr (by omega)), ho₁ a (Or.inl (by omega))]
    exact hZ a (by omega)

end STACS2027.Runtimes.QPRam.Kmo
