module

public import Runtimes.ConvexQP.RAM.KmoSpec
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: a step of Phase M, part A (`col`, `u`, `w`, `ω`, `G Zn`, `σ`)

From the state `s` after `r` steps (`MemCore`, `w` zero from `r` on):
1. `colBlk`: `col := (G_{T_a, r})_a` (`gather`, offset `2r`);
2. `uBlk`: `u := Aj col` (`mvCore`);
3. `wBlk`: `w[0, r) := −u` (`cpLoop`), `w_r := Δ`;
4. `omBlk`: `ω := G w` (`mvCore`, `d` columns);
5. `gzBlk`: `G Zn` into the `σ` region (`mvCore`);
6. `sgBlk`: `σ := (−E)·(G Zn) + q·h'` in place (`linCore false`, `γ = 1`).
The memory predicates `MemA0 … MemA6` record what holds after each block.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-- The scratch registers of a step: `rT`, the library's `400–449`, and `528–539`. -/
def scrW : List ℕ := rT :: (List.range' 400 50 ++ List.range' 528 12)

theorem mvW_sub : ∀ r ∈ mvW, r ∈ scrW := by decide
theorem linW_sub : ∀ r ∈ linW, r ∈ scrW := by decide
theorem r1W_sub : ∀ r ∈ r1W, r ∈ scrW := by decide
theorem axW_sub : ∀ r ∈ axW, r ∈ scrW := by decide
theorem cpW_sub : ∀ r ∈ cpW, r ∈ scrW := by decide
theorem gaW_sub : ∀ r ∈ gaW, r ∈ scrW := by decide
theorem scrW_glob : ∀ r ∈ scrW, r ∈ globFree := by decide

variable {S : ℕ}

section StepA

variable (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ : ℕ) {r : ℕ} (s : MState (MM I) (dd I) r)

/-- The registers during step `r` from the state `s`. -/
def RA (c : Config) : Prop :=
  Glob I F₀ c ∧ StRegs I F₀ s c ∧ c.reg kR = r ∧ c.reg kOFF = 2 * r

theorem RA_regIndep : RegIndep scrW (RA I F₀ s) :=
  (Glob.regIndep' I F₀ scrW_glob).and (by indep [StRegs, SReg])

/-! ### The memory after each block -/

/-- At the start of the step. -/
def MemA0 (m : ℕ → ℕ) : Prop := MemCore I Xs F₀ s m ∧ WZero I F₀ r m

/-- After `colBlk`. -/
def MemA1 (m : ℕ → ℕ) : Prop :=
  MemA0 I Xs F₀ s m ∧ SArr m (lay I F₀).pcol 2 r (colf I Xs s)

/-- After `uBlk`. -/
def MemA2 (m : ℕ → ℕ) : Prop := MemA1 I Xs F₀ s m ∧ SArr m (lay I F₀).pu 2 r (uf I Xs s)

/-- After `wBlk`. -/
def MemA3 (m : ℕ → ℕ) : Prop :=
  MemCore I Xs F₀ s m ∧ SArr m (lay I F₀).pu 2 r (uf I Xs s) ∧
    SArr m (lay I F₀).pw 2 (dd I) (wf I Xs s)

/-- After `omBlk`. -/
def MemA4 (m : ℕ → ℕ) : Prop := MemA3 I Xs F₀ s m ∧ SArr m (lay I F₀).pom 2 (MM I) (omf I Xs s)

/-- After `gzBlk`. -/
def MemA5 (m : ℕ → ℕ) : Prop := MemA4 I Xs F₀ s m ∧ SArr m (lay I F₀).psg 2 (MM I) (gzf I Xs s)

/-- After `sgBlk`. -/
def MemA6 (m : ℕ → ℕ) : Prop := MemA4 I Xs F₀ s m ∧ SArr m (lay I F₀).psg 2 (MM I) (sgf I Xs s)

variable {I Xs F₀ s}

/-- `MemCore` survives writes into the scratch regions `[pcol, php)`. -/
theorem MemCore.of_out (hr : r ≤ dd I) {m m' : ℕ → ℕ} (h : MemCore I Xs F₀ s m)
    (ho : Out (lay I F₀).pcol (lay I F₀).php m m') : MemCore I Xs F₀ s m' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine ⟨fun i hi => sarr_of_out (h.gmem i hi) (le_refl 2) ho (Or.inl ?_), sarr_of_out h.hp
    (le_refl 2) ho (Or.inr le_rfl), sarr_of_out h.zn (le_refl 2) ho (Or.inl (by omega)),
    fun a ha => (ho _ (Or.inr (by omega))).trans (h.tt a ha),
    fun a ha => sarr_of_out (h.aj a ha) (le_refl 2) ho (Or.inl ?_), ho.zeroFrom h.zero (by omega)⟩
  · have := succ_mul_le (gsz I) hi
    omega
  · have := succ_mul_le (asz I) (show a < dd I by omega)
    have : r * 2 ≤ asz I := by omega
    omega

/-! ### Block 1: `col` -/

/-- Inputs of the gather of `col`. -/
def colSet : Stmt := .seq (mov kN kR) (.seq (mov kPS kPT) (.seq (mov kSS kOFF) (mov kPD kPCOL)))

/-- `col := (G_{T_a, r})_a`. -/
def colBlk : Stmt := .seq colSet gather

theorem colBlk_spec (hr : r + 1 ≤ dd I) {R : Config → Prop} (hR : RegIndep scrW R)
    (hRA : ∀ c, R c → RA I F₀ s c) (hS : (lay I F₀).fe ≤ S) :
    HTB S colBlk (fun c => R c ∧ MemA0 I Xs F₀ s c.mem)
      (fun c => R c ∧ MemA1 I Xs F₀ s c.mem) (r * 17 + 11) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hA⟩ => ?_
  have h1 : HTB S colSet (fun c => c = c₀) (fun c => R c ∧ c.mem = c₀.mem ∧ c.reg kN = r ∧
      c.reg kPS = (lay I F₀).pT ∧ c.reg kSS = 2 * r ∧ c.reg kPD = (lay I F₀).pcol) 8 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      obtain ⟨hg, _, hr', hoff⟩ := hRA c hc₀
      refine ⟨(hR.mono (by decide)).run (by decide) hc₀, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [colSet, run_seq', run_mov, setReg_reg, setReg_mem, ↓reduceIte, hr',
        hoff, hg.pT, hg.pcol]
  have h2 := gather_spec (S := S) (R := R) (hR.mono gaW_sub) c₀.mem r (lay I F₀).pT (2 * r)
    (lay I F₀).pcol (fun a => (lay I F₀).pG + TF s a * gsz I) (colf I Xs s) (fun m hm a ha => by
      have ho := out_of_sameOn hm
      refine ⟨(ho _ (Or.inr (by omega))).trans (hA.1.tt a ha), ?_⟩
      have hT := TF_lt s ha
      have hS := hA.1.gmem (TF s a) hT r (by omega)
      have := succ_mul_le (gsz I) hT
      rw [show (lay I F₀).pG + TF s a * gsz I + 2 * r = (lay I F₀).pG + TF s a * gsz I + r * 2 by
        ring]
      exact ⟨(ho _ (Or.inl (by omega))).trans hS.1, (ho _ (Or.inl (by omega))).trans hS.2⟩)
    (by omega) (fun a ha => by
      have hT := TF_lt s ha
      have := succ_mul_le (gsz I) hT
      omega) (by omega)
  refine (h1.seq h2).mono (fun c h => h) (fun c ⟨hc, hm⟩ => ⟨hc, ⟨?_, ?_⟩, ?_⟩) (by omega)
  · exact hA.1.of_out (by omega) (hm ▸ out_wrArr (le_refl 2) le_rfl (by omega))
  · intro a ha1 ha2
    rw [hm, wrArr_of_out (le_refl 2) (by omega)]
    exact hA.2 a ha1 ha2
  · rw [hm]; exact sarr_wrArr (le_refl 2) r

/-! ### Block 2: `u = Aj col` -/

/-- Inputs of `mvCore` for `u = Aj col`. -/
def uSet : Stmt :=
  .seq (mov vR kR) (.seq (mov vRow kPAJ) (.seq (mov vSI kAS) (.seq (mov vN kR)
    (.seq (.const vSA 2) (.seq (mov vX0 kPCOL) (.seq (.const vSX 2) (mov vPU kPU)))))))

/-- `u := Aj col`. -/
def uBlk : Stmt := .seq uSet mvCore

theorem uBlk_spec (hr : r + 1 ≤ dd I) {R : Config → Prop} (hR : RegIndep scrW R)
    (hRA : ∀ c, R c → RA I F₀ s c) (B : ℕ) (hB : ∀ j < r, Nat.size (colf I Xs s j).natAbs ≤ B)
    (hS : (lay I F₀).fe + 16 * B + 6 ≤ S) :
    HTB S uBlk (fun c => R c ∧ MemA1 I Xs F₀ s c.mem)
      (fun c => R c ∧ MemA2 I Xs F₀ s c.mem) (r * (r * (31 * B + 87) + 19) + 15) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hA⟩ => ?_
  have h1 : HTB S uSet (fun c => c = c₀) (fun c => R c ∧ c.mem = c₀.mem ∧ c.reg vR = r ∧
      c.reg vRow = (lay I F₀).pAj ∧ c.reg vSI = asz I ∧ c.reg vN = r ∧ c.reg vSA = 2 ∧
      c.reg vX0 = (lay I F₀).pcol ∧ c.reg vSX = 2 ∧ c.reg vPU = (lay I F₀).pu) 14 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      obtain ⟨hg, _, hr', _⟩ := hRA c hc₀
      refine ⟨(hR.mono (by decide)).run (by decide) hc₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [uSet, run_seq', run_mov, run_const, setReg_reg, setReg_mem, ↓reduceIte,
        hr', hg.pAj, hg.as, hg.pcol, hg.pu]
  have hra : (lay I F₀).pAj + r * asz I ≤ S := by
    have := Nat.mul_le_mul_right (asz I) (show r ≤ dd I by omega)
    omega
  have h2 := mvCore_specB (S := S) (R := R) ((hR.mono mvW_sub)) c₀.mem (lay I F₀).fe r (lay I F₀).pAj
    (asz I) r 2 (lay I F₀).pcol 2 (lay I F₀).pu B (AjF s) (colf I Xs s) hA.1.1.zero
    (fun c hc => (hRA c hc).1.free) (by omega)
    (fun m hm i hi => sarr_of_out (hA.1.1.aj i hi) (le_refl 2) (out_of_sameOn hm) (Or.inl (by
      have := succ_mul_le (asz I) (show i < dd I by omega)
      omega)))
    (fun m hm => sarr_of_out hA.2 (le_refl 2) (out_of_sameOn hm) (Or.inl (by omega))) hB
    (by omega) (fun i hi j hj => addr_lt_rows (by omega) hra hi hj)
    (fun j hj => addr_lt_of_stride (le_refl 2) (show (lay I F₀).pcol + r * 2 ≤ S by omega) hj)
  refine (h1.seq h2).mono (fun c h => h) (fun c ⟨⟨hc, _, hm, _⟩, hv⟩ => ⟨hc, ?_⟩) (by omega)
  rw [hv, Nat.sub_zero] at hm
  have ho : Out (lay I F₀).pu ((lay I F₀).pu + r * 2) c₀.mem c.mem :=
    hm ▸ out_wrArr (le_refl 2) le_rfl le_rfl
  refine ⟨⟨⟨hA.1.1.of_out (by omega) (ho.mono (by omega) (by omega)), fun a ha1 ha2 => ?_⟩,
    sarr_of_out hA.2 (le_refl 2) ho (Or.inl (by omega))⟩, ?_⟩
  · rw [ho a (Or.inr (by omega))]; exact hA.1.2 a ha1 ha2
  · rw [hm]; exact sarr_wrArr (le_refl 2) r

/-! ### Block 3: `w` -/

/-- Inputs of `cpLoop` for `w[0, r) := −u`. -/
def wSet : Stmt :=
  .seq (mov kN kR) (.seq (mov kPS kPU) (.seq (.const kSS 2) (.seq (mov kPD kPW)
    (.seq (.const kSD 2) (.const kNG 1)))))

/-- `w_r := Δ`. -/
def wLast : Stmt := .seq (.add kA kPW kOFF) (sstore kA kDL)

/-- `w := (−u, Δ, 0, …)`. -/
def wBlk : Stmt := .seq wSet (.seq cpLoop wLast)

theorem wBlk_spec (hr : r + 1 ≤ dd I) {R : Config → Prop} (hR : RegIndep scrW R)
    (hRA : ∀ c, R c → RA I F₀ s c) (hS : (lay I F₀).fe ≤ S) :
    HTB S wBlk (fun c => R c ∧ MemA2 I Xs F₀ s c.mem)
      (fun c => R c ∧ MemA3 I Xs F₀ s c.mem) (r * 27 + 17) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hA⟩ => ?_
  have h1 : HTB S wSet (fun c => c = c₀) (fun c => R c ∧ c.mem = c₀.mem ∧ c.reg kN = r ∧
      c.reg kPS = (lay I F₀).pu ∧ c.reg kSS = 2 ∧ c.reg kPD = (lay I F₀).pw ∧ c.reg kSD = 2 ∧
      c.reg kNG = 1) 9 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      obtain ⟨hg, _, hr', _⟩ := hRA c hc₀
      refine ⟨(hR.mono (by decide)).run (by decide) hc₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [wSet, run_seq', run_mov, run_const, setReg_reg, setReg_mem, ↓reduceIte,
        hr', hg.pu, hg.pw]
  have h2 := cpLoop_spec (S := S) (R := R) (hR.mono cpW_sub) c₀.mem r (lay I F₀).pu 2 (lay I F₀).pw 2 1
    (uf I Xs s) (le_refl 2) (fun m hm j hj => by
      have := sarr_of_out hA.2 (le_refl 2) (out_of_sameOn hm) (Or.inl (by omega)) j hj
      exact this)
    (fun j hj => addr_lt_of_stride (le_refl 2) (show (lay I F₀).pu + r * 2 ≤ S by omega) hj)
    (by omega)
  set m₃ := wrArr c₀.mem (lay I F₀).pw 2 (fun j => sgnMul 1 (uf I Xs s j)) r with hm₃
  have h3 : HTB S wLast (fun c => R c ∧ c.mem = m₃)
      (fun c => R c ∧ c.mem = sw m₃ ((lay I F₀).pw + 2 * r) s.Δ) 5 :=
    HTB.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      obtain ⟨hg, ⟨⟨hΔ0, hΔ1⟩, _⟩, _, hoff⟩ := hRA c hc
      refine ⟨by addr_ok [wLast, sstore, hg.pw, hoff], (hR.mono (by decide)).run (by decide) hc, ?_⟩
      simp +decide only [wLast, sstore, run_seq', run_add, run_addc, run_store, setReg_reg,
        setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hg.pw, hoff, hm, hΔ0, hΔ1]
      rfl
  refine (h1.seq (h2.seq h3)).mono (fun c h => h) (fun c ⟨hc, hm⟩ => ⟨hc, ?_⟩) (by omega)
  have ho3 : Out (lay I F₀).pw ((lay I F₀).pw + r * 2) c₀.mem m₃ :=
    out_wrArr (le_refl 2) le_rfl le_rfl
  have ho4 : Out ((lay I F₀).pw + 2 * r) ((lay I F₀).pw + 2 * r + 2) m₃
      (sw m₃ ((lay I F₀).pw + 2 * r) s.Δ) := out_sw le_rfl le_rfl
  have ho : Out (lay I F₀).pw ((lay I F₀).pw + 2 * r + 2) c₀.mem c.mem :=
    hm ▸ (ho3.mono le_rfl (by omega)).trans (ho4.mono (by omega) le_rfl)
  refine ⟨hA.1.1.1.of_out (by omega) (ho.mono (by omega) (by omega)),
    sarr_of_out hA.2 (le_refl 2) ho (Or.inl (by omega)), fun b hb => ?_⟩
  rw [hm]
  rcases Nat.lt_trichotomy b r with hbr | rfl | hbr
  · have hw := sarr_wrArr (m₀ := c₀.mem) (b := (lay I F₀).pw) (le_refl 2)
      (f := fun j => sgnMul 1 (uf I Xs s j)) r b hbr
    have e : wf I Xs s b = sgnMul 1 (uf I Xs s b) := by simp [wf, hbr, sgnMul]
    rw [e]
    exact ⟨(sw_of_out _ (by omega)).trans hw.1, (sw_of_out _ (by omega)).trans hw.2⟩
  · have e : wf I Xs s b = s.Δ := by simp [wf]
    rw [e, show (lay I F₀).pw + b * 2 = (lay I F₀).pw + 2 * b by ring]
    exact smem_sw _ _ _
  · have e : wf I Xs s b = 0 := by simp [wf, show ¬ b < r by omega, show b ≠ r by omega]
    rw [e]
    refine smem_zero ?_ ?_
    · rw [sw_of_out _ (by omega), ho3 _ (Or.inr (by omega))]
      exact hA.1.1.2 _ (by omega) (by omega)
    · rw [sw_of_out _ (by omega), ho3 _ (Or.inr (by omega))]
      exact hA.1.1.2 _ (by omega) (by omega)

/-! ### Blocks 4 and 5: `ω = G w` and `G Zn` -/

/-- The rows of `G` (first `d` entries) are readable away from `[pcol, php)`. -/
theorem gRows_read {m₀ : ℕ → ℕ} (hC : MemCore I Xs F₀ s m₀) {x y : ℕ}
    (hx : (lay I F₀).pcol ≤ x) (m : ℕ → ℕ) (ho : Out x y m₀ m) :
    ∀ i < MM I, SArr m ((lay I F₀).pG + i * gsz I) 2 (dd I) (Gx I Xs i) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  intro i hi
  refine sarr_mono (sarr_of_out (hC.gmem i hi) (le_refl 2) ho (Or.inl ?_)) (Nat.le_succ _)
  have := succ_mul_le (gsz I) hi
  omega

/-- Inputs of `mvCore` for `G x` (`x` at `px`, result at `pu`). -/
def gSet (px pu : ℕ) : Stmt :=
  .seq (mov vR qM) (.seq (mov vRow kPG) (.seq (mov vSI kGS) (.seq (mov vN qD)
    (.seq (.const vSA 2) (.seq (mov vX0 px) (.seq (.const vSX 2) (mov vPU pu)))))))

/-- `ω := G w`. -/
def omBlk : Stmt := .seq (gSet kPW kPOM) mvCore

/-- `G Zn` into the `σ` region. -/
def gzBlk : Stmt := .seq (gSet kPZN kPSG) mvCore

theorem omBlk_spec (hr : r + 1 ≤ dd I) {R : Config → Prop} (hR : RegIndep scrW R)
    (hRA : ∀ c, R c → RA I F₀ s c) (B : ℕ)
    (hB : ∀ j < dd I, Nat.size (wf I Xs s j).natAbs ≤ B) (hS : (lay I F₀).fe + 16 * B + 6 ≤ S) :
    HTB S omBlk (fun c => R c ∧ MemA3 I Xs F₀ s c.mem)
      (fun c => R c ∧ MemA4 I Xs F₀ s c.mem) (MM I * (dd I * (31 * B + 87) + 19) + 15) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hA⟩ => ?_
  have h1 : HTB S (gSet kPW kPOM) (fun c => c = c₀) (fun c => R c ∧ c.mem = c₀.mem ∧
      c.reg vR = MM I ∧ c.reg vRow = (lay I F₀).pG ∧ c.reg vSI = gsz I ∧ c.reg vN = dd I ∧
      c.reg vSA = 2 ∧ c.reg vX0 = (lay I F₀).pw ∧ c.reg vSX = 2 ∧ c.reg vPU = (lay I F₀).pom) 14 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      obtain ⟨hg, _, _, _⟩ := hRA c hc₀
      have hq := hg.qregs
      rw [qregs_iff] at hq
      refine ⟨(hR.mono (by decide)).run (by decide) hc₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [gSet, run_seq', run_mov, run_const, setReg_reg, setReg_mem, ↓reduceIte,
        hg.pG, hg.gs, hg.pw, hg.pom, hq.2.2.2.2.1, hq.2.2.2.2.2.1]
  have h2 := mvCore_specB (S := S) (R := R) ((hR.mono mvW_sub)) c₀.mem (lay I F₀).fe (MM I) (lay I F₀).pG
    (gsz I) (dd I) 2 (lay I F₀).pw 2 (lay I F₀).pom B (Gx I Xs) (wf I Xs s) hA.1.zero
    (fun c hc => (hRA c hc).1.free) (by omega)
    (fun m hm => gRows_read hA.1 (by omega) m (out_of_sameOn hm))
    (fun m hm => sarr_of_out hA.2.2 (le_refl 2) (out_of_sameOn hm) (Or.inl (by omega))) hB
    (by omega) (fun i hi j hj => addr_lt_rows (by omega) (show (lay I F₀).pG + MM I * gsz I ≤ S by
      omega) hi hj)
    (fun j hj => addr_lt_of_stride (le_refl 2) (show (lay I F₀).pw + dd I * 2 ≤ S by omega) hj)
  refine (h1.seq h2).mono (fun c h => h) (fun c ⟨⟨hc, _, hm, _⟩, hv⟩ => ⟨hc, ?_⟩) (by omega)
  rw [hv, Nat.sub_zero] at hm
  have ho : Out (lay I F₀).pom ((lay I F₀).pom + MM I * 2) c₀.mem c.mem :=
    hm ▸ out_wrArr (le_refl 2) le_rfl le_rfl
  refine ⟨⟨hA.1.of_out (by omega) (ho.mono (by omega) (by omega)),
    sarr_of_out hA.2.1 (le_refl 2) ho (Or.inl (by omega)),
    sarr_of_out hA.2.2 (le_refl 2) ho (Or.inl (by omega))⟩, ?_⟩
  rw [hm]; exact sarr_wrArr (le_refl 2) _

theorem gzBlk_spec (hr : r + 1 ≤ dd I) {R : Config → Prop} (hR : RegIndep scrW R)
    (hRA : ∀ c, R c → RA I F₀ s c) (B : ℕ)
    (hB : ∀ j < dd I, Nat.size (ZnF s j).natAbs ≤ B) (hS : (lay I F₀).fe + 16 * B + 6 ≤ S) :
    HTB S gzBlk (fun c => R c ∧ MemA4 I Xs F₀ s c.mem)
      (fun c => R c ∧ MemA5 I Xs F₀ s c.mem) (MM I * (dd I * (31 * B + 87) + 19) + 15) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hA⟩ => ?_
  have h1 : HTB S (gSet kPZN kPSG) (fun c => c = c₀) (fun c => R c ∧ c.mem = c₀.mem ∧
      c.reg vR = MM I ∧ c.reg vRow = (lay I F₀).pG ∧ c.reg vSI = gsz I ∧ c.reg vN = dd I ∧
      c.reg vSA = 2 ∧ c.reg vX0 = (lay I F₀).pZn ∧ c.reg vSX = 2 ∧
      c.reg vPU = (lay I F₀).psg) 14 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      obtain ⟨hg, _, _, _⟩ := hRA c hc₀
      have hq := hg.qregs
      rw [qregs_iff] at hq
      refine ⟨(hR.mono (by decide)).run (by decide) hc₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [gSet, run_seq', run_mov, run_const, setReg_reg, setReg_mem, ↓reduceIte,
        hg.pG, hg.gs, hg.pZn, hg.psg, hq.2.2.2.2.1, hq.2.2.2.2.2.1]
  have h2 := mvCore_specB (S := S) (R := R) ((hR.mono mvW_sub)) c₀.mem (lay I F₀).fe (MM I) (lay I F₀).pG
    (gsz I) (dd I) 2 (lay I F₀).pZn 2 (lay I F₀).psg B (Gx I Xs) (ZnF s) hA.1.1.zero
    (fun c hc => (hRA c hc).1.free) (by omega)
    (fun m hm => gRows_read hA.1.1 (by omega) m (out_of_sameOn hm))
    (fun m hm => sarr_of_out hA.1.1.zn (le_refl 2) (out_of_sameOn hm) (Or.inl (by omega))) hB
    (by omega) (fun i hi j hj => addr_lt_rows (by omega) (show (lay I F₀).pG + MM I * gsz I ≤ S by
      omega) hi hj)
    (fun j hj => addr_lt_of_stride (le_refl 2) (show (lay I F₀).pZn + dd I * 2 ≤ S by omega) hj)
  refine (h1.seq h2).mono (fun c h => h) (fun c ⟨⟨hc, _, hm, _⟩, hv⟩ => ⟨hc, ?_⟩) (by omega)
  rw [hv, Nat.sub_zero] at hm
  have ho : Out (lay I F₀).psg ((lay I F₀).psg + MM I * 2) c₀.mem c.mem :=
    hm ▸ out_wrArr (le_refl 2) le_rfl le_rfl
  refine ⟨⟨⟨hA.1.1.of_out (by omega) (ho.mono (by omega) (by omega)),
    sarr_of_out hA.1.2.1 (le_refl 2) ho (Or.inl (by omega)),
    sarr_of_out hA.1.2.2 (le_refl 2) ho (Or.inl (by omega))⟩,
    sarr_of_out hA.2 (le_refl 2) ho (Or.inl (by omega))⟩, ?_⟩
  rw [hm]; exact sarr_wrArr (le_refl 2) _

/-! ### Block 6: `σ` -/

/-- Inputs of `linCore false` for `σ := (−E)·(G Zn) + q·h'`. -/
def sgSet : Stmt :=
  .seq (mov vN qM) (.seq (mov vPA kPSG) (.seq (mov vPX kPHP) (.seq (.const vAl 1)
    (.seq (mov (vAl + 1) (kE + 1)) (.seq (smov vBe kQ) (sconst vGa 1))))))

/-- `σ := (−E)·(G Zn) + q·h'` in place. -/
def sgBlk : Stmt := .seq sgSet (linCore false)

theorem sgBlk_spec (hr : r + 1 ≤ dd I) {R : Config → Prop} (hR : RegIndep scrW R)
    (hRA : ∀ c, R c → RA I F₀ s c) (B : ℕ)
    (hEp : 0 < bigE I.t I.k) (hE : Nat.size (bigE I.t I.k) ≤ B) (hq : Nat.size s.q ≤ B)
    (hz : ∀ j < MM I, Nat.size (gzf I Xs s j).natAbs ≤ B)
    (hw : ∀ j < MM I, Nat.size (hpf I j).natAbs ≤ B) (hS : (lay I F₀).fe + 16 * B + 6 ≤ S) :
    HTB S sgBlk (fun c => R c ∧ MemA5 I Xs F₀ s c.mem)
      (fun c => R c ∧ MemA6 I Xs F₀ s c.mem) (MM I * (124 * B + 286) + 18) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hA⟩ => ?_
  have h1 : HTB S sgSet (fun c => c = c₀) (fun c => R c ∧ c.mem = c₀.mem ∧ c.reg vN = MM I ∧
      c.reg vPA = (lay I F₀).psg ∧ c.reg vPX = (lay I F₀).php ∧
      SReg c vAl (-(bigE I.t I.k : ℤ)) ∧ SReg c vBe (s.q : ℤ) ∧ SReg c vGa 1) 15 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      obtain ⟨hg, ⟨_, ⟨hq0, hq1⟩, _⟩, _, _⟩ := hRA c hc₀
      obtain ⟨he0, he1⟩ := hg.e
      have hqr := hg.qregs
      rw [qregs_iff] at hqr
      refine ⟨(hR.mono (by decide)).run (by decide) hc₀, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩⟩ <;>
      simp +decide only [sgSet, smov, sconst, run_seq', run_mov, run_const, setReg_reg, setReg_mem,
        ↓reduceIte, hg.psg, hg.php, hqr.2.2.2.2.2.1, he1, hq0, hq1]
      all_goals first | rfl | simp [sgnBit, hEp]
  have h2 := linCore_specB false (S := S) (R := R) (hR.mono linW_sub) c₀.mem (lay I F₀).fe (MM I)
    (lay I F₀).psg (lay I F₀).php B (-(bigE I.t I.k : ℤ)) (s.q : ℤ) 1 (gzf I Xs s) (hpf I)
    hA.1.1.1.zero (fun c hc => (hRA c hc).1.free) (by omega) hA.2
    (fun m hm => sarr_of_out hA.1.1.1.hp (le_refl 2) (out_of_sameOn hm) (Or.inr (by omega)))
    (by simp [GoodDiv]) (by simpa using hE) (by simpa using hq) hz hw (by omega) (by omega)
  refine (h1.seq h2).mono (fun c h => h) (fun c ⟨hc, _, _, _, _, _, _, hm⟩ => ⟨hc, ?_⟩)
    (by omega)
  have ho : Out (lay I F₀).psg ((lay I F₀).psg + MM I * 2) c₀.mem c.mem :=
    hm ▸ out_wrArr (le_refl 2) le_rfl le_rfl
  refine ⟨⟨⟨hA.1.1.1.of_out (by omega) (ho.mono (by omega) (by omega)),
    sarr_of_out hA.1.1.2.1 (le_refl 2) ho (Or.inl (by omega)),
    sarr_of_out hA.1.1.2.2 (le_refl 2) ho (Or.inl (by omega))⟩,
    sarr_of_out hA.1.2 (le_refl 2) ho (Or.inl (by omega))⟩, ?_⟩
  rw [hm]; exact sarr_wrArr (le_refl 2) _

end StepA

end STACS2027.Runtimes.QPRam.Kmo
