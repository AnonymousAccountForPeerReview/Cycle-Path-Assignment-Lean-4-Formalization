module

public import Runtimes.ConvexQP.RAM.KmoK3
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: Phase K, part 4 (the memory after `π`, the loop over the rows `S`)

* `KM2`: the memory after the `π` loop (`H`, the constant `1`, `Zn = kktZn`, `L`, zero regions);
  `km2_of`: from `KM1` and the writes of `kPi`.
* `sInit`: the registers of the rows `S` (`1`, `−1`, `E + 1`, `1 − E`, the pointers);
  `sBody`: the rows `S_{c,0}`, `S_{c,1}` (`rowSB` twice); `kS = sInit; for c < t: sBody`
  (`kS_spec`: the rows `i < 2t` of `G` and `h'` are written).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### The memory after `π` -/

/-- The memory after the `π` loop. -/
structure KM2 (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ bh : ℕ) (m : ℕ → ℕ) : Prop where
  hmem : HMem I m bh
  one : SMem m (lay I F₀).pOne 1
  zn : SArr m (lay I F₀).pZn 2 (dd I) (ZnF₀ I Xs)
  l : SArr m (lay I F₀).pL 2 (I.t * I.k) (Lf I Xs)
  zg : ZeroOn m F₀ (lay I F₀).pZn
  zr : ZeroOn m ((lay I F₀).pZn + 2 * dd I) (lay I F₀).pL
  zero : ZeroFrom m (lay I F₀).fe

/-- `π_c` as computed is `I.pi Xs c`, the entry `tk + c` of the start point. -/
theorem piV_eq {I : Inst} (Xs : Fin I.t → Fin I.k → ℤ) (hk : 0 < I.k) {c : ℕ} (hc : c < I.t) :
    piV I Xs c = ZnF₀ I Xs (I.t * I.k + c) := by
  rw [ZnF₀_p I Xs hc, piV, minAcc_pi I Xs hk hc]

/-- **The memory after `π`.** -/
theorem km2_of {I : Inst} {Xs : Fin I.t → Fin I.k → ℤ} {F₀ bh : ℕ} (hk : 0 < I.k)
    (hbh : bh + hCells I ≤ F₀) {m : ℕ → ℕ} (h : KM1 I Xs F₀ bh m) :
    KM2 I Xs F₀ bh (wrArr m ((lay I F₀).pZn + 2 * (I.t * I.k)) 2 (piV I Xs) I.t) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  have hC : hCells I = I.t * I.k * (2 * (I.t * I.k)) := rfl
  have ho : Out ((lay I F₀).pZn + 2 * (I.t * I.k)) ((lay I F₀).pZn + 2 * (I.t * I.k) + I.t * 2) m
      (wrArr m ((lay I F₀).pZn + 2 * (I.t * I.k)) 2 (piV I Xs) I.t) :=
    out_wrArr (le_refl 2) le_rfl le_rfl
  refine ⟨fun a ha => sarr_of_out (h.hmem a ha) (le_refl 2) ho (Or.inl (by
      have := succ_mul_le (2 * (I.t * I.k)) ha; omega)), ⟨(ho _ (Or.inr (by omega))).trans h.one.1,
      (ho _ (Or.inr (by omega))).trans h.one.2⟩, fun v hv => ?_,
    sarr_of_out h.l (le_refl 2) ho (Or.inr (by omega)), fun a ha1 ha2 => ?_, fun a ha1 ha2 => ?_,
    ho.zeroFrom h.zero (by omega)⟩
  · by_cases hvx : v < I.t * I.k
    · rw [ZnF₀_x I Xs hvx]
      have := h.xs v hvx
      exact ⟨(ho _ (Or.inl (by omega))).trans this.1, (ho _ (Or.inl (by omega))).trans this.2⟩
    · have hc : v - I.t * I.k < I.t := by omega
      have := sarr_wrArr (m₀ := m) (b := (lay I F₀).pZn + 2 * (I.t * I.k)) (f := piV I Xs)
        (le_refl 2) I.t (v - I.t * I.k) hc
      rw [piV_eq Xs hk hc, show I.t * I.k + (v - I.t * I.k) = v by omega,
        show (lay I F₀).pZn + 2 * (I.t * I.k) + (v - I.t * I.k) * 2 = (lay I F₀).pZn + v * 2 by
          omega] at this
      exact this
  · rw [ho a (Or.inl (by omega))]; exact h.z1 a ha1 ha2
  · rw [ho a (Or.inr (by omega))]; exact h.z2 a (by omega) ha2

/-! ### The rows `S` -/

/-- The pointers of the rows `S`: `kRP := pG`, `kHP := php`, `kJJ := 0`, `kXP := 2k`. -/
def sInitB : Stmt := .seq (mov kRP kPG) (.seq (mov kHP kPHP) (.seq (.const kJJ 0) (.add kXP qK qK)))

/-- The registers of the rows `S`: the pairs `1`, `−1`, `E + 1`, `1 − E`, and `sInitB`. -/
def sInit : Stmt :=
  .seq (sconst kONE 1) (.seq (sconst kMONE (-1)) (.seq (sadd kLP kE kONE) (.seq (ssub kHR kONE kE)
    sInitB)))

/-- One cycle `c`: the rows `S_{c,0}` (`+1`, `h' = E + 1`) and `S_{c,1}` (`−1`, `h' = 1 − E`),
then the fill offset `2k (c + 1)`. -/
def sBody : Stmt := .seq (rowSB 0 kONE kLP) (.seq (rowSB 1 kMONE kHR) (.add kJJ kJJ kXP))

/-- The rows `S` of all cycles. -/
def kS : Stmt := .seq sInit (forUp kC qT sBody)

variable {S : ℕ}

section SLoop

variable (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ bh bx : ℕ)

/-- The state of the loop over the rows `S` before cycle `c`. -/
def SInv (mπ : ℕ → ℕ) (c : ℕ) (cfg : Config) : Prop :=
  SG I F₀ bh bx c (2 * c) cfg ∧ RowsK I Xs F₀ cfg.mem (2 * c) ∧ OutGH I F₀ mπ cfg.mem

theorem SG_regIndep' (c R : ℕ) :
    RegIndep (rT :: kC :: (List.range' 400 50 ++ List.range' 530 10)) (SG I F₀ bh bx c R) :=
  (KGl.regIndep' I F₀ bh bx (by decide)).and (by indep [SReg])

variable {I Xs F₀ bh bx}

theorem sBody_spec {c : ℕ} (hc : c < I.t) (mπ : ℕ → ℕ) (hone : SMem mπ (lay I F₀).pOne 1)
    (hS : (lay I F₀).fe ≤ S) :
    HTB S sBody (fun cfg => SInv I Xs F₀ bh bx mπ c cfg ∧ cfg.reg kC = c ∧ cfg.reg qT = I.t)
      (fun cfg => SInv I Xs F₀ bh bx mπ (c + 1) cfg ∧ cfg.reg kC = c ∧ cfg.reg qT = I.t)
      (I.k * 54 + 47) := by
  have hM : MM I = 2 * I.t + 3 * (I.t * I.k) := nRows_eq I.t I.k
  have r0 := (rowSB_spec (I := I) (Xs := Xs) (F₀ := F₀) (bh := bh) (bx := bx) (c := c)
    (R := 2 * c) (by omega) hc 0 kONE kLP 1 ((bigE I.t I.k : ℤ) + 1) (by simp [sgnMul])
    (by decide) (fun cfg h => h.2.2.2.2.2.2.2.1) (fun cfg h => h.2.2.2.2.2.1)
    (fun v _ => by
      have := Gx_S I Xs hc (show 0 < 2 by norm_num) v
      simpa using this)
    (by
      have := hpf_S I hc (show 0 < 2 by norm_num)
      simpa using this) mπ hone hS).frameReg
    (F := fun cfg => cfg.reg kC = c ∧ cfg.reg qT = I.t) (by indep)
  have r1 := (rowSB_spec (I := I) (Xs := Xs) (F₀ := F₀) (bh := bh) (bx := bx) (c := c)
    (R := 2 * c + 1) (by omega) hc 1 kMONE kHR (-1) (1 - (bigE I.t I.k : ℤ)) (by simp [sgnMul])
    (by decide) (fun cfg h => h.2.2.2.2.2.2.2.2) (fun cfg h => h.2.2.2.2.2.2.1)
    (fun v _ => by
      have := Gx_S I Xs hc (show 1 < 2 by norm_num) v
      simpa using this)
    (by
      have := hpf_S I hc (show 1 < 2 by norm_num)
      simp only [one_ne_zero, ↓reduceIte] at this
      rw [this]; ring) mπ hone hS).frameReg
    (F := fun cfg => cfg.reg kC = c ∧ cfg.reg qT = I.t) (by indep)
  have r2 : HTB S (.add kJJ kJJ kXP)
      (fun cfg => (SG I F₀ bh bx c (2 * c + 1 + 1) cfg ∧ RowsK I Xs F₀ cfg.mem (2 * c + 1 + 1) ∧
        OutGH I F₀ mπ cfg.mem) ∧ cfg.reg kC = c ∧ cfg.reg qT = I.t)
      (fun cfg => SInv I Xs F₀ bh bx mπ (c + 1) cfg ∧ cfg.reg kC = c ∧ cfg.reg qT = I.t) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun cfg ⟨⟨⟨hk, hrp, hhp, hjj, hxp, hlp, hhr, h1, hm1⟩, hR, hO⟩, hC, hT⟩ => by
      refine ⟨⟨⟨(KGl.regIndep' I F₀ bh bx (W := wregs (.add kJJ kJJ kXP)) (by decide)).run
        (by decide) hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
      all_goals first
        | exact (regIndep_sreg (W := wregs (.add kJJ kJJ kXP)) (by decide) (by decide) _).run
            (by decide) (by assumption)
        | skip
      all_goals simp +decide only [run_add, setReg_reg, setReg_mem, ↓reduceIte, hrp, hhp, hjj,
        hxp, hC, hT]
      · ring
      · ring
      · ring
      · rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring]; exact hR
      · exact hO
  refine (r0.seq (r1.seq r2)).weaken (by omega)

/-- The registers and the memory before the rows `S`. -/
theorem sInit_spec (m : ℕ → ℕ) (hm : KM2 I Xs F₀ bh m) :
    HT sInit (fun cfg => KGl I F₀ bh bx cfg ∧ cfg.mem = m)
      (fun cfg => SInv I Xs F₀ bh bx m 0 cfg ∧ cfg.mem = m) 90 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  let P : Config → Prop := fun cfg => KGl I F₀ bh bx cfg ∧ cfg.mem = m
  have hP : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ kW) → Indep W P := fun hW =>
    (KGl.regIndep' I F₀ bh bx hW).indep.and (Indep.mem (· = m))
  have s1 := HT.sconst (P := P) (d := kONE) 1 (hP (by decide))
  have s2 := HT.sconst (P := fun cfg => P cfg ∧ SReg cfg kONE 1) (d := kMONE) (-1)
    ((hP (by decide)).and (indep_sreg (by decide) (by decide) 1))
  have s3 := HT.sadd (P := fun cfg => (P cfg ∧ SReg cfg kONE 1) ∧ SReg cfg kMONE (-1)) (d := kLP)
    (x := kE) (y := kONE) (u := (bigE I.t I.k : ℤ)) (v := 1) (by decide) (by decide) (by decide)
    (((hP (by decide)).and (indep_sreg (by decide) (by decide) 1)).and
      (indep_sreg (by decide) (by decide) (-1)))
  have s4 := HT.ssub (P := fun cfg => ((P cfg ∧ SReg cfg kONE 1) ∧ SReg cfg kMONE (-1)) ∧
      SReg cfg kLP ((bigE I.t I.k : ℤ) + 1)) (d := kHR) (x := kONE) (y := kE) (u := 1)
    (v := (bigE I.t I.k : ℤ)) (by decide) (by decide) (by decide)
    ((((hP (by decide)).and (indep_sreg (by decide) (by decide) 1)).and
      (indep_sreg (by decide) (by decide) (-1))).and (indep_sreg (by decide) (by decide) _))
  have s5 : HT sInitB
      (fun cfg => (((P cfg ∧ SReg cfg kONE 1) ∧ SReg cfg kMONE (-1)) ∧
        SReg cfg kLP ((bigE I.t I.k : ℤ) + 1)) ∧ SReg cfg kHR (1 - (bigE I.t I.k : ℤ)))
      (fun cfg => SInv I Xs F₀ bh bx m 0 cfg ∧ cfg.mem = m) 6 :=
    HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨⟨⟨hk, hmc⟩, ho⟩, hmo⟩, hlp⟩, hhr⟩ => by
      have hq := hk.glob.qregs
      rw [qregs_iff] at hq
      have hW : ∀ r ∈ wregs sInitB, r ∈ kW := by decide
      have e1 : (RAM.run sInitB cfg).reg kRP = (lay I F₀).pG := by
        simp +decide only [sInitB, run_seq', run_mov, run_const, run_add, setReg_reg, ↓reduceIte,
          hk.glob.pG]
      have e2 : (RAM.run sInitB cfg).reg kHP = (lay I F₀).php := by
        simp +decide only [sInitB, run_seq', run_mov, run_const, run_add, setReg_reg, ↓reduceIte,
          hk.glob.php]
      have e3 : (RAM.run sInitB cfg).reg kJJ = 0 := by
        simp +decide only [sInitB, run_seq', run_mov, run_const, run_add, setReg_reg, ↓reduceIte]
      have e4 : (RAM.run sInitB cfg).reg kXP = I.k + I.k := by
        simp +decide only [sInitB, run_seq', run_mov, run_const, run_add, setReg_reg, ↓reduceIte,
          hq.2.1]
      have e5 : (RAM.run sInitB cfg).mem = m := by
        simp +decide only [sInitB, run_seq', run_mov, run_const, run_add, setReg_mem, hmc]
      refine ⟨⟨⟨(KGl.regIndep' I F₀ bh bx hW).run (by decide) hk, by rw [e1]; ring,
        by rw [e2]; ring, by rw [e3]; ring, by rw [e4]; ring,
        (regIndep_sreg (by decide) (by decide) _).run (by decide) hlp,
        (regIndep_sreg (by decide) (by decide) _).run (by decide) hhr,
        (regIndep_sreg (by decide) (by decide) _).run (by decide) ho,
        (regIndep_sreg (by decide) (by decide) _).run (by decide) hmo⟩, ?_, ?_⟩, e5⟩
      · rw [e5]
        refine ⟨fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega),
          fun a ha1 ha2 => hm.zg a (by omega) (by omega),
          fun a ha1 ha2 => hm.zr a (by omega) (by omega)⟩
      · rw [e5]; exact OutGH.refl m
  refine (s1.seq (s2.seq ((s3.pre fun cfg h => ⟨h, h.1.1.1.glob.e, h.1.2⟩).seq
    ((s4.pre fun cfg h => ⟨h, h.1.1.2, h.1.1.1.1.glob.e⟩).seq s5)))).weaken (by omega)
/-- **The rows `S`** of all cycles: the rows `i < 2t` of `G` and `h'`. -/
theorem kS_spec (m : ℕ → ℕ) (hm : KM2 I Xs F₀ bh m) (hS : (lay I F₀).fe ≤ S) :
    HTB S kS (fun cfg => KGl I F₀ bh bx cfg ∧ cfg.mem = m)
      (fun cfg => SInv I Xs F₀ bh bx m I.t cfg) (90 + (I.t * (I.k * 54 + 47 + 4) + 3)) := by
  have hl := HTB.forUpC (S := S) (i := kC) (n := qT) (N := I.t) (body := sBody) (SInv I Xs F₀ bh bx m)
    (I.k * 54 + 47) (by decide) (by decide) (by decide)
    (fun c => ((SG_regIndep' I F₀ bh bx c (2 * c)).mono (by decide)).indep.and
      ((Indep.mem (fun m' => RowsK I Xs F₀ m' (2 * c))).and (Indep.mem (OutGH I F₀ m))))
    (fun c hc => sBody_spec hc m hm.one hS)
  have hqt : ∀ cfg, SInv I Xs F₀ bh bx m 0 cfg → cfg.reg qT = I.t := fun cfg h => by
    have hq := h.1.1.glob.qregs
    rw [qregs_iff] at hq
    exact hq.1
  exact ((HTB.of_HT rfl (sInit_spec m hm)).seq (hl.pre fun cfg ⟨h, _⟩ => ⟨h, hqt cfg h⟩)).mono (fun _ h => h)
    (fun cfg ⟨h, _⟩ => h) le_rfl

end SLoop

end STACS2027.Runtimes.QPRam.Kmo
