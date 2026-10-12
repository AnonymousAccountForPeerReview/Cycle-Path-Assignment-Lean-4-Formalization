module

public import Runtimes.ConvexQP.RAM.KmoStepC
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: one step of Phase M

`stepBody` = `off := 2r`; part A (`col`, `u`, `w`, `ω`, `G Zn`, `σ`); the scan; part B (`v`, the
bordered adjugate); part C (`Zn`, `q`, `T`, `Δ`, `rowR`). `step_spec`: from `MInv r` to
`MInv (r + 1)` in `Tstep d M B` steps, where `B` bounds the bit lengths of the step
(`StepBits`). The mathematics (`step_math`): along Phase M every step succeeds (`Bdd` from
`kkt_bdd`, `exists_not_Z`; the invariant from `moveAux_bounds`, `kkt_approx`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {I : Inst} {Xs : Fin I.t → Fin I.k → ℤ} {S : ℕ}

/-- The start of Phase M: `G z̃ ≤ h + 1/E` at `z̃ = Zn₀ / 2^p`. -/
theorem kkt_start (hI : I.Valid) (hX : I.InX (ptOf Xs (2 ^ prec I.t I.k)))
    (hgap : I.gap (ptOf Xs (2 ^ prec I.t I.k)) ≤ eps I.t I.k ^ 2) :
    ∀ i, rowVal (KG I Xs) i (ptZ (kktZn I Xs) (2 ^ prec I.t I.k)) ≤
      kktH I i + 1 / (bigE I.t I.k : ℝ) :=
  kkt_approx (by positivity) hX hgap (eps_pos I.t hI.1).le

/-- **Every step of Phase M succeeds** (and `Δ ≠ 0` before it). -/
theorem step_math (hI : I.Valid) (ht : 0 < I.t) (hX : I.InX (ptOf Xs (2 ^ prec I.t I.k)))
    (hgap : I.gap (ptOf Xs (2 ^ prec I.t I.k)) ≤ eps I.t I.k ^ 2) {r : ℕ} (hr : r + 1 ≤ dd I)
    {s : MState (MM I) (dd I) r}
    (hs : moveAux (KG I Xs) (kktH I) (bigE I.t I.k) (kktZn I Xs) (2 ^ prec I.t I.k) r
      (Nat.le_of_succ_le hr) = some s) :
    s.Δ ≠ 0 ∧ ∃ ib, argMinRatio (mOmega (KG I Xs) hr s)
        (mSigma (KG I Xs) (kktH I) (bigE I.t I.k) s) = some ib ∧
      0 < mOmega (KG I Xs) hr s ib ∧
      moveAux (KG I Xs) (kktH I) (bigE I.t I.k) (kktZn I Xs) (2 ^ prec I.t I.k) (r + 1) hr =
        some (nxt I Xs s hr ib) := by
  have hq : 0 < 2 ^ prec I.t I.k := by positivity
  obtain ⟨hinv, -⟩ := moveAux_bounds (bigE_pos I.t hI.1) (entryBound_pos hI.1)
    (kktG_entry_le hI _) hq (kkt_start hI hX hgap) r _ s hs
  have hb := kkt_bdd (kktZ I Xs) (exists_not_Z hI ht hq hX hgap)
  obtain ⟨ib, hib, hpos, -⟩ := argMinRatio_some _ _ (exists_mOmega_pos hb hr hinv)
  refine ⟨hinv.det_ne, ib, hib, hpos, ?_⟩
  rw [moveAux, hs, Option.bind_some, moveStep, hib, Option.map_some]

/-- The bit lengths of the numbers of the step from `s` are at most `B`. -/
structure StepBits {r : ℕ} (s : MState (MM I) (dd I) r) (B : ℕ) : Prop where
  one : 1 ≤ B
  e : Nat.size (bigE I.t I.k) ≤ B
  q : Nat.size s.q ≤ B
  col : ∀ j < r, Nat.size (colf I Xs s j).natAbs ≤ B
  w : ∀ j < dd I, Nat.size (wf I Xs s j).natAbs ≤ B
  zn : ∀ j < dd I, Nat.size (ZnF s j).natAbs ≤ B
  gz : ∀ i < MM I, Nat.size (gzf I Xs s i).natAbs ≤ B
  hp : ∀ i < MM I, Nat.size (hpf I i).natAbs ≤ B
  om : ∀ i < MM I, Nat.size (omf I Xs s i).natAbs ≤ B
  g : ∀ i < MM I, ∀ j < dd I, Nat.size (Gx I Xs i j).natAbs ≤ B
  aj : ∀ a < r, ∀ b < r, Nat.size (AjF s a b).natAbs ≤ B
  u : ∀ a < r, Nat.size (uf I Xs s a).natAbs ≤ B
  v : ∀ i < MM I, ∀ b < r, Nat.size (vf I Xs s i b).natAbs ≤ B
  sg : ∀ i < MM I, Nat.size (sgf I Xs s i).natAbs ≤ B
  eom : ∀ i < MM I, Nat.size ((bigE I.t I.k : ℤ) * omf I Xs s i).natAbs ≤ B

/-- The bound for one step. -/
def Tstep (d M B : ℕ) : ℕ :=
  1 + (d * 17 + 11) + (d * (d * (31 * B + 87) + 19) + 15) + (d * 27 + 17) +
    2 * (M * (d * (31 * B + 87) + 19) + 15) + (M * (124 * B + 286) + 18) +
    (M * (62 * B + 149) + 10) + (d * (d * (31 * B + 87) + 19) + 15) +
    (d * (d * (248 * B + 286) + 31 * B + 60) + 54 * d + 52) +
    (d * (155 * B + 302) + 31 * B + 80) + (62 * B + 94) + 7

/-- `off := 2r`. -/
def offBlk : Stmt := .add kOFF kR kR

/-- **One step of Phase M** (M1)–(M4). -/
def stepBody : Stmt :=
  .seq offBlk (.seq colBlk (.seq uBlk (.seq wBlk (.seq omBlk (.seq gzBlk (.seq sgBlk
    (.seq scan (.seq vBlk (.seq bordBlk (.seq znBlk (.seq qBlk finBlk)))))))))))

theorem regIndep_stRegs {F₀ r : ℕ} {s : MState (MM I) (dd I) r} :
    RegIndep (wregs offBlk) (StRegs I F₀ s) := by
  indep [StRegs, SReg]

theorem RA_regIndep_scan (I : Inst) (F₀ : ℕ) {r : ℕ} (s : MState (MM I) (dd I) r) :
    RegIndep scanW (RA I F₀ s) :=
  (Glob.regIndep' I F₀ (by decide)).and (by indep [StRegs, SReg])

/-- The new state after a step: `MemCore` and `w` zero from `r + 1` on. -/
theorem memB3_next {F₀ r : ℕ} {s : MState (MM I) (dd I) r} (hr : r + 1 ≤ dd I) (ib : Fin (MM I))
    {m : ℕ → ℕ} (h : MemB3 I Xs F₀ s hr ib m) :
    MemCore I Xs F₀ (nxt I Xs s hr ib) (upd m ((lay I F₀).pT + r) ((lay I F₀).pG + ib * gsz I)) ∧
      WZero I F₀ (r + 1) (upd m ((lay I F₀).pT + r) ((lay I F₀).pG + ib * gsz I)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  have ho : Out ((lay I F₀).pT + r) ((lay I F₀).pT + r + 1) m
      (upd m ((lay I F₀).pT + r) ((lay I F₀).pG + ib * gsz I)) := out_upd le_rfl (by omega)
  refine ⟨⟨fun i hi => sarr_of_out (h.gmem i hi) (le_refl 2) ho (Or.inl (by
      have := succ_mul_le (gsz I) hi; omega)),
    sarr_of_out h.hp (le_refl 2) ho (Or.inl (by omega)),
    sarr_of_out h.zn (le_refl 2) ho (Or.inl (by omega)), fun a ha => ?_,
    fun a ha => sarr_of_out (h.aj a ha) (le_refl 2) ho (Or.inl (by
      have := succ_mul_le (asz I) (show a < dd I by omega)
      have : (r + 1) * 2 ≤ asz I := by omega
      omega)), ho.zeroFrom h.zero (by omega)⟩, fun a ha1 ha2 => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha' | rfl
    · rw [ho _ (Or.inl (by omega)), h.tt a ha', TF_next_lt hr ib ha']
    · simp [TF_next_r hr ib]
  · rw [ho _ (Or.inl (by omega))]
    -- `a` is a cell of an entry `b > r` of `w`, which is `0`
    obtain ⟨b, e, he, hab⟩ : ∃ b e, e < 2 ∧ a = (lay I F₀).pw + b * 2 + e :=
      ⟨(a - (lay I F₀).pw) / 2, (a - (lay I F₀).pw) % 2, Nat.mod_lt _ (by omega), by omega⟩
    have hb : b < dd I := by omega
    have hw := h.w b hb
    have h0 : wf I Xs s b = 0 := by simp [wf, show ¬ b < r by omega, show b ≠ r by omega]
    rw [h0] at hw
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · rw [hab, Nat.add_zero, hw.1]; rfl
    · rw [hab, hw.2]; rfl

/-- **One step of Phase M**: from `MInv r` to `MInv (r + 1)`. -/
theorem step_spec (hI : I.Valid) (ht : 0 < I.t) (hX : I.InX (ptOf Xs (2 ^ prec I.t I.k)))
    (hgap : I.gap (ptOf Xs (2 ^ prec I.t I.k)) ≤ eps I.t I.k ^ 2) (F₀ : ℕ) {r : ℕ}
    (hr : r < dd I) (B : ℕ)
    (hbits : ∀ s : MState (MM I) (dd I) r, moveAux (KG I Xs) (kktH I) (bigE I.t I.k) (kktZn I Xs)
      (2 ^ prec I.t I.k) r hr.le = some s → StepBits (Xs := Xs) s B)
    (hS : (lay I F₀).fe + 16 * B + 6 ≤ S) :
    HTB S stepBody (fun c => MInv I Xs F₀ r c ∧ c.reg kR = r ∧ c.reg qD = dd I)
      (fun c => MInv I Xs F₀ (r + 1) c ∧ c.reg kR = r ∧ c.reg qD = dd I)
      (Tstep (dd I) (MM I) B) := by
  refine HTB.of_forall fun c₀ ⟨⟨hr', s, hs, hg, hst, hC, hW⟩, hR, hD⟩ => ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  have hr1 : r + 1 ≤ dd I := hr
  obtain ⟨hΔ, ib, hib, hpos, hs'⟩ := step_math hI ht hX hgap hr1 hs
  have hb := hbits s hs
  have hEp : 0 < bigE I.t I.k := bigE_pos I.t hI.1
  have hRA := RA_regIndep I F₀ s
  have hRB := RB_regIndep I Xs F₀ s ib
  -- `off := 2r`
  have k0 : HTB S offBlk (fun c => c = c₀) (fun c => RA I F₀ s c ∧ MemA0 I Xs F₀ s c.mem) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) le_rfl fun c hc => by
      subst hc
      refine ⟨⟨(Glob.regIndep' I F₀ (W := wregs offBlk) (by decide)).run (by decide) hg,
        (regIndep_stRegs).run (by decide) hst, ?_, ?_⟩, hC, hW⟩ <;>
      simp +decide only [offBlk, run_add, setReg_reg, ↓reduceIte, hR]
      ring
  have k1 := colBlk_spec (Xs := Xs) hr1 hRA (fun c h => h) (show (lay I F₀).fe ≤ S by omega)
  have k2 := uBlk_spec (Xs := Xs) hr1 hRA (fun c h => h) B hb.col hS
  have k3 := wBlk_spec (Xs := Xs) hr1 hRA (fun c h => h) (show (lay I F₀).fe ≤ S by omega)
  have k4 := omBlk_spec (Xs := Xs) hr1 hRA (fun c h => h) B hb.w hS
  have k5 := gzBlk_spec (Xs := Xs) hr1 hRA (fun c h => h) B hb.zn hS
  have k6 := sgBlk_spec (Xs := Xs) hr1 hRA (fun c h => h) B hEp hb.e hb.q hb.gz hb.hp hS
  -- the scan
  have k7 : HTB S scan (fun c => RA I F₀ s c ∧ MemA6 I Xs F₀ s c.mem)
      (fun c => RB I Xs F₀ s ib c ∧ MemA6 I Xs F₀ s c.mem) (MM I * (62 * B + 149) + 10) := by
    refine HTB.of_forall fun c₁ ⟨hc₁, hA⟩ => ?_
    have hω : ∀ i : Fin (MM I), SMem c₁.mem ((lay I F₀).pom + i * 2)
        (mOmega (KG I Xs) hr1 s i) := fun i => by
      rw [← omf_eq hr1 i.2]; exact hA.1.2 i i.2
    have hσ : ∀ i : Fin (MM I), SMem c₁.mem ((lay I F₀).psg + i * 2)
        (mSigma (KG I Xs) (kktH I) (bigE I.t I.k) s i) := fun i => by
      rw [← sgf_eq i.2]; exact hA.2 i i.2
    refine (scan_spec (S := S) (M := MM I) (R := RA I F₀ s) (m₀ := c₁.mem) (pom := (lay I F₀).pom)
      (psg := (lay I F₀).psg) (pG := (lay I F₀).pG) (gs := gsz I) (RA_regIndep_scan I F₀ s)
      (fun c hc => by rw [hc.1.free]; exact hA.1.1.1.zero)
      (fun c hc => ⟨hc.1.gs, hc.1.pom, hc.1.psg, hc.1.pG, hc.1.qregs.2.2.2.2.2.1⟩) hω hσ B
      (fun j => by rw [← omf_eq hr1 j.2]; exact hb.om j j.2)
      (fun c hc => by rw [hc.1.free]; omega) (by omega) (by omega)).mono
      (fun c h => by subst h; exact ⟨hc₁, rfl⟩) (fun c ⟨hc, hm, ha⟩ => ?_) le_rfl
    rw [hib] at ha
    obtain ⟨_, hbp, hsb, hob⟩ := ha
    refine ⟨⟨hc, hbp, ?_, ?_⟩, hm ▸ hA⟩
    · rw [sgf_eq ib.2]; exact hsb
    · rw [omf_eq hr1 ib.2]; exact hob
  have k8 := vBlk_spec (Xs := Xs) hr1 ib.2 hRB (fun c h => h) B
    (fun j hj => hb.g ib ib.2 j (by omega)) hS
  have k9 := bordBlk_spec (Xs := Xs) hr1 ib hRB (fun c h => h) hΔ B (hb.om ib ib.2) hb.one hb.aj
    hb.u (hb.v ib ib.2) hS
  have k10 := znBlk_spec (Xs := Xs) hr1 ib hRB (fun c h => h) B (hb.eom ib ib.2) (hb.sg ib ib.2)
    hb.one hb.w (hb.om ib ib.2) hS
  have k11 : HTB S (.seq qBlk finBlk) (fun c => RB I Xs F₀ s ib c ∧ MemB3 I Xs F₀ s hr1 ib c.mem)
      (fun c => MInv I Xs F₀ (r + 1) c ∧ c.reg kR = r ∧ c.reg qD = dd I)
      (smulCost (s.q : ℤ) + smulCost (omf I Xs s ib) + 24 + 7) := by
    refine HTB.of_forall fun c₁ ⟨hc₁, hB3⟩ => ?_
    have q1 := qBlk_spec (S := S) I F₀ r s.Δ (sgf I Xs s ib) (omf I Xs s ib) ib s.q c₁.mem
      hB3.zero B hb.q (hb.om ib ib.2) (by omega)
    have q2 := finBlk_spec (S := S) I F₀ r s.Δ (sgf I Xs s ib) (omf I Xs s ib) ib
      ((bigE I.t I.k : ℤ) * s.q * omf I Xs s ib) c₁.mem (by omega)
    refine (q1.seq q2).mono (fun c h => by
        subst h
        obtain ⟨⟨hg1, ⟨hd1, hq1, hrow1⟩, hr1', _⟩, hbp, hsb, hob⟩ := hc₁
        exact ⟨⟨⟨hg1, hr1', hd1, hrow1, hbp, hsb, hob⟩, rfl⟩, hq1⟩)
      (fun c ⟨hg2, hkr, hdl, hq2, hrow2, hm⟩ => ?_) le_rfl
    have hmem := memB3_next hr1 ib hB3
    rw [← hm] at hmem
    refine ⟨⟨hr1, nxt I Xs s hr1 ib, hs', hg2, ⟨?_, ?_, hrow2⟩, hmem.1, hmem.2⟩, hkr,
      hg2.qregs.2.2.2.2.1⟩
    · rw [Δ_next hr1 ib, ← omf_eq hr1 ib.2]; exact hdl
    · rw [q_next hr1 ib hpos, ← omf_eq hr1 ib.2]; exact hq2
  refine (k0.seq (k1.seq (k2.seq (k3.seq (k4.seq (k5.seq (k6.seq (k7.seq (k8.seq (k9.seq
    (k10.seq k11))))))))))).weaken ?_
  have hq := hb.q
  have hω := hb.om ib ib.2
  have hrd : r ≤ dd I := hr.le
  simp only [Tstep, smulCost, gCost]
  have e1 : r * 17 ≤ dd I * 17 := Nat.mul_le_mul_right _ hrd
  have e2 : r * (r * (31 * B + 87) + 19) ≤ dd I * (dd I * (31 * B + 87) + 19) :=
    Nat.mul_le_mul hrd (Nat.add_le_add_right (Nat.mul_le_mul_right _ hrd) _)
  have e3 : r * 27 ≤ dd I * 27 := Nat.mul_le_mul_right _ hrd
  have e4 : r * (r * (248 * B + 286) + 31 * B + 60) ≤
      dd I * (dd I * (248 * B + 286) + 31 * B + 60) :=
    Nat.mul_le_mul hrd (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ hrd) _) _)
  have e5 : 54 * r ≤ 54 * dd I := Nat.mul_le_mul_left _ hrd
  have hq' : Nat.size (s.q : ℤ).natAbs ≤ B := by simpa using hq
  omega

/-! ### Phase M: `d` steps -/

/-- **Phase M**: `d` steps, counted in `kR`. -/
def mLoop : Stmt := forUp kR qD stepBody

theorem MInv_indep (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ r : ℕ) :
    Indep [kR, rT] (MInv I Xs F₀ r) :=
  Indep.exists fun _ => Indep.exists fun s => (Indep.const _).and
    ((Glob.regIndep' I F₀ (by decide)).indep.and
      ((show Indep [kR, rT] (StRegs I F₀ s) by indep [StRegs, SReg]).and
      ((Indep.mem (MemCore I Xs F₀ s)).and (Indep.mem (WZero I F₀ r)))))

/-- **Phase M on the RAM**, from `MInv 0` to `MInv d`. -/
theorem mLoop_spec (hI : I.Valid) (ht : 0 < I.t) (hX : I.InX (ptOf Xs (2 ^ prec I.t I.k)))
    (hgap : I.gap (ptOf Xs (2 ^ prec I.t I.k)) ≤ eps I.t I.k ^ 2) (F₀ B : ℕ)
    (hbits : ∀ r (hr : r < dd I) (s : MState (MM I) (dd I) r), moveAux (KG I Xs) (kktH I)
      (bigE I.t I.k) (kktZn I Xs) (2 ^ prec I.t I.k) r hr.le = some s → StepBits (Xs := Xs) s B)
    (hS : (lay I F₀).fe + 16 * B + 6 ≤ S) :
    HTB S mLoop (fun c => MInv I Xs F₀ 0 c ∧ c.reg qD = dd I)
      (fun c => MInv I Xs F₀ (dd I) c ∧ c.reg kR = dd I ∧ c.reg qD = dd I)
      (dd I * (Tstep (dd I) (MM I) B + 4) + 3) :=
  HTB.forUpC (S := S) (i := kR) (n := qD) (N := dd I) (body := stepBody) (MInv I Xs F₀)
    (Tstep (dd I) (MM I) B) (by decide) (by decide) (by decide) (MInv_indep I Xs F₀)
    (fun j hj => step_spec hI ht hX hgap F₀ hj B (hbits j hj) hS)

end STACS2027.Runtimes.QPRam.Kmo
