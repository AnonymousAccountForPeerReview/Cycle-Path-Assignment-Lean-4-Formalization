module

public import Runtimes.ConvexQP.RAM.KmoStepB
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: a step of Phase M, part C (`Zn`, `q`, `T`, `Δ`)

1. `znBlk`: `Zn := E ω_b Zn + σ_b w` (`smul`, then `axCore false` with `δ = γ = 1`);
2. `qBlk`: `q := E q ω_b` (two `smul`);
3. `finBlk`: `T_r := pG + ib gs`, `Δ := ω_b`, `rowR += 2d`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

section StepC

variable {I : Inst} {Xs : Fin I.t → Fin I.k → ℤ} {F₀ : ℕ} {r : ℕ} {s : MState (MM I) (dd I) r}

variable (I Xs F₀ s) in
/-- After `znBlk`: `Zn` of the new state. -/
structure MemB3 (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) (m : ℕ → ℕ) : Prop where
  gmem : ∀ i < MM I, SArr m ((lay I F₀).pG + i * gsz I) 2 (dd I + 1) (Gx I Xs i)
  hp : SArr m (lay I F₀).php 2 (MM I) (hpf I)
  zn : SArr m (lay I F₀).pZn 2 (dd I) (ZnF (nxt I Xs s hr ib))
  tt : ∀ a < r, m ((lay I F₀).pT + a) = (lay I F₀).pG + TF s a * gsz I
  zero : ZeroFrom m (lay I F₀).fe
  aj : ∀ a < r + 1, SArr m ((lay I F₀).pAj + a * asz I) 2 (r + 1) (AjF (nxt I Xs s hr ib) a)
  w : SArr m (lay I F₀).pw 2 (dd I) (wf I Xs s)

/-! ### Block 1: `Zn` -/

/-- Inputs of `axCore false`: `α = E ω_b` (in `kX`), `β = σ_b`, `γ = δ = 1`. -/
def znSet : Stmt :=
  .seq (mov vN qD) (.seq (mov vPA kPZN) (.seq (mov vPX kPW) (.seq (smov vAl kX)
    (.seq (smov vBe kSB) (.seq (sconst vGa 1) (sconst vDe 1))))))

/-- `Zn := E ω_b Zn + σ_b w`. -/
def znBlk : Stmt := .seq (smul kX kE kOB) (.seq znSet (axCore false))

theorem znBlk_spec (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) {R : Config → Prop}
    (hR : RegIndep scrW R) (hRB : ∀ c, R c → RB I Xs F₀ s ib c) (B : ℕ)
    (hα : Nat.size ((bigE I.t I.k : ℤ) * omf I Xs s ib).natAbs ≤ B)
    (hβ : Nat.size (sgf I Xs s ib).natAbs ≤ B) (h1 : 1 ≤ B)
    (hw : ∀ j < dd I, Nat.size (wf I Xs s j).natAbs ≤ B)
    (hωB : Nat.size (omf I Xs s ib).natAbs ≤ B) (hS : (lay I F₀).fe + 16 * B + 6 ≤ S) :
    HTB S znBlk (fun c => R c ∧ MemB2 I Xs F₀ s hr ib c.mem)
      (fun c => R c ∧ MemB3 I Xs F₀ s hr ib c.mem) (dd I * (155 * B + 302) + 31 * B + 80) := by
  obtain ⟨h0, h1', h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hA⟩ => ?_
  have hF : ∀ c, R c → c.reg rFREE = (lay I F₀).fe := fun c hc => (hRB c hc).1.1.free
  have b1 := HTB.smul (S := S) (P := fun c => R c ∧ c.mem = c₀.mem) (d := kX) (x := kE) (y := kOB)
    (u := (bigE I.t I.k : ℤ)) (v := omf I Xs s ib) (by decide) (by decide) (by decide)
    ((hR.mono (by decide)).indep.and (Indep.mem (· = c₀.mem)))
    (fun c ⟨hc, hm⟩ => by rw [hm, hF c hc]; exact hA.zero)
    (fun c ⟨hc, _⟩ => by rw [hF c hc]; omega)
  have b2 : HTB S znSet (fun c => (R c ∧ c.mem = c₀.mem) ∧
        SReg c kX ((bigE I.t I.k : ℤ) * omf I Xs s ib))
      (fun c => R c ∧ c.mem = c₀.mem ∧ c.reg vN = dd I ∧ c.reg vPA = (lay I F₀).pZn ∧
        c.reg vPX = (lay I F₀).pw ∧ SReg c vAl ((bigE I.t I.k : ℤ) * omf I Xs s ib) ∧
        SReg c vBe (sgf I Xs s ib) ∧ SReg c vGa 1 ∧ SReg c vDe 1) 18 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, hm⟩, ⟨hx0, hx1⟩⟩ => by
      obtain ⟨⟨hg, _, _, _⟩, _, ⟨hs0, hs1⟩, _⟩ := hRB c hc
      have hq := hg.qregs
      rw [qregs_iff] at hq
      refine ⟨(hR.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp +decide only [znSet, smov, sconst, run_seq', run_mov, run_const, setReg_reg, setReg_mem,
        ↓reduceIte, hm, hg.pZn, hg.pw, hq.2.2.2.2.1, hx0, hx1, hs0, hs1]
  have b3 := axCore_specB false (S := S) (R := R) (hR.mono axW_sub) c₀.mem (lay I F₀).fe (dd I)
    (lay I F₀).pZn (lay I F₀).pw B ((bigE I.t I.k : ℤ) * omf I Xs s ib) (sgf I Xs s ib) 1 1
    (ZnF s) (wf I Xs s) hA.zero hF (by omega) hA.zn
    (fun m hm => sarr_of_out hA.w (le_refl 2) (out_of_sameOn hm) (Or.inr (by omega)))
    (by simp [GoodDiv]) hα hβ (by simpa using h1) hw (by omega) (by omega)
  refine (b1.seq (b2.seq b3)).mono
    (fun c h => by subst h; exact ⟨⟨hc₀, rfl⟩, (hRB c hc₀).1.1.e, (hRB c hc₀).2.2.2⟩)
    (fun c ⟨hc, _, _, _, _, _, _, _, hm⟩ => ⟨hc, ?_⟩) ?_
  · have ho : Out (lay I F₀).pZn ((lay I F₀).pZn + dd I * 2) c₀.mem c.mem :=
      hm ▸ out_wrArr (le_refl 2) le_rfl le_rfl
    refine ⟨fun i hi => sarr_of_out (hA.gmem i hi) (le_refl 2) ho (Or.inl (by
        have := succ_mul_le (gsz I) hi; omega)),
      sarr_of_out hA.hp (le_refl 2) ho (Or.inr (by omega)), ?_,
      fun a ha => (ho _ (Or.inr (by omega))).trans (hA.tt a ha), ho.zeroFrom hA.zero (by omega),
      fun a ha => sarr_of_out (hA.aj a ha) (le_refl 2) ho (Or.inl (by
        have := succ_mul_le (asz I) (show a < dd I by omega)
        have : (r + 1) * 2 ≤ asz I := by omega
        omega)),
      sarr_of_out hA.w (le_refl 2) ho (Or.inr (by omega))⟩
    rw [hm]
    refine sarr_congr (sarr_wrArr (le_refl 2) _) fun v hv => ?_
    exact (ZnF_next hr ib hv).symm
  · simp only [smulCost, gCost]
    omega

/-! ### Block 2: `q` -/

/-- `q := E q ω_b`. -/
def qBlk : Stmt := .seq (smul kQ kE kQ) (smul kQ kQ kOB)

/-- The registers of the step except `q`. -/
def RQ (I : Inst) (F₀ r : ℕ) (Δ σb ωb : ℤ) (ib : ℕ) (c : Config) : Prop :=
  Glob I F₀ c ∧ c.reg kR = r ∧ SReg c kDL Δ ∧ c.reg kROW = (lay I F₀).pAj + r * asz I ∧
    c.reg kBP = (lay I F₀).pG + ib * gsz I ∧ SReg c kSB σb ∧ SReg c kOB ωb

theorem RQ_regIndep (I : Inst) (F₀ r : ℕ) (Δ σb ωb : ℤ) (ib : ℕ) :
    RegIndep (kQ :: (kQ + 1) :: scrW) (RQ I F₀ r Δ σb ωb ib) :=
  (Glob.regIndep' I F₀ (fun r hr => by
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · decide
    · decide
    · exact scrW_glob r hr)).and (by indep [SReg])

theorem qBlk_spec (I : Inst) (F₀ r : ℕ) (Δ σb ωb : ℤ) (ib q : ℕ) (m : ℕ → ℕ)
    (hz : ZeroFrom m (lay I F₀).fe) (B : ℕ) (hqB : Nat.size q ≤ B)
    (hωB : Nat.size ωb.natAbs ≤ B) (hS : (lay I F₀).fe + 2 * B ≤ S) :
    HTB S qBlk (fun c => (RQ I F₀ r Δ σb ωb ib c ∧ c.mem = m) ∧ SReg c kQ (q : ℤ))
      (fun c => (RQ I F₀ r Δ σb ωb ib c ∧ c.mem = m) ∧
        SReg c kQ ((bigE I.t I.k : ℤ) * q * ωb))
      (smulCost (q : ℤ) + smulCost ωb + 24) := by
  have hP : Indep (kQ :: (kQ + 1) :: arithW) (fun c => RQ I F₀ r Δ σb ωb ib c ∧ c.mem = m) :=
    ((RQ_regIndep I F₀ r Δ σb ωb ib).mono (by decide)).indep.and (Indep.mem (· = m))
  have hZ : ∀ c, (RQ I F₀ r Δ σb ωb ib c ∧ c.mem = m) → ZeroFrom c.mem (c.reg rFREE) :=
    fun c ⟨hc, hm⟩ => by rw [hm, hc.1.free]; exact hz
  have b1 := HTB.smul (S := S) (P := fun c => RQ I F₀ r Δ σb ωb ib c ∧ c.mem = m) (d := kQ) (x := kE)
    (y := kQ) (u := (bigE I.t I.k : ℤ)) (v := (q : ℤ)) (by decide) (by decide) (by decide) hP hZ
    (fun c ⟨hc, _⟩ => by rw [hc.1.free]; simp only [Int.natAbs_natCast]; omega)
  have b2 := HTB.smul (S := S) (P := fun c => RQ I F₀ r Δ σb ωb ib c ∧ c.mem = m) (d := kQ) (x := kQ)
    (y := kOB) (u := (bigE I.t I.k : ℤ) * q) (v := ωb) (by decide) (by decide) (by decide) hP hZ
    (fun c ⟨hc, _⟩ => by rw [hc.1.free]; omega)
  refine ((b1.pre fun c ⟨hc, hq⟩ => ⟨hc, hc.1.1.e, hq⟩).seq
    (b2.pre fun c ⟨hc, hq⟩ => ⟨hc, hq, hc.1.2.2.2.2.2.2⟩)).weaken (by omega)

/-! ### Block 3: `T`, `Δ`, `rowR` -/

/-- `T_r := pG + ib gs`, `Δ := ω_b`, `rowR += 2d`. -/
def finBlk : Stmt :=
  .seq (.add kA kPT kR) (.seq (.store kA kBP) (.seq (smov kDL kOB) (.add kROW kROW kAS)))

theorem finBlk_spec (I : Inst) (F₀ r : ℕ) (Δ σb ωb : ℤ) (ib : ℕ) (q : ℤ) (m : ℕ → ℕ)
    (hS : (lay I F₀).pT + r < S) :
    HTB S finBlk (fun c => (RQ I F₀ r Δ σb ωb ib c ∧ c.mem = m) ∧ SReg c kQ q)
      (fun c => Glob I F₀ c ∧ c.reg kR = r ∧ SReg c kDL ωb ∧ SReg c kQ q ∧
        c.reg kROW = (lay I F₀).pAj + (r + 1) * asz I ∧
        c.mem = upd m ((lay I F₀).pT + r) ((lay I F₀).pG + ib * gsz I)) 7 :=
  HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hg, hr, _, hrow, hbp, _, ⟨ho0, ho1⟩⟩, hm⟩, ⟨hq0, hq1⟩⟩ => by
    refine ⟨by addr_ok [finBlk, smov, hr, hg.pT], (Glob.regIndep' I F₀ (W := wregs finBlk) (by decide)).run (by decide) hg, ?_, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp +decide only [finBlk, smov, run_seq', run_add, run_store, run_mov, setReg_reg, setReg_mem,
      setMem_reg, setMem_mem_upd, ↓reduceIte, hr, hrow, hbp, ho0, ho1, hq0, hq1, hm, hg.pT, hg.as]
    ring

end StepC

end STACS2027.Runtimes.QPRam.Kmo
