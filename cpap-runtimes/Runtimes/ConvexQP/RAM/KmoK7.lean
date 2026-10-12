module

public import Runtimes.ConvexQP.RAM.KmoK6
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: Phase K (assembly)

`kProg = kPart1; kPi; kS; kXR; kFin`: the layout, `Zn₀ = (Xs, π) = kktZn`, `L = H Xs`, the rows
of `G = kktG (kktZ Xs)` with the column `h` and `h' = E h + 1`, then `Δ = 1`, `q = 2^p`,
`rowR = pAj` (`kFin`). `kProg_spec`: from `QMid`-like data to the invariant `MInv 0` of Phase M,
in `TK I B` steps (`B` bounds the bit lengths of `Xs`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-- `Δ := 1`, `q := 2^p`, `rowR := pAj`. -/
def kFin : Stmt := .seq (sconst kDL 1) (.seq (pow2N (kQ + 1) qP) (.seq (.const kQ 0) (mov kROW kPAJ)))

/-- **Phase K.** -/
def kProg : Stmt := .seq kPart1 (.seq kPi (.seq kS (.seq kXR kFin)))

/-- The bound of Phase K (`B` bounds the bit lengths of `Xs`). -/
def TK (I : Inst) (B : ℕ) : ℕ :=
  (5 * gsz I + 5 * asz I + 50 + 6 + (9 + (I.t * I.k * 27 + 3)) +
    (17 + (I.t * I.k * (I.t * I.k * (31 * B + 87) + 19) + 1))) +
  ((I.t * (I.k * 38 + 17) + 7) + ((90 + (I.t * (I.k * 54 + 47 + 4) + 3)) +
  ((8 + (I.t * (I.k * (77 + (I.t * I.k * 54 + 66 + 1) + 5 + 4) + 3 + 2 + 4) + 3)) +
  (2 + (4 * prec I.t I.k + 6) + 3))))

variable {I : Inst} {Xs : Fin I.t → Fin I.k → ℤ} {S : ℕ}

theorem kFin_spec (I : Inst) (F₀ bh bx : ℕ) (m : ℕ → ℕ) :
    HT kFin (fun cfg => KGl I F₀ bh bx cfg ∧ cfg.mem = m)
      (fun cfg => Glob I F₀ cfg ∧ SReg cfg kDL 1 ∧
        SReg cfg kQ ((2 ^ prec I.t I.k : ℕ) : ℤ) ∧ cfg.reg kROW = (lay I F₀).pAj ∧ cfg.mem = m)
      (2 + (4 * prec I.t I.k + 6) + 3) := by
  have hG : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ globFree) →
      Indep W (fun cfg => Glob I F₀ cfg ∧ cfg.mem = m) := fun hW =>
    (Glob.regIndep' I F₀ hW).indep.and (Indep.mem (· = m))
  have f1 := HT.sconst (P := fun cfg => Glob I F₀ cfg ∧ cfg.mem = m) (d := kDL) 1 (hG (by decide))
  have f2 := HT.pow2N (P := fun cfg => (Glob I F₀ cfg ∧ cfg.mem = m) ∧ SReg cfg kDL 1)
    (d := kQ + 1) (e := qP) (k := prec I.t I.k) (by decide)
    ((hG (by decide)).and (indep_sreg (by decide) (by decide) 1))
  have f3 : HT (.seq (.const kQ 0) (mov kROW kPAJ))
      (fun cfg => ((Glob I F₀ cfg ∧ cfg.mem = m) ∧ SReg cfg kDL 1) ∧
        cfg.reg (kQ + 1) = 2 ^ prec I.t I.k)
      (fun cfg => Glob I F₀ cfg ∧ SReg cfg kDL 1 ∧
        SReg cfg kQ ((2 ^ prec I.t I.k : ℕ) : ℤ) ∧ cfg.reg kROW = (lay I F₀).pAj ∧ cfg.mem = m)
      3 :=
    HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨hg, hm⟩, hdl⟩, hq⟩ => by
      refine ⟨(Glob.regIndep' I F₀ (W := wregs (.seq (.const kQ 0) (mov kROW kPAJ)))
        (by decide)).run (by decide) hg, (regIndep_sreg (by decide) (by decide) _).run
        (by decide) hdl, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
      simp +decide only [run_seq', run_const, run_mov, setReg_reg, setReg_mem, ↓reduceIte, hq,
        hg.pAj, hm, Int.natAbs_natCast]
      simp [sgnBit]
  have f1' : HT (sconst kDL 1) (fun cfg => KGl I F₀ bh bx cfg ∧ cfg.mem = m)
      (fun c => (Glob I F₀ c ∧ c.mem = m) ∧ SReg c kDL 1) 2 :=
    f1.pre fun cfg ⟨hk, hm⟩ => ⟨hk.glob, hm⟩
  have f2' : HT (pow2N (kQ + 1) qP) (fun c => (Glob I F₀ c ∧ c.mem = m) ∧ SReg c kDL 1)
      (fun c => ((Glob I F₀ c ∧ c.mem = m) ∧ SReg c kDL 1) ∧ c.reg (kQ + 1) = 2 ^ prec I.t I.k)
      (4 * prec I.t I.k + 6) :=
    f2.pre fun cfg h => ⟨h, by
      have hq := h.1.1.qregs; rw [qregs_iff] at hq; exact hq.2.2.2.2.2.2.2.1⟩
  exact (f1'.seq (f2'.seq f3)).weaken (by omega)

/-- The memory of the start of Phase M from the memory after the rows. -/
theorem memCore_init {F₀ bh : ℕ} {mπ m : ℕ → ℕ} (hm : KM2 I Xs F₀ bh mπ)
    (hR : RowsK I Xs F₀ m (MM I)) (hO : OutGH I F₀ mπ m) :
    MemCore I Xs F₀ (MState.init (M := MM I) (kktZn I Xs) (2 ^ prec I.t I.k)) m ∧
      WZero I F₀ 0 m := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine ⟨⟨hR.done, fun i hi => hR.hdone i hi, ?_, fun a ha => absurd ha (Nat.not_lt_zero a),
    fun a ha => absurd ha (Nat.not_lt_zero a), fun a ha => ?_⟩, fun a ha1 ha2 => ?_⟩
  · show SArr m (lay I F₀).pZn 2 (dd I) (ZnF₀ I Xs)
    intro v hv
    have := entry_lt (b := (lay I F₀).pZn) (s := 2) (le_refl 2) hv
    exact ⟨(hO _ (Or.inr (by omega)) (Or.inl (by omega))).trans (hm.zn v hv).1,
      (hO _ (Or.inr (by omega)) (Or.inl (by omega))).trans (hm.zn v hv).2⟩
  · rw [hO a (Or.inr (by omega)) (Or.inr (by omega))]; exact hm.zero a ha
  · rw [hO a (Or.inr (by omega)) (Or.inl (by omega))]; exact hm.zr a (by omega) (by omega)

/-- **Phase K on the RAM**: from the constants, `H` and `Xs` to the start of Phase M. -/
theorem kProg_spec (hI : I.Valid) (F₀ bh bx : ℕ) (m₀ : ℕ → ℕ) (hH : HMem I m₀ bh)
    (hX : SArr m₀ bx 2 (I.t * I.k) (flat Xs)) (hbh : bh + hCells I ≤ F₀)
    (hbx : bx + I.t * I.k * 2 ≤ F₀) (hZ : ZeroFrom m₀ F₀) (B : ℕ)
    (hB : ∀ j < I.t * I.k, Nat.size (flat Xs j).natAbs ≤ B) (hS : (lay I F₀).fe + 2 * B ≤ S) :
    HTB S kProg (fun c => QRegs I c ∧ c.reg qBH = bh ∧ c.reg qBX = bx ∧ c.reg rFREE = F₀ ∧
        c.mem = m₀)
      (fun c => MInv I Xs F₀ 0 c ∧ c.reg qD = dd I) (TK I B) := by
  have hk0 : 0 < I.k := by have := hI.1; omega
  have k1 := kPart1_spec I Xs F₀ bh bx m₀ hH hX hbh hbx hZ B hB hS
  have hS' : (lay I F₀).fe ≤ S := by omega
  have k2 : HTB S kPi (fun c => KGl I F₀ bh bx c ∧ KM1 I Xs F₀ bh c.mem)
      (fun c => KGl I F₀ bh bx c ∧ KM2 I Xs F₀ bh c.mem) (I.t * (I.k * 38 + 17) + 7) :=
    HTB.of_forall fun c₀ ⟨hk, h1⟩ => (kPi_spec (Xs := Xs) hk0 c₀.mem h1.l hS').mono
      (fun c hc => by subst hc; exact ⟨hk, rfl⟩)
      (fun c ⟨hk', hm⟩ => ⟨hk', hm ▸ km2_of hk0 hbh h1⟩) le_rfl
  have k3 : HTB S kS (fun c => KGl I F₀ bh bx c ∧ KM2 I Xs F₀ bh c.mem)
      (fun c => ∃ mπ, KM2 I Xs F₀ bh mπ ∧ SInv I Xs F₀ bh bx mπ I.t c)
      (90 + (I.t * (I.k * 54 + 47 + 4) + 3)) :=
    HTB.of_forall fun c₀ ⟨hk, h2⟩ => (kS_spec c₀.mem h2 hS').mono
      (fun c hc => by subst hc; exact ⟨hk, rfl⟩) (fun c h => ⟨c₀.mem, h2, h⟩) le_rfl
  have k4 : HTB S kXR (fun c => ∃ mπ, KM2 I Xs F₀ bh mπ ∧ SInv I Xs F₀ bh bx mπ I.t c)
      (fun c => ∃ mπ, KM2 I Xs F₀ bh mπ ∧ KGl I F₀ bh bx c ∧ RowsK I Xs F₀ c.mem (MM I) ∧
        OutGH I F₀ mπ c.mem)
      (8 + (I.t * (I.k * (77 + (I.t * I.k * 54 + 66 + 1) + 5 + 4) + 3 + 2 + 4) + 3)) :=
    HTB.of_forall fun c₀ ⟨mπ, h2, hs⟩ => (kX_spec mπ h2 hbh hS').mono
      (fun c hc => by subst hc; exact hs) (fun c h => ⟨mπ, h2, h⟩) le_rfl
  have k5 : HTB S kFin (fun c => ∃ mπ, KM2 I Xs F₀ bh mπ ∧ KGl I F₀ bh bx c ∧
        RowsK I Xs F₀ c.mem (MM I) ∧ OutGH I F₀ mπ c.mem)
      (fun c => MInv I Xs F₀ 0 c ∧ c.reg qD = dd I) (2 + (4 * prec I.t I.k + 6) + 3) :=
    HTB.of_forall fun c₀ ⟨mπ, h2, hk, hR, hO⟩ => (HTB.of_HT rfl (kFin_spec I F₀ bh bx c₀.mem)).mono
      (fun c hc => by subst hc; exact ⟨hk, rfl⟩)
      (fun c ⟨hg, hdl, hq, hrow, hm⟩ => by
        have hc := memCore_init h2 hR hO
        rw [← hm] at hc
        have hq' := hg.qregs
        rw [qregs_iff] at hq'
        exact ⟨⟨Nat.zero_le _, MState.init (kktZn I Xs) (2 ^ prec I.t I.k), rfl, hg,
          ⟨hdl, hq, by rw [hrow]; ring⟩, hc.1, hc.2⟩, hq'.2.2.2.2.1⟩) le_rfl
  exact (k1.seq (k2.seq (k3.seq (k4.seq k5)))).weaken (by unfold TK; omega)

end STACS2027.Runtimes.QPRam.Kmo
