module

public import Runtimes.ConvexQP.RAM.KmoK2
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: Phase K, part 3 (the rows of `G` and `h'`, the rows `S_{c,s}`)

`RowsK m R`: the rows `i < R` of `G` (with the column `h`) and the entries `i < R` of `h'` are
written, the rows and entries from `R` on are zero. Rows are written in order; a row is written
inside its own block (and its entry of `h'`), see `RowsK.step`. The contents of the three kinds
of rows (`rowS_content`: a fill and the column `h`; `rowA_content`: `±H_a` and the column `π_c`;
`rowB_content`: one entry) and the writer of one row `S_{c,s}` (`rowSB_spec`; the loop over the
rows `S` is `kS_spec` in `KmoK4.lean`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

section Rows

variable (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ : ℕ)

/-- The rows `i < R` of `G` and the entries `i < R` of `h'` are written, the rest is zero. -/
structure RowsK (m : ℕ → ℕ) (R : ℕ) : Prop where
  done : ∀ i < R, SArr m ((lay I F₀).pG + i * gsz I) 2 (dd I + 1) (Gx I Xs i)
  hdone : ∀ i < R, SMem m ((lay I F₀).php + i * 2) (hpf I i)
  zg : ZeroOn m ((lay I F₀).pG + R * gsz I) ((lay I F₀).pG + MM I * gsz I)
  zh : ZeroOn m ((lay I F₀).php + R * 2) ((lay I F₀).php + MM I * 2)

/-- `m'` agrees with `m` outside `G` and `h'`. -/
def OutGH (m m' : ℕ → ℕ) : Prop :=
  ∀ a, (a < (lay I F₀).pG ∨ (lay I F₀).pAj ≤ a) →
    (a < (lay I F₀).php ∨ (lay I F₀).php + 2 * MM I ≤ a) → m' a = m a

variable {I Xs F₀}

theorem OutGH.refl (m : ℕ → ℕ) : OutGH I F₀ m m := fun _ _ _ => rfl

theorem OutGH.trans {m₁ m₂ m₃ : ℕ → ℕ} (h₁ : OutGH I F₀ m₁ m₂) (h₂ : OutGH I F₀ m₂ m₃) :
    OutGH I F₀ m₁ m₃ := fun a ha hb => (h₂ a ha hb).trans (h₁ a ha hb)

/-- **Writing row `R`.** If `m'` agrees with `m` outside the block of row `R` and its entry of
`h'`, and holds row `R` and `h'_R`, the rows and entries up to `R` are written. -/
theorem RowsK.step {m m' : ℕ → ℕ} {R : ℕ} (h : RowsK I Xs F₀ m R) (hR : R < MM I)
    (ho : ∀ a, (a < (lay I F₀).pG + R * gsz I ∨ (lay I F₀).pG + R * gsz I + gsz I ≤ a) →
      (a < (lay I F₀).php + R * 2 ∨ (lay I F₀).php + R * 2 + 2 ≤ a) → m' a = m a)
    (hrow : SArr m' ((lay I F₀).pG + R * gsz I) 2 (dd I + 1) (Gx I Xs R))
    (hh : SMem m' ((lay I F₀).php + R * 2) (hpf I R)) :
    RowsK I Xs F₀ m' (R + 1) ∧ OutGH I F₀ m m' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  have hRg := succ_mul_le (gsz I) hR
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun a ha1 ha2 => ?_, fun a ha1 ha2 => ?_⟩,
    fun a ha hb => ho a (by omega) (by omega)⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hig := succ_mul_le (gsz I) hi
      exact sarr_of_eq (h.done i hi) fun j hj => by
        have := entry_lt (b := (lay I F₀).pG + i * gsz I) (s := 2) (le_refl 2) hj
        exact ⟨ho _ (Or.inl (by omega)) (Or.inl (by omega)),
          ho _ (Or.inl (by omega)) (Or.inl (by omega))⟩
    · exact hrow
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ⟨(ho _ (Or.inr (by omega)) (Or.inl (by omega))).trans (h.hdone i hi).1,
        (ho _ (Or.inr (by omega)) (Or.inl (by omega))).trans (h.hdone i hi).2⟩
    · exact hh
  · rw [Nat.add_mul, Nat.one_mul] at ha1
    rw [ho a (Or.inr (by omega)) (Or.inl (by omega))]
    exact h.zg a (by omega) ha2
  · rw [ho a (Or.inr (by omega)) (Or.inr (by omega))]
    exact h.zh a (by omega) ha2

end Rows

/-! ### The contents of the three kinds of rows -/

/-- A row `S`: a fill of `k` entries from the column `k0`, and the column `h`. -/
theorem rowS_content {m : ℕ → ℕ} {rb d k0 k : ℕ} (σ hv : ℤ) (hk : k0 + k ≤ d)
    (hz : ∀ a, rb ≤ a → a < rb + (d + 1) * 2 → m a = 0) :
    SArr (sw (wrArr m (rb + k0 * 2) 2 (fun _ => σ) k) (rb + 2 * d) hv) rb 2 (d + 1)
      (fun v => if k0 ≤ v ∧ v < k0 + k then σ else if v = d then hv else 0) := by
  intro v hv'
  by_cases hvd : v = d
  · subst hvd
    have : ¬ (k0 ≤ v ∧ v < k0 + k) := by omega
    simp only [this, ↓reduceIte]
    rw [show rb + v * 2 = rb + 2 * v by ring]
    exact smem_sw _ _ _
  · simp only [hvd, ↓reduceIte]
    have e0 : sw (wrArr m (rb + k0 * 2) 2 (fun _ => σ) k) (rb + 2 * d) hv (rb + v * 2) =
        wrArr m (rb + k0 * 2) 2 (fun _ => σ) k (rb + v * 2) := sw_of_out _ (by omega)
    have e1 : sw (wrArr m (rb + k0 * 2) 2 (fun _ => σ) k) (rb + 2 * d) hv (rb + v * 2 + 1) =
        wrArr m (rb + k0 * 2) 2 (fun _ => σ) k (rb + v * 2 + 1) := sw_of_out _ (by omega)
    by_cases hin : k0 ≤ v ∧ v < k0 + k
    · simp only [hin, and_self, ↓reduceIte]
      have := sarr_wrArr (m₀ := m) (b := rb + k0 * 2) (f := fun _ => σ) (le_refl 2) k (v - k0)
        (by omega)
      rw [show rb + k0 * 2 + (v - k0) * 2 = rb + v * 2 by omega] at this
      exact ⟨e0.trans this.1, e1.trans this.2⟩
    · simp only [hin, ↓reduceIte]
      refine smem_zero ?_ ?_
      · rw [e0, wrArr_of_out (le_refl 2) (by omega)]; exact hz _ (by omega) (by omega)
      · rw [e1, wrArr_of_out (le_refl 2) (by omega)]; exact hz _ (by omega) (by omega)

/-- A row of type A: `n` entries `f` from the column `0`, and the entry `n + c`. -/
theorem rowA_content {m : ℕ → ℕ} {rb d n c : ℕ} (f : ℕ → ℤ) (σ : ℤ)
    (hz : ∀ a, rb ≤ a → a < rb + (d + 1) * 2 → m a = 0) :
    SArr (sw (wrArr m rb 2 f n) (rb + (2 * n + 2 * c)) σ) rb 2 (d + 1)
      (fun v => if v < n then f v else if v = n + c then σ else 0) := by
  intro v hv'
  by_cases hvn : v < n
  · simp only [hvn, ↓reduceIte]
    have := sarr_wrArr (m₀ := m) (b := rb) (f := f) (le_refl 2) n v hvn
    exact ⟨(sw_of_out _ (by omega)).trans this.1, (sw_of_out _ (by omega)).trans this.2⟩
  · simp only [hvn, ↓reduceIte]
    by_cases hvc : v = n + c
    · simp only [hvc, ↓reduceIte]
      rw [show rb + (n + c) * 2 = rb + (2 * n + 2 * c) by ring]
      exact smem_sw _ _ _
    · simp only [hvc, ↓reduceIte]
      refine smem_zero ?_ ?_
      · rw [sw_of_out _ (by omega), wrArr_of_out (le_refl 2) (by omega)]
        exact hz _ (by omega) (by omega)
      · rw [sw_of_out _ (by omega), wrArr_of_out (le_refl 2) (by omega)]
        exact hz _ (by omega) (by omega)

/-- A row of type B: one entry `a`. -/
theorem rowB_content {m : ℕ → ℕ} {rb d a : ℕ} (σ : ℤ)
    (hz : ∀ x, rb ≤ x → x < rb + (d + 1) * 2 → m x = 0) :
    SArr (sw m (rb + 2 * a) σ) rb 2 (d + 1) (fun v => if v = a then σ else 0) := by
  intro v hv'
  by_cases hva : v = a
  · simp only [hva, ↓reduceIte]
    rw [show rb + a * 2 = rb + 2 * a by ring]
    exact smem_sw _ _ _
  · simp only [hva, ↓reduceIte]
    refine smem_zero ?_ ?_
    · rw [sw_of_out _ (by omega)]; exact hz _ (by omega) (by omega)
    · rw [sw_of_out _ (by omega)]; exact hz _ (by omega) (by omega)

/-! ### The rows `S_{c,s}` -/

/-- One row `S`: fill `k` entries from `pOne` with sign `ng`, the column `h` from `hreg`, the
entry of `h'` from `hpreg`; then the next row. -/
def rowSB (ng hreg hpreg : ℕ) : Stmt :=
  .seq (.seq (mov kN qK) (.seq (mov kPS kKO) (.seq (.const kSS 0) (.seq (.add kPD kRP kJJ)
    (.seq (.const kSD 2) (.const kNG ng)))))) (.seq cpLoop (.seq (.add kA kRP kAS)
    (.seq (sstore kA hreg) (.seq (sstore kHP hpreg) (.seq (.add kRP kRP kGS) (addc kHP kHP 2))))))

variable {S : ℕ}

section SRows

variable (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ bh bx : ℕ)

/-- The registers of the loop over the rows `S` (before row `R` of cycle `c`). -/
def SG (c R : ℕ) (cfg : Config) : Prop :=
  KGl I F₀ bh bx cfg ∧ cfg.reg kRP = (lay I F₀).pG + R * gsz I ∧
    cfg.reg kHP = (lay I F₀).php + R * 2 ∧ cfg.reg kJJ = c * I.k * 2 ∧ cfg.reg kXP = I.k * 2 ∧
    SReg cfg kLP ((bigE I.t I.k : ℤ) + 1) ∧ SReg cfg kHR (1 - (bigE I.t I.k : ℤ)) ∧
    SReg cfg kONE 1 ∧ SReg cfg kMONE (-1)

theorem SG_regIndep (c R : ℕ) : RegIndep (rT :: (List.range' 400 50 ++ List.range' 530 10))
    (SG I F₀ bh bx c R) :=
  (KGl.regIndep' I F₀ bh bx (by decide)).and (by indep [SReg])

variable {I Xs F₀ bh bx}

theorem rowSB_spec {c R : ℕ} (hR : R < MM I) (hc : c < I.t) (ng hreg hpreg : ℕ) (σ hp : ℤ)
    (hng : sgnMul ng 1 = σ)
    (hne : hreg ≠ kA ∧ hreg + 1 ≠ kA ∧ hreg ≠ rT ∧ hreg + 1 ≠ rT ∧ hpreg ≠ kA ∧
      hpreg + 1 ≠ kA ∧ hpreg ≠ rT ∧ hpreg + 1 ≠ rT)
    (hσr : ∀ cfg, SG I F₀ bh bx c R cfg → SReg cfg hreg σ)
    (hpr : ∀ cfg, SG I F₀ bh bx c R cfg → SReg cfg hpreg hp)
    (hrow : ∀ v < dd I + 1, Gx I Xs R v =
      if c * I.k ≤ v ∧ v < c * I.k + I.k then σ else if v = dd I then σ else 0)
    (hhp : hpf I R = hp) (mπ : ℕ → ℕ) (hone : SMem mπ (lay I F₀).pOne 1)
    (hS : (lay I F₀).fe ≤ S) :
    HTB S (rowSB ng hreg hpreg)
      (fun cfg => SG I F₀ bh bx c R cfg ∧ RowsK I Xs F₀ cfg.mem R ∧ OutGH I F₀ mπ cfg.mem)
      (fun cfg => SG I F₀ bh bx c (R + 1) cfg ∧ RowsK I Xs F₀ cfg.mem (R + 1) ∧
        OutGH I F₀ mπ cfg.mem) (I.k * 27 + 23) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hR₀, hO₀⟩ => ?_
  have hRg := succ_mul_le (gsz I) hR
  have hck : c * I.k + I.k ≤ I.t * I.k := succ_mul_le I.k hc
  have hSG := SG_regIndep I F₀ bh bx c R
  set rb := (lay I F₀).pG + R * gsz I with hrb
  have b1 : HTB S (.seq (mov kN qK) (.seq (mov kPS kKO) (.seq (.const kSS 0) (.seq (.add kPD kRP kJJ)
      (.seq (.const kSD 2) (.const kNG ng)))))) (fun cfg => cfg = c₀)
      (fun cfg => SG I F₀ bh bx c R cfg ∧ cfg.mem = c₀.mem ∧ cfg.reg kN = I.k ∧
        cfg.reg kPS = (lay I F₀).pOne ∧ cfg.reg kSS = 0 ∧ cfg.reg kPD = rb + c * I.k * 2 ∧
        cfg.reg kSD = 2 ∧ cfg.reg kNG = ng) 8 :=
    HTB.of_HT (by simp [memFree]) <| HT.run_le (by simp [LoopFree]) (by simp [size]) fun cfg hcfg => by
      subst hcfg
      have hq := hc₀.1.glob.qregs
      rw [qregs_iff] at hq
      refine ⟨(hSG.mono (by simp +decide [wregs])).run (by simp [LoopFree]) hc₀, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩ <;>
      simp +decide only [run_seq', run_mov, run_const, run_add, setReg_reg, setReg_mem, ↓reduceIte,
        hq.2.1, hc₀.1.pOne, hc₀.2.1, hc₀.2.2.2.1]
      rfl
  have hone' : SMem c₀.mem (lay I F₀).pOne 1 :=
    ⟨(hO₀ _ (Or.inr (by omega)) (Or.inr (by omega))).trans hone.1,
      (hO₀ _ (Or.inr (by omega)) (Or.inr (by omega))).trans hone.2⟩
  have b2 := cpLoop_spec (S := S) (R := SG I F₀ bh bx c R) (hSG.mono (by decide)) c₀.mem I.k
    (lay I F₀).pOne 0 (rb + c * I.k * 2) 2 ng (fun _ => 1) (le_refl 2) (fun m hm j _ => by
      have ho := out_of_sameOn hm
      simp only [Nat.mul_zero, Nat.add_zero]
      exact ⟨(ho _ (Or.inr (by omega))).trans hone'.1, (ho _ (Or.inr (by omega))).trans hone'.2⟩)
    (fun j _ => by omega) (by omega)
  set m₁ := wrArr c₀.mem (rb + c * I.k * 2) 2 (fun _ => sgnMul ng 1) I.k with hm₁
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8⟩ := hne
  have b3 : HTB S (.seq (.add kA kRP kAS) (.seq (sstore kA hreg) (.seq (sstore kHP hpreg)
      (.seq (.add kRP kRP kGS) (addc kHP kHP 2)))))
      (fun cfg => SG I F₀ bh bx c R cfg ∧ cfg.mem = m₁)
      (fun cfg => SG I F₀ bh bx c (R + 1) cfg ∧
        cfg.mem = sw (sw m₁ (rb + 2 * dd I) σ) ((lay I F₀).php + R * 2) hp) 12 :=
    HTB.of_HT_addrOK (by simp [LoopFree, sstore]) (fun cfg ⟨hcfg, _⟩ => by
      obtain ⟨hk, hrp, hhp', _⟩ := hcfg
      addr_ok [sstore, hrp, hhp', hk.glob.as]) <| HT.run_le (by simp [LoopFree, sstore]) (by simp [size, sstore]) fun cfg ⟨hcfg, hm⟩ => by
      have hs0 := hσr cfg hcfg
      have hp0 := hpr cfg hcfg
      obtain ⟨hk, hrp, hhp', hjj, hxp, hlp, hhr, hone1, hmone⟩ := hcfg
      refine ⟨⟨(KGl.regIndep' I F₀ bh bx (W := wregs (.seq (.add kA kRP kAS) (.seq (sstore kA hreg)
        (.seq (sstore kHP hpreg) (.seq (.add kRP kRP kGS) (addc kHP kHP 2))))))
        (by simp +decide [wregs, sstore])).run (by simp [LoopFree, sstore]) hk, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩, ?_⟩
      · simp +decide only [sstore, run_seq', run_add, run_addc, run_store, setReg_reg,
          setMem_reg, ↓reduceIte, hrp, hk.glob.gs]
        ring
      · simp +decide only [sstore, run_seq', run_add, run_addc, run_store, setReg_reg,
          setMem_reg, ↓reduceIte, hhp']
        ring
      · simp +decide only [sstore, run_seq', run_add, run_addc, run_store, setReg_reg,
          setMem_reg, ↓reduceIte, hjj]
      · simp +decide only [sstore, run_seq', run_add, run_addc, run_store, setReg_reg,
          setMem_reg, ↓reduceIte, hxp]
      all_goals first
        | exact (regIndep_sreg (W := wregs (.seq (.add kA kRP kAS) (.seq (sstore kA hreg)
            (.seq (sstore kHP hpreg) (.seq (.add kRP kRP kGS) (addc kHP kHP 2))))))
            (by simp +decide [wregs, sstore]) (by simp +decide [wregs, sstore]) _).run
            (by simp [LoopFree, sstore]) (by assumption)
        | skip
      simp +decide only [sstore, run_seq', run_add, run_addc, run_store, setReg_reg,
        setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hrp, hhp', hm, hk.glob.as, hn1, hn2,
        hn4, hn5, hn6, hn7, hn8]
      rw [hs0.1, hs0.2, hp0.1, hp0.2]
      rfl
  refine (b1.seq (b2.seq b3)).mono (fun cfg h => h) (fun cfg ⟨hsg, hm⟩ => ?_) (by omega)
  have hzr : ∀ a, rb ≤ a → a < rb + (dd I + 1) * 2 → c₀.mem a = 0 := fun a ha1 ha2 =>
    hR₀.zg a ha1 (by omega)
  have hrow' := rowS_content (m := c₀.mem) (rb := rb) (d := dd I) (k0 := c * I.k) (k := I.k)
    σ σ (by omega) hzr
  rw [show (fun _ : ℕ => σ) = (fun _ : ℕ => sgnMul ng 1) by rw [hng]] at hrow'
  have hst := hR₀.step hR (m' := cfg.mem) (fun a ha hb => by
      rw [hm, sw_of_out _ (by omega), sw_of_out _ (by omega), hm₁,
        wrArr_of_out (le_refl 2) (by omega)])
    (by
      rw [hm]
      refine sarr_congr (sarr_of_eq hrow' fun j hj => ?_) fun v hv => (hrow v hv).symm
      have := entry_lt (b := rb) (s := 2) (le_refl 2) hj
      exact ⟨sw_of_out _ (by omega), sw_of_out _ (by omega)⟩)
    (by rw [hm, hhp]; exact smem_sw _ _ _)
  exact ⟨hsg, hst.1, hO₀.trans hst.2⟩

end SRows

end STACS2027.Runtimes.QPRam.Kmo
