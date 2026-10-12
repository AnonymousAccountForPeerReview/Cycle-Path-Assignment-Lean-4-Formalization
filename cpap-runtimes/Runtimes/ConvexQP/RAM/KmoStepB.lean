module

public import Runtimes.ConvexQP.RAM.KmoArg
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: a step of Phase M, part B (the bordered adjugate)

After the scan (best row `ib`, `σ_b`, `ω_b` in registers):
1. `vBlk`: `v := ρᵀ Aj` (`mvCore` on the transposed `Aj`, `ρ` = row `ib` of `G`);
2. `r1Blk`: `Aj_{ab} := (ω_b Aj_{ab} + u_a v_b) / Δ` for `a, b < r` (`r1Core false`);
3. `colNBlk`: column `r` of `Aj := −u` (`cpLoop`, stride `2d`);
4. `rowNBlk`: row `r` of `Aj := −v` (`cpLoop`);
5. `cornBlk`: `Aj_{rr} := Δ`.
`aj_border`: the cells of the top-left `(r+1) × (r+1)` block after these writes.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### Cells of a row-major matrix -/

theorem cell_eq {S a a' y y' : ℕ} (hy : y < S) (hy' : y' < S) (h : a * S + y = a' * S + y') :
    a = a' ∧ y = y' := by
  have hS : 0 < S := by omega
  have h1 : (a * S + y) / S = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hy, Nat.zero_add]
  have h2 : (a' * S + y') / S = a' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hy', Nat.zero_add]
  have ha : a = a' := by rw [← h1, ← h2, h]
  subst ha
  exact ⟨rfl, by omega⟩

/-- **The bordered write.** If the top-left `r × r` block of the matrix at `pa` (row stride
`S = 2n`, `r < n`) is `A`, then after writing the new top-left block `A'` (`wrRows`), the column
`r` (`cu`), the row `r` (`rv`) and the corner `δ`, the top-left `(r+1) × (r+1)` block is the
bordered matrix. -/
theorem aj_border {m₀ : ℕ → ℕ} {pa n r : ℕ} (hr : r < n) (A' : ℕ → ℕ → ℤ) (cu rv : ℕ → ℤ)
    (δ : ℤ) (B : ℕ → ℕ → ℤ)
    (hcc : ∀ a < r, ∀ b < r, B a b = A' a b) (hcl : ∀ a < r, B a r = cu a)
    (hlc : ∀ b < r, B r b = rv b) (hll : B r r = δ) :
    ∀ a < r + 1, SArr (sw (wrArr (wrArr (wrRows m₀ pa (2 * n) r A' r) (pa + 2 * r) (2 * n) cu r)
      (pa + r * (2 * n)) 2 rv r) (pa + r * (2 * n) + 2 * r) δ) (pa + a * (2 * n)) 2 (r + 1)
      (B a) := by
  intro a ha b hb
  set S := 2 * n with hS
  set m₁ := wrRows m₀ pa S r A' r
  set m₂ := wrArr m₁ (pa + 2 * r) S cu r
  set m₃ := wrArr m₂ (pa + r * S) 2 rv r
  -- the cell `(a, b)`, `e ∈ {0, 1}`
  have hcell : ∀ e < 2, ∀ a' b' e', b' < n → e' < 2 →
      pa + a * S + b * 2 + e = pa + a' * S + b' * 2 + e' → a = a' ∧ b = b' ∧ e = e' := by
    intro e he a' b' e' hb' he' h
    have := cell_eq (S := S) (a := a) (a' := a') (y := b * 2 + e) (y' := b' * 2 + e') (by omega)
      (by omega) (by omega)
    omega
  -- not a cell of the corner unless `a = b = r`
  have hcorner : ∀ e < 2, ¬ (a = r ∧ b = r) →
      sw m₃ (pa + r * S + 2 * r) δ (pa + a * S + b * 2 + e) = m₃ (pa + a * S + b * 2 + e) := by
    intro e he hne
    refine sw_apply_of_ne _ (fun h => ?_) (fun h => ?_)
    · have := hcell e he r r 0 hr (by omega) (by omega)
      omega
    · have := hcell e he r r 1 hr (by omega) (by omega)
      omega
  -- not a cell of row `r` unless `a = r`
  have hrow : ∀ e < 2, a ≠ r →
      m₃ (pa + a * S + b * 2 + e) = m₂ (pa + a * S + b * 2 + e) := by
    intro e he hne
    refine wrArr_of_ne fun j hj => ⟨fun h => ?_, fun h => ?_⟩
    · have := hcell e he r j 0 (by omega) (by omega) (by omega)
      omega
    · have := hcell e he r j 1 (by omega) (by omega) (by omega)
      omega
  -- not a cell of column `r` unless `b = r`
  have hcol : ∀ e < 2, b ≠ r →
      m₂ (pa + a * S + b * 2 + e) = m₁ (pa + a * S + b * 2 + e) := by
    intro e he hne
    refine wrArr_of_ne fun j hj => ⟨fun h => ?_, fun h => ?_⟩
    · have := hcell e he j r 0 hr (by omega) (by omega)
      omega
    · have := hcell e he j r 1 hr (by omega) (by omega)
      omega
  rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha' | rfl <;>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb' | rfl
  · -- the new top-left block
    have hw := sarr_wrRows (m₀ := m₀) (pa := pa) (si := S) (nc := r) (A' := A') (by omega) r ha' b
      hb'
    rw [hcc a ha' b hb']
    have e0 := (hcorner 0 (by omega) (by omega)).trans ((hrow 0 (by omega) (by omega)).trans
      (hcol 0 (by omega) (by omega)))
    have e1 := (hcorner 1 (by omega) (by omega)).trans ((hrow 1 (by omega) (by omega)).trans
      (hcol 1 (by omega) (by omega)))
    exact ⟨by rw [Nat.add_zero] at e0; rw [e0]; exact hw.1, by rw [e1]; exact hw.2⟩
  · -- column `r` (`b = r`)
    have hw := sarr_wrArr (m₀ := m₁) (b := pa + 2 * b) (s := S) (f := cu) (by omega) b a ha'
    rw [hcl a ha']
    have e0 := (hcorner 0 (by omega) (by omega)).trans (hrow 0 (by omega) (by omega))
    have e1 := (hcorner 1 (by omega) (by omega)).trans (hrow 1 (by omega) (by omega))
    have ea : pa + a * S + b * 2 = pa + 2 * b + a * S := by ring
    exact ⟨by rw [Nat.add_zero] at e0; rw [e0, ea]; exact hw.1,
      by rw [e1, ea]; exact hw.2⟩
  · -- row `r` (`a = r`)
    have hw := sarr_wrArr (m₀ := m₂) (b := pa + a * S) (s := 2) (f := rv) (le_refl 2) a b hb'
    rw [hlc b hb']
    have e0 := hcorner 0 (by omega) (by omega)
    have e1 := hcorner 1 (by omega) (by omega)
    exact ⟨by rw [Nat.add_zero] at e0; rw [e0]; exact hw.1, by rw [e1]; exact hw.2⟩
  · -- the corner
    rw [hll, show pa + b * S + b * 2 = pa + b * S + 2 * b by ring]
    exact smem_sw _ _ _

variable {S : ℕ}

section StepB

variable (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ : ℕ) {r : ℕ} (s : MState (MM I) (dd I) r)

/-- The registers after the scan: the best row `ib` with its `σ` and `ω`. -/
def RB (ib : ℕ) (c : Config) : Prop :=
  RA I F₀ s c ∧ c.reg kBP = (lay I F₀).pG + ib * gsz I ∧ SReg c kSB (sgf I Xs s ib) ∧
    SReg c kOB (omf I Xs s ib)

theorem RB_regIndep (ib : ℕ) : RegIndep scrW (RB I Xs F₀ s ib) :=
  (RA_regIndep I F₀ s).and (by indep [SReg])

/-- After `vBlk`. -/
def MemB1 (ib : ℕ) (m : ℕ → ℕ) : Prop :=
  MemA6 I Xs F₀ s m ∧ SArr m (lay I F₀).pv 2 r (vf I Xs s ib)

variable {I Xs F₀ s}

/-! ### Block 1: `v = ρᵀ Aj` -/

/-- Inputs of `mvCore` for `v = ρᵀ Aj` (rows of `Ajᵀ` at `pAj + 2i`, stride `2d`). -/
def vSet : Stmt :=
  .seq (mov vR kR) (.seq (mov vRow kPAJ) (.seq (.const vSI 2) (.seq (mov vN kR)
    (.seq (mov vSA kAS) (.seq (mov vX0 kBP) (.seq (.const vSX 2) (mov vPU kPV)))))))

/-- `v := ρᵀ Aj`. -/
def vBlk : Stmt := .seq vSet mvCore

theorem vBlk_spec (hr : r + 1 ≤ dd I) {ib : ℕ} (hib : ib < MM I) {R : Config → Prop}
    (hR : RegIndep scrW R) (hRB : ∀ c, R c → RB I Xs F₀ s ib c) (B : ℕ)
    (hB : ∀ j < r, Nat.size (Gx I Xs ib j).natAbs ≤ B) (hS : (lay I F₀).fe + 16 * B + 6 ≤ S) :
    HTB S vBlk (fun c => R c ∧ MemA6 I Xs F₀ s c.mem)
      (fun c => R c ∧ MemB1 I Xs F₀ s ib c.mem) (r * (r * (31 * B + 87) + 19) + 15) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hA⟩ => ?_
  have hC := hA.1.1.1
  have h1 : HTB S vSet (fun c => c = c₀) (fun c => R c ∧ c.mem = c₀.mem ∧ c.reg vR = r ∧
      c.reg vRow = (lay I F₀).pAj ∧ c.reg vSI = 2 ∧ c.reg vN = r ∧ c.reg vSA = asz I ∧
      c.reg vX0 = (lay I F₀).pG + ib * gsz I ∧ c.reg vSX = 2 ∧ c.reg vPU = (lay I F₀).pv) 14 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      obtain ⟨⟨hg, _, hr', _⟩, hbp, _⟩ := hRB c hc₀
      refine ⟨(hR.mono (by decide)).run (by decide) hc₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [vSet, run_seq', run_mov, run_const, setReg_reg, setReg_mem, ↓reduceIte,
        hr', hg.pAj, hg.as, hg.pv, hbp]
  have hra : (lay I F₀).pAj + r * asz I ≤ S := by
    have := Nat.mul_le_mul_right (asz I) (show r ≤ dd I by omega)
    omega
  have hib' := succ_mul_le (gsz I) hib
  have h2 := mvCore_specB (S := S) (R := R) ((hR.mono mvW_sub)) c₀.mem (lay I F₀).fe r (lay I F₀).pAj 2 r
    (asz I) ((lay I F₀).pG + ib * gsz I) 2 (lay I F₀).pv B (fun i j => AjF s j i)
    (fun j => Gx I Xs ib j) hC.zero (fun c hc => (hRB c hc).1.1.free) (by omega)
    (fun m hm i hi j hj => by
      have ho := out_of_sameOn hm
      have hS := hC.aj j hj i hi
      have hlt := succ_mul_le (asz I) (show j < dd I by omega)
      rw [show (lay I F₀).pAj + i * 2 + j * asz I = (lay I F₀).pAj + j * asz I + i * 2 by ring]
      exact ⟨(ho _ (Or.inl (by omega))).trans hS.1, (ho _ (Or.inl (by omega))).trans hS.2⟩)
    (fun m hm => sarr_mono (sarr_of_out (hC.gmem ib hib) (le_refl 2) (out_of_sameOn hm)
      (Or.inl (by have := succ_mul_le (gsz I) hib; omega))) (by omega)) hB
    (by omega) (fun i hi j hj => addr_lt_cols (by omega) hra hi hj)
    (fun j hj => addr_lt_of_stride (le_refl 2)
      (show (lay I F₀).pG + ib * gsz I + r * 2 ≤ S by omega) hj)
  refine (h1.seq h2).mono (fun c h => h) (fun c ⟨⟨hc, _, hm, _⟩, hv⟩ => ⟨hc, ?_⟩) (by omega)
  rw [hv, Nat.sub_zero] at hm
  have ho : Out (lay I F₀).pv ((lay I F₀).pv + r * 2) c₀.mem c.mem :=
    hm ▸ out_wrArr (le_refl 2) le_rfl le_rfl
  refine ⟨⟨⟨⟨hC.of_out (by omega) (ho.mono (by omega) (by omega)),
    sarr_of_out hA.1.1.2.1 (le_refl 2) ho (Or.inl (by omega)),
    sarr_of_out hA.1.1.2.2 (le_refl 2) ho (Or.inr (by omega))⟩,
    sarr_of_out hA.1.2 (le_refl 2) ho (Or.inr (by omega))⟩,
    sarr_of_out hA.2 (le_refl 2) ho (Or.inr (by omega))⟩, ?_⟩
  rw [hm]; exact sarr_wrArr (le_refl 2) _

variable (I Xs F₀ s) in
/-- After the bordered update: the new top-left `(r+1) × (r+1)` block of `Aj`, the rest as
before. -/
structure MemB2 (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) (m : ℕ → ℕ) : Prop where
  gmem : ∀ i < MM I, SArr m ((lay I F₀).pG + i * gsz I) 2 (dd I + 1) (Gx I Xs i)
  hp : SArr m (lay I F₀).php 2 (MM I) (hpf I)
  zn : SArr m (lay I F₀).pZn 2 (dd I) (ZnF s)
  tt : ∀ a < r, m ((lay I F₀).pT + a) = (lay I F₀).pG + TF s a * gsz I
  zero : ZeroFrom m (lay I F₀).fe
  aj : ∀ a < r + 1, SArr m ((lay I F₀).pAj + a * asz I) 2 (r + 1) (AjF (nxt I Xs s hr ib) a)
  w : SArr m (lay I F₀).pw 2 (dd I) (wf I Xs s)

/-! ### Blocks 2–5: the bordered update of `Aj` -/

/-- Inputs of `r1Core false`: `α = ω_b`, `β = 1`, `γ = Δ`. -/
def rSet : Stmt :=
  .seq (mov vR kR) (.seq (mov vRow kPAJ) (.seq (mov vSI kAS) (.seq (mov vN kR) (.seq (mov vPU kPU)
    (.seq (mov vX0 kPV) (.seq (sconst vB0 1) (.seq (smov vAl kOB) (smov vGa kDL))))))))

/-- Inputs of `cpLoop` for the column `r := −u`. -/
def cnSet : Stmt :=
  .seq (mov kN kR) (.seq (mov kPS kPU) (.seq (.const kSS 2) (.seq (.add kPD kPAJ kOFF)
    (.seq (mov kSD kAS) (.const kNG 1)))))

/-- Inputs of `cpLoop` for the row `r := −v`. -/
def rnSet : Stmt :=
  .seq (mov kN kR) (.seq (mov kPS kPV) (.seq (.const kSS 2) (.seq (mov kPD kROW)
    (.seq (.const kSD 2) (.const kNG 1)))))

/-- The corner `Aj_{rr} := Δ`. -/
def cornBlk : Stmt := .seq (.add kA kROW kOFF) (sstore kA kDL)

/-- The bordered update of `Aj`. -/
def bordBlk : Stmt :=
  .seq (.seq rSet (r1Core false)) (.seq (.seq cnSet cpLoop) (.seq (.seq rnSet cpLoop) cornBlk))

theorem bordBlk_spec (hr : r + 1 ≤ dd I) (ib : Fin (MM I)) {R : Config → Prop}
    (hR : RegIndep scrW R) (hRB : ∀ c, R c → RB I Xs F₀ s ib c) (hΔ : s.Δ ≠ 0) (B : ℕ)
    (hα : Nat.size (omf I Xs s ib).natAbs ≤ B) (hβ : 1 ≤ B)
    (hA : ∀ a < r, ∀ b < r, Nat.size (AjF s a b).natAbs ≤ B)
    (hu : ∀ a < r, Nat.size (uf I Xs s a).natAbs ≤ B)
    (hv : ∀ b < r, Nat.size (vf I Xs s ib b).natAbs ≤ B) (hS : (lay I F₀).fe + 16 * B + 6 ≤ S) :
    HTB S bordBlk (fun c => R c ∧ MemB1 I Xs F₀ s ib c.mem)
      (fun c => R c ∧ MemB2 I Xs F₀ s hr ib c.mem)
      (r * (r * (248 * B + 286) + 31 * B + 60) + 54 * r + 52) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨hc₀, hA'⟩ => ?_
  have hC := hA'.1.1.1.1
  -- `r1Core`
  have b1 : HTB S rSet (fun c => c = c₀) (fun c => R c ∧ c.mem = c₀.mem ∧ c.reg vR = r ∧
      c.reg vRow = (lay I F₀).pAj ∧ c.reg vSI = asz I ∧ c.reg vN = r ∧ c.reg vPU = (lay I F₀).pu ∧
      c.reg vX0 = (lay I F₀).pv ∧ SReg c vB0 1 ∧ SReg c vAl (omf I Xs s ib) ∧
      SReg c vGa s.Δ) 22 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      obtain ⟨⟨hg, ⟨⟨hΔ0, hΔ1⟩, _⟩, hr', _⟩, _, _, ⟨ho0, ho1⟩⟩ := hRB c hc₀
      refine ⟨(hR.mono (by decide)).run (by decide) hc₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp +decide only [rSet, smov, sconst, run_seq', run_mov, run_const, setReg_reg, setReg_mem,
        ↓reduceIte, hr', hg.pAj, hg.as, hg.pu, hg.pv, hΔ0, hΔ1, ho0, ho1]
  have hasr : r * asz I + asz I ≤ dd I * asz I := succ_mul_le (asz I) (show r < dd I by omega)
  have hsi : r * 2 ≤ asz I := by omega
  have hu' := hA'.1.1.1.2.1
  have hv' := hA'.2
  have b2 := r1Core_specB false (S := S) (R := R) (hR.mono r1W_sub) c₀.mem (lay I F₀).fe r r (lay I F₀).pAj
    (asz I) (lay I F₀).pu (lay I F₀).pv B (omf I Xs s ib) 1 s.Δ (AjF s) (uf I Xs s)
    (vf I Xs s ib) hC.zero (fun c hc => (hRB c hc).1.1.free) hsi (by omega) hC.aj
    (fun m hm => sarr_of_out hu' (le_refl 2) (out_of_sameOn hm) (Or.inr (by omega)))
    (fun m hm => sarr_of_out hv' (le_refl 2) (out_of_sameOn hm) (Or.inr (by omega)))
    (by simpa [GoodDiv] using hΔ) hα (by simpa using hβ) hA hu hv (by omega) (by omega) (by omega)
  set m₁ := wrRows c₀.mem (lay I F₀).pAj (asz I) r
    (r1New false (omf I Xs s ib) 1 s.Δ (AjF s) (uf I Xs s) (vf I Xs s ib)) r with hm₁
  have ho₁ : Out (lay I F₀).pAj ((lay I F₀).pAj + r * asz I) c₀.mem m₁ :=
    out_wrRows hsi le_rfl le_rfl
  -- column `r`
  have b3 : HTB S cnSet (fun c => R c ∧ c.mem = m₁) (fun c => R c ∧ c.mem = m₁ ∧ c.reg kN = r ∧
      c.reg kPS = (lay I F₀).pu ∧ c.reg kSS = 2 ∧ c.reg kPD = (lay I F₀).pAj + 2 * r ∧
      c.reg kSD = asz I ∧ c.reg kNG = 1) 9 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      obtain ⟨⟨hg, _, hr', hoff⟩, _⟩ := hRB c hc
      refine ⟨(hR.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [cnSet, run_seq', run_mov, run_const, run_add, setReg_reg, setReg_mem,
        ↓reduceIte, hr', hg.pAj, hg.as, hg.pu, hoff, hm]
  have b4 := cpLoop_spec (S := S) (R := R) (hR.mono cpW_sub) m₁ r (lay I F₀).pu 2
    ((lay I F₀).pAj + 2 * r) (asz I) 1 (uf I Xs s) (by omega) (fun m hm j hj => by
      have := sarr_of_out (sarr_of_out hu' (le_refl 2) ho₁ (Or.inr (by omega))) (le_refl 2)
        (out_of_sameOn hm) (Or.inr (by omega)) j hj
      exact this)
    (fun j hj => addr_lt_of_stride (le_refl 2) (show (lay I F₀).pu + r * 2 ≤ S by omega) hj)
    (by omega)
  set m₂ := wrArr m₁ ((lay I F₀).pAj + 2 * r) (asz I) (fun j => sgnMul 1 (uf I Xs s j)) r
    with hm₂
  have ho₂ : Out (lay I F₀).pAj ((lay I F₀).pAj + dd I * asz I) m₁ m₂ :=
    out_wrArr (by omega) (by omega) (by omega)
  -- row `r`
  have b5 : HTB S rnSet (fun c => R c ∧ c.mem = m₂) (fun c => R c ∧ c.mem = m₂ ∧ c.reg kN = r ∧
      c.reg kPS = (lay I F₀).pv ∧ c.reg kSS = 2 ∧ c.reg kPD = (lay I F₀).pAj + r * asz I ∧
      c.reg kSD = 2 ∧ c.reg kNG = 1) 9 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      obtain ⟨⟨hg, ⟨_, _, hrow⟩, hr', _⟩, _⟩ := hRB c hc
      refine ⟨(hR.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [rnSet, run_seq', run_mov, run_const, setReg_reg, setReg_mem,
        ↓reduceIte, hr', hg.pv, hrow, hm]
  have b6 := cpLoop_spec (S := S) (R := R) (hR.mono cpW_sub) m₂ r (lay I F₀).pv 2
    ((lay I F₀).pAj + r * asz I) 2 1 (vf I Xs s ib) (le_refl 2) (fun m hm j hj => by
      have := sarr_of_out (sarr_of_out (sarr_of_out hv' (le_refl 2) ho₁ (Or.inr (by omega)))
        (le_refl 2) ho₂ (Or.inr (by omega))) (le_refl 2) (out_of_sameOn hm) (Or.inr (by omega)) j hj
      exact this)
    (fun j hj => addr_lt_of_stride (le_refl 2) (show (lay I F₀).pv + r * 2 ≤ S by omega) hj)
    (by omega)
  set m₃ := wrArr m₂ ((lay I F₀).pAj + r * asz I) 2 (fun j => sgnMul 1 (vf I Xs s ib j)) r
    with hm₃
  have ho₃ : Out (lay I F₀).pAj ((lay I F₀).pAj + dd I * asz I) m₂ m₃ :=
    out_wrArr (le_refl 2) (by omega) (by omega)
  -- the corner
  have b7 : HTB S cornBlk (fun c => R c ∧ c.mem = m₃)
      (fun c => R c ∧ c.mem = sw m₃ ((lay I F₀).pAj + r * asz I + 2 * r) s.Δ) 5 :=
    HTB.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      obtain ⟨⟨_, ⟨⟨hΔ0, hΔ1⟩, _, hrow⟩, _, hoff⟩, _⟩ := hRB c hc
      refine ⟨by addr_ok [cornBlk, sstore, hrow, hoff], (hR.mono (by decide)).run (by decide) hc, ?_⟩
      simp +decide only [cornBlk, sstore, run_seq', run_add, run_addc, run_store, setReg_reg,
        setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hrow, hoff, hm]
      rw [hΔ0, hΔ1]
      rfl
  set m₄ := sw m₃ ((lay I F₀).pAj + r * asz I + 2 * r) s.Δ with hm₄
  have ho₄ : Out (lay I F₀).pAj ((lay I F₀).pAj + dd I * asz I) m₃ m₄ := out_sw (by omega)
    (by omega)
  have ho : Out (lay I F₀).pAj ((lay I F₀).pAj + dd I * asz I) c₀.mem m₄ :=
    (((ho₁.mono le_rfl (by omega)).trans ho₂).trans ho₃).trans ho₄
  have b2' : HTB S (r1Core false) _ (fun c => R c ∧ c.mem = m₁) _ :=
    b2.post fun c ⟨⟨hc, _, hm, _⟩, hv⟩ => ⟨hc, by rw [hv, Nat.sub_zero] at hm; exact hm⟩
  refine ((b1.seq b2').seq ((b3.seq b4).seq ((b5.seq b6).seq b7))).mono (fun c h => h)
    (fun c ⟨hc, hm⟩ => ⟨hc, ?_⟩) (by omega)
  rw [hm]
  refine ⟨fun i hi => sarr_of_out (hC.gmem i hi) (le_refl 2) ho (Or.inl (by
      have := succ_mul_le (gsz I) hi; omega)),
    sarr_of_out hC.hp (le_refl 2) ho (Or.inr (by omega)),
    sarr_of_out hC.zn (le_refl 2) ho (Or.inr (by omega)),
    fun a ha => (ho _ (Or.inr (by omega))).trans (hC.tt a ha), ho.zeroFrom hC.zero (by omega), ?_,
    sarr_of_out hA'.1.1.1.2.2 (le_refl 2) ho (Or.inr (by omega))⟩
  have hb := aj_border (m₀ := c₀.mem) (pa := (lay I F₀).pAj) (n := dd I) (r := r) (by omega)
    (r1New false (omf I Xs s ib) 1 s.Δ (AjF s) (uf I Xs s) (vf I Xs s ib))
    (fun j => sgnMul 1 (uf I Xs s j)) (fun j => sgnMul 1 (vf I Xs s ib j)) s.Δ
    (AjF (nxt I Xs s hr ib)) (fun a ha b hb => AjF_next_cc hr ib ha hb)
    (fun a ha => by rw [AjF_next_cl hr ib ha]; simp [sgnMul])
    (fun b hb => by rw [AjF_next_lc hr ib hb]; simp [sgnMul]) (AjF_next_ll hr ib)
  exact hb

end StepB

end STACS2027.Runtimes.QPRam.Kmo
