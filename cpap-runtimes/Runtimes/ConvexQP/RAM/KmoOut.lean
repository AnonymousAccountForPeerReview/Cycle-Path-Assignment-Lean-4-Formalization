module

public import Runtimes.ConvexQP.RAM.KmoStep
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: Phase O (the output)

From the final state `s` of Phase M (`MInv d`): write `D = |Δ|`; gather `h_T` (the column `d` of
`G` on the rows `T`, `gather` with offset `2d`); `z := Aj h_T = zNum` (`mvCore`); for `a < tk`
write `|z_a|` if `sgnBit z_a = sgnBit Δ`, else `0`, which is `(sign Δ · z_a).toNat`
(`outVal_eq`). The output is `outList (I.exactFrom Xs 2^p)` (`oProg_spec`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP
open scoped Matrix

/-- The value written for `z` with the determinant `Δ ≠ 0`. -/
theorem outVal_eq {Δ : ℤ} (hΔ : Δ ≠ 0) (z : ℤ) :
    (if sgnBit z = sgnBit Δ then z.natAbs else 0) = (Δ.sign * z).toNat := by
  rcases lt_or_gt_of_ne hΔ with h | h
  · rw [Int.sign_eq_neg_one_of_neg h]
    by_cases hz : z < 0
    · simp [sgnBit, hz, h]; omega
    · simp [sgnBit, hz, h]; omega
  · rw [Int.sign_eq_one_of_pos h]
    by_cases hz : z < 0
    · simp [sgnBit, hz, show ¬ Δ < 0 by omega]; omega
    · simp [sgnBit, hz, show ¬ Δ < 0 by omega]; omega

/-! ### The program -/

/-- Inputs of the gather of `h_T`. -/
def hSet : Stmt := .seq (mov kN qD) (.seq (mov kPS kPT) (.seq (mov kSS kAS) (mov kPD kPCOL)))

/-- Inputs of `mvCore` for `z = Aj h_T`. -/
def zSet : Stmt :=
  .seq (mov vR qD) (.seq (mov vRow kPAJ) (.seq (mov vSI kAS) (.seq (mov vN qD)
    (.seq (.const vSA 2) (.seq (mov vX0 kPCOL) (.seq (.const vSX 2) (mov vPU kPU)))))))

/-- Write the weight of the entry `a` (at `kP1`). -/
def outBody : Stmt :=
  .seq (sload kX kP1) (.seq (.const kA 0) (.seq (ifEq kX kDL (.write (kX + 1)) (.write kA))
    (addc kP1 kP1 2)))

/-- **Phase O.** -/
def oProg : Stmt :=
  .seq (.write (kDL + 1)) (.seq (.seq hSet gather) (.seq (.seq zSet mvCore)
    (.seq (mov kP1 kPU) (forUp kJ qKT outBody))))

/-! ### The output list -/

variable {I : Inst} {Xs : Fin I.t → Fin I.k → ℤ} {S : ℕ}

theorem ofFn_eq_range (n : ℕ) (g : ℕ → ℕ) : List.ofFn (fun a : Fin n => g a) = (List.range n).map g := by
  apply List.ext_getElem <;> simp

/-- `h_T`: the column `d` of `G` on the rows `T`. -/
theorem hT_eq (s : MState (MM I) (dd I) (dd I)) {b : ℕ} (hb : b < dd I) :
    Gx I Xs (TF s b) (dd I) = kktH I (s.T ⟨b, hb⟩) := by
  have h1 := (s.T ⟨b, hb⟩).2
  simp only [Gx, lt_irrefl, ↓reduceIte, hf, TF, hb, ↓reduceDIte, h1]

/-- `Aj h_T` on natural indices is `zNum`. -/
theorem zNum_eq (s : MState (MM I) (dd I) (dd I)) {a : ℕ} (ha : a < dd I) :
    mulVec (AjF s) (fun b => Gx I Xs (TF s b) (dd I)) (dd I) a = zNum (kktH I) s ⟨a, ha⟩ := by
  rw [mulVec_eq_fin, zNum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hT_eq s b.2]
  simp [AjF, ha, b.2]

/-- **The output** of the exact rounding, as written by Phase O. -/
theorem outList_eq {s : MState (MM I) (dd I) (dd I)}
    (hs : moveRun (KG I Xs) (kktH I) (bigE I.t I.k) (kktZn I Xs) (2 ^ prec I.t I.k) = some s) :
    outList (I.exactFrom Xs (2 ^ prec I.t I.k)) = s.Δ.natAbs :: (List.range (I.t * I.k)).map
      (fun a => (s.Δ.sign * mulVec (AjF s) (fun b => Gx I Xs (TF s b) (dd I)) (dd I) a).toNat) := by
  have hd := dimKKT_eq I.t I.k
  unfold Inst.exactFrom
  rw [hs]
  simp only [outList, wlists]
  congr 1
  rw [← ofFn_eq_range, List.ofFn_mul]
  refine congrArg _ (List.ofFn_inj.mpr (funext fun c => List.ofFn_inj.mpr (funext fun j => ?_)))
  have hlt : (c : ℕ) * I.k + j < dd I := by
    have := c.2; have := j.2; nlinarith
  rw [zNum_eq s hlt]
  congr 3
  exact Fin.ext (by rw [Inst.colX, colX_val])

/-! ### The specification of Phase O -/

/-- `Δ ≠ 0` along Phase M. -/
theorem state_det_ne (hI : I.Valid) (hX : I.InX (ptOf Xs (2 ^ prec I.t I.k)))
    (hgap : I.gap (ptOf Xs (2 ^ prec I.t I.k)) ≤ eps I.t I.k ^ 2) {r : ℕ} (hr : r ≤ dd I)
    {s : MState (MM I) (dd I) r}
    (hs : moveAux (KG I Xs) (kktH I) (bigE I.t I.k) (kktZn I Xs) (2 ^ prec I.t I.k) r hr = some s) :
    s.Δ ≠ 0 :=
  (moveAux_bounds (bigE_pos I.t hI.1) (entryBound_pos hI.1) (kktG_entry_le hI _)
    (by positivity) (kkt_start hI hX hgap) r hr s hs).1.det_ne

theorem rowEquiv_cases {I : Inst} (i : Fin (nRows I.t I.k)) :
    (∃ c s, i = (rowEquiv I.t I.k).symm (.inl (c, s))) ∨
      ∃ c j b, i = (rowEquiv I.t I.k).symm (.inr ((c, j), b)) := by
  rcases h : rowEquiv I.t I.k i with ⟨c, s⟩ | ⟨⟨c, j⟩, b⟩
  · exact Or.inl ⟨c, s, by rw [← h, Equiv.symm_apply_apply]⟩
  · exact Or.inr ⟨c, j, b, by rw [← h, Equiv.symm_apply_apply]⟩

/-- The registers of Phase O. -/
def RO (I : Inst) (F₀ : ℕ) (s : MState (MM I) (dd I) (dd I)) (c : Config) : Prop :=
  Glob I F₀ c ∧ StRegs I F₀ s c

/-- The weights written by Phase O. -/
def outF (s : MState (MM I) (dd I) (dd I)) (a : ℕ) : ℕ :=
  (s.Δ.sign * mulVec (AjF s) (fun b => Gx I Xs (TF s b) (dd I)) (dd I) a).toNat

theorem outBody_spec (F₀ : ℕ) (s : MState (MM I) (dd I) (dd I)) (hΔ : s.Δ ≠ 0) (m : ℕ → ℕ)
    (pu : ℕ) (z : ℕ → ℤ) (j : ℕ) (hz : SMem m (pu + j * 2) (z j)) (hSz : pu + j * 2 + 1 < S) :
    HTB S outBody (fun c => (RO I F₀ s c ∧ c.mem = m ∧ c.reg kP1 = pu + j * 2 ∧
        c.out = s.Δ.natAbs :: (List.range j).map (fun a => (s.Δ.sign * z a).toNat)) ∧
        c.reg kJ = j ∧ c.reg qKT = I.t * I.k)
      (fun c => (RO I F₀ s c ∧ c.mem = m ∧ c.reg kP1 = pu + (j + 1) * 2 ∧
        c.out = s.Δ.natAbs :: (List.range (j + 1)).map (fun a => (s.Δ.sign * z a).toNat)) ∧
        c.reg kJ = j ∧ c.reg qKT = I.t * I.k) 14 :=
  HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hg, hst⟩, hm, hp, ho⟩, hj, hkt⟩ => by
    refine ⟨by addr_ok [outBody, sload, hp], ?_⟩
    have hR : RO I F₀ s (RAM.run outBody c) :=
      ((Glob.regIndep' I F₀ (W := wregs outBody) (by decide)).and
        (show RegIndep (wregs outBody) (StRegs I F₀ s) by indep [StRegs, SReg])).run
        (by decide) ⟨hg, hst⟩
    obtain ⟨⟨hΔ0, _⟩, _⟩ := hst
    refine ⟨⟨hR, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp +decide only [outBody, sload, run_seq', run_load, run_addc, run_const, setReg_mem,
        run_ifEq (show kX ≠ rT by decide) (show kDL ≠ rT by decide), config_ite_mem, run_write,
        emit_mem, ite_self, hm]
    · simp +decide only [outBody, sload, run_seq', run_load, run_addc, run_const, setReg_reg,
        run_ifEq (show kX ≠ rT by decide) (show kDL ≠ rT by decide), config_ite_reg, run_write,
        emit_reg, ↓reduceIte, hp, ite_self]
      ring
    · have hv := outVal_eq hΔ (z j)
      simp +decide only [outBody, sload, run_seq', run_load, run_addc, run_const, setReg_reg,
        setReg_mem, setReg_out, run_ifEq (show kX ≠ rT by decide) (show kDL ≠ rT by decide),
        config_ite_out, run_write, emit_out, ↓reduceIte, hp, hm, ho, hz.1,
        hz.2, hΔ0]
      rw [List.range_succ, List.map_append, List.map_singleton, ← hv]
      split_ifs <;> rfl
    · simp +decide only [outBody, sload, run_seq', run_load, run_addc, run_const, setReg_reg,
        run_ifEq (show kX ≠ rT by decide) (show kDL ≠ rT by decide), config_ite_reg, run_write,
        emit_reg, ↓reduceIte, hj, ite_self]
    · simp +decide only [outBody, sload, run_seq', run_load, run_addc, run_const, setReg_reg,
        run_ifEq (show kX ≠ rT by decide) (show kDL ≠ rT by decide), config_ite_reg, run_write,
        emit_reg, ↓reduceIte, hkt, ite_self]

/-- The bound of Phase O. -/
def TO (d tk : ℕ) : ℕ := 1 + (8 + (d * 17 + 3)) + (14 + (d * (d * 118 + 19) + 1)) + (2 + (tk * 18 + 3))

/-- **Phase O**: from the final state of Phase M, the output `outList (exactFrom Xs 2^p)`. -/
theorem oProg_spec (hI : I.Valid) (hX : I.InX (ptOf Xs (2 ^ prec I.t I.k)))
    (hgap : I.gap (ptOf Xs (2 ^ prec I.t I.k)) ≤ eps I.t I.k ^ 2) (F₀ : ℕ)
    (hS : (lay I F₀).fe + 2 ≤ S) :
    HTB S oProg (fun c => MInv I Xs F₀ (dd I) c ∧ c.out = [])
      (fun c => c.out = outList (I.exactFrom Xs (2 ^ prec I.t I.k))) (TO (dd I) (I.t * I.k)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  refine HTB.of_forall fun c₀ ⟨⟨hr', s, hs, hg, hst, hC, hW⟩, hout⟩ => ?_
  have hΔ := state_det_ne hI hX hgap hr' hs
  have hROi : RegIndep scrW (RO I F₀ s) :=
    (Glob.regIndep' I F₀ scrW_glob).and (by indep [StRegs, SReg])
  -- `D`
  have o1 : HTB S (.write (kDL + 1)) (fun c => c = c₀)
      (fun c => (RO I F₀ s c ∧ c.mem = c₀.mem) ∧ c.out = [s.Δ.natAbs]) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) le_rfl fun c hc => by
      subst hc
      refine ⟨⟨((hROi.mono (by decide)).run (by decide) ⟨hg, hst⟩), rfl⟩, ?_⟩
      simp only [run_write, emit_out, hout, List.nil_append, hst.1.2]
  -- `h_T`
  set hT : ℕ → ℤ := fun b => Gx I Xs (TF s b) (dd I) with hhT
  have o2a : HTB S hSet (fun c => RO I F₀ s c ∧ c.mem = c₀.mem)
      (fun c => RO I F₀ s c ∧ c.mem = c₀.mem ∧ c.reg kN = dd I ∧ c.reg kPS = (lay I F₀).pT ∧
        c.reg kSS = asz I ∧ c.reg kPD = (lay I F₀).pcol) 8 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      have hq := hc.1.qregs
      rw [qregs_iff] at hq
      refine ⟨(hROi.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [hSet, run_seq', run_mov, setReg_reg, setReg_mem, ↓reduceIte, hm,
        hq.2.2.2.2.1, hc.1.pT, hc.1.as, hc.1.pcol]
  have o2b := gather_spec (S := S) (R := RO I F₀ s) (hROi.mono gaW_sub) c₀.mem (dd I) (lay I F₀).pT
    (asz I) (lay I F₀).pcol (fun a => (lay I F₀).pG + TF s a * gsz I) hT (fun m hm a ha => by
      have ho := out_of_sameOn hm
      refine ⟨(ho _ (Or.inr (by omega))).trans (hC.tt a ha), ?_⟩
      have hTl := TF_lt s ha
      have hS := hC.gmem (TF s a) hTl (dd I) (by omega)
      have := succ_mul_le (gsz I) hTl
      rw [show (lay I F₀).pG + TF s a * gsz I + asz I = (lay I F₀).pG + TF s a * gsz I + dd I * 2 by
        omega]
      exact ⟨(ho _ (Or.inl (by omega))).trans hS.1, (ho _ (Or.inl (by omega))).trans hS.2⟩)
    (by omega) (fun a ha => by
      have hTl := TF_lt s ha
      have := succ_mul_le (gsz I) hTl
      omega) (by omega)
  set m₁ := wrArr c₀.mem (lay I F₀).pcol 2 hT (dd I) with hm₁
  have ho₁ : Out (lay I F₀).pcol ((lay I F₀).pcol + dd I * 2) c₀.mem m₁ :=
    out_wrArr (le_refl 2) le_rfl le_rfl
  -- `z = Aj h_T`
  have o3a : HTB S zSet (fun c => RO I F₀ s c ∧ c.mem = m₁)
      (fun c => RO I F₀ s c ∧ c.mem = m₁ ∧ c.reg vR = dd I ∧ c.reg vRow = (lay I F₀).pAj ∧
        c.reg vSI = asz I ∧ c.reg vN = dd I ∧ c.reg vSA = 2 ∧ c.reg vX0 = (lay I F₀).pcol ∧
        c.reg vSX = 2 ∧ c.reg vPU = (lay I F₀).pu) 14 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      have hq := hc.1.qregs
      rw [qregs_iff] at hq
      refine ⟨(hROi.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp +decide only [zSet, run_seq', run_mov, run_const, setReg_reg, setReg_mem, ↓reduceIte,
        hm, hq.2.2.2.2.1, hc.1.pAj, hc.1.as, hc.1.pcol, hc.1.pu]
  have hTb : ∀ j < dd I, Nat.size (hT j).natAbs ≤ 1 := fun j hj => by
    rw [hhT]
    simp only
    rw [hT_eq s hj]
    rcases rowEquiv_cases (I := I) (s.T ⟨j, hj⟩) with ⟨c, s', e⟩ | ⟨c, j', b, e⟩
    · rw [e, kktH_S, sgnS_val]; split_ifs <;> simp
    · rw [e, kktH_X]; simp
  have o3b := mvCore_specB (S := S) (R := RO I F₀ s) (hROi.mono mvW_sub) m₁ (lay I F₀).fe (dd I)
    (lay I F₀).pAj (asz I) (dd I) 2 (lay I F₀).pcol 2 (lay I F₀).pu 1 (AjF s) hT
    (ho₁.zeroFrom hC.zero (by omega)) (fun c hc => hc.1.free) (by omega)
    (fun m hm i hi => sarr_of_out (sarr_of_out (hC.aj i hi) (le_refl 2) ho₁ (Or.inl (by
        have := succ_mul_le (asz I) hi; omega))) (le_refl 2) (out_of_sameOn hm) (Or.inl (by
        have := succ_mul_le (asz I) hi; omega)))
    (fun m hm => sarr_of_out (sarr_wrArr (le_refl 2) (dd I)) (le_refl 2) (out_of_sameOn hm)
      (Or.inl (by omega))) hTb (by omega)
    (fun i hi j hj => addr_lt_rows (by omega) (show (lay I F₀).pAj + dd I * asz I ≤ S by omega)
      hi hj)
    (fun j hj => addr_lt_of_stride (le_refl 2) (show (lay I F₀).pcol + dd I * 2 ≤ S by omega) hj)
  set z : ℕ → ℤ := mulVec (AjF s) hT (dd I) with hz
  set m₂ := wrArr m₁ (lay I F₀).pu 2 z (dd I) with hm₂
  -- the output loop
  have o4a : HTB S (mov kP1 kPU) (fun c => RO I F₀ s c ∧ c.mem = m₂)
      (fun c => (RO I F₀ s c ∧ c.mem = m₂ ∧ c.reg kP1 = (lay I F₀).pu + 0 * 2) ∧
        c.reg qKT = I.t * I.k) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      have hq := hc.1.qregs
      rw [qregs_iff] at hq
      refine ⟨⟨(hROi.mono (by decide)).run (by decide) hc, ?_, ?_⟩, ?_⟩ <;>
      simp +decide only [run_mov, setReg_reg, setReg_mem, ↓reduceIte, hm, hc.1.pu, hq.2.2.1,
        Nat.zero_mul, Nat.add_zero]
  have hl := HTB.forUpC (S := S) (i := kJ) (n := qKT) (N := I.t * I.k) (body := outBody)
    (fun j c => RO I F₀ s c ∧ c.mem = m₂ ∧ c.reg kP1 = (lay I F₀).pu + j * 2 ∧
      c.out = s.Δ.natAbs :: (List.range j).map (fun a => (s.Δ.sign * z a).toNat)) 14
    (by decide) (by decide) (by decide)
    (fun j => (hROi.mono (by decide)).indep.and (by indep))
    (fun j hj => outBody_spec F₀ s hΔ m₂ (lay I F₀).pu z j
      (sarr_wrArr (le_refl 2) (dd I) j (by omega))
      (addr_lt_of_stride (le_refl 2) (show (lay I F₀).pu + dd I * 2 ≤ S by omega) (by omega)))
  have hout : ∀ {st : Stmt}, writes st = false → ∀ (l : List ℕ), ∀ c c', Frame st c c' →
      c.out = l → c'.out = l := fun hw l c c' hfr h => (hfr.out hw).trans h
  refine (o1.seq (((o2a.seq o2b).frame (hout (by decide) [s.Δ.natAbs])).seq
    ((((o3a.seq o3b).post fun c ⟨⟨hc, _, hm, _⟩, hv⟩ => ⟨hc, by
      rw [hv, Nat.sub_zero] at hm; exact hm⟩).frame (hout (by decide) [s.Δ.natAbs])).seq
    (((o4a.frame (hout (by decide) [s.Δ.natAbs])).post fun c ⟨⟨⟨hc, hm, hp⟩, hk⟩, ho⟩ =>
      ⟨⟨hc, hm, hp, by simpa using ho⟩, hk⟩).seq hl)))).mono (fun c h => h)
    (fun c ⟨⟨_, _, _, ho⟩, _⟩ => by rw [ho, outList_eq hs]) ?_
  simp only [TO]
  norm_num
  omega

end STACS2027.Runtimes.QPRam.Kmo
