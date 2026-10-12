module

public import Runtimes.ConvexQP.RAM.EllLayout
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: E2, the completion `Xs` and `L = H Xs`

At a feasible center (no negative entry, every block sum `≤ 2^p`):

* `feasXs`: the completion `Xs = feasPt I p As` (`Xs_{c,j} = As_{(c,j)}` for `j < k − 1`,
  `Xs_{c,k−1} = 2^p − ∑_j As_{(c,j)}`), written flat (index `c k + j`) at `qBX` (`feasXs_specB`);
* `mvL`: the path loads `L = H Xs` with `mvCore` at `eL` (`mvL_specB`; `mulVec_Hflat` identifies
  the product with `I.L Xs`).

The gap and the success test are in `EllGap.lean`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

/-! ### The completion on flat indices -/

theorem feasPt_flat_lt (I : Inst) (p : ℕ) (As : Idx I → ℤ) {c j : ℕ} (hc : c < I.t)
    (hj : j < I.k - 1) :
    flat (feasPt I p As) (c * I.k + j) = flatR As (c * (I.k - 1) + j) := by
  have hj' : j < I.k := by omega
  have e1 := flat_apply (feasPt I p As) ⟨c, hc⟩ ⟨j, hj'⟩
  have e2 := flatR_apply As ⟨c, hc⟩ ⟨j, hj⟩
  simp only at e1 e2
  rw [e1, e2]
  simp [feasPt, Inst.xiq, hj]

theorem feasPt_flat_last (I : Inst) (p : ℕ) (As : Idx I → ℤ) {c : ℕ} (hc : c < I.t)
    (hk : 0 < I.k) :
    flat (feasPt I p As) (c * I.k + (I.k - 1)) = 2 ^ p - bsum As c := by
  have e1 := flat_apply (feasPt I p As) ⟨c, hc⟩ ⟨I.k - 1, by omega⟩
  simp only at e1
  rw [e1, bsum_eq As ⟨c, hc⟩]
  simp [feasPt, Inst.xiq, blockSum]

/-! ### The program -/

/-- One entry `j < k − 1`: `Xs_{c,j} := As_{(c,j)}`, `S1 += As_{(c,j)}`. -/
def fxIn : Stmt :=
  .seq (sload eV ePa) (.seq (sstore ePx eV) (.seq (sadd eS1 eS1 eV)
    (.seq (addc ePa ePa 2) (addc ePx ePx 2))))

/-- One cycle: the entries `j < k − 1`, then `Xs_{c,k−1} := 2^p − S1`. -/
def fxOut : Stmt :=
  .seq (sconst eS1 0) (.seq (forUp eJ eK1 fxIn)
    (.seq (ssub eV eP2 eS1) (.seq (sstore ePx eV) (addc ePx ePx 2))))

/-- **E2 (1)**: the completion `Xs` at `qBX`. -/
def feasXs : Stmt := .seq (.seq (mov ePa eA) (mov ePx qBX)) (forUp eC qT fxOut)

/-! ### Invariants -/

/-- Before entry `j` of cycle `c`. -/
def FxIn (I : Inst) (Ly : Lay) (As : Idx I → ℤ) (m : ℕ → ℕ) (c j : ℕ) (cfg : Config) : Prop :=
  EG I Ly cfg ∧ cfg.mem = wrArr m Ly.pX 2 (flat (feasPt I (prec I.t I.k) As)) (c * I.k + j) ∧
    cfg.reg eC = c ∧ cfg.reg ePa = Ly.pA + (c * (I.k - 1) + j) * 2 ∧
    cfg.reg ePx = Ly.pX + (c * I.k + j) * 2 ∧
    SReg cfg eS1 (∑ j' ∈ Finset.range j, flatR As (c * (I.k - 1) + j'))

/-- Before cycle `c`. -/
def FxOut (I : Inst) (Ly : Lay) (As : Idx I → ℤ) (m : ℕ → ℕ) (c : ℕ) (cfg : Config) : Prop :=
  EG I Ly cfg ∧ cfg.mem = wrArr m Ly.pX 2 (flat (feasPt I (prec I.t I.k) As)) (c * I.k) ∧
    cfg.reg ePa = Ly.pA + c * (I.k - 1) * 2 ∧ cfg.reg ePx = Ly.pX + c * I.k * 2

/-! ### One entry -/

theorem fxIn_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (As : Idx I → ℤ) (m : ℕ → ℕ)
    (hA : SArr m Ly.pA 2 (nDim I.t I.k) (flatR As)) {c j : ℕ} (hc : c < I.t) (hj : j < I.k - 1)
    (hS : Ly.F ≤ S) :
    HTB S fxIn (fun cfg => FxIn I Ly As m c j cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1)
      (fun cfg => FxIn I Ly As m c (j + 1) cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1) 54 := by
  set Xf := flat (feasPt I (prec I.t I.k) As) with hXf
  set a := c * (I.k - 1) + j with ha
  set b := c * I.k + j with hb
  have han : a < nDim I.t I.k := by rw [nDim_eq]; exact flat_idx_lt hc hj
  have hbt : b < I.t * I.k := flat_idx_lt hc (by omega)
  set z := flatR As a with hz
  have hzX : Xf b = z := feasPt_flat_lt I _ As hc hj
  set s := ∑ j' ∈ Finset.range j, flatR As (c * (I.k - 1) + j') with hs
  set mm := wrArr m Ly.pX 2 Xf b with hmm
  have hAm : SMem mm (Ly.pA + a * 2) z := by
    have := SArr.out hA (le_refl 2) (m' := mm) (lo := Ly.pX) (hi := Ly.pX + b * 2)
      (fun x hx => wrArr_of_out (le_refl 2) hx) (by have := hL.q; have := hL.x; omega)
    exact this a han
  have h1 := HTB.sload (S := S) (P := fun cfg => FxIn I Ly As m c j cfg ∧ cfg.reg eJ = j ∧
      cfg.reg eK1 = I.k - 1) (d := eV) (p := ePa) (a := Ly.pA + a * 2) (z := z)
    (by decide) (by decide) (by decide) (by indep [FxIn, eG_iff, QRegs, SReg])
    (by have := hL.fits hS; omega)
  have h2 := HTB.sstore (S := S) (F := fun cfg => EG I Ly cfg ∧ cfg.reg eC = c ∧
      cfg.reg ePa = Ly.pA + a * 2 ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1 ∧ SReg cfg eS1 s)
    (p := ePx) (x := eV) (a := Ly.pX + b * 2) (z := z) (m := mm) (by decide) (by decide)
    (by decide) ((EG.regIndep I Ly).mono (by decide) |>.and (by indep [SReg]))
    (by have := hL.fits hS; omega)
  have h3 := HTB.sadd (S := S) (P := fun cfg => EG I Ly cfg ∧ cfg.mem = wrArr m Ly.pX 2 Xf (b + 1) ∧
      cfg.reg eC = c ∧ cfg.reg ePa = Ly.pA + a * 2 ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1 ∧
      cfg.reg ePx = Ly.pX + b * 2) (d := eS1) (x := eS1) (y := eV) (u := s) (v := z)
    (by decide) (by decide) (by decide) ((EG.indep (by decide)).and (by indep))
  have h4 : HTB S (.seq (addc ePa ePa 2) (addc ePx ePx 2))
      (fun cfg => (EG I Ly cfg ∧ cfg.mem = wrArr m Ly.pX 2 Xf (b + 1) ∧
        cfg.reg eC = c ∧ cfg.reg ePa = Ly.pA + a * 2 ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1 ∧
        cfg.reg ePx = Ly.pX + b * 2) ∧ SReg cfg eS1 (s + z))
      (fun cfg => FxIn I Ly As m c (j + 1) cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨hE, hm, hc', hpa, hj', hk', hpx⟩,
        hs0, hs1⟩ => by
      have hr : ∀ r, r ∉ wregs (.seq (addc ePa ePa 2) (addc ePx ePx 2)) →
          (RAM.run (.seq (addc ePa ePa 2) (addc ePx ePx 2)) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_, ?_⟩,
        ?_, ?_⟩
      all_goals try (rw [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg, hm, hb, Nat.add_assoc]
      · exact hc'
      · simp +decide [run_addc, hpa]; ring
      · simp +decide [run_addc, hpx]; ring
      · refine ⟨?_, ?_⟩ <;> rw [hr _ (by decide)]
        · rw [Finset.sum_range_succ]; exact hs0
        · rw [Finset.sum_range_succ]; exact hs1
      · exact hj'
      · exact hk'
  refine ((h1.pre fun cfg h => ⟨h, h.1.2.2.2.1, by rw [h.1.2.1]; exact hAm⟩).seq
    ((h2.pre fun cfg ⟨⟨⟨hE, hm, hc', hpa, hpx, hs'⟩, hj', hk'⟩, hv⟩ =>
      ⟨⟨hE, hc', hpa, hj', hk', hs'⟩, hv, hpx, hm⟩).seq
    ((h3.pre fun cfg ⟨⟨hE, hc', hpa, hj', hk', hs'⟩, hv, hpx, hm⟩ =>
      ⟨⟨hE, by rw [hm, wrArr_succ, hzX]; rfl, hc', hpa, hj', hk', hpx⟩, hs', hv⟩).seq
      h4))).weaken (by omega)

/-! ### One cycle -/

theorem fxOut_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (As : Idx I → ℤ) (m : ℕ → ℕ)
    (hA : SArr m Ly.pA 2 (nDim I.t I.k) (flatR As)) {c : ℕ} (hc : c < I.t) (hS : Ly.F ≤ S) :
    HTB S fxOut (fun cfg => FxOut I Ly As m c cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t)
      (fun cfg => FxOut I Ly As m (c + 1) cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t)
      ((I.k - 1) * 58 + 57) := by
  have hk : 0 < I.k := by have := hL.k3; omega
  set Xf := flat (feasPt I (prec I.t I.k) As) with hXf
  set b := c * I.k + (I.k - 1) with hb
  have hb1 : b + 1 = (c + 1) * I.k := by rw [hb, Nat.succ_mul]; omega
  have hbt : b < I.t * I.k := flat_idx_lt hc (by omega)
  set z := (2 : ℤ) ^ prec I.t I.k - bsum As c with hz
  have hzX : Xf b = z := feasPt_flat_last I _ As hc hk
  have h0 := HTB.sconst (S := S) (P := fun cfg => FxOut I Ly As m c cfg ∧ cfg.reg eC = c ∧
    cfg.reg qT = I.t) (d := eS1) 0 (by indep [FxOut, eG_iff, QRegs])
  have hl := HTB.forUpC (S := S) (i := eJ) (n := eK1) (N := I.k - 1) (body := fxIn)
    (FxIn I Ly As m c) 54 (by decide) (by decide) (by decide)
    (fun j => by indep [FxIn, eG_iff, QRegs, SReg])
    (fun j hj => fxIn_specB I Ly hL As m hA hc hj hS)
  have h3 := HTB.ssub (S := S) (P := FxIn I Ly As m c (I.k - 1)) (d := eV) (x := eP2) (y := eS1)
    (u := (2 : ℤ) ^ prec I.t I.k) (v := bsum As c) (by decide) (by decide) (by decide)
    (by indep [FxIn, eG_iff, QRegs, SReg])
  have h4 := HTB.sstore (S := S) (F := fun cfg => EG I Ly cfg ∧ cfg.reg eC = c ∧
      cfg.reg ePa = Ly.pA + (c * (I.k - 1) + (I.k - 1)) * 2)
    (p := ePx) (x := eV) (a := Ly.pX + b * 2) (z := z) (m := wrArr m Ly.pX 2 Xf b)
    (by decide) (by decide) (by decide) ((EG.regIndep I Ly).mono (by decide) |>.and (by indep))
    (by have := hL.fits hS; omega)
  have h5 : HTB S (addc ePx ePx 2)
      (fun cfg => (EG I Ly cfg ∧ cfg.reg eC = c ∧
        cfg.reg ePa = Ly.pA + (c * (I.k - 1) + (I.k - 1)) * 2) ∧ SReg cfg eV z ∧
        cfg.reg ePx = Ly.pX + b * 2 ∧ cfg.mem = wrArr m Ly.pX 2 Xf (b + 1))
      (fun cfg => FxOut I Ly As m (c + 1) cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨hE, hc', hpa⟩, _, hpx, hm⟩ => by
      have hr : ∀ r, r ∉ wregs (addc ePx ePx 2) →
          (RAM.run (addc ePx ePx 2) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_⟩, ?_, ?_⟩
      all_goals try (rw [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg, hm, hb1]
      · rw [hpa, Nat.succ_mul]
      · simp +decide [run_addc, hpx]; rw [← hb1]; ring
      · exact hc'
      · exact hE.t
  refine ((h0.post fun cfg ⟨⟨⟨hE, hm, hpa, hpx⟩, hc', hT⟩, hs⟩ =>
      ⟨⟨hE, by simpa using hm, hc', by simpa using hpa, by simpa using hpx, by simpa using hs⟩,
        hE.k1⟩).seq
    (hl.seq ((h3.pre fun cfg ⟨hI, _, _⟩ => ⟨hI, hI.1.p2, hI.2.2.2.2.2⟩).seq
    ((h4.pre fun cfg ⟨⟨hE, hm, hc', hpa, hpx, _⟩, hv⟩ => ⟨⟨hE, hc', hpa⟩, hv, hpx, hm⟩).seq
      (h5.pre fun cfg ⟨hF, hv, hpx, hm⟩ => ⟨hF, hv, hpx, by
        rw [hm, wrArr_succ, hzX]; rfl⟩))))).weaken (by omega)

/-! ### The completion -/

/-- **E2 (1)**: `feasXs` writes `Xs = feasPt I p As` flat at `qBX` (`t k` entries); `O(tk)`
steps. -/
theorem feasXs_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (As : Idx I → ℤ) (m : ℕ → ℕ)
    (hA : SArr m Ly.pA 2 (nDim I.t I.k) (flatR As)) (hS : Ly.F ≤ S) :
    HTB S feasXs (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => EG I Ly cfg ∧
        cfg.mem = wrArr m Ly.pX 2 (flat (feasPt I (prec I.t I.k) As)) (I.t * I.k))
      (I.t * ((I.k - 1) * 58 + 61) + 7) := by
  have h0 : HTB S (.seq (mov ePa eA) (mov ePx qBX)) (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => FxOut I Ly As m 0 cfg ∧ cfg.reg qT = I.t) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨hE, hm⟩ => by
      have hr : ∀ r, r ∉ wregs (.seq (mov ePa eA) (mov ePx qBX)) →
          (RAM.run (.seq (mov ePa eA) (mov ePx qBX)) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_⟩, ?_⟩
      · rw [run_mem_of_stores (by decide) rfl cfg, hm, Nat.zero_mul]; rfl
      · simp +decide [run_mov, hE.a]
      · simp +decide [run_mov, hE.x]
      · rw [hr _ (by decide)]; exact hE.t
  have hl := HTB.forUpC (S := S) (i := eC) (n := qT) (N := I.t) (body := fxOut)
    (FxOut I Ly As m) ((I.k - 1) * 58 + 57) (by decide) (by decide) (by decide)
    (fun c => by indep [FxOut, eG_iff, QRegs])
    (fun c hc => fxOut_specB I Ly hL As m hA hc hS)
  refine (h0.seq hl).mono (fun _ h => h) (fun cfg ⟨⟨hE, hm, _, _⟩, _, _⟩ => ⟨hE, hm⟩)
    (by have : I.t * ((I.k - 1) * 58 + 57 + 4) = I.t * ((I.k - 1) * 58 + 61) := by ring
        omega)

/-! ### The path loads `L = H Xs` -/

/-- The inputs of `mvCore` for `L = H Xs`. -/
def mvLSet : Stmt :=
  .seq (mov vR qKT) (.seq (mov vRow qBH) (.seq (.add vSI qKT qKT) (.seq (mov vN qKT)
    (.seq (.const vSA 2) (.seq (mov vX0 qBX) (.seq (.const vSX 2) (mov vPU eL)))))))

/-- **E2 (2)**: `L := H Xs` at `eL`. -/
def mvL : Stmt := .seq mvLSet mvCore

theorem mvL_wregs : ∀ r ∈ wregs mvL, r ∈ ellW := by decide

/-- `H · Xs` on flat indices is `flat (I.L Xs)`. -/
theorem mulVec_Hflat_flat (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) {b : ℕ} (hb : b < I.t * I.k) :
    Arith.mulVec (Hflat I) (flat Xs) (I.t * I.k) b = flat (I.L Xs) b := by
  obtain ⟨c, j, rfl⟩ := flat_decomp hb
  rw [mulVec_Hflat, flat_apply]

theorem mvL_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (Xs : Fin I.t → Fin I.k → ℤ)
    (m : ℕ → ℕ) (hH : HMem I m Ly.bh) (hX : SArr m Ly.pX 2 (I.t * I.k) (flat Xs))
    (hz : ZeroFrom m Ly.F) (B : ℕ) (hB : ∀ j < I.t * I.k, Nat.size (flat Xs j).natAbs ≤ B)
    (hS : Ly.F + 2 * B ≤ S) :
    HTB S mvL (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => EG I Ly cfg ∧
        cfg.mem = wrArr m Ly.pL 2 (Arith.mulVec (Hflat I) (flat Xs) (I.t * I.k)) (I.t * I.k))
      (I.t * I.k * (I.t * I.k * (31 * B + 87) + 19) + 17) := by
  have h0 : HTB S mvLSet (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg vR = I.t * I.k ∧ cfg.reg vRow = Ly.bh ∧
        cfg.reg vSI = 2 * (I.t * I.k) ∧ cfg.reg vN = I.t * I.k ∧ cfg.reg vSA = 2 ∧
        cfg.reg vX0 = Ly.pX ∧ cfg.reg vSX = 2 ∧ cfg.reg vPU = Ly.pL) 16 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨hE, hm⟩ => by
      refine ⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE,
        by rw [run_mem_of_stores (by decide) rfl cfg, hm], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp +decide [mvLSet, run_mov, hE.kt, hE.bh, hE.x, hE.l]
      ring
  have hf := hL.fits (S := S) (by omega)
  have hm := mvCore_specB (S := S) (R := EG I Ly) ((EG.regIndep I Ly).mono (by decide)) m Ly.F
    (I.t * I.k) Ly.bh (2 * (I.t * I.k)) (I.t * I.k) 2 Ly.pX 2 Ly.pL B (Hflat I) (flat Xs) hz
    (fun c hc => hc.free) (by have := hL.g; have := hL.u; have := hL.f; omega)
    (fun m' hS => HMem.out hH (lo := Ly.pL) (hi := Ly.pL + I.t * I.k * 2)
      (fun x hx => hS x (by omega)) (by have := hL.h; have := hL.q; have := hL.x; have := hL.l
                                        omega))
    (fun m' hS => SArr.out hX (le_refl 2) (lo := Ly.pL) (hi := Ly.pL + I.t * I.k * 2)
      (fun x hx => hS x (by omega)) (by have := hL.l; omega)) hB hS
    (fun i hi j hj => addr_lt_rows (by omega) (by have := hf.1; unfold hCells at this; omega)
      hi hj)
    (fun j hj => addr_lt_of_stride (le_refl 2) hf.2.2.2.1 hj)
  refine (h0.seq hm).mono (fun _ h => h) (fun cfg ⟨⟨hE, _, hmem, _⟩, h0⟩ => ⟨hE, ?_⟩)
    (by omega)
  rw [hmem, h0, Nat.sub_zero]

end STACS2027.Runtimes.QPRam
