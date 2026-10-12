module

public import Runtimes.ConvexQP.RAM.EllLayout
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: the cut vector `g` (E1 and E3)

One nested pass over the reduced coordinates `(c, j)` writes the cut vector `g` (flat, at `eG`),
in the mode left by the scan in `eF1`, `eF2` (`gMode`):
* `eF1 = a + 1 ≠ 0` (first negative entry `a`): `g = −e_a` (`negCut`);
* `eF1 = 0`, `eF2 = c + 1 ≠ 0` (first cycle `c` with a large block sum): `g = ∑_j e_{(c,j)}`
  (`blockCut`);
* `eF1 = eF2 = 0`: the gradient cut `g_{(c,j)} = L_{c,j} − L_{c,k−1}` (`gradCut`), reading
  `L` at `eL`.

`gLoop_specB`: `O(n)` steps.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

/-- The entry `(c, j)` of the cut vector in the mode `(f1, f2)`. -/
def gMode (f1 f2 : ℕ) (Lf : ℕ → ℤ) (k c j : ℕ) : ℤ :=
  if f1 ≠ 0 then (if c * (k - 1) + j + 1 = f1 then -1 else 0)
  else if f2 ≠ 0 then (if c + 1 = f2 then 1 else 0)
  else Lf (c * k + j) - Lf (c * k + (k - 1))

/-! ### The program -/

/-- `V := g_{(c,j)}` (`ePx = c(k−1)+j`, `ePy` at `L_{c,j}`, `eT1` at `L_{c,k−1}`). -/
def gVal : Stmt :=
  .ifz eF1
    (.ifz eF2
      (.seq (sload eV ePy) (.seq (sload eW eT1) (ssub eV eV eW)))
      (.seq (addc eT2 eC 1) (ifEq eT2 eF2 (sconst eV 1) (sconst eV 0))))
    (.seq (addc eT2 ePx 1) (ifEq eT2 eF1 (sconst eV (-1)) (sconst eV 0)))

/-- One entry: write `g_{(c,j)}`, advance. -/
def gIn : Stmt :=
  .seq gVal (.seq (sstore ePa eV) (.seq (addc ePa ePa 2) (.seq (inc ePx) (addc ePy ePy 2))))

/-- One cycle (`eT1 := ` the address of `L_{c,k−1}`). -/
def gOut : Stmt :=
  .seq (.seq (.add eT1 ePy eK1) (.add eT1 eT1 eK1)) (.seq (forUp eJ eK1 gIn) (addc ePy ePy 2))

/-- **The cut vector** `g` at `eG`. -/
def gLoop : Stmt := .seq (.seq (mov ePa eG) (.seq (.const ePx 0) (mov ePy eL))) (forUp eC qT gOut)

theorem gLoop_wregs : ∀ r ∈ wregs gLoop, r ∈ ellW := by decide

/-! ### Invariants -/

/-- Before entry `j` of cycle `c`. -/
def GIn (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (gf : ℕ → ℤ) (f1 f2 c j : ℕ) (cfg : Config) : Prop :=
  EG I Ly cfg ∧ cfg.mem = wrArr m Ly.pG 2 gf (c * (I.k - 1) + j) ∧ cfg.reg eC = c ∧
    cfg.reg ePa = Ly.pG + (c * (I.k - 1) + j) * 2 ∧ cfg.reg ePx = c * (I.k - 1) + j ∧
    cfg.reg ePy = Ly.pL + (c * I.k + j) * 2 ∧ cfg.reg eT1 = Ly.pL + (c * I.k + (I.k - 1)) * 2 ∧
    cfg.reg eF1 = f1 ∧ cfg.reg eF2 = f2

/-- Before cycle `c`. -/
def GOut (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (gf : ℕ → ℤ) (f1 f2 c : ℕ) (cfg : Config) : Prop :=
  EG I Ly cfg ∧ cfg.mem = wrArr m Ly.pG 2 gf (c * (I.k - 1)) ∧
    cfg.reg ePa = Ly.pG + c * (I.k - 1) * 2 ∧ cfg.reg ePx = c * (I.k - 1) ∧
    cfg.reg ePy = Ly.pL + c * I.k * 2 ∧ cfg.reg eF1 = f1 ∧ cfg.reg eF2 = f2

theorem GIn.indep (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (gf : ℕ → ℤ) (f1 f2 c j : ℕ)
    {W : List ℕ} (hW : ∀ r ∈ W, r ∈ ellW)
    (h : eC ∉ W ∧ ePa ∉ W ∧ ePx ∉ W ∧ ePy ∉ W ∧ eT1 ∉ W ∧ eF1 ∉ W ∧ eF2 ∉ W) :
    Indep W (GIn I Ly m gf f1 f2 c j) :=
  (EG.indep hW).and ((Indep.mem (· = wrArr m Ly.pG 2 gf (c * (I.k - 1) + j))).and
    ((Indep.reg h.1 (· = c)).and
    ((Indep.reg h.2.1 (· = Ly.pG + (c * (I.k - 1) + j) * 2)).and
    ((Indep.reg h.2.2.1 (· = c * (I.k - 1) + j)).and
    ((Indep.reg h.2.2.2.1 (· = Ly.pL + (c * I.k + j) * 2)).and
    ((Indep.reg h.2.2.2.2.1 (· = Ly.pL + (c * I.k + (I.k - 1)) * 2)).and
    ((Indep.reg h.2.2.2.2.2.1 (· = f1)).and (Indep.reg h.2.2.2.2.2.2 (· = f2)))))))))

/-! ### One value -/

theorem gVal_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (m : ℕ → ℕ) (gf Lf : ℕ → ℤ)
    (f1 f2 : ℕ) (hLf : f1 = 0 → f2 = 0 → SArr m Ly.pL 2 (I.t * I.k) Lf)
    {c j : ℕ} (hc : c < I.t) (hj : j < I.k - 1) (hS : Ly.F ≤ S) :
    HTB S gVal (fun cfg => GIn I Ly m gf f1 f2 c j cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1)
      (fun cfg => (GIn I Ly m gf f1 f2 c j cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1) ∧
        SReg cfg eV (gMode f1 f2 Lf I.k c j)) 52 := by
  let P : Config → Prop := fun cfg => GIn I Ly m gf f1 f2 c j cfg ∧ cfg.reg eJ = j ∧
    cfg.reg eK1 = I.k - 1
  have hPi : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ ellW) →
      (eC ∉ W ∧ ePa ∉ W ∧ ePx ∉ W ∧ ePy ∉ W ∧ eT1 ∉ W ∧ eF1 ∉ W ∧ eF2 ∉ W) → eJ ∉ W →
      Indep W P := fun hW h hJ =>
    (GIn.indep I Ly m gf f1 f2 c j hW h).and ((Indep.reg hJ (· = j)).and
      (Indep.reg (r := eK1) (fun h => by have := hW _ h; revert this; decide) (· = I.k - 1)))
  have hb : c * I.k + j < I.t * I.k := flat_idx_lt hc (by omega)
  have hb' : c * I.k + (I.k - 1) < I.t * I.k := flat_idx_lt hc (by omega)
  -- the memory of the entry: `L` lies below the written part of `g`
  have hLm : f1 = 0 → f2 = 0 → SArr (wrArr m Ly.pG 2 gf (c * (I.k - 1) + j)) Ly.pL 2
      (I.t * I.k) Lf := fun h1 h2 =>
    SArr.out (hLf h1 h2) (le_refl 2) (fun x hx => wrArr_of_out (le_refl 2) hx)
      (by have := hL.g; omega)
  -- the gradient branch
  have hf := hL.fits hS
  have hgrad : f1 = 0 → f2 = 0 → HTB S (.seq (sload eV ePy) (.seq (sload eW eT1) (ssub eV eV eW)))
      P (fun cfg => P cfg ∧ SReg cfg eV (gMode f1 f2 Lf I.k c j)) 50 := fun h1 h2 => by
    have g1 := HTB.sload (S := S) (P := P) (d := eV) (p := ePy) (a := Ly.pL + (c * I.k + j) * 2)
      (z := Lf (c * I.k + j)) (by decide) (by decide) (by decide)
      (hPi (by decide) (by decide) (by decide)) (by omega)
    have g2 := HTB.sload (S := S) (P := fun cfg => P cfg ∧ SReg cfg eV (Lf (c * I.k + j))) (d := eW)
      (p := eT1) (a := Ly.pL + (c * I.k + (I.k - 1)) * 2) (z := Lf (c * I.k + (I.k - 1)))
      (by decide) (by decide) (by decide)
      ((hPi (by decide) (by decide) (by decide)).and (indep_sreg (by decide) (by decide) _))
      (by omega)
    have g3 := HTB.ssub (S := S) (P := P) (d := eV) (x := eV) (y := eW) (u := Lf (c * I.k + j))
      (v := Lf (c * I.k + (I.k - 1))) (by decide) (by decide) (by decide)
      (hPi (by decide) (by decide) (by decide))
    refine ((g1.pre fun cfg h => ⟨h, h.1.2.2.2.2.2.1, by
        rw [h.1.2.1]; exact hLm h1 h2 _ hb⟩).seq
      ((g2.pre fun cfg h => ⟨h, h.1.1.2.2.2.2.2.2.1, by
        rw [h.1.1.2.1]; exact hLm h1 h2 _ hb'⟩).seq
      (g3.pre fun cfg ⟨⟨h, hv⟩, hw⟩ => ⟨h, hv, hw⟩))).mono (fun _ h => h)
      (fun cfg ⟨h, hv⟩ => ⟨h, by simpa [gMode, h1, h2] using hv⟩) (by omega)
  -- the block branch
  have hblock : f1 = 0 → f2 ≠ 0 →
      HTB S (.seq (addc eT2 eC 1) (ifEq eT2 eF2 (sconst eV 1) (sconst eV 0)))
        P (fun cfg => P cfg ∧ SReg cfg eV (gMode f1 f2 Lf I.k c j)) 50 := fun h1 h2 =>
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg h => by
      refine ⟨(hPi (W := wregs (.seq (addc eT2 eC 1) (ifEq eT2 eF2 (sconst eV 1) (sconst eV 0))))
        (by decide) (by decide) (by decide)).run (by decide) rfl rfl h, ?_⟩
      have hc' := h.1.2.2.1
      have hf2 := h.1.2.2.2.2.2.2.2.2
      simp only [gMode, h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]
      by_cases he : c + 1 = f2
      · refine ⟨?_, ?_⟩ <;> simp +decide [run_ifEq, run_addc, Arith.sconst, hc', hf2, he, sgnBit]
      · refine ⟨?_, ?_⟩ <;> simp +decide [run_ifEq, run_addc, Arith.sconst, hc', hf2, he, sgnBit]
  -- the negative branch
  have hneg : f1 ≠ 0 →
      HTB S (.seq (addc eT2 ePx 1) (ifEq eT2 eF1 (sconst eV (-1)) (sconst eV 0)))
        P (fun cfg => P cfg ∧ SReg cfg eV (gMode f1 f2 Lf I.k c j)) 50 := fun h1 =>
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg h => by
      refine ⟨(hPi (W := wregs (.seq (addc eT2 ePx 1) (ifEq eT2 eF1 (sconst eV (-1))
        (sconst eV 0)))) (by decide) (by decide) (by decide)).run (by decide) rfl rfl h, ?_⟩
      have hpx := h.1.2.2.2.2.1
      have hf1 := h.1.2.2.2.2.2.2.2.1
      simp only [gMode, h1, ne_eq, not_false_eq_true, ↓reduceIte]
      by_cases he : c * (I.k - 1) + j + 1 = f1
      · refine ⟨?_, ?_⟩ <;> simp +decide [run_ifEq, run_addc, Arith.sconst, hpx, hf1, he, sgnBit]
      · refine ⟨?_, ?_⟩ <;> simp +decide [run_ifEq, run_addc, Arith.sconst, hpx, hf1, he, sgnBit]
  refine (HTB.ifz (HTB.ifz ?_ ?_) ?_).weaken (show 50 + 1 + 1 ≤ 52 by omega)
  · refine HTB.prop_pre (p := f1 = 0 ∧ f2 = 0) (fun ⟨h1, h2⟩ => hgrad h1 h2) |>.pre ?_
    exact fun cfg ⟨⟨h, h1⟩, h2⟩ => ⟨⟨by rw [← h.1.2.2.2.2.2.2.2.1, h1],
      by rw [← h.1.2.2.2.2.2.2.2.2, h2]⟩, h⟩
  · refine HTB.prop_pre (p := f1 = 0 ∧ f2 ≠ 0) (fun ⟨h1, h2⟩ => hblock h1 h2) |>.pre ?_
    exact fun cfg ⟨⟨h, h1⟩, h2⟩ => ⟨⟨by rw [← h.1.2.2.2.2.2.2.2.1, h1],
      by rw [← h.1.2.2.2.2.2.2.2.2]; exact h2⟩, h⟩
  · refine HTB.prop_pre (p := f1 ≠ 0) hneg |>.pre ?_ |>.weaken (show 50 ≤ 50 + 1 by omega)
    exact fun cfg ⟨h, h1⟩ => ⟨by rw [← h.1.2.2.2.2.2.2.2.1]; exact h1, h⟩

/-! ### One entry -/

theorem gIn_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (m : ℕ → ℕ) (gf Lf : ℕ → ℤ)
    (f1 f2 : ℕ) (hLf : f1 = 0 → f2 = 0 → SArr m Ly.pL 2 (I.t * I.k) Lf)
    {c j : ℕ} (hc : c < I.t) (hj : j < I.k - 1)
    (hg : gf (c * (I.k - 1) + j) = gMode f1 f2 Lf I.k c j) (hS : Ly.F ≤ S) :
    HTB S gIn (fun cfg => GIn I Ly m gf f1 f2 c j cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1)
      (fun cfg => GIn I Ly m gf f1 f2 c (j + 1) cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1)
      62 := by
  set a := c * (I.k - 1) + j with ha
  set v := gMode f1 f2 Lf I.k c j with hv
  have han : a < nDim I.t I.k := by rw [nDim_eq]; exact flat_idx_lt hc hj
  have h1 := gVal_specB I Ly hL m gf Lf f1 f2 hLf hc hj hS
  have h2 := HTB.sstore (S := S) (F := fun cfg => EG I Ly cfg ∧ cfg.reg eC = c ∧ cfg.reg ePx = a ∧
      cfg.reg ePy = Ly.pL + (c * I.k + j) * 2 ∧ cfg.reg eT1 = Ly.pL + (c * I.k + (I.k - 1)) * 2 ∧
      cfg.reg eF1 = f1 ∧ cfg.reg eF2 = f2 ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1)
    (p := ePa) (x := eV) (a := Ly.pG + a * 2) (z := v) (m := wrArr m Ly.pG 2 gf a)
    (by decide) (by decide) (by decide)
    ((EG.regIndep I Ly).mono (by decide) |>.and (by indep))
    (by have := hL.fits hS; omega)
  have h3 : HTB S (.seq (addc ePa ePa 2) (.seq (inc ePx) (addc ePy ePy 2)))
      (fun cfg => (EG I Ly cfg ∧ cfg.reg eC = c ∧ cfg.reg ePx = a ∧
        cfg.reg ePy = Ly.pL + (c * I.k + j) * 2 ∧
        cfg.reg eT1 = Ly.pL + (c * I.k + (I.k - 1)) * 2 ∧ cfg.reg eF1 = f1 ∧ cfg.reg eF2 = f2 ∧
        cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1) ∧ cfg.reg ePa = Ly.pG + a * 2 ∧
        cfg.mem = wrArr m Ly.pG 2 gf (a + 1))
      (fun cfg => GIn I Ly m gf f1 f2 c (j + 1) cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1) 6 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨hE, hc', hpx, hpy, ht1, hf1, hf2,
        hj', hk'⟩, hpa,
        hm⟩ => by
      have hr : ∀ r, r ∉ wregs (.seq (addc ePa ePa 2) (.seq (inc ePx) (addc ePy ePy 2))) →
          (RAM.run (.seq (addc ePa ePa 2) (.seq (inc ePx) (addc ePy ePy 2))) cfg).reg r =
            cfg.reg r := fun r hr => run_reg_of_not_mem (by decide) hr cfg
      have ha1 : c * (I.k - 1) + (j + 1) = a + 1 := by omega
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩, ?_, ?_⟩
      all_goals try (rw [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg, hm, ha1]
      · exact hc'
      · simp +decide [run_addc, run_inc, hpa, ha1]; ring
      · simp +decide [run_addc, run_inc, hpx, ha1]
      · simp +decide [run_addc, run_inc, hpy]; ring
      · exact ht1
      · exact hf1
      · exact hf2
      · exact hj'
      · exact hk'
  refine (h1.seq ((h2.pre fun cfg ⟨⟨⟨hE, hm, hc', hpa, hpx, hpy, ht1, hf1, hf2⟩, hj', hk'⟩, hv'⟩ =>
      ⟨⟨hE, hc', hpx, hpy, ht1, hf1, hf2, hj', hk'⟩, hv', hpa, hm⟩).seq
    (h3.pre fun cfg ⟨hF, _, hpa, hm⟩ => ⟨hF, hpa, by
      rw [hm, wrArr_succ, hg]; rfl⟩))).weaken (by omega)

/-! ### One cycle -/

theorem gOut_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (m : ℕ → ℕ) (gf Lf : ℕ → ℤ)
    (f1 f2 : ℕ) (hLf : f1 = 0 → f2 = 0 → SArr m Ly.pL 2 (I.t * I.k) Lf)
    (hg : ∀ c < I.t, ∀ j < I.k - 1, gf (c * (I.k - 1) + j) = gMode f1 f2 Lf I.k c j)
    {c : ℕ} (hc : c < I.t) (hS : Ly.F ≤ S) :
    HTB S gOut (fun cfg => GOut I Ly m gf f1 f2 c cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t)
      (fun cfg => GOut I Ly m gf f1 f2 (c + 1) cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t)
      ((I.k - 1) * 66 + 7) := by
  have hk := hL.k3
  have h0 : HTB S (.seq (.add eT1 ePy eK1) (.add eT1 eT1 eK1))
      (fun cfg => GOut I Ly m gf f1 f2 c cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t)
      (fun cfg => GIn I Ly m gf f1 f2 c 0 cfg ∧ cfg.reg eK1 = I.k - 1) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨hE, hm, hpa, hpx, hpy, hf1, hf2⟩,
        hc', _⟩ => by
      have hr : ∀ r, r ∉ wregs (.seq (.add eT1 ePy eK1) (.add eT1 eT1 eK1)) →
          (RAM.run (.seq (.add eT1 ePy eK1) (.add eT1 eT1 eK1)) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩, ?_⟩
      all_goals try (rw [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg, hm]; rfl
      · exact hc'
      · rw [hpa]; ring
      · rw [hpx]; rfl
      · rw [hpy]; ring
      · simp +decide [hpy, hE.k1]; ring
      · exact hf1
      · exact hf2
      · exact hE.k1
  have hl := HTB.forUpC (S := S) (i := eJ) (n := eK1) (N := I.k - 1) (body := gIn)
    (GIn I Ly m gf f1 f2 c) 62 (by decide) (by decide) (by decide)
    (fun j => by indep [GIn, eG_iff, QRegs])
    (fun j hj => gIn_specB I Ly hL m gf Lf f1 f2 hLf hc hj (hg c hc j hj) hS)
  have h3 : HTB S (addc ePy ePy 2)
      (fun cfg => GIn I Ly m gf f1 f2 c (I.k - 1) cfg ∧ cfg.reg eJ = I.k - 1 ∧
        cfg.reg eK1 = I.k - 1)
      (fun cfg => GOut I Ly m gf f1 f2 (c + 1) cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun cfg ⟨⟨hE, hm, hc', hpa, hpx, hpy, _, hf1, hf2⟩, _, _⟩ => by
      have hr : ∀ r, r ∉ wregs (addc ePy ePy 2) →
          (RAM.run (addc ePy ePy 2) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      have e1 : c * (I.k - 1) + (I.k - 1) = (c + 1) * (I.k - 1) := by rw [Nat.succ_mul]
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        ?_, ?_⟩
      all_goals try (rw [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg, hm, e1]
      · rw [hpa, e1]
      · rw [hpx, e1]
      · simp +decide [run_addc, hpy]
        rw [Nat.succ_mul]
        have : I.k = I.k - 1 + 1 := by omega
        nth_rewrite 4 [this]
        ring
      · exact hf1
      · exact hf2
      · exact hc'
      · exact hE.t
  refine (h0.seq (hl.seq h3)).weaken ?_
  omega

/-! ### The cut vector -/

/-- **The cut vector**: `gLoop` writes `gf` (`n` entries, flat) at `eG`, given that `gf` agrees
with `gMode` of the mode registers `eF1 = f1`, `eF2 = f2`. -/
theorem gLoop_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (m : ℕ → ℕ) (gf Lf : ℕ → ℤ)
    (f1 f2 : ℕ) (hLf : f1 = 0 → f2 = 0 → SArr m Ly.pL 2 (I.t * I.k) Lf)
    (hg : ∀ c < I.t, ∀ j < I.k - 1, gf (c * (I.k - 1) + j) = gMode f1 f2 Lf I.k c j)
    (hS : Ly.F ≤ S) :
    HTB S gLoop (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg eF1 = f1 ∧ cfg.reg eF2 = f2)
      (fun cfg => EG I Ly cfg ∧ cfg.mem = wrArr m Ly.pG 2 gf (I.t * (I.k - 1)) ∧
        cfg.reg eF1 = f1 ∧ cfg.reg eF2 = f2)
      (I.t * ((I.k - 1) * 66 + 11) + 8) := by
  have h0 : HTB S (.seq (mov ePa eG) (.seq (.const ePx 0) (mov ePy eL)))
      (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg eF1 = f1 ∧ cfg.reg eF2 = f2)
      (fun cfg => GOut I Ly m gf f1 f2 0 cfg ∧ cfg.reg qT = I.t) 5 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨hE, hm, hf1, hf2⟩ => by
      have hr : ∀ r, r ∉ wregs (.seq (mov ePa eG) (.seq (.const ePx 0) (mov ePy eL))) →
          (RAM.run (.seq (mov ePa eG) (.seq (.const ePx 0) (mov ePy eL))) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        ?_⟩
      all_goals try (rw [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg, hm, Nat.zero_mul]; rfl
      · simp +decide [run_mov, hE.g]
      · simp +decide [run_mov]
      · simp +decide [run_mov, hE.l]
      · exact hf1
      · exact hf2
      · exact hE.t
  have hl := HTB.forUpC (S := S) (i := eC) (n := qT) (N := I.t) (body := gOut)
    (GOut I Ly m gf f1 f2) ((I.k - 1) * 66 + 7) (by decide) (by decide) (by decide)
    (fun c => by indep [GOut, eG_iff, QRegs])
    (fun c hc => gOut_specB I Ly hL m gf Lf f1 f2 hLf hg hc hS)
  refine (h0.seq hl).mono (fun _ h => h)
    (fun cfg ⟨⟨hE, hm, _, _, _, hf1, hf2⟩, _, _⟩ => ⟨hE, hm, hf1, hf2⟩) ?_
  have : I.t * ((I.k - 1) * 66 + 7 + 4) = I.t * ((I.k - 1) * 66 + 11) := by ring
  omega

end STACS2027.Runtimes.QPRam
