module

public import Runtimes.ConvexQP.RAM.EllLayout
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: E1, the scan of the center

One nested pass over the reduced coordinates `(c, j)` (flat index `a = c (k−1) + j`) of the center
`As` (at `eA`): `eF1` becomes `enc negFind` (`0`, or the first flat index with `As_a < 0`, plus
one) and `eF2` becomes `enc overFind` (`0`, or the first cycle with block sum `> 2^p`, plus one).
By `negFind_eq` and `overFind_eq` these are the searches `firstNeg`, `firstOver` of E1. The memory
is unchanged; `O(n)` steps (`scan_specB`, below every `S ≥ pA + 2n`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

/-! ### The program -/

/-- One entry: `V := As_a`; if no negative entry was found yet and `As_a < 0`, `F1 := a + 1`;
`S1 += As_a`; advance (`ePa` the pointer, `ePx = a`). -/
def scanIn : Stmt :=
  .seq (sload eV ePa) (.seq (.ifz eF1 (.ifz eV .skip (addc eF1 ePx 1)) .skip)
    (.seq (sadd eS1 eS1 eV) (.seq (addc ePa ePa 2) (inc ePx))))

/-- One cycle `c = eC`: the block sum into `S1`; if no cycle was found yet and `2^p < S1`,
`F2 := c + 1`. -/
def scanOut : Stmt :=
  .seq (sconst eS1 0) (.seq (forUp eJ eK1 scanIn)
    (.seq (slt eT1 eP2 eS1) (.ifz eF2 (.ifz eT1 .skip (addc eF2 eC 1)) .skip)))

/-- **E1**: the scan. -/
def scan : Stmt :=
  .seq (.seq (.const eF1 0) (.seq (.const eF2 0) (.seq (mov ePa eA) (.const ePx 0))))
    (forUp eC qT scanOut)

theorem scan_wregs : ∀ r ∈ wregs scan, r ∈ ellW := by decide

theorem scan_stores : stores scan = false := by decide

/-! ### Invariants -/

/-- The registers of the scan at flat index `a` (pointer `pA + 2a`). -/
def ScR (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (a f1 f2 : ℕ) (cfg : Config) : Prop :=
  EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg ePa = Ly.pA + a * 2 ∧ cfg.reg ePx = a ∧
    cfg.reg eF1 = f1 ∧ cfg.reg eF2 = f2

/-- The negativity test. -/
def qNeg {I : Inst} (As : Idx I → ℤ) (a : ℕ) : Bool := decide (flatR As a < 0)

/-- The block-sum test. -/
def qOver {I : Inst} (p : ℕ) (As : Idx I → ℤ) (c : ℕ) : Bool := decide ((2 : ℤ) ^ p < bsum As c)

/-- Before entry `j` of cycle `c`. -/
def ScanIn (I : Inst) (Ly : Lay) (As : Idx I → ℤ) (m : ℕ → ℕ) (c j : ℕ) (cfg : Config) : Prop :=
  ScR I Ly m (c * (I.k - 1) + j) (enc ((List.range (c * (I.k - 1) + j)).find? (qNeg As)))
    (enc ((List.range c).find? (qOver (prec I.t I.k) As))) cfg ∧ cfg.reg eC = c ∧
    SReg cfg eS1 (∑ j' ∈ Finset.range j, flatR As (c * (I.k - 1) + j'))

/-- Before cycle `c`. -/
def ScanOut (I : Inst) (Ly : Lay) (As : Idx I → ℤ) (m : ℕ → ℕ) (c : ℕ) (cfg : Config) : Prop :=
  ScR I Ly m (c * (I.k - 1)) (enc ((List.range (c * (I.k - 1))).find? (qNeg As)))
    (enc ((List.range c).find? (qOver (prec I.t I.k) As))) cfg

theorem ScR.indep (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (a f1 f2 : ℕ) {W : List ℕ}
    (hW : ∀ r ∈ W, r ∈ ellW) (h : ePa ∉ W ∧ ePx ∉ W ∧ eF1 ∉ W ∧ eF2 ∉ W) :
    Indep W (ScR I Ly m a f1 f2) :=
  (EG.indep hW).and ((Indep.mem (· = m)).and ((Indep.reg h.1 (· = Ly.pA + a * 2)).and
    ((Indep.reg h.2.1 (· = a)).and ((Indep.reg h.2.2.1 (· = f1)).and
      (Indep.reg h.2.2.2 (· = f2))))))

/-! ### One entry -/

theorem scanIn_specB (I : Inst) (Ly : Lay) (As : Idx I → ℤ) (m : ℕ → ℕ)
    (hA : SArr m Ly.pA 2 (nDim I.t I.k) (flatR As)) {c j : ℕ} (hc : c < I.t) (hj : j < I.k - 1)
    (hAS : Ly.pA + nDim I.t I.k * 2 ≤ S) :
    HTB S scanIn (fun cfg => ScanIn I Ly As m c j cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1)
      (fun cfg => ScanIn I Ly As m c (j + 1) cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1) 52 := by
  set a := c * (I.k - 1) + j with ha
  have han : a < nDim I.t I.k := by
    rw [nDim_eq]
    have : (c + 1) * (I.k - 1) ≤ I.t * (I.k - 1) := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul] at this; omega
  set z := flatR As a with hz
  set f1 := enc ((List.range a).find? (qNeg As)) with hf1
  set f2 := enc ((List.range c).find? (qOver (prec I.t I.k) As)) with hf2
  set s := ∑ j' ∈ Finset.range j, flatR As (c * (I.k - 1) + j') with hs
  set f1' := if f1 = 0 then (if z < 0 then a + 1 else 0) else f1 with hf1'
  have hf1e : enc ((List.range (a + 1)).find? (qNeg As)) = f1' := by
    rw [find_range_succ, hf1', hf1]
    by_cases hz0 : z < 0 <;> simp [qNeg, hz0, ← hz]
  -- the frame of the arithmetic steps
  let G : ℕ → Config → Prop := fun f cfg =>
    ScR I Ly m a f f2 cfg ∧ cfg.reg eC = c ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1
  have hG : ∀ f {W : List ℕ}, (∀ r ∈ W, r ∈ ellW) → eC ∉ W ∧ eJ ∉ W ∧ eK1 ∉ W →
      (ePa ∉ W ∧ ePx ∉ W ∧ eF1 ∉ W ∧ eF2 ∉ W) → Indep W (G f) := fun f {W} hW h1 h2 =>
    (ScR.indep I Ly m a f f2 hW h2).and ((Indep.reg h1.1 (· = c)).and
      ((Indep.reg h1.2.1 (· = j)).and (Indep.reg h1.2.2 (· = I.k - 1))))
  have h1 := HTB.sload (S := S) (P := fun cfg => G f1 cfg ∧ SReg cfg eS1 s) (d := eV) (p := ePa)
    (a := Ly.pA + a * 2) (z := z) (by decide) (by decide) (by decide)
    ((hG f1 (by decide) (by decide) (by decide)).and (indep_sreg (by decide) (by decide) s))
    (by omega)
  have h2 : HTB S (.ifz eF1 (.ifz eV .skip (addc eF1 ePx 1)) .skip)
      (fun cfg => (G f1 cfg ∧ SReg cfg eS1 s) ∧ SReg cfg eV z)
      (fun cfg => G f1' cfg ∧ SReg cfg eS1 s ∧ SReg cfg eV z) 6 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨⟨hE, hm, hpa, hpx, h1', h2'⟩,
        hc', hj', hk'⟩,
        hs0, hs1⟩, hv0, hv1⟩ => by
      have hr : ∀ r, r ∉ wregs (.ifz eF1 (.ifz eV .skip (addc eF1 ePx 1)) .skip) →
          (RAM.run (.ifz eF1 (.ifz eV .skip (addc eF1 ePx 1)) .skip) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      refine ⟨⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_, ?_⟩,
        ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      all_goals try (rwa [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg]; exact hm
      · simp only [run_ifz', run_skip]
        rw [hf1']
        by_cases hf : f1 = 0
        · have hz' : (cfg.reg eV = 0) ↔ ¬ z < 0 := by
            rw [hv0, sgnBit]; split_ifs with h <;> simp [h]
          simp only [h1', hf, ↓reduceIte]
          by_cases hz0 : z < 0
          · have : cfg.reg eV ≠ 0 := fun h => hz'.mp h hz0
            simp +decide [this, hz0, run_addc, hpx]
          · simp [hz'.mpr hz0, hz0, h1', hf]
        · simp [h1', hf]
  have h3 := HTB.sadd (S := S) (P := G f1') (d := eS1) (x := eS1) (y := eV) (u := s) (v := z)
    (by decide) (by decide) (by decide) (hG f1' (by decide) (by decide) (by decide))
  have h4 : HTB S (.seq (addc ePa ePa 2) (inc ePx)) (fun cfg => G f1' cfg ∧ SReg cfg eS1 (s + z))
      (fun cfg => ScanIn I Ly As m c (j + 1) cfg ∧ cfg.reg eJ = j ∧ cfg.reg eK1 = I.k - 1) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨hE, hm, hpa, hpx, h1', h2'⟩,
        hc', hj', hk'⟩,
        hs0, hs1⟩ => by
      have hr : ∀ r, r ∉ wregs (.seq (addc ePa ePa 2) (inc ePx)) →
          (RAM.run (.seq (addc ePa ePa 2) (inc ePx)) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      have ha1 : c * (I.k - 1) + (j + 1) = a + 1 := by omega
      refine ⟨⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_, ?_⟩,
        ?_, ?_⟩, ?_, ?_⟩
      all_goals try (rw [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg]; exact hm
      · simp +decide [run_addc, run_inc, hpa, ha1]; ring
      · simp +decide [run_addc, run_inc, hpx, ha1]
      · rw [ha1, hf1e]; exact h1'
      · exact h2'
      · exact hc'
      · refine ⟨?_, ?_⟩ <;> rw [hr _ (by decide)]
        · rw [Finset.sum_range_succ]; exact hs0
        · rw [Finset.sum_range_succ]; exact hs1
      · exact hj'
      · exact hk'
  refine ((h1.pre fun cfg ⟨⟨⟨hE, hm, hpa, hpx, h1', h2'⟩, hc', hs'⟩, hj', hk'⟩ =>
      ⟨⟨⟨⟨hE, hm, hpa, hpx, h1', h2'⟩, hc', hj', hk'⟩, hs'⟩, hpa, by rw [hm]; exact hA a han⟩).seq
    (h2.seq ((h3.pre fun cfg ⟨hg, hs', hv⟩ => ⟨hg, hs', hv⟩).seq h4))).weaken (by omega)

/-! ### One cycle -/

theorem scanOut_specB (I : Inst) (Ly : Lay) (As : Idx I → ℤ) (m : ℕ → ℕ)
    (hA : SArr m Ly.pA 2 (nDim I.t I.k) (flatR As)) {c : ℕ} (hc : c < I.t)
    (hAS : Ly.pA + nDim I.t I.k * 2 ≤ S) :
    HTB S scanOut (fun cfg => ScanOut I Ly As m c cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t)
      (fun cfg => ScanOut I Ly As m (c + 1) cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t)
      ((I.k - 1) * 56 + 34) := by
  set a := c * (I.k - 1) + (I.k - 1) with ha
  have ha' : (c + 1) * (I.k - 1) = a := by rw [ha, Nat.succ_mul]
  set f1 := enc ((List.range a).find? (qNeg As)) with hf1
  set f2 := enc ((List.range c).find? (qOver (prec I.t I.k) As)) with hf2
  have hb : bsum As c = ∑ j' ∈ Finset.range (I.k - 1), flatR As (c * (I.k - 1) + j') := rfl
  set f2' := if f2 = 0 then (if (2 : ℤ) ^ prec I.t I.k < bsum As c then c + 1 else 0) else f2
    with hf2'
  have hf2e : enc ((List.range (c + 1)).find? (qOver (prec I.t I.k) As)) = f2' := by
    rw [find_range_succ, hf2', hf2]
    by_cases h0 : (2 : ℤ) ^ prec I.t I.k < bsum As c <;> simp [qOver, h0]
  have h0 := HTB.sconst (S := S) (P := fun cfg => ScanOut I Ly As m c cfg ∧ cfg.reg eC = c ∧
    cfg.reg qT = I.t) (d := eS1) 0 (by indep [ScanOut, ScR, eG_iff, QRegs])
  have hl := HTB.forUpC (S := S) (i := eJ) (n := eK1) (N := I.k - 1) (body := scanIn)
    (ScanIn I Ly As m c) 52 (by decide) (by decide) (by decide)
    (fun j => by indep [ScanIn, ScR, eG_iff, QRegs, SReg])
    (fun j hj => scanIn_specB I Ly As m hA hc hj hAS)
  have h3 := HTB.slt (S := S) (P := fun cfg => ScanIn I Ly As m c (I.k - 1) cfg) (d := eT1) (x :=
      eP2)
    (y := eS1) (u := (2 : ℤ) ^ prec I.t I.k) (v := bsum As c) (by decide) (by decide)
    (by indep [ScanIn, ScR, eG_iff, QRegs, SReg])
  have h4 : HTB S (.ifz eF2 (.ifz eT1 .skip (addc eF2 eC 1)) .skip)
      (fun cfg => ScanIn I Ly As m c (I.k - 1) cfg ∧
        cfg.reg eT1 = if (2 : ℤ) ^ prec I.t I.k < bsum As c then 1 else 0)
      (fun cfg => ScanOut I Ly As m (c + 1) cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t) 6 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨hE, hm, hpa, hpx, h1', h2'⟩,
        hc', _⟩, ht⟩ => by
      have hr : ∀ r, r ∉ wregs (.ifz eF2 (.ifz eT1 .skip (addc eF2 eC 1)) .skip) →
          (RAM.run (.ifz eF2 (.ifz eT1 .skip (addc eF2 eC 1)) .skip) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_, ?_⟩,
        ?_, ?_⟩
      all_goals try (rw [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg]; exact hm
      · rw [hpa, ha']
      · rw [hpx, ha']
      · rw [h1', ha']
      · rw [hf2e, hf2']
        rw [← hf2] at h2'
        simp only [run_ifz', run_skip]
        by_cases hf : f2 = 0
        · by_cases h0 : (2 : ℤ) ^ prec I.t I.k < bsum As c
          · simp +decide [h2', hf, h0, ht, run_addc, hc']
          · simp [h2', hf, h0, ht]
        · simp [h2', hf]
      · exact hc'
      · exact hE.t
  refine ((h0.post fun cfg ⟨⟨⟨hE, hm, hpa, hpx, h1', h2'⟩, hc', hT⟩, hs⟩ =>
      ⟨⟨⟨hE, hm, by simpa using hpa, by simpa using hpx, by simpa using h1', h2'⟩, hc',
        by simpa using hs⟩, hE.k1⟩).seq
    (hl.seq ((h3.pre fun cfg ⟨hI, _, _⟩ => ⟨hI, hI.1.1.p2, by rw [hb]; exact hI.2.2⟩).seq
      h4))).weaken (by omega)

/-! ### The scan -/

/-- **E1**: after `scan`, `eF1 = enc (negFind As)` and `eF2 = enc (overFind p As)`; the memory
and the registers of `EG` are unchanged. -/
theorem scan_specB (I : Inst) (Ly : Lay) (As : Idx I → ℤ) (m : ℕ → ℕ)
    (hA : SArr m Ly.pA 2 (nDim I.t I.k) (flatR As)) (hAS : Ly.pA + nDim I.t I.k * 2 ≤ S) :
    HTB S scan (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg eF1 = enc (negFind As) ∧
        cfg.reg eF2 = enc (overFind (prec I.t I.k) As))
      (I.t * ((I.k - 1) * 56 + 38) + 10) := by
  have h0 : HTB S (.seq (.const eF1 0) (.seq (.const eF2 0) (.seq (mov ePa eA) (.const ePx 0))))
      (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => ScanOut I Ly As m 0 cfg ∧ cfg.reg qT = I.t) 5 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨hE, hm⟩ => by
      have hr : ∀ r, r ∉ wregs (.seq (.const eF1 0) (.seq (.const eF2 0) (.seq (mov ePa eA)
          (.const ePx 0)))) → (RAM.run (.seq (.const eF1 0) (.seq (.const eF2 0)
            (.seq (mov ePa eA) (.const ePx 0)))) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [run_mem_of_stores (by decide) rfl cfg]; exact hm
      · simp +decide [run_mov, hE.a]
      · simp +decide
      · simp +decide [run_mov, enc]
      · simp +decide [run_mov, enc]
      · rw [hr _ (by decide)]; exact hE.t
  have hl := HTB.forUpC (S := S) (i := eC) (n := qT) (N := I.t) (body := scanOut)
    (ScanOut I Ly As m) ((I.k - 1) * 56 + 34) (by decide) (by decide) (by decide)
    (fun c => by indep [ScanOut, ScR, eG_iff, QRegs])
    (fun c hc => scanOut_specB I Ly As m hA hc hAS)
  refine (h0.seq hl).mono (fun _ h => h) (fun cfg ⟨⟨hE, hm, _, _, h1, h2⟩, _, _⟩ =>
    ⟨hE, hm, by rw [h1, negFind, nDim_eq] at *; exact h1, h2⟩)
    (by have : I.t * ((I.k - 1) * 56 + 34 + 4) = I.t * ((I.k - 1) * 56 + 38) := by ring
        omega)

end STACS2027.Runtimes.QPRam
