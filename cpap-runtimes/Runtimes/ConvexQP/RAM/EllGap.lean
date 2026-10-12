module

public import Runtimes.ConvexQP.RAM.EllFeas
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: E2, the gap and the success test

With `Xs` flat at `qBX` and `L = H Xs` flat at `eL`, one nested pass computes
`S1 = ∑_{c,j} L_{c,j} Xs_{c,j}` and, cycle by cycle, the running minimum `π_c = min_j L_{c,j}`
(`pmin`) summed into `S3`; then `gap = S1 − 2^p · S3` (`gapB_specB`). Since `∑_j Xs_{c,j} = 2^p`
for the completion of a center, this is `I.gap Xs` (`gapN_eq`). The test `testB` sets
`eDn := [gap · E² ≤ 4^p]` (`testB_specB`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

/-! ### The abstract quantities -/

/-- The running minimum of `Lf (c k + j')` over `j' < max j 1`. -/
def pmin (Lf : ℕ → ℤ) (k c : ℕ) : ℕ → ℤ
  | 0 => Lf (c * k)
  | j + 1 => min (pmin Lf k c j) (Lf (c * k + j))

theorem pmin_le (Lf : ℕ → ℤ) (k c : ℕ) :
    ∀ j, (∀ j' < j, pmin Lf k c j ≤ Lf (c * k + j')) ∧ pmin Lf k c j ≤ Lf (c * k)
  | 0 => ⟨fun _ h => absurd h (Nat.not_lt_zero _), le_rfl⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := pmin_le Lf k c j
    refine ⟨fun j' hj' => ?_, (min_le_left _ _).trans h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | rfl
    · exact (min_le_left _ _).trans (h1 j' h)
    · exact min_le_right _ _

theorem pmin_mem (Lf : ℕ → ℤ) (k c : ℕ) :
    ∀ j, ∃ j', (j' = 0 ∨ j' < j) ∧ pmin Lf k c j = Lf (c * k + j')
  | 0 => ⟨0, Or.inl rfl, by simp [pmin]⟩
  | j + 1 => by
    obtain ⟨j', hj', he⟩ := pmin_mem Lf k c j
    simp only [pmin]
    rcases le_total (pmin Lf k c j) (Lf (c * k + j)) with h | h
    · exact ⟨j', by omega, by rw [min_eq_left h, he]⟩
    · exact ⟨j, by omega, by rw [min_eq_right h]⟩

/-- `∑_{c' < c} ∑_{j < k} L_{c',j} Xs_{c',j}`. -/
def sxl (Xf Lf : ℕ → ℤ) (k c : ℕ) : ℤ :=
  ∑ c' ∈ Finset.range c, ∑ j ∈ Finset.range k, Lf (c' * k + j) * Xf (c' * k + j)

/-- `∑_{c' < c} π_{c'}`. -/
def spi (Lf : ℕ → ℤ) (k c : ℕ) : ℤ := ∑ c' ∈ Finset.range c, pmin Lf k c' k

/-- The gap as the RAM computes it. -/
def gapN (Xf Lf : ℕ → ℤ) (t k p : ℕ) : ℤ := sxl Xf Lf k t - spi Lf k t * 2 ^ p

theorem pi_eq_pmin (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (c : Fin I.t) (hk : 0 < I.k) :
    I.pi Xs c = pmin (flat (I.L Xs)) I.k c I.k := by
  refine Inst.pi_eq_of I Xs c (fun j => ?_) ?_
  · have := (pmin_le (flat (I.L Xs)) I.k c I.k).1 j j.2
    rwa [flat_apply] at this
  · obtain ⟨j', hj', he⟩ := pmin_mem (flat (I.L Xs)) I.k c I.k
    have hj : j' < I.k := by omega
    refine ⟨⟨j', hj⟩, ?_⟩
    rw [he, show (c : ℕ) * I.k + j' = (c : ℕ) * I.k + (⟨j', hj⟩ : Fin I.k) from rfl, flat_apply]

/-- **The gap as computed** (`∑_j Xs_{c,j} = 2^p` for every cycle). -/
theorem gapN_eq (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (p : ℕ) (hk : 0 < I.k)
    (hsum : ∀ c, ∑ j, Xs c j = 2 ^ p) :
    gapN (flat Xs) (flat (I.L Xs)) I.t I.k p = I.gap Xs := by
  unfold gapN sxl spi Inst.gap
  have e1 : ∀ c : Fin I.t, ∑ j ∈ Finset.range I.k,
      flat (I.L Xs) (c * I.k + j) * flat Xs (c * I.k + j) = ∑ j, I.L Xs c j * Xs c j := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range (fun j => flat (I.L Xs) (c * I.k + j) * flat Xs (c * I.k + j))]
    exact Finset.sum_congr rfl fun j _ => by rw [flat_apply, flat_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun c => ∑ j ∈ Finset.range I.k,
      flat (I.L Xs) (c * I.k + j) * flat Xs (c * I.k + j)),
    ← Fin.sum_univ_eq_sum_range (fun c => pmin (flat (I.L Xs)) I.k c I.k)]
  simp only [e1, ← pi_eq_pmin I Xs _ hk, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hsum c, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ### The program -/

/-- One entry: `S1 += L · Xs`; `S2 := min (S2, L)`; advance. -/
def gpIn : Stmt :=
  .seq (sload eV ePx) (.seq (sload eW ePy) (.seq (smul eV eW eV)
    (.seq (sadd eS1 eS1 eV) (.seq (slt eT1 eW eS2) (.seq (.ifz eT1 .skip (smov eS2 eW))
    (.seq (addc ePx ePx 2) (addc ePy ePy 2)))))))

/-- One cycle: `S2 := L_{c,0}`, the entries, `S3 += S2`. -/
def gpOut : Stmt := .seq (sload eS2 ePy) (.seq (forUp eJ qK gpIn) (sadd eS3 eS3 eS2))

/-- **E2 (3)**: `S1 := ∑ L Xs − 2^p ∑_c π_c`. -/
def gapB : Stmt :=
  .seq (.seq (mov ePx qBX) (.seq (mov ePy eL) (.seq (sconst eS1 0) (sconst eS3 0))))
    (.seq (forUp eC qT gpOut) (.seq (smul eS3 eS3 eP2) (ssub eS1 eS1 eS3)))

/-- **E2 (4)**: `eDn := [S1 · E² ≤ 4^p]`. -/
def testB : Stmt :=
  .seq (sofNat eV qE) (.seq (smul eV eV eV) (.seq (smul eS1 eS1 eV)
    (.seq (.add eT1 qP qP) (.seq (pow2N eT2 eT1) (.seq (sofNat eW eT2) (sle eDn eS1 eW))))))

/-! ### Invariants -/

/-- The registers at flat index `b`. -/
def GpB (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (b : ℕ) (cfg : Config) : Prop :=
  EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg ePx = Ly.pX + b * 2 ∧ cfg.reg ePy = Ly.pL + b * 2

/-- Before entry `j` of cycle `c`. -/
def GpIn (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (Xf Lf : ℕ → ℤ) (c j : ℕ) (cfg : Config) : Prop :=
  GpB I Ly m (c * I.k + j) cfg ∧ cfg.reg eC = c ∧
    SReg cfg eS1 (sxl Xf Lf I.k c +
      ∑ j' ∈ Finset.range j, Lf (c * I.k + j') * Xf (c * I.k + j')) ∧
    SReg cfg eS2 (pmin Lf I.k c j) ∧ SReg cfg eS3 (spi Lf I.k c)

/-- Before cycle `c`. -/
def GpOut (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (Xf Lf : ℕ → ℤ) (c : ℕ) (cfg : Config) : Prop :=
  GpB I Ly m (c * I.k) cfg ∧ SReg cfg eS1 (sxl Xf Lf I.k c) ∧ SReg cfg eS3 (spi Lf I.k c)

theorem GpB.indep (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (b : ℕ) {W : List ℕ}
    (hW : ∀ r ∈ W, r ∈ ellW) (h : ePx ∉ W ∧ ePy ∉ W) : Indep W (GpB I Ly m b) :=
  (EG.indep hW).and ((Indep.mem (· = m)).and ((Indep.reg h.1 (· = Ly.pX + b * 2)).and
    (Indep.reg h.2 (· = Ly.pL + b * 2))))

/-! ### One entry -/

theorem gpIn_specB (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (Xf Lf : ℕ → ℤ)
    (hX : SArr m Ly.pX 2 (I.t * I.k) Xf) (hLf : SArr m Ly.pL 2 (I.t * I.k) Lf)
    (hz : ZeroFrom m Ly.F) (Bx : ℕ) (hBx : ∀ b < I.t * I.k, Nat.size (Xf b).natAbs ≤ Bx)
    {c j : ℕ} (hc : c < I.t) (hj : j < I.k) (hL : Ly.Ok I) (hS : Ly.F + 2 * Bx ≤ S) :
    HTB S gpIn (fun cfg => GpIn I Ly m Xf Lf c j cfg ∧ cfg.reg eJ = j ∧ cfg.reg qK = I.k)
      (fun cfg => GpIn I Ly m Xf Lf c (j + 1) cfg ∧ cfg.reg eJ = j ∧ cfg.reg qK = I.k)
      (31 * Bx + 126) := by
  set b := c * I.k + j with hb
  have hbt : b < I.t * I.k := flat_idx_lt hc hj
  set x := Xf b
  set l := Lf b
  set s1 := sxl Xf Lf I.k c + ∑ j' ∈ Finset.range j, Lf (c * I.k + j') * Xf (c * I.k + j')
  set mn := pmin Lf I.k c j
  set s3 := spi Lf I.k c
  have hZ : ∀ cfg, GpB I Ly m b cfg → ZeroFrom cfg.mem (cfg.reg rFREE) := fun cfg h => by
    rw [h.2.1, h.1.free]; exact hz
  have hf := hL.fits (S := S) (by omega)
  have hxB : Nat.size x.natAbs ≤ Bx := hBx b hbt
  -- frames
  let G0 : Config → Prop := fun cfg => GpB I Ly m b cfg ∧ cfg.reg eC = c ∧ cfg.reg eJ = j ∧
    cfg.reg qK = I.k
  have hG0 : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ ellW) → ePx ∉ W ∧ ePy ∉ W → eC ∉ W ∧ eJ ∉ W →
      Indep W G0 := fun hW h1 h2 =>
    (GpB.indep I Ly m b hW h1).and ((Indep.reg h2.1 (· = c)).and ((Indep.reg h2.2 (· = j)).and
      (Indep.reg (fun h => by have := hW _ h; revert this; decide) (· = I.k))))
  have h1 := HTB.sload (S := S) (P := fun cfg => G0 cfg ∧ SReg cfg eS1 s1 ∧ SReg cfg eS2 mn ∧
      SReg cfg eS3 s3) (d := eV) (p := ePx) (a := Ly.pX + b * 2) (z := x)
    (by decide) (by decide) (by decide)
    ((hG0 (by decide) (by decide) (by decide)).and ((indep_sreg (by decide) (by decide) s1).and
      ((indep_sreg (by decide) (by decide) mn).and (indep_sreg (by decide) (by decide) s3))))
    (by omega)
  have h2 := HTB.sload (S := S) (P := fun cfg => (G0 cfg ∧ SReg cfg eS1 s1 ∧ SReg cfg eS2 mn ∧
      SReg cfg eS3 s3) ∧ SReg cfg eV x) (d := eW) (p := ePy) (a := Ly.pL + b * 2) (z := l)
    (by decide) (by decide) (by decide)
    (((hG0 (by decide) (by decide) (by decide)).and ((indep_sreg (by decide) (by decide) s1).and
      ((indep_sreg (by decide) (by decide) mn).and (indep_sreg (by decide) (by decide) s3)))).and
      (indep_sreg (by decide) (by decide) x)) (by omega)
  have h3 := HTB.smul (S := S) (P := fun cfg => (G0 cfg ∧ SReg cfg eS1 s1 ∧ SReg cfg eS2 mn ∧
      SReg cfg eS3 s3) ∧ SReg cfg eW l) (d := eV) (x := eW) (y := eV) (u := l) (v := x)
    (by decide) (by decide) (by decide)
    (((hG0 (by decide) (by decide) (by decide)).and ((indep_sreg (by decide) (by decide) s1).and
      ((indep_sreg (by decide) (by decide) mn).and (indep_sreg (by decide) (by decide) s3)))).and
      (indep_sreg (by decide) (by decide) l))
    (fun cfg h => hZ cfg h.1.1.1) (fun cfg h => by rw [h.1.1.1.1.free]; omega)
  have h4 := HTB.sadd (S := S) (P := fun cfg => (G0 cfg ∧ SReg cfg eS2 mn ∧ SReg cfg eS3 s3) ∧
      SReg cfg eW l) (d := eS1) (x := eS1) (y := eV) (u := s1) (v := l * x)
    (by decide) (by decide) (by decide)
    (((hG0 (by decide) (by decide) (by decide)).and ((indep_sreg (by decide) (by decide) mn).and
      (indep_sreg (by decide) (by decide) s3))).and (indep_sreg (by decide) (by decide) l))
  have h5 := HTB.slt (S := S) (P := fun cfg => (G0 cfg ∧ SReg cfg eS3 s3 ∧ SReg cfg eS1 (s1 + l *
      x)) ∧
      SReg cfg eW l ∧ SReg cfg eS2 mn) (d := eT1) (x := eW) (y := eS2) (u := l) (v := mn)
    (by decide) (by decide)
    (((hG0 (by decide) (by decide) (by decide)).and ((indep_sreg (by decide) (by decide) s3).and
      (indep_sreg (by decide) (by decide) _))).and ((indep_sreg (by decide) (by decide) l).and
      (indep_sreg (by decide) (by decide) mn)))
  have h6 : HTB S (.ifz eT1 .skip (smov eS2 eW))
      (fun cfg => ((G0 cfg ∧ SReg cfg eS3 s3 ∧ SReg cfg eS1 (s1 + l * x)) ∧ SReg cfg eW l ∧
        SReg cfg eS2 mn) ∧ cfg.reg eT1 = if l < mn then 1 else 0)
      (fun cfg => G0 cfg ∧ SReg cfg eS3 s3 ∧ SReg cfg eS1 (s1 + l * x) ∧
        SReg cfg eS2 (pmin Lf I.k c (j + 1))) 6 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨⟨⟨hE, hm, hpx, hpy⟩, hc', hj',
        hk'⟩, hs3, hs1⟩,
        hw, hmn⟩, ht⟩ => by
      have hr : ∀ r, r ∉ wregs (.ifz eT1 .skip (smov eS2 eW)) →
          (RAM.run (.ifz eT1 .skip (smov eS2 eW)) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      refine ⟨⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩,
        ?_, ?_, ?_⟩
      all_goals try (rw [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg, hm]
      · exact hpx
      · exact hpy
      · exact hc'
      · exact hj'
      · exact hk'
      · exact ⟨by rw [hr _ (by decide)]; exact hs3.1, by rw [hr _ (by decide)]; exact hs3.2⟩
      · exact ⟨by rw [hr _ (by decide)]; exact hs1.1, by rw [hr _ (by decide)]; exact hs1.2⟩
      · -- the running minimum
        have hmin : pmin Lf I.k c (j + 1) = if l < mn then l else mn := by
          simp only [pmin]
          split_ifs with h
          · exact min_eq_right h.le
          · exact min_eq_left (not_lt.mp h)
        rw [hmin]
        obtain ⟨hw0, hw1⟩ := hw
        obtain ⟨hm0, hm1⟩ := hmn
        by_cases h : l < mn
        · have : cfg.reg eT1 ≠ 0 := by rw [ht]; simp [h]
          refine ⟨?_, ?_⟩ <;> simp +decide [run_ifz', this, Arith.smov, run_mov, hw0, hw1, h]
        · have : cfg.reg eT1 = 0 := by rw [ht]; simp [h]
          refine ⟨?_, ?_⟩ <;> simp +decide [run_ifz', this, hm0, hm1, h]
  have h7 : HTB S (.seq (addc ePx ePx 2) (addc ePy ePy 2))
      (fun cfg => G0 cfg ∧ SReg cfg eS3 s3 ∧ SReg cfg eS1 (s1 + l * x) ∧
        SReg cfg eS2 (pmin Lf I.k c (j + 1)))
      (fun cfg => GpIn I Ly m Xf Lf c (j + 1) cfg ∧ cfg.reg eJ = j ∧ cfg.reg qK = I.k) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨hE, hm, hpx, hpy⟩, hc', hj',
        hk'⟩, hs3, hs1,
        hmn⟩ => by
      have hr : ∀ r, r ∉ wregs (.seq (addc ePx ePx 2) (addc ePy ePy 2)) →
          (RAM.run (.seq (addc ePx ePx 2) (addc ePy ePy 2)) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      have hb1 : c * I.k + (j + 1) = b + 1 := by omega
      refine ⟨⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_⟩, ?_, ?_, ?_,
        ?_⟩, ?_, ?_⟩
      all_goals try (rw [hr _ (by decide)])
      · rw [run_mem_of_stores (by decide) rfl cfg, hm]
      · simp +decide [run_addc, hpx, hb1]; ring
      · simp +decide [run_addc, hpy, hb1]; ring
      · exact hc'
      · refine ⟨?_, ?_⟩
        · rw [hr _ (by decide), Finset.sum_range_succ, ← add_assoc]; exact hs1.1
        · rw [hr _ (by decide), Finset.sum_range_succ, ← add_assoc]; exact hs1.2
      · exact ⟨by rw [hr _ (by decide)]; exact hmn.1, by rw [hr _ (by decide)]; exact hmn.2⟩
      · exact ⟨by rw [hr _ (by decide)]; exact hs3.1, by rw [hr _ (by decide)]; exact hs3.2⟩
      · exact hj'
      · exact hk'
  refine ((h1.pre fun cfg ⟨⟨⟨hE, hm, hpx, hpy⟩, hc', hs1, hmn, hs3⟩, hj', hk'⟩ =>
      ⟨⟨⟨⟨hE, hm, hpx, hpy⟩, hc', hj', hk'⟩, hs1, hmn, hs3⟩, hpx, by
        rw [hm]; exact hX b hbt⟩).seq
    ((h2.pre fun cfg h => ⟨h, h.1.1.1.2.2.2, by rw [h.1.1.1.2.1]; exact hLf b hbt⟩).seq
    ((h3.pre fun cfg ⟨⟨⟨hg, hs1, hmn, hs3⟩, hv⟩, hw⟩ => ⟨⟨⟨hg, hs1, hmn, hs3⟩, hw⟩, hw, hv⟩).seq
    ((h4.pre fun cfg ⟨⟨⟨hg, hs1, hmn, hs3⟩, hw⟩, hv⟩ => ⟨⟨⟨hg, hmn, hs3⟩, hw⟩, hs1, hv⟩).seq
    ((h5.pre fun cfg ⟨⟨⟨hg, hmn, hs3⟩, hw⟩, hs1⟩ => ⟨⟨⟨hg, hs3, hs1⟩, hw, hmn⟩, hw, hmn⟩).seq
      (h6.seq h7)))))).weaken ?_
  have : smulCost x ≤ 31 * Bx + 35 := smulCost_le (hBx b hbt)
  omega

/-! ### One cycle -/

theorem gpOut_specB (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (Xf Lf : ℕ → ℤ)
    (hX : SArr m Ly.pX 2 (I.t * I.k) Xf) (hLf : SArr m Ly.pL 2 (I.t * I.k) Lf)
    (hz : ZeroFrom m Ly.F) (Bx : ℕ) (hBx : ∀ b < I.t * I.k, Nat.size (Xf b).natAbs ≤ Bx)
    (hk : 0 < I.k) {c : ℕ} (hc : c < I.t) (hL : Ly.Ok I) (hS : Ly.F + 2 * Bx ≤ S) :
    HTB S gpOut (fun cfg => GpOut I Ly m Xf Lf c cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t)
      (fun cfg => GpOut I Ly m Xf Lf (c + 1) cfg ∧ cfg.reg eC = c ∧ cfg.reg qT = I.t)
      (I.k * (31 * Bx + 130) + 45) := by
  have hct : c * I.k < I.t * I.k := by simpa using flat_idx_lt hc hk
  have h1 := HTB.sload (S := S) (P := fun cfg => GpOut I Ly m Xf Lf c cfg ∧ cfg.reg eC = c ∧
      cfg.reg qT = I.t) (d := eS2) (p := ePy) (a := Ly.pL + c * I.k * 2) (z := Lf (c * I.k))
    (by decide) (by decide) (by decide) (by indep [GpOut, GpB, eG_iff, QRegs, SReg])
    (by have := hL.fits (S := S) (by omega); omega)
  have hl := HTB.forUpC (S := S) (i := eJ) (n := qK) (N := I.k) (body := gpIn)
    (GpIn I Ly m Xf Lf c) (31 * Bx + 126) (by decide) (by decide) (by decide)
    (fun j => by indep [GpIn, GpB, eG_iff, QRegs, SReg])
    (fun j hj => gpIn_specB I Ly m Xf Lf hX hLf hz Bx hBx hc hj hL hS)
  have h3 := HTB.sadd (S := S) (P := fun cfg => GpB I Ly m (c * I.k + I.k) cfg ∧ cfg.reg eC = c ∧
      SReg cfg eS1 (sxl Xf Lf I.k (c + 1))) (d := eS3) (x := eS3) (y := eS2)
    (u := spi Lf I.k c) (v := pmin Lf I.k c I.k) (by decide) (by decide) (by decide)
    (by indep [GpB, eG_iff, QRegs, SReg])
  refine ((h1.pre fun cfg h => ⟨h, h.1.1.2.2.2, by rw [h.1.1.2.1]; exact hLf _ hct⟩).seq
    ((hl.pre fun cfg ⟨⟨⟨⟨hE, hm, hpx, hpy⟩, hs1, hs3⟩, hc', _⟩, hs2⟩ =>
      ⟨⟨⟨hE, hm, by simpa using hpx, by simpa using hpy⟩, hc', by simpa using hs1,
        by simpa [pmin] using hs2, hs3⟩, hE.k⟩).seq
    ((h3.pre fun cfg ⟨⟨hg, hc', hs1, hs2, hs3⟩, _, _⟩ =>
      ⟨⟨hg, hc', by rw [sxl, Finset.sum_range_succ]; exact hs1⟩, hs3, hs2⟩).post
      fun cfg ⟨⟨⟨hE, hm, hpx, hpy⟩, hc', hs1⟩, hs3⟩ =>
        ⟨⟨⟨hE, hm, by rw [hpx, Nat.succ_mul], by rw [hpy, Nat.succ_mul]⟩, hs1,
          by rw [spi, Finset.sum_range_succ]; exact hs3⟩, hc', hE.t⟩))).weaken
    (by have : I.k * (31 * Bx + 126 + 4) = I.k * (31 * Bx + 130) := by ring
        omega)

/-! ### The gap -/

theorem natAbs_two_pow (p : ℕ) : ((2 : ℤ) ^ p).natAbs = 2 ^ p := by
  rw [Int.natAbs_pow]; rfl

theorem size_two_pow (p : ℕ) : Nat.size (((2 : ℤ) ^ p).natAbs) = p + 1 := by
  rw [natAbs_two_pow, Nat.size_pow]

/-- **E2 (3)**: `eS1 := gapN Xs L` (`O(tk · Bx + p)` steps, `Bx` bounding the bit lengths of the
entries of `Xs`). -/
theorem gapB_specB (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (Xf Lf : ℕ → ℤ)
    (hX : SArr m Ly.pX 2 (I.t * I.k) Xf) (hLf : SArr m Ly.pL 2 (I.t * I.k) Lf)
    (hz : ZeroFrom m Ly.F) (Bx : ℕ) (hBx : ∀ b < I.t * I.k, Nat.size (Xf b).natAbs ≤ Bx)
    (hk : 0 < I.k) (hL : Ly.Ok I) (hS : Ly.F + 2 * Bx + 2 * prec I.t I.k + 2 ≤ S) :
    HTB S gapB (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧
        SReg cfg eS1 (gapN Xf Lf I.t I.k (prec I.t I.k)))
      (I.t * (I.k * (31 * Bx + 130) + 49) + 31 * prec I.t I.k + 147) := by
  have h0 : HTB S (.seq (mov ePx qBX) (.seq (mov ePy eL) (.seq (sconst eS1 0) (sconst eS3 0))))
      (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => GpOut I Ly m Xf Lf 0 cfg ∧ cfg.reg qT = I.t) 8 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨hE, hm⟩ => by
      have hr : ∀ r, r ∉ wregs (.seq (mov ePx qBX) (.seq (mov ePy eL) (.seq (sconst eS1 0)
          (sconst eS3 0)))) → (RAM.run (.seq (mov ePx qBX) (.seq (mov ePy eL) (.seq (sconst eS1 0)
            (sconst eS3 0)))) cfg).reg r = cfg.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr cfg
      refine ⟨⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · rw [run_mem_of_stores (by decide) rfl cfg, hm]
      · simp +decide [run_mov, Arith.sconst, hE.x]
      · simp +decide [run_mov, Arith.sconst, hE.l]
      · refine ⟨?_, ?_⟩ <;> simp +decide [run_mov, Arith.sconst, sxl, sgnBit]
      · refine ⟨?_, ?_⟩ <;> simp +decide [run_mov, Arith.sconst, spi, sgnBit]
      · rw [hr _ (by decide)]; exact hE.t
  have hl := HTB.forUpC (S := S) (i := eC) (n := qT) (N := I.t) (body := gpOut)
    (GpOut I Ly m Xf Lf) (I.k * (31 * Bx + 130) + 45) (by decide) (by decide) (by decide)
    (fun c => by indep [GpOut, GpB, eG_iff, QRegs, SReg])
    (fun c hc => gpOut_specB I Ly m Xf Lf hX hLf hz Bx hBx hk hc hL (by omega))
  have h3 := HTB.smul (S := S) (P := fun cfg => GpB I Ly m (I.t * I.k) cfg ∧
      SReg cfg eS1 (sxl Xf Lf I.k I.t)) (d := eS3) (x := eS3) (y := eP2)
    (u := spi Lf I.k I.t) (v := (2 : ℤ) ^ prec I.t I.k) (by decide) (by decide) (by decide)
    (by indep [GpB, eG_iff, QRegs, SReg]) (fun cfg h => by rw [h.1.2.1, h.1.1.free]; exact hz)
    (fun cfg h => by rw [h.1.1.free, size_two_pow]; omega)
  have h4 := HTB.ssub (S := S) (P := GpB I Ly m (I.t * I.k)) (d := eS1) (x := eS1) (y := eS3)
    (u := sxl Xf Lf I.k I.t) (v := spi Lf I.k I.t * 2 ^ prec I.t I.k) (by decide) (by decide)
    (by decide) (by indep [GpB, eG_iff, QRegs])
  have hc2 : smulCost ((2 : ℤ) ^ prec I.t I.k) ≤ 31 * (prec I.t I.k + 1) + 35 :=
    smulCost_le (le_of_eq (size_two_pow _))
  refine (h0.seq (hl.seq ((h3.pre fun cfg ⟨⟨hb, hs1, hs3⟩, _, _⟩ =>
      ⟨⟨hb, hs1⟩, hs3, hb.1.p2⟩).seq
    ((h4.pre fun cfg ⟨⟨hb, hs1⟩, hs3⟩ => ⟨hb, hs1, hs3⟩).post
      fun cfg ⟨⟨hE, hm, _, _⟩, hs⟩ => ⟨hE, hm, hs⟩)))).weaken ?_
  have : I.t * (I.k * (31 * Bx + 130) + 45 + 4) = I.t * (I.k * (31 * Bx + 130) + 49) := by ring
  omega

/-! ### The success test -/

/-- **E2 (4)**: `eDn := [gap · E² ≤ 4^p]`. -/
theorem testB_specB (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (hz : ZeroFrom m Ly.F) (gp : ℤ) (BE : ℕ)
    (hBE : Nat.size (bigE I.t I.k) ≤ BE) (hS : Ly.F + 4 * BE ≤ S) :
    HTB S testB (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ SReg cfg eS1 gp)
      (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧
        cfg.reg eDn = if gp * (bigE I.t I.k : ℤ) ^ 2 ≤ 4 ^ prec I.t I.k then 1 else 0)
      (93 * BE + 8 * prec I.t I.k + 165) := by
  set E : ℤ := (bigE I.t I.k : ℤ) with hEdef
  have hZ : ∀ cfg, (EG I Ly cfg ∧ cfg.mem = m) → ZeroFrom cfg.mem (cfg.reg rFREE) :=
    fun cfg h => by rw [h.2, h.1.free]; exact hz
  have hEB : Nat.size E.natAbs ≤ BE := by rw [hEdef, Int.natAbs_natCast]; exact hBE
  have hEEB : Nat.size (E * E).natAbs ≤ 2 * BE := by
    rw [Int.natAbs_mul]
    have := Nat.size_le.mp hEB
    rw [Nat.size_le, two_mul, pow_add]
    exact Nat.mul_lt_mul'' this this
  have h1 := HTB.sofNat (S := S) (P := fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ SReg cfg eS1 gp)
    (d := eV) (x := qE) (n := bigE I.t I.k) (by decide) (by decide) (by decide)
    (by indep [eG_iff, QRegs, SReg])
  have h2 := HTB.smul (S := S) (P := fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ SReg cfg eS1 gp)
    (d := eV) (x := eV) (y := eV) (u := E) (v := E) (by decide) (by decide) (by decide)
    (by indep [eG_iff, QRegs, SReg]) (fun cfg h => hZ cfg ⟨h.1, h.2.1⟩)
    (fun cfg h => by rw [h.1.free]; omega)
  have h3 := HTB.smul (S := S) (P := fun cfg => EG I Ly cfg ∧ cfg.mem = m) (d := eS1) (x := eS1)
    (y := eV) (u := gp) (v := E * E) (by decide) (by decide) (by decide)
    (by indep [eG_iff, QRegs]) hZ (fun cfg h => by rw [h.1.free]; omega)
  have h4 : HTB S (.add eT1 qP qP)
      (fun cfg => (EG I Ly cfg ∧ cfg.mem = m) ∧ SReg cfg eS1 (gp * (E * E)))
      (fun cfg => (EG I Ly cfg ∧ cfg.mem = m ∧ SReg cfg eS1 (gp * (E * E))) ∧
        cfg.reg eT1 = 2 * prec I.t I.k) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨hE, hm⟩, hs⟩ => by
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, by simpa using hm,
        ?_⟩, ?_⟩
      · exact ⟨by simpa +decide using hs.1, by simpa +decide using hs.2⟩
      · simp +decide [hE.p]; ring
  have h5 := HTB.pow2N (S := S) (P := fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ SReg cfg eS1 (gp *
      (E * E)))
    (d := eT2) (e := eT1) (k := 2 * prec I.t I.k) (by decide) (by indep [eG_iff, QRegs, SReg])
  have h6 := HTB.sofNat (S := S) (P := fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ SReg cfg eS1 (gp *
      (E * E)))
    (d := eW) (x := eT2) (n := 2 ^ (2 * prec I.t I.k)) (by decide) (by decide) (by decide)
    (by indep [eG_iff, QRegs, SReg])
  have h7 := HTB.sle (S := S) (P := fun cfg => EG I Ly cfg ∧ cfg.mem = m) (d := eDn) (x := eS1)
      (y := eW)
    (u := gp * (E * E)) (v := ((2 ^ (2 * prec I.t I.k) : ℕ) : ℤ)) (by decide) (by decide)
    (by indep [eG_iff, QRegs])
  have he : ((2 ^ (2 * prec I.t I.k) : ℕ) : ℤ) = 4 ^ prec I.t I.k := by
    push_cast; rw [pow_mul]; norm_num
  have hE2 : E * E = E ^ 2 := by ring
  have hc1 : smulCost E ≤ 31 * BE + 35 := smulCost_le hEB
  have hc2 : smulCost (E * E) ≤ 31 * (2 * BE) + 35 := smulCost_le hEEB
  refine ((h1.pre fun cfg h => ⟨h, h.1.e⟩).seq
    ((h2.pre fun cfg ⟨h, hv⟩ => ⟨h, hv, hv⟩).seq
    ((h3.pre fun cfg ⟨⟨hE, hm, hs⟩, hv⟩ => ⟨⟨hE, hm⟩, hs, hv⟩).seq
    (h4.seq (h5.seq ((h6.pre fun cfg h => h).seq
    ((h7.pre fun cfg ⟨⟨hE, hm, hs⟩, hw⟩ => ⟨⟨hE, hm⟩, hs, hw⟩).post
      fun cfg ⟨⟨hE, hm⟩, hd⟩ => ⟨hE, hm, by rw [hd, he, hE2]⟩))))))).weaken ?_
  omega

end STACS2027.Runtimes.QPRam
