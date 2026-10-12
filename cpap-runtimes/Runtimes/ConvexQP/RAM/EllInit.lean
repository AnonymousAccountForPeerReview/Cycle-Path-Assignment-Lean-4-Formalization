module

public import Runtimes.ConvexQP.RAM.EllCost
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: allocation and the initial state

`setup` allocates (by bumping `rFREE`) the blocks of Phase E (`As`, `Qs`, `Xs` at `qBX`, `L`,
`g`, `u`; layout `layOf`), sets the global registers of `EG` (`2n`, `k − 1`, `2^p`), writes the
initial state `ellInit` (`As_a = 2^{p−1}`, `Qs = n 2^{p−2} I`, row by row) and `eCnt := N`
(`setup_spec`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

/-! ### The layout -/

/-- The layout of Phase E for `H` at `bh` and the free memory from `F0`. -/
def layOf (I : Inst) (bh F0 : ℕ) : Lay where
  bh := bh
  pA := F0
  pQ := F0 + nDim I.t I.k * 2
  pX := F0 + nDim I.t I.k * 2 + nDim I.t I.k * (2 * nDim I.t I.k)
  pL := F0 + nDim I.t I.k * 2 + nDim I.t I.k * (2 * nDim I.t I.k) + I.t * I.k * 2
  pG := F0 + nDim I.t I.k * 2 + nDim I.t I.k * (2 * nDim I.t I.k) + I.t * I.k * 2 +
    I.t * I.k * 2
  pU := F0 + nDim I.t I.k * 2 + nDim I.t I.k * (2 * nDim I.t I.k) + I.t * I.k * 2 +
    I.t * I.k * 2 + nDim I.t I.k * 2
  F := F0 + nDim I.t I.k * 2 + nDim I.t I.k * (2 * nDim I.t I.k) + I.t * I.k * 2 +
    I.t * I.k * 2 + nDim I.t I.k * 2 + nDim I.t I.k * 2

theorem layOf_ok {I : Inst} (hI : I.Valid) (ht : 0 < I.t) {bh F0 : ℕ}
    (hb : bh + hCells I ≤ F0) : (layOf I bh F0).Ok I :=
  ⟨hI.1, ht, hb, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The program -/

/-- `2n`, `k − 1`. -/
def setA : Stmt := .seq (.add e2N qN qN) (subc eK1 qK 1)

/-- The allocations. -/
def setB : Stmt :=
  .seq (.add eT2 qKT qKT) (.seq (alloc eA e2N) (.seq (alloc eQ eT1) (.seq (alloc qBX eT2)
    (.seq (alloc eL eT2) (.seq (alloc eG e2N) (alloc eU e2N))))))

/-- `2^p` (signed, in `eP2`). -/
def setP : Stmt := .seq (pow2N eT1 qP) (sofNat eP2 eT1)

/-- One entry of the initial center. -/
def aIn : Stmt := .seq (sstore ePa eV) (addc ePa ePa 2)

/-- The initial center `As_a = 2^{p−1}`. -/
def initA : Stmt :=
  .seq (subc eT1 qP 1) (.seq (pow2N eT1 eT1) (.seq (sofNat eV eT1) (.seq (mov ePa eA)
    (forUp eC qN aIn))))

/-- One entry of the initial matrix. -/
def qIn : Stmt := .seq (ifEq eC eJ (sstore ePa eV) (sstore ePa eW)) (addc ePa ePa 2)

/-- The initial matrix `Qs = n 2^{p−2} I`, row by row. -/
def initQ : Stmt :=
  .seq (subc eT1 qP 2) (.seq (pow2N eT1 eT1) (.seq (mulN eT1 eT1 qN) (.seq (sofNat eV eT1)
    (.seq (sconst eW 0) (.seq (mov ePa eQ) (forUp eC qN (forUp eJ qN qIn)))))))

/-- **The setup of Phase E**. -/
def setup : Stmt :=
  .seq (.seq setA (.seq (RAM.mul eT1 e2N qN eC) setB)) (.seq setP (.seq initA (.seq initQ
    (mov eCnt qIt))))

theorem setup_wregs : ∀ r ∈ wregs setup, r = rFREE ∨ r = qBX ∨ r = rT ∨
    (400 ≤ r ∧ r < 450) ∨ (470 ≤ r ∧ r < 500) := by decide +kernel

/-! ### The registers -/

/-- The registers of `EG` except `2^p`. -/
def EGa (I : Inst) (Ly : Lay) (c : Config) : Prop :=
  QRegs I c ∧ c.reg qBH = Ly.bh ∧ c.reg qBX = Ly.pX ∧ c.reg rFREE = Ly.F ∧ c.reg eA = Ly.pA ∧
    c.reg eQ = Ly.pQ ∧ c.reg eL = Ly.pL ∧ c.reg eG = Ly.pG ∧ c.reg eU = Ly.pU ∧
    c.reg e2N = 2 * nDim I.t I.k ∧ c.reg eK1 = I.k - 1

/-- The registers and memory before the setup. -/
def SR0 (I : Inst) (bh F0 : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop :=
  (QRegs I c ∧ c.reg qBH = bh) ∧ c.reg rFREE = F0 ∧ c.mem = m₀

theorem setAB_spec (I : Inst) (bh F0 : ℕ) (m₀ : ℕ → ℕ) :
    HT (.seq setA (.seq (RAM.mul eT1 e2N qN eC) setB))
      (fun c => (QRegs I c ∧ c.reg qBH = bh) ∧ c.reg rFREE = F0 ∧ c.mem = m₀)
      (fun c => EGa I (layOf I bh F0) c ∧ c.mem = m₀) (5 * nDim I.t I.k + 26) := by
  refine HT.pre ?_ fun c h => (show SR0 I bh F0 m₀ c from h)
  set n := nDim I.t I.k with hn
  have h1 : HT setA (SR0 I bh F0 m₀)
      (fun c => SR0 I bh F0 m₀ c ∧ c.reg e2N = 2 * n ∧ c.reg eK1 = I.k - 1) 3 :=
    HT.run_le (by decide) (by decide) fun c ⟨⟨hq, hb⟩, hF, hm⟩ => by
      have hq' : RegIndep (wregs setA) (QRegs I) := by indep [QRegs]
      refine ⟨⟨⟨hq'.run (by decide) hq, ?_⟩, ?_, by rw [run_mem_of_stores (by decide) rfl c, hm]⟩,
        ?_, ?_⟩
      · rw [run_reg_of_not_mem (by decide) (by decide) c]; exact hb
      · rw [run_reg_of_not_mem (by decide) (by decide) c]; exact hF
      · simp +decide [setA, run_subc, hq.2.2.2.1, hn]; ring
      · simp +decide [setA, run_subc, hq.2.1]
  have h2 := HT.mul (P := fun c => SR0 I bh F0 m₀ c ∧ c.reg e2N = 2 * n ∧ c.reg eK1 = I.k - 1)
    (d := eT1) (a := e2N) (b := qN) (k := eC) (x := 2 * n) (y := n) (by decide)
    (by indep [SR0, QRegs]) (fun c h => h.2.1) (fun c h => h.1.1.1.2.2.2.1)
  have h3 : HT setB (fun c => (SR0 I bh F0 m₀ c ∧ c.reg e2N = 2 * n ∧ c.reg eK1 = I.k - 1) ∧
      c.reg eT1 = 2 * n * n) (fun c => EGa I (layOf I bh F0) c ∧ c.mem = m₀) 19 :=
    HT.run_le (by decide) (by decide) fun c ⟨⟨⟨⟨hq, hb⟩, hF, hm⟩, h2n, hk1⟩, ht1⟩ => by
      have hq' : RegIndep (wregs setB) (QRegs I) := by indep [QRegs]
      have hkt := hq.2.2.1
      refine ⟨⟨hq'.run (by decide) hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        by rw [run_mem_of_stores (by decide) rfl c, hm]⟩
      all_goals simp +decide [setB, run_alloc, layOf, hb, hF, h2n, hk1, ht1, hkt, ← hn]
      all_goals ring
  refine (h1.seq (h2.seq h3)).weaken ?_
  omega

theorem setP_spec (I : Inst) (Ly : Lay) (m₀ : ℕ → ℕ) :
    HT setP (fun c => EGa I Ly c ∧ c.mem = m₀) (fun c => EG I Ly c ∧ c.mem = m₀)
      (4 * prec I.t I.k + 9) := by
  have h1 := HT.pow2N (P := fun c => EGa I Ly c ∧ c.mem = m₀) (d := eT1) (e := qP)
    (k := prec I.t I.k) (by decide) (by indep [EGa, QRegs])
  have h2 := HT.sofNat (P := fun c => EGa I Ly c ∧ c.mem = m₀) (d := eP2) (x := eT1)
    (n := 2 ^ prec I.t I.k) (by decide) (by decide) (by decide) (by indep [EGa, QRegs])
  refine ((h1.pre fun c h => ⟨h, h.1.1.2.2.2.2.2.2.2.1⟩).seq (h2.post fun c ⟨⟨hE, hm⟩, h0, h1⟩ =>
    ⟨⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2.1, hE.2.2.2.2.1, hE.2.2.2.2.2.1, hE.2.2.2.2.2.2.1,
      hE.2.2.2.2.2.2.2.1, hE.2.2.2.2.2.2.2.2.1, hE.2.2.2.2.2.2.2.2.2.1, hE.2.2.2.2.2.2.2.2.2.2,
      ?_, ?_⟩, hm⟩)).weaken (by omega)
  · rw [h0]; simp [sgnBit]
  · rw [h1]; simp

/-! ### The initial center -/

theorem aIn_specB (I : Inst) (Ly : Lay) (m₀ : ℕ → ℕ) (h : ℤ) (j : ℕ)
    (ha : Ly.pA + j * 2 + 1 < S) :
    HTB S aIn (fun c => (EG I Ly c ∧ c.mem = wrArr m₀ Ly.pA 2 (fun _ => h) j ∧
        c.reg ePa = Ly.pA + j * 2 ∧ SReg c eV h) ∧ c.reg eC = j ∧ c.reg qN = nDim I.t I.k)
      (fun c => (EG I Ly c ∧ c.mem = wrArr m₀ Ly.pA 2 (fun _ => h) (j + 1) ∧
        c.reg ePa = Ly.pA + (j + 1) * 2 ∧ SReg c eV h) ∧ c.reg eC = j ∧
        c.reg qN = nDim I.t I.k) 6 := by
  have h1 := HTB.sstore (S := S) (F := fun c => EG I Ly c ∧ c.reg eC = j) (p := ePa) (x := eV)
    (a := Ly.pA + j * 2) (z := h) (m := wrArr m₀ Ly.pA 2 (fun _ => h) j) (by decide) (by decide)
    (by decide) (((EG.regIndep I Ly).mono (by decide)).and (by indep)) ha
  have h2 : HTB S (addc ePa ePa 2) (fun c => (EG I Ly c ∧ c.reg eC = j) ∧ SReg c eV h ∧
      c.reg ePa = Ly.pA + j * 2 ∧ c.mem = RAM.upd (RAM.upd (wrArr m₀ Ly.pA 2 (fun _ => h) j)
        (Ly.pA + j * 2) (sgnBit h)) (Ly.pA + j * 2 + 1) h.natAbs)
      (fun c => (EG I Ly c ∧ c.mem = wrArr m₀ Ly.pA 2 (fun _ => h) (j + 1) ∧
        c.reg ePa = Ly.pA + (j + 1) * 2 ∧ SReg c eV h) ∧ c.reg eC = j ∧
        c.reg qN = nDim I.t I.k) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hE, hc⟩, hv, hpa, hm⟩ => by
      have hr : ∀ r, r ∉ wregs (addc ePa ePa 2) → (RAM.run (addc ePa ePa 2) c).reg r = c.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr c
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [run_mem_of_stores (by decide) rfl c, hm, wrArr_succ]; rfl
      · simp +decide [run_addc, hpa]; ring
      · rw [hr _ (by decide)]; exact hv.1
      · rw [hr _ (by decide)]; exact hv.2
      · rw [hr _ (by decide)]; exact hc
      · rw [hr _ (by decide)]; exact hE.n
  exact ((h1.pre fun c ⟨⟨hE, hm, hpa, hv⟩, hc, _⟩ => ⟨⟨hE, hc⟩, hv, hpa, hm⟩).seq h2).weaken
    (by omega)

theorem initA_specB (I : Inst) (Ly : Lay) (m₀ : ℕ → ℕ) (hAS : Ly.pA + nDim I.t I.k * 2 ≤ S) :
    HTB S initA (fun c => EG I Ly c ∧ c.mem = m₀)
      (fun c => EG I Ly c ∧ c.mem = wrArr m₀ Ly.pA 2
        (fun _ => ((2 ^ (prec I.t I.k - 1) : ℕ) : ℤ)) (nDim I.t I.k))
      (4 * prec I.t I.k + nDim I.t I.k * 10 + 18) := by
  set h : ℤ := ((2 ^ (prec I.t I.k - 1) : ℕ) : ℤ) with hh
  have h1 : HTB S (subc eT1 qP 1) (fun c => EG I Ly c ∧ c.mem = m₀)
      (fun c => (EG I Ly c ∧ c.mem = m₀) ∧ c.reg eT1 = prec I.t I.k - 1) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hE, hm⟩ =>
      ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE,
        by rw [run_mem_of_stores (by decide) rfl c, hm]⟩, by simp +decide [run_subc, hE.p]⟩
  have h2 := HTB.pow2N (S := S) (P := fun c => EG I Ly c ∧ c.mem = m₀) (d := eT1) (e := eT1)
    (k := prec I.t I.k - 1) (by decide) ((EG.indep (by decide)).and (Indep.mem (· = m₀)))
  have h3 := HTB.sofNat (S := S) (P := fun c => EG I Ly c ∧ c.mem = m₀) (d := eV) (x := eT1)
    (n := 2 ^ (prec I.t I.k - 1)) (by decide) (by decide) (by decide)
    ((EG.indep (by decide)).and (Indep.mem (· = m₀)))
  have h4 : HTB S (mov ePa eA) (fun c => (EG I Ly c ∧ c.mem = m₀) ∧ SReg c eV h)
      (fun c => (EG I Ly c ∧ c.mem = wrArr m₀ Ly.pA 2 (fun _ => h) 0 ∧
        c.reg ePa = Ly.pA + 0 * 2 ∧ SReg c eV h) ∧ c.reg qN = nDim I.t I.k) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hE, hm⟩, hv⟩ => by
      have hr : ∀ r, r ∉ wregs (mov ePa eA) → (RAM.run (mov ePa eA) c).reg r = c.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr c
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [run_mem_of_stores (by decide) rfl c, hm]; rfl
      · simp +decide [run_mov, hE.a]
      · rw [hr _ (by decide)]; exact hv.1
      · rw [hr _ (by decide)]; exact hv.2
      · rw [hr _ (by decide)]; exact hE.n
  have hl := HTB.forUpC (S := S) (i := eC) (n := qN) (N := nDim I.t I.k) (body := aIn)
    (fun j c => EG I Ly c ∧ c.mem = wrArr m₀ Ly.pA 2 (fun _ => h) j ∧
      c.reg ePa = Ly.pA + j * 2 ∧ SReg c eV h) 6 (by decide) (by decide) (by decide)
    (fun j => by indep [eG_iff, QRegs, SReg])
    (fun j hj => aIn_specB I Ly m₀ h j (by omega))
  refine (h1.seq (h2.seq (h3.seq (h4.seq hl)))).post (fun c ⟨⟨hE, hm, _⟩, _⟩ => ⟨hE, hm⟩)
    |>.weaken ?_
  omega

/-! ### The initial matrix -/

/-- The initial matrix on flat indices `a n + b` (`d` on the diagonal). -/
def qInit (n : ℕ) (d : ℤ) (x : ℕ) : ℤ := if x / n = x % n then d else 0

theorem qInit_cell {n a b : ℕ} (d : ℤ) (hb : b < n) :
    qInit n d (a * n + b) = if a = b then d else 0 := by
  unfold qInit; rw [cell_div hb, cell_mod hb]

/-- Before entry `(a, b)`. -/
def QI (I : Inst) (Ly : Lay) (m₁ : ℕ → ℕ) (d : ℤ) (a b : ℕ) (c : Config) : Prop :=
  EG I Ly c ∧ c.mem = wrArr m₁ Ly.pQ 2 (qInit (nDim I.t I.k) d) (a * nDim I.t I.k + b) ∧
    c.reg ePa = Ly.pQ + (a * nDim I.t I.k + b) * 2 ∧ SReg c eV d ∧ SReg c eW 0 ∧ c.reg eC = a

/-- Before row `a`. -/
def QO (I : Inst) (Ly : Lay) (m₁ : ℕ → ℕ) (d : ℤ) (a : ℕ) (c : Config) : Prop :=
  EG I Ly c ∧ c.mem = wrArr m₁ Ly.pQ 2 (qInit (nDim I.t I.k) d) (a * nDim I.t I.k) ∧
    c.reg ePa = Ly.pQ + a * nDim I.t I.k * 2 ∧ SReg c eV d ∧ SReg c eW 0

theorem qIn_specB (I : Inst) (Ly : Lay) (m₁ : ℕ → ℕ) (d : ℤ) {a b : ℕ} (hb : b < nDim I.t I.k)
    (ha : a < nDim I.t I.k) (hQS : Ly.pQ + nDim I.t I.k * (2 * nDim I.t I.k) ≤ S) :
    HTB S qIn (fun c => QI I Ly m₁ d a b c ∧ c.reg eJ = b ∧ c.reg qN = nDim I.t I.k)
      (fun c => QI I Ly m₁ d a (b + 1) c ∧ c.reg eJ = b ∧ c.reg qN = nDim I.t I.k) 10 := by
  set n := nDim I.t I.k with hn
  set x := a * n + b with hx
  set F : Config → Prop := fun c => EG I Ly c ∧ SReg c eV d ∧ SReg c eW 0 ∧ c.reg eC = a ∧
    c.reg eJ = b with hF
  have hFi : RegIndep [rT] F := ((EG.regIndep I Ly).mono (by decide)).and (by indep [SReg])
  have hxS : Ly.pQ + x * 2 + 1 < S := by
    have e : x * 2 = a * (2 * n) + b * 2 := by rw [hx]; ring
    have := row_le ha
    omega
  let Q : Config → Prop := fun c => F c ∧ c.reg ePa = Ly.pQ + x * 2 ∧
    c.mem = wrArr m₁ Ly.pQ 2 (qInit n d) (x + 1)
  have hs : HTB S (sstore ePa eV) (fun c => (F c ∧ c.reg ePa = Ly.pQ + x * 2 ∧
      c.mem = wrArr m₁ Ly.pQ 2 (qInit n d) x) ∧ c.reg eC = c.reg eJ) Q 4 := by
    refine HTB.of_forall fun c₀ ⟨⟨hF0, hpa, hm⟩, he⟩ => ?_
    have hab : a = b := by rw [← hF0.2.2.2.1, ← hF0.2.2.2.2, he]
    have h := HTB.sstore (S := S) (F := F) (p := ePa) (x := eV) (a := Ly.pQ + x * 2) (z := d)
      (m := wrArr m₁ Ly.pQ 2 (qInit n d) x) (by decide) (by decide) (by decide) hFi hxS
    refine (h.pre fun c hc => ?_).post fun c ⟨hF1, _, hpa1, hm1⟩ => ⟨hF1, hpa1, ?_⟩
    · subst hc; exact ⟨hF0, hF0.2.1, hpa, hm⟩
    · rw [hm1, wrArr_succ, hx, qInit_cell d hb]; simp [hab]; rfl
  have hu : HTB S (sstore ePa eW) (fun c => (F c ∧ c.reg ePa = Ly.pQ + x * 2 ∧
      c.mem = wrArr m₁ Ly.pQ 2 (qInit n d) x) ∧ c.reg eC ≠ c.reg eJ) Q 4 := by
    refine HTB.of_forall fun c₀ ⟨⟨hF0, hpa, hm⟩, he⟩ => ?_
    have hab : a ≠ b := by rw [← hF0.2.2.2.1, ← hF0.2.2.2.2]; exact he
    have h := HTB.sstore (S := S) (F := F) (p := ePa) (x := eW) (a := Ly.pQ + x * 2) (z := 0)
      (m := wrArr m₁ Ly.pQ 2 (qInit n d) x) (by decide) (by decide) (by decide) hFi hxS
    refine (h.pre fun c hc => ?_).post fun c ⟨hF1, _, hpa1, hm1⟩ => ⟨hF1, hpa1, ?_⟩
    · subst hc; exact ⟨hF0, hF0.2.2.1, hpa, hm⟩
    · rw [hm1, wrArr_succ, hx, qInit_cell d hb]; simp [hab]; rfl
  have h1 := HTB.ifEq (a := eC) (b := eJ) (by decide) (by decide)
    (P := fun c => F c ∧ c.reg ePa = Ly.pQ + x * 2 ∧ c.mem = wrArr m₁ Ly.pQ 2 (qInit n d) x)
    (by indep [hF, eG_iff, QRegs, SReg]) hs hu
  have h2 : HTB S (addc ePa ePa 2) Q
      (fun c => QI I Ly m₁ d a (b + 1) c ∧ c.reg eJ = b ∧ c.reg qN = n) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hE, hv, hw, hc, hj⟩, hpa, hm⟩ => by
      have hr : ∀ r, r ∉ wregs (addc ePa ePa 2) → (RAM.run (addc ePa ePa 2) c).reg r = c.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr c
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
      · rw [run_mem_of_stores (by decide) rfl c, hm, hx, hn, Nat.add_assoc]
      · simp +decide [run_addc, hpa, hx]; ring
      all_goals rw [hr _ (by decide)]
      · exact hv.1
      · exact hv.2
      · exact hw.1
      · exact hw.2
      · exact hc
      · exact hj
      · exact hE.n
  exact (h1.pre fun c ⟨⟨hE, hm, hpa, hv, hw, hc⟩, hj, _⟩ => ⟨⟨hE, hv, hw, hc, hj⟩, hpa, hm⟩).seq h2

theorem qOut_specB (I : Inst) (Ly : Lay) (m₁ : ℕ → ℕ) (d : ℤ) (a : ℕ) (ha : a < nDim I.t I.k)
    (hQS : Ly.pQ + nDim I.t I.k * (2 * nDim I.t I.k) ≤ S) :
    HTB S (forUp eJ qN qIn) (fun c => QO I Ly m₁ d a c ∧ c.reg eC = a ∧ c.reg qN = nDim I.t I.k)
      (fun c => QO I Ly m₁ d (a + 1) c ∧ c.reg eC = a ∧ c.reg qN = nDim I.t I.k)
      (nDim I.t I.k * 14 + 3) := by
  have hl := HTB.forUpC (S := S) (i := eJ) (n := qN) (N := nDim I.t I.k) (body := qIn)
    (QI I Ly m₁ d a) 10 (by decide) (by decide) (by decide)
    (fun b => by indep [QI, eG_iff, QRegs, SReg]) (fun b hb => qIn_specB I Ly m₁ d hb ha hQS)
  refine (hl.pre fun c ⟨⟨hE, hm, hpa, hv, hw⟩, hc, hn⟩ =>
    ⟨⟨hE, by simpa using hm, by simpa using hpa, hv, hw, hc⟩, hn⟩).post
      fun c ⟨⟨hE, hm, hpa, hv, hw, hc⟩, _, hn⟩ => ⟨⟨hE, ?_, ?_, hv, hw⟩, hc, hn⟩
  · rw [hm, Nat.succ_mul]
  · rw [hpa, Nat.succ_mul]

theorem initQ_specB (I : Inst) (Ly : Lay) (m₁ : ℕ → ℕ) (hz : ZeroFrom m₁ Ly.F)
    (hQS : Ly.pQ + nDim I.t I.k * (2 * nDim I.t I.k) ≤ S)
    (hS : Ly.F + 2 * Nat.size (nDim I.t I.k) ≤ S) :
    HTB S initQ (fun c => EG I Ly c ∧ c.mem = m₁)
      (fun c => EG I Ly c ∧ c.mem = wrArr m₁ Ly.pQ 2
        (qInit (nDim I.t I.k) ((2 ^ (prec I.t I.k - 2) * nDim I.t I.k : ℕ) : ℤ))
        (nDim I.t I.k * nDim I.t I.k))
      (4 * prec I.t I.k + mulCost (nDim I.t I.k) + nDim I.t I.k * (nDim I.t I.k * 14 + 7) +
        20) := by
  set n := nDim I.t I.k with hn
  set d : ℤ := ((2 ^ (prec I.t I.k - 2) * n : ℕ) : ℤ) with hd
  have hZ : ∀ c, (EG I Ly c ∧ c.mem = m₁) → ZeroFrom c.mem (c.reg rFREE) :=
    fun c h => by rw [h.2, h.1.free]; exact hz
  have hP : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ ellW) → Indep W (fun c => EG I Ly c ∧ c.mem = m₁) :=
    fun hW => (EG.indep hW).and (Indep.mem (· = m₁))
  have h1 : HTB S (subc eT1 qP 2) (fun c => EG I Ly c ∧ c.mem = m₁)
      (fun c => (EG I Ly c ∧ c.mem = m₁) ∧ c.reg eT1 = prec I.t I.k - 2) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hE, hm⟩ =>
      ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE,
        by rw [run_mem_of_stores (by decide) rfl c, hm]⟩, by simp +decide [run_subc, hE.p]⟩
  have h2 := HTB.pow2N (S := S) (P := fun c => EG I Ly c ∧ c.mem = m₁) (d := eT1) (e := eT1)
    (k := prec I.t I.k - 2) (by decide) (hP (by decide))
  have h3 := HTB.mulN (S := S) (P := fun c => EG I Ly c ∧ c.mem = m₁) (d := eT1) (x := eT1) (y :=
      qN)
    (a := 2 ^ (prec I.t I.k - 2)) (b := n) (by decide) (by decide) (hP (by decide)) hZ
    (fun c h => by rw [h.1.free]; omega)
  have h4 := HTB.sofNat (S := S) (P := fun c => EG I Ly c ∧ c.mem = m₁) (d := eV) (x := eT1)
    (n := 2 ^ (prec I.t I.k - 2) * n) (by decide) (by decide) (by decide) (hP (by decide))
  have h5 := HTB.sconst (S := S) (P := fun c => (EG I Ly c ∧ c.mem = m₁) ∧ SReg c eV d) (d := eW) 0
    ((hP (by decide)).and (indep_sreg (by decide) (by decide) d))
  have h6 : HTB S (mov ePa eQ) (fun c => ((EG I Ly c ∧ c.mem = m₁) ∧ SReg c eV d) ∧ SReg c eW 0)
      (fun c => QO I Ly m₁ d 0 c ∧ c.reg qN = n) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hE, hm⟩, hv⟩, hw⟩ => by
      have hr : ∀ r, r ∉ wregs (mov ePa eQ) → (RAM.run (mov ePa eQ) c).reg r = c.reg r :=
        fun r hr => run_reg_of_not_mem (by decide) hr c
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE, ?_, ?_, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩⟩, ?_⟩
      · rw [run_mem_of_stores (by decide) rfl c, hm]; simp; rfl
      · simp +decide [run_mov, hE.qs]
      all_goals rw [hr _ (by decide)]
      · exact hv.1
      · exact hv.2
      · exact hw.1
      · exact hw.2
      · exact hE.n
  have hl := HTB.forUpC (S := S) (i := eC) (n := qN) (N := n) (body := forUp eJ qN qIn)
    (QO I Ly m₁ d) (n * 14 + 3) (by decide) (by decide) (by decide)
    (fun a => by indep [QO, eG_iff, QRegs, SReg]) (fun a ha => qOut_specB I Ly m₁ d a ha hQS)
  refine (h1.seq (h2.seq ((h3.pre fun c ⟨h, he⟩ => ⟨h, he, h.1.n⟩).seq
    (h4.seq (h5.seq (h6.seq hl)))))).post (fun c ⟨⟨hE, hm, _⟩, _⟩ => ⟨hE, hm⟩) |>.weaken ?_
  unfold mulCost
  have : n * (n * 14 + 3 + 4) = n * (n * 14 + 7) := by ring
  omega

/-! ### The setup -/

/-- The cost of the setup. -/
def setupCost (I : Inst) : ℕ :=
  5 * nDim I.t I.k + 26 + (4 * prec I.t I.k + 9 + (4 * prec I.t I.k + nDim I.t I.k * 10 + 18 +
    (4 * prec I.t I.k + mulCost (nDim I.t I.k) + nDim I.t I.k * (nDim I.t I.k * 14 + 7) + 20 +
    2)))

theorem init_As {I : Inst} {j : ℕ} (hj : j < nDim I.t I.k) :
    ((2 ^ (prec I.t I.k - 1) : ℕ) : ℤ) = flatR (ellInit I (consts I.t I.k)).As j := by
  rw [nDim_eq] at hj
  obtain ⟨i, rfl⟩ := fIdx_surj hj
  rw [flatR_fIdx]
  simp [ellInit, consts]

theorem init_Qs {I : Inst} {a b : ℕ} (ha : a < nDim I.t I.k) (hb : b < nDim I.t I.k) :
    qInit (nDim I.t I.k) ((2 ^ (prec I.t I.k - 2) * nDim I.t I.k : ℕ) : ℤ)
      (a * nDim I.t I.k + b) = flatM (ellInit I (consts I.t I.k)).Qs a b := by
  rw [qInit_cell _ hb]
  rw [nDim_eq] at ha hb
  obtain ⟨i, rfl⟩ := fIdx_surj ha
  obtain ⟨i', rfl⟩ := fIdx_surj hb
  rw [flatM_fIdx, flatR_fIdx]
  simp only [ellInit, consts]
  by_cases h : i = i'
  · subst h; simp; ring
  · have : fIdx i ≠ fIdx i' := fun h' => h (fIdx_inj h')
    simp [h, this]

/-- **The setup**: from `QIn I`, the globals of `EG`, the initial state `ellInit` in memory and
`eCnt = N`. -/
theorem setup_specB (I : Inst) (hI : I.Valid) (ht : 0 < I.t) (c₀ : Config) (hin : QIn I c₀)
    (hS : (layOf I (c₀.reg qBH) (c₀.reg rFREE)).F + ellSc I.t I.k ≤ S) :
    HTB S setup (fun c => c = c₀)
      (fun c => EG I (layOf I (c₀.reg qBH) (c₀.reg rFREE)) c ∧
        StMem I (layOf I (c₀.reg qBH) (c₀.reg rFREE)) (ellInit I (consts I.t I.k)) c.mem ∧
        HMem I c.mem (c₀.reg qBH) ∧ ZeroFrom c.mem (layOf I (c₀.reg qBH) (c₀.reg rFREE)).F ∧
        c.reg eCnt = iters I.t I.k)
      (setupCost I) := by
  obtain ⟨hq, hH, hb, hz, _⟩ := hin
  set Ly := layOf I (c₀.reg qBH) (c₀.reg rFREE) with hLy
  have hL : Ly.Ok I := layOf_ok hI ht hb
  have hLh := hL.h; have hLq := hL.q; have hLx := hL.x; have hLl := hL.l; have hLg := hL.g
  have hLu := hL.u; have hLf := hL.f
  have hA0 : Ly.pA = c₀.reg rFREE := rfl
  set n := nDim I.t I.k with hn
  set m₀ := c₀.mem with hm₀
  have hzF : ZeroFrom m₀ Ly.F := hz.mono (by omega)
  have hf := hL.fits (S := S) (by omega)
  have h1 : HTB S _ _ _ _ := HTB.of_HT rfl (setAB_spec I (c₀.reg qBH) (c₀.reg rFREE) m₀)
  have h2 : HTB S _ _ _ _ := HTB.of_HT rfl (setP_spec I Ly m₀)
  have h3 := initA_specB (S := S) I Ly m₀ hf.2.1
  set m₁ := wrArr m₀ Ly.pA 2 (fun _ => ((2 ^ (prec I.t I.k - 1) : ℕ) : ℤ)) n with hm₁
  have hz1 : ZeroFrom m₁ Ly.F := zeroFrom_wrArr (le_refl 2) hzF (by omega)
  have hsz : Nat.size (nDim I.t I.k) ≤ nDim I.t I.k := Nat.size_le.mpr Nat.lt_two_pow_self
  have hpn := prec_ge hL.t0 hL.k3
  have h4 := initQ_specB (S := S) I Ly m₁ hz1 hf.2.2.1 (by unfold ellSc bitB at hS; omega)
  set m₂ := wrArr m₁ Ly.pQ 2 (qInit n ((2 ^ (prec I.t I.k - 2) * n : ℕ) : ℤ)) (n * n) with hm₂
  have hm1o : ∀ x, (x < Ly.pA ∨ Ly.pA + n * 2 ≤ x) → m₁ x = m₀ x :=
    fun x hx => wrArr_of_out (le_refl 2) hx
  have hnn : n * n * 2 = n * (2 * n) := by ring
  have hm2o : ∀ x, (x < Ly.pQ ∨ Ly.pQ + n * (2 * n) ≤ x) → m₂ x = m₁ x :=
    fun x hx => wrArr_of_out (le_refl 2) (by rw [hnn]; exact hx)
  have hpost : StMem I Ly (ellInit I (consts I.t I.k)) m₂ ∧ HMem I m₂ (c₀.reg qBH) ∧
      ZeroFrom m₂ Ly.F := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact SArr.out (SArr.congr_fun (sarr_wrArr (le_refl 2) _) fun j hj => init_As hj)
        (le_refl 2) hm2o (by omega)
    · intro a ha j hj
      have := sarr_wrArr (m₀ := m₁) (b := Ly.pQ) (le_refl 2)
        (f := qInit n ((2 ^ (prec I.t I.k - 2) * n : ℕ) : ℤ)) (n * n) (a * n + j)
        (by have := row_le ha; nlinarith)
      rw [init_Qs ha hj] at this
      rw [show Ly.pQ + a * (2 * n) + j * 2 = Ly.pQ + (a * n + j) * 2 by ring]
      exact this
    · exact HMem.out (HMem.out hH hm1o (by omega)) hm2o (by omega)
    · exact zeroFrom_wrArr (le_refl 2) hz1 (by rw [hnn]; omega)
  have h5 : HTB S (mov eCnt qIt) (fun c => EG I Ly c ∧ c.mem = m₂)
      (fun c => EG I Ly c ∧ StMem I Ly (ellInit I (consts I.t I.k)) c.mem ∧
        HMem I c.mem (c₀.reg qBH) ∧ ZeroFrom c.mem Ly.F ∧ c.reg eCnt = iters I.t I.k) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hE, hm⟩ => by
      have hEi : RegIndep (wregs (mov eCnt qIt)) (EG I Ly) := by indep [eG_iff, QRegs]
      have hmem : (RAM.run (mov eCnt qIt) c).mem = m₂ := by
        rw [run_mem_of_stores (by decide) rfl c, hm]
      refine ⟨hEi.run (by decide) hE, ?_, ?_, ?_, ?_⟩
      · rw [hmem]; exact hpost.1
      · rw [hmem]; exact hpost.2.1
      · rw [hmem]; exact hpost.2.2
      · simp +decide [run_mov, hE.it]
  refine ((h1.pre fun c hc => ?_).seq (h2.seq (h3.seq (h4.seq h5)))).weaken ?_
  · subst hc; exact ⟨⟨hq, rfl⟩, rfl, rfl⟩
  · unfold setupCost; omega

end STACS2027.Runtimes.QPRam
