module

public import Runtimes.ConvexQP.RAM.EllUpd
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: E4, the update (2): center and matrix

* `aB`: `As_a := 1 · As_a + (−1) · roundDiv(2^{2p} u_a, (n+1) S)` (`axCore true`, `α = 1`,
  `β = −1`, `δ = 2^{2p}`, `γ = (n+1) S`);
* `mB`: `Qs_{ab} := roundDiv(α Qs_{ab} + β u_a u_b, γ)` (`r1Core true`) with
  `α = cN (n+1) G`, `β = −2 cN`, `γ = cD (n+1) G`, the numerator of `ellUpdate` up to `ring`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

/-! ### The center -/

/-- The inputs of `axCore` for the center. -/
def aSet : Stmt :=
  .seq (mov vN qN) (.seq (mov vPA eA) (.seq (mov vPX eU) (.seq (sconst vAl 1)
    (.seq (sconst vBe (-1)) (.seq (smov vGa eV) (sofNat vDe eT1))))))

/-- **E4 (4)**: the center. -/
def aB : Stmt := .seq (.add eT1 qP qP) (.seq (pow2N eT1 eT1) (.seq aSet (axCore true)))

theorem aB_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (m : ℕ → ℕ) (z w : ℕ → ℤ)
    (hzA : SArr m Ly.pA 2 (nDim I.t I.k) z) (hw : SArr m Ly.pU 2 (nDim I.t I.k) w)
    (hz : ZeroFrom m Ly.F) (G γ : ℤ) (hγ : 0 < γ) (n1 : ℤ) (B : ℕ)
    (hB1 : 1 ≤ B) (hBp : 2 * prec I.t I.k + 1 ≤ B)
    (hwB : ∀ j < nDim I.t I.k, Nat.size (w j).natAbs ≤ B) (hS : Ly.F + 10 * B + 4 ≤ S) :
    HTB S aB (fun cfg => ((EG I Ly cfg ∧ cfg.mem = m) ∧ SReg cfg eS1 G) ∧ SReg cfg eW n1 ∧
        SReg cfg eV γ)
      (fun cfg => (EG I Ly cfg ∧ SReg cfg eS1 G ∧ SReg cfg eW n1) ∧
        cfg.mem = wrArr m Ly.pA 2 (axNew true 1 (-1) γ ((2 ^ (2 * prec I.t I.k) : ℕ) : ℤ) z w)
          (nDim I.t I.k))
      (nDim I.t I.k * (155 * B + 302) + 8 * prec I.t I.k + 31) := by
  have hLq := hL.q; have hLx := hL.x; have hLl := hL.l; have hLg := hL.g; have hLu := hL.u
  have hLf := hL.f
  set p := prec I.t I.k with hp
  set n := nDim I.t I.k with hn
  set δ : ℤ := ((2 ^ (2 * p) : ℕ) : ℤ) with hδ
  have hδ0 : (0 : ℤ) ≤ δ := by rw [hδ]; positivity
  have hδa : δ.natAbs = 2 ^ (2 * p) := by rw [hδ, Int.natAbs_natCast]
  let R : Config → Prop := fun cfg => EG I Ly cfg ∧ SReg cfg eS1 G ∧ SReg cfg eW n1
  have hR' : RegIndep (wregs aSet) R := ((EG.regIndep I Ly).mono (by decide)).and (by indep [SReg])
  have hR : RegIndep axW R := ((EG.regIndep I Ly).mono (by decide)).and (by indep [SReg])
  let F0 : Config → Prop := fun cfg => ((EG I Ly cfg ∧ cfg.mem = m) ∧ SReg cfg eS1 G) ∧
    SReg cfg eW n1 ∧ SReg cfg eV γ
  have hF0 : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ ellW) →
      eS1 ∉ W ∧ eS1 + 1 ∉ W ∧ eW ∉ W ∧ eW + 1 ∉ W ∧ eV ∉ W ∧ eV + 1 ∉ W → Indep W F0 :=
    fun hW h => (((EG.indep hW).and (Indep.mem (· = m))).and (indep_sreg h.1 h.2.1 G)).and
      ((indep_sreg h.2.2.1 h.2.2.2.1 n1).and (indep_sreg h.2.2.2.2.1 h.2.2.2.2.2 γ))
  have h1 : HTB S (.add eT1 qP qP) F0 (fun cfg => F0 cfg ∧ cfg.reg eT1 = 2 * p) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg h => ⟨(hF0 (W := wregs (.add eT1 qP
        qP))
      (by decide) (by decide)).run (by decide) rfl rfl h, by simp +decide [h.1.1.1.p]; ring⟩
  have h2 := HTB.pow2N (S := S) (P := F0) (d := eT1) (e := eT1) (k := 2 * p) (by decide)
    (hF0 (by decide) (by decide))
  have h3 : HTB S aSet (fun cfg => F0 cfg ∧ cfg.reg eT1 = 2 ^ (2 * p))
      (fun cfg => R cfg ∧ cfg.mem = m ∧ cfg.reg vN = n ∧ cfg.reg vPA = Ly.pA ∧
        cfg.reg vPX = Ly.pU ∧ SReg cfg vAl 1 ∧ SReg cfg vBe (-1) ∧ SReg cfg vGa γ ∧
        SReg cfg vDe δ) 17 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨⟨hE, hm⟩, hs1⟩, hw1, hv⟩, ht⟩ =>
        by
      clear_value p
      refine ⟨hR'.run (by decide) ⟨hE, hs1, hw1⟩,
        by rw [run_mem_of_stores (by decide) rfl cfg, hm], ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      all_goals simp +decide [aSet, run_mov, Arith.sconst, Arith.smov, Arith.sofNat, sgnBit,
        hE.n, hE.a, hE.u, ht, hv.1, hv.2, ← hn, hδ0, hδa]
  have hf := hL.fits (S := S) (by omega)
  have h4 := axCore_specB true (S := S) (R := R) hR m Ly.F n Ly.pA Ly.pU B 1 (-1) γ δ z w hz
    (fun c hc => hc.1.free) (by omega) hzA
    (fun m' hS => SArr.out hw (le_refl 2) (lo := Ly.pA) (hi := Ly.pA + n * 2)
      (fun x hx => hS x (by omega)) (by omega))
    (by simp [GoodDiv, hγ]) (by simpa using hB1) (by simpa using hB1)
    (by rw [hδ, Int.natAbs_natCast, Nat.size_pow]; omega) hwB (by omega) (by omega)
  refine (h1.seq (h2.seq (h3.seq h4))).post
    (fun cfg ⟨hR', _, _, _, _, _, _, _, hm⟩ => ⟨hR', hm⟩) |>.weaken ?_
  omega

/-! ### The matrix -/

/-- `V := α = cN (n+1) G`. -/
def mAl : Stmt := .seq (sofNat eV qCN) (.seq (smul eV eV eW) (smul eV eV eS1))

/-- `S2 := γ = cD (n+1) G`. -/
def mGa : Stmt := .seq (sofNat eS2 qCD) (.seq (smul eS2 eS2 eW) (smul eS2 eS2 eS1))

/-- `W := β = −2 cN`. -/
def mBe : Stmt := .seq (sofNat eW qCN) (.seq (sadd eW eW eW) (sneg eW eW))

/-- The inputs of `r1Core` for the matrix. -/
def mSet : Stmt :=
  .seq (mov vR qN) (.seq (mov vRow eQ) (.seq (mov vSI e2N) (.seq (mov vN qN) (.seq (mov vPU eU)
    (.seq (mov vX0 eU) (.seq (smov vB0 eW) (.seq (smov vAl eV) (smov vGa eS2))))))))

/-- **E4 (5)**: the matrix. -/
def mB : Stmt := .seq mAl (.seq mGa (.seq mBe (.seq mSet (r1Core true))))

theorem mB_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (m : ℕ → ℕ) (A : ℕ → ℕ → ℤ)
    (u : ℕ → ℤ) (hA : QsMem m Ly.pQ (nDim I.t I.k) A) (hu : SArr m Ly.pU 2 (nDim I.t I.k) u)
    (hz : ZeroFrom m Ly.F) (G : ℤ) (hG : 0 < G) (B : ℕ)
    (hα : Nat.size ((cNum I.t I.k : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) * G).natAbs ≤ B)
    (hβ : Nat.size (-((cNum I.t I.k : ℤ) + cNum I.t I.k)).natAbs ≤ B)
    (hAB : ∀ i < nDim I.t I.k, ∀ j < nDim I.t I.k, Nat.size (A i j).natAbs ≤ B)
    (huB : ∀ i < nDim I.t I.k, Nat.size (u i).natAbs ≤ B)
    (hGB : Nat.size G.natAbs ≤ B) (hnB : Nat.size (nDim I.t I.k + 1) ≤ B)
    (hS : Ly.F + 16 * B + 6 ≤ S) :
    HTB S mB (fun cfg => ((EG I Ly cfg ∧ cfg.mem = m) ∧ SReg cfg eS1 G) ∧
        SReg cfg eW ((nDim I.t I.k + 1 : ℕ) : ℤ))
      (fun cfg => EG I Ly cfg ∧ cfg.mem = wrRows m Ly.pQ (2 * nDim I.t I.k) (nDim I.t I.k)
        (r1New true ((cNum I.t I.k : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) * G)
          (-((cNum I.t I.k : ℤ) + cNum I.t I.k))
          ((cDen I.t I.k : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) * G) A u u) (nDim I.t I.k))
      (nDim I.t I.k * (nDim I.t I.k * (248 * B + 286) + 31 * B + 60) + 124 * B + 400) := by
  have hLq := hL.q; have hLx := hL.x; have hLl := hL.l; have hLg := hL.g; have hLu := hL.u
  have hLf := hL.f
  set n := nDim I.t I.k with hn
  set n1 : ℤ := ((n + 1 : ℕ) : ℤ) with hn1
  set α : ℤ := (cNum I.t I.k : ℤ) * n1 * G with hαd
  set γ : ℤ := (cDen I.t I.k : ℤ) * n1 * G with hγd
  set β : ℤ := -((cNum I.t I.k : ℤ) + cNum I.t I.k) with hβd
  have hZ : ∀ cfg, (EG I Ly cfg ∧ cfg.mem = m) → ZeroFrom cfg.mem (cfg.reg rFREE) :=
    fun cfg h => by rw [h.2, h.1.free]; exact hz
  let F0 : Config → Prop := fun cfg => (EG I Ly cfg ∧ cfg.mem = m) ∧ SReg cfg eS1 G
  have hF0 : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ ellW) → eS1 ∉ W ∧ eS1 + 1 ∉ W → Indep W F0 :=
    fun hW h => ((EG.indep hW).and (Indep.mem (· = m))).and (indep_sreg h.1 h.2 G)
  -- `α`
  have a1 := HTB.sofNat (S := S) (P := fun cfg => F0 cfg ∧ SReg cfg eW n1) (d := eV) (x := qCN)
    (n := cNum I.t I.k) (by decide) (by decide) (by decide)
    ((hF0 (by decide) (by decide)).and (indep_sreg (by decide) (by decide) n1))
  have a2 := HTB.smul (S := S) (P := fun cfg => F0 cfg ∧ SReg cfg eW n1) (d := eV) (x := eV) (y :=
      eW)
    (u := (cNum I.t I.k : ℤ)) (v := n1) (by decide) (by decide) (by decide)
    ((hF0 (by decide) (by decide)).and (indep_sreg (by decide) (by decide) n1))
    (fun cfg h => hZ cfg h.1.1)
    (fun cfg h => by rw [h.1.1.1.free, hn1, Int.natAbs_natCast]; omega)
  have a3 := HTB.smul (S := S) (P := fun cfg => F0 cfg ∧ SReg cfg eW n1) (d := eV) (x := eV) (y :=
      eS1)
    (u := (cNum I.t I.k : ℤ) * n1) (v := G) (by decide) (by decide) (by decide)
    ((hF0 (by decide) (by decide)).and (indep_sreg (by decide) (by decide) n1))
    (fun cfg h => hZ cfg h.1.1) (fun cfg h => by rw [h.1.1.1.free]; omega)
  -- `γ`
  let F1 : Config → Prop := fun cfg => (F0 cfg ∧ SReg cfg eW n1) ∧ SReg cfg eV α
  have hF1 : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ ellW) → eS1 ∉ W ∧ eS1 + 1 ∉ W →
      eW ∉ W ∧ eW + 1 ∉ W → eV ∉ W ∧ eV + 1 ∉ W → Indep W F1 := fun hW h h' h'' =>
    ((hF0 hW h).and (indep_sreg h'.1 h'.2 n1)).and (indep_sreg h''.1 h''.2 α)
  have g1 := HTB.sofNat (S := S) (P := F1) (d := eS2) (x := qCD) (n := cDen I.t I.k) (by decide)
    (by decide) (by decide) (hF1 (by decide) (by decide) (by decide) (by decide))
  have g2 := HTB.smul (S := S) (P := F1) (d := eS2) (x := eS2) (y := eW) (u := (cDen I.t I.k : ℤ))
    (v := n1) (by decide) (by decide) (by decide)
    (hF1 (by decide) (by decide) (by decide) (by decide)) (fun cfg h => hZ cfg h.1.1.1)
    (fun cfg h => by rw [h.1.1.1.1.free, hn1, Int.natAbs_natCast]; omega)
  have g3 := HTB.smul (S := S) (P := F1) (d := eS2) (x := eS2) (y := eS1)
    (u := (cDen I.t I.k : ℤ) * n1) (v := G) (by decide) (by decide) (by decide)
    (hF1 (by decide) (by decide) (by decide) (by decide)) (fun cfg h => hZ cfg h.1.1.1)
    (fun cfg h => by rw [h.1.1.1.1.free]; omega)
  -- `β`
  let F2 : Config → Prop := fun cfg => (EG I Ly cfg ∧ cfg.mem = m) ∧ SReg cfg eV α ∧
    SReg cfg eS2 γ
  have hF2 : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ ellW) → eV ∉ W ∧ eV + 1 ∉ W →
      eS2 ∉ W ∧ eS2 + 1 ∉ W → Indep W F2 := fun hW h h' =>
    ((EG.indep hW).and (Indep.mem (· = m))).and ((indep_sreg h.1 h.2 α).and
      (indep_sreg h'.1 h'.2 γ))
  have b1 := HTB.sofNat (S := S) (P := F2) (d := eW) (x := qCN) (n := cNum I.t I.k) (by decide)
    (by decide) (by decide) (hF2 (by decide) (by decide) (by decide))
  have b2 := HTB.sadd (S := S) (P := F2) (d := eW) (x := eW) (y := eW) (u := (cNum I.t I.k : ℤ))
    (v := (cNum I.t I.k : ℤ)) (by decide) (by decide) (by decide)
    (hF2 (by decide) (by decide) (by decide))
  have b3 := HTB.sneg (S := S) (P := F2) (d := eW) (x := eW) (u := (cNum I.t I.k : ℤ) + cNum I.t
      I.k)
    (by decide) (by decide) (hF2 (by decide) (by decide) (by decide))
  -- the inputs and the kernel
  have h4 : HTB S mSet (fun cfg => F2 cfg ∧ SReg cfg eW β)
      (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg vR = n ∧ cfg.reg vRow = Ly.pQ ∧
        cfg.reg vSI = 2 * n ∧ cfg.reg vN = n ∧ cfg.reg vPU = Ly.pU ∧ cfg.reg vX0 = Ly.pU ∧
        SReg cfg vB0 β ∧ SReg cfg vAl α ∧ SReg cfg vGa γ) 24 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨hE, hm⟩, hv, hs2⟩, hw⟩ => by
      refine ⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE,
        by rw [run_mem_of_stores (by decide) rfl cfg, hm], ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      all_goals simp +decide [mSet, run_mov, Arith.smov, hE.n, hE.qs, hE.n2, hE.u, hv.1, hv.2,
        hs2.1, hs2.2, hw.1, hw.2, ← hn]
  have hγ : 0 < γ := by
    have h1 : (0 : ℤ) < cDen I.t I.k := by exact_mod_cast cDen_pos (nDim_ge_two hL.t0 hL.k3)
    have h2 : (0 : ℤ) < n1 := by rw [hn1]; positivity
    positivity
  have hf := hL.fits (S := S) (by omega)
  have h5 := r1Core_specB true (S := S) (R := EG I Ly) ((EG.regIndep I Ly).mono (by decide)) m
      Ly.F n n
    Ly.pQ (2 * n) Ly.pU Ly.pU B α β γ A u u hz (fun c hc => hc.free) (by omega)
    (by omega) hA
    (fun m' hS => SArr.out hu (le_refl 2) (lo := Ly.pQ) (hi := Ly.pQ + n * (2 * n))
      (fun x hx => hS x (by omega)) (by omega))
    (fun m' hS => SArr.out hu (le_refl 2) (lo := Ly.pQ) (hi := Ly.pQ + n * (2 * n))
      (fun x hx => hS x (by omega)) (by omega))
    (by simp [GoodDiv, hγ]) hα hβ hAB huB huB (by omega) (by omega) (by omega)
  have hc1 : smulCost n1 ≤ 31 * B + 35 := smulCost_le (by rw [hn1, Int.natAbs_natCast]; exact hnB)
  have hc2 : smulCost G ≤ 31 * B + 35 := smulCost_le hGB
  have hal := (a1.pre fun cfg (h : F0 cfg ∧ SReg cfg eW n1) => ⟨h, h.1.1.1.cn⟩).seq
    ((a2.pre fun cfg ⟨h, hv⟩ => ⟨h, hv, h.2⟩).seq
    (a3.pre fun cfg ⟨h, hv⟩ => ⟨h, hv, h.1.2⟩))
  have hga := (g1.pre fun cfg h => ⟨h, h.1.1.1.1.cd⟩).seq
    ((g2.pre fun cfg ⟨h, hs⟩ => ⟨h, hs, h.1.2⟩).seq
    (g3.pre fun cfg ⟨h, hs⟩ => ⟨h, hs, h.1.1.2⟩))
  have hbe := (b1.pre fun cfg (h : F1 cfg ∧ SReg cfg eS2 γ) => ⟨⟨h.1.1.1.1, h.1.2, h.2⟩,
      h.1.1.1.1.1.cn⟩).seq
    ((b2.pre fun cfg ⟨h, hw⟩ => ⟨h, hw, hw⟩).seq b3)
  refine (hal.seq (hga.seq (hbe.seq (h4.seq h5)))).post
    (fun cfg ⟨⟨hE, _, hmem, _⟩, h0⟩ => ⟨hE, by rw [hmem, h0, Nat.sub_zero]⟩) |>.weaken ?_
  omega

end STACS2027.Runtimes.QPRam
