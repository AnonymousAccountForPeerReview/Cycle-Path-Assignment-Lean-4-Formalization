module

public import Runtimes.ConvexQP.RAM.EllLayout
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: E4, the update (1): `u`, `G`, `S`

With the state `(As, Qs)` and the cut `g` in memory:
* `uB`: `u = Qs g` at `eU` (`mvCore`, `mulVec_flatM`);
* `dB`: `G = ∑_a u_a g_a = g · u` into `eS1` (`dotCore`, the multipliers are the `g_a`);
* `sB`: `S = ⌊√(G · 2^{3p})⌋` into `eT2` (`pow2N`, `mulN`, `isqrtN`), `n + 1` into `eW` and
  `(n + 1) S` into `eV`.

The center and the matrix are updated in `EllUpd2.lean`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

/-! ### Flat indices of the update -/

/-- The flat `u = Qs g`. -/
theorem mulVec_flatM' {I : Inst} (Q : Matrix (Idx I) (Idx I) ℤ) (g : Idx I → ℤ) (a : ℕ) :
    Arith.mulVec (flatM Q) (flatR g) (nDim I.t I.k) a = flatR (Matrix.mulVec Q g) a := by
  rw [nDim_eq]; exact mulVec_flatM Q g a

/-! ### `u = Qs g` -/

/-- The inputs of `mvCore` for `u = Qs g`. -/
def uSet : Stmt :=
  .seq (mov vR qN) (.seq (mov vRow eQ) (.seq (mov vSI e2N) (.seq (mov vN qN)
    (.seq (.const vSA 2) (.seq (mov vX0 eG) (.seq (.const vSX 2) (mov vPU eU)))))))

/-- **E4 (1)**: `u := Qs g` at `eU`. -/
def uB : Stmt := .seq uSet mvCore

theorem uB_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (st : EllState I) (g : Idx I → ℤ)
    (m : ℕ → ℕ) (hSt : StMem I Ly st m) (hg : SArr m Ly.pG 2 (nDim I.t I.k) (flatR g))
    (hz : ZeroFrom m Ly.F) (B : ℕ) (hB : ∀ j < nDim I.t I.k, Nat.size (flatR g j).natAbs ≤ B)
    (hS : Ly.F + 2 * B ≤ S) :
    HTB S uB (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => EG I Ly cfg ∧ cfg.mem = wrArr m Ly.pU 2
        (Arith.mulVec (flatM st.Qs) (flatR g) (nDim I.t I.k)) (nDim I.t I.k))
      (nDim I.t I.k * (nDim I.t I.k * (31 * B + 87) + 19) + 17) := by
  have h0 : HTB S uSet (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => EG I Ly cfg ∧ cfg.mem = m ∧ cfg.reg vR = nDim I.t I.k ∧ cfg.reg vRow = Ly.pQ ∧
        cfg.reg vSI = 2 * nDim I.t I.k ∧ cfg.reg vN = nDim I.t I.k ∧ cfg.reg vSA = 2 ∧
        cfg.reg vX0 = Ly.pG ∧ cfg.reg vSX = 2 ∧ cfg.reg vPU = Ly.pU) 16 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨hE, hm⟩ => by
      refine ⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE,
        by rw [run_mem_of_stores (by decide) rfl cfg, hm], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp +decide [uSet, run_mov, hE.n, hE.qs, hE.n2, hE.g, hE.u]
  have hf := hL.fits (S := S) (by omega)
  have hm := mvCore_specB (S := S) (R := EG I Ly) ((EG.regIndep I Ly).mono (by decide)) m Ly.F
    (nDim I.t I.k) Ly.pQ (2 * nDim I.t I.k) (nDim I.t I.k) 2 Ly.pG 2 Ly.pU B (flatM st.Qs)
    (flatR g) hz (fun c hc => hc.free) (by have := hL.f; omega)
    (fun m' hS => QsMem.out hSt.q (lo := Ly.pU) (hi := Ly.pU + nDim I.t I.k * 2)
      (fun x hx => hS x (by omega)) (by have := hL.x; have := hL.l; have := hL.g; have := hL.u
                                        omega))
    (fun m' hS => SArr.out hg (le_refl 2) (lo := Ly.pU) (hi := Ly.pU + nDim I.t I.k * 2)
      (fun x hx => hS x (by omega)) (by have := hL.u; omega)) hB hS
    (fun i hi j hj => addr_lt_rows (by omega) hf.2.2.1 hi hj)
    (fun j hj => addr_lt_of_stride (le_refl 2) hf.2.2.2.2.2.1 hj)
  refine (h0.seq hm).mono (fun _ h => h) (fun cfg ⟨⟨hE, _, hmem, _⟩, h0⟩ => ⟨hE, ?_⟩)
    (by omega)
  rw [hmem, h0, Nat.sub_zero]

/-! ### `G = g · u` -/

/-- The inputs of `dotCore` for `G = ∑ u_a g_a`. -/
def dSet : Stmt :=
  .seq (mov vN qN) (.seq (mov vPA eU) (.seq (.const vSA 2) (.seq (mov vPX eG) (.const vSX 2))))

/-- **E4 (2)**: `S1 := G`. -/
def dB : Stmt := .seq dSet (.seq dotCore (smov eS1 vAcc))

theorem dB_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (m : ℕ → ℕ) (uf gf : ℕ → ℤ)
    (hu : SArr m Ly.pU 2 (nDim I.t I.k) uf) (hg : SArr m Ly.pG 2 (nDim I.t I.k) gf)
    (hz : ZeroFrom m Ly.F) (B : ℕ) (hB : ∀ j < nDim I.t I.k, Nat.size (gf j).natAbs ≤ B)
    (hS : Ly.F + 2 * B ≤ S) :
    HTB S dB (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => (EG I Ly cfg ∧ cfg.mem = m) ∧
        SReg cfg eS1 (∑ a ∈ Finset.range (nDim I.t I.k), uf a * gf a))
      (nDim I.t I.k * (31 * B + 87) + 18) := by
  have _ := hL
  have h0 : HTB S dSet (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => (EG I Ly cfg ∧ cfg.mem = m) ∧ cfg.reg vN = nDim I.t I.k ∧ cfg.reg vPA = Ly.pU ∧
        cfg.reg vSA = 2 ∧ cfg.reg vPX = Ly.pG ∧ cfg.reg vSX = 2) 9 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨hE, hm⟩ => by
      refine ⟨⟨(EG.regIndep I Ly).run_of_sub (by decide) (by decide) hE,
        by rw [run_mem_of_stores (by decide) rfl cfg, hm]⟩, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp +decide [dSet, run_mov, hE.n, hE.g, hE.u]
  have hf := hL.fits (S := S) (by omega)
  have h1 := dotCore_specB (S := S) (P := fun cfg => EG I Ly cfg ∧ cfg.mem = m)
    ((EG.indep (by decide)).and (Indep.mem (· = m))) (fun cfg h => by rw [h.2, h.1.free]; exact hz)
    (nDim I.t I.k) Ly.pU 2 Ly.pG 2 B uf gf (fun cfg h => by rw [h.2]; exact hu)
    (fun cfg h => by rw [h.2]; exact hg) hB (fun cfg h => by rw [h.1.free]; omega)
    (fun j hj => addr_lt_of_stride (le_refl 2) hf.2.2.2.2.2.2 hj)
    (fun j hj => addr_lt_of_stride (le_refl 2) hf.2.2.2.2.2.1 hj)
  have h2 := HTB.smov (S := S) (P := fun cfg => EG I Ly cfg ∧ cfg.mem = m) (d := eS1) (x := vAcc)
    (z := ∑ a ∈ Finset.range (nDim I.t I.k), uf a * gf a) (by decide) (by decide) (by decide)
    (by decide) ((EG.indep (by decide)).and (Indep.mem (· = m)))
  refine (h0.seq (h1.seq (h2.pre fun cfg ⟨h, _, _, _, _, _, hs⟩ => ⟨h, hs⟩))).weaken ?_
  omega

/-! ### `S = ⌊√(G 2^{3p})⌋` -/

/-- **E4 (3)**: `T2 := S = ⌊√(G · 2^{3p})⌋`, `W := n + 1`, `V := (n + 1) S`. -/
def sB : Stmt :=
  .seq (.seq (.add eT1 qP qP) (.add eT1 eT1 qP)) (.seq (pow2N eT1 eT1)
    (.seq (mulN eT1 (eS1 + 1) eT1) (.seq (isqrtN eT2 eT1)
    (.seq (addc eT1 qN 1) (.seq (sofNat eW eT1) (.seq (sofNat eV eT2) (smul eV eV eW)))))))

theorem sB_specB (I : Inst) (Ly : Lay) (m : ℕ → ℕ) (hz : ZeroFrom m Ly.F) (G : ℤ) (hG : 0 ≤ G)
    (B : ℕ) (hB3 : 3 * prec I.t I.k + 1 ≤ B)
    (hBN : Nat.size (G.toNat * 2 ^ (3 * prec I.t I.k)) ≤ B)
    (hBn : Nat.size (nDim I.t I.k + 1) ≤ B) (hS : Ly.F + 2 * B + 2 ≤ S) :
    HTB S sB (fun cfg => (EG I Ly cfg ∧ cfg.mem = m) ∧ SReg cfg eS1 G)
      (fun cfg => ((EG I Ly cfg ∧ cfg.mem = m) ∧ SReg cfg eS1 G) ∧
        cfg.reg eT2 = Nat.sqrt (G.toNat * 2 ^ (3 * prec I.t I.k)) ∧
        SReg cfg eW ((nDim I.t I.k + 1 : ℕ) : ℤ) ∧
        SReg cfg eV ((Nat.sqrt (G.toNat * 2 ^ (3 * prec I.t I.k)) : ℤ) * (nDim I.t I.k + 1 : ℕ)))
      (31 * (3 * prec I.t I.k + 1) + 12 * prec I.t I.k +
        isqrtCost (G.toNat * 2 ^ (3 * prec I.t I.k)) + smulCost ((nDim I.t I.k + 1 : ℕ) : ℤ) +
        57) := by
  set p := prec I.t I.k with hp
  set n := nDim I.t I.k with hn
  set Sq := Nat.sqrt (G.toNat * 2 ^ (3 * p)) with hSq
  let F0 : Config → Prop := fun cfg => (EG I Ly cfg ∧ cfg.mem = m) ∧ SReg cfg eS1 G
  have hF0 : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ ellW) → eS1 ∉ W ∧ eS1 + 1 ∉ W → Indep W F0 :=
    fun hW h => ((EG.indep hW).and (Indep.mem (· = m))).and (indep_sreg h.1 h.2 G)
  have hZ : ∀ cfg, F0 cfg → ZeroFrom cfg.mem (cfg.reg rFREE) := fun cfg h => by
    rw [h.1.2, h.1.1.free]; exact hz
  have h1 : HTB S (.seq (.add eT1 qP qP) (.add eT1 eT1 qP)) F0
      (fun cfg => F0 cfg ∧ cfg.reg eT1 = 3 * p) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg h => ⟨(hF0 (W := wregs (.seq (.add
        eT1 qP qP)
      (.add eT1 eT1 qP))) (by decide) (by decide)).run (by decide) rfl rfl h,
        by simp +decide [h.1.1.p]; ring⟩
  have h2 := HTB.pow2N (S := S) (P := F0) (d := eT1) (e := eT1) (k := 3 * p) (by decide)
    (hF0 (by decide) (by decide))
  have h3 := HTB.mulN (S := S) (P := F0) (d := eT1) (x := eS1 + 1) (y := eT1) (a := G.toNat)
    (b := 2 ^ (3 * p)) (by decide) (by decide) (hF0 (by decide) (by decide)) hZ
    (fun cfg h => by rw [h.1.1.free, Nat.size_pow]; omega)
  have h4 := HTB.isqrtN (S := S) (P := F0) (d := eT2) (x := eT1) (N := G.toNat * 2 ^ (3 * p))
    (by decide) (hF0 (by decide) (by decide)) hZ (fun cfg h => by rw [h.1.1.free]; omega)
  have h5 : HTB S (addc eT1 qN 1) (fun cfg => F0 cfg ∧ cfg.reg eT2 = Sq)
      (fun cfg => (F0 cfg ∧ cfg.reg eT2 = Sq) ∧ cfg.reg eT1 = n + 1) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg h => ⟨((hF0 (W := wregs (addc eT1
        qN 1)) (by decide)
      (by decide)).and (Indep.reg (r := eT2) (by decide) (· = Sq))).run (by decide) rfl rfl h,
        by simp +decide [run_addc, h.1.1.1.n, hn]⟩
  have h6 := HTB.sofNat (S := S) (P := fun cfg => F0 cfg ∧ cfg.reg eT2 = Sq) (d := eW) (x := eT1)
    (n := n + 1) (by decide) (by decide) (by decide)
    ((hF0 (by decide) (by decide)).and (Indep.reg (r := eT2) (by decide) (· = Sq)))
  have h7 := HTB.sofNat (S := S) (P := fun cfg => (F0 cfg ∧ cfg.reg eT2 = Sq) ∧ SReg cfg eW ((n +
      1 : ℕ) : ℤ))
    (d := eV) (x := eT2) (n := Sq) (by decide) (by decide) (by decide)
    (((hF0 (by decide) (by decide)).and (Indep.reg (r := eT2) (by decide) (· = Sq))).and
      (indep_sreg (by decide) (by decide) _))
  have h8 := HTB.smul (S := S) (P := fun cfg => (F0 cfg ∧ cfg.reg eT2 = Sq) ∧ SReg cfg eW ((n +
      1 : ℕ) : ℤ))
    (d := eV) (x := eV) (y := eW) (u := (Sq : ℤ)) (v := ((n + 1 : ℕ) : ℤ)) (by decide) (by decide)
    (by decide) (((hF0 (by decide) (by decide)).and (Indep.reg (r := eT2) (by decide) (· = Sq))).and
      (indep_sreg (by decide) (by decide) _)) (fun cfg h => hZ cfg h.1.1)
    (fun cfg h => by rw [h.1.1.1.1.free, Int.natAbs_natCast]; omega)
  have hGn : (G.natAbs : ℕ) = G.toNat := by
    have h1 : ((G.natAbs : ℕ) : ℤ) = G := Int.natAbs_of_nonneg hG
    have h2 : ((G.toNat : ℕ) : ℤ) = G := Int.toNat_of_nonneg hG
    exact_mod_cast h1.trans h2.symm
  refine (h1.seq (h2.seq ((h3.pre fun cfg ⟨h, he⟩ => ⟨h, by rw [h.2.2, hGn], he⟩).seq
    (h4.seq (h5.seq ((h6.pre fun cfg ⟨h, he⟩ => ⟨h, he⟩).seq
    ((h7.pre fun cfg ⟨h, hw⟩ => ⟨⟨h, hw⟩, h.2⟩).seq
    ((h8.pre fun cfg ⟨h, hv⟩ => ⟨h, hv, h.2⟩).post
      fun cfg ⟨⟨⟨h, ht⟩, hw⟩, hv⟩ => ⟨h, ht, hw, hv⟩)))))))).weaken ?_
  simp only [mulCost, Nat.size_pow]
  omega

end STACS2027.Runtimes.QPRam
