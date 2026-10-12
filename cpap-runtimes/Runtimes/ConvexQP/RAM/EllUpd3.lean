module

public import Runtimes.ConvexQP.RAM.EllUpd2
import Mathlib.Tactic

/-!
# Lemma 16, Phase E on the RAM: E4, the update (3): assembly

`upd = uB; dB; sB; aB; mB` turns the state `st` in memory into `ellUpdate I K st g`
(`upd_specB`, below every `S ≥ F + 16 B + 6`), given the cut `g` in memory, `G > 0` and a bound
`B` on the bit lengths of the numbers of the update (`UpdBits`). The values agree with `ellUpdate` entrywise: `u` by
`mulVec_flatM`, `G` by `dot_flatR`, `S` literally, the center up to `mul_comm`, the matrix up to
`ring`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

variable {S : ℕ}

/-- **E4**: the update of center and matrix. -/
def upd : Stmt := .seq uB (.seq dB (.seq sB (.seq aB mB)))

theorem upd_wregs : ∀ r ∈ wregs upd, r ∈ ellW := by decide +kernel

/-- The bit lengths of the update are at most `B`. -/
structure UpdBits (I : Inst) (st : EllState I) (g : Idx I → ℤ) (B : ℕ) : Prop where
  h1 : 1 ≤ B
  hp : 3 * prec I.t I.k + 1 ≤ B
  hg : ∀ j < nDim I.t I.k, Nat.size (flatR g j).natAbs ≤ B
  hu : ∀ j < nDim I.t I.k, Nat.size (flatR (updU I st g) j).natAbs ≤ B
  hq : ∀ i < nDim I.t I.k, ∀ j < nDim I.t I.k, Nat.size (flatM st.Qs i j).natAbs ≤ B
  hG : Nat.size (updG I st g).natAbs ≤ B
  hα : Nat.size ((cNum I.t I.k : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) * updG I st g).natAbs ≤ B
  hβ : Nat.size (-((cNum I.t I.k : ℤ) + cNum I.t I.k)).natAbs ≤ B
  hn : Nat.size (nDim I.t I.k + 1) ≤ B
  hN : Nat.size ((updG I st g).toNat * 2 ^ (3 * prec I.t I.k)) ≤ B

/-- The cost of the update. -/
def updCost (n B : ℕ) : ℕ :=
  n * n * (300 * B + 400) + n * (220 * B + 500) + 40 * (B + 1) ^ 2 + 250 * B + 600

/-! ### The values -/

theorem updG_flat {I : Inst} (st : EllState I) (g : Idx I → ℤ) :
    ∑ a ∈ Finset.range (nDim I.t I.k),
      Arith.mulVec (flatM st.Qs) (flatR g) (nDim I.t I.k) a * flatR g a = updG I st g := by
  simp only [mulVec_flatM']
  rw [nDim_eq, dot_flatR]
  rfl

theorem center_flat {I : Inst} (st : EllState I) (g : Idx I → ℤ) {a : ℕ}
    (ha : a < nDim I.t I.k) :
    axNew true 1 (-1)
        ((updS I (consts I.t I.k) st g : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ))
        ((2 ^ (2 * prec I.t I.k) : ℕ) : ℤ) (flatR st.As)
        (Arith.mulVec (flatM st.Qs) (flatR g) (nDim I.t I.k)) a =
      flatR (ellUpdate I (consts I.t I.k) st g).As a := by
  rw [nDim_eq] at ha
  obtain ⟨i, rfl⟩ := fIdx_surj ha
  rw [axNew, mulVec_flatM', flatR_fIdx, flatR_fIdx, flatR_fIdx, rnd]
  simp only [ellUpdate, consts, ite_true]
  push_cast
  rw [mul_comm ((2 : ℤ) ^ (2 * prec I.t I.k)), mul_comm (updS I _ st g : ℤ)]
  unfold updU; ring

theorem matrix_flat {I : Inst} (st : EllState I) (g : Idx I → ℤ) {a b : ℕ}
    (ha : a < nDim I.t I.k) (hb : b < nDim I.t I.k) :
    r1New true ((cNum I.t I.k : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) * updG I st g)
        (-((cNum I.t I.k : ℤ) + cNum I.t I.k))
        ((cDen I.t I.k : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) * updG I st g) (flatM st.Qs)
        (Arith.mulVec (flatM st.Qs) (flatR g) (nDim I.t I.k))
        (Arith.mulVec (flatM st.Qs) (flatR g) (nDim I.t I.k)) a b =
      flatM (ellUpdate I (consts I.t I.k) st g).Qs a b := by
  rw [nDim_eq] at ha hb
  obtain ⟨i, rfl⟩ := fIdx_surj ha
  obtain ⟨i', rfl⟩ := fIdx_surj hb
  rw [r1New, mulVec_flatM', mulVec_flatM', flatM_fIdx, flatM_fIdx, flatR_fIdx, flatR_fIdx,
    flatR_fIdx, flatR_fIdx, rnd]
  simp only [ellUpdate, consts, ite_true]
  push_cast
  congr 1
  unfold updU; ring

/-! ### The update -/

theorem updCost_ge (n B N : ℕ) (hN : Nat.size N ≤ B) (p : ℕ) (hp : 3 * p + 1 ≤ B) (sc : ℕ)
    (hsc : sc ≤ 31 * B + 35) :
    n * (n * (31 * B + 87) + 19) + 17 + (n * (31 * B + 87) + 18 +
      (31 * (3 * p + 1) + 12 * p + isqrtCost N + sc + 57 +
      (n * (155 * B + 302) + 8 * p + 31 +
      (n * (n * (248 * B + 286) + 31 * B + 60) + 124 * B + 400)))) ≤ updCost n B := by
  have h1 := isqrtCost_le N
  have h2 : 40 * (Nat.size N + 1) ^ 2 ≤ 40 * (B + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have e : n * (n * (31 * B + 87) + 19) + n * (31 * B + 87) + n * (155 * B + 302) +
      n * (n * (248 * B + 286) + 31 * B + 60) = n * n * (279 * B + 373) + n * (217 * B + 468) := by
    ring
  have h3 : n * n * (279 * B + 373) ≤ n * n * (300 * B + 400) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : n * (217 * B + 468) ≤ n * (220 * B + 500) := Nat.mul_le_mul_left _ (by omega)
  unfold updCost
  omega

/-- **E4**: `upd` replaces the state `st` in memory by `ellUpdate I K st g` (`g` in memory at
`eG`, `G > 0`, all bit lengths at most `B`); `H` and the free memory are kept. -/
theorem upd_specB (I : Inst) (Ly : Lay) (hL : Ly.Ok I) (st : EllState I) (g : Idx I → ℤ)
    (m : ℕ → ℕ) (hSt : StMem I Ly st m) (hg : SArr m Ly.pG 2 (nDim I.t I.k) (flatR g))
    (hH : HMem I m Ly.bh) (hz : ZeroFrom m Ly.F) (hG : 0 < updG I st g) (B : ℕ)
    (hB : UpdBits I st g B) (hS : Ly.F + 16 * B + 6 ≤ S) :
    HTB S upd (fun cfg => EG I Ly cfg ∧ cfg.mem = m)
      (fun cfg => EG I Ly cfg ∧ StMem I Ly (ellUpdate I (consts I.t I.k) st g) cfg.mem ∧
        HMem I cfg.mem Ly.bh ∧ ZeroFrom cfg.mem Ly.F)
      (updCost (nDim I.t I.k) B) := by
  have hLh := hL.h; have hLq := hL.q; have hLx := hL.x; have hLl := hL.l; have hLg := hL.g
  have hLu := hL.u; have hLf := hL.f
  have hBp := hB.hp
  set uf := Arith.mulVec (flatM st.Qs) (flatR g) (nDim I.t I.k) with huf
  set G := updG I st g with hGd
  set Sq := Nat.sqrt (G.toNat * 2 ^ (3 * prec I.t I.k)) with hSq
  have hSu : Sq = updS I (consts I.t I.k) st g := rfl
  have hS1 : 1 ≤ Sq := by
    have h0 : 0 < G.toNat := Int.lt_toNat.mpr hG
    exact Nat.sqrt_pos.mpr (Nat.mul_pos h0 (Nat.two_pow_pos _))
  set γ : ℤ := (Sq : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) with hγd
  have hγ : 0 < γ := by
    have : (0 : ℤ) < Sq := by exact_mod_cast hS1
    exact mul_pos this (by exact_mod_cast Nat.succ_pos (nDim I.t I.k))
  -- `u`
  have h1 := uB_specB (S := S) I Ly hL st g m hSt hg hz B hB.hg (by omega)
  set m1 := wrArr m Ly.pU 2 uf (nDim I.t I.k) with hm1
  have hm1o : ∀ x, (x < Ly.pU ∨ Ly.pU + nDim I.t I.k * 2 ≤ x) → m1 x = m x :=
    fun x hx => wrArr_of_out (le_refl 2) hx
  have hu1 : SArr m1 Ly.pU 2 (nDim I.t I.k) uf := sarr_wrArr (le_refl 2) _
  have hg1 : SArr m1 Ly.pG 2 (nDim I.t I.k) (flatR g) := SArr.out hg (le_refl 2) hm1o (by omega)
  have hz1 : ZeroFrom m1 Ly.F := zeroFrom_wrArr (le_refl 2) hz (by omega)
  have hSt1 : StMem I Ly st m1 := hSt.out hL hm1o (by omega)
  have hufB : ∀ j < nDim I.t I.k, Nat.size (uf j).natAbs ≤ B := fun j hj => by
    rw [huf, mulVec_flatM']; exact hB.hu j hj
  -- `G`
  have h2 := dB_specB (S := S) I Ly hL m1 uf (flatR g) hu1 hg1 hz1 B hB.hg (by omega)
  have hGe : ∑ a ∈ Finset.range (nDim I.t I.k), uf a * flatR g a = G := updG_flat st g
  -- `Sq`
  have h3 := sB_specB (S := S) I Ly m1 hz1 G hG.le B (by omega) hB.hN hB.hn (by omega)
  -- the center
  have h4 := aB_specB (S := S) I Ly hL m1 (flatR st.As) uf hSt1.a hu1 hz1 G γ hγ
    ((nDim I.t I.k + 1 : ℕ) : ℤ) B hB.h1
    (by omega) hufB (by omega)
  set m2 := wrArr m1 Ly.pA 2
    (axNew true 1 (-1) γ ((2 ^ (2 * prec I.t I.k) : ℕ) : ℤ) (flatR st.As) uf)
    (nDim I.t I.k) with hm2
  have hm2o : ∀ x, (x < Ly.pA ∨ Ly.pA + nDim I.t I.k * 2 ≤ x) → m2 x = m1 x :=
    fun x hx => wrArr_of_out (le_refl 2) hx
  have hq2 : QsMem m2 Ly.pQ (nDim I.t I.k) (flatM st.Qs) := QsMem.out hSt1.q hm2o (by omega)
  have hu2 : SArr m2 Ly.pU 2 (nDim I.t I.k) uf := SArr.out hu1 (le_refl 2) hm2o (by omega)
  have hz2 : ZeroFrom m2 Ly.F := zeroFrom_wrArr (le_refl 2) hz1 (by omega)
  have ha2 : SArr m2 Ly.pA 2 (nDim I.t I.k)
      (axNew true 1 (-1) γ ((2 ^ (2 * prec I.t I.k) : ℕ) : ℤ) (flatR st.As) uf) :=
    sarr_wrArr (le_refl 2) _
  -- the matrix
  have h5 := mB_specB (S := S) I Ly hL m2 (flatM st.Qs) uf hq2 hu2 hz2 G hG B hB.hα hB.hβ hB.hq hufB
    hB.hG hB.hn hS
  have hsi : nDim I.t I.k * 2 ≤ 2 * nDim I.t I.k := by omega
  have hrow : ∀ x, (x < Ly.pQ ∨ Ly.pQ + nDim I.t I.k * (2 * nDim I.t I.k) ≤ x) →
      wrRows m2 Ly.pQ (2 * nDim I.t I.k) (nDim I.t I.k)
        (r1New true ((cNum I.t I.k : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) * G)
        (-((cNum I.t I.k : ℤ) + cNum I.t I.k))
        ((cDen I.t I.k : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) * G)
        (flatM st.Qs) uf uf) (nDim I.t I.k) x = m2 x := fun x hx => wrRows_of_out hsi hx
  have hc := smulCost_le (v := ((nDim I.t I.k + 1 : ℕ) : ℤ)) (B := B)
    (by rw [Int.natAbs_natCast]; exact hB.hn)
  set m3 := wrRows m2 Ly.pQ (2 * nDim I.t I.k) (nDim I.t I.k)
    (r1New true ((cNum I.t I.k : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) * G)
    (-((cNum I.t I.k : ℤ) + cNum I.t I.k)) ((cDen I.t I.k : ℤ) * ((nDim I.t I.k + 1 : ℕ) : ℤ) * G)
    (flatM st.Qs) uf uf) (nDim I.t I.k) with hm3
  have hpost : StMem I Ly (ellUpdate I (consts I.t I.k) st g) m3 ∧ HMem I m3 Ly.bh ∧
      ZeroFrom m3 Ly.F := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · refine SArr.out (SArr.congr_fun ha2 fun a ha => ?_) (le_refl 2) hrow (by omega)
      rw [hγd, hSu]
      exact center_flat st g ha
    · intro a ha
      exact SArr.congr_fun (sarr_wrRows hsi _ ha) fun b hb => matrix_flat st g ha hb
    · exact HMem.out (HMem.out (HMem.out hH hm1o (by omega)) hm2o (by omega)) hrow (by omega)
    · exact zeroFrom_wrRows hsi hz2 (by omega)
  refine ((h1.seq ((h2.pre fun cfg h => h).seq ((h3.pre fun cfg ⟨h, hs⟩ =>
      ⟨h, by rw [← hGe]; exact hs⟩).seq ((h4.pre fun cfg ⟨⟨h, hs⟩, _, hw, hv⟩ =>
        ⟨⟨h, hs⟩, hw, hv⟩).seq (h5.pre fun cfg ⟨⟨hE, hs, hw⟩, hm⟩ => ⟨⟨⟨hE, hm⟩, hs⟩, hw⟩))))).post
    fun cfg h => ⟨h.1, by rw [h.2]; exact hpost⟩).weaken ?_
  exact updCost_ge (nDim I.t I.k) B _ hB.hN (prec I.t I.k) hBp _ hc

end STACS2027.Runtimes.QPRam
