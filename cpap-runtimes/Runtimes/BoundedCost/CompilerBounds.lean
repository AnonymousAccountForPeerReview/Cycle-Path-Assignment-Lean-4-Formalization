module

public import Runtimes.BoundedCost.CompilerLayout
public import Runtimes.BoundedCost.SearchWork
import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 4000

namespace STACS2027.Runtimes.BoundedCost

def compilerNodeTime (constant registers clauses : ℕ) : ℕ :=
  (800 + registers) * ((constant + 1) * (2 * clauses + 2) ^ 2 + 1)

def compilerPathTime (constant registers clauses budget : ℕ) : ℕ :=
  let n := 2 * clauses + 1
  let d := min budget clauses + 1
  d * (compilerNodeTime constant registers clauses + 7) + 3 + 8 * (clauses + 2 * n) + 21

def compilerInnerTime (constant registers clauses budget : ℕ) : ℕ :=
  let d := min budget clauses + 1
  6 * d + 13 + 25 * d + 11 +
    3 ^ d * (compilerPathTime constant registers clauses budget + 19 * d + 8)

def compilerOuterTime (constant registers clauses budget special : ℕ) : ℕ :=
  let n := 2 * clauses + 1
  6 * special + 13 + 25 * special + 11 +
    3 ^ special * (12 * n + 44 * special + 11 +
      compilerInnerTime constant registers clauses budget + 19 * special + 12)

def compilerPrefixTime (constant registers clauses budget special : ℕ) : ℕ :=
  300 * (clauses + (2 * clauses + 1) + 1) +
    compilerOuterTime constant registers clauses budget special

def compilerFinalTime (constant clauses : ℕ) : ℕ :=
  320 * (clauses + 1) ^ 2 + 400 + 5 * (constant + 1) + 80 * (clauses + 1)

def compilerUniformConstant (constant registers : ℕ) : ℕ :=
  100 * (800 + registers) * (constant + 2)

theorem compilerNodeTime_le (constant registers clauses : ℕ) :
    compilerNodeTime constant registers clauses ≤
      (800 + registers) * (constant + 2) * (2 * clauses + 3) ^ 2 := by
  unfold compilerNodeTime
  have hpow : (2 * clauses + 2) ^ 2 ≤ (2 * clauses + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul := Nat.mul_le_mul_left (constant + 1) hpow
  have hsq : 1 ≤ (2 * clauses + 3) ^ 2 := by nlinarith
  have hi : (constant + 1) * (2 * clauses + 2) ^ 2 + 1 ≤
      (constant + 2) * (2 * clauses + 3) ^ 2 := by nlinarith only [hmul, hsq]
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (800 + registers) hi

theorem compilerPathTime_le (constant registers clauses budget : ℕ) :
    compilerPathTime constant registers clauses budget ≤
      ((800 + registers) * (constant + 2) + 40) *
        (min budget clauses + 1) * (2 * clauses + 3) ^ 2 := by
  let d := min budget clauses + 1
  let q := 2 * clauses + 3
  let a := (800 + registers) * (constant + 2)
  have hnode := Nat.mul_le_mul_left d (compilerNodeTime_le constant registers clauses)
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hqq : q ≤ q ^ 2 := by nlinarith only [hq]
  have hdv : d ≤ d * q ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hqv : q ≤ d * q ^ 2 := hqq.trans (Nat.le_mul_of_pos_left _ hd)
  have hv : 1 ≤ d * q ^ 2 := Nat.succ_le_of_lt (by positivity)
  have hrestore : 3 + 8 * (clauses + 2 * (2 * clauses + 1)) + 21 ≤ 23 * q := by dsimp [q]; omega
  change d * compilerNodeTime constant registers clauses ≤ d * (a * q ^ 2) at hnode
  change compilerPathTime constant registers clauses budget ≤ (a + 40) * d * q ^ 2
  unfold compilerPathTime
  change d * (compilerNodeTime constant registers clauses + 7) + 3 +
      8 * (clauses + 2 * (2 * clauses + 1)) + 21 ≤ _
  nlinarith only [hnode, hdv, hqv, hrestore]

private theorem compilerInnerArithmetic (a d v p path : ℕ)
    (hdv : d ≤ v) (hv : 1 ≤ v) (hp : 1 ≤ p) (hpath : path ≤ (a + 40) * v) :
    6 * d + 13 + 25 * d + 11 + p * (path + 19 * d + 8) ≤ p * ((a + 150) * v) := by
  have hvp : v ≤ p * v := Nat.le_mul_of_pos_left _ hp
  have hins : path + 19 * d + 8 ≤ (a + 67) * v := by nlinarith only [hpath, hdv, hv]
  have hmul := Nat.mul_le_mul_left p hins
  have hbase : 6 * d + 13 + 25 * d + 11 ≤ 55 * v := by omega
  have hbase' := hbase.trans (Nat.mul_le_mul_left 55 hvp)
  calc
    _ ≤ 55 * (p * v) + p * ((a + 67) * v) := Nat.add_le_add hbase' hmul
    _ ≤ p * ((a + 150) * v) := by nlinarith

theorem compilerInnerTime_le (constant registers clauses budget : ℕ) :
    compilerInnerTime constant registers clauses budget ≤
      3 ^ (min budget clauses + 1) *
        (((800 + registers) * (constant + 2) + 150) *
          (min budget clauses + 1) * (2 * clauses + 3) ^ 2) := by
  have hdv : min budget clauses + 1 ≤ (min budget clauses + 1) * (2 * clauses + 3) ^ 2 :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hv : 1 ≤ (min budget clauses + 1) * (2 * clauses + 3) ^ 2 := by omega
  have hp : 1 ≤ 3 ^ (min budget clauses + 1) := Nat.one_le_pow _ _ (by decide)
  have hpath := compilerPathTime_le constant registers clauses budget
  simpa only [compilerInnerTime, Nat.mul_assoc] using
    compilerInnerArithmetic ((800 + registers) * (constant + 2)) (min budget clauses + 1)
      ((min budget clauses + 1) * (2 * clauses + 3) ^ 2) (3 ^ (min budget clauses + 1))
      (compilerPathTime constant registers clauses budget) hdv hv hp (by simpa only [Nat.mul_assoc] using hpath)

private theorem compilerOuterArithmetic (a d v p inner n s t : ℕ)
    (hs : s ≤ d) (hdv : d ≤ v) (hnv : n ≤ v) (hv : 1 ≤ v) (hp : 1 ≤ p)
    (ht : t ≤ p) (hinner : inner ≤ p * ((a + 150) * v)) :
    6 * s + 13 + 25 * s + 11 + t * (12 * n + 44 * s + 11 + inner + 19 * s + 12) ≤
      p * p * ((a + 400) * v) := by
  have hvp : v ≤ p * v := Nat.le_mul_of_pos_left _ hp
  have hvpp : p * v ≤ p * p * v := by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left p hvp
  have hseed : 12 * n + 44 * s + 11 + 19 * s + 12 ≤ 98 * v := by omega
  have hins : 12 * n + 44 * s + 11 + inner + 19 * s + 12 ≤ p * ((a + 248) * v) := by
    nlinarith only [hseed, hinner, hvp]
  have hmul := (Nat.mul_le_mul_left t hins).trans (Nat.mul_le_mul_right (p * ((a + 248) * v)) ht)
  have hbase : 6 * s + 13 + 25 * s + 11 ≤ 55 * (p * p * v) := by
    have hsmall : 6 * s + 13 + 25 * s + 11 ≤ 55 * v := by omega
    exact hsmall.trans (Nat.mul_le_mul_left _ (hvp.trans hvpp))
  calc
    _ ≤ 55 * (p * p * v) + p * (p * ((a + 248) * v)) := Nat.add_le_add hbase hmul
    _ ≤ p * p * ((a + 400) * v) := by nlinarith

theorem compilerOuterTime_le (constant registers clauses budget special : ℕ)
    (hs : special ≤ min budget clauses + 1) :
    compilerOuterTime constant registers clauses budget special ≤
      3 ^ (min budget clauses + 1) * 3 ^ (min budget clauses + 1) *
        (((800 + registers) * (constant + 2) + 400) *
          (min budget clauses + 1) * (2 * clauses + 3) ^ 2) := by
  have hdv : min budget clauses + 1 ≤ (min budget clauses + 1) * (2 * clauses + 3) ^ 2 :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hnv : 2 * clauses + 1 ≤ (min budget clauses + 1) * (2 * clauses + 3) ^ 2 := by
    have hq : 2 * clauses + 1 ≤ (2 * clauses + 3) ^ 2 := by nlinarith
    exact hq.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hv : 1 ≤ (min budget clauses + 1) * (2 * clauses + 3) ^ 2 := by omega
  have hp : 1 ≤ 3 ^ (min budget clauses + 1) := Nat.one_le_pow _ _ (by decide)
  have ht := Nat.pow_le_pow_right (by decide : 1 ≤ 3) hs
  have hinner := compilerInnerTime_le constant registers clauses budget
  simpa only [compilerOuterTime, Nat.mul_assoc] using
    compilerOuterArithmetic ((800 + registers) * (constant + 2)) (min budget clauses + 1)
      ((min budget clauses + 1) * (2 * clauses + 3) ^ 2) (3 ^ (min budget clauses + 1))
      (compilerInnerTime constant registers clauses budget) (2 * clauses + 1) special (3 ^ special)
      hs hdv hnv hv hp ht (by simpa only [Nat.mul_assoc] using hinner)

theorem compilerPrefixTime_le (constant registers clauses budget special : ℕ)
    (hs : special ≤ min budget clauses + 1) :
    compilerPrefixTime constant registers clauses budget special ≤
      3 ^ (min budget clauses + 1) * 3 ^ (min budget clauses + 1) *
        (((800 + registers) * (constant + 2) + 1000) *
          (min budget clauses + 1) * (2 * clauses + 3) ^ 2) := by
  have hout := compilerOuterTime_le constant registers clauses budget special hs
  let d := min budget clauses + 1
  let q := 2 * clauses + 3
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hpow : 1 ≤ 3 ^ d * 3 ^ d := Nat.succ_le_of_lt (by positivity)
  have hqv : q ≤ d * q ^ 2 :=
    (show q ≤ q ^ 2 by nlinarith only [hq]).trans (Nat.le_mul_of_pos_left _ hd)
  have hqbig : q ≤ 3 ^ d * 3 ^ d * (d * q ^ 2) :=
    hqv.trans (Nat.le_mul_of_pos_left _ hpow)
  have hbase : 300 * (clauses + (2 * clauses + 1) + 1) ≤ 450 * q := by dsimp [q]; omega
  have hbase' := hbase.trans (Nat.mul_le_mul_left 450 hqbig)
  unfold compilerPrefixTime
  dsimp [d, q] at hbase'
  nlinarith only [hout, hbase']

theorem compilerTotalTime_le (constant registers clauses budget special : ℕ)
    (hs : special ≤ min budget clauses + 1) :
    clauses * compilerPrefixTime constant registers clauses budget special +
      compilerFinalTime constant clauses ≤
        compilerUniformConstant constant registers * 15 ^ budget * (budget + 1) *
          (2 * clauses + 3) ^ 3 := by
  let q := 2 * clauses + 3
  let a := (800 + registers) * (constant + 2)
  let d := min budget clauses + 1
  have hprefix := Nat.mul_le_mul_left clauses (compilerPrefixTime_le constant registers clauses budget special hs)
  have hwork : 3 ^ d * 3 ^ d * d ≤ 9 * 15 ^ budget * (budget + 1) := by
    have hd : d ≤ budget + 1 := by dsimp [d]; omega
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 3) hd
    exact (Nat.mul_le_mul (Nat.mul_le_mul hp hp) hd).trans (compressionPathWork_le budget)
  have hwork' := Nat.mul_le_mul_right ((a + 1000) * q ^ 2) hwork
  have hm : clauses ≤ q := by dsimp [q]; omega
  have hprefix' : clauses * compilerPrefixTime constant registers clauses budget special ≤
      9 * (a + 1000) * 15 ^ budget * (budget + 1) * q ^ 3 := by
    calc
      _ ≤ clauses * (3 ^ d * 3 ^ d * d * ((a + 1000) * q ^ 2)) := by
        simpa [d, a, q, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprefix
      _ ≤ clauses * (9 * 15 ^ budget * (budget + 1) * ((a + 1000) * q ^ 2)) :=
        Nat.mul_le_mul_left _ hwork'
      _ ≤ q * (9 * 15 ^ budget * (budget + 1) * ((a + 1000) * q ^ 2)) :=
        Nat.mul_le_mul_right _ hm
      _ = _ := by ring
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hqcube : q ^ 2 ≤ q ^ 3 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ hq
  have hmq : clauses + 1 ≤ q := by dsimp [q]; omega
  have hfinal : compilerFinalTime constant clauses ≤ 1000 * (constant + 2) * q ^ 3 := by
    have hsquare := Nat.pow_le_pow_left hmq 2
    have hqlinear : q ≤ q ^ 3 := (show q ≤ q ^ 2 by nlinarith only [hq]).trans hqcube
    have hconstant := Nat.mul_le_mul_left (5 * (constant + 1)) (show 1 ≤ q ^ 3 from Nat.one_le_pow _ _ hq)
    have hsquare' := Nat.mul_le_mul_left 320 (hsquare.trans hqcube)
    have hlinear := Nat.mul_le_mul_left 80 (hmq.trans hqlinear)
    have hfixed := Nat.mul_le_mul_left 400 (Nat.one_le_pow 3 q hq)
    unfold compilerFinalTime
    nlinarith only [hsquare', hlinear, hfixed, hconstant]
  have hgeometric : 1 ≤ 15 ^ budget * (budget + 1) := Nat.succ_le_of_lt (by positivity)
  have hfinal' : compilerFinalTime constant clauses ≤
      (1000 * (constant + 2) * q ^ 3) * (15 ^ budget * (budget + 1)) :=
    hfinal.trans (by simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (1000 * (constant + 2) * q ^ 3) hgeometric)
  have hcoefficient : 9 * (a + 1000) + 1000 * (constant + 2) ≤ 100 * a := by dsimp [a]; nlinarith
  have hsum := Nat.add_le_add hprefix' hfinal'
  have hcoef := Nat.mul_le_mul_right (15 ^ budget * (budget + 1) * q ^ 3) hcoefficient
  have htotal : clauses * compilerPrefixTime constant registers clauses budget special + compilerFinalTime constant clauses ≤
      100 * a * 15 ^ budget * (budget + 1) * q ^ 3 := by nlinarith only [hsum, hcoef]
  simpa only [compilerUniformConstant, a, q, Nat.mul_assoc] using htotal

theorem compilerTotalSpace_le (constant registers clauses budget : ℕ) :
    (compilerLayout constant clauses budget).space ≤
      compilerUniformConstant constant registers * 15 ^ budget * (budget + 1) *
        (2 * clauses + 3) ^ 3 := by
  have hl := compilerLayout_space_bound constant clauses budget
  have hp : (clauses + 1) ^ 2 ≤ (2 * clauses + 3) ^ 3 := by
    have hsq := Nat.pow_le_pow_left (by omega : clauses + 1 ≤ 2 * clauses + 3) 2
    have hcub : (2 * clauses + 3) ^ 2 ≤ (2 * clauses + 3) ^ 3 := by
      rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
    exact hsq.trans hcub
  have hc : 128 * (constant + 1) ≤ compilerUniformConstant constant registers := by
    unfold compilerUniformConstant; nlinarith
  have hgeom : 1 ≤ 15 ^ budget * (budget + 1) := Nat.succ_le_of_lt (by positivity)
  have hfirst := (Nat.mul_le_mul_right _ hc).trans (Nat.mul_le_mul_left _ hp)
  have hlast := Nat.mul_le_mul_left
    (compilerUniformConstant constant registers * (2 * clauses + 3) ^ 3) hgeom
  nlinarith only [hl, hfirst, hlast]

end STACS2027.Runtimes.BoundedCost
