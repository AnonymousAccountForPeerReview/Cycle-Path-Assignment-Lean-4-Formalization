module

public import Runtimes.Sort.MergeSpec
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# A stable bottom-up merge sort on the RAM: program and the merge of one block

**Interface** (registers `800–816`): input `oKB` (the base of the keys `KEY[0..L)`) and `oL`
(`L`, the number of indices); output `oSQ` (the base of the sorted indices). The two buffers
`A`, `B` (`L` cells each) are allocated at the free address `F`: `A = F`, `B = F + L` at first,
swapped after every pass.

```
msort  = A, B := alloc L, alloc L;  A[i] := i (i < L);  w := 1;  w2 := 2
         while w < L:  lo := 0
                       while lo < L:  mid := min(lo + w, L); hi := min(lo + 2w, L)
                                      i := lo; j := mid
                                      for k = lo .. hi − 1: mBody     -- the merge of block lo
                                      lo := lo + 2w
                       swap A B;  w := 2w;  w2 := 2w
         SQ := A
mBody  = if i < mid then x := A[i]; kx := KEY[x]
                         if j < hi then y := A[j]; ky := KEY[y]
                                        if ky < kx then B[k] := y; j++ else B[k] := x; i++
                         else B[k] := x; i++
         else y := A[j]; B[k] := y; j++
```
Keys are only compared (`ifLt`, truncated subtraction); no memory is indexed by a key. This
file: registers, the program, the memory of a pass (`PMem`), the run of `mBody` (`run_mBody`,
`mBody_addrOK`) and the merge of one block (`mergeLoop_spec`, the abstract `MState` of
`MergeSpec.lean`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Sort

open STACS2027.RAM STACS2027.RAM.PairIds
open scoped List

/-! ### Registers -/

/-- Input: the base of the keys. -/
abbrev oKB : ℕ := 800
/-- Input: the number `L` of indices. -/
abbrev oL : ℕ := 801
/-- Output: the base of the sorted indices. -/
abbrev oSQ : ℕ := 802
/-- The source buffer `A`. -/
abbrev oA : ℕ := 803
/-- The destination buffer `B`. -/
abbrev oB : ℕ := 804
/-- The width `w` of the runs. -/
abbrev oW : ℕ := 805
/-- `2w`. -/
abbrev oW2 : ℕ := 806
/-- The start `lo` of the current block. -/
abbrev oLo : ℕ := 807
/-- `mid = min(lo + w, L)`. -/
abbrev oMid : ℕ := 808
/-- `hi = min(lo + 2w, L)`. -/
abbrev oHi : ℕ := 809
/-- The position `i` in the left run. -/
abbrev oI : ℕ := 810
/-- The position `j` in the right run. -/
abbrev oJ : ℕ := 811
/-- The output position `k`. -/
abbrev oK : ℕ := 812
/-- The left entry `x`. -/
abbrev oX : ℕ := 813
/-- The right entry `y`. -/
abbrev oY : ℕ := 814
/-- The key of `x`. -/
abbrev oKX : ℕ := 815
/-- The key of `y`. -/
abbrev oKY : ℕ := 816

/-! ### The program -/

/-- `B[k] := x; i++`. -/
def takeX : Stmt := .seq (st oB oK oX) (inc oI)
/-- `B[k] := y; j++`. -/
def takeY : Stmt := .seq (st oB oK oY) (inc oJ)
/-- Both runs non-empty: compare the keys. -/
def mBoth : Stmt := .seq (ld oY oA oJ) (.seq (ld oKY oKB oY) (ifLt oKY oKX takeY takeX))
/-- The left run non-empty. -/
def mLeft : Stmt := .seq (ld oX oA oI) (.seq (ld oKX oKB oX) (ifLt oJ oHi mBoth takeX))
/-- The left run exhausted. -/
def mRight : Stmt := .seq (ld oY oA oJ) takeY
/-- **One step of the merge**: the next entry of the block. -/
def mBody : Stmt := ifLt oI oMid mLeft mRight

/-- The bounds of the block at `lo`, and the start positions. -/
def bSetup : Stmt :=
  .seq (.add oMid oLo oW) (.seq (ifLt oL oMid (mov oMid oL) .skip) (.seq (.add oHi oMid oW)
    (.seq (ifLt oL oHi (mov oHi oL) .skip) (.seq (mov oI oLo) (mov oJ oMid)))))
/-- **The merge of one block**, then the next block. -/
def blkBody : Stmt := .seq bSetup (.seq (forRange oK oLo oHi mBody) (.add oLo oLo oW2))
/-- The test of the block loop: `lo < L`. -/
def blkCond : Stmt := .sub rT oL oLo
/-- **One pass**: every block, then swap the buffers and double the width. -/
def passBody : Stmt :=
  .seq (.const oLo 0) (.seq (whileC blkCond blkBody) (.seq (swap oA oB)
    (.seq (.add oW oW oW) (.add oW2 oW oW))))
/-- The test of the pass loop: `w < L`. -/
def passCond : Stmt := .sub rT oL oW
/-- `A[i] := i`. -/
def initBody : Stmt := st oA oK oK
/-- The buffers, and `A = 0, 1, …, L − 1`. -/
def sInit : Stmt := .seq (alloc oA oL) (.seq (alloc oB oL) (forUp oK oL initBody))
/-- **The merge sort.** -/
def msort : Stmt :=
  .seq sInit (.seq (.const oW 1) (.seq (.add oW2 oW oW) (.seq (whileC passCond passBody)
    (mov oSQ oA))))

/-! ### The memory of a pass -/

/-- The buffers: `A` and `B` are `[F, F + L)` and `[F + L, F + 2L)` in some order, the keys lie
below `F`. -/
def Lay (L KB F A B : ℕ) : Prop := KB + L ≤ F ∧ ((A = F ∧ B = F + L) ∨ (A = F + L ∧ B = F))

/-- The memory during a pass: the keys at `KB`, the source array `a` at `A`, the output so far
`o` at `B`, and outside the buffers the memory `m₀` of the start. -/
structure PMem (keys a : List ℕ) (KB F A B : ℕ) (m₀ : ℕ → ℕ) (o : List ℕ) (m : ℕ → ℕ) : Prop where
  ky : Arr m KB keys
  src : Arr m A a
  dst : Arr m B o
  out : ∀ x, x < F ∨ F + 2 * keys.length ≤ x → m x = m₀ x

/-- Appending to the output. -/
theorem PMem.push {keys a o : List ℕ} {KB F A B : ℕ} {m₀ m : ℕ → ℕ}
    (h : PMem keys a KB F A B m₀ o m) (hl : Lay keys.length KB F A B) (ha : a.length = keys.length)
    (ho : o.length < keys.length) (v : ℕ) :
    PMem keys a KB F A B m₀ (o ++ [v]) (upd m (B + o.length) v) := by
  obtain ⟨hk, hAB⟩ := hl
  refine ⟨h.ky.upd_of_disjoint (by omega), h.src.upd_of_disjoint (by omega),
    h.dst.upd_snoc rfl, fun x hx => ?_⟩
  have hne : x ≠ B + o.length := by omega
  simp only [upd_apply, hne, ↓reduceIte]; exact h.out x hx

/-- The registers fixed during a pass. -/
@[mk_iff] structure PG (L KB F A B w : ℕ) (c : Config) : Prop where
  rkb : c.reg oKB = KB
  rl : c.reg oL = L
  ra : c.reg oA = A
  rb : c.reg oB = B
  rw : c.reg oW = w
  rw2 : c.reg oW2 = 2 * w
  rfree : c.reg rFREE = F + 2 * L

/-! ### The run of one merge step -/

/-- **The effect of `mBody`**: the next entry is `x = A[i]` if the left run is not exhausted
and (the right run is exhausted or `KEY[x] ≤ KEY[y]`, `y = A[j]`), and `y` otherwise; it is
stored at `B[k]` and its position advances. -/
theorem run_mBody (c : Config) :
    (run mBody c).mem = upd c.mem (c.reg oB + c.reg oK)
        (if c.reg oI < c.reg oMid ∧ (c.reg oJ < c.reg oHi →
            c.mem (c.reg oKB + c.mem (c.reg oA + c.reg oI)) ≤
              c.mem (c.reg oKB + c.mem (c.reg oA + c.reg oJ)))
          then c.mem (c.reg oA + c.reg oI) else c.mem (c.reg oA + c.reg oJ)) ∧
      (run mBody c).reg oI = (if c.reg oI < c.reg oMid ∧ (c.reg oJ < c.reg oHi →
            c.mem (c.reg oKB + c.mem (c.reg oA + c.reg oI)) ≤
              c.mem (c.reg oKB + c.mem (c.reg oA + c.reg oJ)))
          then c.reg oI + 1 else c.reg oI) ∧
      (run mBody c).reg oJ = (if c.reg oI < c.reg oMid ∧ (c.reg oJ < c.reg oHi →
            c.mem (c.reg oKB + c.mem (c.reg oA + c.reg oI)) ≤
              c.mem (c.reg oKB + c.mem (c.reg oA + c.reg oJ)))
          then c.reg oJ else c.reg oJ + 1) ∧
      (run mBody c).out = c.out := by
  have hout : (run mBody c).out = c.out := run_out_of_writes (by decide) rfl c
  refine ⟨?_, ?_, ?_, hout⟩ <;>
  · simp +decide only [mBody, mLeft, mRight, mBoth, takeX, takeY, run_ifLt, run_seq', run_ld,
      run_st (show oX ≠ rT by decide), run_st (show oY ≠ rT by decide),
      run_inc (show oI ≠ rT by decide), run_inc (show oJ ≠ rT by decide), setReg_reg, setReg_mem,
      setMem_reg, ↓reduceIte]
    split_ifs <;> simp_all
    all_goals exfalso; omega

/-- **The addresses of `mBody`**: the buffers and the keys below `S`, the entries read below
`L`, and the right run non-empty when the left one is exhausted. -/
theorem mBody_addrOK {S L : ℕ} {c : Config} (hA : c.reg oA + L ≤ S) (hB : c.reg oB + L ≤ S)
    (hK : c.reg oKB + L ≤ S) (hk : c.reg oK < L) (hmid : c.reg oMid ≤ L) (hhi : c.reg oHi ≤ L)
    (hx : c.reg oI < c.reg oMid → c.mem (c.reg oA + c.reg oI) < L)
    (hy : c.reg oJ < c.reg oHi → c.mem (c.reg oA + c.reg oJ) < L)
    (hj : ¬ c.reg oI < c.reg oMid → c.reg oJ < c.reg oHi) : AddrOK S mBody c := by
  addr_ok [mBody, mLeft, mRight, mBoth, takeX, takeY]

/-! ### The merge of one block -/

theorem bk_getD {w : ℕ} {a : List ℕ} {b p : ℕ} (hp : p < (bk w a b).length) :
    (bk w a b).getD p 0 = a.getD (w * b + p) 0 := by
  have hp' := hp
  rw [bk, length_sl] at hp'
  rw [getD_eq_getElem' hp, getD_eq_getElem' (by omega)]
  exact getElem_sl hp

theorem take_succ_getD (l : List ℕ) {n : ℕ} (hn : n < l.length) :
    l.take (n + 1) = l.take n ++ [l.getD n 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn, getD_eq_getElem' hn]; rfl

variable {S : ℕ}

section block

variable (keys a : List ℕ) (KB F A B w : ℕ) (m₀ : ℕ → ℕ)

/-- **The merge of block `b`** (`lo = 2wb`) before the output position `k`: `p` entries of the
left run and `q` of the right run are out (`MState`), stored after the merges of the blocks
before `b`. -/
def MInv (b k : ℕ) (c : Config) : Prop :=
  PG keys.length KB F A B w c ∧ c.reg oLo = 2 * w * b ∧
    c.reg oMid = min (2 * w * b + w) keys.length ∧
    ∃ p q, 2 * w * b + (p + q) = k ∧
      MState (keys := keys) (bk w a (2 * b)) (bk w a (2 * b + 1)) p q ∧
      c.reg oI = 2 * w * b + p ∧ c.reg oJ = min (2 * w * b + w) keys.length + q ∧
      PMem keys a KB F A B m₀
        ((List.range b).flatMap (blk keys w a) ++ (blk keys w a b).take (p + q)) c.mem

variable {keys a KB F A B w m₀}

theorem MInv.indep (b k : ℕ) : Indep [oK, rT] (MInv keys a KB F A B w m₀ b k) := by
  indep [MInv, pG_iff]

/-- **One step of the merge.** -/
theorem mBody_spec (hl : Lay keys.length KB F A B) (hS : F + 2 * keys.length ≤ S)
    (hG : Good keys w a) (b k : ℕ) (hk : k < min (2 * w * b + 2 * w) keys.length) :
    HTB S mBody (fun c => MInv keys a KB F A B w m₀ b k c ∧ c.reg oK = k ∧
        c.reg oHi = min (2 * w * b + 2 * w) keys.length)
      (fun c => MInv keys a KB F A B w m₀ b (k + 1) c ∧ c.reg oK = k ∧
        c.reg oHi = min (2 * w * b + 2 * w) keys.length) 32 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  obtain ⟨⟨hP, hlo, hmid, p, q, hpq, hM, hi, hj, hm⟩, hk', hhi⟩ := hc
  set L := keys.length with hL
  set lo := 2 * w * b with hlo'
  set xs := bk w a (2 * b) with hxs
  set ys := bk w a (2 * b + 1) with hys
  have hblk : blk keys w a b = mergeK keys xs ys := rfl
  have e1 : w * (2 * b) = lo := by rw [hlo']; ring
  have e2 : w * (2 * b + 1) = lo + w := by rw [hlo']; ring
  have hxl : xs.length = min (lo + w) L - lo := by rw [hxs, hG.length_bk, e1]
  have hyl : ys.length = min (lo + 2 * w) L - min (lo + w) L := by
    rw [hys, hG.length_bk, e2]; omega
  have hxg : ∀ p, p < xs.length → xs.getD p 0 = a.getD (lo + p) 0 := fun p hp => by
    have := bk_getD (w := w) (a := a) (b := 2 * b) (p := p) hp; rwa [e1] at this
  have hyg : ∀ q, q < ys.length → ys.getD q 0 = a.getD (lo + w + q) 0 := fun q hq => by
    have := bk_getD (w := w) (a := a) (b := 2 * b + 1) (p := q) hq; rwa [e2] at this
  have hxm : ∀ x ∈ xs, x < L := fun x hx => by have := hG.mem_bk hx; omega
  have hym : ∀ y ∈ ys, y < L := fun y hy => by have := hG.mem_bk hy; omega
  clear_value xs ys
  obtain ⟨hpx, hqy, hMe⟩ := hM
  have hlay := hl
  obtain ⟨hKF, hAB⟩ := hl
  have hA : A + L ≤ S := by omega
  have hB : B + L ≤ S := by omega
  have hKS : KB + L ≤ S := by omega
  clear hAB hKF
  have ha := hG.len
  -- the entries read
  have hxv : ∀ hp : p < xs.length, c.mem (A + (lo + p)) = xs[p] ∧ xs[p] < L := by
    intro hp
    have h1 : c.mem (A + (lo + p)) = a.getD (lo + p) 0 := hm.src.getD (by omega)
    refine ⟨by rw [h1, ← hxg p hp, getD_eq_getElem' hp], hxm _ (List.getElem_mem hp)⟩
  have hyv : ∀ hq : q < ys.length, c.mem (A + (min (lo + w) L + q)) = ys[q] ∧ ys[q] < L := by
    intro hq
    have hmid' : min (lo + w) L = lo + w := by omega
    have h1 : c.mem (A + (lo + w + q)) = a.getD (lo + w + q) 0 := hm.src.getD (by omega)
    refine ⟨by rw [hmid', h1, ← hyg q hq, getD_eq_getElem' hq], hym _ (List.getElem_mem hq)⟩
  have hbl : (blk keys w a b).length = xs.length + ys.length := by rw [hblk, length_mergeK]
  have hpre : ((List.range b).flatMap (blk keys w a)).length = lo := by
    rw [hG.length_passPre]; omega
  have hlen : ((List.range b).flatMap (blk keys w a) ++ (blk keys w a b).take (p + q)).length =
      k := by
    rw [List.length_append, hpre, List.length_take, hbl]; omega
  -- the registers kept
  have hreg : ∀ r, r ∉ [rT, oI, oJ, oX, oY, oKX, oKY] → (run mBody c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) (fun h => hr (by
      have : ∀ x ∈ wregs mBody, x ∈ [rT, oI, oJ, oX, oY, oKX, oKY] := by decide
      exact this r h)) c
  have hP' : PG L KB F A B w (run mBody c) :=
    (show RegIndep [rT, oI, oJ, oX, oY, oKX, oKY] (PG L KB F A B w) by indep [pG_iff]).run_of_sub
      (by decide) (by decide) hP
  -- the common end of the two outcomes
  have tail : ∀ (p' q' v : ℕ), p' + q' = p + q + 1 →
      MState (keys := keys) xs ys p' q' → (blk keys w a b).getD (p + q) 0 = v →
      (run mBody c).mem = upd c.mem (B + k) v → (run mBody c).reg oI = lo + p' →
      (run mBody c).reg oJ = min (lo + w) L + q' →
      MInv keys a KB F A B w m₀ b (k + 1) (run mBody c) ∧ (run mBody c).reg oK = k ∧
        (run mBody c).reg oHi = min (lo + 2 * w) L := by
    intro p' q' v hs hM' hv hmem' hI' hJ'
    refine ⟨⟨hP', by rw [hreg oLo (by decide), hlo], by rw [hreg oMid (by decide), hmid], p', q',
      by omega, by rw [← hxs, ← hys]; exact hM', hI', hJ', ?_⟩, by rw [hreg oK (by decide), hk'],
      by rw [hreg oHi (by decide), hhi]⟩
    rw [hs, take_succ_getD _ (by omega), hv, ← List.append_assoc, hmem', ← hlen]
    exact hm.push hlay ha (by rw [hlen]; omega) v
  obtain ⟨hmem, hI', hJ', -⟩ := run_mBody c
  simp only [hP.ra, hP.rb, hP.rkb, hi, hj, hk', hmid, hhi] at hmem hI' hJ'
  refine ⟨mBody_addrOK (L := L) (by rw [hP.ra]; exact hA) (by rw [hP.rb]; exact hB)
    (by rw [hP.rkb]; exact hKS) (by omega) (by omega) (by omega) (fun h => ?_) (fun h => ?_)
    (fun h => by omega), ?_⟩
  · rw [hP.ra, hi]
    have hp : p < xs.length := by omega
    rw [(hxv hp).1]; exact (hxv hp).2
  · rw [hP.ra, hj]
    have hq : q < ys.length := by omega
    rw [(hyv hq).1]; exact (hyv hq).2
  -- the outcome
  generalize run mBody c = c' at hmem hI' hJ' tail ⊢
  split_ifs at hmem hI' hJ' with hc
  · have hp : p < xs.length := by have h1 := hc.1; clear * - h1 hxl; omega
    have hle : ∀ hq : q < ys.length, keys.getD xs[p] 0 ≤ keys.getD ys[q] 0 := fun hq => by
      have := hc.2 (by omega)
      rwa [(hxv hp).1, (hyv hq).1, hm.ky.getD (hxv hp).2, hm.ky.getD (hyv hq).2] at this
    obtain ⟨hv, hM'⟩ := MState.left ⟨hpx, hqy, hMe⟩ hp hle
    rw [(hxv hp).1] at hmem
    exact tail (p + 1) q _ (by omega) hM' (by rw [hblk, hv]) hmem (by rw [hI']; omega) hJ'
  · have hq : q < ys.length ∧ ∀ hp : p < xs.length, keys.getD ys[q] 0 < keys.getD xs[p] 0 := by
      by_cases hp : p < xs.length
      · have h1 : ¬ (min (lo + w) L + q < min (lo + 2 * w) L →
            c.mem (KB + c.mem (A + (lo + p))) ≤ c.mem (KB + c.mem (A + (min (lo + w) L + q)))) :=
          fun h => hc ⟨by omega, h⟩
        have hq : q < ys.length := by
          by_contra hq; exact h1 fun h => absurd h (by omega)
        refine ⟨hq, fun _ => ?_⟩
        have h2 : ¬ (c.mem (KB + c.mem (A + (lo + p))) ≤
            c.mem (KB + c.mem (A + (min (lo + w) L + q)))) := fun h => h1 fun _ => h
        rw [(hxv hp).1, (hyv hq).1, hm.ky.getD (hxv hp).2, hm.ky.getD (hyv hq).2] at h2
        omega
      · have hq : q < ys.length := by clear * - hpq hk hp hxl hyl hpx; omega
        exact ⟨hq, fun h => absurd h hp⟩
    obtain ⟨hv, hM'⟩ := MState.right ⟨hpx, hqy, hMe⟩ hq.1 hq.2
    rw [(hyv hq.1).1] at hmem
    exact tail p (q + 1) _ (by omega) hM' (by rw [hblk, hv]) hmem hI' (by rw [hJ']; omega)

/-- **The merge of block `b`**: `k` from `lo = 2wb` to `hi = min(lo + 2w, L)`, after which the
merges of the blocks `0, …, b` are stored at `B`. -/
theorem mergeLoop_spec (hl : Lay keys.length KB F A B) (hS : F + 2 * keys.length ≤ S)
    (hG : Good keys w a) (b : ℕ) (hb : 2 * w * b ≤ min (2 * w * b + 2 * w) keys.length) :
    HTB S (forRange oK oLo oHi mBody)
      (fun c => MInv keys a KB F A B w m₀ b (2 * w * b) c ∧ c.reg oLo = 2 * w * b ∧
        c.reg oHi = min (2 * w * b + 2 * w) keys.length ∧
        2 * w * b ≤ min (2 * w * b + 2 * w) keys.length)
      (fun c => PG keys.length KB F A B w c ∧ c.reg oLo = 2 * w * b ∧
        PMem keys a KB F A B m₀ ((List.range (b + 1)).flatMap (blk keys w a)) c.mem)
      ((min (2 * w * b + 2 * w) keys.length - 2 * w * b) * 36 + 4) := by
  have h := HTB.forRange (S := S) (i := oK) (a := oLo) (n := oHi) (A := 2 * w * b)
    (N := min (2 * w * b + 2 * w) keys.length) (body := mBody)
    (MInv keys a KB F A B w m₀ b) (fun _ => 32) (by decide) (by decide) (by decide) (by decide)
    (fun j => MInv.indep b j) (fun j _ hj => mBody_spec hl hS hG b j hj)
  refine h.mono (fun c h => h) (fun c hc => ?_) (by simp [Finset.sum_const, Nat.card_Ico])
  obtain ⟨⟨hP, hlo, _, p, q, hpq, ⟨hpx, hqy, _⟩, _, _, hm⟩, _, _⟩ := hc
  refine ⟨hP, hlo, ?_⟩
  have e1 : w * (2 * b) = 2 * w * b := by ring
  have e2 : w * (2 * b + 1) = 2 * w * b + w := by ring
  have hx := hG.length_bk (2 * b)
  have hy := hG.length_bk (2 * b + 1)
  rw [e1] at hx
  rw [e2] at hy
  have hfull : (blk keys w a b).take (p + q) = blk keys w a b := by
    rw [List.take_of_length_le]
    rw [blk, length_mergeK]
    omega
  rw [hfull] at hm
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  exact hm

end block

end STACS2027.Runtimes.Sort
