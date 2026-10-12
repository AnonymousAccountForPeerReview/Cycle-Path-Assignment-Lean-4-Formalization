module

public import Outerplanar.RAM.Poly1Lib
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Phase P1 of the polygon solver: the stable counting sort

`csort` sorts the indices `0, …, L - 1` of a key array (`L` keys below `K`, at `rKB`) stably by
key: it stores `bucketIdx keys K` at a fresh `rKO` and the bucket starts `offOf keys` (`K + 1`
cells) at a fresh `rKF`, in `O(L + K)` steps (`csort_spec`). Three passes:

1. counting: `OFF[k + 1] := |bucket k|` (`cntS`);
2. prefix sums: `PTR[k] := OFF[k]`, `OFF[k + 1] += OFF[k]`, so `OFF[k] = offOf keys k`;
3. filling: for `i = 0, …, L - 1`, `ORD[PTR[key i]++] := i`; after `i` indices the bucket `k`
   holds `bkt keys i k` at `offOf keys k` (`arr_flatMap` concatenates the buckets).

Space: the sort accesses its keys and its three arrays only (`OFF`, `PTR`, `ORD`: `2K + 1 + L`
cells from the free address `F₀`). `csort_specB` is the triple within the bound
`S ≥ F₀ + (K + 1) + K + L` (`HTB S`); the growth triple `csort_spec` used by the polygon solver
is derived from it. The abstract side (`bkt`, `offOf`, `bucketIdx`) is in `SortSpec.lean`, which
depends on no polygon, so that the graph-level phases (`PairIds.lean`) can sort too.
-/

@[expose] public section

namespace STACS2027.RAM.P1

variable {S : ℕ}

/-! ### Registers and program -/

/-- Argument: base of the keys. -/
abbrev rKB : ℕ := 100
/-- Argument: the number of keys `L`. -/
abbrev rKL : ℕ := 101
/-- Argument: the number of buckets `K` (all keys are below `K`). -/
abbrev rKN : ℕ := 102
/-- Result: base of the sorted indices (`L` cells). -/
abbrev rKO : ℕ := 103
/-- Result: base of the bucket starts (`K + 1` cells). -/
abbrev rKF : ℕ := 104
/-- Base of the insertion pointers (`K` cells). -/
abbrev rKP : ℕ := 105
/-- Loop counter. -/
abbrev rKI : ℕ := 106
/-- Temporary. -/
abbrev rKX : ℕ := 107
/-- Temporary. -/
abbrev rKY : ℕ := 108
/-- Temporary. -/
abbrev rKZ : ℕ := 109

/-- Allocation of `OFF` (`K + 1` cells), `PTR` (`K`) and `ORD` (`L`). -/
def csInit : Stmt :=
  .seq (addc rKZ rKN 1) (.seq (alloc rKF rKZ) (.seq (alloc rKP rKN) (alloc rKO rKL)))
/-- Counting: `OFF[key i + 1] += 1`. -/
def csCount : Stmt :=
  .seq (ld rKX rKB rKI) (.seq (inc rKX) (.seq (ld rKY rKF rKX) (.seq (inc rKY) (st rKF rKX rKY))))
/-- Prefix sums: `PTR[k] := OFF[k]; OFF[k + 1] += OFF[k]`. -/
def csPrefix : Stmt :=
  .seq (ld rKX rKF rKI) (.seq (st rKP rKI rKX) (.seq (addc rKY rKI 1)
    (.seq (ld rKZ rKF rKY) (.seq (.add rKZ rKZ rKX) (st rKF rKY rKZ)))))
/-- Filling: `ORD[PTR[key i]] := i; PTR[key i] += 1`. -/
def csFill : Stmt :=
  .seq (ld rKX rKB rKI) (.seq (ld rKY rKP rKX) (.seq (st rKO rKY rKI)
    (.seq (inc rKY) (st rKP rKX rKY))))
/-- **The stable counting sort.** -/
def csort : Stmt :=
  .seq csInit (.seq (forUp rKI rKL csCount) (.seq (forUp rKI rKN csPrefix) (forUp rKI rKL csFill)))

/-! ### Specification -/

/-- The arguments of `csort`. -/
structure CsIn (keys : List ℕ) (K : ℕ) (c : Config) : Prop where
  kl : c.reg rKL = keys.length
  kn : c.reg rKN = K
  ak : ArrAt rKB keys c
  free : ZeroFrom c.mem (c.reg rFREE)

/-- The results of `csort`. -/
def CsOut (keys : List ℕ) (K : ℕ) (c : Config) : Prop :=
  ArrAt rKO (bucketIdx keys K) c ∧ TabAt rKF (K + 1) (offOf keys) c

/-! ### The state during the passes -/

/-- The registers fixed during the passes (layout: `OFF` at `F₀`, then `PTR`, then `ORD`). -/
@[mk_iff] structure CsGlob (keys : List ℕ) (K F₀ : ℕ) (c : Config) : Prop where
  kl : c.reg rKL = keys.length
  kn : c.reg rKN = K
  kf : c.reg rKF = F₀
  kp : c.reg rKP = F₀ + (K + 1)
  ko : c.reg rKO = F₀ + (K + 1) + K
  free : c.reg rFREE = F₀ + (K + 1) + K + keys.length
  bk : c.reg rKB + keys.length ≤ F₀

/-- The memory facts kept during the passes. -/
structure CsBase (keys : List ℕ) (K F₀ kb : ℕ) (m₀ m : ℕ → ℕ) : Prop where
  ak : Arr m kb keys
  same : SameOn (· < F₀) m₀ m
  zero : ZeroFrom m (F₀ + (K + 1) + K + keys.length)

theorem CsBase.upd {keys : List ℕ} {K F₀ kb : ℕ} {m₀ m : ℕ → ℕ} (h : CsBase keys K F₀ kb m₀ m)
    (hkb : kb + keys.length ≤ F₀) {a : ℕ} (v : ℕ) (ha : F₀ ≤ a)
    (ha' : a < F₀ + (K + 1) + K + keys.length) : CsBase keys K F₀ kb m₀ (RAM.upd m a v) :=
  ⟨h.ak.upd_of_disjoint (by omega), h.same.upd_of_ge ha v, h.zero.upd ha'⟩

/-- The key `i`. -/
theorem key_lt {keys : List ℕ} {K : ℕ} (hK : ∀ x ∈ keys, x < K) {i : ℕ} (hi : i < keys.length) :
    keys.getD i 0 < K := by
  rw [getD_of_lt hi]; exact hK _ (List.getElem_mem hi)

/-! ### Pass 1: counting -/

/-- The invariant of the counting pass after `i` keys. -/
def CntInv (keys : List ℕ) (K F₀ : ℕ) (m₀ : ℕ → ℕ) (i : ℕ) (c : Config) : Prop :=
  CsGlob keys K F₀ c ∧ CsBase keys K F₀ (c.reg rKB) m₀ c.mem ∧ Tab c.mem F₀ (K + 1) (cntS keys i)

theorem cntS_succ (keys : List ℕ) (i : ℕ) :
    Function.update (cntS keys i) (keys.getD i 0 + 1) ((bkt keys i (keys.getD i 0)).length + 1) =
      cntS keys (i + 1) := by
  funext x
  cases x with
  | zero => simp [cntS]
  | succ x =>
    by_cases hx : x = keys.getD i 0
    · subst hx; simp [cntS, length_bkt_succ]
    · rw [Function.update_of_ne (by omega)]
      have hx' : ¬ keys.getD i 0 = x := Ne.symm hx
      simp only [cntS, length_bkt_succ, hx', ↓reduceIte, Nat.add_zero]

theorem csCount_spec (keys : List ℕ) (K : ℕ) (hK : ∀ x ∈ keys, x < K) (F₀ : ℕ) (m₀ : ℕ → ℕ)
    (hS : F₀ + (K + 1) + K + keys.length ≤ S) (i : ℕ) (hi : i < keys.length) :
    HTB S csCount (fun c => CntInv keys K F₀ m₀ i c ∧ c.reg rKI = i ∧ c.reg rKL = keys.length)
      (fun c => CntInv keys K F₀ m₀ (i + 1) c ∧ c.reg rKI = i ∧ c.reg rKL = keys.length) 10 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  obtain ⟨⟨hG, hB, hT⟩, hi', hl⟩ := hc
  have hx : c.mem (c.reg rKB + i) = keys.getD i 0 := hB.ak.getD hi
  have hxK := key_lt hK hi
  have hy : c.mem (F₀ + (keys.getD i 0 + 1)) = (bkt keys i (keys.getD i 0)).length :=
    hT.get (by omega)
  have hG' : CsGlob keys K F₀ (RAM.run csCount c) :=
    (show RegIndep (wregs csCount) (CsGlob keys K F₀) by indep [csGlob_iff]).run (by decide) hG
  have hrr : ∀ r, r ∉ wregs csCount → (RAM.run csCount c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hmem : (RAM.run csCount c).mem =
      upd c.mem (F₀ + (keys.getD i 0 + 1)) ((bkt keys i (keys.getD i 0)).length + 1) := by
    simp +decide only [csCount, run_seq', run_ld, run_inc (show rKX ≠ rT by decide),
      run_inc (show rKY ≠ rT by decide), run_st (show rKY ≠ rT by decide), setReg_reg,
      ↓reduceIte, setReg_mem, setMem_mem_upd, hi', hx, hG.kf, hy]
  have hbk := hG.bk
  refine ⟨by addr_ok [csCount, hi', hx, hG.kf], ⟨hG', ?_, ?_⟩, ?_, ?_⟩
  · rw [hrr rKB (by decide), hmem]
    exact hB.upd hG.bk _ (by omega) (by have := hG.free; omega)
  · rw [hmem, ← cntS_succ]
    exact hT.upd rfl
  · rw [hrr rKI (by decide), hi']
  · rw [hrr rKL (by decide), hl]

/-! ### Pass 2: prefix sums -/

/-- The bucket starts after `k` steps of the prefix pass: final up to `k`, counts above. -/
def preF (keys : List ℕ) (k x : ℕ) : ℕ := if x ≤ k then offOf keys x else cntS keys keys.length x

/-- The invariant of the prefix pass after `k` steps. -/
def PreInv (keys : List ℕ) (K F₀ : ℕ) (m₀ : ℕ → ℕ) (k : ℕ) (c : Config) : Prop :=
  CsGlob keys K F₀ c ∧ CsBase keys K F₀ (c.reg rKB) m₀ c.mem ∧
    Tab c.mem F₀ (K + 1) (preF keys k) ∧ Tab c.mem (F₀ + (K + 1)) k (offOf keys)

theorem preF_succ (keys : List ℕ) (k : ℕ) :
    Function.update (preF keys k) (k + 1) ((bkt keys keys.length k).length + offOf keys k) =
      preF keys (k + 1) := by
  funext x
  by_cases hx : x = k + 1
  · subst hx; simp [preF, offOf_succ]; omega
  · rw [Function.update_of_ne hx]
    simp only [preF]
    by_cases h : x ≤ k
    · simp [h, show x ≤ k + 1 by omega]
    · simp [h, show ¬ x ≤ k + 1 by omega]

theorem csPrefix_spec (keys : List ℕ) (K F₀ : ℕ) (m₀ : ℕ → ℕ)
    (hS : F₀ + (K + 1) + K + keys.length ≤ S) (k : ℕ) (hk : k < K) :
    HTB S csPrefix (fun c => PreInv keys K F₀ m₀ k c ∧ c.reg rKI = k ∧ c.reg rKN = K)
      (fun c => PreInv keys K F₀ m₀ (k + 1) c ∧ c.reg rKI = k ∧ c.reg rKN = K) 11 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  obtain ⟨⟨hG, hB, hT, hP⟩, hk', hn⟩ := hc
  have hx : c.mem (F₀ + k) = offOf keys k := by
    rw [hT.get (by omega)]; simp [preF]
  have hy : c.mem (F₀ + (k + 1)) = (bkt keys keys.length k).length := by
    rw [hT.get (by omega)]; simp [preF, cntS]
  have hG' : CsGlob keys K F₀ (RAM.run csPrefix c) :=
    (show RegIndep (wregs csPrefix) (CsGlob keys K F₀) by indep [csGlob_iff]).run (by decide) hG
  have hrr : ∀ r, r ∉ wregs csPrefix → (RAM.run csPrefix c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hfree := hG.free
  have hne : F₀ + (k + 1) ≠ F₀ + (K + 1) + k := by omega
  have hmem : (RAM.run csPrefix c).mem =
      upd (upd c.mem (F₀ + (K + 1) + k) (offOf keys k)) (F₀ + (k + 1))
        ((bkt keys keys.length k).length + offOf keys k) := by
    simp +decide only [csPrefix, run_seq', run_ld, run_addc (show rKI ≠ rT by decide), run_add,
      run_st (show rKX ≠ rT by decide), run_st (show rKZ ≠ rT by decide), setReg_reg,
      ↓reduceIte, setReg_mem, setMem_reg, setMem_mem_upd, upd_apply, hne, hk', hx, hy, hG.kf,
      hG.kp]
  refine ⟨by addr_ok [csPrefix, hk', hG.kf, hG.kp], ⟨hG', ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hrr rKB (by decide), hmem]
    exact (hB.upd hG.bk _ (by omega) (by omega)).upd hG.bk _ (by omega) (by omega)
  · rw [hmem, ← preF_succ]
    exact (hT.upd_of_disjoint (by omega)).upd rfl
  · rw [hmem]
    exact ((hP.upd_of_disjoint (by omega)).snoc (by simp)).upd_of_disjoint (by omega)
  · rw [hrr rKI (by decide), hk']
  · rw [hrr rKN (by decide), hn]

/-! ### Pass 3: filling -/

/-- The invariant of the filling pass after `i` indices. -/
def FillInv (keys : List ℕ) (K F₀ : ℕ) (m₀ : ℕ → ℕ) (i : ℕ) (c : Config) : Prop :=
  CsGlob keys K F₀ c ∧ CsBase keys K F₀ (c.reg rKB) m₀ c.mem ∧
    Tab c.mem F₀ (K + 1) (offOf keys) ∧
    Tab c.mem (F₀ + (K + 1)) K (fun k => offOf keys k + (bkt keys i k).length) ∧
    ∀ k, k < K → Arr c.mem (F₀ + (K + 1) + K + offOf keys k) (bkt keys i k)

theorem csFill_spec (keys : List ℕ) (K : ℕ) (hK : ∀ x ∈ keys, x < K) (F₀ : ℕ) (m₀ : ℕ → ℕ)
    (hS : F₀ + (K + 1) + K + keys.length ≤ S) (i : ℕ) (hi : i < keys.length) :
    HTB S csFill (fun c => FillInv keys K F₀ m₀ i c ∧ c.reg rKI = i ∧ c.reg rKL = keys.length)
      (fun c => FillInv keys K F₀ m₀ (i + 1) c ∧ c.reg rKI = i ∧ c.reg rKL = keys.length) 10 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  obtain ⟨⟨hG, hB, hO, hP, hA⟩, hi', hl⟩ := hc
  set x := keys.getD i 0 with hxdef
  have hx : c.mem (c.reg rKB + i) = x := hB.ak.getD hi
  have hxK : x < K := key_lt hK hi
  have hy : c.mem (F₀ + (K + 1) + x) = offOf keys x + (bkt keys i x).length := hP.get hxK
  have hG' : CsGlob keys K F₀ (RAM.run csFill c) :=
    (show RegIndep (wregs csFill) (CsGlob keys K F₀) by indep [csGlob_iff]).run (by decide) hG
  have hrr : ∀ r, r ∉ wregs csFill → (RAM.run csFill c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hfree := hG.free
  -- the bucket of `x` is not full yet
  have hbx : (bkt keys i x).length + 1 ≤ (bkt keys keys.length x).length := by
    have := length_bkt_mono keys x (show i + 1 ≤ keys.length by omega)
    have hx' : keys.getD i 0 = x := hxdef.symm
    simpa only [length_bkt_succ, hx', ↓reduceIte] using this
  have hoff := offOf_mono keys (show x + 1 ≤ K by omega)
  rw [offOf_succ, offOf_eq_length keys K hK] at hoff
  have hmem : (RAM.run csFill c).mem =
      upd (upd c.mem (F₀ + (K + 1) + K + (offOf keys x + (bkt keys i x).length)) i)
        (F₀ + (K + 1) + x) (offOf keys x + (bkt keys i x).length + 1) := by
    simp +decide only [csFill, run_seq', run_ld, run_inc (show rKY ≠ rT by decide),
      run_st (show rKI ≠ rT by decide), run_st (show rKY ≠ rT by decide), setReg_reg,
      ↓reduceIte, setReg_mem, setMem_reg, setMem_mem_upd, hi', hx, hG.kp, hG.ko, hy]
  have hbk := hG.bk
  refine ⟨by addr_ok [csFill, hi', hx, hy, hG.kp, hG.ko], ⟨hG', ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    try rw [hmem]
  · rw [hrr rKB (by decide)]
    exact (hB.upd hG.bk _ (by omega) (by omega)).upd hG.bk _ (by omega) (by omega)
  · exact (hO.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)
  · have h := (hP.upd_of_disjoint (a := F₀ + (K + 1) + K + (offOf keys x + (bkt keys i x).length))
      (v := i) (by omega)).upd (i := x) (v := offOf keys x + (bkt keys i x).length + 1) rfl
    refine h.congr_fun fun k _ => ?_
    by_cases hkx : k = x
    · subst hkx; simp [length_bkt_succ, hxdef]; omega
    · have hk' : ¬ keys.getD i 0 = k := fun h => hkx (by rw [← h])
      rw [Function.update_of_ne hkx]
      simp only [length_bkt_succ, hk', ↓reduceIte, Nat.add_zero]
  · intro k hk
    have hAk := hA k hk
    by_cases hkx : k = x
    · subst hkx
      rw [bkt_succ]
      simp only [← hxdef, ↓reduceIte]
      exact (hAk.upd_snoc (by omega)).upd_of_disjoint (by simp; omega)
    · have hk' : ¬ keys.getD i 0 = k := fun h => hkx (by rw [← h])
      rw [bkt_succ]
      simp only [hk', ↓reduceIte, List.append_nil]
      have hdis : F₀ + (K + 1) + K + (offOf keys x + (bkt keys i x).length) <
            F₀ + (K + 1) + K + offOf keys k ∨
          F₀ + (K + 1) + K + offOf keys k + (bkt keys i k).length ≤
            F₀ + (K + 1) + K + (offOf keys x + (bkt keys i x).length) := by
        rcases lt_or_gt_of_ne hkx with hlt | hlt
        · right
          have := offOf_add_le keys (i := i) (by omega) hlt
          omega
        · left
          have := offOf_mono keys (show x + 1 ≤ k by omega)
          rw [offOf_succ] at this
          omega
      exact (hAk.upd_of_disjoint hdis).upd_of_disjoint (by omega)
  · rw [hrr rKI (by decide), hi']
  · rw [hrr rKL (by decide), hl]

/-! ### The sort -/

theorem csInit_spec (keys : List ℕ) (K F₀ : ℕ) (m₀ : ℕ → ℕ) :
    HTB S csInit (fun c => CsIn keys K c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => CntInv keys K F₀ m₀ 0 c ∧ c.reg rKL = keys.length) 11 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hc, hF, hm⟩ => ?_
  simp only [csInit, run_seq', run_addc (show rKN ≠ rT by decide),
    run_alloc (show rKZ ≠ rT by decide) (show rKF ≠ rKZ by decide),
    run_alloc (show rKN ≠ rT by decide) (show rKP ≠ rKN by decide),
    run_alloc (show rKL ≠ rT by decide) (show rKO ≠ rKL by decide)]
  have := hc.ak.2
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  all_goals simp +decide only [setReg_reg, ↓reduceIte, setReg_mem, hF, hc.kl, hc.kn]
  all_goals try omega
  · exact hc.ak.1
  · rw [hm]; exact SameOn.refl _ _
  · exact hc.free.mono (by omega)
  · have : cntS keys 0 = fun _ => 0 := by funext x; cases x <;> rfl
    rw [this]
    exact hc.free.tab (by omega) _

/-- The counting pass. -/
theorem csCountLoop_spec (keys : List ℕ) (K : ℕ) (hK : ∀ x ∈ keys, x < K) (F₀ : ℕ)
    (m₀ : ℕ → ℕ) (hS : F₀ + (K + 1) + K + keys.length ≤ S) :
    HTB S (forUp rKI rKL csCount) (fun c => CntInv keys K F₀ m₀ 0 c ∧ c.reg rKL = keys.length)
      (fun c => CntInv keys K F₀ m₀ keys.length c ∧ c.reg rKI = keys.length ∧
        c.reg rKL = keys.length) (keys.length * 14 + 3) :=
  HTB.forUpC (i := rKI) (n := rKL) (N := keys.length) (body := csCount) (CntInv keys K F₀ m₀) 10
    (by decide) (by decide) (by decide) (fun j => by indep [CntInv, csGlob_iff])
    (fun j hj => csCount_spec keys K hK F₀ m₀ hS j hj)

/-- The prefix pass. -/
theorem csPrefixLoop_spec (keys : List ℕ) (K F₀ : ℕ) (m₀ : ℕ → ℕ)
    (hS : F₀ + (K + 1) + K + keys.length ≤ S) :
    HTB S (forUp rKI rKN csPrefix) (fun c => PreInv keys K F₀ m₀ 0 c ∧ c.reg rKN = K)
      (fun c => PreInv keys K F₀ m₀ K c ∧ c.reg rKI = K ∧ c.reg rKN = K) (K * 15 + 3) :=
  HTB.forUpC (i := rKI) (n := rKN) (N := K) (body := csPrefix) (PreInv keys K F₀ m₀) 11
    (by decide) (by decide) (by decide) (fun j => by indep [PreInv, csGlob_iff])
    (fun j hj => csPrefix_spec keys K F₀ m₀ hS j hj)

/-- The filling pass. -/
theorem csFillLoop_spec (keys : List ℕ) (K : ℕ) (hK : ∀ x ∈ keys, x < K) (F₀ : ℕ)
    (m₀ : ℕ → ℕ) (hS : F₀ + (K + 1) + K + keys.length ≤ S) :
    HTB S (forUp rKI rKL csFill) (fun c => FillInv keys K F₀ m₀ 0 c ∧ c.reg rKL = keys.length)
      (fun c => FillInv keys K F₀ m₀ keys.length c ∧ c.reg rKI = keys.length ∧
        c.reg rKL = keys.length) (keys.length * 14 + 3) :=
  HTB.forUpC (i := rKI) (n := rKL) (N := keys.length) (body := csFill) (FillInv keys K F₀ m₀) 10
    (by decide) (by decide) (by decide) (fun j => by indep [FillInv, csGlob_iff])
    (fun j hj => csFill_spec keys K hK F₀ m₀ hS j hj)

/-- **The stable counting sort within the space bound `S`**: from the free address `F₀`, it
stores `bucketIdx keys K` at `rKO` and the bucket starts at `rKF`, in `O(L + K)` steps, accessing
only the keys and the `2K + 1 + L` cells above `F₀` (all below `S`), and ends with the free
address `F₀ + (K + 1) + K + L`. -/
theorem csort_specB (keys : List ℕ) (K : ℕ) (hK : ∀ x ∈ keys, x < K) (F₀ : ℕ) (m₀ : ℕ → ℕ)
    (hS : F₀ + (K + 1) + K + keys.length ≤ S) :
    HTB S csort (fun c => CsIn keys K c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => (CsOut keys K c ∧ ZeroFrom c.mem (c.reg rFREE)) ∧ SameOn (· < F₀) m₀ c.mem ∧
        c.reg rFREE = F₀ + (K + 1) + K + keys.length ∧ c.reg rKF = F₀ ∧
        c.reg rKO = F₀ + (K + 1) + K)
      (28 * keys.length + 15 * K + 20) := by
  have h₁ : HTB S csInit _ _ _ := csInit_spec keys K F₀ m₀
  have h₂ := (csCountLoop_spec keys K hK F₀ m₀ hS).post (Q' := fun c => PreInv keys K F₀ m₀ 0 c ∧
    c.reg rKN = K) fun c ⟨⟨hG, hB, hT⟩, _, _⟩ => by
      refine ⟨⟨hG, hB, hT.congr_fun fun x _ => ?_, tab_zero _ _ _⟩, hG.kn⟩
      cases x <;> simp [preF, cntS, offOf_zero]
  have h₃ := (csPrefixLoop_spec keys K F₀ m₀ hS).post (Q' := fun c => FillInv keys K F₀ m₀ 0 c ∧
    c.reg rKL = keys.length) fun c ⟨⟨hG, hB, hT, hP⟩, _, _⟩ => by
      refine ⟨⟨hG, hB, hT.congr_fun fun x hx => by simp [preF, show x ≤ K by omega], ?_, ?_⟩, hG.kl⟩
      · refine hP.congr_fun fun k _ => by simp [bkt_zero]
      · intro k _; simp [bkt_zero]
  refine (h₁.seq (h₂.seq (h₃.seq (csFillLoop_spec keys K hK F₀ m₀ hS)))).mono (fun _ h => h) ?_
    (by omega)
  rintro c ⟨⟨hG, hB, hO, -, hA⟩, -, -⟩
  have hlen := offOf_eq_length keys K hK
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩, hB.same, hG.free, hG.kf, hG.ko⟩
  · rw [hG.ko]
    exact arr_flatMap (bkt keys keys.length) K fun k hk => hA k hk
  · rw [hG.ko, hG.free, length_bucketIdx keys K hK]
  · rw [hG.kf]; exact hO
  · rw [hG.kf, hG.free]; omega
  · rw [hG.free]; exact hB.zero

/-- **The stable counting sort** (growth triple): `bucketIdx keys K` at `rKO`, the bucket starts
at `rKF`, in `O(L + K)` steps (from `csort_specB`). -/
theorem csort_spec (keys : List ℕ) (K : ℕ) (hK : ∀ x ∈ keys, x < K) :
    HG csort (wregs csort) (CsIn keys K) (fun c => CsOut keys K c ∧ ZeroFrom c.mem (c.reg rFREE))
      (28 * keys.length + 15 * K + 20) :=
  HG.ofGhost (by decide) (fun _ h => h) fun F₀ m₀ =>
    (csort_specB keys K hK F₀ m₀ (S := F₀ + (K + 1) + K + keys.length) le_rfl).toHT.post
      fun _ ⟨h, hs, hF, _⟩ => ⟨h, hs, by omega⟩

end STACS2027.RAM.P1
