module

public import Runtimes.Sort.MergeProg
import Mathlib.Tactic

/-!
# A stable bottom-up merge sort on the RAM: the passes and the specification

**`msort_spec`**: given `L` keys `keys` (arbitrary naturals) at `reg oKB` below the free address
`F` (`SortIn`), `msort` stores the indices `0, …, L − 1` sorted stably by key — the list
`sortKey keys`, i.e. `List.mergeSort` on `(key, index)`, sorted by `(key, index)`
(`pairwise_sortKey`) — at `reg oSQ ∈ [F, F + L]`, within
`CM · (L · (⌈log₂ L⌉ + 1) + 1)` steps, accessing only the addresses below any `S ≥ F + 2L`
(the keys and the two buffers), leaving the memory outside `[F, F + 2L)` unchanged, without
output. Keys are only compared (truncated subtraction): no memory is indexed by a key.

The block loop of a pass (`blkLoop_spec`, potential `57 (L − lo)`: every block holds at least
one entry) costs `57 L + 2`; the pass loop (`HTB.whileG`, ghost: the number `p` of passes,
`w = 2^p`) runs `⌈log₂ L⌉` passes (`Nat.lt_clog_iff_pow_lt`), and the array after `p` passes is
`sortP keys p` (`good_sortP`), the stable sort when `2^p ≥ L` (`Good.eq_sortKey`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Sort

open STACS2027.RAM STACS2027.RAM.PairIds
open scoped List

variable {S : ℕ}

/-! ### The block loop of a pass -/

section blocks

variable (keys a : List ℕ) (KB F A B w : ℕ) (m₀ : ℕ → ℕ)

/-- The block loop before block `b` (after the test). -/
def BInv (b : ℕ) (c : Config) : Prop :=
  PG keys.length KB F A B w c ∧ c.reg oLo = 2 * w * b ∧ c.reg rT = keys.length - 2 * w * b ∧
    PMem keys a KB F A B m₀ ((List.range b).flatMap (blk keys w a)) c.mem

variable {keys a KB F A B w m₀}

theorem run_bSetup (c : Config) :
    (run bSetup c).reg oMid = min (c.reg oLo + c.reg oW) (c.reg oL) ∧
      (run bSetup c).reg oHi = min (min (c.reg oLo + c.reg oW) (c.reg oL) + c.reg oW) (c.reg oL) ∧
      (run bSetup c).reg oI = c.reg oLo ∧
      (run bSetup c).reg oJ = min (c.reg oLo + c.reg oW) (c.reg oL) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp +decide only [bSetup, run_seq', run_add, run_ifLt, run_mov (show oL ≠ rT by decide),
      run_mov (show oLo ≠ rT by decide), run_mov (show oMid ≠ rT by decide), run_skip, setReg_reg,
      ↓reduceIte, config_ite_reg]
    split_ifs <;> omega

/-- The bounds of block `b`. -/
theorem bSetup_spec (b : ℕ) :
    HTB S bSetup (fun c => BInv keys a KB F A B w m₀ b c ∧ c.reg rT ≠ 0)
      (fun c => MInv keys a KB F A B w m₀ b (2 * w * b) c ∧ c.reg oLo = 2 * w * b ∧
        c.reg oHi = min (2 * w * b + 2 * w) keys.length ∧
        2 * w * b ≤ min (2 * w * b + 2 * w) keys.length) 16 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hP, hlo, hT, hm⟩, h0⟩ => ?_
  have hlt : 2 * w * b < keys.length := by omega
  have hreg : ∀ r, r ∉ [rT, oMid, oHi, oI, oJ] → (run bSetup c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) (fun h => hr (by
      have : ∀ x ∈ wregs bSetup, x ∈ [rT, oMid, oHi, oI, oJ] := by decide
      exact this r h)) c
  have hmem : (run bSetup c).mem = c.mem := run_mem_of_stores (by decide) rfl c
  obtain ⟨hmid, hhi, hi, hj⟩ := run_bSetup c
  simp only [hlo, hP.rw, hP.rl] at hmid hhi hi hj
  rw [show min (min (2 * w * b + w) keys.length + w) keys.length =
    min (2 * w * b + 2 * w) keys.length by omega] at hhi
  have hP' : PG keys.length KB F A B w (run bSetup c) :=
    (show RegIndep [rT, oMid, oHi, oI, oJ] (PG keys.length KB F A B w) by indep [pG_iff]).run_of_sub
      (by decide) (by decide) hP
  refine ⟨⟨hP', by rw [hreg oLo (by decide), hlo], hmid, 0, 0, by omega, mState_zero _ _,
    by rw [hi]; rfl, by rw [hj]; rfl, ?_⟩, by rw [hreg oLo (by decide), hlo], hhi, by omega⟩
  rw [hmem, Nat.add_zero, List.take_zero, List.append_nil]
  exact hm

/-- One block, then the test of the next. -/
theorem blkStep_spec (hl : Lay keys.length KB F A B) (hS : F + 2 * keys.length ≤ S)
    (hG : Good keys w a) (b : ℕ) :
    HTB S (.seq blkBody blkCond) (fun c => BInv keys a KB F A B w m₀ b c ∧ c.reg rT ≠ 0)
      (BInv keys a KB F A B w m₀ (b + 1))
      (16 + (((min (2 * w * b + 2 * w) keys.length - 2 * w * b) * 36 + 4) + 1) + 1) := by
  refine HTB.pre_fact (p := 2 * w * b < keys.length) (fun c ⟨⟨_, _, hT, _⟩, h0⟩ => by omega)
    fun hlt => ?_
  have h3 : HTB S (.add oLo oLo oW2)
      (fun c => PG keys.length KB F A B w c ∧ c.reg oLo = 2 * w * b ∧
        PMem keys a KB F A B m₀ ((List.range (b + 1)).flatMap (blk keys w a)) c.mem)
      (fun c => PG keys.length KB F A B w c ∧ c.reg oLo = 2 * w * (b + 1) ∧
        PMem keys a KB F A B m₀ ((List.range (b + 1)).flatMap (blk keys w a)) c.mem) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hP, hlo, hm⟩ =>
      ⟨(show RegIndep [oLo] (PG keys.length KB F A B w) by indep [pG_iff]).setReg (by decide) _ hP,
        by simp +decide [hlo, hP.rw2]; ring, hm⟩
  have h4 : HTB S blkCond
      (fun c => PG keys.length KB F A B w c ∧ c.reg oLo = 2 * w * (b + 1) ∧
        PMem keys a KB F A B m₀ ((List.range (b + 1)).flatMap (blk keys w a)) c.mem)
      (BInv keys a KB F A B w m₀ (b + 1)) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hP, hlo, hm⟩ =>
      ⟨(show RegIndep [rT] (PG keys.length KB F A B w) by indep [pG_iff]).setReg (by decide) _ hP,
        by simp +decide [blkCond, hlo], by simp +decide [blkCond, hlo, hP.rl], hm⟩
  exact ((bSetup_spec b).seq ((mergeLoop_spec hl hS hG b (by omega)).seq h3)).seq h4

/-- **The block loop of a pass**: after it, the pass `pass keys w a` is stored at `B`. -/
theorem blkLoop_spec (hl : Lay keys.length KB F A B) (hS : F + 2 * keys.length ≤ S)
    (hG : Good keys w a) (hw : 0 < w) :
    HTB S (whileC blkCond blkBody)
      (fun c => PG keys.length KB F A B w c ∧ c.reg oLo = 0 ∧
        PMem keys a KB F A B m₀ [] c.mem)
      (fun c => PG keys.length KB F A B w c ∧ PMem keys a KB F A B m₀ (pass keys w a) c.mem)
      (1 + (60 * keys.length + 1)) := by
  have hinit : HTB S blkCond
      (fun c => PG keys.length KB F A B w c ∧ c.reg oLo = 0 ∧ PMem keys a KB F A B m₀ [] c.mem)
      (BInv keys a KB F A B w m₀ 0) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hP, hlo, hm⟩ =>
      ⟨(show RegIndep [rT] (PG keys.length KB F A B w) by indep [pG_iff]).setReg (by decide) _ hP,
        by simp +decide [blkCond, hlo], by simp +decide [blkCond, hlo, hP.rl],
        by simpa [blkCond] using hm⟩
  have h := HTB.whileG (BInv keys a KB F A B w m₀) (fun b => 60 * (keys.length - 2 * w * b)) 0
    hinit fun b => by
      by_cases hlt : 2 * w * b < keys.length
      · refine HTB.toG (blkStep_spec hl hS hG b) ?_
        have e : 2 * w * (b + 1) = 2 * w * b + 2 * w := by ring
        rw [e]
        omega
      · exact fun c ⟨⟨_, _, hT, _⟩, h0⟩ => (h0 (by omega)).elim
  refine h.mono (fun _ h => h) (fun c ⟨y, ⟨hP, _, hT, hm⟩, h0⟩ => ⟨hP, ?_⟩) (by simp)
  rwa [hG.passPre_full hw (by omega)] at hm

end blocks

/-! ### The passes -/

section passes

variable (keys : List ℕ) (KB F : ℕ) (m₀ : ℕ → ℕ)

/-- The pass loop after `p` passes (after the test): the array `sortP keys p` at `A`. -/
def SInv (p : ℕ) (c : Config) : Prop :=
  ∃ A B, Lay keys.length KB F A B ∧ PG keys.length KB F A B (2 ^ p) c ∧
    c.reg rT = keys.length - 2 ^ p ∧ PMem keys (sortP keys p) KB F A B m₀ [] c.mem

variable {keys KB F m₀}

/-- One pass with fixed buffers `A`, `B`, then the test of the next. -/
theorem passStep_AB (hS : F + 2 * keys.length ≤ S) (p A B : ℕ) (hl : Lay keys.length KB F A B) :
    HTB S (.seq passBody passCond)
      (fun c => PG keys.length KB F A B (2 ^ p) c ∧ PMem keys (sortP keys p) KB F A B m₀ [] c.mem)
      (SInv keys KB F m₀ (p + 1)) (60 * keys.length + 10) := by
  have hw : 0 < 2 ^ p := by positivity
  have h0 : HTB S (.const oLo 0)
      (fun c => PG keys.length KB F A B (2 ^ p) c ∧ PMem keys (sortP keys p) KB F A B m₀ [] c.mem)
      (fun c => PG keys.length KB F A B (2 ^ p) c ∧ c.reg oLo = 0 ∧
        PMem keys (sortP keys p) KB F A B m₀ [] c.mem) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hP, hm⟩ =>
      ⟨(show RegIndep [oLo] (PG keys.length KB F A B (2 ^ p)) by indep [pG_iff]).setReg (by decide)
        _ hP, by simp, hm⟩
  have hloop := blkLoop_spec (S := S) (m₀ := m₀) hl hS (good_sortP p) hw
  have hfin : HTB S (.seq (.seq (swap oA oB) (.seq (.add oW oW oW) (.add oW2 oW oW))) passCond)
      (fun c => PG keys.length KB F A B (2 ^ p) c ∧
        PMem keys (sortP keys p) KB F A B m₀ (pass keys (2 ^ p) (sortP keys p)) c.mem)
      (SInv keys KB F m₀ (p + 1)) 6 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hP, hm⟩ => by
      refine ⟨B, A, ⟨hl.1, by rcases hl.2 with h | h <;> omega⟩, ?_, ?_, ?_⟩
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp +decide [passCond, run_swap (show oA ≠ oB by decide), h1, h2, h3, h4, h5, h7,
            pow_succ] <;> ring
      · simp +decide [passCond, run_swap (show oA ≠ oB by decide), hP.rw, hP.rl, pow_succ]
        ring_nf
      · have hmem : (run (.seq (.seq (swap oA oB) (.seq (.add oW oW oW) (.add oW2 oW oW)))
            passCond) c).mem = c.mem := run_mem_of_stores (by decide) rfl c
        rw [hmem]
        exact ⟨hm.ky, hm.dst, arr_nil _ _, hm.out⟩
  exact (h0.seq (hloop.seq hfin).reassoc).reassoc.weaken (by omega)

/-- One pass, then the test of the next. -/
theorem passStep_spec (hS : F + 2 * keys.length ≤ S) (p : ℕ) :
    HTB S (.seq passBody passCond) (fun c => SInv keys KB F m₀ p c ∧ c.reg rT ≠ 0)
      (SInv keys KB F m₀ (p + 1)) (60 * keys.length + 10) :=
  fun c ⟨⟨A, B, hl, hP, _, hm⟩, _⟩ => passStep_AB hS p A B hl c ⟨hP, hm⟩

/-- **The pass loop**: `⌈log₂ L⌉` passes, after which the stable sort is at `A`. -/
theorem passLoop_spec (hS : F + 2 * keys.length ≤ S) {P : Config → Prop}
    (hinit : HTB S passCond P (SInv keys KB F m₀ 0) 1) :
    HTB S (whileC passCond passBody) P
      (fun c => ∃ A B, Lay keys.length KB F A B ∧ PG keys.length KB F A B (c.reg oW) c ∧
        PMem keys (sortKey keys) KB F A B m₀ [] c.mem)
      (1 + (Nat.clog 2 keys.length * (60 * keys.length + 11) + 1)) := by
  have h := HTB.whileG (SInv keys KB F m₀)
    (fun p => (Nat.clog 2 keys.length - p) * (60 * keys.length + 11)) 0 hinit fun p => by
      by_cases hp : p < Nat.clog 2 keys.length
      · refine HTB.toG (passStep_spec hS p) ?_
        have e : Nat.clog 2 keys.length - p = (Nat.clog 2 keys.length - (p + 1)) + 1 := by omega
        rw [e, Nat.add_mul, one_mul]
        omega
      · intro c ⟨⟨A, B, _, _, hT, _⟩, h0⟩
        exfalso
        have : 2 ^ p < keys.length := by omega
        exact hp ((Nat.lt_clog_iff_pow_lt (by norm_num)).mpr this)
  refine h.mono (fun _ h => h) (fun c ⟨p, ⟨A, B, hl, hP, hT, hm⟩, h0⟩ => ⟨A, B, hl, ?_, ?_⟩)
    (by simp)
  · rw [hP.rw]; exact hP
  · rwa [(good_sortP p).eq_sortKey (by omega)] at hm

end passes

/-! ### The whole sort -/

/-- The input of `msort`: `L` keys at `reg oKB`, below the free address. -/
structure SortIn (keys : List ℕ) (c : Config) : Prop where
  rl : c.reg oL = keys.length
  ky : Arr c.mem (c.reg oKB) keys
  below : c.reg oKB + keys.length ≤ c.reg rFREE

/-- The result of `msort` (`c₀`: the configuration on entry). -/
structure SortOut (keys : List ℕ) (c₀ c : Config) : Prop where
  sq : Arr c.mem (c.reg oSQ) (sortKey keys)
  rsq : c₀.reg rFREE ≤ c.reg oSQ ∧ c.reg oSQ + keys.length ≤ c.reg rFREE
  free : c.reg rFREE = c₀.reg rFREE + 2 * keys.length
  same : ∀ x, x < c₀.reg rFREE ∨ c₀.reg rFREE + 2 * keys.length ≤ x → c.mem x = c₀.mem x

/-- The constant of the running time of `msort`. -/
def CM : ℕ := 100

section init

variable (keys : List ℕ) (KB F : ℕ) (m₀ : ℕ → ℕ)

/-- The initialisation after `i` cells of `A`. -/
def IInv (i : ℕ) (c : Config) : Prop :=
  c.reg oA = F ∧ c.reg oB = F + keys.length ∧ c.reg oKB = KB ∧ c.reg oL = keys.length ∧
    c.reg rFREE = F + 2 * keys.length ∧ Arr c.mem KB keys ∧ Arr c.mem F (List.range i) ∧
    ∀ x, x < F ∨ F + 2 * keys.length ≤ x → c.mem x = m₀ x

variable {keys KB F m₀}

theorem initBody_spec (hKB : KB + keys.length ≤ F) (hS : F + 2 * keys.length ≤ S) (i : ℕ)
    (hi : i < keys.length) :
    HTB S initBody (fun c => IInv keys KB F m₀ i c ∧ c.reg oK = i ∧ c.reg oL = keys.length)
      (fun c => IInv keys KB F m₀ (i + 1) c ∧ c.reg oK = i ∧ c.reg oL = keys.length) 2 := by
  refine HTB.run_le (by decide) (by decide)
    fun c ⟨⟨hA, hB, hK, hL, hF, hky, harr, hout⟩, hi', hl⟩ =>
    ⟨by addr_ok [initBody, hA, hi'], ?_⟩
  have hrun : run initBody c = (c.setMem (F + i) i).setReg rT (F + i) := by
    simp +decide [initBody, run_st, hA, hi']
  rw [hrun]
  refine ⟨⟨by simp +decide [hA], by simp +decide [hB], by simp +decide [hK], by simp +decide [hL],
    by simp +decide [hF], ?_, ?_, fun x hx => ?_⟩, by simp +decide [hi'], by simp +decide [hl]⟩
  · simp only [setReg_mem, setMem_mem_upd]; exact hky.upd_of_disjoint (by omega)
  · simp only [setReg_mem, setMem_mem_upd]
    rw [List.range_succ]
    exact harr.upd_snoc (by simp)
  · simp only [setReg_mem, setMem_mem_upd, upd_apply, show x ≠ F + i by omega, ↓reduceIte]
    exact hout x hx

/-- **The initialisation**: the buffers, `A = 0, 1, …, L − 1`. -/
theorem sInit_spec (c₀ : Config) (hIn : SortIn keys c₀)
    (hS : c₀.reg rFREE + 2 * keys.length ≤ S) :
    HTB S sInit (· = c₀)
      (fun c => IInv keys (c₀.reg oKB) (c₀.reg rFREE) c₀.mem keys.length c ∧
        c.reg oK = keys.length ∧ c.reg oL = keys.length) (6 + (keys.length * (2 + 4) + 3)) := by
  have hKB := hIn.below
  have h0 : HTB S (.seq (alloc oA oL) (alloc oB oL)) (· = c₀)
      (fun c => IInv keys (c₀.reg oKB) (c₀.reg rFREE) c₀.mem 0 c ∧ c.reg oL = keys.length) 6 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      rw [hc]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x _ => ?_⟩, ?_⟩
      all_goals simp +decide only [run_seq',
        run_alloc (show oL ≠ rT by decide) (show oA ≠ oL by decide),
        run_alloc (show oL ≠ rT by decide) (show oB ≠ oL by decide), setReg_reg, setReg_mem,
        ↓reduceIte, hIn.rl]
      all_goals first | omega | exact hIn.ky | simp
  have h1 := HTB.forUpC (S := S) (i := oK) (n := oL) (N := keys.length) (body := initBody)
    (IInv keys (c₀.reg oKB) (c₀.reg rFREE) c₀.mem) 2 (by decide) (by decide) (by decide)
    (fun j => by indep [IInv]) (fun j hj => initBody_spec hKB hS j hj)
  exact (h0.seq h1).assoc

/-- The width `w = 1`. -/
theorem w1_spec (KB F : ℕ) (m₀ : ℕ → ℕ) :
    HTB S (.seq (.const oW 1) (.add oW2 oW oW))
      (fun c => IInv keys KB F m₀ keys.length c ∧ c.reg oK = keys.length ∧ c.reg oL = keys.length)
      (fun c => IInv keys KB F m₀ keys.length c ∧ c.reg oW = 1 ∧ c.reg oW2 = 2) 2 :=
  HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hI, _, _⟩ =>
    ⟨(show Indep (wregs (.seq (.const oW 1) (.add oW2 oW oW))) (IInv keys KB F m₀ keys.length) by
        indep [IInv]).run (by decide) rfl rfl hI,
      by simp, by simp⟩

/-- The first test of the pass loop. -/
theorem pass0_spec (hKB : KB + keys.length ≤ F) :
    HTB S passCond (fun c => IInv keys KB F m₀ keys.length c ∧ c.reg oW = 1 ∧ c.reg oW2 = 2)
      (SInv keys KB F m₀ 0) 1 :=
  HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
    fun c ⟨⟨hA, hB, hK, hL, hF, hky, harr, hout⟩, hw, hw2⟩ =>
      ⟨F, F + keys.length, ⟨hKB, Or.inl ⟨rfl, rfl⟩⟩,
        ⟨by simp [passCond, hK], by simp [passCond, hL], by simp [passCond, hA],
          by simp [passCond, hB], by simp [passCond, hw], by simp [passCond, hw2],
          by simp [passCond, hF]⟩,
        by simp [passCond, hL, hw], ⟨hky, harr, arr_nil _ _, hout⟩⟩

end init

/-- **The stable merge sort.** Given `L` keys `keys` (arbitrary naturals) at `reg oKB` below the
free address `F` (`SortIn`), `msort` stores `sortKey keys` — the indices `0, …, L − 1` sorted by
`(key, index)` (`List.mergeSort` on `(key, index)`; `pairwise_sortKey`, `eq_sortKey`) — at
`reg oSQ ∈ [F, F + L]`, sets `rFREE := F + 2L`, leaves the memory outside `[F, F + 2L)`
unchanged, within `CM · (L · (⌈log₂ L⌉ + 1) + 1)` steps, accessing only the addresses below any
`S ≥ F + 2L`, comparing keys only. -/
theorem msort_spec (keys : List ℕ) (c₀ : Config) (hIn : SortIn keys c₀)
    (hS : c₀.reg rFREE + 2 * keys.length ≤ S) :
    HTB S msort (· = c₀) (fun c => SortOut keys c₀ c ∧ Frame msort c₀ c)
      (CM * (keys.length * (Nat.clog 2 keys.length + 1) + 1)) := by
  have hKB := hIn.below
  have hmov : HTB S (mov oSQ oA)
      (fun c => ∃ A B, Lay keys.length (c₀.reg oKB) (c₀.reg rFREE) A B ∧
        PG keys.length (c₀.reg oKB) (c₀.reg rFREE) A B (c.reg oW) c ∧
        PMem keys (sortKey keys) (c₀.reg oKB) (c₀.reg rFREE) A B c₀.mem [] c.mem)
      (SortOut keys c₀) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨A, B, hl, hP, hm⟩ => by
      rw [run_mov (by decide)]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [setReg_mem, setReg_reg, ↓reduceIte, hP.ra]
        exact hm.src
      · simp +decide only [setReg_reg, ↓reduceIte, hP.ra, hP.rfree]
        rcases hl.2 with h | h <;> omega
      · simp +decide only [setReg_reg, ↓reduceIte, hP.rfree]
      · intro x hx
        simp only [setReg_mem]
        exact hm.out x hx
  have h := ((w1_spec (S := S) (keys := keys) (c₀.reg oKB) (c₀.reg rFREE) c₀.mem).seq
    ((passLoop_spec (m₀ := c₀.mem) hS (pass0_spec hKB)).seq hmov)).assoc
  have hall := ((sInit_spec c₀ hIn hS).seq h).withFrame c₀
  refine hall.mono (fun c hc => ⟨hc, hc⟩) (fun c h => h) ?_
  have hP : Nat.clog 2 keys.length ≤ keys.length * Nat.clog 2 keys.length := by
    rcases Nat.eq_zero_or_pos keys.length with h0 | h0
    · simp [h0]
    · exact Nat.le_mul_of_pos_left _ h0
  have e1 : Nat.clog 2 keys.length * (60 * keys.length + 11) =
      60 * (keys.length * Nat.clog 2 keys.length) + 11 * Nat.clog 2 keys.length := by ring
  have e2 : CM * (keys.length * (Nat.clog 2 keys.length + 1) + 1) =
      100 * (keys.length * Nat.clog 2 keys.length) + 100 * keys.length + 100 := by
    simp only [CM]; ring
  rw [e1, e2]
  omega

/-- The registers written by `msort`: `rT`, `rFREE` and `802–816` (not the inputs `oKB`, `oL`). -/
theorem msort_wregs : ∀ r ∈ wregs msort, r = rT ∨ r = rFREE ∨ (oSQ ≤ r ∧ r ≤ oKY) := by
  decide

/-- `msort` does not write output. -/
theorem msort_writes : writes msort = false := by decide

end STACS2027.Runtimes.Sort
