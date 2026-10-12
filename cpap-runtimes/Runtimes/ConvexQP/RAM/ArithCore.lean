module

public import Outerplanar.RAM.BoundedLib
public import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Big-number arithmetic on the add/subtract RAM: the doubling-table core

Registers and memory cells of the RAM hold unbounded naturals, so a big number is one cell;
the machine has only addition and truncated subtraction. This file provides the one
non-trivial loop of the arithmetic library:

**`gCore`** (registers `400–409`): from `a₀ = reg gA0 ≥ 1`, `b₀ = reg gB0` and `L = reg gL`, it
builds the table `(a₀·2^j, b₀·2^j)` for all `j` with `a₀·2^j ≤ L` (doubling) in the scratch cells
`rFREE, rFREE + 1, …`, then walks the table from the top, subtracting `a₀·2^j` from the remainder
whenever possible and adding `b₀·2^j` to an accumulator. It ends with
`reg gAcc = b₀ · (L / a₀)` and `reg gR = L % a₀` (`gCore_specB`), zeroes the scratch cells again
on the way down (so the memory is unchanged), and costs `O(size L + 1 − size a₀)` steps.
With `a₀ = 1, b₀ = x, L = y` this is the multiplication `x·y` in `O(size y + 1)` steps; with
`a₀ = y, b₀ = 1, L = x` the division with remainder in `O(size x − size y + 2)` steps.

Also: `pow2Core` (`reg pR := 2 ^ reg pE`, registers `410–411`, `4e + 2` steps) and the register
list `arithW` of the whole library (`rT` and `400–449`); the *memory restoring* rule
`HTB.memRestore` (a program that leaves the memory as it found it satisfies frame-style triples
for every assertion independent of its registers) gives the frame forms.

**Space** (`Outerplanar/RAM/BoundedHT.lean`): the table occupies the `2 · entB a₀ L` cells from the
free address `F`, so `gCore_specB` is an `HTB S` triple for every `S ≥ F + 2 · entB a₀ L`
(the scratch counts in the space bound); `gCore_frameB`, `pow2Core_specB`, `HTB.mulN`
(scratch `2 · size y`), `HTB.divmodN` (`2 · (size x + 1 − size y)`), `HTB.pow2N` are the bounded
forms. The macros with a scratch table have a master form with the bound in the precondition
(`HTB.mulN_pre`, `HTB.divmodN_pre`), from which the `hS` form follows. Only the bounded forms
exist for the routines with a scratch table (the time-only forms were removed with the last
time-only caller); `HTB.toHT` recovers a time-only triple.
Guide: `NOTE-arith.md`.
-/

@[expose] public section

namespace STACS2027.Runtimes.Arith

open STACS2027.RAM

/-! ### Registers -/

/-- `gCore` input: the unit `a₀ ≥ 1`. -/
abbrev gA0 : ℕ := 400
/-- `gCore` input: the companion `b₀`. -/
abbrev gB0 : ℕ := 401
/-- `gCore` input: the number `L` to decompose. -/
abbrev gL : ℕ := 402
/-- `gCore`: the current `a₀·2^k`. -/
abbrev gP : ℕ := 403
/-- `gCore`: the current `b₀·2^k`. -/
abbrev gQ : ℕ := 404
/-- `gCore`: the number of table entries. -/
abbrev gK : ℕ := 405
/-- `gCore`: the address of the current table entry. -/
abbrev gPtr : ℕ := 406
/-- `gCore`: `gPtr + 1`. -/
abbrev gPtr2 : ℕ := 407
/-- `gCore` output: the remainder `L % a₀`. -/
abbrev gR : ℕ := 408
/-- `gCore` output: the accumulator `b₀ · (L / a₀)`. -/
abbrev gAcc : ℕ := 409
/-- `pow2Core` input: the exponent (consumed). -/
abbrev pE : ℕ := 410
/-- `pow2Core` output: `2 ^ e`. -/
abbrev pR : ℕ := 411

/-- All registers the arithmetic library may write: `rT` and the block `400–449`. -/
def arithW : List ℕ := rT :: List.range' 400 50

/-- The registers written by `gCore` (and by `pow2Core`): `rT` and `400–411`. -/
def gW : List ℕ := rT :: List.range' 400 12

theorem mem_arithW_of_gW {r : ℕ} (h : r ∈ gW) : r ∈ arithW := by
  simp only [gW, arithW, List.mem_cons, List.mem_range'_1] at h ⊢
  omega

/-! ### Bit lengths -/

/-- `2 ^ (size n - 1) ≤ n` for `n ≥ 1`. -/
theorem pow_size_pred_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ (Nat.size n - 1) ≤ n :=
  Nat.lt_size.mp (by have := Nat.size_pos.mpr hn; omega)

/-- If `a·2^k ≤ L` with `a ≥ 1`, then `k + size a ≤ size L`. -/
theorem add_size_le_of_mul_pow_le {a k L : ℕ} (ha : 1 ≤ a) (h : a * 2 ^ k ≤ L) :
    k + Nat.size a ≤ Nat.size L := by
  have h1 := pow_size_pred_le ha
  have h2 : 2 ^ (Nat.size a - 1 + k) ≤ L := by
    rw [pow_add]
    exact le_trans (Nat.mul_le_mul_right _ h1) h
  have h3 := Nat.lt_size.mpr h2
  have := Nat.size_pos.mpr ha
  omega

/-! ### The table -/

/-- The memory with the first `k` table entries `(a·2^j, b·2^j)` at `F + 2j`, `F + 2j + 1`. -/
def mtab (m₀ : ℕ → ℕ) (F a b : ℕ) : ℕ → ℕ → ℕ
  | 0 => m₀
  | k + 1 => upd (upd (mtab m₀ F a b k) (F + 2 * k) (a * 2 ^ k)) (F + 2 * k + 1) (b * 2 ^ k)

theorem mtab_of_ge {m₀ : ℕ → ℕ} {F a b : ℕ} : ∀ {k i : ℕ}, F + 2 * k ≤ i → mtab m₀ F a b k i = m₀ i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    have h1 : i ≠ F + 2 * k + 1 := by omega
    have h2 : i ≠ F + 2 * k := by omega
    simp only [mtab, upd_apply, h1, h2, ↓reduceIte]
    exact mtab_of_ge (by omega)

theorem mtab_lo (m₀ : ℕ → ℕ) (F a b k : ℕ) : mtab m₀ F a b (k + 1) (F + 2 * k) = a * 2 ^ k := by
  simp [mtab]

theorem mtab_hi (m₀ : ℕ → ℕ) (F a b k : ℕ) : mtab m₀ F a b (k + 1) (F + 2 * k + 1) = b * 2 ^ k := by
  simp [mtab]

/-- Clearing the top entry. -/
theorem mtab_clear {m₀ : ℕ → ℕ} {F : ℕ} (hz : ZeroFrom m₀ F) (a b k : ℕ) :
    upd (upd (mtab m₀ F a b (k + 1)) (F + 2 * k) 0) (F + 2 * k + 1) 0 = mtab m₀ F a b k := by
  funext i
  simp only [mtab, upd_apply]
  by_cases h1 : i = F + 2 * k + 1
  · subst h1; simp only [↓reduceIte]; rw [mtab_of_ge (by omega), hz.get (by omega)]
  · by_cases h2 : i = F + 2 * k
    · subst h2; simp only [h1, ↓reduceIte]
      rw [mtab_of_ge (by omega), hz.get (by omega)]
    · simp [h1, h2]

/-! ### The program -/

/-- Build test: `rT := L + 1 − a₀·2^k` (nonzero iff `a₀·2^k ≤ L`). -/
def gCond : Stmt := .seq (addc rT gL 1) (.sub rT rT gP)

/-- Build step: store the entry, double, count. -/
def gBody : Stmt :=
  .seq (.store gPtr gP) (.seq (addc gPtr2 gPtr 1) (.seq (.store gPtr2 gQ)
    (.seq (addc gPtr gPtr 2) (.seq (.add gP gP gP) (.seq (.add gQ gQ gQ) (inc gK))))))

/-- Descent step: take the top entry, clear it, subtract if possible. -/
def gDesc : Stmt :=
  .seq (dec gK) (.seq (subc gPtr gPtr 2) (.seq (addc gPtr2 gPtr 1) (.seq (.load gP gPtr)
    (.seq (.load gQ gPtr2) (.seq (.const rT 0) (.seq (.store gPtr rT) (.seq (.store gPtr2 rT)
    (ifLe gP gR (.seq (.sub gR gR gP) (.add gAcc gAcc gQ)) .skip))))))))

/-- Initialisation. -/
def gInit : Stmt := .seq (mov gP gA0) (.seq (mov gQ gB0) (.seq (mov gPtr rFREE) (.const gK 0)))

/-- Between the two loops. -/
def gMid : Stmt := .seq (mov gR gL) (.const gAcc 0)

/-- **The doubling-table core**: `gAcc := b₀ · (L / a₀)`, `gR := L % a₀`. -/
def gCore : Stmt := .seq gInit (.seq (whileC gCond gBody) (.seq gMid (.loop gK gDesc)))

theorem wregs_gCore_sub : ∀ r ∈ wregs gCore, r ∈ gW := by decide
theorem writes_gCore : writes gCore = false := rfl

/-- The number of table entries is at most `entB a L = size L + 1 − size a`. -/
def entB (a L : ℕ) : ℕ := Nat.size L + 1 - Nat.size a

/-! ### The build loop -/

/-- The state after a build test. -/
structure BInv (m₀ : ℕ → ℕ) (F a b L : ℕ) (c : Config) : Prop where
  l : c.reg gL = L
  free : c.reg rFREE = F
  p : c.reg gP = a * 2 ^ c.reg gK
  q : c.reg gQ = b * 2 ^ c.reg gK
  ptr : c.reg gPtr = F + 2 * c.reg gK
  mem : c.mem = mtab m₀ F a b (c.reg gK)
  t : c.reg rT = L + 1 - a * 2 ^ c.reg gK
  kb : c.reg gK ≤ entB a L

theorem gInit_spec (m₀ : ℕ → ℕ) (F a b L : ℕ) :
    HT gInit (fun c => c.reg gA0 = a ∧ c.reg gB0 = b ∧ c.reg gL = L ∧ c.reg rFREE = F ∧
      c.mem = m₀)
      (fun c => c.reg gL = L ∧ c.reg rFREE = F ∧ c.reg gP = a ∧ c.reg gQ = b ∧
        c.reg gPtr = F ∧ c.reg gK = 0 ∧ c.mem = m₀) 7 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨ha, hb, hl, hF, hm⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp +decide only [gInit, run_seq', run_mov, run_const, setReg_reg, setReg_mem, ↓reduceIte,
    ha, hb, hl, hF, hm]

theorem gCond_spec (m₀ : ℕ → ℕ) (F a b L : ℕ) :
    HT gCond (fun c => c.reg gL = L ∧ c.reg rFREE = F ∧ c.reg gP = a ∧ c.reg gQ = b ∧
        c.reg gPtr = F ∧ c.reg gK = 0 ∧ c.mem = m₀)
      (fun c => BInv m₀ F a b L c ∧ entB a L - c.reg gK ≤ entB a L) 3 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨hl, hF, hp, hq, hptr, hk, hm⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
  simp +decide only [gCond, run_seq', run_addc, run_sub, setReg_reg, setReg_mem, ↓reduceIte,
    hl, hF, hp, hq, hptr, hk, hm] <;> simp [mtab]

theorem gStep_spec (m₀ : ℕ → ℕ) (F a b L : ℕ) (ha : 1 ≤ a) (v : ℕ) :
    HT (.seq gBody gCond) (fun c => BInv m₀ F a b L c ∧ c.reg rT ≠ 0 ∧ entB a L - c.reg gK = v)
      (fun c => BInv m₀ F a b L c ∧ entB a L - c.reg gK < v) 13 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨hI, ht, hv⟩ => ?_
  have hle : a * 2 ^ c.reg gK ≤ L := by have := hI.t; omega
  have hkb : c.reg gK + 1 ≤ entB a L := by
    have := add_size_le_of_mul_pow_le ha hle; unfold entB; omega
  have hp := hI.p
  have hq := hI.q
  have hptr := hI.ptr
  have hm := hI.mem
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
  simp +decide only [gBody, gCond, run_seq', run_store, run_addc, run_add, run_inc, run_sub,
    setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hI.l, hI.free,
    hp, hq, hptr, hm]
  · rw [pow_succ]; ring
  · rw [pow_succ]; ring
  · ring
  · rfl
  · rw [pow_succ]; ring_nf
  · omega
  · omega

/-! ### The descent loop -/

/-- The state before a descent step. -/
structure DInv (m₀ : ℕ → ℕ) (F a b L : ℕ) (c : Config) : Prop where
  mem : c.mem = mtab m₀ F a b (c.reg gK)
  ptr : c.reg gPtr = F + 2 * c.reg gK
  qc : ∃ q, c.reg gR + a * q = L ∧ c.reg gAcc = b * q
  rlt : c.reg gR < a * 2 ^ c.reg gK
  kb : c.reg gK ≤ entB a L

theorem gDesc_spec (m₀ : ℕ → ℕ) (F a b L : ℕ) (hz : ZeroFrom m₀ F) (v : ℕ) :
    HT gDesc (fun c => DInv m₀ F a b L c ∧ c.reg gK ≠ 0 ∧ c.reg gK = v)
      (fun c => DInv m₀ F a b L c ∧ c.reg gK < v) 16 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨hI, hk, hv⟩ => ?_
  obtain ⟨k, hk'⟩ : ∃ k, c.reg gK = k + 1 := ⟨c.reg gK - 1, by omega⟩
  have hptr : c.reg gPtr - 2 = F + 2 * k := by rw [hI.ptr, hk']; omega
  have hlo : c.mem (F + 2 * k) = a * 2 ^ k := by rw [hI.mem, hk', mtab_lo]
  have hhi : c.mem (F + 2 * k + 1) = b * 2 ^ k := by rw [hI.mem, hk', mtab_hi]
  have hclr : upd (upd c.mem (F + 2 * k) 0) (F + 2 * k + 1) 0 = mtab m₀ F a b k := by
    rw [hI.mem, hk', mtab_clear hz]
  obtain ⟨q, hq1, hq2⟩ := hI.qc
  have hrlt := hI.rlt
  rw [hk', pow_succ] at hrlt
  have hkb := hI.kb
  by_cases hle : a * 2 ^ k ≤ c.reg gR
  · refine ⟨⟨?_, ?_, ⟨q + 2 ^ k, ?_, ?_⟩, ?_, ?_⟩, ?_⟩ <;>
    simp +decide only [gDesc, run_seq', run_dec, run_subc, run_addc, run_load, run_const,
      run_store, run_ifLe, run_sub, run_add, setReg_reg, setReg_mem, setMem_reg,
      setMem_mem_upd, ↓reduceIte, hk', hptr, hlo, hhi, Nat.add_sub_cancel, hle, hclr, hq2]
    · rw [Nat.mul_add]; omega
    · ring
    · have : a * (2 ^ k * 2) = 2 * (a * 2 ^ k) := by ring
      omega
    · omega
    · omega
  · refine ⟨⟨?_, ?_, ⟨q, ?_, ?_⟩, ?_, ?_⟩, ?_⟩ <;>
    simp +decide only [gDesc, run_seq', run_dec, run_subc, run_addc, run_load, run_const,
      run_store, run_ifLe, run_skip, setReg_reg, setReg_mem, setMem_reg,
      setMem_mem_upd, ↓reduceIte, hk', hptr, hlo, hhi, Nat.add_sub_cancel, hle, hclr, hq2]
    · exact hq1
    · omega
    · omega
    · omega

/-- Cost of `gCore` for at most `K` table entries. -/
def gCost (K : ℕ) : ℕ := 31 * K + 15

theorem gMid_spec (m₀ : ℕ → ℕ) (F a b L : ℕ) :
    HT gMid (fun c => BInv m₀ F a b L c ∧ c.reg rT = 0)
      (fun c => DInv m₀ F a b L c ∧ c.reg gK ≤ entB a L) 3 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨hI, h0⟩ => ?_
  have hm := hI.mem
  have hptr := hI.ptr
  have hkb := hI.kb
  have ht := hI.t
  refine ⟨⟨?_, ?_, ⟨0, ?_, ?_⟩, ?_, ?_⟩, ?_⟩ <;>
  simp +decide only [gMid, run_seq', run_mov, run_const, setReg_reg, setReg_mem, ↓reduceIte,
    hI.l, hm, hptr, Nat.mul_zero, Nat.add_zero] <;> omega

section bounded

variable {S : ℕ}

/-- A build step within the bound: the two stores at `F + 2k`, `F + 2k + 1`, `k < entB a L`. -/
theorem gStep_specB (m₀ : ℕ → ℕ) (F a b L : ℕ) (ha : 1 ≤ a) (hS : F + 2 * entB a L ≤ S) (v : ℕ) :
    HTB S (.seq gBody gCond) (fun c => BInv m₀ F a b L c ∧ c.reg rT ≠ 0 ∧ entB a L - c.reg gK = v)
      (fun c => BInv m₀ F a b L c ∧ entB a L - c.reg gK < v) 13 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨hI, ht, _⟩ => by
    have hle : a * 2 ^ c.reg gK ≤ L := by have := hI.t; omega
    have hkb : c.reg gK + 1 ≤ entB a L := by
      have := add_size_le_of_mul_pow_le ha hle; unfold entB; omega
    have hptr := hI.ptr
    addr_ok [gBody, gCond, hptr]) (gStep_spec m₀ F a b L ha v)

/-- A descent step within the bound: the loads and stores at `F + 2k`, `F + 2k + 1`. -/
theorem gDesc_specB (m₀ : ℕ → ℕ) (F a b L : ℕ) (hz : ZeroFrom m₀ F) (hS : F + 2 * entB a L ≤ S)
    (v : ℕ) :
    HTB S gDesc (fun c => DInv m₀ F a b L c ∧ c.reg gK ≠ 0 ∧ c.reg gK = v)
      (fun c => DInv m₀ F a b L c ∧ c.reg gK < v) 16 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨hI, hk, _⟩ => by
    have hkb := hI.kb
    have hptr := hI.ptr
    addr_ok [gDesc, hptr]) (gDesc_spec m₀ F a b L hz v)

/-- **The doubling-table core within the bound** `S ≥ F + 2 · entB a₀ L` (the table at
`F, F + 1, …`). For `a₀ ≥ 1`, from `reg gA0 = a₀`, `reg gB0 = b₀`, `reg gL = L` and zero memory
from `rFREE = F` on: `reg gAcc = b₀ · (L / a₀)`, `reg gR = L % a₀`, the memory unchanged, within
`gCost (size L + 1 − size a₀)` steps. -/
theorem gCore_specB (m₀ : ℕ → ℕ) (F a b L : ℕ) (ha : 1 ≤ a) (hz : ZeroFrom m₀ F)
    (hS : F + 2 * entB a L ≤ S) :
    HTB S gCore (fun c => c.reg gA0 = a ∧ c.reg gB0 = b ∧ c.reg gL = L ∧ c.reg rFREE = F ∧
      c.mem = m₀)
      (fun c => c.reg gAcc = b * (L / a) ∧ c.reg gR = L % a ∧ c.mem = m₀)
      (gCost (entB a L)) := by
  have hw := HTB.whileC (cond := gCond) (body := gBody) (fun c => entB a L - c.reg gK)
    (HTB.of_HT rfl (gCond_spec m₀ F a b L)) (gStep_specB m₀ F a b L ha hS)
  have hd := HTB.loopT (a := gK) (body := gDesc) (fun c => c.reg gK)
    (gDesc_specB m₀ F a b L hz hS) (entB a L)
  refine ((HTB.of_HT rfl (gInit_spec m₀ F a b L)).seq (hw.seq
    ((HTB.of_HT rfl (gMid_spec m₀ F a b L)).seq hd))).mono
    (fun _ h => h) (fun c ⟨hI, h0⟩ => ?_) (by unfold gCost; omega)
  obtain ⟨q, hq1, hq2⟩ := hI.qc
  have hrlt := hI.rlt
  have hm := hI.mem
  rw [h0] at hrlt hm
  simp only [pow_zero, Nat.mul_one] at hrlt
  obtain ⟨hd1, hd2⟩ := (Nat.div_mod_unique (by omega : 0 < a)).mpr ⟨hq1, hrlt⟩
  exact ⟨by rw [hq2, hd1], hd2.symm, hm⟩

/-- `gCore` in frame style within the bound: every assertion `P` independent of `rT, 400–411`
that implies `ZeroFrom c.mem (c.reg rFREE)` and leaves room for the table survives. -/
theorem gCore_frameB {P : Config → Prop} (hP : Indep gW P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (a b L : ℕ)
    (hS : ∀ c, P c → c.reg rFREE + 2 * entB a L ≤ S) :
    HTB S gCore (fun c => P c ∧ (c.reg gA0 = a ∧ c.reg gB0 = b ∧ c.reg gL = L ∧ 1 ≤ a))
      (fun c => P c ∧ (c.reg gAcc = b * (L / a) ∧ c.reg gR = L % a)) (gCost (entB a L)) :=
  HTB.memRestore (fun c₀ hp ⟨h1, h2, h3, ha⟩ =>
    (gCore_specB c₀.mem (c₀.reg rFREE) a b L ha (hZ c₀ hp) (hS c₀ hp)).mono
      (fun c hc => by subst hc; exact ⟨h1, h2, h3, rfl, rfl⟩)
      (fun c ⟨e1, e2, e3⟩ => ⟨⟨e1, e2⟩, e3⟩) le_rfl)
    writes_gCore wregs_gCore_sub hP

end bounded

/-! ### Powers of two -/

/-- `reg pR := 2 ^ reg pE` (consumes `pE`). -/
def pow2Core : Stmt := .seq (.const pR 1) (.loop pE (.seq (.add pR pR pR) (dec pE)))

theorem wregs_pow2Core : wregs pow2Core = [pR, pR, rT, pE] := rfl

/-- **Powers of two** in `4e + 2` steps. -/
theorem pow2Core_spec {P : Config → Prop} (hP : Indep [pE, pR, rT] P) (e : ℕ) :
    HT pow2Core (fun c => P c ∧ c.reg pE = e) (fun c => P c ∧ c.reg pR = 2 ^ e) (4 * e + 2) := by
  let Inv : Config → Prop := fun c => P c ∧ c.reg pR = 2 ^ (e - c.reg pE) ∧ c.reg pE ≤ e
  have h0 : HT (.const pR 1) (fun c => P c ∧ c.reg pE = e) (fun c => Inv c ∧ c.reg pE ≤ e) 1 :=
    HT.run_le trivial le_rfl fun c ⟨hc, he⟩ => by
      refine ⟨⟨hP.setReg (by simp) _ hc, ?_, ?_⟩, ?_⟩ <;> simp +decide [he]
  have hl := HT.loopT (a := pE) (body := .seq (.add pR pR pR) (dec pE)) (Inv := Inv)
    (fun c => c.reg pE) (T := 3) (fun v => HT.run_le (by decide) (by decide)
      fun c ⟨⟨hc, hr, hle⟩, hne, hv⟩ => by
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · simp only [run_seq', run_add, run_dec (show pE ≠ rT by decide)]
          exact hP.setReg (by simp) _ (hP.setReg (by simp) _ (hP.setReg (by simp) _ hc))
        · simp +decide only [run_seq', run_add, run_dec, setReg_reg, ↓reduceIte, hr]
          rw [← two_mul, ← pow_succ']
          congr 1
          omega
        · simp +decide only [run_seq', run_add, run_dec, setReg_reg, ↓reduceIte]; omega
        · simp +decide only [run_seq', run_add, run_dec, setReg_reg, ↓reduceIte]; omega) e
  refine (h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨hc, hr, _⟩, h0⟩ => ⟨hc, by rw [hr, h0]; rfl⟩)
    (by omega)

/-- **Powers of two** within any bound (memory-free: from `pow2Core_spec`). -/
theorem pow2Core_specB {S : ℕ} {P : Config → Prop} (hP : Indep [pE, pR, rT] P) (e : ℕ) :
    HTB S pow2Core (fun c => P c ∧ c.reg pE = e) (fun c => P c ∧ c.reg pR = 2 ^ e) (4 * e + 2) :=
  HTB.of_HT rfl (pow2Core_spec hP e)

/-! ### Public macros on naturals -/

theorem ne_of_not_mem_arithW {x r : ℕ} (hx : x ∉ arithW) (hr : r ∈ arithW) : x ≠ r :=
  fun h => hx (h ▸ hr)

/-- `d := reg x * reg y`. -/
def mulN (d x y : ℕ) : Stmt :=
  .seq (.seq (.const gA0 1) (.seq (mov gB0 x) (mov gL y))) (.seq gCore (mov d gAcc))

/-- Cost of `mulN` with multiplier `b`. -/
def mulCost (b : ℕ) : ℕ := 31 * Nat.size b + 22

/-- A bound on the free address is independent of every register list without `rFREE`. -/
theorem indep_free {W : List ℕ} (hW : rFREE ∉ W) (K S : ℕ) :
    Indep W (fun c => c.reg rFREE + K ≤ S) := Indep.reg hW (· + K ≤ S)

/-- **Multiplication within the bound, scratch bound in the precondition** (the master form of
`HTB.mulN`): `d := x * y` in `31 · size y + 22` steps, by a run accessing only the
addresses below `S`, the scratch table (`2 · size y` cells from `rFREE`) fitting below `S`. The
registers `x, y` lie outside the library's block (`d` may equal `x` or `y`); `P` must not mention
`d`, `rT`, `400–449`, and must give `ZeroFrom c.mem (c.reg rFREE)` (the table is zeroed again). -/
theorem HTB.mulN_pre {S : ℕ} {P : Config → Prop} {d x y a b : ℕ} (hx : x ∉ arithW)
    (hy : y ∉ arithW) (hP : Indep (d :: arithW) P) (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) :
    HTB S (Arith.mulN d x y)
      (fun c => (P c ∧ c.reg x = a ∧ c.reg y = b) ∧ c.reg rFREE + 2 * Nat.size b ≤ S)
      (fun c => P c ∧ c.reg d = a * b) (mulCost b) := by
  have hPg : Indep gW (fun c => P c ∧ c.reg rFREE + 2 * Nat.size b ≤ S) :=
    (hP.mono fun r hr => List.mem_cons_of_mem _ (mem_arithW_of_gW hr)).and
      (indep_free (by decide) _ _)
  have h1 : HTB S (.seq (.const gA0 1) (.seq (mov gB0 x) (mov gL y)))
      (fun c => (P c ∧ c.reg x = a ∧ c.reg y = b) ∧ c.reg rFREE + 2 * Nat.size b ≤ S)
      (fun c => (P c ∧ c.reg rFREE + 2 * Nat.size b ≤ S) ∧
        (c.reg gA0 = 1 ∧ c.reg gB0 = a ∧ c.reg gL = b ∧ 1 ≤ 1)) 5 :=
    HTB.of_HT rfl <| HT.run_le (by simp [LoopFree]) (by simp [size])
      fun c ⟨⟨hc, ha, hb⟩, hF⟩ => by
      have hxT := ne_of_not_mem_arithW hx (show rT ∈ arithW by decide)
      have hyT := ne_of_not_mem_arithW hy (show rT ∈ arithW by decide)
      have hx1 := ne_of_not_mem_arithW hx (show gA0 ∈ arithW by decide)
      have hy1 := ne_of_not_mem_arithW hy (show gA0 ∈ arithW by decide)
      have hy2 := ne_of_not_mem_arithW hy (show gB0 ∈ arithW by decide)
      refine ⟨?_, ?_, ?_, ?_, le_rfl⟩
      · simp only [run_seq', run_const, run_mov hxT, run_mov hyT]
        refine hPg.setReg (by decide) _ (hPg.setReg (by decide) _ (hPg.setReg (by decide) _
          (hPg.setReg (by decide) _ (hPg.setReg (by decide) _ ⟨hc, hF⟩))))
      all_goals simp +decide [run_mov hxT, run_mov hyT, hyT, hx1, hy1, hy2, ha, hb]
  have h3 : HTB S (mov d gAcc) (fun c => (P c ∧ c.reg rFREE + 2 * Nat.size b ≤ S) ∧
        (c.reg gAcc = a * (b / 1) ∧ c.reg gR = b % 1))
      (fun c => P c ∧ c.reg d = a * b) 2 :=
    HTB.of_HT rfl <| HT.run_le (by simp) (by simp) fun c ⟨⟨hc, _⟩, h1, _⟩ => by
      rw [run_mov (by decide)]
      exact ⟨hP.setReg List.mem_cons_self _ (hP.setReg (List.mem_cons_of_mem _ (by decide)) _ hc),
        by simp [h1]⟩
  have hent : entB 1 b = Nat.size b := by simp [entB, Nat.size_one]
  refine (h1.seq ((gCore_frameB hPg (fun c h => hZ c h.1) 1 a b
    (fun c h => by rw [hent]; exact h.2)).seq h3)).weaken ?_
  simp only [entB, Nat.size_one, Nat.add_sub_cancel, gCost, mulCost]
  omega

/-- **Multiplication within the bound**: `d := x * y` in `31 · size y + 22` steps, by a run
accessing only the addresses below `S`, provided the scratch table (`2 · size y` cells from
`rFREE`) fits below `S` (`hS`). Conditions as `HTB.mulN_pre`. -/
theorem HTB.mulN {S : ℕ} {P : Config → Prop} {d x y a b : ℕ} (hx : x ∉ arithW) (hy : y ∉ arithW)
    (hP : Indep (d :: arithW) P) (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE))
    (hS : ∀ c, P c → c.reg rFREE + 2 * Nat.size b ≤ S) :
    HTB S (Arith.mulN d x y) (fun c => P c ∧ c.reg x = a ∧ c.reg y = b)
      (fun c => P c ∧ c.reg d = a * b) (mulCost b) :=
  (HTB.mulN_pre hx hy hP hZ).pre fun c hc => ⟨hc, hS c hc.1⟩

/-- `q := reg x / reg y`, `r := reg x % reg y` (for `reg y ≥ 1`). -/
def divmodN (q r x y : ℕ) : Stmt :=
  .seq (.seq (.const gB0 1) (.seq (mov gA0 y) (mov gL x)))
    (.seq gCore (.seq (mov q gAcc) (mov r gR)))

/-- Cost of `divmodN` for `a / b`. -/
def divCost (a b : ℕ) : ℕ := 31 * (Nat.size a + 1 - Nat.size b) + 24

/-- **Division with remainder within the bound, scratch bound in the precondition** (the master
form of `HTB.divmodN`): `q := x / y`, `r := x % y` (`y ≥ 1`) in
`31 · (size x + 1 − size y) + 24` steps, the scratch table (`2 · (size x + 1 − size y)` cells from
`rFREE`) below `S`. `x, y, q` lie outside the library's block, `q ≠ r`; `P` must not mention `q`,
`r`, `rT`, `400–449` and must give `ZeroFrom c.mem (c.reg rFREE)`. -/
theorem HTB.divmodN_pre {S : ℕ} {P : Config → Prop} {q r x y a b : ℕ} (hx : x ∉ arithW)
    (hy : y ∉ arithW) (hq : q ∉ arithW) (hqr : q ≠ r) (hP : Indep (q :: r :: arithW) P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (hb : 1 ≤ b) :
    HTB S (Arith.divmodN q r x y)
      (fun c => (P c ∧ c.reg x = a ∧ c.reg y = b) ∧
        c.reg rFREE + 2 * (Nat.size a + 1 - Nat.size b) ≤ S)
      (fun c => P c ∧ c.reg q = a / b ∧ c.reg r = a % b) (divCost a b) := by
  have hPg : Indep gW (fun c => P c ∧ c.reg rFREE + 2 * (Nat.size a + 1 - Nat.size b) ≤ S) :=
    (hP.mono fun r hr =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_arithW_of_gW hr))).and
      (indep_free (by decide) _ _)
  have h1 : HTB S (.seq (.const gB0 1) (.seq (mov gA0 y) (mov gL x)))
      (fun c => (P c ∧ c.reg x = a ∧ c.reg y = b) ∧
        c.reg rFREE + 2 * (Nat.size a + 1 - Nat.size b) ≤ S)
      (fun c => (P c ∧ c.reg rFREE + 2 * (Nat.size a + 1 - Nat.size b) ≤ S) ∧
        (c.reg gA0 = b ∧ c.reg gB0 = 1 ∧ c.reg gL = a ∧ 1 ≤ b)) 5 :=
    HTB.of_HT rfl <| HT.run_le (by simp [LoopFree]) (by simp [size])
      fun c ⟨⟨hc, ha, hb'⟩, hF⟩ => by
      have hxT := ne_of_not_mem_arithW hx (show rT ∈ arithW by decide)
      have hyT := ne_of_not_mem_arithW hy (show rT ∈ arithW by decide)
      have hx1 := ne_of_not_mem_arithW hx (show gA0 ∈ arithW by decide)
      have hx2 := ne_of_not_mem_arithW hx (show gB0 ∈ arithW by decide)
      have hy2 := ne_of_not_mem_arithW hy (show gB0 ∈ arithW by decide)
      refine ⟨?_, ?_, ?_, ?_, hb⟩
      · simp only [run_seq', run_const, run_mov hxT, run_mov hyT]
        refine hPg.setReg (by decide) _ (hPg.setReg (by decide) _ (hPg.setReg (by decide) _
          (hPg.setReg (by decide) _ (hPg.setReg (by decide) _ ⟨hc, hF⟩))))
      all_goals simp +decide [run_mov hxT, run_mov hyT, hxT, hx1, hx2, hy2, ha, hb']
  have h3 : HTB S (.seq (mov q gAcc) (mov r gR))
      (fun c => (P c ∧ c.reg rFREE + 2 * (Nat.size a + 1 - Nat.size b) ≤ S) ∧
        (c.reg gAcc = 1 * (a / b) ∧ c.reg gR = a % b))
      (fun c => P c ∧ c.reg q = a / b ∧ c.reg r = a % b) 4 :=
    HTB.of_HT rfl <| HT.run_le (by simp [LoopFree]) (by simp [size]) fun c ⟨⟨hc, _⟩, h1, h2⟩ => by
      have hq1 := ne_of_not_mem_arithW hq (show gR ∈ arithW by decide)
      have hqT := ne_of_not_mem_arithW hq (show rT ∈ arithW by decide)
      simp only [run_seq', run_mov (show gAcc ≠ rT by decide), run_mov (show gR ≠ rT by decide)]
      refine ⟨?_, ?_, ?_⟩
      · refine hP.setReg (List.mem_cons_of_mem _ List.mem_cons_self) _ (hP.setReg
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by decide))) _ (hP.setReg
          List.mem_cons_self _ (hP.setReg
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by decide))) _ hc)))
      · simp [h1, hqr, hqT]
      · simp [h2, Ne.symm hq1]
  refine (h1.seq ((gCore_frameB hPg (fun c h => hZ c h.1) b 1 a (fun c h => h.2)).seq
    h3)).weaken ?_
  simp only [entB, gCost, divCost]
  omega

/-- **Division with remainder within the bound** (`hS`: the scratch table,
`2 · (size x + 1 − size y)` cells from `rFREE`, below `S`). Conditions as `HTB.divmodN_pre`. -/
theorem HTB.divmodN {S : ℕ} {P : Config → Prop} {q r x y a b : ℕ} (hx : x ∉ arithW)
    (hy : y ∉ arithW) (hq : q ∉ arithW) (hqr : q ≠ r) (hP : Indep (q :: r :: arithW) P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (hb : 1 ≤ b)
    (hS : ∀ c, P c → c.reg rFREE + 2 * (Nat.size a + 1 - Nat.size b) ≤ S) :
    HTB S (Arith.divmodN q r x y) (fun c => P c ∧ c.reg x = a ∧ c.reg y = b)
      (fun c => P c ∧ c.reg q = a / b ∧ c.reg r = a % b) (divCost a b) :=
  (HTB.divmodN_pre hx hy hq hqr hP hZ hb).pre fun c hc => ⟨hc, hS c hc.1⟩

/-- `d := 2 ^ reg e`. -/
def pow2N (d e : ℕ) : Stmt := .seq (mov pE e) (.seq pow2Core (mov d pR))

/-- **Powers of two** `d := 2 ^ e` in `4e + 6` steps (`e` outside the library's block; `P` must
not mention `d`, `rT`, `400–449`). -/
theorem HT.pow2N {P : Config → Prop} {d e k : ℕ} (he : e ∉ arithW) (hP : Indep (d :: arithW) P) :
    HT (Arith.pow2N d e) (fun c => P c ∧ c.reg e = k) (fun c => P c ∧ c.reg d = 2 ^ k)
      (4 * k + 6) := by
  have hP3 : Indep [pE, pR, rT] P := hP.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact List.mem_cons_of_mem _ (by decide)
  have heT := ne_of_not_mem_arithW he (show rT ∈ arithW by decide)
  have h1 : HT (mov pE e) (fun c => P c ∧ c.reg e = k) (fun c => P c ∧ c.reg pE = k) 2 :=
    HT.run_le (by simp) (by simp) fun c ⟨hc, hk⟩ => by
      rw [run_mov heT]
      exact ⟨hP3.setReg (by decide) _ (hP3.setReg (by decide) _ hc), by simp [hk]⟩
  have h3 : HT (mov d pR) (fun c => P c ∧ c.reg pR = 2 ^ k) (fun c => P c ∧ c.reg d = 2 ^ k) 2 :=
    HT.run_le (by simp) (by simp) fun c ⟨hc, hk⟩ => by
      rw [run_mov (by decide)]
      exact ⟨hP.setReg List.mem_cons_self _ (hP.setReg (List.mem_cons_of_mem _ (by decide)) _ hc),
        by simp [hk]⟩
  exact (h1.seq ((pow2Core_spec hP3 k).seq h3)).weaken (by omega)

/-- **Powers of two** within any bound (memory-free: from `HT.pow2N`). -/
theorem HTB.pow2N {S : ℕ} {P : Config → Prop} {d e k : ℕ} (he : e ∉ arithW)
    (hP : Indep (d :: arithW) P) :
    HTB S (Arith.pow2N d e) (fun c => P c ∧ c.reg e = k) (fun c => P c ∧ c.reg d = 2 ^ k)
      (4 * k + 6) :=
  HTB.of_HT rfl (HT.pow2N he hP)

end STACS2027.Runtimes.Arith
