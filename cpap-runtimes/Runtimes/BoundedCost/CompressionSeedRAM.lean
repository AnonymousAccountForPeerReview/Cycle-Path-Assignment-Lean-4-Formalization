module

public import Runtimes.BoundedCost.ArrayBlocks
public import Runtimes.BoundedCost.CompressionSetupRAM
public import Runtimes.BoundedCost.ContractionRAM
import Mathlib.Tactic

/-! A concrete ternary compression seed scan.  Each special occurrence is
independently deleted or forces one of its two literal codes. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

structure CompressionSeedRow where
  first : ℕ
  second : ℕ
  choice : ℕ
  deriving Inhabited

def seedSelected (row : CompressionSeedRow) (code : ℕ) : Bool :=
  (row.choice == 1 && row.first == code) || (row.choice == 2 && row.second == code)

def seedForcedValue (rows : List CompressionSeedRow) (count code : ℕ) : ℕ :=
  if (List.range count).any (fun i => seedSelected (rows.getD i default) code) then 1 else 0

def seedDeletedCount (rows : List CompressionSeedRow) (count : ℕ) : ℕ :=
  (List.range count).countP (fun i => (rows.getD i default).choice == 0)

theorem seedDeletedCount_succ (rows : List CompressionSeedRow) (i : ℕ) :
    seedDeletedCount rows (i + 1) = seedDeletedCount rows i +
      if (rows.getD i default).choice = 0 then 1 else 0 := by
  simp [seedDeletedCount, List.range_succ]

theorem seedForcedValue_succ (rows : List CompressionSeedRow) (i code : ℕ)
    (hchoice : (rows.getD i default).choice ≤ 2) :
    seedForcedValue rows (i + 1) code =
      if (rows.getD i default).choice = 0 then seedForcedValue rows i code else
        if code = (if (rows.getD i default).choice = 1 then
          (rows.getD i default).first else (rows.getD i default).second) then 1 else
            seedForcedValue rows i code := by
  have hor : (rows.getD i default).choice = 0 ∨ (rows.getD i default).choice = 1 ∨
      (rows.getD i default).choice = 2 := by omega
  unfold seedForcedValue
  rw [List.range_succ, List.any_append, List.any_cons, List.any_nil]
  simp only [Bool.or_false]
  rcases hor with h | h | h <;>
    cases ha : (List.range i).any (fun j => seedSelected (rows.getD j default) code) <;>
    by_cases hf : (rows.getD i default).first = code <;>
    by_cases hs : (rows.getD i default).second = code <;>
    simp +decide only [seedSelected, h, ha, hf, hs, Bool.beq_eq_decide_eq, beq_iff_eq, Bool.true_eq_false,
      Bool.false_eq_true, Bool.true_and, Bool.false_and, Bool.or_true, Bool.true_or,
      Bool.or_false, Bool.false_or, ↓reduceIte, decide_true, decide_false,
      show (code = (rows.getD i default).first) ↔ ((rows.getD i default).first = code) from eq_comm,
      show (code = (rows.getD i default).second) ↔ ((rows.getD i default).second = code) from eq_comm]

abbrev seedSpecialBase : ℕ := 430
abbrev seedSpecialCount : ℕ := 431
abbrev seedDeleted : ℕ := 432
abbrev seedDigitsBase : ℕ := 433
abbrev seedForcedBase : ℕ := 435
abbrev seedVariableCount : ℕ := 220
abbrev seedGlobalBudget : ℕ := 225
abbrev seedIndex : ℕ := 460
abbrev seedOffset : ℕ := 461
abbrev seedFirst : ℕ := 462
abbrev seedSecond : ℕ := 463
abbrev seedChoice : ℕ := 464
abbrev seedOne : ℕ := 465
abbrev seedTemporary : ℕ := 466

def compressionSeedBody : Stmt :=
  .seq (.add seedOffset seedIndex seedIndex)
    (.seq (ld seedFirst seedSpecialBase seedOffset)
      (.seq (inc seedOffset)
        (.seq (ld seedSecond seedSpecialBase seedOffset)
          (.seq (ld seedChoice seedDigitsBase seedIndex)
            (.seq (.const seedOne 1)
              (.ifz seedChoice (inc seedDeleted)
                (.seq (subc seedTemporary seedChoice 1)
                  (.ifz seedTemporary (st seedForcedBase seedFirst seedOne)
                    (st seedForcedBase seedSecond seedOne)))))))))

def compressionSeedScan : Stmt := .seq (.const seedDeleted 0)
  (forUp seedIndex seedSpecialCount compressionSeedBody)

@[mk_iff] structure CompressionSeedGlobals (special digits forced nodes budget count : ℕ)
    (c : Config) : Prop where
  special : c.reg seedSpecialBase = special
  digits : c.reg seedDigitsBase = digits
  forced : c.reg seedForcedBase = forced
  nodes : c.reg seedVariableCount = nodes
  budget : c.reg seedGlobalBudget = budget
  count : c.reg seedSpecialCount = count

def CompressionSeedRowsMem (special digits nodes : ℕ) (rows : List CompressionSeedRow)
    (memory : ℕ → ℕ) : Prop :=
  ∀ i, i < rows.length →
    let row := rows.getD i default
    row.first < 2 * nodes ∧ row.second < 2 * nodes ∧ row.choice ≤ 2 ∧
      memory (special + 2 * i) = row.first ∧ memory (special + 2 * i + 1) = row.second ∧
      memory (digits + i) = row.choice

def SeedScanInv (special digits forced nodes budget : ℕ) (rows : List CompressionSeedRow)
    (memory : ℕ → ℕ) (oldOutput : List ℕ) (count : ℕ) (c : Config) : Prop :=
  CompressionSeedGlobals special digits forced nodes budget rows.length c ∧
    Tab c.mem forced (2 * nodes) (seedForcedValue rows count) ∧
    SameOn (OutsideCells forced (2 * nodes)) memory c.mem ∧
    c.reg seedDeleted = seedDeletedCount rows count ∧ c.out = oldOutput

private theorem compressionSeedBody_run (special digits forced index deleted : ℕ)
    (row : CompressionSeedRow) (c : Config)
    (hs : c.reg seedSpecialBase = special) (hd : c.reg seedDigitsBase = digits)
    (hf : c.reg seedForcedBase = forced) (hi : c.reg seedIndex = index)
    (hc : c.reg seedDeleted = deleted)
    (hfirst : c.mem (special + 2 * index) = row.first)
    (hsecond : c.mem (special + 2 * index + 1) = row.second)
    (hchoice : c.mem (digits + index) = row.choice) (hbound : row.choice ≤ 2) :
    (run compressionSeedBody c).mem =
      (if row.choice = 0 then c.mem else
        upd c.mem (forced + if row.choice = 1 then row.first else row.second) 1) ∧
      (run compressionSeedBody c).reg seedDeleted =
        deleted + if row.choice = 0 then 1 else 0 := by
  have hfirst' : c.mem (special + (index + index)) = row.first := by
    simpa [show index + index = 2 * index by omega] using hfirst
  have hsecond' : c.mem (special + (index + (index + 1))) = row.second := by
    simpa only [show 2 * index + 1 = index + (index + 1) by omega, Nat.add_assoc] using hsecond
  have hor : row.choice = 0 ∨ row.choice = 1 ∨ row.choice = 2 := by omega
  rcases hor with h | h | h <;>
    simp +decide [compressionSeedBody, ld, st, inc, addc, subc, hs, hd, hf, hi, hc,
      hfirst', hsecond', hchoice, h, Nat.add_assoc]

theorem compressionSeedBody_spec {S special digits forced nodes budget : ℕ}
    {rows : List CompressionSeedRow} {memory : ℕ → ℕ} {oldOutput : List ℕ}
    (hmem : CompressionSeedRowsMem special digits nodes rows memory)
    (hspecial : DisjointCells forced (2 * nodes) special (2 * rows.length))
    (hdigits : DisjointCells forced (2 * nodes) digits rows.length)
    (hS : special + 2 * rows.length ≤ S ∧ digits + rows.length ≤ S ∧ forced + 2 * nodes ≤ S)
    (i : ℕ) (hi : i < rows.length) :
    HTB S compressionSeedBody
      (fun c => SeedScanInv special digits forced nodes budget rows memory oldOutput i c ∧
        c.reg seedIndex = i ∧ c.reg seedSpecialCount = rows.length)
      (fun c => SeedScanInv special digits forced nodes budget rows memory oldOutput (i + 1) c ∧
        c.reg seedIndex = i ∧ c.reg seedSpecialCount = rows.length) 40 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hg, htable, hsame, hdeleted, hout⟩, hindex, hcount⟩
  let row := rows.getD i default
  obtain ⟨hfb, hsb, hcb, hfirst, hsecond, hchoice⟩ := hmem i hi
  change row.first < 2 * nodes at hfb
  change row.second < 2 * nodes at hsb
  change row.choice ≤ 2 at hcb
  have hfirst' : c.mem (special + 2 * i) = row.first := by
    rw [hsame _ (hspecial.outside (by omega))]
    exact hfirst
  have hsecond' : c.mem (special + 2 * i + 1) = row.second := by
    rw [hsame _ (hspecial.outside (by omega))]
    exact hsecond
  have hchoice' : c.mem (digits + i) = row.choice := by
    rw [hsame _ (hdigits.outside (by omega))]
    exact hchoice
  obtain ⟨hrun, hnumber⟩ := compressionSeedBody_run special digits forced i
    (seedDeletedCount rows i) row c hg.special hg.digits hg.forced hindex hdeleted
    hfirst' hsecond' hchoice' hcb
  have hg' : CompressionSeedGlobals special digits forced nodes budget rows.length
      (run compressionSeedBody c) := by
    have h : RegIndep (wregs compressionSeedBody)
        (CompressionSeedGlobals special digits forced nodes budget rows.length) := by
      indep [compressionSeedGlobals_iff, compressionSeedBody, ld, st, inc, addc, subc]
    exact h.run (by decide) hg
  have hindex' : (run compressionSeedBody c).reg seedIndex = i := by
    exact (run_reg_of_not_mem (by decide) (by decide) c).trans hindex
  have hout' : (run compressionSeedBody c).out = oldOutput := by
    exact (run_out_of_writes (by decide) (by decide) c).trans hout
  refine ⟨?_, ⟨⟨hg', ?_, ?_, ?_, hout'⟩, hindex', hg'.count⟩⟩
  · have hfirstAdd : c.mem (special + (i + i)) = row.first := by
      simpa [show i + i = 2 * i by omega] using hfirst'
    have hsecondAdd : c.mem (special + (i + (i + 1))) = row.second := by
      simpa only [show 2 * i + 1 = i + (i + 1) by omega, Nat.add_assoc] using hsecond'
    have hor : row.choice = 0 ∨ row.choice = 1 ∨ row.choice = 2 := by omega
    rcases hg with ⟨hs, hd, hf, hn, hb, hm⟩
    rcases hor with h | h | h <;>
      addr_ok [compressionSeedBody, ld, st, inc, addc, subc, hindex, hs, hd, hf,
        hfirstAdd, hsecondAdd, hchoice', h, Nat.add_assoc]
  · intro code hcode
    rw [hrun, seedForcedValue_succ rows i code hcb]
    change (if row.choice = 0 then c.mem else
      upd c.mem (forced + if row.choice = 1 then row.first else row.second) 1) (forced + code) =
      if row.choice = 0 then seedForcedValue rows i code else
        if code = (if row.choice = 1 then row.first else row.second) then 1 else seedForcedValue rows i code
    by_cases hzero : row.choice = 0
    · simp only [if_pos hzero]
      exact htable code hcode
    · simp only [if_neg hzero, upd_apply]
      by_cases he : code = if row.choice = 1 then row.first else row.second
      · simp [he]
      · have ha : forced + code ≠ forced + (if row.choice = 1 then row.first else row.second) := by omega
        simp only [if_neg he, if_neg ha]
        exact htable code hcode
  · intro a ha
    rw [hrun]
    by_cases hz : row.choice = 0
    · simpa only [if_pos hz] using hsame a ha
    · rw [if_neg hz, upd_apply, if_neg (by
        unfold OutsideCells at ha
        split_ifs <;> omega)]
      exact hsame a ha
  · rw [hnumber, seedDeletedCount_succ]

theorem compressionSeedScan_spec {S special digits forced nodes budget : ℕ}
    {rows : List CompressionSeedRow} {memory : ℕ → ℕ} {oldOutput : List ℕ}
    (hmem : CompressionSeedRowsMem special digits nodes rows memory)
    (hspecial : DisjointCells forced (2 * nodes) special (2 * rows.length))
    (hdigits : DisjointCells forced (2 * nodes) digits rows.length)
    (hzero : Tab memory forced (2 * nodes) (fun _ => 0))
    (hS : special + 2 * rows.length ≤ S ∧ digits + rows.length ≤ S ∧ forced + 2 * nodes ≤ S) :
    HTB S compressionSeedScan
      (fun c => CompressionSeedGlobals special digits forced nodes budget rows.length c ∧
        c.mem = memory ∧ c.out = oldOutput)
      (SeedScanInv special digits forced nodes budget rows memory oldOutput rows.length)
      (44 * rows.length + 4) := by
  let Inv := SeedScanInv special digits forced nodes budget rows memory oldOutput
  have hinit : HTB S (.const seedDeleted 0)
      (fun c => CompressionSeedGlobals special digits forced nodes budget rows.length c ∧
        c.mem = memory ∧ c.out = oldOutput)
      (fun c => Inv 0 c ∧ c.reg seedSpecialCount = rows.length) 1 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨hg, hm, ho⟩
    have hg' : CompressionSeedGlobals special digits forced nodes budget rows.length
        (run (.const seedDeleted 0) c) := by
      have h : RegIndep [seedDeleted]
          (CompressionSeedGlobals special digits forced nodes budget rows.length) := by
        indep [compressionSeedGlobals_iff]
      exact h.run_of_sub (by decide) (by simp [wregs]) hg
    refine ⟨AddrOK.of_memFree rfl, ⟨hg', ?_, ?_, ?_, ?_⟩, hg'.count⟩
    · intro code hcode
      simpa only [run, setReg_mem, hm, seedForcedValue, List.range_zero, List.any_nil,
        Bool.false_eq_true, ↓reduceIte] using hzero code hcode
    · intro a ha; simpa using congrFun hm a
    · simp +decide [seedDeletedCount]
    · simpa using ho
  have hl := HTB.forUpC (S := S) (i := seedIndex) (n := seedSpecialCount)
    (N := rows.length) (body := compressionSeedBody) Inv 40
    (by decide) (by decide) (by decide)
    (fun j => by indep [Inv, SeedScanInv, compressionSeedGlobals_iff])
    (fun j hj => compressionSeedBody_spec hmem hspecial hdigits hS j hj)
  exact (hinit.seq hl |>.post (fun c hc => hc.1)).weaken (by omega)

def compressionSeedClearReady : Stmt :=
  .seq (mov ArrayBlocks.targetBase seedForcedBase)
    (.seq (.add ArrayBlocks.arrayLength seedVariableCount seedVariableCount)
      (.const ArrayBlocks.fillValue 0))

def compressionSeedClear : Stmt := .seq compressionSeedClearReady ArrayBlocks.fillArray

def compressionSeedSetup : Stmt := .seq compressionSeedClear compressionSeedScan

theorem compressionSeedClear_spec {S special digits forced nodes budget count : ℕ}
    {memory : ℕ → ℕ} {oldOutput : List ℕ} (hS : forced + 2 * nodes ≤ S) :
    HTB S compressionSeedClear
      (fun c => CompressionSeedGlobals special digits forced nodes budget count c ∧
        c.mem = memory ∧ c.out = oldOutput)
      (fun c => CompressionSeedGlobals special digits forced nodes budget count c ∧
        c.mem = ArrayBlocks.prefixMemory memory forced (List.replicate (2 * nodes) 0) (2 * nodes) ∧
        c.out = oldOutput)
      (12 * nodes + 7) := by
  let Fr := CompressionSeedGlobals special digits forced nodes budget count
  have hready : HTB S compressionSeedClearReady
      (fun c => Fr c ∧ c.mem = memory ∧ c.out = oldOutput)
      (fun c => (ArrayBlocks.FillGlobals forced (2 * nodes) 0 c ∧
        c.mem = memory ∧ c.out = oldOutput) ∧ Fr c) 4 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨hg, hm, ho⟩
    have hg' : Fr (run compressionSeedClearReady c) := by
      have h : RegIndep (wregs compressionSeedClearReady) Fr := by
        indep [Fr, compressionSeedGlobals_iff, compressionSeedClearReady, mov]
      exact h.run (by decide) hg
    refine ⟨AddrOK.of_memFree (by decide), ?_, hg'⟩
    simp +decide [compressionSeedClearReady, mov, ArrayBlocks.FillGlobals, hg.forced, hg.nodes, hm, ho,
      show nodes + nodes = 2 * nodes by omega]
  have hfill := (ArrayBlocks.fillArray_spec (memory := memory) (out := oldOutput)
      (target := forced) (length := 2 * nodes) (fill := 0) hS).frameReg
    (F := Fr) (by indep [Fr, compressionSeedGlobals_iff, ArrayBlocks.fillArray,
      ArrayBlocks.fillBody, forUp, upLoop, wregs, st, inc, addc])
  exact (hready.seq hfill |>.post (fun c hc => ⟨hc.2, hc.1.2.1, hc.1.2.2⟩)).weaken (by omega)

theorem compressionSeedSetup_spec {S special digits forced nodes budget : ℕ}
    {rows : List CompressionSeedRow} {memory : ℕ → ℕ} {oldOutput : List ℕ}
    (hmem : CompressionSeedRowsMem special digits nodes rows memory)
    (hspecial : DisjointCells forced (2 * nodes) special (2 * rows.length))
    (hdigits : DisjointCells forced (2 * nodes) digits rows.length)
    (hS : special + 2 * rows.length ≤ S ∧ digits + rows.length ≤ S ∧ forced + 2 * nodes ≤ S) :
    HTB S compressionSeedSetup
      (fun c => CompressionSeedGlobals special digits forced nodes budget rows.length c ∧
        c.mem = memory ∧ c.out = oldOutput)
      (SeedScanInv special digits forced nodes budget rows memory oldOutput rows.length)
      (12 * nodes + 44 * rows.length + 11) := by
  let cleared := ArrayBlocks.prefixMemory memory forced (List.replicate (2 * nodes) 0) (2 * nodes)
  have hmem' : CompressionSeedRowsMem special digits nodes rows cleared := by
    intro i hi
    obtain ⟨hfb, hsb, hcb, hf, hs, hd⟩ := hmem i hi
    refine ⟨hfb, hsb, hcb, ?_, ?_, ?_⟩
    · dsimp only [cleared]
      rw [ArrayBlocks.prefixMemory_outside (hspecial.outside (by omega))]
      exact hf
    · dsimp only [cleared]
      rw [ArrayBlocks.prefixMemory_outside (hspecial.outside (by omega))]
      exact hs
    · dsimp only [cleared]
      rw [ArrayBlocks.prefixMemory_outside (hdigits.outside (by omega))]
      exact hd
  have hz : Tab cleared forced (2 * nodes) (fun _ => 0) := by
    intro code hcode
    dsimp only [cleared]
    rw [ArrayBlocks.prefixMemory, ite_eq_left (by omega), Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, hcode]
  have hclear := compressionSeedClear_spec (special := special) (digits := digits)
    (budget := budget) (count := rows.length) (memory := memory) (oldOutput := oldOutput) hS.2.2
  have hscan := compressionSeedScan_spec (budget := budget) (oldOutput := oldOutput)
    hmem' hspecial hdigits hz hS
  refine (hclear.seq hscan |>.post ?_).weaken (by omega)
  rintro c ⟨hg, ht, hs, hd, ho⟩
  refine ⟨hg, ht, ?_, hd, ho⟩
  intro a ha
  exact (hs a ha).trans (ArrayBlocks.prefixMemory_outside ha)

end STACS2027.Runtimes.BoundedCost
