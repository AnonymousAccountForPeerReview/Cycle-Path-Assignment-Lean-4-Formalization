module

public import Runtimes.BoundedCost.ContractionData
public import Outerplanar.RAM.Layout
import Mathlib.Tactic

/-! The RAM compression setup scans the original occurrence positions.  It
marks the reference-true processed clauses active and packs the reference-false
processed clauses in their original order. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

structure CompressionSetupRow where
  first : ℕ
  second : ℕ
  firstTruth : Bool
  secondTruth : Bool
  deriving Inhabited

def setupRowTrue (row : CompressionSetupRow) : Bool := row.firstTruth || row.secondTruth

def setupActiveValue (rows : List CompressionSetupRow) (processed i : ℕ) : ℕ :=
  if i < processed ∧ setupRowTrue (rows.getD i default) = true then 1 else 0

def setupSpecialPrefix (rows : List CompressionSetupRow) (processed count : ℕ) : List (ℕ × ℕ) :=
  (List.range count).filterMap fun i =>
    if i < processed ∧ setupRowTrue (rows.getD i default) = false then
      some ((rows.getD i default).first, (rows.getD i default).second) else none

theorem setupSpecialPrefix_succ (rows : List CompressionSetupRow) (processed i : ℕ) :
    setupSpecialPrefix rows processed (i + 1) = setupSpecialPrefix rows processed i ++
      if i < processed ∧ setupRowTrue (rows.getD i default) = false then
        [((rows.getD i default).first, (rows.getD i default).second)] else [] := by
  simp [setupSpecialPrefix, List.range_succ]
  split <;> simp_all

theorem setupSpecialPrefix_length_le (rows : List CompressionSetupRow) (processed i : ℕ) :
    (setupSpecialPrefix rows processed i).length ≤ i := by
  exact (List.length_filterMap_le _ _).trans (by simp)

abbrev setupSpecialBase : ℕ := 430
abbrev setupSpecialCount : ℕ := 431
abbrev setupBaseSnapshot : ℕ := 434
abbrev setupIndex : ℕ := 440
abbrev setupOffset : ℕ := 441
abbrev setupFirst : ℕ := 442
abbrev setupSecond : ℕ := 443
abbrev setupFirstTruth : ℕ := 444
abbrev setupSecondTruth : ℕ := 445
abbrev setupActive : ℕ := 446
abbrev setupTemporary : ℕ := 447
abbrev setupFormulaBase : ℕ := 200
abbrev setupClauseCount : ℕ := 201
abbrev setupActiveBase : ℕ := 202
abbrev setupCandidateBase : ℕ := 203
abbrev setupPrefixCount : ℕ := 224

def setupPackFalse : Stmt :=
  .seq (.add setupOffset setupSpecialCount setupSpecialCount)
    (.seq (st setupSpecialBase setupOffset setupFirst)
      (.seq (inc setupOffset)
        (.seq (st setupSpecialBase setupOffset setupSecond) (inc setupSpecialCount))))

def setupReadClause : Stmt :=
  .seq (.add setupOffset setupIndex setupIndex)
    (.seq (ld setupFirst setupFormulaBase setupOffset)
      (.seq (inc setupOffset)
        (.seq (ld setupSecond setupFormulaBase setupOffset)
          (.seq (ld setupFirstTruth setupCandidateBase setupFirst)
            (.seq (ld setupSecondTruth setupCandidateBase setupSecond)
              (.ifz setupFirstTruth
                (.ifz setupSecondTruth setupPackFalse (.const setupActive 1))
                (.const setupActive 1)))))))

def compressionSetupBody : Stmt :=
  .seq (.const setupActive 0)
    (.seq (.sub setupTemporary setupPrefixCount setupIndex)
      (.seq (.ifz setupTemporary .skip setupReadClause)
        (.seq (st setupActiveBase setupIndex setupActive)
          (st setupBaseSnapshot setupIndex setupActive))))

def compressionSetupScan : Stmt := .seq (.const setupSpecialCount 0)
  (forUp setupIndex setupClauseCount compressionSetupBody)

@[mk_iff] structure CompressionSetupGlobals (formula active candidate special snapshot processed clauses : ℕ)
    (c : Config) : Prop where
  formula : c.reg setupFormulaBase = formula
  active : c.reg setupActiveBase = active
  candidate : c.reg setupCandidateBase = candidate
  special : c.reg setupSpecialBase = special
  snapshot : c.reg setupBaseSnapshot = snapshot
  processed : c.reg setupPrefixCount = processed
  clauses : c.reg setupClauseCount = clauses

def CompressionSetupRowsMem (formula candidate nodes : ℕ) (rows : List CompressionSetupRow)
    (memory : ℕ → ℕ) : Prop :=
  ∀ i, i < rows.length →
    let row := rows.getD i default
    row.first < 2 * nodes ∧ row.second < 2 * nodes ∧
      memory (formula + 2 * i) = row.first ∧ memory (formula + 2 * i + 1) = row.second ∧
      memory (candidate + row.first) = (if row.firstTruth then 1 else 0) ∧
      memory (candidate + row.second) = (if row.secondTruth then 1 else 0)

def setupOutside (active snapshot special count packed a : ℕ) : Prop :=
  (a < active ∨ active + count ≤ a) ∧
    (a < snapshot ∨ snapshot + count ≤ a) ∧
      (a < special ∨ special + 2 * packed ≤ a)

def SetupScanInv (formula active candidate special snapshot processed : ℕ)
    (rows : List CompressionSetupRow) (memory : ℕ → ℕ) (oldOutput : List ℕ)
    (count : ℕ) (c : Config) : Prop :=
  CompressionSetupGlobals formula active candidate special snapshot processed rows.length c ∧
  Tab c.mem active count (setupActiveValue rows processed) ∧
  Tab c.mem snapshot count (setupActiveValue rows processed) ∧
  Arr c.mem special (contractionArcCodes (setupSpecialPrefix rows processed count)) ∧
  SameOn (setupOutside active snapshot special rows.length rows.length)
    memory c.mem ∧
  c.reg setupSpecialCount = (setupSpecialPrefix rows processed count).length ∧ c.out = oldOutput

private def setupStepMemory (memory : ℕ → ℕ) (active special snapshot processed index count : ℕ)
    (row : CompressionSetupRow) : ℕ → ℕ :=
  let packed := if index < processed ∧ setupRowTrue row = false then
    upd (upd memory (special + 2 * count) row.first) (special + 2 * count + 1) row.second
    else memory
  let value := if index < processed ∧ setupRowTrue row = true then 1 else 0
  upd (upd packed (active + index) value) (snapshot + index) value

private theorem compressionSetupBody_run (formula active candidate special snapshot processed index count : ℕ)
    (row : CompressionSetupRow) (c : Config)
    (hf : c.reg setupFormulaBase = formula) (ha : c.reg setupActiveBase = active)
    (ht : c.reg setupCandidateBase = candidate) (hs : c.reg setupSpecialBase = special)
    (hb : c.reg setupBaseSnapshot = snapshot) (hp : c.reg setupPrefixCount = processed)
    (hi : c.reg setupIndex = index) (hc : c.reg setupSpecialCount = count)
    (hfirst : c.mem (formula + 2 * index) = row.first)
    (hsecond : c.mem (formula + 2 * index + 1) = row.second)
    (hfirstTruth : c.mem (candidate + row.first) = if row.firstTruth then 1 else 0)
    (hsecondTruth : c.mem (candidate + row.second) = if row.secondTruth then 1 else 0) :
    (run compressionSetupBody c).mem = setupStepMemory c.mem active special snapshot processed index count row ∧
      (run compressionSetupBody c).reg setupSpecialCount =
        count + if index < processed ∧ setupRowTrue row = false then 1 else 0 := by
  have hfirst' : c.mem (formula + (index + index)) = row.first := by
    simpa [show index + index = 2 * index by omega] using hfirst
  have hsecond' : c.mem (formula + (index + (index + 1))) = row.second := by
    simpa only [show 2 * index + 1 = index + (index + 1) by omega, Nat.add_assoc] using hsecond
  by_cases hindex : index < processed
  · have hsub : processed - index ≠ 0 := by omega
    cases hft : row.firstTruth <;> cases hst : row.secondTruth <;>
      simp +decide [compressionSetupBody, setupReadClause, setupPackFalse, setupStepMemory,
        setupRowTrue, ld, st, inc, addc, hf, ha, ht, hs, hb, hp, hi, hc, hfirst', hsecond',
        hfirstTruth, hsecondTruth, hindex, hsub, hft, hst, two_mul, Nat.add_assoc]
  · have hsub : processed - index = 0 := by omega
    simp +decide [compressionSetupBody, setupStepMemory, st, ha, hb, hp, hi, hc, hindex, hsub]

private theorem setupStepMemory_preserve (memory : ℕ → ℕ) (active special snapshot processed index count a : ℕ)
    (row : CompressionSetupRow)
    (hne : a ≠ active + index ∧ a ≠ snapshot + index ∧
      a ≠ special + 2 * count ∧ a ≠ special + 2 * count + 1) :
    setupStepMemory memory active special snapshot processed index count row a = memory a := by
  simp [setupStepMemory, upd_apply, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2]
  split <;> simp_all [upd_apply]

private theorem setupStepMemory_active (memory : ℕ → ℕ) (active special snapshot processed index count : ℕ)
    (row : CompressionSetupRow) (hne : active + index ≠ snapshot + index) :
    setupStepMemory memory active special snapshot processed index count row (active + index) =
      if index < processed ∧ setupRowTrue row = true then 1 else 0 := by
  simp [setupStepMemory, upd_apply, hne]

private theorem setupStepMemory_snapshot (memory : ℕ → ℕ) (active special snapshot processed index count : ℕ)
    (row : CompressionSetupRow) :
    setupStepMemory memory active special snapshot processed index count row (snapshot + index) =
      if index < processed ∧ setupRowTrue row = true then 1 else 0 := by
  simp [setupStepMemory, upd_apply]

theorem compressionSetupBody_spec {S formula active candidate special snapshot processed nodes : ℕ}
    {rows : List CompressionSetupRow} {memory : ℕ → ℕ} {oldOutput : List ℕ}
    (hmem : CompressionSetupRowsMem formula candidate nodes rows memory)
    (has : active + rows.length ≤ snapshot ∨ snapshot + rows.length ≤ active)
    (hap : active + rows.length ≤ special ∨ special + 2 * rows.length ≤ active)
    (hsp : snapshot + rows.length ≤ special ∨ special + 2 * rows.length ≤ snapshot)
    (hinput : ∀ a, (formula ≤ a ∧ a < formula + 2 * rows.length) ∨
      (candidate ≤ a ∧ a < candidate + 2 * nodes) →
        setupOutside active snapshot special rows.length rows.length a)
    (hS : formula + 2 * rows.length ≤ S ∧ candidate + 2 * nodes ≤ S ∧
      active + rows.length ≤ S ∧ snapshot + rows.length ≤ S ∧ special + 2 * rows.length ≤ S)
    (i : ℕ) (hi : i < rows.length) :
    HTB S compressionSetupBody
      (fun c => SetupScanInv formula active candidate special snapshot processed rows memory oldOutput i c ∧
        c.reg setupIndex = i ∧ c.reg setupClauseCount = rows.length)
      (fun c => SetupScanInv formula active candidate special snapshot processed rows memory oldOutput (i + 1) c ∧
        c.reg setupIndex = i ∧ c.reg setupClauseCount = rows.length) 80 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hg, hactive, hsnapshot, hpacked, hsame, hcount, hout⟩, hindex, _⟩
  let row := rows.getD i default
  let packed := setupSpecialPrefix rows processed i
  change Arr c.mem special (contractionArcCodes packed) at hpacked
  change c.reg setupSpecialCount = packed.length at hcount
  have hlen : packed.length ≤ i := setupSpecialPrefix_length_le rows processed i
  obtain ⟨hfirstBound, hsecondBound, hfirst, hsecond, hfirstTruth, hsecondTruth⟩ := hmem i hi
  change row.first < 2 * nodes at hfirstBound
  change row.second < 2 * nodes at hsecondBound
  have hfirst' : c.mem (formula + 2 * i) = row.first :=
    (hsame _ (hinput _ (Or.inl (by omega)))).trans hfirst
  have hsecond' : c.mem (formula + 2 * i + 1) = row.second :=
    (hsame _ (hinput _ (Or.inl (by omega)))).trans hsecond
  have hfirstTruth' : c.mem (candidate + row.first) = if row.firstTruth then 1 else 0 :=
    (hsame _ (hinput _ (Or.inr (by omega)))).trans hfirstTruth
  have hsecondTruth' : c.mem (candidate + row.second) = if row.secondTruth then 1 else 0 :=
    (hsame _ (hinput _ (Or.inr (by omega)))).trans hsecondTruth
  have hfirstAdd : c.mem (formula + (i + i)) = row.first := by
    simpa only [show i + i = 2 * i by omega] using hfirst'
  have hsecondAdd : c.mem (formula + (i + i + 1)) = row.second := by
    simpa only [show i + i = 2 * i by omega, Nat.add_assoc] using hsecond'
  obtain ⟨hrun, hnumber⟩ := compressionSetupBody_run formula active candidate special snapshot processed i
    packed.length row c hg.formula hg.active hg.candidate hg.special hg.snapshot hg.processed hindex
    hcount hfirst' hsecond' hfirstTruth' hsecondTruth'
  have hg' : CompressionSetupGlobals formula active candidate special snapshot processed rows.length
      (run compressionSetupBody c) := by
    have h : RegIndep (wregs compressionSetupBody)
        (CompressionSetupGlobals formula active candidate special snapshot processed rows.length) := by
      indep [compressionSetupGlobals_iff, compressionSetupBody, setupReadClause, setupPackFalse]
    exact h.run (by decide) hg
  have hi' : (run compressionSetupBody c).reg setupIndex = i :=
    (run_reg_of_not_mem (by decide) (by decide) c).trans hindex
  have hout' : (run compressionSetupBody c).out = oldOutput :=
    (run_out_of_writes (by decide) (by decide) c).trans hout
  have hpcode : (contractionArcCodes packed).length = 2 * packed.length := by
    simp [contractionArcCodes, List.length_flatMap, Function.comp_def, Nat.mul_comm]
  refine ⟨?_, ⟨hg', ?_, ?_, ?_, ?_, ?_, hout'⟩, hi', hg'.clauses⟩
  · rcases hg with ⟨hf, ha, ht, hs, hb, hp, hn⟩
    have hs' : c.reg setupSpecialCount = packed.length := hcount
    by_cases hit : i < processed
    · have hz : processed - i ≠ 0 := by omega
      cases hft : row.firstTruth <;> cases hst : row.secondTruth <;>
        addr_ok [compressionSetupBody, setupReadClause, setupPackFalse, ld, st, inc, addc,
          hindex, hf, ha, ht, hs, hb, hp, hn, hs', hfirstAdd, hsecondAdd, hfirstTruth', hsecondTruth', hz, hft, hst]
    · have hz : processed - i = 0 := by omega
      cases hft : row.firstTruth <;> cases hst : row.secondTruth <;>
        addr_ok [compressionSetupBody, setupReadClause, setupPackFalse, ld, st, inc, addc,
          hindex, hf, ha, ht, hs, hb, hp, hn, hs', hfirstAdd, hsecondAdd, hfirstTruth', hsecondTruth', hz, hft, hst]
  · intro j hj
    rw [hrun]
    by_cases hjold : j < i
    · rw [setupStepMemory_preserve c.mem active special snapshot processed i packed.length
        (active + j) row (by rcases has with h | h <;> rcases hap with h | h <;> omega)]
      exact hactive j hjold
    · have he : j = i := by omega
      subst j
      rw [setupStepMemory_active c.mem active special snapshot processed i packed.length row
        (by rcases has with h | h <;> omega)]
      rfl
  · intro j hj
    rw [hrun]
    by_cases hjold : j < i
    · rw [setupStepMemory_preserve c.mem active special snapshot processed i packed.length
        (snapshot + j) row (by rcases has with h | h <;> rcases hsp with h | h <;> omega)]
      exact hsnapshot j hjold
    · have he : j = i := by omega
      subst j
      rw [setupStepMemory_snapshot]
      rfl
  · rw [hrun]
    by_cases hp : i < processed ∧ setupRowTrue (rows.getD i default) = false
    · have hnew : contractionArcCodes (packed ++ [(row.first, row.second)]) =
          contractionArcCodes packed ++ [row.first, row.second] := by simp [contractionArcCodes]
      have hnext : setupSpecialPrefix rows processed (i + 1) = packed ++ [(row.first, row.second)] := by
        rw [setupSpecialPrefix_succ, ite_eq_left hp]
      rw [hnext, hnew]
      have hstep : setupStepMemory c.mem active special snapshot processed i packed.length row =
          upd (upd (upd (upd c.mem (special + 2 * packed.length) row.first)
            (special + 2 * packed.length + 1) row.second)
            (active + i) (setupActiveValue rows processed i))
            (snapshot + i) (setupActiveValue rows processed i) := by
        unfold setupStepMemory
        rw [ite_eq_left hp]
        rfl
      rw [hstep]
      have hpack := hpacked.upd_snoc (a := special + 2 * packed.length) (x := row.first) (by omega)
      have hpack' := hpack.upd_snoc (a := special + 2 * packed.length + 1) (x := row.second) (by
        simp only [List.length_append, List.length_singleton, hpcode]; omega)
      have ha := hpack'.upd_of_disjoint (a := active + i) (v := setupActiveValue rows processed i)
        (by rcases hap with h | h <;> simp only [List.length_append, List.length_singleton, hpcode] <;> omega)
      have hb := ha.upd_of_disjoint (a := snapshot + i) (v := setupActiveValue rows processed i)
        (by rcases hsp with h | h <;> simp only [List.length_append, List.length_singleton, hpcode] <;> omega)
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hb
    · have ha := hpacked.upd_of_disjoint (a := active + i) (v := setupActiveValue rows processed i)
        (by rcases hap with h | h <;> omega)
      have hb := ha.upd_of_disjoint (a := snapshot + i) (v := setupActiveValue rows processed i)
        (by rcases hsp with h | h <;> omega)
      have hnext : setupSpecialPrefix rows processed (i + 1) = packed := by
        rw [setupSpecialPrefix_succ, ite_eq_right hp, List.append_nil]
      have hstep : setupStepMemory c.mem active special snapshot processed i packed.length row =
          upd (upd c.mem (active + i) (setupActiveValue rows processed i))
            (snapshot + i) (setupActiveValue rows processed i) := by
        unfold setupStepMemory
        rw [ite_eq_right hp]
        rfl
      rw [hnext, hstep]
      exact hb
  · intro a ha
    rw [hrun, setupStepMemory_preserve c.mem active special snapshot processed i packed.length a row
      (by unfold setupOutside at ha; omega)]
    exact hsame a ha
  · rw [hnumber, setupSpecialPrefix_succ]
    change packed.length + (if i < processed ∧ setupRowTrue row = false then 1 else 0) =
      (packed ++ if i < processed ∧ setupRowTrue row = false then [(row.first, row.second)] else []).length
    split_ifs <;> simp

theorem compressionSetupScan_spec {S formula active candidate special snapshot processed nodes : ℕ}
    {rows : List CompressionSetupRow} {memory : ℕ → ℕ} {oldOutput : List ℕ}
    (hmem : CompressionSetupRowsMem formula candidate nodes rows memory)
    (has : active + rows.length ≤ snapshot ∨ snapshot + rows.length ≤ active)
    (hap : active + rows.length ≤ special ∨ special + 2 * rows.length ≤ active)
    (hsp : snapshot + rows.length ≤ special ∨ special + 2 * rows.length ≤ snapshot)
    (hinput : ∀ a, (formula ≤ a ∧ a < formula + 2 * rows.length) ∨
      (candidate ≤ a ∧ a < candidate + 2 * nodes) →
      setupOutside active snapshot special rows.length rows.length a)
    (hS : formula + 2 * rows.length ≤ S ∧ candidate + 2 * nodes ≤ S ∧
      active + rows.length ≤ S ∧ snapshot + rows.length ≤ S ∧ special + 2 * rows.length ≤ S) :
    HTB S compressionSetupScan
      (fun c => CompressionSetupGlobals formula active candidate special snapshot processed rows.length c ∧
        c.mem = memory ∧ c.out = oldOutput)
      (SetupScanInv formula active candidate special snapshot processed rows memory oldOutput rows.length)
      (84 * rows.length + 4) := by
  let Inv := SetupScanInv formula active candidate special snapshot processed rows memory oldOutput
  have hinit : HTB S (.const setupSpecialCount 0)
      (fun c => CompressionSetupGlobals formula active candidate special snapshot processed rows.length c ∧
        c.mem = memory ∧ c.out = oldOutput)
      (fun c => Inv 0 c ∧ c.reg setupClauseCount = rows.length) 1 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨hg, hm, ho⟩
    have hg' : CompressionSetupGlobals formula active candidate special snapshot processed rows.length
        (run (.const setupSpecialCount 0) c) := by
      have h : RegIndep [setupSpecialCount]
          (CompressionSetupGlobals formula active candidate special snapshot processed rows.length) := by
        indep [compressionSetupGlobals_iff]
      exact h.run_of_sub (by decide) (by simp [wregs]) hg
    refine ⟨AddrOK.of_memFree rfl, ⟨hg', ?_, ?_, ?_, ?_, ?_, ?_⟩, hg'.clauses⟩
    · intro i hi; omega
    · intro i hi; omega
    · simp [setupSpecialPrefix, contractionArcCodes, Arr]
    · intro a ha; simpa using congrFun hm a
    · simp +decide [setupSpecialPrefix]
    · simpa using ho
  have hl := HTB.forUpC (S := S) (i := setupIndex) (n := setupClauseCount)
    (N := rows.length) (body := compressionSetupBody) Inv 80
    (by decide) (by decide) (by decide)
    (fun j => by indep [Inv, SetupScanInv, compressionSetupGlobals_iff])
    (fun j hj => compressionSetupBody_spec hmem has hap hsp hinput hS j hj)
  exact (hinit.seq hl |>.post (fun c hc => hc.1)).weaken (by omega)

end STACS2027.Runtimes.BoundedCost
