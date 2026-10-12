module

public import Runtimes.BoundedCost.Search
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-! Readonly bounded RAM analysis of the active clause occurrences at one annotated
search node. Literal truth is read from dense dual-literal tables. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

abbrev scanFormulaBase : ℕ := 200
abbrev scanClauseCount : ℕ := 201
abbrev scanActiveBase : ℕ := 202
abbrev scanCandidateBase : ℕ := 203
abbrev scanReferenceBase : ℕ := 204
abbrev scanUnsatisfied : ℕ := 206
abbrev scanCut : ℕ := 207
abbrev scanConflict : ℕ := 208
abbrev scanFirstLiteral : ℕ := 209
abbrev scanSecondLiteral : ℕ := 210
abbrev scanIndex : ℕ := 211
abbrev scanOffset : ℕ := 212
abbrev scanActive : ℕ := 213
abbrev scanFirst : ℕ := 214
abbrev scanSecond : ℕ := 215
abbrev scanFirstTruth : ℕ := 216
abbrev scanSecondTruth : ℕ := 217
abbrev scanFirstReference : ℕ := 218
abbrev scanSecondReference : ℕ := 219

structure SearchRow where
  first : ℕ
  second : ℕ
  active : Bool
  firstTruth : Bool
  secondTruth : Bool
  firstReference : Bool
  secondReference : Bool
  deriving Inhabited

structure SearchSummary where
  unsatisfied : ℕ := 0
  cut : ℕ := 0
  conflict : ℕ := 0
  firstLiteral : ℕ := 0
  secondLiteral : ℕ := 0
  deriving Inhabited

def summarizeRow (i : ℕ) (row : SearchRow) (state : SearchSummary) : SearchSummary :=
  if row.active && !(row.firstTruth || row.secondTruth) then
    if row.firstReference && row.secondReference then
      if state.conflict = 0 then
        { state with
          unsatisfied := state.unsatisfied + 1
          conflict := i + 1
          firstLiteral := row.first
          secondLiteral := row.second }
      else { state with unsatisfied := state.unsatisfied + 1 }
    else { state with unsatisfied := state.unsatisfied + 1, cut := state.cut + 1 }
  else state

def summarizePrefix (rows : List SearchRow) (count : ℕ) : SearchSummary :=
  (List.range count).foldl (fun state i => summarizeRow i (rows.getD i default) state) default

theorem summarizePrefix_succ (rows : List SearchRow) (count : ℕ) :
    summarizePrefix rows (count + 1) =
      summarizeRow count (rows.getD count default) (summarizePrefix rows count) := by
  simp [summarizePrefix, List.range_succ, List.foldl_append]

def SearchSummaryRep (summary : SearchSummary) (c : Config) : Prop :=
  c.reg scanUnsatisfied = summary.unsatisfied ∧ c.reg scanCut = summary.cut ∧
  c.reg scanConflict = summary.conflict ∧ c.reg scanFirstLiteral = summary.firstLiteral ∧
  c.reg scanSecondLiteral = summary.secondLiteral

def searchScanRecordConflict : Stmt :=
  .seq (addc scanConflict scanIndex 1)
    (.seq (mov scanFirstLiteral scanFirst) (mov scanSecondLiteral scanSecond))

def searchScanUnsatisfied : Stmt :=
  .seq (inc scanUnsatisfied)
    (.seq (ld scanFirstReference scanReferenceBase scanFirst)
      (.seq (ld scanSecondReference scanReferenceBase scanSecond)
        (.ifz scanFirstReference (inc scanCut)
          (.ifz scanSecondReference (inc scanCut)
            (.ifz scanConflict searchScanRecordConflict .skip)))))

def searchScanBody : Stmt :=
  .seq (ld scanActive scanActiveBase scanIndex)
    (.ifz scanActive .skip
      (.seq (.add scanOffset scanIndex scanIndex)
        (.seq (ld scanFirst scanFormulaBase scanOffset)
          (.seq (inc scanOffset)
            (.seq (ld scanSecond scanFormulaBase scanOffset)
              (.seq (ld scanFirstTruth scanCandidateBase scanFirst)
                (.seq (ld scanSecondTruth scanCandidateBase scanSecond)
                  (.ifz scanFirstTruth (.ifz scanSecondTruth searchScanUnsatisfied .skip) .skip))))))))

def searchScanInit : Stmt :=
  .seq (.const scanUnsatisfied 0) (.seq (.const scanCut 0)
    (.seq (.const scanConflict 0) (.seq (.const scanFirstLiteral 0) (.const scanSecondLiteral 0))))

def searchScan : Stmt := .seq searchScanInit (forUp scanIndex scanClauseCount searchScanBody)

def SearchScanGlobals (formula active candidate reference count : ℕ) (c : Config) : Prop :=
  c.reg scanFormulaBase = formula ∧ c.reg scanActiveBase = active ∧
  c.reg scanCandidateBase = candidate ∧ c.reg scanReferenceBase = reference ∧
  c.reg scanClauseCount = count

def SearchRowsMem (formula active candidate reference bound : ℕ)
    (rows : List SearchRow) (memory : ℕ → ℕ) : Prop :=
  ∀ i, i < rows.length →
    let row := rows.getD i default
    row.first < bound ∧ row.second < bound ∧
      memory (formula + 2 * i) = row.first ∧ memory (formula + 2 * i + 1) = row.second ∧
      memory (active + i) = (if row.active then 1 else 0) ∧
      memory (candidate + row.first) = (if row.firstTruth then 1 else 0) ∧
      memory (candidate + row.second) = (if row.secondTruth then 1 else 0) ∧
      memory (reference + row.first) = (if row.firstReference then 1 else 0) ∧
      memory (reference + row.second) = (if row.secondReference then 1 else 0)

theorem searchScanBody_spec {S formula active candidate reference bound : ℕ}
    {rows : List SearchRow} {memory : ℕ → ℕ}
    (hmem : SearchRowsMem formula active candidate reference bound rows memory)
    (hS : formula + 2 * rows.length ≤ S ∧ active + rows.length ≤ S ∧
      candidate + bound ≤ S ∧ reference + bound ≤ S)
    (i : ℕ) (hi : i < rows.length) (summary : SearchSummary) :
    HTB S searchScanBody
      (fun c => (SearchScanGlobals formula active candidate reference rows.length c ∧
        c.mem = memory ∧ SearchSummaryRep summary c) ∧ c.reg scanIndex = i ∧
        c.reg scanClauseCount = rows.length)
      (fun c => (SearchScanGlobals formula active candidate reference rows.length c ∧
        c.mem = memory ∧ SearchSummaryRep (summarizeRow i (rows.getD i default) summary) c) ∧
        c.reg scanIndex = i ∧ c.reg scanClauseCount = rows.length) 100 := by
  let row := rows.getD i default
  obtain ⟨hf, hs, hfirst, hsecond, hactive, htfirst, htsecond, hrfirst, hrsecond⟩ := hmem i hi
  have hfirst' : memory (formula + (i + i)) = row.first := by
    simpa [row, show i + i = 2 * i by omega] using hfirst
  have hsecond' : memory (formula + (i + i + 1)) = row.second := by
    simpa [row, Nat.add_assoc, show i + i = 2 * i by omega] using hsecond
  change memory (active + i) = (if row.active then 1 else 0) at hactive
  change memory (candidate + row.first) = (if row.firstTruth then 1 else 0) at htfirst
  change memory (candidate + row.second) = (if row.secondTruth then 1 else 0) at htsecond
  change memory (reference + row.first) = (if row.firstReference then 1 else 0) at hrfirst
  change memory (reference + row.second) = (if row.secondReference then 1 else 0) at hrsecond
  have hactiveAddr : active + i < S := by omega
  have hfirstAddr : formula + (i + i) < S := by omega
  have hsecondAddr : formula + (i + i + 1) < S := by omega
  have hcandidateFirst : candidate + row.first < S := by change candidate + (rows.getD i default).first < S; omega
  have hcandidateSecond : candidate + row.second < S := by change candidate + (rows.getD i default).second < S; omega
  have hreferenceFirst : reference + row.first < S := by change reference + (rows.getD i default).first < S; omega
  have hreferenceSecond : reference + row.second < S := by change reference + (rows.getD i default).second < S; omega
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hg, hm, hrep⟩, hindex, hcount⟩
  have hglobal : SearchScanGlobals formula active candidate reference rows.length
      (run searchScanBody c) := by
    have hindep : RegIndep (wregs searchScanBody)
        (SearchScanGlobals formula active candidate reference rows.length) := by
      indep [SearchScanGlobals, searchScanBody, searchScanUnsatisfied, searchScanRecordConflict]
    exact hindep.run (by decide) hg
  have hmemory : (run searchScanBody c).mem = memory :=
    (run_mem_of_stores (by decide) (by decide) c).trans hm
  have hindex' : (run searchScanBody c).reg scanIndex = i :=
    (run_reg_of_not_mem (by decide) (by decide) c).trans hindex
  have hcount' : (run searchScanBody c).reg scanClauseCount = rows.length :=
    (run_reg_of_not_mem (by decide) (by decide) c).trans hcount
  rcases hg with ⟨hformula, hactiveBase, hcandidate, hreference, _⟩
  rcases hrep with ⟨hunsatisfied, hcut, hconflict, hfirstLiteral, hsecondLiteral⟩
  refine ⟨?_, ⟨hglobal, hmemory, ?_⟩, hindex', hcount'⟩
  · simp +decide only [searchScanBody, searchScanUnsatisfied, searchScanRecordConflict,
      addrOK_seq, addrOK_ifz, addrOK_ld, addrOK_inc, addrOK_mov, addrOK_addc,
      addrOK_add, addrOK_skip, run_ld, run_inc, run_mov, run_addc, run_add,
      run_seq', run_ifz', setReg_reg, setReg_mem, ↓reduceIte, hm, hformula, hactiveBase,
      hcandidate, hreference, hindex, hfirst', hsecond', hactive,
      htfirst, htsecond, hrfirst, hrsecond, hactiveAddr, hfirstAddr, hsecondAddr,
      hcandidateFirst, hcandidateSecond, hreferenceFirst, hreferenceSecond, true_and,
      and_true, implies_true]
  · change SearchSummaryRep (summarizeRow i row summary) (run searchScanBody c)
    cases ha : row.active <;> cases ht : row.firstTruth <;> cases hu : row.secondTruth <;>
      cases hr : row.firstReference <;> cases hv : row.secondReference <;>
      by_cases hc : summary.conflict = 0 <;>
      simp +decide only [SearchSummaryRep, searchScanBody, searchScanUnsatisfied, searchScanRecordConflict,
        run_seq', run_ifz', run_skip, run_ld, run_inc, run_mov, run_addc, run_add, setReg_reg, setReg_mem, hm,
        hformula, hactiveBase, hcandidate, hreference, hindex, hfirst', hsecond', hactive,
        htfirst, htsecond, hrfirst, hrsecond, summarizeRow, ha, ht, hu, hr, hv,
        hunsatisfied, hcut, hconflict, hfirstLiteral, hsecondLiteral, hc,
        Bool.false_eq_true, eq_self, Bool.false_and, Bool.true_and,
        Bool.false_or, Bool.true_or, Bool.not_false, Bool.not_true, ↓reduceIte,
        true_and, and_true]

/-- One complete scan has linear time, preserves the formula and both truth tables,
and returns the exact summary of the active occurrences. -/
theorem searchScan_spec {S formula active candidate reference bound : ℕ}
    {rows : List SearchRow} {memory : ℕ → ℕ}
    (hmem : SearchRowsMem formula active candidate reference bound rows memory)
    (hS : formula + 2 * rows.length ≤ S ∧ active + rows.length ≤ S ∧
      candidate + bound ≤ S ∧ reference + bound ≤ S) :
    HTB S searchScan
      (fun c => SearchScanGlobals formula active candidate reference rows.length c ∧ c.mem = memory)
      (fun c => SearchScanGlobals formula active candidate reference rows.length c ∧
        c.mem = memory ∧ SearchSummaryRep (summarizePrefix rows rows.length) c)
      (104 * rows.length + 8) := by
  let Inv := fun i c => SearchScanGlobals formula active candidate reference rows.length c ∧
    c.mem = memory ∧ SearchSummaryRep (summarizePrefix rows i) c
  have hinit : HTB S searchScanInit
      (fun c => SearchScanGlobals formula active candidate reference rows.length c ∧ c.mem = memory)
      (fun c => Inv 0 c ∧ c.reg scanClauseCount = rows.length) 5 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨hg, hm⟩
    have hg' : SearchScanGlobals formula active candidate reference rows.length
        (run searchScanInit c) := by
      have hi : RegIndep (wregs searchScanInit)
          (SearchScanGlobals formula active candidate reference rows.length) := by
        indep [SearchScanGlobals, searchScanInit]
      exact hi.run (by decide) hg
    refine ⟨by simp [searchScanInit], ⟨hg', ?_, ?_⟩, hg'.2.2.2.2⟩
    · simpa [searchScanInit] using hm
    · simp +decide [SearchSummaryRep, summarizePrefix, searchScanInit, run_seq', setReg_reg,
        default]
  have hloop := HTB.forUpC (S := S) (i := scanIndex) (n := scanClauseCount)
    (N := rows.length) (body := searchScanBody) Inv 100
    (by decide) (by decide) (by decide)
    (fun i => by indep [Inv, SearchScanGlobals, SearchSummaryRep])
    (fun i hi => by
      simpa [Inv, summarizePrefix_succ] using
        searchScanBody_spec hmem hS i hi (summarizePrefix rows i))
  exact (hinit.seq hloop).mono (fun _ hc => hc) (fun _ hc => hc.1) (by omega)

end STACS2027.Runtimes.BoundedCost
