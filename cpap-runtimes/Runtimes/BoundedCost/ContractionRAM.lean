module

public import Runtimes.BoundedCost.ContractionData
public import Runtimes.Flow.PaddedEncoding
public import Outerplanar.RAM.Layout
import Mathlib.Tactic

/-! # Bounded RAM construction of contracted occurrence cut graphs -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

abbrev contractionFormulaBase : ℕ := 200
abbrev contractionClauseCount : ℕ := 201
abbrev contractionActiveBase : ℕ := 202
abbrev contractionReferenceBase : ℕ := 204
abbrev contractionVariableCount : ℕ := 220
abbrev contractionForcedBase : ℕ := 222
abbrev contractionLabelsBase : ℕ := 223
abbrev contractionOutputBase : ℕ := 300
abbrev contractionArcCount : ℕ := 301
abbrev contractionIncompatible : ℕ := 302
abbrev contractionIndex : ℕ := 303
abbrev contractionOffset : ℕ := 304
abbrev contractionPositive : ℕ := 305
abbrev contractionNegative : ℕ := 306
abbrev contractionReference : ℕ := 307
abbrev contractionLabel : ℕ := 308
abbrev contractionFirst : ℕ := 309
abbrev contractionSecond : ℕ := 310
abbrev contractionFirstTruth : ℕ := 311
abbrev contractionSecondTruth : ℕ := 312
abbrev contractionTail : ℕ := 313
abbrev contractionHead : ℕ := 314
abbrev contractionTemporary : ℕ := 315
abbrev contractionValue : ℕ := 316

def contractionChooseLabel : Stmt :=
  .ifz contractionPositive
    (.ifz contractionNegative (addc contractionLabel contractionIndex 2)
      (.ifz contractionReference (.const contractionLabel 0) (.const contractionLabel 1)))
    (.ifz contractionNegative
      (.ifz contractionReference (.const contractionLabel 1) (.const contractionLabel 0))
      (.seq (.const contractionLabel 0) (.const contractionIncompatible 1)))

def contractionLabelBody : Stmt :=
  .seq (.add contractionOffset contractionIndex contractionIndex)
    (.seq (ld contractionPositive contractionForcedBase contractionOffset)
      (.seq (ld contractionReference contractionReferenceBase contractionOffset)
        (.seq (inc contractionOffset)
          (.seq (ld contractionNegative contractionForcedBase contractionOffset)
            (.seq contractionChooseLabel
              (.seq (st contractionLabelsBase contractionOffset contractionLabel)
                (.seq (dec contractionOffset)
                  (st contractionLabelsBase contractionOffset contractionLabel))))))))

def contractionEmitArc : Stmt :=
  .seq (.add contractionOffset contractionArcCount contractionArcCount)
    (.seq (addc contractionOffset contractionOffset 5)
      (.seq (st contractionOutputBase contractionOffset contractionTail)
        (.seq (inc contractionOffset)
          (.seq (st contractionOutputBase contractionOffset contractionHead)
            (inc contractionArcCount)))))

def contractionRetainArc : Stmt :=
  .ifz contractionHead .skip
    (.ifz contractionTail contractionEmitArc
      (.seq (subc contractionTemporary contractionTail 1)
        (.ifz contractionTemporary .skip contractionEmitArc)))

def contractionReadArc (tail head : ℕ) : Stmt :=
  .seq (ld contractionTail contractionLabelsBase tail)
    (.seq (ld contractionHead contractionLabelsBase head) contractionRetainArc)

def contractionClauseBody : Stmt :=
  .seq (ld contractionValue contractionActiveBase contractionIndex)
    (.ifz contractionValue .skip
      (.seq (.add contractionOffset contractionIndex contractionIndex)
        (.seq (ld contractionFirst contractionFormulaBase contractionOffset)
          (.seq (inc contractionOffset)
            (.seq (ld contractionSecond contractionFormulaBase contractionOffset)
              (.seq (ld contractionFirstTruth contractionReferenceBase contractionFirst)
                (.seq (ld contractionSecondTruth contractionReferenceBase contractionSecond)
                  (.ifz contractionFirstTruth
                    (.ifz contractionSecondTruth .skip
                      (contractionReadArc contractionFirst contractionSecond))
                    (.ifz contractionSecondTruth
                      (contractionReadArc contractionSecond contractionFirst) .skip)))))))))

def contractionStoreOffset (base offset value : ℕ) : Stmt :=
  .seq (.const contractionOffset offset) (st base contractionOffset value)

def contractionHeader : Stmt :=
  .seq (addc contractionValue contractionVariableCount 2)
    (.seq (contractionStoreOffset contractionOutputBase 0 contractionValue)
      (.seq (.const contractionValue 0)
        (.seq (contractionStoreOffset contractionOutputBase 1 contractionValue)
          (.seq (contractionStoreOffset contractionOutputBase 2 contractionValue)
            (.seq (.const contractionValue 1)
              (.seq (contractionStoreOffset contractionOutputBase 3 contractionValue)
                (contractionStoreOffset contractionOutputBase 4 contractionVariableCount)))))))

def contractionBuild : Stmt :=
  .seq (.const contractionIncompatible 0)
    (.seq (.const contractionArcCount 0)
      (.seq (forUp contractionIndex contractionVariableCount contractionLabelBody)
        (.seq contractionHeader
          (.seq (forUp contractionIndex contractionClauseCount contractionClauseBody)
            (contractionStoreOffset contractionOutputBase 1 contractionArcCount)))))

@[mk_iff] structure ContractionGlobals (formula active reference forced labels output nodes clauses : ℕ)
    (c : Config) : Prop where
  formula : c.reg contractionFormulaBase = formula
  active : c.reg contractionActiveBase = active
  reference : c.reg contractionReferenceBase = reference
  forced : c.reg contractionForcedBase = forced
  labels : c.reg contractionLabelsBase = labels
  output : c.reg contractionOutputBase = output
  nodes : c.reg contractionVariableCount = nodes
  clauses : c.reg contractionClauseCount = clauses

def TerminalRowsMem (forced reference : ℕ) (rows : List TerminalRow) (memory : ℕ → ℕ) : Prop :=
  ∀ x, x < rows.length →
    memory (forced + 2 * x) = (if (rows.getD x default).positiveForced then 1 else 0) ∧
    memory (forced + 2 * x + 1) = (if (rows.getD x default).negativeForced then 1 else 0) ∧
    memory (reference + 2 * x) = (if (rows.getD x default).reference then 1 else 0)

def OutsideCells (base length a : ℕ) : Prop := a < base ∨ base + length ≤ a

def DisjointCells (base length other otherLength : ℕ) : Prop :=
  base + length ≤ other ∨ other + otherLength ≤ base

theorem DisjointCells.outside {base length other otherLength : ℕ}
    (h : DisjointCells base length other otherLength) {a : ℕ}
    (ha : other ≤ a ∧ a < other + otherLength) : OutsideCells base length a := by
  unfold DisjointCells OutsideCells at *
  omega

def LabelBuildInv (formula active reference forced labels output clauses : ℕ)
    (rows : List TerminalRow) (memory : ℕ → ℕ) (oldOutput : List ℕ) (count : ℕ)
    (c : Config) : Prop :=
  ContractionGlobals formula active reference forced labels output rows.length clauses c ∧
  Tab c.mem labels (2 * count) (TerminalLabelValue rows) ∧
  SameOn (OutsideCells labels (2 * count)) memory c.mem ∧
  c.reg contractionIncompatible = (if terminalConflictPrefix rows count then 1 else 0) ∧
  c.reg contractionArcCount = 0 ∧ c.out = oldOutput

private theorem contractionChooseLabel_run (x flag : ℕ) (row : TerminalRow) (c : Config)
    (hx : c.reg contractionIndex = x)
    (hp : c.reg contractionPositive = if row.positiveForced then 1 else 0)
    (hn : c.reg contractionNegative = if row.negativeForced then 1 else 0)
    (hr : c.reg contractionReference = if row.reference then 1 else 0)
    (hf : c.reg contractionIncompatible = flag) :
    (run contractionChooseLabel c).reg contractionLabel = terminalLabel x row ∧
    (run contractionChooseLabel c).reg contractionIncompatible =
      (if terminalConflict row then 1 else flag) := by
  cases hpos : row.positiveForced <;> cases hneg : row.negativeForced <;>
    cases href : row.reference <;>
    simp +decide [contractionChooseLabel, addc, terminalLabel, terminalConflict, hx, hp, hn, hr, hf,
      hpos, hneg, href]

theorem contractionLabelBody_spec {S formula active reference forced labels output clauses : ℕ}
    {rows : List TerminalRow} {memory : ℕ → ℕ} {oldOutput : List ℕ}
    (hmem : TerminalRowsMem forced reference rows memory)
    (hforced : DisjointCells labels (2 * rows.length) forced (2 * rows.length))
    (hreference : DisjointCells labels (2 * rows.length) reference (2 * rows.length))
    (hS : forced + 2 * rows.length ≤ S ∧ reference + 2 * rows.length ≤ S ∧
      labels + 2 * rows.length ≤ S) (x : ℕ) (hx : x < rows.length) :
    HTB S contractionLabelBody
      (fun c => LabelBuildInv formula active reference forced labels output clauses rows memory oldOutput x c ∧
        c.reg contractionIndex = x ∧ c.reg contractionVariableCount = rows.length)
      (fun c => LabelBuildInv formula active reference forced labels output clauses rows memory oldOutput (x + 1) c ∧
        c.reg contractionIndex = x ∧ c.reg contractionVariableCount = rows.length) 80 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hg, htab, hsame, hflag, hcount, hout⟩, hi, hn⟩
  let row := rows.getD x default
  obtain ⟨hp, hm, hr⟩ := hmem x hx
  have hpos : c.mem (forced + 2 * x) = if row.positiveForced then 1 else 0 :=
    (hsame _ (by
      have h := hforced.outside (a := forced + 2 * x) (by omega)
      unfold OutsideCells at *
      omega)).trans hp
  have hneg : c.mem (forced + 2 * x + 1) = if row.negativeForced then 1 else 0 :=
    (hsame _ (by
      have h := hforced.outside (a := forced + 2 * x + 1) (by omega)
      unfold OutsideCells at *
      omega)).trans hm
  have href : c.mem (reference + 2 * x) = if row.reference then 1 else 0 :=
    (hsame _ (by
      have h := hreference.outside (a := reference + 2 * x) (by omega)
      unfold OutsideCells at *
      omega)).trans hr
  have hpos' : c.mem (forced + (x + x)) = if row.positiveForced then 1 else 0 := by
    simpa [show x + x = 2 * x by omega] using hpos
  have hneg' : c.mem (forced + (x + x + 1)) = if row.negativeForced then 1 else 0 := by
    simpa [Nat.add_assoc, show x + x = 2 * x by omega] using hneg
  have href' : c.mem (reference + (x + x)) = if row.reference then 1 else 0 := by
    simpa [show x + x = 2 * x by omega] using href
  have hg' : ContractionGlobals formula active reference forced labels output rows.length clauses
      (run contractionLabelBody c) := by
    have hf : RegIndep (wregs contractionLabelBody)
        (ContractionGlobals formula active reference forced labels output rows.length clauses) := by
      indep [contractionGlobals_iff, contractionLabelBody, contractionChooseLabel]
    exact hf.run (by decide) hg
  have hi' : (run contractionLabelBody c).reg contractionIndex = x :=
    (run_reg_of_not_mem (by decide) (by decide) c).trans hi
  have hn' : (run contractionLabelBody c).reg contractionVariableCount = rows.length := hg'.nodes
  have hout' : (run contractionLabelBody c).out = oldOutput :=
    (run_out_of_writes (by decide) (by decide) c).trans hout
  have hcount' : (run contractionLabelBody c).reg contractionArcCount = 0 :=
    (run_reg_of_not_mem (by decide) (by decide) c).trans hcount
  rcases hg with ⟨hformula, hactive, hreferenceBase, hforcedBase, hlabels, houtput, hnodes, hclauses⟩
  have hrunMem : (run contractionLabelBody c).mem =
      upd (upd c.mem (labels + 2 * x + 1) (terminalLabel x row))
        (labels + 2 * x) (terminalLabel x row) := by
    cases hp : row.positiveForced <;> cases hm : row.negativeForced <;> cases hr : row.reference <;>
      simp +decide [contractionLabelBody, contractionChooseLabel, addc, subc, inc, dec, st, ld, terminalLabel,
        hi, hforcedBase, hreferenceBase, hlabels, hpos', hneg', href', hp, hm, hr]
    all_goals congr 2 <;> omega
  have hflag' : (run contractionLabelBody c).reg contractionIncompatible =
      if terminalConflictPrefix rows (x + 1) then 1 else 0 := by
    rw [terminalConflictPrefix_succ]
    change (run contractionLabelBody c).reg contractionIncompatible =
      if terminalConflictPrefix rows x || terminalConflict row then 1 else 0
    cases hp : row.positiveForced <;> cases hm : row.negativeForced <;> cases hr : row.reference <;>
      cases hc : terminalConflictPrefix rows x <;>
      simp +decide [contractionLabelBody, contractionChooseLabel, addc, subc, inc, dec, st, ld, terminalConflict,
        hi, hforcedBase, hreferenceBase, hlabels, hpos', hneg', href', hp, hm, hr, hflag, hc]
  refine ⟨?_, ⟨hg', ?_, ?_, hflag', hcount', hout'⟩, hi', hn'⟩
  · cases hp : row.positiveForced <;> cases hm : row.negativeForced <;> cases hr : row.reference <;>
      addr_ok [contractionLabelBody, contractionChooseLabel, inc, dec, addc, subc, st, ld, hi, hforcedBase, hreferenceBase,
        hlabels, hpos', hneg', href', hp, hm, hr]
  · intro code hcode
    rw [hrunMem]
    by_cases hlt : code < 2 * x
    · have hne : labels + code ≠ labels + 2 * x := by omega
      have hne' : labels + code ≠ labels + 2 * x + 1 := by omega
      simp only [upd_apply, hne, hne', ite_false]
      exact htab code hlt
    · have he : code = 2 * x ∨ code = 2 * x + 1 := by omega
      rcases he with rfl | rfl <;>
        simp [upd_apply, TerminalLabelValue, show (2 * x + 1) / 2 = x by omega, row, Nat.add_assoc]
  · intro a ha
    rw [hrunMem]
    have hn : a ≠ labels + 2 * x ∧ a ≠ labels + 2 * x + 1 := by
      unfold OutsideCells at ha
      omega
    simp only [upd_apply, hn.1, hn.2, ite_false]
    exact hsame a (by unfold OutsideCells at *; omega)

def contractionLabelScan : Stmt := .seq (.const contractionIncompatible 0)
  (.seq (.const contractionArcCount 0)
    (forUp contractionIndex contractionVariableCount contractionLabelBody))

theorem contractionLabelScan_spec {S formula active reference forced labels output clauses : ℕ}
    {rows : List TerminalRow} {memory : ℕ → ℕ} {oldOutput : List ℕ}
    (hmem : TerminalRowsMem forced reference rows memory)
    (hforced : DisjointCells labels (2 * rows.length) forced (2 * rows.length))
    (hreference : DisjointCells labels (2 * rows.length) reference (2 * rows.length))
    (hS : forced + 2 * rows.length ≤ S ∧ reference + 2 * rows.length ≤ S ∧
      labels + 2 * rows.length ≤ S) :
    HTB S contractionLabelScan
      (fun c => ContractionGlobals formula active reference forced labels output rows.length clauses c ∧
        c.mem = memory ∧ c.out = oldOutput)
      (LabelBuildInv formula active reference forced labels output clauses rows memory oldOutput rows.length)
      (84 * rows.length + 5) := by
  let Inv := LabelBuildInv formula active reference forced labels output clauses rows memory oldOutput
  have hinit : HTB S (.seq (.const contractionIncompatible 0) (.const contractionArcCount 0))
      (fun c => ContractionGlobals formula active reference forced labels output rows.length clauses c ∧
        c.mem = memory ∧ c.out = oldOutput)
      (fun c => Inv 0 c ∧ c.reg contractionVariableCount = rows.length) 2 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨hg, hm, ho⟩
    have hg' : ContractionGlobals formula active reference forced labels output rows.length clauses
        (run (.seq (.const contractionIncompatible 0) (.const contractionArcCount 0)) c) := by
      have h : RegIndep [contractionIncompatible, contractionArcCount]
          (ContractionGlobals formula active reference forced labels output rows.length clauses) := by
        indep [contractionGlobals_iff]
      exact h.run_of_sub (by decide) (by simp [wregs]) hg
    refine ⟨AddrOK.of_memFree rfl, ⟨hg', ?_, ?_, ?_, ?_, ?_⟩, hg'.nodes⟩
    · intro i hi; omega
    · intro a ha; simpa using congrFun hm a
    · simp +decide [terminalConflictPrefix]
    · simp +decide
    · simpa using ho
  have hl := HTB.forUpC (S := S) (i := contractionIndex) (n := contractionVariableCount)
    (N := rows.length) (body := contractionLabelBody) Inv 80
    (by decide) (by decide) (by decide)
    (fun j => by indep [Inv, LabelBuildInv, contractionGlobals_iff])
    (fun j hj => contractionLabelBody_spec hmem hforced hreference hS j hj)
  exact (hinit.seq hl |>.post (fun c hc => hc.1)).assoc.weaken (by omega)

def ContractionRowsMem (formula active reference nodes : ℕ) (rows : List ContractionRow)
    (memory : ℕ → ℕ) : Prop :=
  ∀ i, i < rows.length →
    let row := rows.getD i default
    row.first < 2 * nodes ∧ row.second < 2 * nodes ∧
      memory (formula + 2 * i) = row.first ∧ memory (formula + 2 * i + 1) = row.second ∧
      memory (active + i) = (if row.active then 1 else 0) ∧
      memory (reference + row.first) = (if row.firstReference then 1 else 0) ∧
      memory (reference + row.second) = (if row.secondReference then 1 else 0)

theorem contractionArcsPrefix_succ (labels : ℕ → ℕ) (rows : List ContractionRow) (count : ℕ) :
    contractionArcsPrefix labels rows (count + 1) =
      contractionArcsPrefix labels rows count ++
        (contractionRowArc labels (rows.getD count default)).toList := by
  simp only [contractionArcsPrefix, List.range_succ, List.filterMap_append]
  congr 1

theorem contractionArcsPrefix_length (labels : ℕ → ℕ) (rows : List ContractionRow) (count : ℕ) :
    (contractionArcsPrefix labels rows count).length ≤ count := by
  exact (List.length_filterMap_le _ _).trans_eq (List.length_range (n := count))

theorem contractionArcCodes_length (arcs : List (ℕ × ℕ)) :
    (contractionArcCodes arcs).length = 2 * arcs.length := by
  induction arcs with
  | nil => rfl
  | cons e arcs ih => simp [contractionArcCodes, ih]; omega

theorem contractionArcCodes_append (arcs rest : List (ℕ × ℕ)) :
    contractionArcCodes (arcs ++ rest) = contractionArcCodes arcs ++ contractionArcCodes rest := by
  simp [contractionArcCodes]

def contractionPrefixInput (nodes : ℕ) (arcs : List (ℕ × ℕ)) : List ℕ :=
  [nodes + 2, 0, 0, 1, nodes] ++ contractionArcCodes arcs

@[simp] theorem contractionPrefixInput_length (nodes : ℕ) (arcs : List (ℕ × ℕ)) :
    (contractionPrefixInput nodes arcs).length = 5 + 2 * arcs.length := by
  simp [contractionPrefixInput, contractionArcCodes_length]
  omega

def ClauseBuildInv (formula active reference forced labels output nodes : ℕ)
    (labelValues : ℕ → ℕ) (rows : List ContractionRow) (memory : ℕ → ℕ)
    (oldOutput : List ℕ) (flag count : ℕ) (c : Config) : Prop :=
  ContractionGlobals formula active reference forced labels output nodes rows.length c ∧
  Tab c.mem labels (2 * nodes) labelValues ∧
  Arr c.mem output (contractionPrefixInput nodes (contractionArcsPrefix labelValues rows count)) ∧
  SameOn (OutsideCells output (5 + 2 * (contractionArcsPrefix labelValues rows count).length)) memory c.mem ∧
  c.reg contractionArcCount = (contractionArcsPrefix labelValues rows count).length ∧
  c.reg contractionIncompatible = flag ∧ c.out = oldOutput

private def storeContractionArc (output count : ℕ) (arc : Option (ℕ × ℕ))
    (memory : ℕ → ℕ) : ℕ → ℕ :=
  match arc with
  | none => memory
  | some e => upd (upd memory (output + 5 + 2 * count) e.1) (output + 5 + 2 * count + 1) e.2

private theorem contractionRetainArc_run (output count tail head : ℕ) (c : Config)
    (ho : c.reg contractionOutputBase = output) (hc : c.reg contractionArcCount = count)
    (ht : c.reg contractionTail = tail) (hh : c.reg contractionHead = head) :
    (run contractionRetainArc c).mem = storeContractionArc output count (retainContractedArc tail head) c.mem ∧
    (run contractionRetainArc c).reg contractionArcCount =
      count + (retainContractedArc tail head).toList.length := by
  by_cases hhzero : head = 0
  · simp +decide [contractionRetainArc, retainContractedArc, hh, hhzero, storeContractionArc, hc]
  · by_cases htzero : tail = 0
    · simp +decide [contractionRetainArc, contractionEmitArc, retainContractedArc, storeContractionArc,
        ht, hh, ho, hc, htzero, hhzero, addc, inc, st, subc, two_mul, Nat.add_assoc]
      ac_rfl
    · by_cases htone : tail = 1
      · simp +decide [contractionRetainArc, retainContractedArc, storeContractionArc,
          ht, hh, hc, htzero, hhzero, htone, subc]
      · have hsub : tail - 1 ≠ 0 := by omega
        simp +decide [contractionRetainArc, contractionEmitArc, retainContractedArc, storeContractionArc,
          ht, hh, ho, hc, htzero, hhzero, htone, addc, inc, st, subc, hsub, two_mul, Nat.add_assoc]
        ac_rfl

private theorem contractionClauseBody_run (formula active reference labels output index count : ℕ)
    (labelValues : ℕ → ℕ) (row : ContractionRow) (c : Config)
    (hf : c.reg contractionFormulaBase = formula) (ha : c.reg contractionActiveBase = active)
    (hr : c.reg contractionReferenceBase = reference) (hl : c.reg contractionLabelsBase = labels)
    (ho : c.reg contractionOutputBase = output) (hi : c.reg contractionIndex = index)
    (hc : c.reg contractionArcCount = count)
    (hactive : c.mem (active + index) = if row.active then 1 else 0)
    (hfirst : c.mem (formula + 2 * index) = row.first)
    (hsecond : c.mem (formula + 2 * index + 1) = row.second)
    (hfirstRef : c.mem (reference + row.first) = if row.firstReference then 1 else 0)
    (hsecondRef : c.mem (reference + row.second) = if row.secondReference then 1 else 0)
    (hfirstLabel : c.mem (labels + row.first) = labelValues row.first)
    (hsecondLabel : c.mem (labels + row.second) = labelValues row.second) :
    (run contractionClauseBody c).mem =
      storeContractionArc output count (contractionRowArc labelValues row) c.mem ∧
    (run contractionClauseBody c).reg contractionArcCount =
      count + (contractionRowArc labelValues row).toList.length := by
  have hfirst' : c.mem (formula + (index + index)) = row.first := by
    simpa [show index + index = 2 * index by omega] using hfirst
  have hsecond' : c.mem (formula + (index + index + 1)) = row.second := by
    simpa [Nat.add_assoc, show index + index = 2 * index by omega] using hsecond
  have hsubFirst : labelValues row.first - 1 = 0 ↔ labelValues row.first = 0 ∨ labelValues row.first = 1 := by omega
  have hsubSecond : labelValues row.second - 1 = 0 ↔ labelValues row.second = 0 ∨ labelValues row.second = 1 := by omega
  cases hact : row.active <;> cases hfr : row.firstReference <;> cases hsr : row.secondReference <;>
    by_cases hfo : labelValues row.first = 0 <;> by_cases hso : labelValues row.second = 0 <;>
    by_cases hfi : labelValues row.first = 1 <;> by_cases hsi : labelValues row.second = 1 <;>
    simp +decide [contractionClauseBody, contractionReadArc, contractionRetainArc,
      contractionEmitArc, contractionRowArc, retainContractedArc, storeContractionArc,
      ld, st, inc, addc, subc, hf, ha, hr, hl, ho, hi, hc, hactive, hfirst', hsecond',
      hfirstRef, hsecondRef, hfirstLabel, hsecondLabel, hact, hfr, hsr,
      hfo, hso, hfi, hsi, hsubFirst, hsubSecond, two_mul, mul_two]
  all_goals ac_rfl

private theorem DisjointCells.outside_left {base length other otherLength : ℕ}
    (h : DisjointCells base length other otherLength) {a : ℕ}
    (ha : base ≤ a ∧ a < base + length) : OutsideCells other otherLength a := by
  unfold DisjointCells OutsideCells at *
  omega

theorem contractionClauseBody_spec {S formula active reference forced labels output nodes : ℕ}
    {labelValues : ℕ → ℕ} {rows : List ContractionRow} {memory : ℕ → ℕ}
    {oldOutput : List ℕ} {flag : ℕ}
    (hmem : ContractionRowsMem formula active reference nodes rows memory)
    (hformula : DisjointCells output (5 + 2 * rows.length) formula (2 * rows.length))
    (hactive : DisjointCells output (5 + 2 * rows.length) active rows.length)
    (hreference : DisjointCells output (5 + 2 * rows.length) reference (2 * nodes))
    (hlabels : DisjointCells output (5 + 2 * rows.length) labels (2 * nodes))
    (hS : formula + 2 * rows.length ≤ S ∧ active + rows.length ≤ S ∧
      reference + 2 * nodes ≤ S ∧ labels + 2 * nodes ≤ S ∧ output + 5 + 2 * rows.length ≤ S)
    (i : ℕ) (hi : i < rows.length) :
    HTB S contractionClauseBody
      (fun c => ClauseBuildInv formula active reference forced labels output nodes labelValues rows memory
        oldOutput flag i c ∧ c.reg contractionIndex = i ∧ c.reg contractionClauseCount = rows.length)
      (fun c => ClauseBuildInv formula active reference forced labels output nodes labelValues rows memory
        oldOutput flag (i + 1) c ∧ c.reg contractionIndex = i ∧ c.reg contractionClauseCount = rows.length)
      200 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hg, htab, harray, hsame, hcount, hflag, hout⟩, hindex, hclauseCount⟩
  let row := rows.getD i default
  let edgePrefix := contractionArcsPrefix labelValues rows i
  let arc := contractionRowArc labelValues row
  let count := edgePrefix.length
  have hcountBound : count ≤ i := contractionArcsPrefix_length labelValues rows i
  have hcountEq : count = (contractionArcsPrefix labelValues rows i).length := rfl
  have hcounter : c.reg contractionArcCount = count := hcount
  obtain ⟨hfBound, hsBound, hfCode, hsCode, haBit, hfBit, hsBit⟩ := hmem i hi
  change row.first < 2 * nodes at hfBound
  change row.second < 2 * nodes at hsBound
  have hread (a : ℕ) (ha : OutsideCells output (5 + 2 * rows.length) a) : c.mem a = memory a :=
    hsame a (by unfold OutsideCells at *; omega)
  have hfCode' : c.mem (formula + 2 * i) = row.first :=
    (hread _ (hformula.outside (by omega))).trans hfCode
  have hsCode' : c.mem (formula + 2 * i + 1) = row.second :=
    (hread _ (hformula.outside (by omega))).trans hsCode
  have haBit' : c.mem (active + i) = if row.active then 1 else 0 :=
    (hread _ (hactive.outside (by omega))).trans haBit
  have hfBit' : c.mem (reference + row.first) = if row.firstReference then 1 else 0 :=
    (hread _ (hreference.outside (by change reference ≤ reference + row.first ∧
      reference + row.first < reference + 2 * nodes; omega))).trans hfBit
  have hsBit' : c.mem (reference + row.second) = if row.secondReference then 1 else 0 :=
    (hread _ (hreference.outside (by change reference ≤ reference + row.second ∧
      reference + row.second < reference + 2 * nodes; omega))).trans hsBit
  have hfLabel := htab row.first hfBound
  have hsLabel := htab row.second hsBound
  have hg' : ContractionGlobals formula active reference forced labels output nodes rows.length
      (run contractionClauseBody c) := by
    have hindep : RegIndep (wregs contractionClauseBody)
        (ContractionGlobals formula active reference forced labels output nodes rows.length) := by
      indep [contractionGlobals_iff, contractionClauseBody, contractionReadArc,
        contractionRetainArc, contractionEmitArc]
    exact hindep.run (by decide) hg
  have hi' : (run contractionClauseBody c).reg contractionIndex = i :=
    (run_reg_of_not_mem (by decide) (by decide) c).trans hindex
  have hflag' : (run contractionClauseBody c).reg contractionIncompatible = flag :=
    (run_reg_of_not_mem (by decide) (by decide) c).trans hflag
  have hout' : (run contractionClauseBody c).out = oldOutput :=
    (run_out_of_writes (by decide) (by decide) c).trans hout
  rcases hg with ⟨hgFormula, hgActive, hgReference, hgForced, hgLabels, hgOutput, hgNodes, hgCount⟩
  have hrun := contractionClauseBody_run formula active reference labels output i count labelValues row c
    hgFormula hgActive hgReference hgLabels hgOutput hindex hcount
    haBit' hfCode' hsCode' hfBit' hsBit' hfLabel hsLabel
  change (run contractionClauseBody c).mem = storeContractionArc output count arc c.mem ∧
    (run contractionClauseBody c).reg contractionArcCount = count + arc.toList.length at hrun
  have hnext : contractionArcsPrefix labelValues rows (i + 1) = edgePrefix ++ arc.toList :=
    contractionArcsPrefix_succ labelValues rows i
  refine ⟨?_, ⟨hg', ?_, ?_, ?_, ?_, hflag', hout'⟩, hi', hg'.clauses⟩
  · have hfCode'' : c.mem (formula + (i + i)) = row.first := by
      simpa [show i + i = 2 * i by omega] using hfCode'
    have hsCode'' : c.mem (formula + (i + i + 1)) = row.second := by
      simpa [Nat.add_assoc, show i + i = 2 * i by omega] using hsCode'
    cases ha : row.active <;> cases hf : row.firstReference <;> cases hs : row.secondReference <;>
      addr_ok [contractionClauseBody, contractionReadArc, contractionRetainArc, contractionEmitArc,
        inc, addc, subc, ld, st, hgFormula, hgActive, hgReference, hgLabels, hgOutput,
        hindex, hcounter, hfCode'', hsCode'', haBit', hfBit', hsBit', hfLabel, hsLabel, ha, hf, hs]
  · rw [hrun.1]
    cases he : arc with
    | none => exact htab
    | some edge =>
      have ht : OutsideCells labels (2 * nodes) (output + 5 + 2 * count) :=
        hlabels.outside_left (by omega)
      have hh : OutsideCells labels (2 * nodes) (output + 5 + 2 * count + 1) :=
        hlabels.outside_left (by omega)
      exact (htab.upd_of_disjoint ht).upd_of_disjoint hh
  · rw [hrun.1, hnext]
    cases he : arc with
    | none => simpa [storeContractionArc, he] using harray
    | some edge =>
      have hfirst := harray.upd_snoc (x := edge.1) (a := output + 5 + 2 * count) (by
        rw [contractionPrefixInput_length]; dsimp [count, edgePrefix]; omega)
      have hsecond := hfirst.upd_snoc (x := edge.2) (a := output + 5 + 2 * count + 1) (by
        rw [List.length_append, contractionPrefixInput_length]; simp; dsimp [count, edgePrefix]; omega)
      simpa [storeContractionArc, contractionPrefixInput, contractionArcCodes_append,
        contractionArcCodes, List.append_assoc, he] using hsecond
  · intro a ha
    rw [hrun.1, hnext] at *
    cases he : arc with
    | none =>
      simp only [storeContractionArc, he, Option.toList_none, List.append_nil] at *
      exact hsame a ha
    | some edge =>
      simp only [he, Option.toList_some, List.length_append, List.length_singleton] at ha
      have hn : a ≠ output + 5 + 2 * count ∧ a ≠ output + 5 + 2 * count + 1 := by
        unfold OutsideCells at ha
        dsimp [count, edgePrefix]
        omega
      simp only [storeContractionArc, he, upd_apply, hn.1, hn.2, ite_false]
      exact hsame a (by unfold OutsideCells at *; dsimp [count, edgePrefix] at *; omega)
  · rw [hnext, List.length_append, hrun.2]

/-- One bounded scan appends every retained active arc occurrence in input order. -/
theorem contractionClauseScan_spec {S formula active reference forced labels output nodes : ℕ}
    {labelValues : ℕ → ℕ} {rows : List ContractionRow} {memory : ℕ → ℕ}
    {oldOutput : List ℕ} {flag : ℕ}
    (hmem : ContractionRowsMem formula active reference nodes rows memory)
    (hformula : DisjointCells output (5 + 2 * rows.length) formula (2 * rows.length))
    (hactive : DisjointCells output (5 + 2 * rows.length) active rows.length)
    (hreference : DisjointCells output (5 + 2 * rows.length) reference (2 * nodes))
    (hlabels : DisjointCells output (5 + 2 * rows.length) labels (2 * nodes))
    (hS : formula + 2 * rows.length ≤ S ∧ active + rows.length ≤ S ∧
      reference + 2 * nodes ≤ S ∧ labels + 2 * nodes ≤ S ∧ output + 5 + 2 * rows.length ≤ S) :
    HTB S (forUp contractionIndex contractionClauseCount contractionClauseBody)
      (ClauseBuildInv formula active reference forced labels output nodes labelValues rows memory oldOutput flag 0)
      (ClauseBuildInv formula active reference forced labels output nodes labelValues rows memory oldOutput flag rows.length)
      (204 * rows.length + 3) := by
  let Inv := ClauseBuildInv formula active reference forced labels output nodes labelValues rows memory oldOutput flag
  have h := HTB.forUpC (S := S) (i := contractionIndex) (n := contractionClauseCount)
    (N := rows.length) (body := contractionClauseBody) Inv 200
    (by decide) (by decide) (by decide)
    (fun j => by indep [Inv, ClauseBuildInv, contractionGlobals_iff])
    (fun j hj => contractionClauseBody_spec hmem hformula hactive hreference hlabels hS j hj)
  exact h.pre (fun c hc => ⟨hc, hc.1.clauses⟩) |>.post (fun c hc => hc.1) |>.weaken (by omega)

end STACS2027.Runtimes.BoundedCost
