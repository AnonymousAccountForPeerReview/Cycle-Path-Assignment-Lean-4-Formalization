module

public import Runtimes.BoundedCost.ContractionHeader
public import Runtimes.BoundedCost.ContractionRows
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM

theorem ContractionRowsMem.of_labelFrame {formula active reference labels nodes : ℕ}
    {rows : List ContractionRow} {memory memory' : ℕ → ℕ}
    (hmem : ContractionRowsMem formula active reference nodes rows memory)
    (hframe : SameOn (OutsideCells labels (2 * nodes)) memory memory')
    (hformula : DisjointCells labels (2 * nodes) formula (2 * rows.length))
    (hactive : DisjointCells labels (2 * nodes) active rows.length)
    (hreference : DisjointCells labels (2 * nodes) reference (2 * nodes)) :
    ContractionRowsMem formula active reference nodes rows memory' := by
  intro i hi
  obtain ⟨hfirst, hsecond, hf, hs, ha, hrf, hrs⟩ := hmem i hi
  refine ⟨hfirst, hsecond, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hframe _ (hformula.outside (by omega))).trans hf
  · exact (hframe _ (hformula.outside (by omega))).trans hs
  · exact (hframe _ (hactive.outside (by omega))).trans ha
  · exact (hframe _ (hreference.outside (by omega))).trans hrf
  · exact (hframe _ (hreference.outside (by omega))).trans hrs

def ContractionResult (formula active reference forced labels output : ℕ)
    (terminals : List TerminalRow) (rows : List ContractionRow) (memory : ℕ → ℕ)
    (oldOutput : List ℕ) (c : Config) : Prop :=
  ContractionGlobals formula active reference forced labels output terminals.length rows.length c ∧
  Tab c.mem labels (2 * terminals.length) (TerminalLabelValue terminals) ∧
  Arr c.mem output (contractionEdgeInput terminals.length
    (contractionArcsPrefix (TerminalLabelValue terminals) rows rows.length)) ∧
  SameOn (fun a => OutsideCells labels (2 * terminals.length) a ∧
    OutsideCells output (5 + 2 * rows.length) a) memory c.mem ∧
  c.reg contractionArcCount = (contractionArcsPrefix (TerminalLabelValue terminals) rows rows.length).length ∧
  c.reg contractionIncompatible = (if terminalConflictPrefix terminals terminals.length then 1 else 0) ∧
  c.out = oldOutput

/-- The executable builder uses two bounded scans and emits the exact contracted edge input. -/
theorem contractionBuild_spec {S formula active reference forced labels output : ℕ}
    {terminals : List TerminalRow} {rows : List ContractionRow} {memory : ℕ → ℕ}
    {oldOutput : List ℕ}
    (hterminal : TerminalRowsMem forced reference terminals memory)
    (hrows : ContractionRowsMem formula active reference terminals.length rows memory)
    (hlabelForced : DisjointCells labels (2 * terminals.length) forced (2 * terminals.length))
    (hlabelReference : DisjointCells labels (2 * terminals.length) reference (2 * terminals.length))
    (hlabelFormula : DisjointCells labels (2 * terminals.length) formula (2 * rows.length))
    (hlabelActive : DisjointCells labels (2 * terminals.length) active rows.length)
    (houtFormula : DisjointCells output (5 + 2 * rows.length) formula (2 * rows.length))
    (houtActive : DisjointCells output (5 + 2 * rows.length) active rows.length)
    (houtReference : DisjointCells output (5 + 2 * rows.length) reference (2 * terminals.length))
    (houtLabels : DisjointCells output (5 + 2 * rows.length) labels (2 * terminals.length))
    (hS : forced + 2 * terminals.length ≤ S ∧ reference + 2 * terminals.length ≤ S ∧
      labels + 2 * terminals.length ≤ S ∧ formula + 2 * rows.length ≤ S ∧
      active + rows.length ≤ S ∧ output + 5 + 2 * rows.length ≤ S) :
    HTB S contractionBuild
      (fun c => ContractionGlobals formula active reference forced labels output terminals.length rows.length c ∧
        c.mem = memory ∧ c.out = oldOutput)
      (ContractionResult formula active reference forced labels output terminals rows memory oldOutput)
      (84 * terminals.length + 204 * rows.length + 51) := by
  let labelsInv := LabelBuildInv formula active reference forced labels output rows.length
    terminals memory oldOutput terminals.length
  let rest := Stmt.seq contractionHeader
    (.seq (forUp contractionIndex contractionClauseCount contractionClauseBody)
      (contractionStoreOffset contractionOutputBase 1 contractionArcCount))
  have hrest : HTB S rest labelsInv
      (ContractionResult formula active reference forced labels output terminals rows memory oldOutput)
      (204 * rows.length + 46) := by
    intro c hc
    obtain ⟨hg, htab, hframe, hflag, hcount, hout⟩ := hc
    have hrows' := hrows.of_labelFrame hframe hlabelFormula hlabelActive hlabelReference
    let flag := if terminalConflictPrefix terminals terminals.length then 1 else 0
    have hhead := contractionHeader_spec (S := S) (formula := formula) (active := active)
      (reference := reference) (forced := forced) (labelValues := TerminalLabelValue terminals)
      (rows := rows) (memory := c.mem) (oldOutput := oldOutput) (flag := flag) houtLabels (by omega)
    obtain ⟨cHead, tHead, heHead, hHead, htHead⟩ := hhead c ⟨hg, htab, rfl, hcount, hflag, hout⟩
    have hscan := contractionClauseScan_spec (forced := forced) (labelValues := TerminalLabelValue terminals) (memory := c.mem) (oldOutput := oldOutput) (flag := flag)
      hrows' houtFormula houtActive houtReference houtLabels ⟨hS.2.2.2.1, hS.2.2.2.2.1,
        hS.2.1, hS.2.2.1, hS.2.2.2.2.2⟩
    obtain ⟨cScan, tScan, heScan, hScan, htScan⟩ := hscan cHead hHead
    have hfoot := contractionFooter_spec (S := S) (formula := formula) (active := active)
      (reference := reference) (forced := forced) (labelValues := TerminalLabelValue terminals)
      (rows := rows) (memory := c.mem) (oldOutput := oldOutput) (flag := flag) houtLabels (by omega)
    obtain ⟨cFinal, tFinal, heFinal, hFinal, htFinal⟩ := hfoot cScan hScan
    obtain ⟨hgFinal, htFinalLabels, haFinal, hmFinal, hcFinal, hfFinal, hoFinal⟩ := hFinal
    refine ⟨cFinal, tHead + (tScan + tFinal), ExecB.seq heHead (ExecB.seq heScan heFinal),
      ⟨hgFinal, htFinalLabels, haFinal, ?_, hcFinal, hfFinal, hoFinal⟩, ?_⟩
    · intro a ha
      exact (hmFinal a ha.2).trans (hframe a ha.1)
    · omega
  have hl := contractionLabelScan_spec (formula := formula) (active := active) (output := output) (clauses := rows.length) (oldOutput := oldOutput)
    hterminal hlabelForced hlabelReference ⟨hS.1, hS.2.1, hS.2.2.1⟩
  have hl' : HTB S
      (.seq (.seq (.const contractionIncompatible 0) (.const contractionArcCount 0))
        (forUp contractionIndex contractionVariableCount contractionLabelBody))
      (fun c => ContractionGlobals formula active reference forced labels output terminals.length rows.length c ∧
        c.mem = memory ∧ c.out = oldOutput) labelsInv (84 * terminals.length + 5) := by
    exact hl.reassoc
  have hfull := (hl'.seq hrest).assoc.assoc
  have hb : (84 * terminals.length + 5) + (204 * rows.length + 46) =
      84 * terminals.length + 204 * rows.length + 51 := by omega
  rw [hb] at hfull
  exact hfull

end STACS2027.Runtimes.BoundedCost
