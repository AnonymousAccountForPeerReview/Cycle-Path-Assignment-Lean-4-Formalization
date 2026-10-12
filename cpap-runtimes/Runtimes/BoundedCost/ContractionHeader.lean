module

public import Runtimes.BoundedCost.ContractionRAM
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM

def ContractionBuilt (formula active reference forced labels output nodes : ℕ)
    (labelValues : ℕ → ℕ) (rows : List ContractionRow) (memory : ℕ → ℕ)
    (oldOutput : List ℕ) (flag : ℕ) (c : Config) : Prop :=
  ContractionGlobals formula active reference forced labels output nodes rows.length c ∧
  Tab c.mem labels (2 * nodes) labelValues ∧
  Arr c.mem output (contractionEdgeInput nodes (contractionArcsPrefix labelValues rows rows.length)) ∧
  SameOn (OutsideCells output (5 + 2 * rows.length)) memory c.mem ∧
  c.reg contractionArcCount = (contractionArcsPrefix labelValues rows rows.length).length ∧
  c.reg contractionIncompatible = flag ∧ c.out = oldOutput

theorem contractionHeader_spec {S formula active reference forced labels output nodes : ℕ}
    {labelValues : ℕ → ℕ} {rows : List ContractionRow} {memory : ℕ → ℕ}
    {oldOutput : List ℕ} {flag : ℕ}
    (hlabels : DisjointCells output (5 + 2 * rows.length) labels (2 * nodes))
    (hS : output + 5 ≤ S) :
    HTB S contractionHeader
      (fun c => ContractionGlobals formula active reference forced labels output nodes rows.length c ∧
        Tab c.mem labels (2 * nodes) labelValues ∧ c.mem = memory ∧
        c.reg contractionArcCount = 0 ∧ c.reg contractionIncompatible = flag ∧ c.out = oldOutput)
      (ClauseBuildInv formula active reference forced labels output nodes labelValues rows memory oldOutput flag 0)
      40 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨hg, ht, hm, hc, hf, ho⟩
  have hg' : ContractionGlobals formula active reference forced labels output nodes rows.length
      (run contractionHeader c) := by
    have h : RegIndep (wregs contractionHeader)
        (ContractionGlobals formula active reference forced labels output nodes rows.length) := by
      indep [contractionGlobals_iff, contractionHeader, contractionStoreOffset]
    exact h.run (by decide) hg
  have hrun : (run contractionHeader c).mem =
      upd (upd (upd (upd (upd c.mem output (nodes + 2)) (output + 1) 0)
        (output + 2) 0) (output + 3) 1) (output + 4) nodes := by
    simp +decide [contractionHeader, contractionStoreOffset, addc, st, hg.output, hg.nodes]
  have harray : Arr (run contractionHeader c).mem output [nodes + 2, 0, 0, 1, nodes] := by
    rw [hrun]
    have hnil : Arr c.mem output [] := by intro i hi; simp at hi
    have h := ((((hnil.upd_snoc (a := output) (x := nodes + 2) (by simp)).upd_snoc (a := output + 1) (x := 0) (by simp)).upd_snoc
      (a := output + 2) (x := 0) (by simp)).upd_snoc (a := output + 3) (x := 1) (by simp)).upd_snoc (a := output + 4) (x := nodes) (by simp)
    simpa using h
  refine ⟨?_, hg', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · addr_ok [contractionHeader, contractionStoreOffset, addc, st, hg.output, hg.nodes]
  · intro i hi
    rw [hrun]
    have hne (j : ℕ) (hj : j < 5) : labels + i ≠ output + j := by
      unfold DisjointCells at hlabels
      omega
    simp only [upd_apply, hne 4 (by omega), hne 3 (by omega), hne 2 (by omega),
      hne 1 (by omega), show labels + i ≠ output by simpa using hne 0 (by omega), ite_false]
    exact ht i hi
  · simpa [contractionPrefixInput, contractionArcsPrefix, contractionArcCodes] using harray
  · intro a ha
    simp only [contractionArcsPrefix, List.range_zero, List.filterMap_nil, List.length_nil,
      Nat.mul_zero, Nat.add_zero] at ha
    have hne (j : ℕ) (hj : j < 5) : a ≠ output + j := by unfold OutsideCells at ha; omega
    rw [hrun]
    simp only [upd_apply, hne 4 (by omega), hne 3 (by omega), hne 2 (by omega),
      hne 1 (by omega), show a ≠ output by simpa using hne 0 (by omega), ite_false]
    exact congrFun hm a
  · simpa +decide [contractionHeader, contractionStoreOffset, addc, st, contractionArcsPrefix] using hc
  · exact (run_reg_of_not_mem (by decide) (by decide) c).trans hf
  · exact (run_out_of_writes (by decide) (by decide) c).trans ho

theorem contractionFooter_spec {S formula active reference forced labels output nodes : ℕ}
    {labelValues : ℕ → ℕ} {rows : List ContractionRow} {memory : ℕ → ℕ}
    {oldOutput : List ℕ} {flag : ℕ}
    (hlabels : DisjointCells output (5 + 2 * rows.length) labels (2 * nodes))
    (hS : output + 5 ≤ S) :
    HTB S (contractionStoreOffset contractionOutputBase 1 contractionArcCount)
      (ClauseBuildInv formula active reference forced labels output nodes labelValues rows memory oldOutput flag rows.length)
      (ContractionBuilt formula active reference forced labels output nodes labelValues rows memory oldOutput flag)
      3 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨hg, ht, ha, hm, hc, hf, ho⟩
  let arcs := contractionArcsPrefix labelValues rows rows.length
  have hrun : (run (contractionStoreOffset contractionOutputBase 1 contractionArcCount) c).mem =
      upd c.mem (output + 1) arcs.length := by
    simp +decide [contractionStoreOffset, st, hg.output, hc, arcs]
  have hg' : ContractionGlobals formula active reference forced labels output nodes rows.length
      (run (contractionStoreOffset contractionOutputBase 1 contractionArcCount) c) := by
    have h : RegIndep (wregs (contractionStoreOffset contractionOutputBase 1 contractionArcCount))
        (ContractionGlobals formula active reference forced labels output nodes rows.length) := by
      indep [contractionGlobals_iff, contractionStoreOffset]
    exact h.run (by decide) hg
  refine ⟨?_, hg', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · addr_ok [contractionStoreOffset, st, hg.output]
  · intro i hi
    rw [hrun]
    have hne : labels + i ≠ output + 1 := by unfold DisjointCells at hlabels; omega
    simp only [upd_apply, hne, ite_false]
    exact ht i hi
  · rw [hrun]
    have h := ha.upd_set (i := 1) (v := arcs.length) rfl
    simpa [contractionPrefixInput, contractionEdgeInput, arcs] using h
  · intro a ha'
    have hlen := contractionArcsPrefix_length labelValues rows rows.length
    have hne : a ≠ output + 1 := by unfold OutsideCells at ha'; omega
    rw [hrun]
    simp only [upd_apply, hne, ite_false]
    exact hm a (by unfold OutsideCells at *; omega)
  · exact (run_reg_of_not_mem (by decide) (by decide) c).trans hc
  · exact (run_reg_of_not_mem (by decide) (by decide) c).trans hf
  · exact (run_out_of_writes (by decide) (by decide) c).trans ho

end STACS2027.Runtimes.BoundedCost
