module

public import Runtimes.BoundedCost.InnerIndependence
import Mathlib.Tactic

/-! Odometer writes alter only the inner digit array and its represented list. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem innerRep_setDigit {F : Stmt} {layout : CompilerLayout} {nodes S depth globalBudget deleted : ℕ}
    {original : CNF} {τ : Assignment} {activeBits forcedBits oldOutput digits : List ℕ}
    {oldMemory : ℕ → ℕ} {answer : Option Assignment} {c : Config} {i v : ℕ}
    (hgeo : InnerGeometry S layout nodes original.length depth)
    (hcodes : (TwoSat.codes original).length ≤ 2 * original.length)
    (hactive : activeBits.length = original.length) (hforced : forcedBits.length = 2 * nodes)
    (h : InnerRep F layout nodes original τ depth globalBudget deleted activeBits forcedBits
      oldOutput oldMemory answer digits c) (hi : i < digits.length) :
    InnerRep F layout nodes original τ depth globalBudget deleted activeBits forcedBits
      oldOutput oldMemory answer (digits.set i v) (c.setMem (layout.innerDigits + i) v) := by
  obtain ⟨⟨hp, hr, ha, hf, hob, hol, hk, hlen⟩, hans, hframe⟩ := h
  obtain ⟨hg, hc, ht, hz, ho, hd, hdepth, hds⟩ := hp
  obtain ⟨hcut, hlabels, hactiveSeed, hseedDigits, hdigitsOutput⟩ := hgeo
  obtain ⟨_, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hcut
  have hindex : i < depth := by omega
  have htruth : TruthTable (c.setMem (layout.innerDigits + i) v).mem layout.reference nodes τ :=
    ht.upd_outside (by omega)
  have hg' : LeastCutGlobals layout.formula layout.active layout.candidate layout.reference
      layout.forced layout.labels layout.edgeInput nodes original.length layout.span
      (c.setMem (layout.innerDigits + i) v) := by
    simpa only [LeastCutGlobals, contractionGlobals_iff, registerView, setMem_reg] using hg
  refine ⟨⟨⟨hg', ?_, htruth, hz, ho, hd, ?_, ?_⟩, hr, ?_, ?_, hob, ?_, hk, ?_⟩, ?_, ?_⟩
  · exact hc.upd_of_disjoint (by omega)
  · simpa only [List.length_set, setMem_reg] using hdepth
  · exact hds.upd_set rfl
  · exact ha.upd_of_disjoint (by omega)
  · exact hf.upd_of_disjoint (by omega)
  · simpa only [List.length_set, setMem_reg] using hol
  · simpa only [List.length_set] using hlen
  · cases answer with
    | none => exact hans
    | some σ => exact ⟨hans.1, hans.2.upd_outside (by omega)⟩
  · intro a ha
    have hne : a ≠ layout.innerDigits + i := by
      have hd := ha.2
      unfold OutsideCells at hd
      omega
    exact (by simpa only [setMem_mem, upd_apply, if_neg hne] using hframe a ha)

end STACS2027.Runtimes.BoundedCost
