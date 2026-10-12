module

public import Runtimes.BoundedCost.PathRepresentation
public import Runtimes.BoundedCost.SearchNodeRAM
import Mathlib.Tactic

/-! The concrete search node preserves the original formula, reference table,
and bounded path controls. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem pathBasic_of_searchNodeResult {F : Stmt} {layout : CompilerLayout} {nodes S : ℕ}
    {original : CNF} {τ : Assignment} {digits oldOutput : List ℕ}
    {rows : List (Bool × Clause)} {forced : ℕ → Bool} {budget choice : ℕ} {c₀ c : Config}
    (hlen : rows.length = original.length)
    (hcodeslen : (TwoSat.codes original).length ≤ 2 * original.length)
    (hgeo : LeastCutGeometry S layout.span layout.formula layout.active layout.candidate layout.reference
      layout.forced layout.labels layout.edgeInput nodes original.length)
    (hdigits : ∀ i, i < digits.length → SearchNodeMemoryFrame layout.span layout.active
      layout.candidate layout.forced layout.labels layout.edgeInput nodes original.length
      (layout.innerDigits + i))
    (hb : PathBasic F layout nodes original τ digits oldOutput c₀)
    (hp : SearchNodeResult (Flow.hornSeparator F) layout.span layout.active layout.candidate
      layout.forced layout.labels layout.edgeInput nodes rows τ forced budget choice 0 c₀ c) :
    PathBasic F layout nodes original τ digits oldOutput c := by
  obtain ⟨hg, hc, hr, hz, ho, hd, hl, ha⟩ := hb
  obtain ⟨hz', ho', hregs, hframe, _⟩ := hp
  rw [hlen] at hframe
  refine ⟨?_, ?_, ?_, hz', ho'.trans ho, ?_, ?_, ?_⟩
  · rcases hg with ⟨hg, hcandidate, hregion, hspan⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hg with ⟨hformula, hactive, href, hforced, hlabels, houtput, hn, hm⟩
      constructor
      all_goals first
        | exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hformula
        | exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hactive
        | exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans href
        | exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hforced
        | exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hlabels
        | exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans houtput
        | exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn
        | exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hm
    · exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcandidate
    · exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hregion
    · exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hspan
  · intro i hi
    have him : i < 2 * original.length := lt_of_lt_of_le hi hcodeslen
    have hf := hgeo.frame_input (Or.inl (by omega : layout.formula ≤ layout.formula + i ∧
      layout.formula + i < layout.formula + 2 * original.length))
    have hout : OutsideCells layout.active original.length (layout.formula + i) ∧
        OutsideCells layout.forced (2 * nodes) (layout.formula + i) := by
      obtain ⟨_, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hgeo
      unfold OutsideCells
      omega
    exact (hframe _ ⟨hf, hout⟩).trans (hc i hi)
  · intro u hu
    have hf := hgeo.frame_input (Or.inr (Or.inr (Or.inl
      (by omega : layout.reference ≤ layout.reference + u ∧
        layout.reference + u < layout.reference + 2 * nodes))))
    have hout : OutsideCells layout.active original.length (layout.reference + u) ∧
        OutsideCells layout.forced (2 * nodes) (layout.reference + u) := by
      obtain ⟨_, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hgeo
      unfold OutsideCells
      omega
    exact (hframe _ ⟨hf, hout⟩).trans (hr u hu)
  · exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hd
  · exact (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
  · intro i hi
    exact (hframe _ (hdigits i hi)).trans (ha i hi)

end STACS2027.Runtimes.BoundedCost
