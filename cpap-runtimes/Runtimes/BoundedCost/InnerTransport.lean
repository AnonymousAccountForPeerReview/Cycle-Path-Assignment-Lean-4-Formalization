module

public import Runtimes.BoundedCost.InnerDigitUpdates
public import Runtimes.BoundedCost.PathRestoreTables
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def pathBasicRegisters : List ℕ := [200, 201, 202, 203, 204, 220, 222, 223, 300, 350, 400, 344, 345]

theorem pathBasic_transport {F : Stmt} {layout : CompilerLayout} {nodes : ℕ} {original : CNF}
    {τ : Assignment} {digits oldOutput : List ℕ} {c₀ c : Config}
    (hb : PathBasic F layout nodes original τ digits oldOutput c₀)
    (hreg : ∀ r ∈ pathBasicRegisters, c.reg (callerRegister r) = c₀.reg (callerRegister r))
    (hcodes : Arr c.mem layout.formula (TwoSat.codes original))
    (href : TruthTable c.mem layout.reference nodes τ)
    (hdigits : Arr c.mem layout.innerDigits digits)
    (hzero : ∀ r, r ∉ wregs (Flow.hornSeparator F) → c.reg (Flow.rl 0 r) = 0)
    (hout : c.out = c₀.out) : PathBasic F layout nodes original τ digits oldOutput c := by
  obtain ⟨hg, _, _, _, ho, hd, hl, _⟩ := hb
  refine ⟨?_, hcodes, href, hzero, hout.trans ho, ?_, ?_, hdigits⟩
  · rcases hg with ⟨hg, hcandidate, hregion, hspan⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hg with ⟨hformula, hactive, href, hforced, hlabels, houtput, hn, hm⟩
      constructor
      all_goals first
        | exact (hreg _ (by decide)).trans hformula
        | exact (hreg _ (by decide)).trans hactive
        | exact (hreg _ (by decide)).trans href
        | exact (hreg _ (by decide)).trans hforced
        | exact (hreg _ (by decide)).trans hlabels
        | exact (hreg _ (by decide)).trans houtput
        | exact (hreg _ (by decide)).trans hn
        | exact (hreg _ (by decide)).trans hm
    · exact (hreg _ (by decide)).trans hcandidate
    · exact (hreg _ (by decide)).trans hregion
    · exact (hreg _ (by decide)).trans hspan
  · exact (hreg _ (by decide)).trans hd
  · exact (hreg _ (by decide)).trans hl

theorem innerGeometry_snapshot_frames {S nodes clauses depth : ℕ} {layout : CompilerLayout}
    (h : InnerGeometry S layout nodes clauses depth) :
    (∀ i < clauses, SearchNodeMemoryFrame layout.span layout.active layout.candidate layout.forced
      layout.labels layout.edgeInput nodes clauses (layout.baseActive + i)) ∧
    (∀ u < 2 * nodes, SearchNodeMemoryFrame layout.span layout.active layout.candidate layout.forced
      layout.labels layout.edgeInput nodes clauses (layout.seedForced + u)) ∧
    (∀ j < depth, SearchNodeMemoryFrame layout.span layout.active layout.candidate layout.forced
      layout.labels layout.edgeInput nodes clauses (layout.innerDigits + j)) := by
  obtain ⟨hcut, hlabels, hbase, hforced, hdigits⟩ := h
  obtain ⟨hh, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hcut
  unfold SearchNodeMemoryFrame LeastCutFrame OutsideCells
  exact ⟨fun i hi => by omega, fun u hu => by omega, fun j hj => by omega⟩

theorem innerBasic_of_path {F : Stmt} {S time nodes depth globalBudget deleted : ℕ}
    {layout : CompilerLayout} {original : CNF} {τ : Assignment} {digits oldOutput : List ℕ}
    {c₀ c : Config} {rows : List (Bool × Clause)} {forced : ℕ → Bool}
    (hgeo : InnerGeometry S layout nodes original.length depth)
    (hlen : rows.length = original.length)
    (hb : InnerBasic F layout nodes original τ depth globalBudget deleted
      (maskWords rows) (forcedWords nodes forced) oldOutput digits c₀)
    (hpath : PathBasic F layout nodes original τ digits oldOutput c)
    (he : ExecB S (renamedPathControl callerRegister (searchNode F)) c₀ time c)
    (hframe : SameOn (SearchNodeMemoryFrame layout.span layout.active layout.candidate layout.forced
      layout.labels layout.edgeInput nodes original.length) c₀.mem c.mem) :
    InnerBasic F layout nodes original τ depth globalBudget deleted
      (maskWords rows) (forcedWords nodes forced) oldOutput digits c := by
  obtain ⟨_, hr, ha, hf, hob, hol, hk, hlength⟩ := hb
  have hregs (r : ℕ) (h38 : 38 ≤ r) (hb : r ∉ wregs contractionBuild)
      (hd : r ∉ wregs CandidateDecode.program) (hs : r ∉ wregs searchScan)
      (hu : r ∉ wregs annotatedNodeUpdate) (hi : r ≠ pathIndex) (hc : r ≠ nodeChoice) :
      c.reg (callerRegister r) = c₀.reg (callerRegister r) :=
    actualPath_registerFrame he h38 hb hd hs hu hi hc
  refine ⟨hpath, ?_, ?_, ?_, ?_, ?_, ?_, hlength⟩
  · obtain ⟨ha, hf, has, hfs, hm, hn, hbudget, hdeleted⟩ := hr
    exact ⟨(hregs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha,
      (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hf,
      (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans has,
      (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfs,
      (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hm,
      (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn,
      (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbudget,
      (hregs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdeleted⟩
  · intro i hi
    have hi' : i < original.length := by simpa only [maskWords_length, hlen] using hi
    exact (hframe _ ((innerGeometry_snapshot_frames hgeo).1 i hi')).trans (ha i hi)
  · intro u hu
    have hu' : u < 2 * nodes := by simpa only [forcedWords_length] using hu
    exact (hframe _ ((innerGeometry_snapshot_frames hgeo).2.1 u hu')).trans (hf u hu)
  · simpa only [innerCallerRegister_base] using
      (hregs 532 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (by simpa only [innerCallerRegister_base] using hob)
  · simpa only [innerCallerRegister_depth] using
      (hregs 533 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (by simpa only [innerCallerRegister_depth] using hol)
  · simpa only [innerCallerRegister_radix] using
      (hregs rK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (by simpa only [innerCallerRegister_radix] using hk)

end STACS2027.Runtimes.BoundedCost
