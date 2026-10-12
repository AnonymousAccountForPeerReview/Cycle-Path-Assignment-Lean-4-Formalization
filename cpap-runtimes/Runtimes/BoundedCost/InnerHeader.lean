module

public import Runtimes.BoundedCost.InnerSearchRAM
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def InnerStart (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (depth globalBudget deleted : ℕ) (activeBits forcedBits oldOutput : List ℕ)
    (oldMemory : ℕ → ℕ) (c : Config) : Prop :=
  ∃ digits, PathBasic F layout nodes original τ digits oldOutput c ∧ digits.length = depth ∧
    PathRestore.Globals layout.active layout.forced layout.baseActive layout.seedForced original.length
      (2 * nodes) globalBudget deleted (registerView callerRegister c) ∧
    Arr c.mem layout.baseActive activeBits ∧ Arr c.mem layout.seedForced forcedBits ∧
    c.reg (callerRegister nodeSuccess) = 0 ∧
    SameOn (InnerMemoryFrame layout nodes original.length depth) oldMemory c.mem

theorem pathBasic_transport_newDigits {F : Stmt} {layout : CompilerLayout} {nodes : ℕ} {original : CNF}
    {τ : Assignment} {digits newDigits oldOutput : List ℕ} {c₀ c : Config}
    (hb : PathBasic F layout nodes original τ digits oldOutput c₀)
    (hlen : newDigits.length = digits.length)
    (hreg : ∀ r ∈ pathBasicRegisters, c.reg (callerRegister r) = c₀.reg (callerRegister r))
    (hcodes : Arr c.mem layout.formula (TwoSat.codes original))
    (href : TruthTable c.mem layout.reference nodes τ)
    (hdigits : Arr c.mem layout.innerDigits newDigits)
    (hzero : ∀ r, r ∉ wregs (Flow.hornSeparator F) → c.reg (Flow.rl 0 r) = 0)
    (hout : c.out = c₀.out) : PathBasic F layout nodes original τ newDigits oldOutput c := by
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
  · exact ((hreg _ (by decide)).trans hl).trans hlen.symm

theorem innerHeader_spec {F : Stmt} {S nodes depth globalBudget deleted : ℕ}
    {layout : CompilerLayout} {original : CNF} {τ : Assignment} {activeBits forcedBits oldOutput : List ℕ}
    {oldMemory : ℕ → ℕ}
    (hgeo : InnerGeometry S layout nodes original.length depth)
    (hcodeslen : (TwoSat.codes original).length ≤ 2 * original.length)
    (hactive : activeBits.length = original.length) (hforced : forcedBits.length = 2 * nodes) :
    HTB S (onCallerRegisters (LoopHeaders.program true))
      (InnerStart F layout nodes original τ depth globalBudget deleted activeBits forcedBits oldOutput oldMemory)
      (InnerRep F layout nodes original τ depth globalBudget deleted activeBits forcedBits oldOutput
        oldMemory none (Poly.cfg 3 depth 0)) (6 * depth + 13) := by
  intro c hpre
  obtain ⟨digits, hb, hlen, hr, ha, hf, hs, hframe⟩ := hpre
  obtain ⟨hcut, hlabels, hbase, hseed, hdigitsOutput⟩ := hgeo
  obtain ⟨_, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hcut
  have hheader := onCallerRegisters_htb (LoopHeaders.program_spec true
    (S := S) (base := layout.innerDigits) (depth := depth) (memory := c.mem) (out := c.out) (by omega))
  obtain ⟨c', time, he, hp, ht⟩ := hheader c
    ⟨hb.2.2.2.2.2.1, by simpa only [LoopHeaders.inputDepth, ite_true, registerView, hlen] using hb.2.2.2.2.2.2.1, rfl, rfl⟩
  obtain ⟨hg, hm, hds, ho⟩ := hp
  change c'.mem = ArrayBlocks.prefixMemory c.mem layout.innerDigits (List.replicate depth 0) depth at hm
  change Arr c'.mem layout.innerDigits (List.replicate depth 0) at hds
  change c'.out = c.out at ho
  simp only [LoopHeaders.Globals, LoopHeaders.inputBase, LoopHeaders.inputDepth,
    LoopHeaders.controlBase, LoopHeaders.controlDepth, ite_true, registerView] at hg
  have hregs (r : ℕ) (hr : r ∈ pathBasicRegisters) :
      c'.reg (callerRegister r) = c.reg (callerRegister r) := by
    simp only [pathBasicRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))
  have hmem (a : ℕ) (hout : OutsideCells layout.innerDigits depth a) : c'.mem a = c.mem a := by
    rw [hm]
    exact ArrayBlocks.prefixMemory_outside (by simpa only [List.length_replicate, OutsideCells] using hout)
  have hcodes : Arr c'.mem layout.formula (TwoSat.codes original) := by
    intro i hi
    exact (hmem _ (by unfold OutsideCells; omega)).trans (hb.2.1 i hi)
  have href : TruthTable c'.mem layout.reference nodes τ := by
    intro u hu
    exact (hmem _ (by unfold OutsideCells; omega)).trans (hb.2.2.1 u hu)
  have hz (r : ℕ) (hr : r ∉ wregs (Flow.hornSeparator F)) : c'.reg (Flow.rl 0 r) = 0 :=
    (callerRegister_exec_zero he r).trans (hb.2.2.2.1 r hr)
  have hcfg : Poly.cfg 3 depth 0 = List.replicate depth 0 := by simp [Poly.cfg, List.map_const']
  have hpath := pathBasic_transport_newDigits (newDigits := Poly.cfg 3 depth 0) hb (by simp [hcfg, hlen]) hregs hcodes href
    (by simpa only [hcfg] using hds) hz ho
  have hrestore : PathRestore.Globals layout.active layout.forced layout.baseActive layout.seedForced
      original.length (2 * nodes) globalBudget deleted (registerView callerRegister c') := by
    obtain ⟨hact, hfor, has, hfs, hclauses, hnodes, hk, hd⟩ := hr
    exact ⟨(he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hact,
      (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hfor,
      (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans has,
      (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hfs,
      (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hclauses,
      (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hnodes,
      (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hk,
      (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hd⟩
  have ha' : Arr c'.mem layout.baseActive activeBits := by
    intro i hi
    exact (hmem _ (by unfold OutsideCells; omega)).trans (ha i hi)
  have hf' : Arr c'.mem layout.seedForced forcedBits := by
    intro u hu
    exact (hmem _ (by unfold OutsideCells; omega)).trans (hf u hu)
  have hs' : c'.reg (callerRegister nodeSuccess) = 0 :=
    (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hs
  refine ⟨c', time, he, ⟨⟨hpath, hrestore, ha', hf', ?_, ?_, ?_, by simp⟩, hs', ?_⟩, ht⟩
  · exact hg.2.2.1
  · simpa only [hcfg, List.length_replicate, innerCallerRegister_depth] using hg.2.2.2.1
  · exact hg.2.2.2.2
  · intro a ha
    exact (hmem a ha.2).trans (hframe a ha)

end STACS2027.Runtimes.BoundedCost
