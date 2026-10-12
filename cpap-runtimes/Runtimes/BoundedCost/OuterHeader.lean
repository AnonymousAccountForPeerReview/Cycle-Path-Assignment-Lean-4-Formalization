module

public import Runtimes.BoundedCost.OuterIndependence
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def OuterStart (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (rows : List (Bool × Clause)) (special : CNF)
    (budget depth processed : ℕ) (oldOutput : List ℕ) (c : Config) : Prop :=
  Compiler.Globals layout nodes original.length budget depth (registerView callerRegister c) ∧
  Arr c.mem layout.formula (TwoSat.codes original) ∧ TruthTable c.mem layout.reference nodes τ ∧
  Compiler.StageZero (Flow.hornSeparator F) c ∧ c.out = oldOutput ∧
  Arr c.mem layout.baseActive (maskWords rows) ∧ Arr c.mem layout.special (TwoSat.codes special) ∧
  c.reg (callerRegister seedSpecialCount) = special.length ∧
  c.reg (callerRegister Compiler.processed) = processed ∧ c.reg (callerRegister Compiler.alive) = 1 ∧
  c.reg (callerRegister nodeSuccess) = 0

theorem outerHeader_spec {F : Stmt} {S nodes budget depth processed : ℕ}
    {layout : CompilerLayout} {original special : CNF} {τ : Assignment}
    {rows : List (Bool × Clause)} {oldOutput : List ℕ}
    (hgeo : OuterGeometry S layout nodes original.length depth special.length)
    (hrows : rows.length = original.length)
    (hcodeslen : (TwoSat.codes original).length ≤ 2 * original.length)
    (hspeciallen : (TwoSat.codes special).length ≤ 2 * special.length) :
    HTB S (onCallerRegisters (LoopHeaders.program false))
      (OuterStart F layout nodes original τ rows special budget depth processed oldOutput)
      (OuterRep F layout nodes original τ rows special budget depth processed oldOutput none
        (Poly.cfg 3 special.length 0)) (6 * special.length + 13) := by
  intro c hpre
  obtain ⟨hg, hc, hr, hz, ho, hbase, hspecial, hcount, hp, halive, hs⟩ := hpre
  have hgeoInner := hgeo.inner
  obtain ⟨hinner, hseedSpecial, hspecialDigits, houterInner⟩ := hgeo
  obtain ⟨hcut, hlabels, hbaseSeed, hseedInner, hinnerOutput⟩ := hinner
  obtain ⟨_, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hcut
  have hheader := onCallerRegisters_htb (LoopHeaders.program_spec false
    (S := S) (base := layout.outerDigits) (depth := special.length)
    (memory := c.mem) (out := c.out) (by omega))
  obtain ⟨c', time, he, hpost, ht⟩ := hheader c
    ⟨hg.outerDigits, hcount, rfl, rfl⟩
  obtain ⟨hheaderGlobals, hm, hds, hout⟩ := hpost
  change c'.mem = ArrayBlocks.prefixMemory c.mem layout.outerDigits
    (List.replicate special.length 0) special.length at hm
  change Arr c'.mem layout.outerDigits (List.replicate special.length 0) at hds
  change c'.out = c.out at hout
  simp only [LoopHeaders.Globals, LoopHeaders.inputBase, LoopHeaders.inputDepth,
    LoopHeaders.controlBase, LoopHeaders.controlDepth, Bool.false_eq_true, ite_false,
    registerView] at hheaderGlobals
  have hglobals : Compiler.Globals layout nodes original.length budget depth
      (registerView callerRegister c') := by
    apply Compiler.globals_reg_frame hg
    intro r hr
    have hcases : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 220 ∨
        r = 222 ∨ r = 223 ∨ r = 225 ∨ r = 226 ∨ r = 300 ∨ r = 344 ∨ r = 345 ∨
        r = 350 ∨ r = 400 ∨ r = 406 ∨ r = 430 ∨ r = 433 ∨ r = 434 ∨ r = 435 := by
      simpa [Compiler.globalRegisters] using hr
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))
  have hmem (a : ℕ) (ha : OutsideCells layout.outerDigits special.length a) :
      c'.mem a = c.mem a := by
    rw [hm]
    exact ArrayBlocks.prefixMemory_outside
      (by simpa only [List.length_replicate, OutsideCells] using ha)
  have hcodes : Arr c'.mem layout.formula (TwoSat.codes original) := by
    intro i hi
    exact (hmem _ (by unfold OutsideCells; omega)).trans (hc i hi)
  have href : TruthTable c'.mem layout.reference nodes τ := by
    intro u hu
    exact (hmem _ (by unfold OutsideCells; omega)).trans (hr u hu)
  have hbase' : Arr c'.mem layout.baseActive (maskWords rows) := by
    intro i hi
    have hi' : i < original.length := by simpa only [maskWords_length, hrows] using hi
    exact (hmem _ (by unfold OutsideCells; omega)).trans (hbase i hi)
  have hspecial' : Arr c'.mem layout.special (TwoSat.codes special) := by
    intro i hi
    exact (hmem _ (by unfold OutsideCells; omega)).trans (hspecial i hi)
  have hz' : Compiler.StageZero (Flow.hornSeparator F) c' := by
    intro r hr
    exact (callerRegister_exec_zero he r).trans (hz r hr)
  have hcfg : Poly.cfg 3 special.length 0 = List.replicate special.length 0 := by
    simp [Poly.cfg, List.map_const']
  refine ⟨c', time, he, ⟨⟨hglobals, hcodes, href, hz', hout.trans ho, hbase', hspecial',
    hheaderGlobals.2.2.1, ?_, hheaderGlobals.2.2.2.2,
    by simpa only [hcfg] using hds, by simp,
    (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hcount,
    (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hp,
    (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans halive⟩,
    (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hs⟩, ht⟩
  simpa only [hcfg, List.length_replicate] using hheaderGlobals.2.2.2.1

end STACS2027.Runtimes.BoundedCost
