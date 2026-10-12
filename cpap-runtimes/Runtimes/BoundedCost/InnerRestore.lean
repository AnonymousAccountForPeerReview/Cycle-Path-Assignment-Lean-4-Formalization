module

public import Runtimes.BoundedCost.InnerTransport
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem innerBasic_after_restore {F : Stmt} {S time nodes depth globalBudget deleted : ℕ}
    {layout : CompilerLayout} {original : CNF} {τ : Assignment} {digits oldOutput : List ℕ}
    {c₀ c : Config} {rows : List (Bool × Clause)} {forced : ℕ → Bool}
    (hgeo : InnerGeometry S layout nodes original.length depth)
    (hlen : rows.length = original.length)
    (hcodeslen : (TwoSat.codes original).length ≤ 2 * original.length)
    (hb : InnerBasic F layout nodes original τ depth globalBudget deleted
      (maskWords rows) (forcedWords nodes forced) oldOutput digits c₀)
    (he : ExecB S (onCallerRegisters PathRestore.program) c₀ time c)
    (hrestore : PathRestore.Globals layout.active layout.forced layout.baseActive layout.seedForced
      original.length (2 * nodes) globalBudget deleted (registerView callerRegister c))
    (hmem : c.mem = PathRestore.restoredMemory c₀.mem layout.active layout.forced
      (maskWords rows) (forcedWords nodes forced)) (hout : c.out = c₀.out) :
    InnerBasic F layout nodes original τ depth globalBudget deleted
      (maskWords rows) (forcedWords nodes forced) oldOutput digits c ∧
    MaskTable c.mem layout.active rows ∧ ForcedTable c.mem layout.forced nodes forced ∧
    SameOn (SearchNodeMemoryFrame layout.span layout.active layout.candidate layout.forced
      layout.labels layout.edgeInput nodes original.length) c₀.mem c.mem := by
  obtain ⟨hpath, _, ha, hf, hob, hol, hk, hlength⟩ := hb
  obtain ⟨hcut, hlabels, hbase, hseed, hdigits⟩ := hgeo
  obtain ⟨_, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hcut
  have hregs (r : ℕ) (hr : r ∈ pathBasicRegisters) :
      c.reg (callerRegister r) = c₀.reg (callerRegister r) := by
    simp only [pathBasicRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))
  have hcode : Arr c.mem layout.formula (TwoSat.codes original) := by
    rw [hmem]
    exact pathRestore_array hpath.2.1 (by
      intro i hi
      unfold PathRestoreMemoryFrame OutsideCells
      omega)
  have href : TruthTable c.mem layout.reference nodes τ := by
    rw [hmem]
    exact pathRestore_truth hpath.2.2.1 (by
      intro i hi
      unfold PathRestoreMemoryFrame OutsideCells
      omega)
  have hds : Arr c.mem layout.innerDigits digits := by
    rw [hmem]
    exact pathRestore_array hpath.2.2.2.2.2.2.2 (by
      intro i hi
      unfold PathRestoreMemoryFrame OutsideCells
      omega)
  have hz (r : ℕ) (hr : r ∉ wregs (Flow.hornSeparator F)) : c.reg (Flow.rl 0 r) = 0 :=
    (callerRegister_exec_zero he r).trans (hpath.2.2.2.1 r hr)
  have hpath' := pathBasic_transport hpath hregs hcode href hds hz hout
  have ha' : Arr c.mem layout.baseActive (maskWords rows) := by
    rw [hmem]
    exact pathRestore_array ha (by
      intro i hi
      simp only [maskWords_length, hlen] at hi
      unfold PathRestoreMemoryFrame OutsideCells
      omega)
  have hf' : Arr c.mem layout.seedForced (forcedWords nodes forced) := by
    rw [hmem]
    exact pathRestore_array hf (by
      intro i hi
      simp only [forcedWords_length] at hi
      unfold PathRestoreMemoryFrame OutsideCells
      omega)
  have hobb : c.reg (innerCallerRegister rOB) = layout.innerDigits := by
    simpa only [innerCallerRegister_base] using
      (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans
        (by simpa only [innerCallerRegister_base] using hob)
  have holl : c.reg (innerCallerRegister rOL) = digits.length := by
    simpa only [innerCallerRegister_depth] using
      (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans
        (by simpa only [innerCallerRegister_depth] using hol)
  have hkk : c.reg (innerCallerRegister rK) = 3 := by
    simpa only [innerCallerRegister_radix] using
      (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans
        (by simpa only [innerCallerRegister_radix] using hk)
  refine ⟨⟨hpath', hrestore, ha', hf', hobb, holl, hkk, hlength⟩, ?_⟩
  have ht := pathRestore_tables c₀.mem layout.active layout.forced nodes rows forced (Or.inl (by omega))
  refine ⟨by simpa only [← hmem] using ht.1, by simpa only [← hmem] using ht.2.1, ?_⟩
  intro a ha
  rw [hmem]
  exact ht.2.2 a (by simpa only [hlen] using ⟨ha.2.1, ha.2.2⟩)

end STACS2027.Runtimes.BoundedCost
