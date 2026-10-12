module

public import Runtimes.BoundedCost.CompilerFrames
import Mathlib.Tactic

/-! Protected caller controls survive both nested compression scans. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Compiler

open STACS2027 STACS2027.RAM STACS2027.RAM.P3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem protected_compression_register (F : Stmt) (r : ℕ)
    (hr : r ∈ globalRegisters ++ [prefixIndex, processed, alive]) :
    callerRegister r ∉ wregs (compression F) ∨ r = alive := by
  have hcases : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 220 ∨
      r = 222 ∨ r = 223 ∨ r = 225 ∨ r = 226 ∨ r = 300 ∨ r = 344 ∨ r = 345 ∨
      r = 350 ∨ r = 400 ∨ r = 406 ∨ r = 430 ∨ r = 433 ∨ r = 434 ∨ r = 435 ∨
      r = prefixIndex ∨ r = processed ∨ r = alive := by
    simpa [globalRegisters] using hr
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr =>
    exact Or.inr rfl
  all_goals
    left
    simp +decide only [compression, outerBody, innerScan, pathBody, wregs,
      renamedTernaryScan, renamedTernaryLoop, renamedPathControl, renamedPathControlStep,
      renameRegisters_wregs, onCallerRegisters, forUp, upLoop, List.mem_append,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
    simp only [true_and, and_true]
    apply not_mem_searchNode_wregs <;> decide

theorem not_mem_compression_global (F : Stmt) {r : ℕ} (hr : r ∈ globalRegisters) :
    callerRegister r ∉ wregs (compression F) := by
  rcases protected_compression_register F r (List.mem_append_left _ hr) with h | h
  · exact h
  · subst r
    simp [globalRegisters, alive] at hr

theorem not_mem_compression_prefixIndex (F : Stmt) :
    callerRegister prefixIndex ∉ wregs (compression F) := by
  rcases protected_compression_register F prefixIndex (by simp) with h | h
  · exact h
  · contradiction

theorem not_mem_compression_processed (F : Stmt) :
    callerRegister processed ∉ wregs (compression F) := by
  rcases protected_compression_register F processed (by simp) with h | h
  · exact h
  · contradiction

def innerProtectedRegisters : List ℕ := globalRegisters ++
  [prefixIndex, processed, alive, rOB, rOL, wordIndex, wordCount, seedSpecialCount, seedDeleted]

/-- The inner traversal leaves the global metadata and the outer traversal's
word controls and selected compression branch unchanged. -/
theorem not_mem_innerScan_protected (F : Stmt) {r : ℕ}
    (hr : r ∈ innerProtectedRegisters) : callerRegister r ∉ wregs (innerScan F) := by
  have hcases : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 220 ∨
      r = 222 ∨ r = 223 ∨ r = 225 ∨ r = 226 ∨ r = 300 ∨ r = 344 ∨ r = 345 ∨
      r = 350 ∨ r = 400 ∨ r = 406 ∨ r = 430 ∨ r = 433 ∨ r = 434 ∨ r = 435 ∨
      r = prefixIndex ∨ r = processed ∨ r = alive ∨ r = rOB ∨ r = rOL ∨
      r = wordIndex ∨ r = wordCount ∨ r = seedSpecialCount ∨ r = seedDeleted := by
    simpa [innerProtectedRegisters, globalRegisters] using hr
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp +decide only [innerScan, pathBody, wregs, renamedTernaryScan, renamedTernaryLoop,
      renamedPathControl, renamedPathControlStep, renameRegisters_wregs, onCallerRegisters,
      forUp, upLoop, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false, not_or]
    simp only [true_and, and_true]
    apply not_mem_searchNode_wregs <;> decide

end STACS2027.Runtimes.BoundedCost.Compiler
