module

public import Runtimes.BoundedCost.ActualInnerRAM
public import Runtimes.BoundedCost.CompilerFrames
import Mathlib.Tactic

/-! Concrete compiler metadata and read-only tables provide the complete inner
scan's initial state and remain available after its actual execution. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def innerDigitWords (memory : ℕ → ℕ) (base depth : ℕ) : List ℕ :=
  List.ofFn fun i : Fin depth => memory (base + i.val)

@[simp] theorem innerDigitWords_length (memory : ℕ → ℕ) (base depth : ℕ) :
    (innerDigitWords memory base depth).length = depth := by simp [innerDigitWords]

theorem innerDigitWords_array (memory : ℕ → ℕ) (base depth : ℕ) :
    Arr memory base (innerDigitWords memory base depth) := by
  intro i hi
  simp [innerDigitWords]

theorem innerStart_of_globals {F : Stmt} {layout : CompilerLayout} {nodes depth globalBudget deleted : ℕ}
    {original : CNF} {τ : Assignment} {rows : List (Bool × Clause)} {forced : ℕ → Bool}
    {oldOutput : List ℕ} {oldMemory : ℕ → ℕ} {c : Config}
    (hg : Compiler.Globals layout nodes original.length globalBudget depth (registerView callerRegister c))
    (hdeleted : c.reg (callerRegister PathRestore.specialDeleted) = deleted)
    (hcodes : Arr c.mem layout.formula (TwoSat.codes original))
    (href : TruthTable c.mem layout.reference nodes τ)
    (hactive : Arr c.mem layout.baseActive (maskWords rows))
    (hforced : Arr c.mem layout.seedForced (forcedWords nodes forced))
    (hzero : ∀ r, r ∉ wregs (Flow.hornSeparator F) → c.reg (Flow.rl 0 r) = 0)
    (hout : c.out = oldOutput) (hsuccess : c.reg (callerRegister nodeSuccess) = 0)
    (hframe : SameOn (InnerMemoryFrame layout nodes original.length depth) oldMemory c.mem) :
    InnerStart F layout nodes original τ depth globalBudget deleted
      (maskWords rows) (forcedWords nodes forced) oldOutput oldMemory c := by
  refine ⟨innerDigitWords c.mem layout.innerDigits depth, ?_, by simp, ?_, hactive, hforced, hsuccess, hframe⟩
  · exact ⟨hg.leastCut, hcodes, href, hzero, hout, hg.innerDigits,
      by simpa only [innerDigitWords_length, registerView, pathDepth] using hg.depth,
      innerDigitWords_array c.mem layout.innerDigits depth⟩
  · exact ⟨hg.active, hg.forced, hg.baseActive, hg.seedForced, hg.clauses, hg.truthLength,
      hg.budget, hdeleted⟩

theorem innerGeometry_compilerLayout (constant clauses budget S : ℕ)
    (hspace : (compilerLayout constant clauses budget).space ≤ S) :
    InnerGeometry S (compilerLayout constant clauses budget) (2 * clauses + 1) clauses
      (min budget clauses + 1) := by
  constructor
  · constructor <;> dsimp [compilerLayout] at hspace ⊢ <;> omega
  all_goals dsimp [compilerLayout]; omega

theorem innerGeometry_readOnlyGap {S nodes clauses depth a : ℕ} {layout : CompilerLayout}
    (hgeo : InnerGeometry S layout nodes clauses depth)
    (ha : layout.labels + 2 * nodes ≤ a ∧ a < layout.innerDigits) :
    InnerMemoryFrame layout nodes clauses depth a := by
  obtain ⟨hcut, hlabels, hbase, hseed, hdigits⟩ := hgeo
  obtain ⟨hh, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hcut
  unfold InnerMemoryFrame SearchNodeMemoryFrame LeastCutFrame OutsideCells
  omega

namespace Compiler

theorem globals_actualInner_frame {F : Stmt} {layout : CompilerLayout} {n m k depth S time : ℕ}
    {c c' : Config} (h : Globals layout n m k depth (registerView callerRegister c))
    (he : ExecB S (innerScan F) c time c') :
    Globals layout n m k depth (registerView callerRegister c') := by
  apply globals_reg_frame h
  intro r hr
  have hcases : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 220 ∨
      r = 222 ∨ r = 223 ∨ r = 225 ∨ r = 226 ∨ r = 300 ∨ r = 344 ∨ r = 345 ∨
      r = 350 ∨ r = 400 ∨ r = 406 ∨ r = 430 ∨ r = 433 ∨ r = 434 ∨ r = 435 := by
    simpa [globalRegisters] using hr
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply actualInner_registerFrame he <;> decide

end Compiler

end STACS2027.Runtimes.BoundedCost
