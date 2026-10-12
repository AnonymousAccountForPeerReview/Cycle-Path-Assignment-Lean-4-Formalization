module

public import Runtimes.BoundedCost.CompilerState
public import Runtimes.BoundedCost.PathRegisterFrame
import Mathlib.Tactic

/-! The fixed caller metadata survives all search operations and disjoint
ternary controls; the relocated flow registers remain reusable. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Compiler

open STACS2027 STACS2027.RAM

def globalRegisters : List ℕ :=
  [200, 201, 202, 203, 204, 220, 222, 223, 225, 226, 300, 344, 345, 350,
    400, 406, 430, 433, 434, 435]

theorem globals_reg_frame {layout : CompilerLayout} {n m k depth : ℕ} {c c' : Config}
    (h : Globals layout n m k depth (registerView callerRegister c))
    (hreg : ∀ r ∈ globalRegisters, c'.reg (callerRegister r) = c.reg (callerRegister r)) :
    Globals layout n m k depth (registerView callerRegister c') := by
  rcases h with ⟨hf, hm, ha, hc, hr, hn, hforced, hl, hk, hom, he, hi, hd, hregion,
    hspan, htruth, hspecial, ho, hbase, hseed⟩
  constructor
  all_goals exact (hreg _ (by decide)).trans (by assumption)

theorem globals_reg_indep (layout : CompilerLayout) (n m k depth : ℕ) (W : List ℕ)
    (hW : ∀ r ∈ globalRegisters, callerRegister r ∉ W) :
    RegIndep W (fun c => Globals layout n m k depth (registerView callerRegister c)) := by
  intro c c' hreg hg
  exact globals_reg_frame hg (fun r hr => hreg _ (hW r hr))

def StageZero (program : Stmt) (c : Config) : Prop :=
  ∀ r, r ∉ wregs program → c.reg (Flow.rl 0 r) = 0

theorem stageZero_reg_indep (program : Stmt) (W : List ℕ)
    (hW : ∀ r ∈ W, r % 4 ≠ 0) : RegIndep W (StageZero program) := by
  intro c c' hreg hz r hr
  have hout : Flow.rl 0 r ∉ W := by
    intro h
    exact hW _ h (Flow.rl_mod (by decide) r)
  exact (hreg _ hout).trans (hz r hr)

theorem StageZero.caller_exec {program s : Stmt} {S time : ℕ} {c c' : Config}
    (h : StageZero program c) (he : ExecB S (onCallerRegisters s) c time c') :
    StageZero program c' := by
  intro r hr
  exact (callerRegister_exec_zero he r).trans (h r hr)

theorem globals_actualPath_frame {F : Stmt} {layout : CompilerLayout} {n m k depth S time : ℕ}
    {c c' : Config} (h : Globals layout n m k depth (registerView callerRegister c))
    (he : ExecB S (renamedPathControl callerRegister (searchNode F)) c time c') :
    Globals layout n m k depth (registerView callerRegister c') := by
  apply globals_reg_frame h
  intro r hr
  have hcases : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 220 ∨
      r = 222 ∨ r = 223 ∨ r = 225 ∨ r = 226 ∨ r = 300 ∨ r = 344 ∨ r = 345 ∨
      r = 350 ∨ r = 400 ∨ r = 406 ∨ r = 430 ∨ r = 433 ∨ r = 434 ∨ r = 435 := by
    simpa [globalRegisters] using hr
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply actualPath_registerFrame he <;> decide

end STACS2027.Runtimes.BoundedCost.Compiler
