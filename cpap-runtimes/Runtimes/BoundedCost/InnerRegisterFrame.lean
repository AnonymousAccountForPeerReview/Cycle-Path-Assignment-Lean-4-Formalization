module

public import Runtimes.BoundedCost.InnerIndependence
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem not_mem_actualInner_wregs {F : Stmt} {r : ℕ}
    (hr : 38 ≤ r) (hb : r ∉ wregs contractionBuild) (hd : r ∉ wregs CandidateDecode.program)
    (hs : r ∉ wregs searchScan) (hu : r ∉ wregs annotatedNodeUpdate)
    (hi : r ≠ pathIndex) (hc : r ≠ nodeChoice)
    (hrestore : r ∉ wregs PathRestore.program) (hheader : r ∉ wregs (LoopHeaders.program true))
    (hcontrol : callerRegister r ∉ innerControlWrites) :
    callerRegister r ∉ wregs (Compiler.innerScan F) := by
  have hpath := not_mem_actualPath_wregs hr hb hd hs hu hi hc (F := F)
  have hr' := not_mem_renameRegisters_wregs callerRegister_injective hrestore
  have hh' := not_mem_renameRegisters_wregs callerRegister_injective hheader
  have htemp : callerRegister r ≠ rT := by unfold callerRegister; simp only [rT]; omega
  simp only [innerControlWrites, List.mem_append, List.mem_cons, not_or] at hcontrol
  simp only [Compiler.innerScan, Compiler.pathBody, renamedTernaryScan, renamedTernaryLoop,
    forUp, upLoop, inc, addc, wregs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, not_or]
  tauto

theorem actualInner_registerFrame {F : Stmt} {S time : ℕ} {c₀ c : Config}
    (he : ExecB S (Compiler.innerScan F) c₀ time c)
    {r : ℕ} (hr : 38 ≤ r) (hb : r ∉ wregs contractionBuild) (hd : r ∉ wregs CandidateDecode.program)
    (hs : r ∉ wregs searchScan) (hu : r ∉ wregs annotatedNodeUpdate)
    (hi : r ≠ pathIndex) (hc : r ≠ nodeChoice)
    (hrestore : r ∉ wregs PathRestore.program) (hheader : r ∉ wregs (LoopHeaders.program true))
    (hcontrol : callerRegister r ∉ innerControlWrites) :
    c.reg (callerRegister r) = c₀.reg (callerRegister r) :=
  he.reg_frame (not_mem_actualInner_wregs hr hb hd hs hu hi hc hrestore hheader hcontrol)

end STACS2027.Runtimes.BoundedCost
