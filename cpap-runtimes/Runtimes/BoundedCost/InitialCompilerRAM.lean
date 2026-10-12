module

public import Runtimes.BoundedCost.PrefixLoopRAM
import Mathlib.Tactic

/-! Actual compiler initialization copies the input formula and builds its
all-false assignment while retaining the reusable flow-register invariant. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Compiler

open STACS2027 STACS2027.RAM Complexity.SAT

theorem initialCompilerRAM_spec {F : Stmt} {constant k S : ℕ} {f : CNF}
    (hf : SolverDomain f) (hspace : (compilerLayout constant f.length k).space ≤ S) :
    HTB S (onCallerRegisters (CompilerInit.program constant))
      (fun c => c = initial (a2In f k))
      (fun c => PrefixBasic F (compilerLayout constant f.length k) f k
          (min k f.length + 1) [] c ∧
        TruthTable c.mem (compilerLayout constant f.length k).candidate
          (2 * f.length + 1) (fun _ => false) ∧
        c.reg (callerRegister processed) = 0)
      (400 + 5 * (constant + 1) + 80 * (f.length + 1)) := by
  let input := a2In f k
  let memory := (initial input).mem
  have hcodes : Arr memory 2 (TwoSat.codes f) := by
    intro i hi
    change (k :: f.length :: TwoSat.codes f).getD (2 + i) 0 = (TwoSat.codes f)[i]
    rw [show 2 + i = (i + 1) + 1 by omega]
    simp [List.getD_eq_getElem?_getD, hi]
  have hinit := onCallerRegisters_htb (CompilerInit.program_spec
    (memory := memory) (out := []) (TwoSat.length_codes hf) hspace
    (by simp [memory, input, initial, a2In])
    (by simp [memory, input, initial, a2In]) hcodes)
  intro c hc
  subst c
  obtain ⟨c', time, he, hp, ht⟩ := hinit (initial input) ⟨rfl, rfl⟩
  have htables := initialized_tables (constant := constant) (k := k) hf memory
  have hz : StageZero (Flow.hornSeparator F) (initial input) := by intro r hr; rfl
  have hg := globals_of_initialized hp.1
  have hmem : c'.mem = CompilerInit.initializedMemory constant f.length k memory
      (TwoSat.codes f) := hp.2.1
  have hpcount : (registerView callerRegister c').reg processed = 0 := hp.1.2.1.2.2.2.2.2.2.2.2.2.2
  refine ⟨c', time, he, ⟨⟨hg, ?_, hz.caller_exec he, hp.2.2⟩, ?_, hpcount⟩, ht⟩
  · rw [hmem]
    exact htables.1
  · rw [hmem]
    exact htables.2

theorem initialPrefixRep_alive {F : Stmt} {layout : CompilerLayout} {f : CNF} {k depth : ℕ}
    {c : Config} (hb : PrefixBasic F layout f k depth [] c)
    (htruth : TruthTable c.mem layout.candidate (2 * f.length + 1) (fun _ => false))
    (hp : c.reg (callerRegister processed) = 0) :
    PrefixRep F layout f k depth [] 0 (some (fun _ => false))
      (c.setReg (callerRegister alive) 1) := by
  refine ⟨?_, ?_⟩
  · rcases hb with ⟨hg, hc, hz, ho⟩
    refine ⟨?_, hc, ?_, ho⟩
    · exact (globals_reg_indep layout (2 * f.length + 1) f.length k depth
        [callerRegister alive] (by
          intro r hr
          simp only [List.mem_singleton]
          intro h
          have he := callerRegister_injective h
          subst r
          simp [globalRegisters, alive] at hr)).setReg (by simp) 1 hg
    · exact (stageZero_reg_indep (Flow.hornSeparator F) [callerRegister alive]
        (by intro r hr; have he := List.mem_singleton.mp hr; subst r; decide)).setReg (by simp) 1 hz
  · exact ⟨by simp, by simpa +decide [setReg_reg, callerRegister, alive, processed] using hp,
      htruth⟩

end STACS2027.Runtimes.BoundedCost.Compiler
