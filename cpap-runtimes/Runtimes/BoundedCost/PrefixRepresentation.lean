module

public import Runtimes.BoundedCost.CompilerFrames
public import Runtimes.BoundedCost.PrefixCheckRAM
import Mathlib.Tactic

/-! The physical prefix loop represents either a current dense assignment or
an absorbing negative result. All fixed input metadata remains available. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Compiler

open STACS2027 STACS2027.RAM Complexity.SAT

def PrefixBasic (F : Stmt) (layout : CompilerLayout) (f : CNF) (k depth : ℕ)
    (oldOutput : List ℕ) (c : Config) : Prop :=
  Globals layout (2 * f.length + 1) f.length k depth (registerView callerRegister c) ∧
    Arr c.mem layout.formula (TwoSat.codes f) ∧ StageZero (Flow.hornSeparator F) c ∧
    c.out = oldOutput

def PrefixAnswerRep (layout : CompilerLayout) (n count : ℕ) : Option Assignment → Config → Prop
  | none, c => c.reg (callerRegister alive) = 0
  | some σ, c => c.reg (callerRegister alive) = 1 ∧
      c.reg (callerRegister processed) = count ∧ TruthTable c.mem layout.candidate n σ

def PrefixRep (F : Stmt) (layout : CompilerLayout) (f : CNF) (k depth : ℕ)
    (oldOutput : List ℕ) (count : ℕ) (state : Option Assignment) (c : Config) : Prop :=
  PrefixBasic F layout f k depth oldOutput c ∧
    PrefixAnswerRep layout (2 * f.length + 1) count state c

theorem prefixRep_indep (F : Stmt) (layout : CompilerLayout) (f : CNF) (k depth : ℕ)
    (oldOutput : List ℕ) (count : ℕ) (state : Option Assignment) :
    Indep [callerRegister prefixIndex, rT]
      (PrefixRep F layout f k depth oldOutput count state) := by
  intro c c' hreg hp
  rcases hp with ⟨⟨hg, hc, hz, ho⟩, ha⟩
  have hg' : Globals layout (2 * f.length + 1) f.length k depth
      (registerView callerRegister c') := by
    apply globals_reg_frame hg
    intro r hr
    apply hreg.reg
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
    constructor
    · intro he
      have he' := callerRegister_injective he
      subst r
      simp [globalRegisters, prefixIndex] at hr
    · have : 0 < r := by
        have hs : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 220 ∨
          r = 222 ∨ r = 223 ∨ r = 225 ∨ r = 226 ∨ r = 300 ∨ r = 344 ∨ r = 345 ∨
          r = 350 ∨ r = 400 ∨ r = 406 ∨ r = 430 ∨ r = 433 ∨ r = 434 ∨ r = 435 := by
            simpa [globalRegisters] using hr
        omega
      unfold callerRegister
      simp only [rT]
      omega
  have hz' := (stageZero_reg_indep (Flow.hornSeparator F)
    [callerRegister prefixIndex, rT] (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · decide
      · have he := List.mem_singleton.mp hr
        subst r
        decide)).indep c c' hreg hz
  refine ⟨⟨hg', by simpa only [hreg.mem] using hc, hz', hreg.out.trans ho⟩, ?_⟩
  cases state with
  | none => exact (hreg.reg _ (by decide)).trans ha
  | some σ =>
    exact ⟨(hreg.reg _ (by decide)).trans ha.1,
      (hreg.reg _ (by decide)).trans ha.2.1, by simpa only [hreg.mem] using ha.2.2⟩

theorem globals_prefixCheck_frame {layout : CompilerLayout} {n m k depth S time : ℕ}
    {c c' : Config} (hg : Globals layout n m k depth (registerView callerRegister c))
    (he : ExecB S prefixCheckCaller c time c') :
    Globals layout n m k depth (registerView callerRegister c') := by
  apply globals_reg_frame hg
  intro r hr
  have hs : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 220 ∨
      r = 222 ∨ r = 223 ∨ r = 225 ∨ r = 226 ∨ r = 300 ∨ r = 344 ∨ r = 345 ∨
      r = 350 ∨ r = 400 ∨ r = 406 ∨ r = 430 ∨ r = 433 ∨ r = 434 ∨ r = 435 := by
    simpa [globalRegisters] using hr
  apply he.reg_frame
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact not_mem_renameRegisters_wregs callerRegister_injective (by decide)

end STACS2027.Runtimes.BoundedCost.Compiler
