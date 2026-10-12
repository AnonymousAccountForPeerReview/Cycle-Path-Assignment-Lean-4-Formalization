module

public import Runtimes.BoundedCost.ActualCompressionRAM
public import Runtimes.BoundedCost.CompilerExecution
public import Runtimes.NamedHoles
import Mathlib.Tactic

/-! The full fixed Almost 2-SAT RAM compiler executes iterative compression
and normalized output with the manuscript's uniform fixed-parameter bound.
Its only algorithmic hypothesis is the cited almost-linear flow contract. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem actualCompilerRAM_spec {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ C : ℕ, ∀ (f : CNF) (budget : ℕ), SolverDomain f →
      ∃ output steps,
        ComputesIn (Compiler.program F C) (a2In f budget) output steps
          (compilerLayout C f.length budget).space ∧
        steps ≤ Compiler.compilerExecutionCost C
          (compressionCompilerCost F C f.length budget) f.length ∧ A2Answer f budget output := by
  obtain ⟨C, hcompression⟩ := actualCompressionRAM_spec hF hAL
  refine ⟨C, ?_⟩
  intro f budget hf
  exact Compiler.compilerExecution_spec hf (citedFlowLeastCutFactory_correct hF hAL) le_rfl
    (fun hk i hi τ hold hnew => hcompression hf le_rfl hk hi hold hnew)

theorem compilerExecutionCost_le (F : Stmt) (constant clauses budget : ℕ) :
    Compiler.compilerExecutionCost constant (compressionCompilerCost F constant clauses budget) clauses ≤
      clauses * compilerPrefixTime constant (wregs (Flow.hornSeparator F)).length clauses budget
        (min budget clauses + 1) + compilerFinalTime constant clauses + 8 := by
  have hprefix : compressionCompilerCost F constant clauses budget +
      16 * (2 * clauses + 1) + 116 * clauses + 30 ≤
      compilerPrefixTime constant (wregs (Flow.hornSeparator F)).length clauses budget
        (min budget clauses + 1) := by
    unfold compressionCompilerCost compilerPrefixTime
    omega
  have hmul := Nat.mul_le_mul_left clauses hprefix
  unfold Compiler.compilerExecutionCost compilerFinalTime
  omega

def compilerFptTime (constant registers budget inputLength : ℕ) : ℕ :=
  (compilerUniformConstant constant registers + 8) * 15 ^ budget * (budget + 1) * (inputLength + 1) ^ 3

theorem compilerFptTime_bound (constant registers : ℕ) :
    FPTBound (compilerFptTime constant registers) :=
  ⟨compilerUniformConstant constant registers + 8, fun _ _ => le_rfl⟩

theorem actualCompilerRAM_fpt {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ C : ℕ, Almost2SatSolver (Compiler.program F C)
        (compilerFptTime C (wregs (Flow.hornSeparator F)).length) ∧
      FPTBound (compilerFptTime C (wregs (Flow.hornSeparator F)).length) := by
  obtain ⟨C, hcompiler⟩ := actualCompilerRAM_spec hF hAL
  refine ⟨C, ?_, compilerFptTime_bound _ _⟩
  intro f budget hf
  obtain ⟨output, steps, hrun, htime, hanswer⟩ := hcompiler f budget hf
  have hlength : (a2In f budget).length = 2 * f.length + 2 := by
    simp [a2In, TwoSat.length_codes hf]
  have hgeom : 1 ≤ 15 ^ budget * (budget + 1) * (2 * f.length + 3) ^ 3 :=
    Nat.succ_le_of_lt (by positivity)
  have hraw := compilerExecutionCost_le F C f.length budget
  have htotal := compilerTotalTime_le C (wregs (Flow.hornSeparator F)).length f.length budget
    (min budget f.length + 1) le_rfl
  have htime' : steps ≤ compilerFptTime C (wregs (Flow.hornSeparator F)).length budget
      (a2In f budget).length := by
    rw [hlength]
    unfold compilerFptTime
    have hsmall := htime.trans (hraw.trans (Nat.add_le_add_right htotal 8))
    nlinarith only [hsmall, hgeom]
  have hspace := compilerTotalSpace_le C (wregs (Flow.hornSeparator F)).length f.length budget
  have hspace' : (compilerLayout C f.length budget).space ≤
      compilerFptTime C (wregs (Flow.hornSeparator F)).length budget (a2In f budget).length := by
    rw [hlength]
    unfold compilerFptTime
    nlinarith only [hspace, hgeom]
  obtain ⟨c, he, ho⟩ := hrun
  exact ⟨output, steps, ⟨c, he.mono hspace', ho⟩, htime', hanswer⟩

/-- The named fixed-parameter solver construction is discharged by an actual
RAM program; the flow algorithm is the sole cited algorithmic hypothesis. -/
theorem almostTwoSatFptSolverExists_of_citedFlow {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    AlmostTwoSatFptSolverExists := by
  obtain ⟨C, hsolver, hbound⟩ := actualCompilerRAM_fpt hF hAL
  exact ⟨Compiler.program F C, compilerFptTime C (wregs (Flow.hornSeparator F)).length,
    hsolver, hbound⟩

end STACS2027.Runtimes.BoundedCost
