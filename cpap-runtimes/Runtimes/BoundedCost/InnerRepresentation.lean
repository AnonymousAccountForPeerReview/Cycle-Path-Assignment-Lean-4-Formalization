module

public import Runtimes.BoundedCost.PathRegisterFrame
public import Runtimes.BoundedCost.CompilerProgram
public import Runtimes.BoundedCost.EncodedIterative
import Mathlib.Tactic

/-! Concrete snapshots and success state for the inner ternary path scan. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

@[mk_iff] structure InnerGeometry (S : ℕ) (layout : CompilerLayout) (nodes clauses depth : ℕ) : Prop where
  cut : LeastCutGeometry S layout.span layout.formula layout.active layout.candidate layout.reference
    layout.forced layout.labels layout.edgeInput nodes clauses
  labelsSnapshot : layout.labels + 2 * nodes ≤ layout.baseActive
  activeForcedSnapshot : layout.baseActive + clauses ≤ layout.seedForced
  snapshotDigits : layout.seedForced + 2 * nodes ≤ layout.innerDigits
  digitsOutput : layout.innerDigits + depth ≤ layout.edgeInput

def InnerMemoryFrame (layout : CompilerLayout) (nodes clauses depth a : ℕ) : Prop :=
  SearchNodeMemoryFrame layout.span layout.active layout.candidate layout.forced
    layout.labels layout.edgeInput nodes clauses a ∧ OutsideCells layout.innerDigits depth a

def InnerAnswerRep (layout : CompilerLayout) (nodes : ℕ) : Option Assignment → Config → Prop
  | none, c => c.reg (callerRegister nodeSuccess) = 0
  | some σ, c => c.reg (callerRegister nodeSuccess) = 1 ∧ TruthTable c.mem layout.candidate nodes σ

def InnerBasic (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (depth globalBudget deleted : ℕ) (activeBits forcedBits : List ℕ)
    (oldOutput : List ℕ) (digits : List ℕ) (c : Config) : Prop :=
  PathBasic F layout nodes original τ digits oldOutput c ∧
  PathRestore.Globals layout.active layout.forced layout.baseActive layout.seedForced original.length
    (2 * nodes) globalBudget deleted (registerView callerRegister c) ∧
  Arr c.mem layout.baseActive activeBits ∧ Arr c.mem layout.seedForced forcedBits ∧
  c.reg (innerCallerRegister rOB) = layout.innerDigits ∧
  c.reg (innerCallerRegister rOL) = digits.length ∧ c.reg (innerCallerRegister rK) = 3 ∧
  digits.length = depth

def InnerRep (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (depth globalBudget deleted : ℕ) (activeBits forcedBits : List ℕ)
    (oldOutput : List ℕ) (oldMemory : ℕ → ℕ) (answer : Option Assignment)
    (digits : List ℕ) (c : Config) : Prop :=
  InnerBasic F layout nodes original τ depth globalBudget deleted activeBits forcedBits oldOutput digits c ∧
  InnerAnswerRep layout nodes answer c ∧
  SameOn (InnerMemoryFrame layout nodes original.length depth) oldMemory c.mem

end STACS2027.Runtimes.BoundedCost
