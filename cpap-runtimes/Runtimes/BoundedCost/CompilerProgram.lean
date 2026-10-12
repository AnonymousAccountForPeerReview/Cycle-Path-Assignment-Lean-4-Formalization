module

public import Runtimes.BoundedCost.CompilerInit
public import Runtimes.BoundedCost.ReferenceCopyRAM
public import Runtimes.BoundedCost.PrefixMaskRAM
public import Runtimes.BoundedCost.PrefixCheckRAM
public import Runtimes.BoundedCost.CompressionSeedRAM
public import Runtimes.BoundedCost.PathRestore
public import Runtimes.BoundedCost.PathControl
public import Runtimes.BoundedCost.SearchNodeRAM
public import Runtimes.BoundedCost.LoopHeaders
public import Runtimes.BoundedCost.TernaryStateControl
import Mathlib.Tactic

/-! One fixed RAM program performs iterative compression, both ternary scans,
all annotated nodes, and normalized certificate output. Its only inserted
algorithm is the cited flow program. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Compiler

open STACS2027 STACS2027.RAM STACS2027.RAM.P3

abbrev alive : ℕ := 347
abbrev prefixIndex : ℕ := 490
abbrev negativeValue : ℕ := 491
abbrev branchExcess : ℕ := 492
abbrev prefixExcess : ℕ := 493
abbrev trivialExcess : ℕ := 494
abbrev processed : ℕ := 224
abbrev budget : ℕ := 225

def pathBody (F : Stmt) : Stmt :=
  .ifz (callerRegister nodeSuccess)
    (.seq (onCallerRegisters PathRestore.program)
      (renamedPathControl callerRegister (searchNode F))) .skip

def innerScan (F : Stmt) : Stmt :=
  .seq (onCallerRegisters (LoopHeaders.program true))
    (renamedTernaryScan innerCallerRegister (pathBody F))

def outerBody (F : Stmt) : Stmt :=
  .ifz (callerRegister nodeSuccess)
    (.seq (onCallerRegisters compressionSeedSetup)
      (.seq (onCallerRegisters (.sub branchExcess seedDeleted budget))
        (.ifz (callerRegister branchExcess) (innerScan F) .skip))) .skip

def compression (F : Stmt) : Stmt :=
  .seq (.const (callerRegister nodeSuccess) 0)
    (.seq (onCallerRegisters compressionSetupScan)
      (.seq (onCallerRegisters (LoopHeaders.program false))
        (.seq (renamedTernaryScan callerRegister (outerBody F))
          (.ifz (callerRegister nodeSuccess) (.const (callerRegister alive) 0) .skip))))

def prefixBody (F : Stmt) : Stmt :=
  .ifz (callerRegister alive) .skip
    (.seq (onCallerRegisters (inc processed))
      (.seq prefixCheckCaller
        (.seq (onCallerRegisters (.sub prefixExcess scanUnsatisfied budget))
          (.ifz (callerRegister prefixExcess) .skip (compression F)))))

def prefixLoop (F : Stmt) : Stmt :=
  forUp (callerRegister prefixIndex) (callerRegister scanClauseCount) (prefixBody F)

def negativeOutput : Stmt := onCallerRegisters
  (.seq (.const negativeValue 0) (.write negativeValue))

def positiveOutput : Stmt := onCallerRegisters Certificate.outputCertificate

def finish : Stmt := .ifz (callerRegister alive) negativeOutput positiveOutput

def properBudget (F : Stmt) : Stmt :=
  .seq (.const (callerRegister alive) 1) (.seq (prefixLoop F) finish)

def program (F : Stmt) (constant : ℕ) : Stmt :=
  .seq (onCallerRegisters (CompilerInit.program constant))
    (.seq (onCallerRegisters (.sub trivialExcess scanClauseCount budget))
      (.ifz (callerRegister trivialExcess) positiveOutput (properBudget F)))

end STACS2027.Runtimes.BoundedCost.Compiler
