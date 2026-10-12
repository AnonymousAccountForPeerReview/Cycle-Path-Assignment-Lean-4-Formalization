module

public import ApproximationHardness.Registered.Framework
public import NPHardness.GlobalGraph
import Lean.Elab.Tactic.Omega

/-!
# The registers of the instance-map machine

The stack machine computing the Theorem 8 graph of a formula uses the `K + 1 = 42`
registers named here. Register `0` holds the input word at the start and the
output word at the end; the others are work registers, several of which are empty
between macro commands (`R.s`, `R.g`, `R.mc`, `R.t1`, `R.t2`, `R.tmp`).
-/

@[expose] public section

namespace STACS2027.Registered

open Complexity
open Complexity.StackMachine (Registers set)

namespace R

/-- Output (initially the input). -/
abbrev out : Reg := 0
/-- Input copy consumed by the first pass. -/
abbrev inA : Reg := 1
/-- Input copy consumed by the second pass. -/
abbrev inB : Reg := 2
/-- Scratch register of the arithmetic commands (empty between macros). -/
abbrev s : Reg := 3
/-- Loop register of `readUnaryC` (empty between macros). -/
abbrev g : Reg := 4
/-- Counter register of `multiply` (empty between macros). -/
abbrev mc : Reg := 5
/-- The number of emitted records (unary). -/
abbrev cnt : Reg := 6
/-- The constant `gadgetWidth k` (unary). -/
abbrev W : Reg := 7
/-- The constant `2` (unary): the length of an edge record. -/
abbrev two : Reg := 8
/-- `variableBound f` (unary), computed by the first pass. -/
abbrev n : Reg := 9
/-- The index of the current clause (unary). -/
abbrev j : Reg := 10
/-- `n + j` (unary, temporary). -/
abbrev nj : Reg := 11
/-- `gadgetWidth k * (n + j)` (unary): the block of the current clause. -/
abbrev bnj : Reg := 12
/-- The codes of the literals read so far, most recent first. -/
abbrev done : Reg := 13
/-- The number of codes on `done` (unary). -/
abbrev dc : Reg := 14
/-- The clause counter of the clause loops (unary). -/
abbrev m : Reg := 15
/-- The literal counter of a clause (unary). -/
abbrev len : Reg := 16
/-- Temporary holding one endpoint number (empty between macros). -/
abbrev tmp : Reg := 17
/-- Temporaries of the comparisons (empty between macros). -/
abbrev t1 : Reg := 18
abbrev t2 : Reg := 19
/-- A copy of `done` being scanned. -/
abbrev scan : Reg := 20
/-- The scan counter, a copy of `dc` (unary). -/
abbrev sc : Reg := 21
/-- The variable of the scanned literal (unary). -/
abbrev sv : Reg := 22
/-- The number of earlier occurrences found by the scan (unary). -/
abbrev cE : Reg := 23
/-- The variables of the literals of the current clause (unary). -/
abbrev v0 : Reg := 24
abbrev v1 : Reg := 25
abbrev v2 : Reg := 26
/-- Their signs, one bit each. -/
abbrev sg0 : Reg := 27
abbrev sg1 : Reg := 28
abbrev sg2 : Reg := 29
/-- Their blocks `gadgetWidth k * var` (unary). -/
abbrev b0 : Reg := 30
abbrev b1 : Reg := 31
abbrev b2 : Reg := 32
/-- Their port endpoints `variableEndpoint port false` and `variableEndpoint port true` (unary). -/
abbrev ef0 : Reg := 33
abbrev et0 : Reg := 34
abbrev ef1 : Reg := 35
abbrev et1 : Reg := 36
abbrev ef2 : Reg := 37
abbrev et2 : Reg := 38
/-- The block `gadgetWidth k * v` of the variable gadget being emitted (unary). -/
abbrev vb : Reg := 39
/-- The counter of the variable-gadget loop (unary). -/
abbrev vc : Reg := 40
/-- The variable read by the first pass (unary). -/
abbrev x : Reg := 41

end R

/-- The variable register, sign register, block register and endpoint registers of slot `i`. -/
def slotV : Nat → Reg
  | 0 => R.v0
  | 1 => R.v1
  | _ => R.v2

def slotS : Nat → Reg
  | 0 => R.sg0
  | 1 => R.sg1
  | _ => R.sg2

def slotB : Nat → Reg
  | 0 => R.b0
  | 1 => R.b1
  | _ => R.b2

def slotE : Nat → Bool → Reg
  | 0, false => R.ef0
  | 0, true => R.et0
  | 1, false => R.ef1
  | 1, true => R.et1
  | _, false => R.ef2
  | _, true => R.et2

/-- A unary register holding `n`. -/
def unary (n : Nat) : List Bool := List.replicate n true

@[simp] theorem unary_length (n : Nat) : (unary n).length = n := by simp [unary]

@[simp] theorem unary_zero : unary 0 = [] := rfl

theorem unary_succ (n : Nat) : unary (n + 1) = true :: unary n := by simp [unary, List.replicate_succ]

theorem unary_add (a b : Nat) : unary (a + b) = unary a ++ unary b := by
  simp [unary]

end STACS2027.Registered
