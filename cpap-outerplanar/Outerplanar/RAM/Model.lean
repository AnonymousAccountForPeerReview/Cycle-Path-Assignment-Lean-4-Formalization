module

public import Init
import Lean.Elab.Tactic.Omega

/-!
# A unit-cost random-access machine

(The definitions and theorems are copied verbatim from the Section 6 formalization,
`ApproximationHardness/RAM/Model.lean`; only the wording of this module documentation differs: it says
"after exactly `t` steps" for `Computes`, where Section 6 says "within `t` steps".)

The machine has registers `reg : Nat → Nat`, a memory `mem : Nat → Nat` and a
write-only output list. Its programs are built from the instructions of the
classical RAM of ANONYMIZED and ANONYMIZED (1973) with uniform cost: load a constant,
add, truncated subtract, indirect load `d := mem[reg a]`, indirect store
`mem[reg a] := reg b`, and writing a register to the output; and from
sequencing, a branch on zero, and a loop `while reg a ≠ 0`. There is no
multiplication or division.

`Exec s c t c'`: the program `s` started in `c` halts in `c'` after exactly `t`
steps, where every instruction, every branch test and every loop test is one
step. `initial input` holds the input in the memory cells `0, …, |input| - 1`;
everything else is `0`. `Computes s input output t` says that `s` halts on
`input` after exactly `t` steps with output `output`.
-/

@[expose] public section

namespace STACS2027.RAM

/-- A configuration of the machine. -/
structure Config where
  reg : Nat → Nat
  mem : Nat → Nat
  out : List Nat

/-- Programs. -/
inductive Stmt where
  | skip
  | const (d c : Nat)
  | add (d a b : Nat)
  | sub (d a b : Nat)
  | load (d a : Nat)
  | store (a b : Nat)
  | write (a : Nat)
  | seq (s t : Stmt)
  | ifz (a : Nat) (s t : Stmt)
  | loop (a : Nat) (body : Stmt)

/-- Set register `d` to `v`. -/
def Config.setReg (c : Config) (d v : Nat) : Config :=
  ⟨fun i => if i = d then v else c.reg i, c.mem, c.out⟩

/-- Set memory cell `a` to `v`. -/
def Config.setMem (c : Config) (a v : Nat) : Config :=
  ⟨c.reg, fun i => if i = a then v else c.mem i, c.out⟩

/-- Append `v` to the output. -/
def Config.emit (c : Config) (v : Nat) : Config := ⟨c.reg, c.mem, c.out ++ [v]⟩

/-- `Exec s c t c'`: from `c`, the program `s` halts in `c'` after exactly `t` unit-cost steps. -/
inductive Exec : Stmt → Config → Nat → Config → Prop where
  | skip (c : Config) : Exec .skip c 1 c
  | const (d v : Nat) (c : Config) : Exec (.const d v) c 1 (c.setReg d v)
  | add (d a b : Nat) (c : Config) : Exec (.add d a b) c 1 (c.setReg d (c.reg a + c.reg b))
  | sub (d a b : Nat) (c : Config) : Exec (.sub d a b) c 1 (c.setReg d (c.reg a - c.reg b))
  | load (d a : Nat) (c : Config) : Exec (.load d a) c 1 (c.setReg d (c.mem (c.reg a)))
  | store (a b : Nat) (c : Config) : Exec (.store a b) c 1 (c.setMem (c.reg a) (c.reg b))
  | write (a : Nat) (c : Config) : Exec (.write a) c 1 (c.emit (c.reg a))
  | seq {s u : Stmt} {c c₁ c₂ : Config} {t t' : Nat} :
      Exec s c t c₁ → Exec u c₁ t' c₂ → Exec (.seq s u) c (t + t') c₂
  | ifzTrue {a : Nat} {s u : Stmt} {c c' : Config} {t : Nat} :
      c.reg a = 0 → Exec s c t c' → Exec (.ifz a s u) c (t + 1) c'
  | ifzFalse {a : Nat} {s u : Stmt} {c c' : Config} {t : Nat} :
      c.reg a ≠ 0 → Exec u c t c' → Exec (.ifz a s u) c (t + 1) c'
  | loopDone {a : Nat} {body : Stmt} {c : Config} : c.reg a = 0 → Exec (.loop a body) c 1 c
  | loopNext {a : Nat} {body : Stmt} {c c₁ c₂ : Config} {t t' : Nat} :
      c.reg a ≠ 0 → Exec body c t c₁ → Exec (.loop a body) c₁ t' c₂ →
      Exec (.loop a body) c (t + t' + 1) c₂

/-- The initial configuration on `input`: the input in cells `0, …, |input| - 1`, all else `0`. -/
def initial (input : List Nat) : Config := ⟨fun _ => 0, fun i => input.getD i 0, []⟩

/-- `s` halts on `input` after `time` steps with output `output`. -/
def Computes (s : Stmt) (input output : List Nat) (time : Nat) : Prop :=
  ∃ c, Exec s (initial input) time c ∧ c.out = output

/-- The machine is deterministic: the halting time and the final configuration are unique. -/
theorem Exec.det {s : Stmt} {c c' c'' : Config} {t t' : Nat} (h : Exec s c t c') (h' : Exec s c t' c'') :
    t = t' ∧ c' = c'' := by
  induction h generalizing t' c'' with
  | skip => cases h'; exact ⟨rfl, rfl⟩
  | const => cases h'; exact ⟨rfl, rfl⟩
  | add => cases h'; exact ⟨rfl, rfl⟩
  | sub => cases h'; exact ⟨rfl, rfl⟩
  | load => cases h'; exact ⟨rfl, rfl⟩
  | store => cases h'; exact ⟨rfl, rfl⟩
  | write => cases h'; exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h' with
    | seq h₁ h₂ =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₁
      obtain ⟨rfl, rfl⟩ := ih₂ h₂
      exact ⟨rfl, rfl⟩
  | ifzTrue ha _ ih =>
    cases h' with
    | ifzTrue _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
    | ifzFalse hb _ => exact absurd ha hb
  | ifzFalse ha _ ih =>
    cases h' with
    | ifzTrue hb _ => exact absurd hb ha
    | ifzFalse _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
  | loopDone ha =>
    cases h' with
    | loopDone _ => exact ⟨rfl, rfl⟩
    | loopNext hb _ _ => exact absurd ha hb
  | loopNext ha _ _ ih₁ ih₂ =>
    cases h' with
    | loopDone hb => exact absurd hb ha
    | loopNext _ h₁ h₂ =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₁
      obtain ⟨rfl, rfl⟩ := ih₂ h₂
      exact ⟨rfl, rfl⟩

end STACS2027.RAM
