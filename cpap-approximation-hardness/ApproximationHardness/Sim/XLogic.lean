module

public import ApproximationHardness.Sim.XRAM
public import ApproximationHardness.RAM.Spec
import Lean.Elab.Tactic.Omega

/-!
# Running programs of the RAM with bit input and output

`XOk s c c' b`: from `c`, the program `s` halts in `c'` within `b` steps. Composition rules, the
primitive instructions, and a rule for loops with an invariant indexed by the number of iterations.
`ofStmt` embeds the programs of `ApproximationHardness.RAM.Model` without output instructions.
-/

@[expose] public section

namespace STACS2027.Sim

/-- From `c`, `s` halts in `c'` within `b` steps. -/
def XOk (s : XStmt) (c c' : XConfig) (b : Nat) : Prop := ∃ t, XExec s c t c' ∧ t ≤ b

theorem XOk.mono {s : XStmt} {c c' : XConfig} {b b' : Nat} (h : XOk s c c' b) (hb : b ≤ b') : XOk s c c' b' := by
  obtain ⟨t, he, ht⟩ := h; exact ⟨t, he, by omega⟩

theorem XOk.seq {s u : XStmt} {c c₁ c₂ : XConfig} {b₁ b₂ : Nat} (h₁ : XOk s c c₁ b₁) (h₂ : XOk u c₁ c₂ b₂) :
    XOk (.seq s u) c c₂ (b₁ + b₂) := by
  obtain ⟨t, he, ht⟩ := h₁; obtain ⟨t', he', ht'⟩ := h₂; exact ⟨t + t', XExec.seq he he', by omega⟩

theorem XOk.ifzT {a : Nat} {s u : XStmt} {c c' : XConfig} {b : Nat} (ha : c.reg a = 0) (h : XOk s c c' b) :
    XOk (.ifz a s u) c c' (b + 1) := by
  obtain ⟨t, he, ht⟩ := h; exact ⟨t + 1, XExec.ifzTrue ha he, by omega⟩

theorem XOk.ifzF {a : Nat} {s u : XStmt} {c c' : XConfig} {b : Nat} (ha : c.reg a ≠ 0) (h : XOk u c c' b) :
    XOk (.ifz a s u) c c' (b + 1) := by
  obtain ⟨t, he, ht⟩ := h; exact ⟨t + 1, XExec.ifzFalse ha he, by omega⟩

theorem xok_skip (c : XConfig) : XOk .skip c c 1 := ⟨1, XExec.skip c, Nat.le_refl _⟩
theorem xok_const (d v : Nat) (c : XConfig) : XOk (.const d v) c (c.setReg d v) 1 := ⟨1, XExec.const d v c, Nat.le_refl _⟩
theorem xok_add (d a b : Nat) (c : XConfig) : XOk (.add d a b) c (c.setReg d (c.reg a + c.reg b)) 1 :=
  ⟨1, XExec.add d a b c, Nat.le_refl _⟩
theorem xok_sub (d a b : Nat) (c : XConfig) : XOk (.sub d a b) c (c.setReg d (c.reg a - c.reg b)) 1 :=
  ⟨1, XExec.sub d a b c, Nat.le_refl _⟩
theorem xok_load (d a : Nat) (c : XConfig) : XOk (.load d a) c (c.setReg d (c.mem (c.reg a))) 1 :=
  ⟨1, XExec.load d a c, Nat.le_refl _⟩
theorem xok_store (a b : Nat) (c : XConfig) : XOk (.store a b) c (c.setMem (c.reg a) (c.reg b)) 1 :=
  ⟨1, XExec.store a b c, Nat.le_refl _⟩
theorem xok_getBit (d : Nat) (c : XConfig) : XOk (.getBit d) c (c.getBit d) 1 := ⟨1, XExec.getBit d c, Nat.le_refl _⟩
theorem xok_emit (a : Nat) (c : XConfig) : XOk (.emit a) c (c.emit a) 1 := ⟨1, XExec.emit a c, Nat.le_refl _⟩

/-- A loop of `T` iterations: the loop register is nonzero before the iterations and zero after the
last one. -/
theorem xok_loop {a : Nat} {body : XStmt} (T : Nat) (I : Nat → XConfig → Prop) (b : Nat)
    (hstep : ∀ j c, j < T → I j c → c.reg a ≠ 0 ∧ ∃ c', XOk body c c' b ∧ I (j + 1) c')
    (hend : ∀ c, I T c → c.reg a = 0) :
    ∀ c, I 0 c → ∃ c', XOk (.loop a body) c c' (T * (b + 1) + 1) ∧ I T c' := by
  have key : ∀ r j c, j + r = T → I j c → ∃ c', XOk (.loop a body) c c' (r * (b + 1) + 1) ∧ I T c' := by
    intro r
    induction r with
    | zero =>
      intro j c hj hI
      have : j = T := by omega
      subst this
      exact ⟨c, ⟨1, XExec.loopDone (hend c hI), by omega⟩, hI⟩
    | succ r ih =>
      intro j c hj hI
      obtain ⟨ha, c₁, ⟨t, he, ht⟩, hI₁⟩ := hstep j c (by omega) hI
      obtain ⟨c₂, ⟨t', he', ht'⟩, hI₂⟩ := ih (j + 1) c₁ (by omega) hI₁
      exact ⟨c₂, ⟨t + t' + 1, XExec.loopNext ha he he', by rw [Nat.succ_mul]; omega⟩, hI₂⟩
  intro c hc
  exact key T 0 c (by omega) hc

/-! ### Embedding the RAM without output -/

/-- The programs of `ApproximationHardness.RAM.Model`, with `write` dropped. -/
def ofStmt : RAM.Stmt → XStmt
  | .skip => .skip
  | .const d c => .const d c
  | .add d a b => .add d a b
  | .sub d a b => .sub d a b
  | .load d a => .load d a
  | .store a b => .store a b
  | .write _ => .skip
  | .seq s t => .seq (ofStmt s) (ofStmt t)
  | .ifz a s t => .ifz a (ofStmt s) (ofStmt t)
  | .loop a body => .loop a (ofStmt body)

/-- A sequence of programs. -/
def xseqs : List XStmt → XStmt
  | [] => .skip
  | s :: ss => .seq s (xseqs ss)

end STACS2027.Sim
