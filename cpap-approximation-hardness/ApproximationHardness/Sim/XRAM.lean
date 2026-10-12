module

public import ApproximationHardness.RAM.Model
public import ApproximationHardness.Sim.Basic
import Lean.Elab.Tactic.Omega

/-!
# The RAM with a bit input and a bit output

`XStmt` is the unit-cost RAM of `ApproximationHardness.RAM.Model` with two more instructions: `getBit d` reads
the next input bit (`0` or `1`, and `2` at the end of the input) and `emit a` appends the bit
`reg a ≠ 0` to the output. Its programs read their input word and write their output word bit by
bit; they are the programs simulated on the registered stack machines (`ApproximationHardness.Sim.Simulate`).

`XExec s c t c'` is the unit-cost semantics. `xrun F s c` is a total semantics in which every
loop stops after at most `F` iterations; it agrees with `XExec` when the time is at most `F`
(`xrun_of_exec`).
-/

@[expose] public section

namespace STACS2027.Sim

/-- Programs of the RAM with bit input and output. -/
inductive XStmt where
  | skip
  | const (d c : Nat)
  | add (d a b : Nat)
  | sub (d a b : Nat)
  | load (d a : Nat)
  | store (a b : Nat)
  | getBit (d : Nat)
  | emit (a : Nat)
  | seq (s t : XStmt)
  | ifz (a : Nat) (s t : XStmt)
  | loop (a : Nat) (body : XStmt)

/-- Configurations: registers, memory, the unread input bits, the output bits. -/
structure XConfig where
  reg : Nat → Nat
  mem : Nat → Nat
  inp : List Bool
  out : List Bool

def XConfig.setReg (c : XConfig) (d v : Nat) : XConfig :=
  ⟨fun i => if i = d then v else c.reg i, c.mem, c.inp, c.out⟩

def XConfig.setMem (c : XConfig) (a v : Nat) : XConfig :=
  ⟨c.reg, fun i => if i = a then v else c.mem i, c.inp, c.out⟩

/-- The value read by `getBit`: the next input bit, `2` at the end of the input. -/
def bitVal : List Bool → Nat
  | [] => 2
  | false :: _ => 0
  | true :: _ => 1

/-- One step of `getBit d`. -/
def XConfig.getBit (c : XConfig) (d : Nat) : XConfig :=
  ⟨fun i => if i = d then bitVal c.inp else c.reg i, c.mem, c.inp.tail, c.out⟩

/-- One step of `emit a`. -/
def XConfig.emit (c : XConfig) (a : Nat) : XConfig := ⟨c.reg, c.mem, c.inp, c.out ++ [decide (c.reg a ≠ 0)]⟩

/-- The unit-cost semantics: from `c`, `s` halts in `c'` after exactly `t` steps. -/
inductive XExec : XStmt → XConfig → Nat → XConfig → Prop where
  | skip (c : XConfig) : XExec .skip c 1 c
  | const (d v : Nat) (c : XConfig) : XExec (.const d v) c 1 (c.setReg d v)
  | add (d a b : Nat) (c : XConfig) : XExec (.add d a b) c 1 (c.setReg d (c.reg a + c.reg b))
  | sub (d a b : Nat) (c : XConfig) : XExec (.sub d a b) c 1 (c.setReg d (c.reg a - c.reg b))
  | load (d a : Nat) (c : XConfig) : XExec (.load d a) c 1 (c.setReg d (c.mem (c.reg a)))
  | store (a b : Nat) (c : XConfig) : XExec (.store a b) c 1 (c.setMem (c.reg a) (c.reg b))
  | getBit (d : Nat) (c : XConfig) : XExec (.getBit d) c 1 (c.getBit d)
  | emit (a : Nat) (c : XConfig) : XExec (.emit a) c 1 (c.emit a)
  | seq {s u : XStmt} {c c₁ c₂ : XConfig} {t t' : Nat} :
      XExec s c t c₁ → XExec u c₁ t' c₂ → XExec (.seq s u) c (t + t') c₂
  | ifzTrue {a : Nat} {s u : XStmt} {c c' : XConfig} {t : Nat} :
      c.reg a = 0 → XExec s c t c' → XExec (.ifz a s u) c (t + 1) c'
  | ifzFalse {a : Nat} {s u : XStmt} {c c' : XConfig} {t : Nat} :
      c.reg a ≠ 0 → XExec u c t c' → XExec (.ifz a s u) c (t + 1) c'
  | loopDone {a : Nat} {body : XStmt} {c : XConfig} : c.reg a = 0 → XExec (.loop a body) c 1 c
  | loopNext {a : Nat} {body : XStmt} {c c₁ c₂ : XConfig} {t t' : Nat} :
      c.reg a ≠ 0 → XExec body c t c₁ → XExec (.loop a body) c₁ t' c₂ →
      XExec (.loop a body) c (t + t' + 1) c₂

/-- The initial configuration on the input word `w`: registers and memory `0`. -/
def xinit (w : List Bool) : XConfig := ⟨fun _ => 0, fun _ => 0, w, []⟩

/-- The total semantics in which every loop runs at most `F` iterations. -/
def xrun (F : Nat) : XStmt → XConfig → XConfig
  | .skip, c => c
  | .const d v, c => c.setReg d v
  | .add d a b, c => c.setReg d (c.reg a + c.reg b)
  | .sub d a b, c => c.setReg d (c.reg a - c.reg b)
  | .load d a, c => c.setReg d (c.mem (c.reg a))
  | .store a b, c => c.setMem (c.reg a) (c.reg b)
  | .getBit d, c => c.getBit d
  | .emit a, c => c.emit a
  | .seq s t, c => xrun F t (xrun F s c)
  | .ifz a s t, c => if c.reg a = 0 then xrun F s c else xrun F t c
  | .loop a body, c => iter (fun c => if c.reg a = 0 then c else xrun F body c) F c

theorem XExec.time_pos {s : XStmt} {c c' : XConfig} {t : Nat} (h : XExec s c t c') : 1 ≤ t := by
  induction h <;> omega

theorem iter_fixed {S : Type} (f : S → S) (s : S) (h : f s = s) : ∀ n, iter f n s = s := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp only [iter, h, ih]

/-- The fuel semantics agrees with the unit-cost semantics when the time is at most the fuel. -/
theorem xrun_of_exec {F : Nat} {s : XStmt} {c c' : XConfig} {t : Nat} (h : XExec s c t c') :
    (t ≤ F → xrun F s c = c') ∧
    (t ≤ F → ∀ a body, s = .loop a body → ∀ N, t ≤ N + 1 →
      iter (fun c => if c.reg a = 0 then c else xrun F body c) N c = c') := by
  induction h with
  | skip => exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
  | const => exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
  | add => exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
  | sub => exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
  | load => exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
  | store => exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
  | getBit => exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
  | emit => exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
  | seq h₁ h₂ ih₁ ih₂ =>
    refine ⟨fun ht => ?_, fun _ _ _ h => by cases h⟩
    simp only [xrun]
    rw [ih₁.1 (by omega), ih₂.1 (by omega)]
  | ifzTrue ha _ ih =>
    refine ⟨fun ht => ?_, fun _ _ _ h => by cases h⟩
    simp only [xrun, ha, ite_true]; exact ih.1 (by omega)
  | ifzFalse ha _ ih =>
    refine ⟨fun ht => ?_, fun _ _ _ h => by cases h⟩
    simp only [xrun, ha, ite_false]; exact ih.1 (by omega)
  | @loopDone a body c ha =>
    have key : ∀ N, iter (fun c => if c.reg a = 0 then c else xrun F body c) N c = c :=
      iter_fixed _ c (by simp [ha])
    refine ⟨fun _ => key F, ?_⟩
    intro _ a' body' he N _
    cases he
    exact key N
  | @loopNext a body c c₁ c₂ t t' ha hb hr ihb ihr =>
    have hb1 := hb.time_pos
    have key : ∀ N, t + t' + 1 ≤ F → t + t' + 1 ≤ N + 1 →
        iter (fun c => if c.reg a = 0 then c else xrun F body c) N c = c₂ := by
      intro N hF hN
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      simp only [iter, ha, ite_false]
      rw [ihb.1 (by omega)]
      exact ihr.2 (by omega) a body rfl N' (by omega)
    refine ⟨fun ht => key F ht (by omega), ?_⟩
    intro hF a' body' he N hN
    cases he
    exact key N hF hN

/-- `s` halts on the input word `w` after `t` steps with output word `out`. -/
def XComputes (s : XStmt) (w out : List Bool) (t : Nat) : Prop :=
  ∃ c, XExec s (xinit w) t c ∧ c.out = out

end STACS2027.Sim
