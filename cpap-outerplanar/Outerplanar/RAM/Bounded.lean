module

public import Outerplanar.RAM.Model
import Lean.Elab.Tactic.Omega

/-!
# Space-bounded runs of the unit-cost RAM

The machine of `Model.lean` has an unbounded memory. To state that a program uses memory
proportional to its running time, we restrict the runs to the addresses `0, …, S - 1`:

* `ExecB S s c t c'`: the run `Exec s c t c'` in which every `load d a` and every
  `store a b` accesses an address `reg a < S` (the inductive `Exec` with this extra premise
  on `load` and `store`; the constructors have the same names);
* `ComputesIn s input output time space`: `s` halts on `input` after exactly `time` steps with
  output `output`, accessing only the addresses below `space` (the input cells included).

Facts:
* `ExecB.exec` (a bounded run is a run, so `ComputesIn.computes : ComputesIn … → Computes …`),
  `ExecB.mono` (monotone in the bound), `ExecB.det` (determinism, through `Exec.det`);
* `ExecB.congr`: runs from configurations that agree on the registers, the output and the
  memory below `S` (`EqBelow S`) agree: same time, same final registers and output, final
  memories agreeing below `S`. Hence the result of a bounded run does not depend on what the
  memory holds at or above `S` — in particular not on the zero-initialization of the memory
  beyond the bound (`ComputesIn.of_eqBelow`, `ComputesIn.of_mem`);
* `memFree s`: `s` has no `load` and no `store`; every run of such a program is bounded by
  every `S` (`Exec.toExecB_of_memFree`).

The file depends only on `Model.lean` (and core Lean), so that it can be copied next to the
copied machine.
-/

@[expose] public section

namespace STACS2027.RAM

/-- `ExecB S s c t c'`: from `c`, the program `s` halts in `c'` after exactly `t` unit-cost steps,
and every `load` and `store` of the run accesses an address below `S`. -/
inductive ExecB (S : Nat) : Stmt → Config → Nat → Config → Prop where
  | skip (c : Config) : ExecB S .skip c 1 c
  | const (d v : Nat) (c : Config) : ExecB S (.const d v) c 1 (c.setReg d v)
  | add (d a b : Nat) (c : Config) : ExecB S (.add d a b) c 1 (c.setReg d (c.reg a + c.reg b))
  | sub (d a b : Nat) (c : Config) : ExecB S (.sub d a b) c 1 (c.setReg d (c.reg a - c.reg b))
  | load (d a : Nat) (c : Config) :
      c.reg a < S → ExecB S (.load d a) c 1 (c.setReg d (c.mem (c.reg a)))
  | store (a b : Nat) (c : Config) :
      c.reg a < S → ExecB S (.store a b) c 1 (c.setMem (c.reg a) (c.reg b))
  | write (a : Nat) (c : Config) : ExecB S (.write a) c 1 (c.emit (c.reg a))
  | seq {s u : Stmt} {c c₁ c₂ : Config} {t t' : Nat} :
      ExecB S s c t c₁ → ExecB S u c₁ t' c₂ → ExecB S (.seq s u) c (t + t') c₂
  | ifzTrue {a : Nat} {s u : Stmt} {c c' : Config} {t : Nat} :
      c.reg a = 0 → ExecB S s c t c' → ExecB S (.ifz a s u) c (t + 1) c'
  | ifzFalse {a : Nat} {s u : Stmt} {c c' : Config} {t : Nat} :
      c.reg a ≠ 0 → ExecB S u c t c' → ExecB S (.ifz a s u) c (t + 1) c'
  | loopDone {a : Nat} {body : Stmt} {c : Config} : c.reg a = 0 → ExecB S (.loop a body) c 1 c
  | loopNext {a : Nat} {body : Stmt} {c c₁ c₂ : Config} {t t' : Nat} :
      c.reg a ≠ 0 → ExecB S body c t c₁ → ExecB S (.loop a body) c₁ t' c₂ →
      ExecB S (.loop a body) c (t + t' + 1) c₂

/-- `s` halts on `input` after `time` steps with output `output`, and the run accesses only the
memory addresses `0, …, space - 1` (the cells of the input included). -/
def ComputesIn (s : Stmt) (input output : List Nat) (time space : Nat) : Prop :=
  ∃ c, ExecB space s (initial input) time c ∧ c.out = output

namespace ExecB

variable {S S' : Nat} {s : Stmt} {c c' c'' : Config} {t t' : Nat}

/-- A bounded run is a run. -/
theorem exec (h : ExecB S s c t c') : Exec s c t c' := by
  induction h with
  | skip c => exact Exec.skip c
  | const d v c => exact Exec.const d v c
  | add d a b c => exact Exec.add d a b c
  | sub d a b c => exact Exec.sub d a b c
  | load d a c _ => exact Exec.load d a c
  | store a b c _ => exact Exec.store a b c
  | write a c => exact Exec.write a c
  | seq _ _ ih₁ ih₂ => exact Exec.seq ih₁ ih₂
  | ifzTrue ha _ ih => exact Exec.ifzTrue ha ih
  | ifzFalse ha _ ih => exact Exec.ifzFalse ha ih
  | loopDone ha => exact Exec.loopDone ha
  | loopNext ha _ _ ih₁ ih₂ => exact Exec.loopNext ha ih₁ ih₂

/-- A run within the bound `S` is within every larger bound. -/
theorem mono (hS : S ≤ S') (h : ExecB S s c t c') : ExecB S' s c t c' := by
  induction h with
  | skip c => exact .skip c
  | const d v c => exact .const d v c
  | add d a b c => exact .add d a b c
  | sub d a b c => exact .sub d a b c
  | load d a c ha => exact .load d a c (Nat.lt_of_lt_of_le ha hS)
  | store a b c ha => exact .store a b c (Nat.lt_of_lt_of_le ha hS)
  | write a c => exact .write a c
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifzTrue ha _ ih => exact .ifzTrue ha ih
  | ifzFalse ha _ ih => exact .ifzFalse ha ih
  | loopDone ha => exact .loopDone ha
  | loopNext ha _ _ ih₁ ih₂ => exact .loopNext ha ih₁ ih₂

/-- Determinism (through `Exec.det`), for any two bounds. -/
theorem det (h : ExecB S s c t c') (h' : ExecB S' s c t' c'') : t = t' ∧ c' = c'' :=
  Exec.det h.exec h'.exec

/-- Determinism against an unbounded run. -/
theorem det_exec (h : ExecB S s c t c') (h' : Exec s c t' c'') : t = t' ∧ c' = c'' :=
  Exec.det h.exec h'

end ExecB

/-! ### Independence of the memory at and above the bound -/

/-- `c` and `d` have the same registers and output, and the same memory below `S`. -/
structure EqBelow (S : Nat) (c d : Config) : Prop where
  reg : c.reg = d.reg
  out : c.out = d.out
  mem : ∀ a, a < S → c.mem a = d.mem a

theorem EqBelow.refl (S : Nat) (c : Config) : EqBelow S c c := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem EqBelow.symm {S : Nat} {c d : Config} (h : EqBelow S c d) : EqBelow S d c :=
  ⟨h.reg.symm, h.out.symm, fun a ha => (h.mem a ha).symm⟩

theorem EqBelow.setReg {S : Nat} {c d : Config} (h : EqBelow S c d) (r v : Nat) :
    EqBelow S (c.setReg r v) (d.setReg r v) :=
  ⟨by simp only [Config.setReg, h.reg], h.out, h.mem⟩

theorem EqBelow.setMem {S : Nat} {c d : Config} (h : EqBelow S c d) (a v : Nat) :
    EqBelow S (c.setMem a v) (d.setMem a v) :=
  ⟨h.reg, h.out, fun x hx => by
    simp only [Config.setMem]
    split
    · rfl
    · exact h.mem x hx⟩

theorem EqBelow.emit {S : Nat} {c d : Config} (h : EqBelow S c d) (v : Nat) :
    EqBelow S (c.emit v) (d.emit v) :=
  ⟨h.reg, by simp only [Config.emit, h.out], h.mem⟩

/-- **The memory at and above the bound is irrelevant.** A bounded run from `c` is matched by a
bounded run from every `d` agreeing with `c` on the registers, the output and the memory below
`S`: same time, and final configurations agreeing in the same way. -/
theorem ExecB.congr {S : Nat} {s : Stmt} {c c' d : Config} {t : Nat} (h : ExecB S s c t c')
    (hd : EqBelow S c d) : ∃ d', ExecB S s d t d' ∧ EqBelow S c' d' := by
  induction h generalizing d with
  | skip c => exact ⟨d, .skip d, hd⟩
  | const r v c => exact ⟨_, .const r v d, hd.setReg r v⟩
  | add r a b c =>
    refine ⟨_, .add r a b d, ?_⟩
    rw [hd.reg]; exact hd.setReg r _
  | sub r a b c =>
    refine ⟨_, .sub r a b d, ?_⟩
    rw [hd.reg]; exact hd.setReg r _
  | load r a c ha =>
    refine ⟨_, .load r a d (hd.reg ▸ ha), ?_⟩
    rw [hd.mem _ ha, hd.reg]; exact hd.setReg r _
  | store a b c ha =>
    refine ⟨_, .store a b d (hd.reg ▸ ha), ?_⟩
    rw [hd.reg]; exact hd.setMem _ _
  | write a c =>
    refine ⟨_, .write a d, ?_⟩
    rw [hd.reg]; exact hd.emit _
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨d₁, h₁, hd₁⟩ := ih₁ hd
    obtain ⟨d₂, h₂, hd₂⟩ := ih₂ hd₁
    exact ⟨d₂, .seq h₁ h₂, hd₂⟩
  | ifzTrue ha _ ih =>
    obtain ⟨d', h', hd'⟩ := ih hd
    exact ⟨d', .ifzTrue (hd.reg ▸ ha) h', hd'⟩
  | ifzFalse ha _ ih =>
    obtain ⟨d', h', hd'⟩ := ih hd
    exact ⟨d', .ifzFalse (hd.reg ▸ ha) h', hd'⟩
  | loopDone ha => exact ⟨d, .loopDone (hd.reg ▸ ha), hd⟩
  | loopNext ha _ _ ih₁ ih₂ =>
    obtain ⟨d₁, h₁, hd₁⟩ := ih₁ hd
    obtain ⟨d₂, h₂, hd₂⟩ := ih₂ hd₁
    exact ⟨d₂, .loopNext (hd.reg ▸ ha) h₁ h₂, hd₂⟩

/-! ### Bounded computations -/

namespace ComputesIn

variable {s : Stmt} {input output : List Nat} {time space : Nat}

/-- A bounded computation is a computation. -/
theorem computes (h : ComputesIn s input output time space) : Computes s input output time :=
  let ⟨c, he, hc⟩ := h
  ⟨c, he.exec, hc⟩

/-- Monotone in the space bound. -/
theorem mono {space' : Nat} (h : ComputesIn s input output time space) (hs : space ≤ space') :
    ComputesIn s input output time space' :=
  let ⟨c, he, hc⟩ := h
  ⟨c, he.mono hs, hc⟩

/-- The time and the output of a computation are unique. -/
theorem unique {output' : List Nat} {time' space' : Nat} (h : ComputesIn s input output time space)
    (h' : ComputesIn s input output' time' space') : time = time' ∧ output = output' := by
  obtain ⟨c, he, hc⟩ := h
  obtain ⟨c', he', hc'⟩ := h'
  obtain ⟨rfl, rfl⟩ := he.det he'
  exact ⟨rfl, hc.symm.trans hc'⟩

/-- **Transport to another initial configuration**: from every configuration agreeing with
`initial input` on the registers, the (empty) output and the memory below `space`, the program
halts after the same number of steps, with the same output, within the same space. -/
theorem of_eqBelow (h : ComputesIn s input output time space) {c : Config}
    (hc : EqBelow space (initial input) c) : ∃ c', ExecB space s c time c' ∧ c'.out = output := by
  obtain ⟨c₁, he, hout⟩ := h
  obtain ⟨c', he', hc'⟩ := he.congr hc
  exact ⟨c', he', hc'.out ▸ hout⟩

/-- Transport to any initial memory `m` holding the input below `space` (whatever `m` holds at
and above `space`, the result is the same). -/
theorem of_mem (h : ComputesIn s input output time space) {m : Nat → Nat}
    (hm : ∀ a, a < space → m a = input.getD a 0) :
    ∃ c', ExecB space s ⟨fun _ => 0, m, []⟩ time c' ∧ c'.out = output :=
  h.of_eqBelow ⟨rfl, rfl, fun a ha => (hm a ha).symm⟩

end ComputesIn

/-! ### Programs without memory access -/

/-- `s` contains no `load` and no `store` instruction. -/
def memFree : Stmt → Bool
  | .load _ _ | .store _ _ => false
  | .seq s t | .ifz _ s t => memFree s && memFree t
  | .loop _ b => memFree b
  | _ => true

@[simp] theorem memFree_seq (s t : Stmt) : memFree (.seq s t) = (memFree s && memFree t) := rfl
@[simp] theorem memFree_ifz (a : Nat) (s t : Stmt) : memFree (.ifz a s t) = (memFree s && memFree t) := rfl
@[simp] theorem memFree_loop (a : Nat) (b : Stmt) : memFree (.loop a b) = memFree b := rfl

/-- A run of a program without memory access is bounded by every `S`. -/
theorem Exec.toExecB_of_memFree {S : Nat} {s : Stmt} {c c' : Config} {t : Nat}
    (hm : memFree s = true) (h : Exec s c t c') : ExecB S s c t c' := by
  induction h with
  | skip c => exact .skip c
  | const d v c => exact .const d v c
  | add d a b c => exact .add d a b c
  | sub d a b c => exact .sub d a b c
  | load => simp [memFree] at hm
  | store => simp [memFree] at hm
  | write a c => exact .write a c
  | seq _ _ ih₁ ih₂ =>
    simp only [memFree_seq, Bool.and_eq_true] at hm
    exact .seq (ih₁ hm.1) (ih₂ hm.2)
  | ifzTrue ha _ ih =>
    simp only [memFree_ifz, Bool.and_eq_true] at hm
    exact .ifzTrue ha (ih hm.1)
  | ifzFalse ha _ ih =>
    simp only [memFree_ifz, Bool.and_eq_true] at hm
    exact .ifzFalse ha (ih hm.2)
  | loopDone ha => exact .loopDone ha
  | loopNext ha _ _ ih₁ ih₂ => exact .loopNext ha (ih₁ hm) (ih₂ hm)

end STACS2027.RAM
