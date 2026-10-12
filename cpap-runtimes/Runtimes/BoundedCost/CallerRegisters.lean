module

public import Outerplanar.RAM.BoundedHT
import Mathlib.Tactic

/-! Register renaming places compiler controls in a residue class disjoint from
the reused flow workspace. Memory addresses and unit-cost execution are preserved. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027.RAM

def renameRegisters (φ : ℕ → ℕ) : Stmt → Stmt
  | .skip => .skip
  | .const d v => .const (φ d) v
  | .add d a b => .add (φ d) (φ a) (φ b)
  | .sub d a b => .sub (φ d) (φ a) (φ b)
  | .load d a => .load (φ d) (φ a)
  | .store a b => .store (φ a) (φ b)
  | .write a => .write (φ a)
  | .seq s u => .seq (renameRegisters φ s) (renameRegisters φ u)
  | .ifz a s u => .ifz (φ a) (renameRegisters φ s) (renameRegisters φ u)
  | .loop a body => .loop (φ a) (renameRegisters φ body)

def registerView (φ : ℕ → ℕ) (c : Config) : Config :=
  ⟨fun r => c.reg (φ r), c.mem, c.out⟩

theorem renameRegisters_wregs (φ : ℕ → ℕ) (program : Stmt) :
    wregs (renameRegisters φ program) = (wregs program).map φ := by
  induction program <;> simp_all [renameRegisters, wregs, List.map_append]

theorem renameRegisters_stores (φ : ℕ → ℕ) (program : Stmt) :
    stores (renameRegisters φ program) = stores program := by
  induction program <;> simp_all [renameRegisters, stores]

theorem renameRegisters_writes (φ : ℕ → ℕ) (program : Stmt) :
    writes (renameRegisters φ program) = writes program := by
  induction program <;> simp_all [renameRegisters, writes]

theorem registerView_setReg {φ : ℕ → ℕ} (hφ : Function.Injective φ)
    (c : Config) (r v : ℕ) :
    registerView φ (c.setReg (φ r) v) = (registerView φ c).setReg r v := by
  cases c
  simp only [registerView, Config.setReg, Config.mk.injEq, and_true]
  funext i
  simp [hφ.eq_iff]

theorem registerView_setMem (φ : ℕ → ℕ) (c : Config) (a v : ℕ) :
    registerView φ (c.setMem a v) = (registerView φ c).setMem a v := rfl

theorem registerView_emit (φ : ℕ → ℕ) (c : Config) (v : ℕ) :
    registerView φ (c.emit v) = (registerView φ c).emit v := rfl

/-- Every bounded execution lifts through an injective register renaming with its
time and memory bound unchanged. -/
theorem renameRegisters_exec {S : ℕ} {φ : ℕ → ℕ} (hφ : Function.Injective φ)
    {s : Stmt} {c d : Config} {t : ℕ} (h : ExecB S s c t d) :
    ∀ C, registerView φ C = c →
      ∃ D, ExecB S (renameRegisters φ s) C t D ∧ registerView φ D = d := by
  induction h with
  | skip c => intro C hC; exact ⟨C, .skip C, hC⟩
  | const r v c =>
    intro C hC
    exact ⟨_, .const (φ r) v C, by rw [registerView_setReg hφ, hC]⟩
  | add r a b c =>
    intro C hC
    refine ⟨_, .add (φ r) (φ a) (φ b) C, ?_⟩
    rw [registerView_setReg hφ, ← hC]
    rfl
  | sub r a b c =>
    intro C hC
    refine ⟨_, .sub (φ r) (φ a) (φ b) C, ?_⟩
    rw [registerView_setReg hφ, ← hC]
    rfl
  | load r a c ha =>
    intro C hC
    have ha' : C.reg (φ a) < S := by simpa [← hC, registerView] using ha
    refine ⟨_, .load (φ r) (φ a) C ha', ?_⟩
    rw [registerView_setReg hφ, ← hC]
    rfl
  | store a b c ha =>
    intro C hC
    have ha' : C.reg (φ a) < S := by simpa [← hC, registerView] using ha
    refine ⟨_, .store (φ a) (φ b) C ha', ?_⟩
    rw [registerView_setMem, ← hC]
    rfl
  | write a c =>
    intro C hC
    refine ⟨_, .write (φ a) C, ?_⟩
    rw [registerView_emit, ← hC]
    rfl
  | seq hs hu ihs ihu =>
    intro C hC
    obtain ⟨middle, hs', hm⟩ := ihs C hC
    obtain ⟨D, hu', hD⟩ := ihu middle hm
    exact ⟨D, .seq hs' hu', hD⟩
  | ifzTrue ha hs ih =>
    intro C hC
    obtain ⟨D, hs', hD⟩ := ih C hC
    refine ⟨D, .ifzTrue ?_ hs', hD⟩
    simpa [← hC, registerView] using ha
  | ifzFalse ha hu ih =>
    intro C hC
    obtain ⟨D, hu', hD⟩ := ih C hC
    refine ⟨D, .ifzFalse ?_ hu', hD⟩
    simpa [← hC, registerView] using ha
  | loopDone ha =>
    intro C hC
    refine ⟨C, .loopDone ?_, hC⟩
    simpa [← hC, registerView] using ha
  | loopNext ha hbody hloop ihbody ihloop =>
    intro C hC
    obtain ⟨middle, hbody', hm⟩ := ihbody C hC
    obtain ⟨D, hloop', hD⟩ := ihloop middle hm
    refine ⟨D, .loopNext ?_ hbody' hloop', hD⟩
    simpa [← hC, registerView] using ha

theorem renameRegisters_htb {S bound : ℕ} {φ : ℕ → ℕ} (hφ : Function.Injective φ)
    {s : Stmt} {P Q : Config → Prop} (h : HTB S s P Q bound) :
    HTB S (renameRegisters φ s) (fun c => P (registerView φ c))
      (fun c => Q (registerView φ c)) bound := by
  intro C hC
  obtain ⟨d, t, he, hd, ht⟩ := h (registerView φ C) hC
  obtain ⟨D, he', hD⟩ := renameRegisters_exec hφ he C rfl
  exact ⟨D, t, he', by change Q (registerView φ D); rw [hD]; exact hd, ht⟩

theorem registerView_initial (φ : ℕ → ℕ) (input : List ℕ) :
    registerView φ (initial input) = initial input := rfl

theorem renameRegisters_computesIn {S time : ℕ} {φ : ℕ → ℕ}
    (hφ : Function.Injective φ) {s : Stmt} {input output : List ℕ}
    (h : ComputesIn s input output time S) :
    ComputesIn (renameRegisters φ s) input output time S := by
  obtain ⟨d, hd, hout⟩ := h
  obtain ⟨D, he, hD⟩ := renameRegisters_exec hφ hd (initial input) rfl
  exact ⟨D, he, by simpa [registerView] using congrArg Config.out hD |>.trans hout⟩

def callerRegister (r : ℕ) : ℕ := 4 * r + 3

theorem callerRegister_injective : Function.Injective callerRegister := by
  intro a b h
  unfold callerRegister at h
  omega

def onCallerRegisters (program : Stmt) : Stmt := renameRegisters callerRegister program

theorem onCallerRegisters_htb {S bound : ℕ} {s : Stmt} {P Q : Config → Prop}
    (h : HTB S s P Q bound) :
    HTB S (onCallerRegisters s) (fun c => P (registerView callerRegister c))
      (fun c => Q (registerView callerRegister c)) bound :=
  renameRegisters_htb callerRegister_injective h

end STACS2027.Runtimes.BoundedCost
