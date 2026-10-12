module

public import Outerplanar.RAM.HT
import Mathlib.Tactic

/-!
# Frames and structural rules for RAM programs (with loops)

The Hoare triples `HT` of `Outerplanar/RAM/HT.lean` only speak about the configurations
before and after a run. This file supplies the *frame* reasoning needed to compose them.

* **Syntactic footprint.** `wregs s` lists the registers `s` may write, `stores s` / `writes s`
  say whether `s` contains a `store` / `write` instruction. `Exec.frame`: every run of `s`
  (loops included) leaves all other registers unchanged, leaves the memory unchanged if
  `stores s = false`, the output unchanged if `writes s = false`, and only ever appends to the
  output (`Frame`).
* **Independence.** `Agree W c c'`: `c'` differs from `c` at most in the registers of `W`.
  `Indep W P`: the assertion `P` is insensitive to the registers of `W`. `RegIndep W P`: `P`
  depends only on the registers outside `W` (not on memory and output), so it survives every
  program not writing them (`HT.frameReg`, `RegIndep.exec`, `RegIndep.run`). The tactic
  `indep` proves both kinds of goals for assertions that read registers only at concrete
  register numbers.
* **Structural rules.** `HT.frame` (the frame rule), `HT.frameReg`, `HT.frameIndep`, `HT.withFrame`
  (relational frame information through a ghost initial configuration), `HT.and`
  (conjunction of two triples, by determinism), `HT.skip`, `HT.exists_pre`, `HT.prop_pre`,
  `HT.cases`, `HT.run_le` (loop-free code with an explicit bound), and the counted loop rule
  `HT.loopT` (fixed bound per iteration, a measure decreasing at every iteration).
* `LoopFree` is decidable (`by decide` proves `LoopFree s` for a concrete program `s`).
-/

@[expose] public section

namespace STACS2027.RAM

/-! ### Syntactic footprint -/

/-- The registers a program may write (with repetitions). -/
def wregs : Stmt → List ℕ
  | .const d _ | .add d _ _ | .sub d _ _ | .load d _ => [d]
  | .seq s t | .ifz _ s t => wregs s ++ wregs t
  | .loop _ b => wregs b
  | _ => []

/-- Whether a program contains a `store` instruction. -/
def stores : Stmt → Bool
  | .store _ _ => true
  | .seq s t | .ifz _ s t => stores s || stores t
  | .loop _ b => stores b
  | _ => false

/-- Whether a program contains a `write` instruction. -/
def writes : Stmt → Bool
  | .write _ => true
  | .seq s t | .ifz _ s t => writes s || writes t
  | .loop _ b => writes b
  | _ => false

@[simp] theorem wregs_seq (s t : Stmt) : wregs (.seq s t) = wregs s ++ wregs t := rfl
@[simp] theorem wregs_ifz (a : ℕ) (s t : Stmt) : wregs (.ifz a s t) = wregs s ++ wregs t := rfl
@[simp] theorem wregs_loop (a : ℕ) (b : Stmt) : wregs (.loop a b) = wregs b := rfl
@[simp] theorem stores_seq (s t : Stmt) : stores (.seq s t) = (stores s || stores t) := rfl
@[simp] theorem stores_ifz (a : ℕ) (s t : Stmt) : stores (.ifz a s t) = (stores s || stores t) := rfl
@[simp] theorem stores_loop (a : ℕ) (b : Stmt) : stores (.loop a b) = stores b := rfl
@[simp] theorem writes_seq (s t : Stmt) : writes (.seq s t) = (writes s || writes t) := rfl
@[simp] theorem writes_ifz (a : ℕ) (s t : Stmt) : writes (.ifz a s t) = (writes s || writes t) := rfl
@[simp] theorem writes_loop (a : ℕ) (b : Stmt) : writes (.loop a b) = writes b := rfl

/-- What a run of `s` from `c` to `c'` may have changed: only the registers of `wregs s`; the
memory only if `s` stores; the output only if `s` writes, and then only by appending. -/
structure Frame (s : Stmt) (c c' : Config) : Prop where
  reg : ∀ r, r ∉ wregs s → c'.reg r = c.reg r
  mem : stores s = false → c'.mem = c.mem
  out : writes s = false → c'.out = c.out
  outApp : ∃ l, c'.out = c.out ++ l

/-- **Frame lemma**: every run of a program (loops included) respects its footprint. -/
theorem Exec.frame {s : Stmt} {c c' : Config} {t : ℕ} (h : Exec s c t c') : Frame s c c' := by
  induction h with
  | skip c => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, ⟨[], by simp⟩⟩
  | const d v c =>
    refine ⟨fun r hr => ?_, fun _ => rfl, fun _ => rfl, ⟨[], by simp⟩⟩
    simp only [wregs, List.mem_singleton] at hr; simp [hr]
  | add d a b c =>
    refine ⟨fun r hr => ?_, fun _ => rfl, fun _ => rfl, ⟨[], by simp⟩⟩
    simp only [wregs, List.mem_singleton] at hr; simp [hr]
  | sub d a b c =>
    refine ⟨fun r hr => ?_, fun _ => rfl, fun _ => rfl, ⟨[], by simp⟩⟩
    simp only [wregs, List.mem_singleton] at hr; simp [hr]
  | load d a c =>
    refine ⟨fun r hr => ?_, fun _ => rfl, fun _ => rfl, ⟨[], by simp⟩⟩
    simp only [wregs, List.mem_singleton] at hr; simp [hr]
  | store a b c => exact ⟨fun _ _ => rfl, fun h => by simp [stores] at h, fun _ => rfl, ⟨[], by simp⟩⟩
  | write a c =>
    exact ⟨fun _ _ => rfl, fun _ => rfl, fun h => by simp [writes] at h, ⟨[c.reg a], by simp⟩⟩
  | seq _ _ ih₁ ih₂ =>
    refine ⟨fun r hr => ?_, fun h => ?_, fun h => ?_, ?_⟩
    · simp only [wregs_seq, List.mem_append, not_or] at hr
      rw [ih₂.reg r hr.2, ih₁.reg r hr.1]
    · simp only [stores_seq, Bool.or_eq_false_iff] at h
      rw [ih₂.mem h.2, ih₁.mem h.1]
    · simp only [writes_seq, Bool.or_eq_false_iff] at h
      rw [ih₂.out h.2, ih₁.out h.1]
    · obtain ⟨l₁, h₁⟩ := ih₁.outApp
      obtain ⟨l₂, h₂⟩ := ih₂.outApp
      exact ⟨l₁ ++ l₂, by rw [h₂, h₁, List.append_assoc]⟩
  | ifzTrue _ _ ih =>
    refine ⟨fun r hr => ?_, fun h => ?_, fun h => ?_, ih.outApp⟩
    · simp only [wregs_ifz, List.mem_append, not_or] at hr; exact ih.reg r hr.1
    · simp only [stores_ifz, Bool.or_eq_false_iff] at h; exact ih.mem h.1
    · simp only [writes_ifz, Bool.or_eq_false_iff] at h; exact ih.out h.1
  | ifzFalse _ _ ih =>
    refine ⟨fun r hr => ?_, fun h => ?_, fun h => ?_, ih.outApp⟩
    · simp only [wregs_ifz, List.mem_append, not_or] at hr; exact ih.reg r hr.2
    · simp only [stores_ifz, Bool.or_eq_false_iff] at h; exact ih.mem h.2
    · simp only [writes_ifz, Bool.or_eq_false_iff] at h; exact ih.out h.2
  | loopDone _ => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, ⟨[], by simp⟩⟩
  | loopNext _ _ _ ih₁ ih₂ =>
    refine ⟨fun r hr => ?_, fun h => ?_, fun h => ?_, ?_⟩
    · rw [ih₂.reg r hr, ih₁.reg r hr]
    · rw [ih₂.mem h, ih₁.mem h]
    · rw [ih₂.out h, ih₁.out h]
    · obtain ⟨l₁, h₁⟩ := ih₁.outApp
      obtain ⟨l₂, h₂⟩ := ih₂.outApp
      exact ⟨l₁ ++ l₂, by rw [h₂, h₁, List.append_assoc]⟩

theorem Exec.reg_frame {s : Stmt} {c c' : Config} {t r : ℕ} (h : Exec s c t c') (hr : r ∉ wregs s) :
    c'.reg r = c.reg r := h.frame.reg r hr

theorem Exec.mem_frame {s : Stmt} {c c' : Config} {t : ℕ} (h : Exec s c t c') (hs : stores s = false) :
    c'.mem = c.mem := h.frame.mem hs

theorem Exec.out_frame {s : Stmt} {c c' : Config} {t : ℕ} (h : Exec s c t c') (hw : writes s = false) :
    c'.out = c.out := h.frame.out hw

/-- The registers outside `wregs s` keep their values through a loop-free program. -/
theorem run_reg_of_not_mem {s : Stmt} (hs : LoopFree s) {r : ℕ} (hr : r ∉ wregs s) (c : Config) :
    (run s c).reg r = c.reg r := (exec_run s hs c).reg_frame hr

theorem run_mem_of_stores {s : Stmt} (hs : LoopFree s) (hst : stores s = false) (c : Config) :
    (run s c).mem = c.mem := (exec_run s hs c).mem_frame hst

theorem run_out_of_writes {s : Stmt} (hs : LoopFree s) (hw : writes s = false) (c : Config) :
    (run s c).out = c.out := (exec_run s hs c).out_frame hw

/-! ### Agreement and independence -/

/-- `c'` agrees with `c` except possibly on the registers of `W`. -/
structure Agree (W : List ℕ) (c c' : Config) : Prop where
  reg : ∀ r, r ∉ W → c'.reg r = c.reg r
  mem : c'.mem = c.mem
  out : c'.out = c.out

/-- The assertion `P` does not depend on the registers of `W`. -/
def Indep (W : List ℕ) (P : Config → Prop) : Prop := ∀ c c', Agree W c c' → P c → P c'

theorem Agree.refl (W : List ℕ) (c : Config) : Agree W c c := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Agree.symm {W : List ℕ} {c c' : Config} (h : Agree W c c') : Agree W c' c :=
  ⟨fun r hr => (h.reg r hr).symm, h.mem.symm, h.out.symm⟩

theorem Agree.trans {W : List ℕ} {c₁ c₂ c₃ : Config} (h₁ : Agree W c₁ c₂) (h₂ : Agree W c₂ c₃) :
    Agree W c₁ c₃ :=
  ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.mem.trans h₁.mem, h₂.out.trans h₁.out⟩

theorem Agree.mono {W W' : List ℕ} {c c' : Config} (h : Agree W c c') (hW : ∀ r ∈ W, r ∈ W') :
    Agree W' c c' :=
  ⟨fun r hr => h.reg r fun h' => hr (hW r h'), h.mem, h.out⟩

/-- Setting a register of `W`. -/
theorem agree_setReg {W : List ℕ} {d : ℕ} (hd : d ∈ W) (c : Config) (v : ℕ) :
    Agree W c (c.setReg d v) :=
  ⟨fun r hr => by
    have hne : r ≠ d := fun h => hr (h ▸ hd)
    simp [hne], rfl, rfl⟩

theorem Frame.agree {s : Stmt} {c c' : Config} (h : Frame s c c') (hs : stores s = false)
    (hw : writes s = false) : Agree (wregs s) c c' := ⟨h.reg, h.mem hs, h.out hw⟩

/-- The footprint of a loop-free program, for `run`. -/
theorem run_frame {s : Stmt} (hs : LoopFree s) (c : Config) : Frame s c (run s c) :=
  (exec_run s hs c).frame

/-- A loop-free program that neither stores nor writes, and writes only registers of `W`, changes
nothing outside `W`. Typical use: `agree_run (by decide) rfl rfl (by decide) c`. -/
theorem agree_run {s : Stmt} {W : List ℕ} (hs : LoopFree s) (hst : stores s = false)
    (hw : writes s = false) (hW : ∀ r ∈ wregs s, r ∈ W) (c : Config) : Agree W c (run s c) :=
  ((run_frame hs c).agree hst hw).mono hW

namespace Indep

variable {W W' : List ℕ} {P Q : Config → Prop}

/-- Independence holds in both directions (agreement is symmetric). -/
theorem iff (h : Indep W P) {c c' : Config} (hc : Agree W c c') : P c ↔ P c' :=
  ⟨h c c' hc, h c' c hc.symm⟩

theorem mono (h : Indep W P) (hW : ∀ r ∈ W', r ∈ W) : Indep W' P :=
  fun c c' hc => h c c' (hc.mono hW)

theorem and (hP : Indep W P) (hQ : Indep W Q) : Indep W (fun c => P c ∧ Q c) :=
  fun c c' hc h => ⟨hP c c' hc h.1, hQ c c' hc h.2⟩

theorem or (hP : Indep W P) (hQ : Indep W Q) : Indep W (fun c => P c ∨ Q c) :=
  fun c c' hc h => h.imp (hP c c' hc) (hQ c c' hc)

theorem imp (hP : Indep W P) (hQ : Indep W Q) : Indep W (fun c => P c → Q c) :=
  fun c c' hc h hp => hQ c c' hc (h ((hP.iff hc).mpr hp))

theorem not (hP : Indep W P) : Indep W (fun c => ¬ P c) :=
  fun _ _ hc h hp => h ((hP.iff hc).mpr hp)

theorem «forall» {α : Sort*} {P : α → Config → Prop} (h : ∀ x, Indep W (P x)) :
    Indep W (fun c => ∀ x, P x c) := fun c c' hc hp x => h x c c' hc (hp x)

theorem «exists» {α : Sort*} {P : α → Config → Prop} (h : ∀ x, Indep W (P x)) :
    Indep W (fun c => ∃ x, P x c) := fun c c' hc ⟨x, hp⟩ => ⟨x, h x c c' hc hp⟩

theorem const (p : Prop) : Indep W (fun _ => p) := fun _ _ _ h => h

/-- An assertion about a register outside `W`. -/
theorem reg {r : ℕ} (hr : r ∉ W) (p : ℕ → Prop) : Indep W (fun c => p (c.reg r)) :=
  fun c c' hc (h : p (c.reg r)) => show p (c'.reg r) by rw [hc.reg r hr]; exact h

/-- An assertion about the memory and the output only. -/
theorem memOut (p : (ℕ → ℕ) → List ℕ → Prop) : Indep W (fun c => p c.mem c.out) :=
  fun c c' hc (h : p c.mem c.out) => show p c'.mem c'.out by rw [hc.mem, hc.out]; exact h

/-- An assertion about the memory only. -/
theorem mem (p : (ℕ → ℕ) → Prop) : Indep W (fun c => p c.mem) :=
  fun c c' hc (h : p c.mem) => show p c'.mem by rw [hc.mem]; exact h

/-- An assertion about the output only. -/
theorem out (p : List ℕ → Prop) : Indep W (fun c => p c.out) :=
  fun c c' hc (h : p c.out) => show p c'.out by rw [hc.out]; exact h

/-- Writing a register of `W` preserves an assertion independent of `W`. -/
theorem setReg (h : Indep W P) {d : ℕ} (hd : d ∈ W) {c : Config} (v : ℕ) (hc : P c) :
    P (c.setReg d v) := h c _ (agree_setReg hd c v) hc

end Indep

/-! ### Register-only independence -/

/-- The assertion `P` depends only on the registers outside `W` (not on the memory, nor on the
output). Such assertions survive *every* program whose written registers avoid them
(`HT.frameReg`), including programs that store or write. -/
def RegIndep (W : List ℕ) (P : Config → Prop) : Prop :=
  ∀ c c', (∀ r, r ∉ W → c'.reg r = c.reg r) → P c → P c'

namespace RegIndep

variable {W W' : List ℕ} {P Q : Config → Prop}

theorem indep (h : RegIndep W P) : Indep W P := fun c c' hc => h c c' hc.reg

theorem mono (h : RegIndep W P) (hW : ∀ r ∈ W', r ∈ W) : RegIndep W' P :=
  fun c c' hc => h c c' fun r hr => hc r fun h' => hr (hW r h')

theorem and (hP : RegIndep W P) (hQ : RegIndep W Q) : RegIndep W (fun c => P c ∧ Q c) :=
  fun c c' hc h => ⟨hP c c' hc h.1, hQ c c' hc h.2⟩

theorem const (p : Prop) : RegIndep W (fun _ => p) := fun _ _ _ h => h

theorem reg {r : ℕ} (hr : r ∉ W) (p : ℕ → Prop) : RegIndep W (fun c => p (c.reg r)) :=
  fun c c' hc (h : p (c.reg r)) => show p (c'.reg r) by rw [hc r hr]; exact h

/-- Through a run (loops included). -/
theorem exec {s : Stmt} (h : RegIndep (wregs s) P) {c c' : Config} {t : ℕ} (he : Exec s c t c')
    (hc : P c) : P c' := h c c' he.frame.reg hc

/-- Through a loop-free program. -/
theorem run {s : Stmt} (h : RegIndep (wregs s) P) (hs : LoopFree s) {c : Config} (hc : P c) :
    P (RAM.run s c) := h.exec (exec_run s hs c) hc

/-- Through a loop-free program writing only registers of `W`. -/
theorem run_of_sub {s : Stmt} (h : RegIndep W P) (hs : LoopFree s) (hsub : ∀ r ∈ wregs s, r ∈ W)
    {c : Config} (hc : P c) : P (RAM.run s c) := (h.mono hsub).run hs hc

theorem setReg (h : RegIndep W P) {d : ℕ} (hd : d ∈ W) {c : Config} (v : ℕ) (hc : P c) :
    P (c.setReg d v) := h.indep.setReg hd v hc

/-- Stores do not affect register-only assertions. -/
theorem setMem {c : Config} (h : RegIndep W P) (a v : ℕ) (hc : P c) : P (c.setMem a v) :=
  h c _ (fun _ _ => rfl) hc

/-- Writes do not affect register-only assertions. -/
theorem emit {c : Config} (h : RegIndep W P) (v : ℕ) (hc : P c) : P (c.emit v) :=
  h c _ (fun _ _ => rfl) hc

end RegIndep

/-- Through a loop-free program that neither stores nor writes. -/
theorem Indep.run {s : Stmt} {P : Config → Prop} (h : Indep (wregs s) P) (hs : LoopFree s)
    (hst : stores s = false) (hw : writes s = false) {c : Config} (hc : P c) : P (RAM.run s c) :=
  h c _ ((exec_run s hs c).frame.agree hst hw) hc

/-- `indep` proves goals `Indep W P` and `RegIndep W P` when `P` reads the configuration only
through `c.mem`, `c.out` (not allowed for `RegIndep`) and `c.reg r` for registers `r` that
`decide` shows are not in `W` (so `W` and these `r` must be concrete, e.g. `W = wregs body` for a
concrete program `body`). `indep [f, g]` first rewrites with the simp lemmas `f`, `g` (e.g. the
definition of `P`, or the lemma `foo_iff` generated by `@[mk_iff]` for a structure `Foo` — note
the lower-case first letter). -/
syntax (name := indepTac) "indep" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| indep) => `(tactic|
      (intro _ _ hA hP
       first
       | (have hr := hA.reg
          have hm := hA.mem
          have ho := hA.out
          (try simp (disch := decide) only [hr, hm, ho])
          exact hP)
       | ((try simp (disch := decide) only [hA])
          exact hP)))
  | `(tactic| indep [$ls,*]) => `(tactic|
      (intro _ _ hA hP
       simp only [$ls,*] at hP ⊢
       first
       | (have hr := hA.reg
          have hm := hA.mem
          have ho := hA.out
          (try simp (disch := decide) only [hr, hm, ho])
          exact hP)
       | ((try simp (disch := decide) only [hA])
          exact hP)))

/-! ### Structural rules for `HT` -/

instance decLoopFree : DecidablePred LoopFree
  | .skip | .const .. | .add .. | .sub .. | .load .. | .store .. | .write .. => isTrue trivial
  | .loop .. => isFalse id
  | .seq s t =>
    haveI := decLoopFree s; haveI := decLoopFree t
    inferInstanceAs (Decidable (LoopFree s ∧ LoopFree t))
  | .ifz _ s t =>
    haveI := decLoopFree s; haveI := decLoopFree t
    inferInstanceAs (Decidable (LoopFree s ∧ LoopFree t))

namespace HT

variable {s u : Stmt} {P Q R F : Config → Prop} {b b' : ℕ}

theorem skip : HT .skip P P 1 := fun c hc => ⟨c, 1, Exec.skip c, hc, le_rfl⟩

/-- Loop-free code with an explicit bound. -/
theorem run_le (hs : LoopFree s) (hb : size s ≤ b) (h : ∀ c, P c → Q (RAM.run s c)) : HT s P Q b :=
  (HT.run hs h).weaken hb

/-- **Frame rule**: an assertion preserved by every change allowed by the footprint of `s`. -/
theorem frame (h : HT s P Q b) (hF : ∀ c c', Frame s c c' → F c → F c') :
    HT s (fun c => P c ∧ F c) (fun c => Q c ∧ F c) b := by
  intro c ⟨hp, hf⟩
  obtain ⟨c', t, he, hq, ht⟩ := h c hp
  exact ⟨c', t, he, ⟨hq, hF c c' he.frame hf⟩, ht⟩

/-- **Frame rule for register-only assertions**, for every program. -/
theorem frameReg (h : HT s P Q b) (hF : RegIndep (wregs s) F) :
    HT s (fun c => P c ∧ F c) (fun c => Q c ∧ F c) b :=
  h.frame fun _ _ hfr hf => hF _ _ hfr.reg hf

/-- Frame rule for a program that neither stores nor writes. -/
theorem frameIndep (h : HT s P Q b) (hs : stores s = false) (hw : writes s = false)
    (hF : Indep (wregs s) F) : HT s (fun c => P c ∧ F c) (fun c => Q c ∧ F c) b :=
  h.frame fun c c' hfr hf => hF c c' (hfr.agree hs hw) hf

/-- Relational frame information, through a ghost initial configuration `c₀`. -/
theorem withFrame (h : HT s P Q b) (c₀ : Config) :
    HT s (fun c => P c ∧ c = c₀) (fun c => Q c ∧ Frame s c₀ c) b := by
  intro c ⟨hp, hc⟩
  subst hc
  obtain ⟨c', t, he, hq, ht⟩ := h c hp
  exact ⟨c', t, he, ⟨hq, he.frame⟩, ht⟩

/-- Two triples for the same program combine (the machine is deterministic). -/
theorem and {Q₁ Q₂ : Config → Prop} {b₁ b₂ : ℕ} (h₁ : HT s P Q₁ b₁) (h₂ : HT s P Q₂ b₂) :
    HT s P (fun c => Q₁ c ∧ Q₂ c) (min b₁ b₂) := by
  intro c hc
  obtain ⟨c₁, t₁, he₁, hq₁, ht₁⟩ := h₁ c hc
  obtain ⟨c₂, t₂, he₂, hq₂, ht₂⟩ := h₂ c hc
  obtain ⟨rfl, rfl⟩ := Exec.det he₁ he₂
  exact ⟨c₁, t₁, he₁, ⟨hq₁, hq₂⟩, le_min ht₁ ht₂⟩

/-- Ghost variables: an existential precondition. -/
theorem exists_pre {α : Sort*} {P : α → Config → Prop} (h : ∀ x, HT s (P x) Q b) :
    HT s (fun c => ∃ x, P x c) Q b := fun c ⟨x, hx⟩ => h x c hx

/-- A pure proposition in the precondition. -/
theorem prop_pre {p : Prop} (h : p → HT s P Q b) : HT s (fun c => p ∧ P c) Q b :=
  fun c ⟨hp, hc⟩ => h hp c hc

/-- Case split on a proposition. -/
theorem cases (p : Prop) (h₁ : HT s (fun c => P c ∧ p) Q b) (h₂ : HT s (fun c => P c ∧ ¬ p) Q b) :
    HT s P Q b := by
  intro c hc
  by_cases hp : p
  · exact h₁ c ⟨hc, hp⟩
  · exact h₂ c ⟨hc, hp⟩

/-- Case split on a property of the initial configuration. -/
theorem casesOn (p : Config → Prop) (h₁ : HT s (fun c => P c ∧ p c) Q b)
    (h₂ : HT s (fun c => P c ∧ ¬ p c) Q b) : HT s P Q b := by
  intro c hc
  by_cases hp : p c
  · exact h₁ c ⟨hc, hp⟩
  · exact h₂ c ⟨hc, hp⟩

/-- An unconditional triple from a family of triples indexed by the initial configuration. -/
theorem of_forall (h : ∀ c₀, P c₀ → HT s (fun c => c = c₀) Q b) : HT s P Q b :=
  fun c hc => h c hc c rfl

/-- Sequencing three programs. -/
theorem seq3 {s₁ s₂ s₃ : Stmt} {R₁ R₂ : Config → Prop} {b₁ b₂ b₃ : ℕ} (h₁ : HT s₁ P R₁ b₁)
    (h₂ : HT s₂ R₁ R₂ b₂) (h₃ : HT s₃ R₂ Q b₃) : HT (.seq s₁ (.seq s₂ s₃)) P Q (b₁ + (b₂ + b₃)) :=
  h₁.seq (h₂.seq h₃)

/-- Sequencing with a bound given up to `≤`. -/
theorem seq_le {b₁ b₂ : ℕ} (h₁ : HT s P R b₁) (h₂ : HT u R Q b₂) (hb : b₁ + b₂ ≤ b) :
    HT (.seq s u) P Q b := (h₁.seq h₂).weaken hb

/-- **Loop with a decreasing measure**: every body run from the invariant (test register
nonzero) costs at most `T` steps and lowers the measure `μ`; from a configuration with measure
at most `K` the loop costs at most `K * (T + 1) + 1` steps. -/
theorem loopT {a : ℕ} {body : Stmt} {Inv : Config → Prop} (μ : Config → ℕ) {T : ℕ}
    (hbody : ∀ v, HT body (fun c => Inv c ∧ c.reg a ≠ 0 ∧ μ c = v) (fun c => Inv c ∧ μ c < v) T)
    (K : ℕ) : HT (.loop a body) (fun c => Inv c ∧ μ c ≤ K) (fun c => Inv c ∧ c.reg a = 0)
      (K * (T + 1) + 1) := by
  suffices key : ∀ k c, Inv c → μ c ≤ k →
      ∃ c' t, Exec (.loop a body) c t c' ∧ (Inv c' ∧ c'.reg a = 0) ∧ t ≤ k * (T + 1) + 1 from
    fun c ⟨hi, hk⟩ => key K c hi hk
  intro k
  induction k with
  | zero =>
    intro c hi hk
    by_cases ha : c.reg a = 0
    · exact ⟨c, 1, Exec.loopDone ha, ⟨hi, ha⟩, by omega⟩
    · obtain ⟨_, _, _, ⟨_, hlt⟩, _⟩ := hbody (μ c) c ⟨hi, ha, rfl⟩
      omega
  | succ k ih =>
    intro c hi hk
    by_cases ha : c.reg a = 0
    · exact ⟨c, 1, Exec.loopDone ha, ⟨hi, ha⟩, by omega⟩
    · obtain ⟨c₁, t₁, he₁, ⟨hi₁, hlt⟩, ht₁⟩ := hbody (μ c) c ⟨hi, ha, rfl⟩
      obtain ⟨c₂, t₂, he₂, hq, ht₂⟩ := ih c₁ hi₁ (by omega)
      refine ⟨c₂, t₁ + t₂ + 1, Exec.loopNext ha he₁ he₂, hq, ?_⟩
      rw [Nat.succ_mul]; omega

end HT

end STACS2027.RAM
