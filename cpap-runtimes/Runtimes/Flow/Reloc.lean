module

public import Outerplanar.RAM.Lib
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Running a RAM program inside another: relocation and buffered output

To run several programs one after another as **one** program, each is *relocated* into its own
residue class modulo `4`: register `r` of stage `j < 3` becomes `4r + j` (`rl j r`), memory cell
`a` becomes `4a + j` (the address is computed with three additions, `addrOf`), and a `write` is
either kept (the last stage) or *buffered*: the value is stored at the buffer pointer `xP`
(a cell of another class `k`), which then advances by `4`. Class `3` holds the registers of the
composition (`xT` the address temporary, `xP`, `xFour = 4`, `xJ j = j`).

`sim_step` is the simulation theorem: if `s` runs from `c` to `c'` in `t` steps, accessing only
the addresses below `S` (`ExecB S`), and `C` represents `c` in class `j` (`Sim`), then
`tr j b s` runs from `C` to some `C'` representing `c'`, in at most `4t` steps, with the output
related by `OutRel` (buffered or not), writing no register outside class `j` except `xT`, `xP`,
and no memory cell outside class `j` except the buffer cells between the old and the new
pointer; the relocated run accesses only the addresses below any `S' ≥ 4S` that is also above
the buffer cells it writes (`4 (B + |c'.out|) ≤ S'`): a cell `a < S` of the stage becomes
`4a + j < 4S`.

`Exec.exists_execB` (every run is bounded by some `S`) recovers the time-only simulation.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027.RAM

/-- Register `r` of stage `j`. -/
def rl (j r : ℕ) : ℕ := 4 * r + j

/-- The address temporary of the composition (class `3`). -/
abbrev xT : ℕ := 3
/-- The buffer pointer (class `3`). -/
abbrev xP : ℕ := 7
/-- Holds `4` (class `3`). -/
abbrev xFour : ℕ := 11
/-- Holds `j` (class `3`). -/
def xJ (j : ℕ) : ℕ := 4 * (3 + j) + 3

/-- `xT := 4 · reg (rl j a) + j`. -/
def addrOf (j a : ℕ) : Stmt :=
  .seq (.add xT (rl j a) (rl j a)) (.seq (.add xT xT xT) (.add xT xT (xJ j)))

/-- **The relocation** of a program into class `j`; `b`: buffered writes. -/
def tr (j : ℕ) (b : Bool) : Stmt → Stmt
  | .skip => .skip
  | .const d v => .const (rl j d) v
  | .add d a e => .add (rl j d) (rl j a) (rl j e)
  | .sub d a e => .sub (rl j d) (rl j a) (rl j e)
  | .load d a => .seq (addrOf j a) (.load (rl j d) xT)
  | .store a e => .seq (addrOf j a) (.store xT (rl j e))
  | .write a => if b then .seq (.store xP (rl j a)) (.add xP xP xFour) else .write (rl j a)
  | .seq s u => .seq (tr j b s) (tr j b u)
  | .ifz a s u => .ifz (rl j a) (tr j b s) (tr j b u)
  | .loop a body => .loop (rl j a) (tr j b body)

/-- `C` represents `c` in class `j`. -/
structure Sim (j : ℕ) (c C : Config) : Prop where
  reg : ∀ r, C.reg (rl j r) = c.reg r
  mem : ∀ a, C.mem (4 * a + j) = c.mem a
  jreg : C.reg (xJ j) = j
  four : C.reg xFour = 4

/-- The output `o` of the relocated program: buffered at `4 (B + i) + k` with the pointer `xP`
after it (`b = true`), or appended to the output `O₀` (`b = false`). -/
def OutRel : Bool → ℕ → ℕ → List ℕ → List ℕ → Config → Prop
  | true, k, B, O₀, o, C => C.reg xP = 4 * (B + o.length) + k ∧
      (∀ i, i < o.length → C.mem (4 * (B + i) + k) = o.getD i 0) ∧ C.out = O₀
  | false, _, _, O₀, o, C => C.out = O₀ ++ o

theorem rl_mod {j : ℕ} (hj : j < 4) (r : ℕ) : rl j r % 4 = j := by unfold rl; omega

theorem rl_inj {j r r' : ℕ} (h : rl j r = rl j r') : r = r' := by unfold rl at h; omega

theorem xJ_mod (j : ℕ) : xJ j % 4 = 3 := by unfold xJ; omega

/-- A register of a stage is not a register of the composition. -/
theorem rl_ne {j : ℕ} (hj : j < 3) (r : ℕ) {x : ℕ} (hx : x % 4 = 3) : rl j r ≠ x := by
  intro h; have := rl_mod (j := j) (by omega) r; rw [h] at this; omega

theorem xJ_ne_xT (j : ℕ) : xJ j ≠ xT := by show 4 * (3 + j) + 3 ≠ 3; omega
theorem xJ_ne_xP (j : ℕ) : xJ j ≠ xP := by show 4 * (3 + j) + 3 ≠ 7; omega

/-! ### Bounded runs: the output grows, every run is bounded -/

/-- The output only grows along a run. -/
theorem ExecB.out_length_le {S : ℕ} {s : Stmt} {c c' : Config} {t : ℕ} (h : ExecB S s c t c') :
    c.out.length ≤ c'.out.length := by
  induction h with
  | write a c => simp [Config.emit]
  | seq _ _ ih₁ ih₂ => omega
  | ifzTrue _ _ ih => exact ih
  | ifzFalse _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => omega
  | _ => simp [Config.setReg, Config.setMem]

/-- **Every run accesses only the addresses below some bound.** -/
theorem Exec.exists_execB {s : Stmt} {c c' : Config} {t : ℕ} (h : Exec s c t c') :
    ∃ S, ExecB S s c t c' := by
  induction h with
  | skip c => exact ⟨0, .skip c⟩
  | const d v c => exact ⟨0, .const d v c⟩
  | add d a b c => exact ⟨0, .add d a b c⟩
  | sub d a b c => exact ⟨0, .sub d a b c⟩
  | load d a c => exact ⟨c.reg a + 1, .load d a c (by omega)⟩
  | store a b c => exact ⟨c.reg a + 1, .store a b c (by omega)⟩
  | write a c => exact ⟨0, .write a c⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨S₁, h₁⟩ := ih₁
    obtain ⟨S₂, h₂⟩ := ih₂
    exact ⟨S₁ + S₂, .seq (h₁.mono (by omega)) (h₂.mono (by omega))⟩
  | ifzTrue ha _ ih =>
    obtain ⟨S₁, h₁⟩ := ih
    exact ⟨S₁, .ifzTrue ha h₁⟩
  | ifzFalse ha _ ih =>
    obtain ⟨S₁, h₁⟩ := ih
    exact ⟨S₁, .ifzFalse ha h₁⟩
  | loopDone ha => exact ⟨0, .loopDone ha⟩
  | loopNext ha _ _ ih₁ ih₂ =>
    obtain ⟨S₁, h₁⟩ := ih₁
    obtain ⟨S₂, h₂⟩ := ih₂
    exact ⟨S₁ + S₂, .loopNext ha (h₁.mono (by omega)) (h₂.mono (by omega))⟩

/-- A computation is a bounded computation for some bound. -/
theorem Computes.exists_computesIn {s : Stmt} {input output : List ℕ} {t : ℕ}
    (h : Computes s input output t) : ∃ S, ComputesIn s input output t S := by
  obtain ⟨c, he, hc⟩ := h
  obtain ⟨S, hb⟩ := Exec.exists_execB he
  exact ⟨S, c, hb, hc⟩

/-! ### The simulation -/

/-- The conclusion of the simulation: a relocated run accessing only the addresses below `S'`. -/
def SimPost (S' j k B : ℕ) (b : Bool) (O₀ : List ℕ) (s : Stmt) (c' : Config) (t : ℕ)
    (C : Config) : Prop :=
  ∃ C' t', ExecB S' (tr j b s) C t' C' ∧ Sim j c' C' ∧ OutRel b k B O₀ c'.out C' ∧ t' ≤ 4 * t ∧
    C.reg xP ≤ C'.reg xP ∧
    (∀ r, r % 4 ≠ j → r ≠ xT → r ≠ xP → C'.reg r = C.reg r) ∧
    (∀ a, a % 4 ≠ j → (a % 4 ≠ k ∨ a < C.reg xP ∨ C'.reg xP ≤ a) → C'.mem a = C.mem a)

section sim

variable {j k B : ℕ} {b : Bool} {O₀ : List ℕ}

/-- A step of a register-only instruction. -/
theorem sim_setReg (hj : j < 3) {c C : Config} (hS : Sim j c C) (hO : OutRel b k B O₀ c.out C)
    (d v : ℕ) : Sim j (c.setReg d v) (C.setReg (rl j d) v) ∧
      OutRel b k B O₀ (c.setReg d v).out (C.setReg (rl j d) v) := by
  have hJ : xJ j ≠ rl j d := (rl_ne hj d (xJ_mod j)).symm
  have hF : xFour ≠ rl j d := (rl_ne hj d (by decide)).symm
  have hP : xP ≠ rl j d := (rl_ne hj d (by decide)).symm
  refine ⟨⟨fun r => ?_, fun a => hS.mem a, ?_, ?_⟩, ?_⟩
  · by_cases hr : r = d
    · subst hr; simp
    · have : rl j r ≠ rl j d := fun h => hr (rl_inj h)
      simp [this, hr, hS.reg r]
  · simp [hJ, hS.jreg]
  · simp [hF, hS.four]
  · cases b
    · exact hO
    · obtain ⟨h1, h2, h3⟩ := hO
      exact ⟨by simp [hP, h1], fun i hi => h2 i hi, h3⟩

theorem frame_setReg (hj : j < 3) {C : Config} (d v : ℕ) :
    (∀ r, r % 4 ≠ j → r ≠ xT → r ≠ xP → (C.setReg (rl j d) v).reg r = C.reg r) := by
  intro r hr _ _
  have : r ≠ rl j d := fun h => hr (by rw [h, rl]; omega)
  simp [this]

/-- The address computation. -/
theorem addrOf_run {c C : Config} (hS : Sim j c C) (a : ℕ) :
    run (addrOf j a) C = C.setReg xT (4 * c.reg a + j) := by
  simp only [addrOf, run_seq', run_add, setReg_reg, setReg_setReg, ↓reduceIte, hS.reg a,
    xJ_ne_xT, hS.jreg]
  congr 1; omega

theorem addrOf_exec (j a : ℕ) (C : Config) : Exec (addrOf j a) C 3 (run (addrOf j a) C) := by
  have h := exec_run (addrOf j a) (by simp [addrOf, LoopFree]) C
  have hc : RAM.cost (addrOf j a) C = 3 := by simp [addrOf, RAM.cost]
  rwa [hc] at h

/-- **The simulation of a bounded run** (see the module documentation). -/
theorem sim_step {j k B : ℕ} {b : Bool} {O₀ : List ℕ} (hj : j < 3) (hk : k < 4)
    (hjk : b = true → j ≠ k) {S S' : ℕ} (hSS : 4 * S ≤ S') {s : Stmt} {c c' : Config} {t : ℕ}
    (he : ExecB S s c t c') :
    ∀ C, Sim j c C → OutRel b k B O₀ c.out C → (b = true → 4 * (B + c'.out.length) ≤ S') →
      SimPost S' j k B b O₀ s c' t C := by
  induction he with
  | skip c =>
    intro C hS hO _
    exact ⟨C, 1, ExecB.skip C, hS, hO, by omega, le_rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | const d v c =>
    intro C hS hO _
    obtain ⟨hS', hO'⟩ := sim_setReg hj hS hO d v
    refine ⟨_, 1, ExecB.const (rl j d) v C, hS', hO', by omega, ?_, frame_setReg hj d v,
      fun _ _ _ => rfl⟩
    have : xP ≠ rl j d := (rl_ne hj d (by decide)).symm
    simp [this]
  | add d a e c =>
    intro C hS hO _
    have h := sim_setReg hj hS hO d (c.reg a + c.reg e)
    rw [← hS.reg a, ← hS.reg e] at h
    refine ⟨_, 1, ExecB.add (rl j d) (rl j a) (rl j e) C, ?_, ?_, by omega, ?_,
      frame_setReg hj d _, fun _ _ _ => rfl⟩
    · rw [hS.reg a, hS.reg e] at h ⊢; exact h.1
    · rw [hS.reg a, hS.reg e] at h ⊢; exact h.2
    · have : xP ≠ rl j d := (rl_ne hj d (by decide)).symm
      simp [this]
  | sub d a e c =>
    intro C hS hO _
    have h := sim_setReg hj hS hO d (c.reg a - c.reg e)
    refine ⟨_, 1, ExecB.sub (rl j d) (rl j a) (rl j e) C, ?_, ?_, by omega, ?_,
      frame_setReg hj d _, fun _ _ _ => rfl⟩
    · rw [hS.reg a, hS.reg e]; exact h.1
    · rw [hS.reg a, hS.reg e]; exact h.2
    · have : xP ≠ rl j d := (rl_ne hj d (by decide)).symm
      simp [this]
  | load d a c ha =>
    intro C hS hO _
    set C₁ := run (addrOf j a) C with hC₁
    have hrun := addrOf_run hS a
    have he₁ : ExecB S' (addrOf j a) C 3 C₁ := Exec.toExecB_of_memFree rfl (addrOf_exec j a C)
    have hT : C₁.reg xT = 4 * c.reg a + j := by rw [hC₁, hrun]; simp
    have hm : C₁.mem = C.mem := by rw [hC₁, hrun]; simp
    have hS₁ : Sim j c C₁ := by
      refine ⟨fun r => ?_, fun a' => by rw [hm]; exact hS.mem a', ?_, ?_⟩
      · have : rl j r ≠ xT := rl_ne hj r (by decide)
        rw [hC₁, hrun]; simp [this, hS.reg r]
      · rw [hC₁, hrun]; simp [xJ_ne_xT, hS.jreg]
      · rw [hC₁, hrun]; simp [hS.four]
    have hO₁ : OutRel b k B O₀ c.out C₁ := by
      cases b
      · have hO' : C.out = O₀ ++ c.out := hO
        show C₁.out = _; rw [hC₁, hrun]; simpa using hO'
      · obtain ⟨h1, h2, h3⟩ := hO
        refine ⟨?_, fun i hi => by rw [hm]; exact h2 i hi, by rw [hC₁, hrun]; simpa using h3⟩
        rw [hC₁, hrun]; simpa using h1
    obtain ⟨hS', hO'⟩ := sim_setReg hj hS₁ hO₁ d (c.mem (c.reg a))
    have hval : C₁.mem (C₁.reg xT) = c.mem (c.reg a) := by
      rw [hT, hm, show 4 * c.reg a + j = 4 * c.reg a + j from rfl]; exact hS.mem _
    refine ⟨C₁.setReg (rl j d) (C₁.mem (C₁.reg xT)), 3 + 1,
      ExecB.seq he₁ (ExecB.load _ _ C₁ (by rw [hT]; omega)), ?_, ?_, by omega, ?_, ?_, ?_⟩
    · rw [hval]; exact hS'
    · rw [hval]; exact hO'
    · have : xP ≠ rl j d := (rl_ne hj d (by decide)).symm
      rw [hC₁, hrun]; simp [this]
    · intro r hr hT' hP'
      have : r ≠ rl j d := fun h => hr (by rw [h, rl]; omega)
      rw [hC₁, hrun]; simp [this, hT']
    · intro a' _ _; simp [hm]
  | store a e c ha =>
    intro C hS hO _
    set C₁ := run (addrOf j a) C with hC₁
    have hrun := addrOf_run hS a
    have he₁ : ExecB S' (addrOf j a) C 3 C₁ := Exec.toExecB_of_memFree rfl (addrOf_exec j a C)
    have hT : C₁.reg xT = 4 * c.reg a + j := by rw [hC₁, hrun]; simp
    have hm : C₁.mem = C.mem := by rw [hC₁, hrun]; simp
    have hreg : ∀ r, r ≠ xT → C₁.reg r = C.reg r := fun r hr => by rw [hC₁, hrun]; simp [hr]
    have heT : rl j e ≠ xT := rl_ne hj e (by decide)
    have hvE : C₁.reg (rl j e) = c.reg e := by rw [hreg _ heT, hS.reg e]
    refine ⟨C₁.setMem (C₁.reg xT) (C₁.reg (rl j e)), 3 + 1,
      ExecB.seq he₁ (ExecB.store _ _ C₁ (by rw [hT]; omega)),
      ⟨fun r => ?_, fun a' => ?_, ?_, ?_⟩, ?_, by omega, ?_, ?_, ?_⟩
    · simp [hreg _ (rl_ne hj r (by decide)), hS.reg r]
    · simp only [Config.setMem, hT, hvE, hm]
      by_cases ha : a' = c.reg a
      · subst ha; simp
      · simp [ha, hS.mem a']
    · simp [hreg _ (xJ_ne_xT j), hS.jreg]
    · simp [hreg xFour (by decide), hS.four]
    · cases b
      · have hO' : C.out = O₀ ++ c.out := hO
        show (C₁.setMem _ _).out = _; simp only [setMem_out]; rw [hC₁, hrun]; simpa using hO'
      · obtain ⟨h1, h2, h3⟩ := hO
        refine ⟨by simp [hreg xP (by decide), h1], fun i hi => ?_, by
          simp only [setMem_out]; rw [hC₁, hrun]; simpa using h3⟩
        have hne : 4 * (B + i) + k ≠ 4 * c.reg a + j := by
          have := hjk rfl; omega
        simp only [Config.setMem, hT, hm, hne, ↓reduceIte]
        exact h2 i hi
    · simp [hreg xP (by decide)]
    · intro r _ hT' _; simp [hreg r hT']
    · intro a' ha' _
      have : a' ≠ 4 * c.reg a + j := fun h => ha' (by omega)
      simp [Config.setMem, hT, this, hm]
  | write a c =>
    intro C hS hO hb
    cases b with
    | false =>
      refine ⟨C.emit (C.reg (rl j a)), 1, ?_, ⟨hS.reg, hS.mem, hS.jreg, hS.four⟩, ?_, by omega,
        le_rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
      · simp only [tr, Bool.false_eq_true, ↓reduceIte]; exact ExecB.write _ C
      · show (C.emit _).out = _
        simp only [Config.emit]
        have : C.out = O₀ ++ c.out := hO
        rw [this, hS.reg a]; simp
    | true =>
      obtain ⟨h1, h2, h3⟩ := hO
      have hjk' := hjk rfl
      set C₁ := C.setMem (C.reg xP) (C.reg (rl j a))
      set C₂ := C₁.setReg xP (C₁.reg xP + C₁.reg xFour)
      have hb' := hb rfl
      simp only [Config.emit, List.length_append, List.length_singleton] at hb'
      have he : ExecB S' (tr j true (.write a)) C 2 C₂ := by
        simp only [tr, ↓reduceIte]
        exact ExecB.seq (ExecB.store _ _ C (by rw [h1]; omega)) (ExecB.add _ _ _ C₁)
      have hP2 : C₂.reg xP = C.reg xP + 4 := by simp [C₂, C₁, hS.four]
      have hm : ∀ a', a' ≠ C.reg xP → C₂.mem a' = C.mem a' := fun a' h => by simp [C₂, C₁, h]
      refine ⟨C₂, 2, he, ⟨fun r => ?_, fun a' => ?_, ?_, ?_⟩, ?_, by omega, by omega, ?_, ?_⟩
      · simp [C₂, C₁, rl_ne hj r (show xP % 4 = 3 by decide), hS.reg r]
      · rw [hm _ (by rw [h1]; omega)]; exact hS.mem a'
      · simp [C₂, C₁, xJ_ne_xP, hS.jreg]
      · simp [C₂, C₁, hS.four]
      · refine ⟨by rw [hP2, h1, Config.emit]; simp; omega, fun i hi => ?_, by simp [C₂, C₁, h3]⟩
        simp only [Config.emit, List.length_append, List.length_singleton] at hi ⊢
        by_cases hil : i < c.out.length
        · rw [hm _ (by rw [h1]; omega), h2 i hil]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hil]
        · have hi' : i = c.out.length := by omega
          subst hi'
          have : 4 * (B + c.out.length) + k = C.reg xP := by rw [h1]
          simp [C₂, C₁, this, hS.reg a]
      · intro r _ _ hP'; simp [C₂, C₁, hP']
      · intro a' _ ha'
        rcases ha' with ha' | ha' | ha'
        · exact hm _ (by rw [h1]; omega)
        · exact hm _ (by omega)
        · exact hm _ (by omega)
  | seq _ hu ih₁ ih₂ =>
    intro C hS hO hb
    obtain ⟨C₁, t₁, he₁, hS₁, hO₁, ht₁, hp₁, hr₁, hm₁⟩ :=
      ih₁ C hS hO fun h => le_trans (by have := ExecB.out_length_le hu; omega) (hb h)
    obtain ⟨C₂, t₂, he₂, hS₂, hO₂, ht₂, hp₂, hr₂, hm₂⟩ := ih₂ C₁ hS₁ hO₁ hb
    refine ⟨C₂, t₁ + t₂, ExecB.seq he₁ he₂, hS₂, hO₂, by omega, le_trans hp₁ hp₂,
      fun r h1 h2 h3 => (hr₂ r h1 h2 h3).trans (hr₁ r h1 h2 h3), fun a h1 h2 => ?_⟩
    rw [hm₂ a h1 (by omega), hm₁ a h1 (by omega)]
  | ifzTrue ha _ ih =>
    intro C hS hO hb
    obtain ⟨C', t', he', hS', hO', ht', hp, hr, hm⟩ := ih C hS hO hb
    exact ⟨C', t' + 1, ExecB.ifzTrue (by rw [hS.reg]; exact ha) he', hS', hO', by omega, hp, hr, hm⟩
  | ifzFalse ha _ ih =>
    intro C hS hO hb
    obtain ⟨C', t', he', hS', hO', ht', hp, hr, hm⟩ := ih C hS hO hb
    exact ⟨C', t' + 1, ExecB.ifzFalse (by rw [hS.reg]; exact ha) he', hS', hO', by omega, hp, hr,
      hm⟩
  | loopDone ha =>
    intro C hS hO _
    exact ⟨C, 1, ExecB.loopDone (by rw [hS.reg]; exact ha), hS, hO, by omega, le_rfl,
      fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | loopNext ha _ hl ih₁ ih₂ =>
    intro C hS hO hb
    obtain ⟨C₁, t₁, he₁, hS₁, hO₁, ht₁, hp₁, hr₁, hm₁⟩ :=
      ih₁ C hS hO fun h => le_trans (by have := ExecB.out_length_le hl; omega) (hb h)
    obtain ⟨C₂, t₂, he₂, hS₂, hO₂, ht₂, hp₂, hr₂, hm₂⟩ := ih₂ C₁ hS₁ hO₁ hb
    refine ⟨C₂, t₁ + t₂ + 1, ExecB.loopNext (by rw [hS.reg]; exact ha) he₁ he₂, hS₂, hO₂, by omega,
      le_trans hp₁ hp₂, fun r h1 h2 h3 => (hr₂ r h1 h2 h3).trans (hr₁ r h1 h2 h3),
      fun a h1 h2 => ?_⟩
    rw [hm₂ a h1 (by omega), hm₁ a h1 (by omega)]

end sim

end STACS2027.Runtimes.Flow
