module

public import Complexity.StackTableauProgram
public import Complexity.Restricted.Commands
public import Complexity.StackCompile
public import Complexity.PolynomialBound
import Lean.Elab.Tactic.Omega

/-!
# Runs of structured stack commands

The registered foundation's structured stack language
(`Complexity.StackTableauProgram.Command`) compiles, with exact instruction counts, to the
single-tape machines of the registered model. This file sets up `K + 1 = 256` stack registers and
the judgment `Ok c r r' b`: from the registers `r`, the command `c` halts with decision `true` in
the registers `r'` within `b` instructions. It gives the composition rules, a rule for counted
loops whose body implements a step function on an abstract state, and an evaluator `eval` for
commands, proved sound (`eval_sound`), with which loop-free commands are run symbolically.
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame)

/-- The number of stack registers is `K + 1`. -/
abbrev K : Nat := 255
abbrev Regs := Registers K
abbrev Reg := Fin (K + 1)

/-- From `r`, `c` halts with decision `true` in `r'` within `b` instructions. -/
def Ok (c : Command K) (r r' : Regs) (b : Nat) : Prop := ∃ t, Exec c r t (true, r') ∧ t ≤ b

theorem Ok.mono {c : Command K} {r r' : Regs} {b b' : Nat} (h : Ok c r r' b) (hb : b ≤ b') : Ok c r r' b' := by
  obtain ⟨t, he, ht⟩ := h; exact ⟨t, he, Nat.le_trans ht hb⟩

theorem Ok.seq {c₁ c₂ : Command K} {r r₁ r₂ : Regs} {b₁ b₂ : Nat} (h₁ : Ok c₁ r r₁ b₁) (h₂ : Ok c₂ r₁ r₂ b₂) :
    Ok (.seq c₁ c₂) r r₂ (b₁ + b₂) := by
  obtain ⟨t, he, ht⟩ := h₁; obtain ⟨s, he', hs⟩ := h₂
  exact ⟨t + s, Exec.seq he he', by omega⟩

theorem Ok.frame {c : Command K} {r r' : Regs} {b : Nat} (h : Ok c r r' b) (i : Reg) (hw : writes c i = false) :
    r' i = r i := by
  obtain ⟨t, he, -⟩ := h; exact exec_frame he i hw

theorem Ok.branch_nil {j : Reg} {e z o : Command K} {r r' : Regs} {b : Nat} (hr : r j = []) (h : Ok e r r' b) :
    Ok (.branch j e z o) r r' (b + 1) := by
  obtain ⟨t, he, ht⟩ := h; exact ⟨t + 1, Exec.branchEmpty hr he, by omega⟩

theorem Ok.branch_false {j : Reg} {e z o : Command K} {r r' : Regs} {b : Nat} {tl : List Bool}
    (hr : r j = false :: tl) (h : Ok z r r' b) : Ok (.branch j e z o) r r' (b + 1) := by
  obtain ⟨t, he, ht⟩ := h; exact ⟨t + 1, Exec.branchZero hr he, by omega⟩

theorem Ok.branch_true {j : Reg} {e z o : Command K} {r r' : Regs} {b : Nat} {tl : List Bool}
    (hr : r j = true :: tl) (h : Ok o r r' b) : Ok (.branch j e z o) r r' (b + 1) := by
  obtain ⟨t, he, ht⟩ := h; exact ⟨t + 1, Exec.branchOne hr he, by omega⟩

/-! ### Counted loops -/

/-- `n` applications of `f`, the first one innermost. -/
def iter {S : Type} (f : S → S) : Nat → S → S
  | 0, s => s
  | n + 1, s => iter f n (f s)

/-- A counted loop whose body implements the step `step` of an abstract state: `E s r` says that the
registers `r` represent `s`, and does not depend on the counter `j`. -/
theorem ok_repeat {S : Type} {j : Reg} {body : Command K} (hw : writes body j = false)
    (E : S → Regs → Prop) (step : S → S) (b : Nat)
    (hE : ∀ s r w, E s r → E s (set r j w))
    (hstep : ∀ s r, E s r → ∃ r', Ok body r r' b ∧ E (step s) r') :
    ∀ n s r, E s r → (r j).length = n → ∃ r', Ok (.repeat j body) r r' (n * (b + 1) + 2) ∧
      E (iter step n s) r' ∧ r' j = [] := by
  intro n
  induction n with
  | zero =>
    intro s r hs hn
    have hj : r j = [] := List.eq_nil_of_length_eq_zero hn
    exact ⟨r, ⟨2, Exec.repeatDone hj, by omega⟩, hs, hj⟩
  | succ n ih =>
    intro s r hs hn
    cases hj : r j with
    | nil => rw [hj] at hn; simp at hn
    | cons x tail =>
      rw [hj] at hn
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
      obtain ⟨r₁, ⟨t, he, ht⟩, hs₁⟩ := hstep s (set r j tail) (hE s r tail hs)
      have hmid : r₁ j = tail := by
        have := exec_frame he j hw
        simpa using this
      obtain ⟨r₂, ⟨t', he', ht'⟩, hs₂, hj₂⟩ := ih (step s) r₁ hs₁ (by rw [hmid]; exact hn)
      refine ⟨r₂, ⟨t + t' + 1, Exec.repeatNext hj he he', ?_⟩, ?_, hj₂⟩
      · simp only [Nat.succ_mul]; omega
      · exact hs₂

/-- A counted loop, with the counter preserved by every run of the body (stated semantically). -/
theorem ok_repeat' {S : Type} {j : Reg} {body : Command K}
    (E : S → Regs → Prop) (step : S → S) (b : Nat)
    (hE : ∀ s r w, E s r → E s (set r j w))
    (hstep : ∀ s r, E s r → ∃ r', Ok body r r' b ∧ E (step s) r' ∧ r' j = r j) :
    ∀ n s r, E s r → (r j).length = n → ∃ r', Ok (.repeat j body) r r' (n * (b + 1) + 2) ∧
      E (iter step n s) r' ∧ r' j = [] := by
  intro n
  induction n with
  | zero =>
    intro s r hs hn
    have hj : r j = [] := List.eq_nil_of_length_eq_zero hn
    exact ⟨r, ⟨2, Exec.repeatDone hj, by omega⟩, hs, hj⟩
  | succ n ih =>
    intro s r hs hn
    cases hj : r j with
    | nil => rw [hj] at hn; simp at hn
    | cons x tail =>
      rw [hj] at hn
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
      obtain ⟨r₁, ⟨t, he, ht⟩, hs₁, hj₁⟩ := hstep s (set r j tail) (hE s r tail hs)
      have hmid : r₁ j = tail := by rw [hj₁]; simp
      obtain ⟨r₂, ⟨t', he', ht'⟩, hs₂, hj₂⟩ := ih (step s) r₁ hs₁ (by rw [hmid]; exact hn)
      refine ⟨r₂, ⟨t + t' + 1, Exec.repeatNext hj he he', ?_⟩, hs₂, hj₂⟩
      simp only [Nat.succ_mul]; omega

theorem iter_succ' {S : Type} (f : S → S) : ∀ (n : Nat) (s : S), iter f (n + 1) s = f (iter f n s) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih => intro s; simp only [iter] at ih ⊢; rw [ih]

/-- A counted loop of `n` iterations with an invariant indexed by the number of iterations done. -/
theorem ok_repeatN {j : Reg} {body : Command K} (n : Nat) (I : Nat → Regs → Prop) (b : Nat)
    (hE : ∀ i r w, I i r → I i (set r j w))
    (hstep : ∀ i r, i < n → I i r → ∃ r', Ok body r r' b ∧ I (i + 1) r' ∧ r' j = r j) :
    ∀ r, I 0 r → (r j).length = n → ∃ r', Ok (.repeat j body) r r' (n * (b + 1) + 2) ∧ I n r' ∧ r' j = [] := by
  have key : ∀ m i r, i + m = n → I i r → (r j).length = m →
      ∃ r', Ok (.repeat j body) r r' (m * (b + 1) + 2) ∧ I n r' ∧ r' j = [] := by
    intro m
    induction m with
    | zero =>
      intro i r hi hr hm
      have hj : r j = [] := List.eq_nil_of_length_eq_zero hm
      have : i = n := by omega
      subst this
      exact ⟨r, ⟨2, Exec.repeatDone hj, by omega⟩, hr, hj⟩
    | succ m ih =>
      intro i r hi hr hm
      cases hj : r j with
      | nil => rw [hj] at hm; simp at hm
      | cons x tail =>
        rw [hj] at hm
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hm
        obtain ⟨r₁, ⟨t, he, ht⟩, hr₁, hj₁⟩ := hstep i (set r j tail) (by omega) (hE i r tail hr)
        have hmid : r₁ j = tail := by rw [hj₁]; simp
        obtain ⟨r₂, ⟨t', he', ht'⟩, hr₂, hj₂⟩ := ih (i + 1) r₁ (by omega) hr₁ (by rw [hmid]; exact hm)
        refine ⟨r₂, ⟨t + t' + 1, Exec.repeatNext hj he he', ?_⟩, hr₂, hj₂⟩
        simp only [Nat.succ_mul]; omega
  intro r hr hn
  exact key n 0 r (by omega) hr hn

/-! ### An evaluator -/

/-- Run a command, with `fuel` iterations allowed per counted loop; `none` if the fuel runs out or
a side condition of an arithmetic command fails. -/
def eval (fuel : Nat) : Command K → Regs → Option (Bool × Regs × Nat)
  | .stop b, r => some (b, r, 1)
  | .push j b, r => some (true, set r j (b :: r j), 2)
  | .pop j, r => some (true, set r j (r j).tail, 2)
  | .clear j, r => some (true, set r j [], (r j).length + 2)
  | .copy s d t, r =>
    if s ≠ d ∧ s ≠ t ∧ d ≠ t ∧ r t = [] then some (true, set r d (r s), (r d).length + 5 * (r s).length + 6)
    else none
  | .length s d t, r =>
    if s ≠ d ∧ s ≠ t ∧ d ≠ t ∧ r t = [] then
      some (true, set r d (List.replicate (r s).length true), (r d).length + 5 * (r s).length + 6)
    else none
  | .add s d t, r =>
    if s ≠ d ∧ s ≠ t ∧ d ≠ t ∧ r t = [] then
      some (true, set r d (List.replicate (r s).length true ++ r d), 5 * (r s).length + 4)
    else none
  | .multiply .., _ => none
  | .prependNat .., _ => none
  | .prependLiteral .., _ => none
  | .seq a b, r =>
    match eval fuel a r with
    | some (true, r₁, t₁) => (eval fuel b r₁).map fun (d, r₂, t₂) => (d, r₂, t₁ + t₂)
    | some (false, r₁, t₁) => some (false, r₁, t₁)
    | none => none
  | .ifThenElse test yes no, r =>
    match eval fuel test r with
    | some (true, r₁, t₁) => (eval fuel yes r₁).map fun (d, r₂, t₂) => (d, r₂, t₁ + t₂)
    | some (false, r₁, t₁) => (eval fuel no r₁).map fun (d, r₂, t₂) => (d, r₂, t₁ + t₂)
    | none => none
  | .branch j e z o, r =>
    match r j with
    | [] => (eval fuel e r).map fun (d, r₂, t₂) => (d, r₂, t₂ + 1)
    | false :: _ => (eval fuel z r).map fun (d, r₂, t₂) => (d, r₂, t₂ + 1)
    | true :: _ => (eval fuel o r).map fun (d, r₂, t₂) => (d, r₂, t₂ + 1)
  | .repeat j body, r => evalRepeat j (eval fuel body) fuel r
where
  /-- At most `n` iterations of a counted loop. -/
  evalRepeat (j : Reg) (body : Regs → Option (Bool × Regs × Nat)) : Nat → Regs → Option (Bool × Regs × Nat)
    | n, r =>
      match r j with
      | [] => some (true, r, 2)
      | _ :: tail =>
        match n with
        | 0 => none
        | n + 1 =>
          match body (set r j tail) with
          | some (true, r₁, t₁) => (evalRepeat j body n r₁).map fun (d, r₂, t₂) => (d, r₂, t₁ + t₂ + 1)
          | some (false, r₁, t₁) => some (false, r₁, t₁ + 1)
          | none => none

theorem eval_sound (fuel : Nat) :
    ∀ (c : Command K) (r : Regs) (d : Bool) (r' : Regs) (t : Nat), eval fuel c r = some (d, r', t) →
      Exec c r t (d, r') := by
  intro c
  induction c with
  | stop b => intro r d r' t h; simp [eval] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.stop _ _
  | push j b => intro r d r' t h; simp [eval] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.push _ _ _
  | pop j => intro r d r' t h; simp [eval] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.pop _ _
  | clear j => intro r d r' t h; simp [eval] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.clear _ _
  | copy s dd tt =>
    intro r d r' t h
    simp only [eval] at h
    split at h
    · next hc => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.copy hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · simp at h
  | length s dd tt =>
    intro r d r' t h
    simp only [eval] at h
    split at h
    · next hc => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.length hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · simp at h
  | add s dd tt =>
    intro r d r' t h
    simp only [eval] at h
    split at h
    · next hc => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.add hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · simp at h
  | multiply => intro r d r' t h; simp [eval] at h
  | prependNat => intro r d r' t h; simp [eval] at h
  | prependLiteral => intro r d r' t h; simp [eval] at h
  | seq a b iha ihb =>
    intro r d r' t h
    simp only [eval] at h
    split at h
    · next r₁ t₁ h₁ =>
      cases h₂ : eval fuel b r₁ with
      | none => rw [h₂] at h; simp at h
      | some v =>
        obtain ⟨d₂, r₂, t₂⟩ := v
        rw [h₂] at h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
        exact Exec.seq (iha r true r₁ t₁ h₁) (ihb r₁ _ _ _ h₂)
    · next r₁ t₁ h₁ => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.seqFailure (iha r false r₁ t₁ h₁)
    · simp at h
  | ifThenElse test yes no iht ihy ihn =>
    intro r d r' t h
    simp only [eval] at h
    split at h
    · next r₁ t₁ h₁ =>
      cases h₂ : eval fuel yes r₁ with
      | none => rw [h₂] at h; simp at h
      | some v =>
        obtain ⟨d₂, r₂, t₂⟩ := v
        rw [h₂] at h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
        exact Exec.ifTrue (iht r true r₁ t₁ h₁) (ihy r₁ _ _ _ h₂)
    · next r₁ t₁ h₁ =>
      cases h₂ : eval fuel no r₁ with
      | none => rw [h₂] at h; simp at h
      | some v =>
        obtain ⟨d₂, r₂, t₂⟩ := v
        rw [h₂] at h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
        exact Exec.ifFalse (iht r false r₁ t₁ h₁) (ihn r₁ _ _ _ h₂)
    · simp at h
  | branch j e z o ihe ihz iho =>
    intro r d r' t h
    simp only [eval] at h
    split at h
    · next hj =>
      cases h₂ : eval fuel e r with
      | none => rw [h₂] at h; simp at h
      | some v =>
        obtain ⟨d₂, r₂, t₂⟩ := v
        rw [h₂] at h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
        exact Exec.branchEmpty hj (ihe r _ _ _ h₂)
    · next tl hj =>
      cases h₂ : eval fuel z r with
      | none => rw [h₂] at h; simp at h
      | some v =>
        obtain ⟨d₂, r₂, t₂⟩ := v
        rw [h₂] at h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
        exact Exec.branchZero hj (ihz r _ _ _ h₂)
    · next tl hj =>
      cases h₂ : eval fuel o r with
      | none => rw [h₂] at h; simp at h
      | some v =>
        obtain ⟨d₂, r₂, t₂⟩ := v
        rw [h₂] at h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
        exact Exec.branchOne hj (iho r _ _ _ h₂)
  | «repeat» j body ih =>
    intro r d r' t h
    simp only [eval] at h
    suffices key : ∀ n r d r' t, eval.evalRepeat j (eval fuel body) n r = some (d, r', t) →
        Exec (.repeat j body) r t (d, r') from key fuel r d r' t h
    intro n
    induction n with
    | zero =>
      intro r d r' t h
      unfold eval.evalRepeat at h
      split at h
      · next hj => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.repeatDone hj
      · simp at h
    | succ n ihn =>
      intro r d r' t h
      unfold eval.evalRepeat at h
      split at h
      · next hj => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.repeatDone hj
      · next x tail hj =>
        simp only at h
        split at h
        · next r₁ t₁ h₁ =>
          cases h₂ : eval.evalRepeat j (eval fuel body) n r₁ with
          | none => rw [h₂] at h; simp at h
          | some v =>
            obtain ⟨d₂, r₂, t₂⟩ := v
            rw [h₂] at h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
            exact Exec.repeatNext hj (ih _ true r₁ t₁ h₁) (ihn r₁ _ _ _ h₂)
        · next r₁ t₁ h₁ => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Exec.repeatFailure hj (ih _ false r₁ t₁ h₁)
        · simp at h

theorem ok_of_eval {c : Command K} {r r' : Regs} {t b : Nat} (fuel : Nat) (h : eval fuel c r = some (true, r', t))
    (hb : t ≤ b) : Ok c r r' b :=
  ⟨t, eval_sound fuel c r true r' t h, hb⟩

/-! ### Registers -/

@[simp] theorem set_same' (r : Regs) (j : Reg) (v : List Bool) : set r j v j = v := StackMachine.set_same r j v

theorem set_apply (r : Regs) (j i : Reg) (v : List Bool) : set r j v i = if i = j then v else r i := rfl

/-- Run a command with the evaluator and check a property of the result. -/
theorem ok_of_evalP {c : Command K} {r : Regs} {b : Nat} {P : Regs → Prop} (fuel : Nat)
    (h : match eval fuel c r with
      | some (true, r', t) => t ≤ b ∧ P r'
      | _ => False) : ∃ r', Ok c r r' b ∧ P r' := by
  cases he : eval fuel c r with
  | none => rw [he] at h; exact h.elim
  | some v =>
    obtain ⟨d, r', t⟩ := v
    rw [he] at h
    cases d with
    | false => exact h.elim
    | true => exact ⟨r', ok_of_eval fuel he h.1, h.2⟩

/-! ### The layout of the registers -/

/-- The input word, and at the end the output word. -/
@[simp] abbrev INP : Reg := 0
/-- The emitted output bits, last first. -/
@[simp] abbrev OUTB : Reg := 1
/-- The memory, as a list of entries. -/
@[simp] abbrev MEM : Reg := 2
/-- The fuel: one bit per allowed iteration of a loop. -/
@[simp] abbrev FUEL : Reg := 3
/-- The scratch registers of the arithmetic. -/
@[simp] abbrev XA : Reg := 4
@[simp] abbrev XB : Reg := 5
@[simp] abbrev XZ : Reg := 6
@[simp] abbrev XC : Reg := 7
@[simp] abbrev XT : Reg := 8
/-- The scratch register of `copy`, `length` and `add`: always empty. -/
@[simp] abbrev XU : Reg := 9
/-- The scratch registers of the memory scan. -/
@[simp] abbrev XK : Reg := 10
@[simp] abbrev XW : Reg := 11
@[simp] abbrev XV : Reg := 12
@[simp] abbrev XF : Reg := 13
@[simp] abbrev XP : Reg := 14
@[simp] abbrev XM : Reg := 15
@[simp] abbrev XQ : Reg := 16
@[simp] abbrev XE : Reg := 17

/-- Do nothing. -/
def skipC : Command K := .stop true

theorem ok_skip (r : Regs) : Ok skipC r r 1 := ⟨1, Exec.stop true r, Nat.le_refl _⟩

/-! ### Primitive commands -/

theorem ok_push (j : Reg) (b : Bool) (r : Regs) : Ok (.push j b) r (set r j (b :: r j)) 2 :=
  ⟨2, Exec.push j b r, Nat.le_refl _⟩

theorem ok_pop (j : Reg) (r : Regs) : Ok (.pop j) r (set r j (r j).tail) 2 :=
  ⟨2, Exec.pop j r, Nat.le_refl _⟩

theorem ok_clear (j : Reg) (r : Regs) : Ok (.clear j) r (set r j []) ((r j).length + 2) :=
  ⟨_, Exec.clear j r, Nat.le_refl _⟩

theorem ok_copy {s d t : Reg} (h1 : s ≠ d) (h2 : s ≠ t) (h3 : d ≠ t) (r : Regs) (ht : r t = []) :
    Ok (.copy s d t) r (set r d (r s)) ((r d).length + 5 * (r s).length + 6) :=
  ⟨_, Exec.copy h1 h2 h3 ht, Nat.le_refl _⟩

theorem ok_length {s d t : Reg} (h1 : s ≠ d) (h2 : s ≠ t) (h3 : d ≠ t) (r : Regs) (ht : r t = []) :
    Ok (.length s d t) r (set r d (List.replicate (r s).length true)) ((r d).length + 5 * (r s).length + 6) :=
  ⟨_, Exec.length h1 h2 h3 ht, Nat.le_refl _⟩

theorem ok_addU {s d t : Reg} (h1 : s ≠ d) (h2 : s ≠ t) (h3 : d ≠ t) (r : Regs) (ht : r t = []) :
    Ok (.add s d t) r (set r d (List.replicate (r s).length true ++ r d)) (5 * (r s).length + 4) :=
  ⟨_, Exec.add h1 h2 h3 ht, Nat.le_refl _⟩

end STACS2027.Sim
