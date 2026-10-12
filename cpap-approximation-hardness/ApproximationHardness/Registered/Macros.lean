module

public import ApproximationHardness.Registered.Registers
import Lean.Elab.Tactic.Omega

/-!
# Macro commands: unary input, comparison, record emission

Each macro is a structured stack command with a partial model and a
specification (`Spec`). The models are written with the foundation's parsers
(`readNat`), so that on encoded input they evaluate by the parser lemmas.
-/

@[expose] public section

namespace STACS2027.Registered

open Complexity
open Complexity.SAT
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame readUnaryC readUnaryC_spec unaryModel drainBody
  drain_spec unaryModel_of_readNat unaryModel_of_readNat_none)

/-! ### Reading a unary numeral -/

/-- Empty `dst`, then pop `1^v 0` from `src` and push `v` ones onto `dst`. -/
def readUnary (src dst : Reg) : Command K := .seq (.clear dst) (readUnaryC src dst R.g)

def readUnaryModel (src dst : Reg) (r : Regs) : Option Regs :=
  match readNat (r src) with
  | some (v, rest) => some (set (set r src rest) dst (unary v))
  | none => none

theorem readUnaryModel_writeNat (src dst : Reg) (r : Regs) (v : Nat) (rest : SAT.Word)
    (h : r src = writeNat v ++ rest) :
    readUnaryModel src dst r = some (set (set r src rest) dst (unary v)) := by
  simp [readUnaryModel, h]

theorem readUnary_writes (src dst i : Reg) (hs : i ≠ src) (hd : i ≠ dst) (hg : i ≠ R.g) :
    writes (readUnary src dst) i = false := by
  simp [readUnary, writes, readUnaryC, Complexity.Restricted.readUnaryBody, hs, hd, hg]

theorem Spec.readUnary (src dst : Reg) (hsd : src ≠ dst) (hsg : src ≠ R.g) (hdg : dst ≠ R.g)
    {P : Regs → Prop} {L : Nat} (hg : ∀ r, P r → r R.g = [])
    (hL : ∀ r, P r → (r src).length ≤ L ∧ (r dst).length ≤ L) :
    Spec (readUnary src dst) P (9 * L + 10) (readUnaryModel src dst) := by
  have s1 := Spec.clear dst (P := P) (L := L) (fun r hr => (hL r hr).2)
  have s2 : Spec (readUnaryC src dst R.g) (fun r' => ∃ r, P r ∧ r' = set r dst []) (8 * L + 8)
      (fun r => match readNat (r src) with
        | some (v, rest) => some (set (set r src rest) dst (unary v ++ r dst))
        | none => none) := by
    rintro r' ⟨r, hr, rfl⟩
    have hg' : set r dst [] R.g = [] := by simp [StackMachine.set, Ne.symm hdg, hg r hr]
    obtain ⟨t, r'', he, ht, h1, h2, h3, h4⟩ := readUnaryC_spec src dst R.g hsd hsg hdg _ hg'
    refine ⟨t, _, he, ?_, ?_⟩
    · have := (hL r hr).1
      have e : set r dst [] src = r src := by simp [StackMachine.set, hsd]
      rw [e] at ht
      omega
    · dsimp only
      cases hn : readNat (set r dst [] src) with
      | none =>
        have hf := unaryModel_of_readNat_none (set r dst [] dst) hn
        simp only [Realizes]
        exact hf
      | some p =>
        obtain ⟨v, rest⟩ := p
        have hu := unaryModel_of_readNat (d := set r dst [] dst) hn
        rw [hu] at h1 h2 ⊢
        simp only [Realizes, Prod.mk.injEq, true_and]
        funext i
        by_cases hi : i = dst
        · subst hi; simp [StackMachine.set, h2, unary]
        · by_cases hi' : i = src
          · subst hi'; simp [StackMachine.set, hsd, h1]
          · by_cases hi'' : i = R.g
            · subst hi''; simp [StackMachine.set, Ne.symm hsg, Ne.symm hdg, h3, hg r hr]
            · simp [StackMachine.set, hi, hi', h4 i hi' hi hi'']
  have h := s1.seq (fun r r' hr hm => ⟨r, hr, by simpa using hm.symm⟩) s2
  refine (h.mono (fun r hr => hr) (by omega)).congr ?_
  intro r hr
  simp only [Option.bind_some, readUnaryModel]
  have e : set r dst [] src = r src := by simp [StackMachine.set, hsd]
  rw [e]
  cases readNat (r src) with
  | none => rfl
  | some p =>
    obtain ⟨v, rest⟩ := p
    simp only [Option.some.injEq]
    funext i
    by_cases hi : i = dst
    · subst hi; simp [StackMachine.set]
    · simp [StackMachine.set, hi]

/-! ### Comparing two unary registers -/

/-- Decide `|x| ≤ |y|`, leaving every register as it was. -/
def leU (x y : Reg) : Command K :=
  .seq (.copy x R.t1 R.s) (.seq (.copy y R.t2 R.s)
    (.ifThenElse (.repeat R.t1 (drainBody R.t2))
      (.seq (.clear R.t2) (.stop true))
      (.seq (.clear R.t1) (.stop false))))

theorem SpecT.leU (x y : Reg) (hx1 : x ≠ R.t1) (_hx2 : x ≠ R.t2) (hxs : x ≠ R.s)
    (hy1 : y ≠ R.t1) (hy2 : y ≠ R.t2) (hys : y ≠ R.s) {P : Regs → Prop} {L : Nat}
    (hs : ∀ r, P r → r R.s = []) (h1 : ∀ r, P r → r R.t1 = []) (h2 : ∀ r, P r → r R.t2 = [])
    (hL : ∀ r, P r → (r x).length ≤ L ∧ (r y).length ≤ L) :
    SpecT (leU x y) P (15 * L + 18) (fun r => (decide ((r x).length ≤ (r y).length), r)) := by
  intro r hr
  have hsr := hs r hr
  have h1r := h1 r hr
  have h2r := h2 r hr
  obtain ⟨hxL, hyL⟩ := hL r hr
  let r₁ := set r R.t1 (r x)
  have hc1 : Exec (.copy x R.t1 R.s) r ((r R.t1).length + 5 * (r x).length + 6) (true, r₁) :=
    Exec.copy hx1 hxs (by decide) hsr
  let r₂ := set r₁ R.t2 (r₁ y)
  have hc2 : Exec (.copy y R.t2 R.s) r₁ ((r₁ R.t2).length + 5 * (r₁ y).length + 6) (true, r₂) :=
    Exec.copy (r := r₁) hy2 hys (by decide) (by simp +decide [r₁, hsr])
  have e1 : r₁ R.t2 = [] := by simp +decide [r₁, h2r]
  have e2 : r₁ y = r y := by simp [r₁, hy1]
  obtain ⟨td, r₃, hd, htd, hle, hgt, hfr⟩ := drain_spec R.t1 R.t2 (by decide) (r x) (r y) r₂
    (by simp +decide [r₂, r₁, StackMachine.set]) (by simp [r₂, e2])
  have hback : ∀ (r' : Regs), r' R.t1 = [] → r' R.t2 = [] →
      (∀ j, j ≠ R.t1 → j ≠ R.t2 → r' j = r₂ j) → r' = r := by
    intro r' e1 e2 e3
    funext j
    by_cases j1 : j = R.t1
    · subst j1; rw [e1, h1r]
    · by_cases j2 : j = R.t2
      · subst j2; rw [e2, h2r]
      · rw [e3 j j1 j2]
        simp [r₂, r₁, StackMachine.set, j1, j2]
  show ∃ t, Exec (Registered.leU x y) r t (decide ((r x).length ≤ (r y).length), r) ∧ t ≤ 15 * L + 18
  by_cases hab : (r x).length ≤ (r y).length
  · obtain ⟨hx3, hy3⟩ := hle hab
    have hdec : decide ((r x).length ≤ (r y).length) = true := by simp [hab]
    rw [hdec] at hd ⊢
    let r₄ := set r₃ R.t2 []
    have hcl : Exec (.seq (.clear R.t2) (.stop true)) r₃ ((r₃ R.t2).length + 2 + 1) (true, r₄) :=
      Exec.seq (Exec.clear R.t2 r₃) (Exec.stop _ _)
    have hr₄ : r₄ = r := by
      apply hback r₄ (by simp +decide [r₄, hx3]) (by simp [r₄])
      intro j hj1 hj2
      simp [r₄, hj2, hfr j hj1 hj2]
    refine ⟨(r R.t1).length + 5 * (r x).length + 6 + ((r₁ R.t2).length + 5 * (r₁ y).length + 6 +
      (td + ((r₃ R.t2).length + 2 + 1))), ?_, ?_⟩
    · have hex : Exec (Registered.leU x y) r _ (true, r₄) :=
        Exec.seq hc1 (Exec.seq hc2 (Exec.ifTrue hd hcl))
      rw [hr₄] at hex
      exact hex
    · rw [h1r, e1, e2]
      simp only [List.length_nil]
      omega
  · obtain ⟨hy3, hx3⟩ := hgt hab
    have hdec : decide ((r x).length ≤ (r y).length) = false := by simp [hab]
    rw [hdec] at hd ⊢
    let r₄ := set r₃ R.t1 []
    have hcl : Exec (.seq (.clear R.t1) (.stop false)) r₃ ((r₃ R.t1).length + 2 + 1) (false, r₄) :=
      Exec.seq (Exec.clear R.t1 r₃) (Exec.stop _ _)
    have hr₄ : r₄ = r := by
      apply hback r₄ (by simp [r₄]) (by simp +decide [r₄, hy3])
      intro j hj1 hj2
      simp [r₄, hj1, hfr j hj1 hj2]
    refine ⟨(r R.t1).length + 5 * (r x).length + 6 + ((r₁ R.t2).length + 5 * (r₁ y).length + 6 +
      (td + ((r₃ R.t1).length + 2 + 1))), ?_, ?_⟩
    · have hex : Exec (Registered.leU x y) r _ (false, r₄) :=
        Exec.seq hc1 (Exec.seq hc2 (Exec.ifFalse hd hcl))
      rw [hr₄] at hex
      exact hex
    · rw [h1r, e1, e2]
      simp only [List.length_nil]
      omega

/-! ### Emitting edge records -/

/-- An endpoint number: the length of a base register plus a constant or the length of
an offset register. -/
inductive Endpoint where
  | const (base : Reg) (c : Nat)
  | reg (base : Reg) (off : Reg)

def Endpoint.value : Endpoint → Regs → Nat
  | .const base c, r => (r base).length + c
  | .reg base off, r => (r base).length + (r off).length

/-- The constant of an endpoint (`0` for a register offset). -/
def Endpoint.constant : Endpoint → Nat
  | .const _ c => c
  | .reg _ _ => 0

/-- Compute the endpoint on `tmp` and prepend its (positive) literal code to the output. -/
def emitEndpoint : Endpoint → Command K
  | .const base c => .seq (.copy base R.tmp R.s) (.seq (pushN R.tmp c)
      (.seq (.prependLiteral R.tmp R.out R.s true) (.clear R.tmp)))
  | .reg base off => .seq (.copy base R.tmp R.s) (.seq (.add off R.tmp R.s)
      (.seq (.prependLiteral R.tmp R.out R.s true) (.clear R.tmp)))

def emitEndpointModel (e : Endpoint) (r : Regs) : Regs :=
  set r R.out (encodeLiteral ⟨e.value r, true⟩ ++ r R.out)

/-- `Good e a b r`: the base register of `e` has at most `a` bits and its offset register
at most `b`. -/
def Endpoint.Good (e : Endpoint) (a b : Nat) (r : Regs) : Prop :=
  match e with
  | .const base _ => (r base).length ≤ a
  | .reg base off => (r base).length ≤ a ∧ (r off).length ≤ b

theorem Endpoint.value_le {e : Endpoint} {a b c : Nat} {r : Regs} (h : e.Good a b r)
    (hc : e.constant ≤ c) : e.value r ≤ a + b + c := by
  cases e with
  | const base k => simp only [Endpoint.Good] at h; simp only [Endpoint.constant] at hc
                    simp only [Endpoint.value]; omega
  | reg base off => simp only [Endpoint.Good] at h; simp only [Endpoint.value]; omega

/-- The endpoint registers are none of the registers written by an emission. -/
def Endpoint.Sane : Endpoint → Prop
  | .const base _ => base ≠ R.tmp ∧ base ≠ R.s ∧ base ≠ R.out ∧ base ≠ R.cnt
  | .reg base off => base ≠ R.tmp ∧ base ≠ R.s ∧ base ≠ R.out ∧ base ≠ R.cnt ∧
      off ≠ R.tmp ∧ off ≠ R.s ∧ off ≠ R.out ∧ off ≠ R.cnt

theorem Endpoint.value_set (d : Endpoint) (hd : d.Sane) (r : Regs) (j : Reg)
    (hj : j = R.out ∨ j = R.cnt ∨ j = R.tmp ∨ j = R.s) (w : SAT.Word) :
    d.value (set r j w) = d.value r := by
  cases d with
  | const base k =>
    obtain ⟨h1, h2, h3, h4⟩ := hd
    have hb : base ≠ j := by rcases hj with rfl | rfl | rfl | rfl <;> assumption
    simp [Endpoint.value, StackMachine.set, hb]
  | reg base off =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hd
    have hb : base ≠ j := by rcases hj with rfl | rfl | rfl | rfl <;> assumption
    have ho : off ≠ j := by rcases hj with rfl | rfl | rfl | rfl <;> assumption
    simp [Endpoint.value, StackMachine.set, hb, ho]

theorem pushN_writes (j i : Reg) (n : Nat) (hi : i ≠ j) : writes (pushN j n) i = false := by
  induction n with
  | zero => simp [pushN, writes]
  | succ n ih => simp [pushN, writes, ih, hi]

theorem emitEndpoint_writes (e : Endpoint) (i : Reg) (hi : i ≠ R.out) (hi' : i ≠ R.tmp) :
    writes (emitEndpoint e) i = false := by
  cases e with
  | const base c => simp [emitEndpoint, writes, hi, hi', pushN_writes R.tmp i c hi']
  | reg base off => simp [emitEndpoint, writes, hi, hi']

theorem Spec.emitEndpoint (e : Endpoint) (hsane : e.Sane) {P : Regs → Prop} {a b c : Nat}
    (hc : e.constant ≤ c)
    (hs : ∀ r, P r → r R.s = []) (htmp : ∀ r, P r → r R.tmp = [])
    (hgood : ∀ r, P r → e.Good a b r) :
    Spec (emitEndpoint e) P (11 * a + 11 * b + 8 * c + 20) (fun r => some (emitEndpointModel e r)) := by
  cases e with
  | const base k =>
    obtain ⟨hbt, hbs, hbo, _⟩ := hsane
    simp only [Endpoint.constant] at hc
    let f₁ : Regs → Regs := fun r => set r R.tmp (r base)
    let f₂ : Regs → Regs := fun r => set (f₁ r) R.tmp (List.replicate k true ++ f₁ r R.tmp)
    let f₃ : Regs → Regs := fun r => set (f₂ r) R.out (encodeLiteral ⟨(f₂ r R.tmp).length, true⟩ ++ f₂ r R.out)
    have s1 := Spec.copy (P := P) (a := a) (b := 0) hbt hbs (by decide) hs
      (fun r hr => ⟨hgood r hr, by rw [htmp r hr]; exact Nat.le_refl _⟩)
    have s2 := Spec.pushN R.tmp k (fun r' => ∃ r, P r ∧ r' = f₁ r)
    have s3 := Spec.prependLiteral (number := R.tmp) (output := R.out) (scratch := R.s) true
      (by decide) (by decide) (by decide) (P := fun r' => ∃ r, P r ∧ r' = f₂ r) (a := a + c)
      (by rintro r' ⟨r, hr, rfl⟩; simp +decide [f₂, f₁, hs r hr])
      (by
        rintro r' ⟨r, hr, rfl⟩
        have := hgood r hr
        simp only [Endpoint.Good] at this
        simp +decide [f₂, f₁, List.length_append, List.length_replicate]
        omega)
    have s4 := Spec.clear R.tmp (P := fun r' => ∃ r, P r ∧ r' = f₃ r) (L := a + c) (by
        rintro r' ⟨r, hr, rfl⟩
        have := hgood r hr
        simp only [Endpoint.Good] at this
        simp +decide [f₃, f₂, f₁, StackMachine.set, List.length_append, List.length_replicate]
        omega)
    have h := s1.seq (fun r r' hr hm => ⟨r, hr, by simpa [f₁] using hm.symm⟩)
      (s2.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa [f₂] using hm.symm⟩)
        (s3.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa [f₃] using hm.symm⟩) s4))
    refine (h.mono (fun r hr => hr) ?_).congr ?_
    · omega
    · intro r hr
      simp only [Option.bind_some, Option.some.injEq, emitEndpointModel, Endpoint.value]
      funext i
      by_cases hi : i = R.out
      · subst hi
        simp +decide [StackMachine.set, List.length_append, List.length_replicate]
        rw [Nat.add_comm]
      · by_cases hi' : i = R.tmp
        · subst hi'; simp +decide [StackMachine.set, htmp r hr]
        · simp [StackMachine.set, hi, hi']
  | reg base off =>
    obtain ⟨hbt, hbs, hbo, _, hot, hos, hoo, _⟩ := hsane
    let f₁ : Regs → Regs := fun r => set r R.tmp (r base)
    let f₂ : Regs → Regs := fun r => set (f₁ r) R.tmp (List.replicate (f₁ r off).length true ++ f₁ r R.tmp)
    let f₃ : Regs → Regs := fun r => set (f₂ r) R.out (encodeLiteral ⟨(f₂ r R.tmp).length, true⟩ ++ f₂ r R.out)
    have s1 := Spec.copy (P := P) (a := a) (b := 0) hbt hbs (by decide) hs
      (fun r hr => ⟨(hgood r hr).1, by rw [htmp r hr]; exact Nat.le_refl _⟩)
    have s2 := Spec.add (src := off) (dst := R.tmp) (scratch := R.s) hot hos (by decide)
      (P := fun r' => ∃ r, P r ∧ r' = f₁ r) (a := b)
      (by rintro r' ⟨r, hr, rfl⟩; simp +decide [f₁, hs r hr])
      (by rintro r' ⟨r, hr, rfl⟩; have := (hgood r hr).2; simpa [f₁, StackMachine.set, hot] using this)
    have s3 := Spec.prependLiteral (number := R.tmp) (output := R.out) (scratch := R.s) true
      (by decide) (by decide) (by decide) (P := fun r' => ∃ r, P r ∧ r' = f₂ r) (a := a + b)
      (by rintro r' ⟨r, hr, rfl⟩; simp +decide [f₂, f₁, StackMachine.set, hs r hr])
      (by
        rintro r' ⟨r, hr, rfl⟩
        have := hgood r hr
        simp only [Endpoint.Good] at this
        simp +decide [f₂, f₁, hot, List.length_append, List.length_replicate]
        omega)
    have s4 := Spec.clear R.tmp (P := fun r' => ∃ r, P r ∧ r' = f₃ r) (L := a + b) (by
        rintro r' ⟨r, hr, rfl⟩
        have := hgood r hr
        simp only [Endpoint.Good] at this
        simp +decide [f₃, f₂, f₁, StackMachine.set, hot, List.length_append, List.length_replicate]
        omega)
    have h := s1.seq (fun r r' hr hm => ⟨r, hr, by simpa [f₁] using hm.symm⟩)
      (s2.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa [f₂] using hm.symm⟩)
        (s3.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa [f₃] using hm.symm⟩) s4))
    refine (h.mono (fun r hr => hr) ?_).congr ?_
    · omega
    · intro r hr
      simp only [Option.bind_some, Option.some.injEq, emitEndpointModel, Endpoint.value]
      funext i
      by_cases hi : i = R.out
      · subst hi
        simp +decide [StackMachine.set, hot, List.length_append, List.length_replicate]
        rw [Nat.add_comm]
      · by_cases hi' : i = R.tmp
        · subst hi'; simp +decide [StackMachine.set, htmp r hr]
        · simp [StackMachine.set, hi, hi']

/-- The record of the edge from `e₁` to `e₂`: both literal codes, then the count `2`,
then one more record counted. -/
def emitEdge (e₁ e₂ : Endpoint) : Command K :=
  .seq (emitEndpoint e₂) (.seq (emitEndpoint e₁)
    (.seq (.prependNat R.two R.out R.s) (.push R.cnt true)))

/-- The record emitted for the endpoints `e₁`, `e₂` in state `r`. -/
def edgeRecord (e₁ e₂ : Endpoint) (r : Regs) : Clause :=
  [⟨e₁.value r, true⟩, ⟨e₂.value r, true⟩]

def emitEdgeModel (e₁ e₂ : Endpoint) (r : Regs) : Regs :=
  set (set r R.out (encodeClause (edgeRecord e₁ e₂ r) ++ r R.out)) R.cnt (true :: r R.cnt)

theorem encodeClause_two (l₁ l₂ : Literal) :
    encodeClause [l₁, l₂] = writeNat 2 ++ (encodeLiteral l₁ ++ (encodeLiteral l₂ ++ [])) := by
  simp [encodeClause, writeList, writeValues]

theorem Spec.emitEdge (e₁ e₂ : Endpoint) (h₁ : e₁.Sane) (h₂ : e₂.Sane) {P : Regs → Prop} {a b c : Nat}
    (hc₁ : e₁.constant ≤ c) (hc₂ : e₂.constant ≤ c)
    (hs : ∀ r, P r → r R.s = []) (htmp : ∀ r, P r → r R.tmp = [])
    (htwo : ∀ r, P r → r R.two = [true, true])
    (hg₁ : ∀ r, P r → e₁.Good a b r) (hg₂ : ∀ r, P r → e₂.Good a b r) :
    Spec (emitEdge e₁ e₂) P (22 * a + 22 * b + 16 * c + 58) (fun r => some (emitEdgeModel e₁ e₂ r)) := by
  have s1 := Spec.emitEndpoint e₂ h₂ hc₂ hs htmp hg₂
  have key : ∀ r, P r → e₁.value (emitEndpointModel e₂ r) = e₁.value r ∧
      e₂.value (emitEndpointModel e₂ r) = e₂.value r ∧
      (emitEndpointModel e₂ r) R.s = [] ∧ (emitEndpointModel e₂ r) R.tmp = [] ∧
      (emitEndpointModel e₂ r) R.two = [true, true] ∧
      e₁.Good a b (emitEndpointModel e₂ r) := by
    intro r hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · cases e₁ with
      | const base k =>
        obtain ⟨_, _, hbo, _⟩ := h₁
        simp [Endpoint.value, emitEndpointModel, StackMachine.set, hbo]
      | reg base off =>
        obtain ⟨_, _, hbo, _, _, _, hoo, _⟩ := h₁
        simp [Endpoint.value, emitEndpointModel, StackMachine.set, hbo, hoo]
    · cases e₂ with
      | const base k =>
        obtain ⟨_, _, hbo, _⟩ := h₂
        simp [Endpoint.value, emitEndpointModel, StackMachine.set, hbo]
      | reg base off =>
        obtain ⟨_, _, hbo, _, _, _, hoo, _⟩ := h₂
        simp [Endpoint.value, emitEndpointModel, StackMachine.set, hbo, hoo]
    · simp +decide [emitEndpointModel, StackMachine.set, hs r hr]
    · simp +decide [emitEndpointModel, StackMachine.set, htmp r hr]
    · simp +decide [emitEndpointModel, StackMachine.set, htwo r hr]
    · have := hg₁ r hr
      cases e₁ with
      | const base k =>
        obtain ⟨_, _, hbo, _⟩ := h₁
        simpa [Endpoint.Good, emitEndpointModel, StackMachine.set, hbo] using this
      | reg base off =>
        obtain ⟨_, _, hbo, _, _, _, hoo, _⟩ := h₁
        simpa [Endpoint.Good, emitEndpointModel, StackMachine.set, hbo, hoo] using this
  have s2 := Spec.emitEndpoint e₁ h₁ (P := fun r' => ∃ r, P r ∧ r' = emitEndpointModel e₂ r)
    (a := a) (b := b) (c := c) hc₁
    (by rintro r' ⟨r, hr, rfl⟩; exact (key r hr).2.2.1)
    (by rintro r' ⟨r, hr, rfl⟩; exact (key r hr).2.2.2.1)
    (by rintro r' ⟨r, hr, rfl⟩; exact (key r hr).2.2.2.2.2)
  have s3 := Spec.prependNat (number := R.two) (output := R.out) (scratch := R.s) (by decide) (by decide)
    (by decide) (P := fun r'' => ∃ r, P r ∧ r'' = emitEndpointModel e₁ (emitEndpointModel e₂ r)) (a := 2)
    (by rintro r'' ⟨r, hr, rfl⟩; simp +decide [emitEndpointModel, StackMachine.set, hs r hr])
    (by rintro r'' ⟨r, hr, rfl⟩; simp +decide [emitEndpointModel, StackMachine.set, htwo r hr])
  have s4 := Spec.push R.cnt true (fun r''' => ∃ r, P r ∧ r''' = set (emitEndpointModel e₁ (emitEndpointModel e₂ r))
    R.out (writeNat ((emitEndpointModel e₁ (emitEndpointModel e₂ r)) R.two).length ++
      (emitEndpointModel e₁ (emitEndpointModel e₂ r)) R.out))
  have h := s1.seq (fun r r' hr hm => ⟨r, hr, by simpa using hm.symm⟩)
    (s2.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa using hm.symm⟩)
      (s3.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa using hm.symm⟩) s4))
  refine (h.mono (fun r hr => hr) (by omega)).congr ?_
  intro r hr
  simp only [Option.bind_some, Option.some.injEq, emitEdgeModel]
  funext i
  by_cases hi : i = R.cnt
  · subst hi; simp +decide [emitEndpointModel, StackMachine.set]
  · by_cases hi' : i = R.out
    · subst hi'
      simp +decide [emitEndpointModel, StackMachine.set, htwo r hr, edgeRecord, encodeClause_two,
        Endpoint.value_set e₁ h₁ _ R.out (Or.inl rfl)]
    · simp [emitEndpointModel, StackMachine.set, hi, hi']

theorem emitEdge_writes (e₁ e₂ : Endpoint) (i : Reg) (hi : i ≠ R.out) (hi' : i ≠ R.tmp)
    (hc : i ≠ R.cnt) : writes (emitEdge e₁ e₂) i = false := by
  simp [emitEdge, writes, emitEndpoint_writes e₂ i hi hi', emitEndpoint_writes e₁ i hi hi', hi, hc]

/-- Emit the records of a list of edges, in order. -/
def emitEdges : List (Endpoint × Endpoint) → Command K
  | [] => .stop true
  | e :: es => .seq (emitEdge e.1 e.2) (emitEdges es)

/-- The word of the records of `es` (in state `r`), most recent record first. -/
def recordsWord (es : List (Endpoint × Endpoint)) (r : Regs) : SAT.Word :=
  writeValues encodeClause ((es.map (fun e => edgeRecord e.1 e.2 r)).reverse)

def emitEdgesModel (es : List (Endpoint × Endpoint)) (r : Regs) : Regs :=
  set (set r R.out (recordsWord es r ++ r R.out)) R.cnt (unary es.length ++ r R.cnt)

theorem writeValues_append {α : Type} (enc : α → SAT.Word) (xs ys : List α) :
    writeValues enc (xs ++ ys) = writeValues enc xs ++ writeValues enc ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [writeValues, ih]

/-- Emitting a record changes neither the endpoint values nor the `Good` bounds. -/
theorem Endpoint.value_emitEdgeModel (d e₁ e₂ : Endpoint) (hd : d.Sane) (r : Regs) :
    d.value (emitEdgeModel e₁ e₂ r) = d.value r := by
  cases d with
  | const base k =>
    obtain ⟨_, _, hbo, hbc⟩ := hd
    simp [Endpoint.value, emitEdgeModel, StackMachine.set, hbo, hbc]
  | reg base off =>
    obtain ⟨_, _, hbo, hbc, _, _, hoo, hoc⟩ := hd
    simp [Endpoint.value, emitEdgeModel, StackMachine.set, hbo, hbc, hoo, hoc]

theorem Endpoint.good_emitEdgeModel {d : Endpoint} {a b : Nat} (hd : d.Sane) (e₁ e₂ : Endpoint)
    {r : Regs} (h : d.Good a b r) : d.Good a b (emitEdgeModel e₁ e₂ r) := by
  cases d with
  | const base k =>
    obtain ⟨_, _, hbo, hbc⟩ := hd
    simpa [Endpoint.Good, emitEdgeModel, StackMachine.set, hbo, hbc] using h
  | reg base off =>
    obtain ⟨_, _, hbo, hbc, _, _, hoo, hoc⟩ := hd
    simpa [Endpoint.Good, emitEdgeModel, StackMachine.set, hbo, hbc, hoo, hoc] using h

theorem edgeRecord_emitEdgeModel (e : Endpoint × Endpoint) (e₁ e₂ : Endpoint) (r : Regs)
    (h₁ : e.1.Sane) (h₂ : e.2.Sane) :
    edgeRecord e.1 e.2 (emitEdgeModel e₁ e₂ r) = edgeRecord e.1 e.2 r := by
  simp [edgeRecord, Endpoint.value_emitEdgeModel _ _ _ h₁, Endpoint.value_emitEdgeModel _ _ _ h₂]

theorem recordsWord_emitEdgeModel (es : List (Endpoint × Endpoint)) (e₁ e₂ : Endpoint) (r : Regs)
    (hsane : ∀ e ∈ es, e.1.Sane ∧ e.2.Sane) :
    recordsWord es (emitEdgeModel e₁ e₂ r) = recordsWord es r := by
  unfold recordsWord
  congr 2
  apply List.map_congr_left
  intro e he
  exact edgeRecord_emitEdgeModel e e₁ e₂ r (hsane e he).1 (hsane e he).2

/-- The cost of emitting one edge whose endpoints are `Good a b c`. -/
def edgeCost (a b c : Nat) : Nat := 22 * a + 22 * b + 16 * c + 58

theorem Spec.emitEdges (es : List (Endpoint × Endpoint)) (hsane : ∀ e ∈ es, e.1.Sane ∧ e.2.Sane)
    {P : Regs → Prop} {a b c : Nat} (hconst : ∀ e ∈ es, e.1.constant ≤ c ∧ e.2.constant ≤ c)
    (hs : ∀ r, P r → r R.s = []) (htmp : ∀ r, P r → r R.tmp = [])
    (htwo : ∀ r, P r → r R.two = [true, true])
    (hgood : ∀ r, P r → ∀ e ∈ es, e.1.Good a b r ∧ e.2.Good a b r)
    (hP : ∀ r e₁ e₂, P r → P (emitEdgeModel e₁ e₂ r)) :
    Spec (emitEdges es) P (es.length * edgeCost a b c + 1) (fun r => some (emitEdgesModel es r)) := by
  induction es generalizing P with
  | nil =>
    have h := (Spec.stop_true P).congr (m' := fun r => some (emitEdgesModel [] r)) (by
      intro r _
      simp only [emitEdgesModel, recordsWord, List.map_nil, List.reverse_nil, writeValues,
        List.nil_append, List.length_nil, unary_zero, Option.some.injEq]
      funext i
      by_cases hi : i = R.cnt
      · subst hi; simp [StackMachine.set]
      · by_cases hi' : i = R.out
        · subst hi'; simp +decide [StackMachine.set]
        · simp [StackMachine.set, hi, hi'])
    simpa [Registered.emitEdges] using h
  | cons e es ih =>
    have h1 := Spec.emitEdge e.1 e.2 (hsane e (by simp)).1 (hsane e (by simp)).2 (P := P) (a := a) (b := b)
      (c := c) (hconst e (by simp)).1 (hconst e (by simp)).2 hs htmp htwo
      (fun r hr => (hgood r hr e (by simp)).1) (fun r hr => (hgood r hr e (by simp)).2)
    have h2 := ih (fun d hd => hsane d (by simp [hd])) (P := P) (fun d hd => hconst d (by simp [hd]))
      hs htmp htwo (fun r hr d hd => hgood r hr d (by simp [hd])) hP
    have h := h1.seq (P₂ := P) (fun r r' hr hm => by
      simp only [Option.some.injEq] at hm; subst hm; exact hP r e.1 e.2 hr) h2
    refine (h.mono (fun r hr => hr) ?_).congr ?_
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, edgeCost]
      omega
    · intro r hr
      simp only [Option.bind_some, Option.some.injEq, emitEdgesModel]
      rw [recordsWord_emitEdgeModel es e.1 e.2 r (fun d hd => hsane d (by simp [hd]))]
      funext i
      by_cases hi : i = R.cnt
      · subst hi
        simp +decide [emitEdgeModel, StackMachine.set, List.length_cons, List.replicate_succ,
          List.cons_append, unary, Complexity.Restricted.replicate_append_cons]
      · by_cases hi' : i = R.out
        · subst hi'
          simp +decide [emitEdgeModel, StackMachine.set, recordsWord, writeValues_append, writeValues]
        · simp [emitEdgeModel, StackMachine.set, hi, hi']

theorem emitEdges_writes (es : List (Endpoint × Endpoint)) (i : Reg) (hi : i ≠ R.out)
    (hi' : i ≠ R.tmp) (hc : i ≠ R.cnt) : writes (emitEdges es) i = false := by
  induction es with
  | nil => simp [emitEdges, writes]
  | cons e es ih =>
    simp only [emitEdges, writes, Bool.or_eq_false_iff]
    exact ⟨emitEdge_writes e.1 e.2 i hi hi' hc, ih⟩

end STACS2027.Registered
