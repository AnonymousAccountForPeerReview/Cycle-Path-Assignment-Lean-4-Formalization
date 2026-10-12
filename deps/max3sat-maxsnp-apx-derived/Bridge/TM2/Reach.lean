module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Complexity.StackCompile

/-!
# Bounded reachability for stack programs

Generic infrastructure used by the TM2 bridge: a counted multi-step relation on
`Complexity.StackProgram` configurations, a finite-label encoding obtained from a
`Fintype` instance, and polynomial bounds for evaluations of `Polynomial ℕ`.
-/

@[expose] public section

namespace Bridge

open Complexity.StackProgram
open Complexity.StackMachine (Registers set branch)

/-- `Steps p n q r q' r'`: exactly `n` non-halting instructions lead from `(q, r)` to `(q', r')`. -/
inductive Steps {k : Nat} {L : Type} (p : Program k L) :
    Nat → L → Registers k → L → Registers k → Prop where
  | refl (q : L) (r : Registers k) : Steps p 0 q r q r
  | head {q r q' r' n q'' r''} (h : step p q r = .inr (q', r'))
      (rest : Steps p n q' r' q'' r'') : Steps p (n + 1) q r q'' r''

/-- At most `B` non-halting instructions lead from `(q, r)` to `(q', r')`. -/
def Reach {k : Nat} {L : Type} (p : Program k L) (B : Nat) (q : L) (r : Registers k)
    (q' : L) (r' : Registers k) : Prop :=
  ∃ n, n ≤ B ∧ Steps p n q r q' r'

theorem Steps.trans {k : Nat} {L : Type} {p : Program k L} {n m q r q' r' q'' r''}
    (h₁ : Steps p n q r q' r') (h₂ : Steps p m q' r' q'' r'') :
    Steps p (n + m) q r q'' r'' := by
  induction h₁ with
  | refl => simpa using h₂
  | head h _ ih =>
    have := Steps.head h (ih h₂)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem Steps.run {k : Nat} {L : Type} {p : Program k L} {n m q r q' r' result}
    (h : Steps p n q r q' r') (hr : run p m q' r' = some result) :
    run p (n + m) q r = some result := by
  induction h with
  | refl => simpa using hr
  | head hs _ ih =>
    have h2 := ih hr
    rw [Nat.add_right_comm]
    simp only [Complexity.StackProgram.run, hs]
    exact h2

theorem step_length_le {k : Nat} {L : Type} {p : Program k L} {q r q' r'}
    (h : step p q r = .inr (q', r')) (j : Fin (k + 1)) :
    (r' j).length ≤ (r j).length + 1 := by
  unfold step at h
  cases hc : p.code q with
  | halt b => simp [hc] at h
  | goto a =>
    simp only [hc, Sum.inr.injEq, Prod.mk.injEq] at h
    rw [← h.2]; omega
  | push i b a =>
    simp only [hc, Sum.inr.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  | pop i e z o =>
    simp only [hc, Sum.inr.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [hj]
  | peek i e z o =>
    simp only [hc, Sum.inr.injEq, Prod.mk.injEq] at h
    rw [← h.2]; omega

theorem Steps.length_le {k : Nat} {L : Type} {p : Program k L} {n q r q' r'}
    (h : Steps p n q r q' r') (j : Fin (k + 1)) :
    (r' j).length ≤ (r j).length + n := by
  induction h with
  | refl => omega
  | head hs _ ih =>
    have := step_length_le hs j
    omega

namespace Reach

variable {k : Nat} {L : Type} {p : Program k L}

theorem refl (B : Nat) (q : L) (r : Registers k) : Reach p B q r q r :=
  ⟨0, Nat.zero_le _, .refl q r⟩

theorem single {q r q' r'} (h : step p q r = .inr (q', r')) : Reach p 1 q r q' r' :=
  ⟨1, Nat.le_refl _, .head h (.refl _ _)⟩

theorem trans {B₁ B₂ q r q' r' q'' r''} (h₁ : Reach p B₁ q r q' r')
    (h₂ : Reach p B₂ q' r' q'' r'') : Reach p (B₁ + B₂) q r q'' r'' := by
  obtain ⟨n, hn, h₁⟩ := h₁
  obtain ⟨m, hm, h₂⟩ := h₂
  exact ⟨n + m, Nat.add_le_add hn hm, h₁.trans h₂⟩

theorem mono {B B' q r q' r'} (h : Reach p B q r q' r') (hB : B ≤ B') :
    Reach p B' q r q' r' := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨n, Nat.le_trans hn hB, h⟩

theorem head {B q r q' r' q'' r''} (h : step p q r = .inr (q', r'))
    (rest : Reach p B q' r' q'' r'') : Reach p (B + 1) q r q'' r'' :=
  ((single h).trans rest).mono (by omega)

theorem length_le {B q r q' r'} (h : Reach p B q r q' r') (j : Fin (k + 1)) :
    (r' j).length ≤ (r j).length + B := by
  obtain ⟨n, hn, h⟩ := h
  have := h.length_le j
  omega

theorem run {B m q r q' r' result} (h : Reach p B q r q' r')
    (hr : Complexity.StackProgram.run p m q' r' = some result) :
    ∃ t, t ≤ B + m ∧ Complexity.StackProgram.run p t q r = some result := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨n + m, by omega, h.run hr⟩

end Reach

/-! ### One-step lemmas from the instruction at a label -/

section StepLemmas

variable {k : Nat} {L : Type} {p : Program k L}

theorem step_of_goto {q q' : L} (h : p.code q = .goto q') (r : Registers k) :
    step p q r = .inr (q', r) := by
  simp [step, h]

theorem step_of_push {q q' : L} {j : Fin (k + 1)} {b : Bool} (h : p.code q = .push j b q')
    (r : Registers k) : step p q r = .inr (q', set r j (b :: r j)) := by
  simp [step, h]

theorem step_of_pop {q e z o : L} {j : Fin (k + 1)} (h : p.code q = .pop j e z o)
    (r : Registers k) : step p q r = .inr (branch (r j) e z o, set r j (r j).tail) := by
  simp [step, h]

theorem step_of_peek {q e z o : L} {j : Fin (k + 1)} (h : p.code q = .peek j e z o)
    (r : Registers k) : step p q r = .inr (branch (r j) e z o, r) := by
  simp [step, h]

end StepLemmas

theorem branch_cons_same {α : Type} (b : Bool) (xs : List Bool) (e z : α) :
    branch (b :: xs) e z z = z := by
  cases b <;> rfl

theorem branch_bool {α : Type} (b : Bool) (xs : List Bool) (e : α) (f : Bool → α) :
    branch (b :: xs) e (f false) (f true) = f b := by
  cases b <;> rfl

theorem branch_replicate_same {α : Type} (n : Nat) (tl : List Bool) (e z : α) :
    branch (List.replicate n true ++ false :: tl) e z z = z := by
  cases n <;> rfl

/-- A pop/push loop moves a whole register onto another one, reversing it. -/
theorem reach_move {k : Nat} {L : Type} {p : Program k L} {src dst : Fin (k + 1)}
    (hne : src ≠ dst) {lp le : L} {la : Bool → L}
    (hpop : p.code lp = .pop src le (la false) (la true))
    (hpush : ∀ b, p.code (la b) = .push dst b lp)
    (w : List Bool) (r : Registers k) (hw : r src = w) :
    ∃ r', Reach p (2 * w.length + 1) lp r le r' ∧ r' src = [] ∧
      r' dst = w.reverse ++ r dst ∧ ∀ j, j ≠ src → j ≠ dst → r' j = r j := by
  induction w generalizing r with
  | nil =>
    have hstep : step p lp r = .inr (le, set r src []) := by
      rw [step_of_pop hpop r, hw]; rfl
    refine ⟨set r src [], (Reach.single hstep).mono (by omega), by simp, ?_, ?_⟩
    · simp [Complexity.StackMachine.set_other r hne.symm]
    · intro j hj _
      exact Complexity.StackMachine.set_other r hj _
  | cons b w ih =>
    have hstep : step p lp r = .inr (la b, set r src w) := by
      rw [step_of_pop hpop r, hw, branch_bool]; rfl
    have hstep2 := step_of_push (hpush b) (set r src w)
    obtain ⟨r', h, h1, h2, h3⟩ := ih (set (set r src w) dst (b :: set r src w dst))
      (by rw [Complexity.StackMachine.set_other _ hne, Complexity.StackMachine.set_same])
    refine ⟨r', ?_, h1, ?_, ?_⟩
    · refine (Reach.head hstep (Reach.head hstep2 h)).mono ?_
      simp only [List.length_cons]
      omega
    · rw [h2, Complexity.StackMachine.set_same,
        Complexity.StackMachine.set_other r hne.symm]
      simp
    · intro j hj hj'
      rw [h3 j hj hj', Complexity.StackMachine.set_other _ hj',
        Complexity.StackMachine.set_other r hj]

theorem iterate_bind_none {σ : Type} (f : σ → Option σ) (t : Nat) :
    (flip bind f)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    exact ih

/-! ### Encodings of finite label types -/

/-- Any finite label type with a designated element has an explicit finite encoding. -/
noncomputable def encodingOfFintype (L : Type) [Fintype L] (d : L) : Encoding L where
  states := Fintype.card L - 1
  encode q := ⟨(Fintype.equivFin L q).val, by
    have := (Fintype.equivFin L q).isLt
    omega⟩
  decode i := if h : i.val < Fintype.card L then (Fintype.equivFin L).symm ⟨i.val, h⟩ else d
  decode_encode q := by simp

/-- Running a compiled program on an input is running the program from its start label. -/
theorem runInput_compile {k : Nat} {L : Type} (p : Program k L) (e : Encoding L)
    (fuel : Nat) (input : List Bool) :
    Complexity.StackMachine.runInput (compile p e) fuel input =
      Complexity.StackProgram.run p fuel p.start (fun j => if j = 0 then input else []) := by
  exact compile_run p e fuel p.start _

/-! ### Polynomial evaluations are polynomially bounded -/

theorem polynomialBound_eval (P : Polynomial ℕ) : Complexity.PolynomialBound (fun n => P.eval n) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    simpa only [Polynomial.eval_monomial] using
      (Complexity.PolynomialBound.constant a).mul (Complexity.PolynomialBound.identity.pow n)

end Bridge
