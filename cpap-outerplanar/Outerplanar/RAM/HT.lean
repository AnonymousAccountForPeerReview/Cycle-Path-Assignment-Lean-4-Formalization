module

public import Outerplanar.RAM.Spec
import Mathlib.Tactic

/-!
# A Hoare logic with step bounds for the unit-cost RAM

`HT s P Q b`: from every configuration satisfying `P`, the program `s` halts in a
configuration satisfying `Q` within `b` steps. `HTt s P Q`: the same with a postcondition
that may mention the step count.

Rules: consequence, sequencing, branching, loop-free code (`HT.run`: the final
configuration is `run s c`), and loops by a potential (`HT.loop`): if every run of the body
from the invariant (with the test register nonzero) costs `t` steps and lowers a potential
`Φ` by at least `t + 1`, the loop costs at most `Φ` of the initial configuration plus one
step and ends in the invariant with the test register zero. Amortized analyses are
expressed by the potential.
-/

@[expose] public section

namespace STACS2027.RAM

/-- From every configuration satisfying `P`, `s` halts in one satisfying `Q c' t`, where
`t` is the number of steps. -/
def HTt (s : Stmt) (P : Config → Prop) (Q : Config → ℕ → Prop) : Prop :=
  ∀ c, P c → ∃ c' t, Exec s c t c' ∧ Q c' t

/-- From every configuration satisfying `P`, `s` halts within `b` steps in one satisfying
`Q`. -/
def HT (s : Stmt) (P Q : Config → Prop) (b : ℕ) : Prop :=
  HTt s P (fun c' t => Q c' ∧ t ≤ b)

namespace HT

variable {s u : Stmt} {P P' Q Q' R : Config → Prop} {b b' : ℕ}

theorem mono (h : HT s P Q b) (hP : ∀ c, P' c → P c) (hQ : ∀ c, Q c → Q' c) (hb : b ≤ b') :
    HT s P' Q' b' := by
  intro c hc
  obtain ⟨c', t, he, hq, ht⟩ := h c (hP c hc)
  exact ⟨c', t, he, hQ c' hq, le_trans ht hb⟩

theorem pre {P' : Config → Prop} (h : HT s P Q b) (hP : ∀ c, P' c → P c) : HT s P' Q b :=
  h.mono hP (fun _ h => h) le_rfl

theorem post {Q' : Config → Prop} (h : HT s P Q b) (hQ : ∀ c, Q c → Q' c) : HT s P Q' b :=
  h.mono (fun _ h => h) hQ le_rfl

theorem weaken (h : HT s P Q b) (hb : b ≤ b') : HT s P Q b' :=
  h.mono (fun _ h => h) (fun _ h => h) hb

/-- Sequencing. -/
theorem seq (h₁ : HT s P R b) (h₂ : HT u R Q b') : HT (.seq s u) P Q (b + b') := by
  intro c hc
  obtain ⟨c₁, t₁, he₁, hr, ht₁⟩ := h₁ c hc
  obtain ⟨c₂, t₂, he₂, hq, ht₂⟩ := h₂ c₁ hr
  exact ⟨c₂, t₁ + t₂, Exec.seq he₁ he₂, hq, by omega⟩

/-- Branching on a register. -/
theorem ifz {a : ℕ} (h₁ : HT s (fun c => P c ∧ c.reg a = 0) Q b)
    (h₂ : HT u (fun c => P c ∧ c.reg a ≠ 0) Q b) : HT (.ifz a s u) P Q (b + 1) := by
  intro c hc
  by_cases ha : c.reg a = 0
  · obtain ⟨c', t, he, hq, ht⟩ := h₁ c ⟨hc, ha⟩
    exact ⟨c', t + 1, Exec.ifzTrue ha he, hq, by omega⟩
  · obtain ⟨c', t, he, hq, ht⟩ := h₂ c ⟨hc, ha⟩
    exact ⟨c', t + 1, Exec.ifzFalse ha he, hq, by omega⟩

/-- Loop-free code: the final configuration is `run s c`. -/
theorem run (hs : LoopFree s) (h : ∀ c, P c → Q (RAM.run s c)) : HT s P Q (size s) := by
  intro c hc
  exact ⟨_, _, exec_run s hs c, h c hc, cost_le_size s c⟩

/-- A loop with a potential: every body run from the invariant (with the test register
nonzero) lowers the potential `Φ` by more than its step count; the loop then costs at most
the initial potential plus one step. -/
theorem loopPot {a : ℕ} {body : Stmt} {Inv : Config → Prop} (Φ : Config → ℕ)
    (hbody : ∀ v, HTt body (fun c => Inv c ∧ c.reg a ≠ 0 ∧ Φ c = v)
      (fun c' t => Inv c' ∧ Φ c' + t + 1 ≤ v)) :
    ∀ c, Inv c → ∃ c' t, Exec (.loop a body) c t c' ∧ Inv c' ∧ c'.reg a = 0 ∧
      t + Φ c' ≤ Φ c + 1 := by
  intro c
  induction hv : Φ c using Nat.strong_induction_on generalizing c with
  | _ v ih =>
  intro hc
  by_cases ha : c.reg a = 0
  · exact ⟨c, 1, Exec.loopDone ha, hc, ha, by omega⟩
  · obtain ⟨c₁, t₁, he₁, hi₁, hΦ₁⟩ := hbody v c ⟨hc, ha, hv⟩
    obtain ⟨c', t₂, he₂, hi', ha', hΦ'⟩ := ih (Φ c₁) (by omega) c₁ rfl hi₁
    exact ⟨c', t₁ + t₂ + 1, Exec.loopNext ha he₁ he₂, hi', ha', by omega⟩

/-- A loop with a potential bounded by `K` under the invariant. -/
theorem loop {a : ℕ} {body : Stmt} {Inv : Config → Prop} (Φ : Config → ℕ) {K : ℕ}
    (hbody : ∀ v, HTt body (fun c => Inv c ∧ c.reg a ≠ 0 ∧ Φ c = v)
      (fun c' t => Inv c' ∧ Φ c' + t + 1 ≤ v))
    (hK : ∀ c, Inv c → Φ c ≤ K) :
    HT (.loop a body) Inv (fun c => Inv c ∧ c.reg a = 0) (K + 1) := by
  intro c hc
  obtain ⟨c', t, he, hi, ha, ht⟩ := loopPot Φ hbody c hc
  exact ⟨c', t, he, ⟨hi, ha⟩, by have := hK c hc; omega⟩

/-- A body with a fixed bound `T` lowering the potential by at least `T + 1`. -/
theorem body_of_HT {body : Stmt} {Inv : Config → Prop} {a : ℕ} {Φ : Config → ℕ} {T : ℕ}
    (h : ∀ v, HT body (fun c => Inv c ∧ c.reg a ≠ 0 ∧ Φ c = v) (fun c' => Inv c' ∧ Φ c' + T + 1 ≤ v) T) :
    ∀ v, HTt body (fun c => Inv c ∧ c.reg a ≠ 0 ∧ Φ c = v) (fun c' t => Inv c' ∧ Φ c' + t + 1 ≤ v) := by
  intro v c hc
  obtain ⟨c', t, he, ⟨hi, hΦ⟩, ht⟩ := h v c hc
  exact ⟨c', t, he, hi, by omega⟩

end HT

end STACS2027.RAM
