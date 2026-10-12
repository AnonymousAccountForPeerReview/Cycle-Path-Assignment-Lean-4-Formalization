module

public import ApproximationHardness.Registered.Machine
import Lean.Elab.Tactic.Omega

/-!
# Evaluation of the models on encoded formulas

On the code `encode f` of a formula whose clauses have two or three literals,
the models of the passes are evaluated: the first pass computes
`variableBound f`, the variable loop emits the variable gadgets, and the clause
loop emits the clause gadgets with the ports of Section 5's `placeFormula`.
The result (`mainModel_encode`) is the code of the records of `formulaGraph k f`
in reverse order.
-/

@[expose] public section

namespace STACS2027.Registered

open Complexity
open Complexity.SAT
open Complexity.StackMachine (Registers set)

/-! ### The scan -/

theorem writeValues_cons {α : Type} (enc : α → SAT.Word) (x : α) (xs : List α) :
    writeValues enc (x :: xs) = enc x ++ writeValues enc xs := rfl

/-- One scan step on the code of `l` followed by the codes of `ls`. -/
theorem scanStepModel_cons (i : Nat) (r : Regs) (l : Literal) (ls : List Literal) (s : Bool) (stail : SAT.Word)
    (hscan : r R.scan = writeValues encodeLiteral (l :: ls)) (hsg : r (slotS i) = s :: stail) :
    scanStepModel i r = some (set (set r R.scan (writeValues encodeLiteral ls)) R.cE
      (if s = l.positive ∧ l.var = (r (slotV i)).length then true :: r R.cE else r R.cE)) := by
  simp [scanStepModel, hscan, writeValues_cons, hsg]

/-- The scan over the codes of `ls` counts the occurrences of the current literal. -/
theorem scan_eval (i : Nat) (ls : List Literal) : ∀ (r : Regs) (v _c : Nat) (s : Bool),
    r (slotS i) = [s] → r (slotV i) = unary v → r R.scan = writeValues encodeLiteral ls →
    r R.sc = unary ls.length →
    iter (scanStepModel i) R.sc ls.length r =
      some (set (set (set r R.scan []) R.sc []) R.cE (unary (ls.count ⟨v, s⟩) ++ r R.cE)) := by
  induction ls with
  | nil =>
    intro r v c s hsg hv hscan hsc
    simp only [List.length_nil, iter, List.count_nil, unary_zero, List.nil_append, Option.some.injEq]
    funext j
    by_cases h1 : j = R.cE
    · subst h1; simp +decide [StackMachine.set]
    · by_cases h2 : j = R.sc
      · subst h2; simp +decide [StackMachine.set, hsc]
      · by_cases h3 : j = R.scan
        · subst h3; simp +decide [StackMachine.set, hscan, writeValues]
        · simp [StackMachine.set, h1, h2, h3]
  | cons l ls ih =>
    intro r v c s hsg hv hscan hsc
    simp only [List.length_cons] at hsc
    rw [unary_succ] at hsc
    rw [List.length_cons, iter_cons _ _ _ _ true (unary ls.length) hsc]
    have hsg' : set r R.sc (unary ls.length) (slotS i) = s :: [] := by simp [StackMachine.set, hsg]
    have hscan' : set r R.sc (unary ls.length) R.scan = writeValues encodeLiteral (l :: ls) := by
      simp +decide [StackMachine.set, hscan]
    rw [scanStepModel_cons i _ l ls s [] hscan' hsg', Option.bind_some]
    have hv' : set r R.sc (unary ls.length) (slotV i) = unary v := by simp [StackMachine.set, hv]
    rw [hv', unary_length]
    rw [ih _ v c s (by simp [StackMachine.set, hsg]) (by simp [StackMachine.set, hv])
      (by simp +decide [StackMachine.set]) (by simp +decide [StackMachine.set])]
    congr 1
    funext j
    by_cases h1 : j = R.cE
    · subst h1
      simp +decide [StackMachine.set, List.count_cons]
      by_cases hl : l = ⟨v, s⟩
      · subst hl
        simp [unary, Complexity.Restricted.replicate_append_cons, List.replicate_succ]
      · have hne : ¬ (s = l.positive ∧ l.var = v) := by
          intro ⟨h1, h2⟩; apply hl; cases l; simp_all
        simp [hne, hl]
    · by_cases h2 : j = R.sc
      · subst h2; simp +decide [StackMachine.set]
      · by_cases h3 : j = R.scan
        · subst h3; simp +decide [StackMachine.set]
        · simp [StackMachine.set, h1, h2, h3]

/-- The scan loop on a state whose `done` holds the codes of `past`. -/
theorem scanLoopModel_eval (i : Nat) (r : Regs) (past : List Literal) (v : Nat) (s : Bool)
    (hsg : r (slotS i) = [s]) (hv : r (slotV i) = unary v)
    (hdone : r R.done = writeValues encodeLiteral past) (hdc : r R.dc = unary past.length) :
    scanLoopModel i r = some (set (set (set r R.cE (unary (past.count ⟨v, s⟩))) R.scan []) R.sc []) := by
  unfold scanLoopModel
  rw [hdc, unary_length]
  rw [scan_eval i past (scanStart r) v 0 s (by simp [scanStart, StackMachine.set, hsg])
    (by simp [scanStart, StackMachine.set, hv]) (by simp +decide [scanStart, StackMachine.set, hdone])
    (by simp +decide [scanStart, StackMachine.set, hdc])]
  congr 1
  funext j
  by_cases h1 : j = R.cE
  · subst h1; simp +decide [scanStart, StackMachine.set]
  · by_cases h2 : j = R.sc
    · subst h2; simp +decide [StackMachine.set]
    · by_cases h3 : j = R.scan
      · subst h3; simp +decide [StackMachine.set]
      · simp [scanStart, StackMachine.set, h1, h2, h3]

/-! ### The port endpoints -/

/-- The port endpoints computed from the sign and a positive count: the port of
Section 5's `PlacedLiteral` with `earlier = c`. -/
theorem portModel_eval (i : Nat) (r : Regs) (s : Bool) (c : Nat)
    (hsg : r (slotS i) = [s]) (hcE : r R.cE = unary (c + 1)) :
    portModel i r = some (set (set (set r R.cE (if s then unary (c + 1) else unary c))
      (slotE i false) (unary (variableEndpoint (if s then 0 else c + 1) false)))
      (slotE i true) (unary (variableEndpoint (if s then 0 else c + 1) true))) := by
  have hfs := slotE_ne_slotE_side i i
  cases s with
  | true =>
    simp only [portModel, hsg, portState, ↓reduceIte, Option.some.injEq]
    funext j
    by_cases h1 : j = slotE i true
    · subst h1; simp
    · by_cases h2 : j = slotE i false
      · subst h2; simp [StackMachine.set, hfs]
      · by_cases h3 : j = R.cE
        · subst h3; simp +decide [StackMachine.set, hcE]
        · simp [StackMachine.set, h1, h2, h3]
  | false =>
    cases c with
    | zero =>
      simp only [portModel, hsg, hcE, unary_succ, unary_zero, portState, Option.some.injEq]
      funext j
      by_cases h1 : j = slotE i true
      · subst h1; simp
      · by_cases h2 : j = slotE i false
        · subst h2; simp [StackMachine.set, hfs]
        · by_cases h3 : j = R.cE
          · subst h3; simp +decide [StackMachine.set]
          · simp [StackMachine.set, h1, h2, h3]
    | succ c =>
      have hve : ∀ b, variableEndpoint (c + 1 + 1) b = variableEndpoint 2 b := by
        intro b; simp [variableEndpoint]
      simp only [portModel, hsg, hcE, unary_succ, portState, Option.some.injEq]
      funext j
      by_cases h1 : j = slotE i true
      · subst h1; simp [hve]
      · by_cases h2 : j = slotE i false
        · subst h2; simp [StackMachine.set, hfs, hve]
        · by_cases h3 : j = R.cE
          · subst h3; simp +decide [StackMachine.set]
          · simp [StackMachine.set, h1, h2, h3]

/-! ### One literal -/

/-- The placed literal of `l` after `past` (in any order), as Section 5 places it. -/
def placed (l : Literal) (past : List Literal) : PlacedLiteral := ⟨l, past.count l⟩

/-- The state after reading the literal `l` into slot `i`, from a state with input
`encodeLiteral l ++ rest` and the codes of `past` on `done`. -/
def litState (k i : Nat) (l : Literal) (rest : SAT.Word) (past : List Literal) (r : Regs) : Regs :=
  let p := placed l past
  set (set (set (set (set (set (set (set (set (set (set r R.inB rest) (slotS i) [l.positive])
    (slotV i) (unary l.var)) R.done (encodeLiteral l ++ r R.done)) R.dc (true :: r R.dc))
    R.scan []) R.sc []) R.cE (if l.positive then unary (past.count l + 1) else unary (past.count l)))
    (slotE i false) (unary (variableEndpoint p.port false)))
    (slotE i true) (unary (variableEndpoint p.port true)))
    (slotB i) (unary (gadgetWidth k * l.var))

theorem readLitModel_eval (k i : Nat) (r : Regs) (l : Literal) (rest : SAT.Word) (past : List Literal)
    (hinB : r R.inB = encodeLiteral l ++ rest) (hdone : r R.done = writeValues encodeLiteral past)
    (hdc : r R.dc = unary past.length) :
    readLitModel k i r = some (litState k i l rest past r) := by
  have hfs := slotE_ne_slotE_side i i
  unfold readLitModel
  rw [readLitCodeModel_encode i r l rest hinB, Option.bind_some]
  have h1 := scanLoopModel_eval i (afterLit i l rest r) (l :: past) l.var l.positive
    (by simp [afterLit, StackMachine.set]) (by simp [afterLit, StackMachine.set])
    (by simp +decide [afterLit, StackMachine.set, hdone, writeValues_cons])
    (by simp +decide [afterLit, StackMachine.set, hdc, unary_succ])
  rw [h1, Option.bind_some]
  have hcount : (l :: past).count l = past.count l + 1 := by simp []
  have h2 := portModel_eval i (set (set (set (afterLit i l rest r) R.cE (unary ((l :: past).count ⟨l.var, l.positive⟩)))
    R.scan []) R.sc []) l.positive (past.count l) (by simp +decide [afterLit, StackMachine.set])
    (by simp +decide [StackMachine.set, hcount])
  rw [h2, Option.bind_some]
  simp only [Option.some.injEq, mulWModel, litState, placed, PlacedLiteral.port]
  funext j
  by_cases c1 : j = slotB i
  · subst c1; simp +decide [afterLit, StackMachine.set]
  · by_cases c2 : j = slotE i true
    · subst c2; simp +decide [StackMachine.set]; by_cases hp : l.positive = true <;> simp [hp]
    · by_cases c3 : j = slotE i false
      · subst c3; simp +decide [StackMachine.set, hfs]; by_cases hp : l.positive = true <;> simp [hp]
      · by_cases c4 : j = R.cE
        · subst c4
          simp +decide [StackMachine.set]
        · by_cases c5 : j = R.sc
          · subst c5; simp +decide [StackMachine.set]
          · by_cases c6 : j = R.scan
            · subst c6; simp +decide [StackMachine.set]
            · simp [afterLit, StackMachine.set, c1, c2, c3, c4, c5, c6]

end STACS2027.Registered
