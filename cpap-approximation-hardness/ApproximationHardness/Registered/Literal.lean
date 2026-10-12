module

public import ApproximationHardness.Registered.Macros
public import ApproximationHardness.Registered.Slots
import Lean.Elab.Tactic.Omega

/-!
# Reading one literal of the current clause

`readLit i` reads the `i`-th literal of the current clause from the input copy
`R.inB`: its sign into `slotS i`, its variable into `slotV i`; it moves the
literal's code onto `R.done`, counts the occurrences of the same literal on
`R.done` (the literal itself included) by a scan, derives the port endpoints
of the occurrence (`slotE i`) from the sign and the count, and multiplies the
variable by the gadget width (`slotB i`).
-/

@[expose] public section

namespace STACS2027.Registered

open Complexity
open Complexity.SAT
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame eqU eqU_spec)

/-! ### Invariants -/

/-- Registers that are constant throughout, or empty between macros. -/
structure Base (k : Nat) (r : Regs) : Prop where
  s : r R.s = []
  g : r R.g = []
  mc : r R.mc = []
  t1 : r R.t1 = []
  t2 : r R.t2 = []
  tmp : r R.tmp = []
  W : r R.W = unary (gadgetWidth k)
  two : r R.two = [true, true]

theorem Base.set {k : Nat} {r : Regs} (h : Base k r) (j : Reg)
    (hj : j ≠ R.s ∧ j ≠ R.g ∧ j ≠ R.mc ∧ j ≠ R.t1 ∧ j ≠ R.t2 ∧ j ≠ R.tmp ∧ j ≠ R.W ∧ j ≠ R.two)
    (w : SAT.Word) : Base k (set r j w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hj
  exact ⟨by simp [StackMachine.set, Ne.symm h1, h.s], by simp [StackMachine.set, Ne.symm h2, h.g],
    by simp [StackMachine.set, Ne.symm h3, h.mc], by simp [StackMachine.set, Ne.symm h4, h.t1],
    by simp [StackMachine.set, Ne.symm h5, h.t2], by simp [StackMachine.set, Ne.symm h6, h.tmp],
    by simp [StackMachine.set, Ne.symm h7, h.W], by simp [StackMachine.set, Ne.symm h8, h.two]⟩

/-- Size bounds holding throughout the processing of one clause, for an input of
length at most `L`. -/
structure Work (k L : Nat) (r : Regs) : Prop where
  base : Base k r
  size : (r R.done).length + (r R.inB).length ≤ L
  dc : (r R.dc).length ≤ (r R.done).length
  n : (r R.n).length ≤ L
  len : (r R.len).length ≤ L
  nj : (r R.nj).length ≤ 2 * L
  bnj : (r R.bnj).length ≤ gadgetWidth k * (2 * L)
  scan : (r R.scan).length ≤ L
  sc : (r R.sc).length ≤ L
  sv : r R.sv = []
  cE : (r R.cE).length ≤ L
  v0 : (r R.v0).length ≤ L
  v1 : (r R.v1).length ≤ L
  v2 : (r R.v2).length ≤ L
  sg0 : (r R.sg0).length ≤ 1
  sg1 : (r R.sg1).length ≤ 1
  sg2 : (r R.sg2).length ≤ 1
  b0 : (r R.b0).length ≤ gadgetWidth k * L
  b1 : (r R.b1).length ≤ gadgetWidth k * L
  b2 : (r R.b2).length ≤ gadgetWidth k * L
  ef0 : (r R.ef0).length ≤ 6
  et0 : (r R.et0).length ≤ 6
  ef1 : (r R.ef1).length ≤ 6
  et1 : (r R.et1).length ≤ 6
  ef2 : (r R.ef2).length ≤ 6
  et2 : (r R.et2).length ≤ 6

theorem Work.v {k L : Nat} {r : Regs} (h : Work k L r) (i : Nat) : (r (slotV i)).length ≤ L := by
  rcases slotV_cases i with e | e | e <;> rw [e]
  · exact h.v0
  · exact h.v1
  · exact h.v2

theorem Work.sg {k L : Nat} {r : Regs} (h : Work k L r) (i : Nat) : (r (slotS i)).length ≤ 1 := by
  rcases slotS_cases i with e | e | e <;> rw [e]
  · exact h.sg0
  · exact h.sg1
  · exact h.sg2

theorem Work.b {k L : Nat} {r : Regs} (h : Work k L r) (i : Nat) :
    (r (slotB i)).length ≤ gadgetWidth k * L := by
  rcases slotB_cases i with e | e | e <;> rw [e]
  · exact h.b0
  · exact h.b1
  · exact h.b2

theorem Work.e {k L : Nat} {r : Regs} (h : Work k L r) (i : Nat) (side : Bool) :
    (r (slotE i side)).length ≤ 6 := by
  rcases slotE_cases i side with e | e | e | e | e | e <;> rw [e]
  · exact h.ef0
  · exact h.et0
  · exact h.ef1
  · exact h.et1
  · exact h.ef2
  · exact h.et2

end STACS2027.Registered

namespace STACS2027.Registered

open Complexity
open Complexity.SAT
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame eqU eqU_spec)

/-! ### The sign and the code of the literal -/

/-- Set the sign register of slot `i` to the one bit `s`. -/
def setSign (i : Nat) (s : Bool) : Command K := .seq (.clear (slotS i)) (.push (slotS i) s)

theorem exec_setSign (i : Nat) (s : Bool) (r : Regs) :
    Exec (setSign i s) r ((r (slotS i)).length + 2 + 2) (true, set r (slotS i) [s]) := by
  have h := Exec.seq (Exec.clear (slotS i) r) (Exec.push (slotS i) s (set r (slotS i) []))
  simpa [setSign, StackMachine.set] using h

/-- After the sign: read the variable, move the code `s 1^v 0` onto `done`, count it. -/
def litRest (i : Nat) : Command K :=
  .seq (readUnary R.inB (slotV i)) (.seq (.push R.done false) (.seq (.add (slotV i) R.done R.s)
    (.seq (.branch (slotS i) (.stop false) (.push R.done false) (.push R.done true)) (.push R.dc true))))

/-- Read the sign bit, then the rest of the literal. -/
def readLitCode (i : Nat) : Command K :=
  .branch R.inB (.stop false)
    (.seq (.pop R.inB) (.seq (setSign i false) (litRest i)))
    (.seq (.pop R.inB) (.seq (setSign i true) (litRest i)))

/-- The state after reading the literal `l` from `inB = encodeLiteral l ++ rest`. -/
def afterLit (i : Nat) (l : Literal) (rest : SAT.Word) (r : Regs) : Regs :=
  set (set (set (set (set r R.inB rest) (slotS i) [l.positive]) (slotV i) (unary l.var))
    R.done (encodeLiteral l ++ r R.done)) R.dc (true :: r R.dc)

def readLitCodeModel (i : Nat) (r : Regs) : Option Regs :=
  match readLiteral (r R.inB) with
  | some (l, rest) => some (afterLit i l rest r)
  | none => none

theorem readLitCodeModel_encode (i : Nat) (r : Regs) (l : Literal) (rest : SAT.Word)
    (h : r R.inB = encodeLiteral l ++ rest) : readLitCodeModel i r = some (afterLit i l rest r) := by
  simp [readLitCodeModel, h]

def readLitCodeCost (L : Nat) : Nat := 14 * L + 40


/-- `litRest` from a state whose sign register holds `[s]` and whose input is `tail`. -/
theorem exec_litRest (i : Nat) (s : Bool) {L : Nat} (r : Regs) (hs : r R.s = []) (hg : r R.g = [])
    (hsg : r (slotS i) = [s]) (hL : (r R.inB).length ≤ L) (hv : (r (slotV i)).length ≤ L) :
    ∃ t res, Exec (litRest i) r t res ∧ t ≤ 14 * L + 25 ∧
      Realizes (match readNat (r R.inB) with
        | some (v, rest) => some (set (set (set (set r R.inB rest) (slotV i) (unary v)) R.done
            (s :: (unary v ++ false :: r R.done))) R.dc (true :: r R.dc))
        | none => none) res := by
  have hV := slotV_ne_inB i
  have hVS := slotV_ne_slotS i i
  have hVd := slotV_ne_done i
  have hVs := slotV_ne_s i
  have hVg := slotV_ne_g i
  have hVdc := slotV_ne_dc i
  have hSd := slotS_ne_done i
  have hSs := slotS_ne_s i
  have hSdc := slotS_ne_dc i
  have hSi := slotS_ne_inB i
  obtain ⟨t₁, res₁, he₁, ht₁, hres₁⟩ := Spec.readUnary R.inB (slotV i) hV.symm (by decide) hVg
    (P := fun r' => r' = r) (L := L) (fun _ h => h ▸ hg) (fun _ h => h ▸ ⟨hL, hv⟩) r rfl
  cases hn : readNat (r R.inB) with
  | none =>
    simp only [readUnaryModel, hn, Realizes] at hres₁
    obtain ⟨b, r₁⟩ := res₁
    simp only at hres₁
    subst hres₁
    exact ⟨t₁, (false, r₁), Exec.seqFailure he₁, by omega, by simp [Realizes]⟩
  | some p =>
    obtain ⟨v, rest⟩ := p
    simp only [readUnaryModel, hn, Realizes] at hres₁
    subst hres₁
    have hvL : v + 1 + rest.length = (r R.inB).length := by
      have := congrArg List.length (readNat_eq_some hn)
      simp only [List.length_append, SATBounds.writeNat_length] at this
      omega
    let r₁ := set (set r R.inB rest) (slotV i) (unary v)
    let r₂ := set r₁ R.done (false :: r₁ R.done)
    have he₂ : Exec (.push R.done false) r₁ 2 (true, r₂) := Exec.push R.done false r₁
    have hs₂ : r₂ R.s = [] := by simp +decide [r₂, r₁, StackMachine.set, hs, hVs.symm]
    let r₃ := set r₂ R.done (List.replicate (r₂ (slotV i)).length true ++ r₂ R.done)
    have he₃ : Exec (.add (slotV i) R.done R.s) r₂ (5 * (r₂ (slotV i)).length + 4) (true, r₃) :=
      Exec.add hVd hVs (by decide) hs₂
    have hv₂ : r₂ (slotV i) = unary v := by simp +decide [r₂, r₁, StackMachine.set, hVd, hVd.symm]
    have hsg₃ : r₃ (slotS i) = [s] := by
      simp +decide [r₃, r₂, r₁, StackMachine.set, hSd, hVS.symm, hSi, hsg]
    let r₄ := set r₃ R.done (s :: r₃ R.done)
    have he₄ : Exec (.branch (slotS i) (.stop false) (.push R.done false) (.push R.done true)) r₃ 3
        (true, r₄) := by
      cases s with
      | false => exact Exec.branchZero hsg₃ (Exec.push R.done false r₃)
      | true => exact Exec.branchOne hsg₃ (Exec.push R.done true r₃)
    let r₅ := set r₄ R.dc (true :: r₄ R.dc)
    have he₅ : Exec (.push R.dc true) r₄ 2 (true, r₅) := Exec.push R.dc true r₄
    refine ⟨t₁ + (2 + ((5 * (r₂ (slotV i)).length + 4) + (3 + 2))), (true, r₅),
      Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅))), ?_, ?_⟩
    · rw [hv₂, unary_length]
      omega
    · simp only [Realizes, Prod.mk.injEq, true_and]
      funext j
      by_cases hj : j = R.dc
      · subst hj; simp +decide [r₅, r₄, r₃, r₂, r₁, StackMachine.set, hVdc.symm]
      · by_cases hj' : j = R.done
        · subst hj'
          simp +decide [r₅, r₄, r₃, r₂, r₁, StackMachine.set, hVd, hVd.symm, unary]
        · simp [r₅, r₄, r₃, r₂, r₁, StackMachine.set, hj, hj']

theorem Spec.readLitCode (i : Nat) {P : Regs → Prop} {L : Nat}
    (hs : ∀ r, P r → r R.s = []) (hg : ∀ r, P r → r R.g = [])
    (hL : ∀ r, P r → (r R.inB).length ≤ L) (hv : ∀ r, P r → (r (slotV i)).length ≤ L)
    (hsg : ∀ r, P r → (r (slotS i)).length ≤ 1) :
    Spec (readLitCode i) P (readLitCodeCost L) (readLitCodeModel i) := by
  intro r hr
  have hSi := slotS_ne_inB i
  have hSs := slotS_ne_s i
  have hSg := slotS_ne_g i
  have hVS := slotV_ne_slotS i i
  cases hin : r R.inB with
  | nil =>
    refine ⟨2, (false, r), Exec.branchEmpty hin (Exec.stop false r), by simp [readLitCodeCost], ?_⟩
    simp [readLitCodeModel, hin, readLiteral, Realizes]
  | cons s tail =>
    let r₁ := set r R.inB tail
    have he₁ : Exec (.pop R.inB) r 2 (true, r₁) := by
      have := Exec.pop R.inB r
      rwa [hin] at this
    let r₂ := set r₁ (slotS i) [s]
    have he₂ : Exec (setSign i s) r₁ ((r₁ (slotS i)).length + 2 + 2) (true, r₂) := exec_setSign i s r₁
    have hsg₁ : (r₁ (slotS i)).length ≤ 1 := by simpa [r₁, StackMachine.set, hSi] using hsg r hr
    have hL₂ : (r₂ R.inB).length ≤ L := by
      have := hL r hr
      rw [hin] at this
      simp only [List.length_cons] at this
      simp [r₂, r₁, StackMachine.set, hSi.symm]
      omega
    obtain ⟨t₃, res₃, he₃, ht₃, hres₃⟩ := exec_litRest i s (L := L) r₂
      (by simp +decide [r₂, r₁, StackMachine.set, hSs.symm, hs r hr])
      (by simp +decide [r₂, r₁, StackMachine.set, hSg.symm, hg r hr])
      (by simp [r₂]) hL₂
      (by simpa [r₂, r₁, StackMachine.set, hVS, hVS.symm, slotV_ne_inB i, (slotV_ne_inB i).symm] using hv r hr)
    have hin₂ : r₂ R.inB = tail := by simp [r₂, r₁, StackMachine.set, hSi.symm]
    rw [hin₂] at hres₃
    have hbranch : ∀ res, Exec (.seq (.pop R.inB) (.seq (setSign i s) (litRest i))) r (2 + ((r₁ (slotS i)).length + 2 + 2 + t₃)) res →
        Exec (Registered.readLitCode i) r (2 + ((r₁ (slotS i)).length + 2 + 2 + t₃) + 1) res := by
      intro res h
      cases s with
      | false => exact Exec.branchZero hin h
      | true => exact Exec.branchOne hin h
    cases hn : readNat tail with
    | none =>
      rw [hn] at hres₃
      simp only [Realizes] at hres₃
      obtain ⟨b, r₃⟩ := res₃
      simp only at hres₃
      subst hres₃
      refine ⟨_, (false, r₃), hbranch _ (Exec.seq he₁ (Exec.seq he₂ he₃)), ?_, ?_⟩
      · simp only [readLitCodeCost]; omega
      · simp [readLitCodeModel, hin, readLiteral, hn, Realizes]
    | some p =>
      obtain ⟨v, rest⟩ := p
      rw [hn] at hres₃
      simp only [Realizes] at hres₃
      subst hres₃
      refine ⟨_, _, hbranch _ (Exec.seq he₁ (Exec.seq he₂ he₃)), ?_, ?_⟩
      · simp only [readLitCodeCost]; omega
      · simp only [readLitCodeModel, hin, readLiteral, hn, Option.pure_def,
          Realizes, Prod.mk.injEq, true_and, afterLit]
        funext j
        by_cases hj : j = R.dc
        · subst hj
          simp +decide [r₂, r₁, StackMachine.set, 
            (slotS_ne_dc i).symm]
        · by_cases hj' : j = R.done
          · subst hj'
            simp +decide [r₂, r₁, StackMachine.set, 
              (slotS_ne_done i).symm, encodeLiteral, unary,
              Complexity.StackParse.writeNat_eq]
          · by_cases hj'' : j = slotV i
            · subst hj''; simp [StackMachine.set, hj, hj']
            · by_cases hj''' : j = slotS i
              · subst hj'''; simp [r₂, StackMachine.set, hVS.symm, hj, hj', hSi]
              · by_cases hj4 : j = R.inB
                · subst hj4
                  simp [StackMachine.set, hSi.symm, (slotV_ne_inB i).symm, hj, hj']
                · simp [r₂, r₁, StackMachine.set, hj, hj', hj'', hj''', hj4]

/-! ### Counting the earlier occurrences -/

/-- Compare the scanned variable with the current one; count a match. -/
def cmp (i : Nat) : Command K :=
  .ifThenElse (eqU R.sv (slotV i) R.t1 R.t2 R.s) (.push R.cE true) (.stop true)

/-- Compare when `b`, otherwise do nothing. -/
def cmpIf (i : Nat) (b : Bool) : Command K := if b then cmp i else .stop true

/-- Compare exactly when the current literal's sign is `s'`. -/
def sgTest (i : Nat) (s' : Bool) : Command K :=
  .branch (slotS i) (.stop false) (cmpIf i (!s')) (cmpIf i s')

/-- The step after the sign bit `s'` of the scanned literal was popped. -/
def scanTail (i : Nat) (s' : Bool) : Command K :=
  .seq (.pop R.scan) (.seq (readUnary R.scan R.sv) (.seq (sgTest i s') (.clear R.sv)))

/-- One step of the scan: pop one literal code from `scan`; if its sign is that of the
current literal, compare the variables. -/
def scanStep (i : Nat) : Command K :=
  .branch R.scan (.stop false) (scanTail i false) (scanTail i true)

def scanStepModel (i : Nat) (r : Regs) : Option Regs :=
  match readLiteral (r R.scan) with
  | none => none
  | some (l, rest) =>
    match r (slotS i) with
    | [] => none
    | s :: _ => some (set (set r R.scan rest) R.cE
        (if s = l.positive ∧ l.var = (r (slotV i)).length then true :: r R.cE else r R.cE))

def scanStepCost (L : Nat) : Nat := 30 * L + 50

theorem scanStep_writes (i : Nat) (j : Reg) (hj : j ≠ R.scan ∧ j ≠ R.sv ∧ j ≠ R.cE ∧ j ≠ R.g ∧
    j ≠ R.t1 ∧ j ≠ R.t2) : writes (scanStep i) j = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hj
  have hc : writes (cmp i) j = false := by
    simp [cmp, writes, eqU, Complexity.Restricted.drainBody, h3, h5, h6]
  have hci : ∀ b, writes (cmpIf i b) j = false := by
    intro b; cases b <;> simp [cmpIf, writes, hc]
  simp [scanStep, scanTail, sgTest, writes, readUnary, Complexity.Restricted.readUnaryC,
    Complexity.Restricted.readUnaryBody, h1, h2, h4, hci]


/-- The comparison as a total test: decision `|sv| = |v_i|`, state unchanged. -/
theorem exec_eqU_sv (i : Nat) (r : Regs) (hs : r R.s = []) (h1 : r R.t1 = []) (h2 : r R.t2 = []) :
    ∃ t, Exec (eqU R.sv (slotV i) R.t1 R.t2 R.s) r t
      (decide ((r R.sv).length = (r (slotV i)).length), r) ∧
      t ≤ 10 * ((r R.sv).length + (r (slotV i)).length) + 30 := by
  obtain ⟨t, r', he, ht, hr'⟩ := eqU_spec R.sv (slotV i) R.t1 R.t2 R.s (by decide) (by decide)
    (by decide) (slotV_ne_t1 i) (slotV_ne_t2 i) (slotV_ne_s i) (by decide) (by decide)
    (by decide) r h1 h2 hs
  subst hr'
  exact ⟨t, he, ht⟩

theorem exec_cmpIf (i : Nat) (b : Bool) (r : Regs) (hs : r R.s = []) (h1 : r R.t1 = [])
    (h2 : r R.t2 = []) :
    ∃ t, Exec (cmpIf i b) r t (true, if b ∧ (r R.sv).length = (r (slotV i)).length then
        set r R.cE (true :: r R.cE) else r) ∧
      t ≤ 10 * ((r R.sv).length + (r (slotV i)).length) + 33 := by
  cases b with
  | false => exact ⟨1, Exec.stop true r, by omega⟩
  | true =>
    obtain ⟨t, he, ht⟩ := exec_eqU_sv i r hs h1 h2
    by_cases heq : (r R.sv).length = (r (slotV i)).length
    · have hd : decide ((r R.sv).length = (r (slotV i)).length) = true := by simp [heq]
      rw [hd] at he
      refine ⟨t + 2, ?_, by omega⟩
      simp only [cmpIf, heq, true_and, ↓reduceIte]
      exact Exec.ifTrue he (Exec.push R.cE true r)
    · have hd : decide ((r R.sv).length = (r (slotV i)).length) = false := by simp [heq]
      rw [hd] at he
      refine ⟨t + 1, ?_, by omega⟩
      simp only [cmpIf, heq, ↓reduceIte]
      exact Exec.ifFalse he (Exec.stop true r)

/-- `scanTail` from a state whose `scan` register starts with `s'`. -/
theorem exec_scanTail (i : Nat) (s' : Bool) {L : Nat} (r : Regs) (tail : SAT.Word)
    (hsc : r R.scan = s' :: tail) (hs : r R.s = []) (hg : r R.g = []) (h1 : r R.t1 = [])
    (h2 : r R.t2 = []) (hsv : r R.sv = []) (hL : (r R.scan).length ≤ L)
    (hv : (r (slotV i)).length ≤ L) :
    ∃ t res, Exec (scanTail i s') r t res ∧ t ≤ scanStepCost L - 1 ∧
      Realizes (match readNat tail with
        | none => none
        | some (u, rest) =>
          match r (slotS i) with
          | [] => none
          | s :: _ => some (set (set r R.scan rest) R.cE
              (if s = s' ∧ u = (r (slotV i)).length then true :: r R.cE else r R.cE))) res := by
  have hSs := slotS_ne_scan i
  have hSv := slotS_ne_sv i
  have hScE := slotS_ne_cE i
  have hVs := slotV_ne_scan i
  have hVsv := slotV_ne_sv i
  have hVcE := slotV_ne_cE i
  have hVt1 := slotV_ne_t1 i
  have hVt2 := slotV_ne_t2 i
  have hVS := slotV_ne_slotS i i
  let r₁ := set r R.scan tail
  have he₁ : Exec (.pop R.scan) r 2 (true, r₁) := by
    have := Exec.pop R.scan r
    rwa [hsc] at this
  have htail : tail.length + 1 ≤ L := by rw [hsc] at hL; simpa using hL
  obtain ⟨t₂, res₂, he₂, ht₂, hres₂⟩ := Spec.readUnary R.scan R.sv (by decide) (by decide) (by decide)
    (P := fun r' => r' = r₁) (L := L) (fun _ h => h ▸ by simp +decide [r₁, hg])
    (fun _ h => h ▸ by simp +decide [r₁, hsv]; omega) r₁ rfl
  have hsc₁ : r₁ R.scan = tail := by simp [r₁]
  simp only [readUnaryModel, hsc₁] at hres₂
  cases hn : readNat tail with
  | none =>
    simp only [hn, Realizes] at hres₂
    obtain ⟨b, r₂⟩ := res₂
    simp only at hres₂
    subst hres₂
    refine ⟨2 + t₂, (false, r₂), Exec.seq he₁ (Exec.seqFailure he₂), ?_, by simp [Realizes]⟩
    simp only [scanStepCost]; omega
  | some p =>
    obtain ⟨u, rest⟩ := p
    simp only [hn, Realizes] at hres₂
    subst hres₂
    have hu : u + 1 + rest.length = tail.length := by
      have := congrArg List.length (readNat_eq_some hn)
      simp only [List.length_append, SATBounds.writeNat_length] at this
      omega
    let r₂ := set (set r₁ R.scan rest) R.sv (unary u)
    have hsg₂ : r₂ (slotS i) = r (slotS i) := by
      simp [r₂, r₁, StackMachine.set, hSv, hSs]
    have hs₂ : r₂ R.s = [] := by simp +decide [r₂, r₁, StackMachine.set, hs]
    have h1₂ : r₂ R.t1 = [] := by simp +decide [r₂, r₁, StackMachine.set, h1]
    have h2₂ : r₂ R.t2 = [] := by simp +decide [r₂, r₁, StackMachine.set, h2]
    have hsv₂ : r₂ R.sv = unary u := by simp [r₂]
    have hv₂ : r₂ (slotV i) = r (slotV i) := by
      simp [r₂, r₁, StackMachine.set, hVsv, hVs]
    cases hsg : r (slotS i) with
    | nil =>
      have hsg₂' : r₂ (slotS i) = [] := hsg₂.trans hsg
      refine ⟨2 + (t₂ + 2), (false, r₂),
        Exec.seq he₁ (Exec.seq he₂ (Exec.seqFailure (Exec.branchEmpty hsg₂' (Exec.stop false r₂)))),
        ?_, by simp [Realizes]⟩
      simp only [scanStepCost]; omega
    | cons s stail =>
      have hsg₂' : r₂ (slotS i) = s :: stail := hsg₂.trans hsg
      obtain ⟨t₃, he₃, ht₃⟩ := exec_cmpIf i (s == s') r₂ hs₂ h1₂ h2₂
      rw [hsv₂, hv₂, unary_length] at he₃ ht₃
      let r₃ := if (s == s') = true ∧ u = (r (slotV i)).length then set r₂ R.cE (true :: r₂ R.cE) else r₂
      have he₃' : Exec (sgTest i s') r₂ (t₃ + 1) (true, r₃) := by
        cases s with
        | false =>
          apply Exec.branchZero hsg₂'
          simpa [r₃] using he₃
        | true =>
          apply Exec.branchOne hsg₂'
          simpa [r₃] using he₃
      have hsv₃ : (r₃ R.sv).length = u := by
        simp only [r₃]
        split <;> simp +decide [StackMachine.set, hsv₂, unary_length]
      refine ⟨2 + (t₂ + ((t₃ + 1) + ((r₃ R.sv).length + 2))), (true, set r₃ R.sv []),
        Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' (Exec.clear R.sv r₃))), ?_, ?_⟩
      · rw [hsv₃]
        simp only [scanStepCost]; omega
      · simp only [Realizes, Prod.mk.injEq, true_and]
        funext j
        simp only [r₃, r₂, r₁]
        by_cases hc : s = s' ∧ u = (r (slotV i)).length
        · simp only [hc, and_self, ↓reduceIte, beq_iff_eq]
          by_cases hj : j = R.sv
          · subst hj; simp +decide [StackMachine.set, hsv]
          · by_cases hj' : j = R.cE
            · subst hj'; simp +decide [StackMachine.set]
            · by_cases hj'' : j = R.scan
              · subst hj''; simp +decide [StackMachine.set]
              · simp [StackMachine.set, hj, hj', hj'']
        · have hc' : ¬ ((s == s') = true ∧ u = (r (slotV i)).length) := by simpa using hc
          simp only [hc, hc', ↓reduceIte]
          by_cases hj : j = R.sv
          · subst hj; simp +decide [StackMachine.set, hsv]
          · by_cases hj' : j = R.cE
            · subst hj'; simp +decide [StackMachine.set]
            · by_cases hj'' : j = R.scan
              · subst hj''; simp +decide [StackMachine.set]
              · simp [StackMachine.set, hj, hj', hj'']

theorem Spec.scanStep (i : Nat) {P : Regs → Prop} {L : Nat}
    (hs : ∀ r, P r → r R.s = []) (hg : ∀ r, P r → r R.g = [])
    (h1 : ∀ r, P r → r R.t1 = []) (h2 : ∀ r, P r → r R.t2 = []) (hsv : ∀ r, P r → r R.sv = [])
    (hL : ∀ r, P r → (r R.scan).length ≤ L ∧ (r (slotV i)).length ≤ L) :
    Spec (Registered.scanStep i) P (scanStepCost L) (scanStepModel i) := by
  intro r hr
  cases hsc : r R.scan with
  | nil =>
    refine ⟨2, (false, r), Exec.branchEmpty hsc (Exec.stop false r), by simp [scanStepCost], ?_⟩
    simp [scanStepModel, hsc, readLiteral, Realizes]
  | cons s' tail =>
    obtain ⟨t, res, he, ht, hres⟩ := exec_scanTail i s' (L := L) r tail hsc (hs r hr) (hg r hr)
      (h1 r hr) (h2 r hr) (hsv r hr) (hL r hr).1 (hL r hr).2
    refine ⟨t + 1, res, ?_, by simp only [scanStepCost] at ht ⊢; omega, ?_⟩
    · cases s' with
      | false => exact Exec.branchZero hsc he
      | true => exact Exec.branchOne hsc he
    · simp only [scanStepModel, hsc, readLiteral]
      cases hn : readNat tail with
      | none => simp only [hn] at hres; simpa using hres
      | some p =>
        obtain ⟨u, rest⟩ := p
        simp only [hn] at hres
        simpa using hres

/-! ### Preservation of `Work` -/

theorem Base.of_eq {k : Nat} {r r' : Regs} (h : Base k r) (hs : r' R.s = r R.s) (hg : r' R.g = r R.g)
    (hmc : r' R.mc = r R.mc) (h1 : r' R.t1 = r R.t1) (h2 : r' R.t2 = r R.t2) (htmp : r' R.tmp = r R.tmp)
    (hW : r' R.W = r R.W) (htwo : r' R.two = r R.two) : Base k r' :=
  ⟨hs.trans h.s, hg.trans h.g, hmc.trans h.mc, h1.trans h.t1, h2.trans h.t2, htmp.trans h.tmp,
    hW.trans h.W, htwo.trans h.two⟩

/-- The three slots. -/
theorem slot_cases {i : Nat} (hi : i < 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega

def scanStart (r : Regs) : Regs := set (set (set r R.cE []) R.scan (r R.done)) R.sc (r R.dc)

/-- Prove every field of `Work` for a state given as a `set` chain. -/
macro "work_fields" : tactic => `(tactic|
  (refine ⟨Base.of_eq ‹Base _ _› ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
   all_goals simp +decide [afterLit, scanStart, StackMachine.set, unary_length, List.length_append,
     List.length_cons, SATBounds.encodeLiteral_length]
   all_goals try omega
   all_goals try (split <;> (try simp only [List.length_cons]) <;> omega)))

theorem Work.readLitCode {k L : Nat} {i : Nat} (hi : i < 3) {r r' : Regs} (h : Work k L r)
    (hm : readLitCodeModel i r = some r') : Work k L r' := by
  unfold readLitCodeModel at hm
  cases hl : readLiteral (r R.inB) with
  | none => rw [hl] at hm; simp at hm
  | some p =>
    obtain ⟨l, rest⟩ := p
    rw [hl] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    have hlen := congrArg List.length (readLiteral_eq_some hl)
    simp only [List.length_append, SATBounds.encodeLiteral_length] at hlen
    obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25⟩ := h
    rcases slot_cases hi with rfl | rfl | rfl <;> work_fields

/-- The scan loop: clear the count, copy `done` and `dc`, run `scanStep` `|dc|` times. -/
def scanLoop (i : Nat) : Command K :=
  .seq (.clear R.cE) (.seq (.copy R.done R.scan R.s) (.seq (.copy R.dc R.sc R.s)
    (.repeat R.sc (scanStep i))))

def scanLoopModel (i : Nat) (r : Regs) : Option Regs :=
  iter (scanStepModel i) R.sc (r R.dc).length (scanStart r)

def scanLoopCost (L : Nat) : Nat := 14 * L + 16 + (L * (scanStepCost L + 1) + 2)

/-- The scan loop's invariant: the count and the remaining counter fit in `L`. -/
def ScanInv (k L : Nat) (r : Regs) : Prop := Work k L r ∧ (r R.cE).length + (r R.sc).length ≤ L

theorem Work.scanStep {k L : Nat} {i : Nat} {r r' : Regs} (b : Bool) (tail : SAT.Word)
    (h : ScanInv k L r) (hsc : r R.sc = b :: tail)
    (hm : scanStepModel i (set r R.sc tail) = some r') : ScanInv k L r' := by
  obtain ⟨h, hce⟩ := h
  unfold scanStepModel at hm
  have hsc' : set r R.sc tail R.scan = r R.scan := by simp +decide [StackMachine.set]
  rw [hsc'] at hm
  cases hl : readLiteral (r R.scan) with
  | none => rw [hl] at hm; simp at hm
  | some p =>
    obtain ⟨l, rest⟩ := p
    rw [hl] at hm
    have hsg' : set r R.sc tail (slotS i) = r (slotS i) := by simp [StackMachine.set]
    rw [hsg'] at hm
    cases hsg : r (slotS i) with
    | nil => rw [hsg] at hm; simp at hm
    | cons sg stail =>
      rw [hsg] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      have hlen := congrArg List.length (readLiteral_eq_some hl)
      simp only [List.length_append, SATBounds.encodeLiteral_length] at hlen
      rw [hsc] at hce
      simp only [List.length_cons] at hce
      obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
        h20, h21, h22, h23, h24, h25⟩ := h
      refine ⟨?_, ?_⟩
      · work_fields
      · simp +decide [StackMachine.set]
        split
        · simp only [List.length_cons]; omega
        · omega

theorem ScanInv.start {k L : Nat} {r : Regs} (h : Work k L r) : ScanInv k L (scanStart r) := by
  obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  refine ⟨?_, ?_⟩
  · work_fields
  · simp +decide [scanStart, StackMachine.set]; omega

theorem Work.scanLoop {k L : Nat} {i : Nat} {r r' : Regs} (h : Work k L r)
    (hm : scanLoopModel i r = some r') : Work k L r' :=
  (iter_invariant (j := R.sc) (P := ScanInv k L) (m := scanStepModel i)
    (fun _ b tail _ hr hsc hm => Work.scanStep b tail hr hsc hm) _ _ _ (ScanInv.start h) hm).1

theorem Spec.scanLoop (k : Nat) (i : Nat) {L : Nat} :
    Spec (Registered.scanLoop i) (Work k L) (scanLoopCost L) (scanLoopModel i) := by
  have s1 := Spec.clear R.cE (P := Work k L) (L := L) (fun r hr => hr.cE)
  have s2 := Spec.copy (src := R.done) (dst := R.scan) (scratch := R.s) (by decide) (by decide) (by decide)
    (P := fun r' => ∃ r, Work k L r ∧ r' = set r R.cE []) (a := L) (b := L)
    (by rintro r' ⟨r, hr, rfl⟩; simp +decide [StackMachine.set, hr.base.s])
    (by rintro r' ⟨r, hr, rfl⟩; have := hr.size; have := hr.scan; simp +decide [StackMachine.set]; omega)
  have s3 := Spec.copy (src := R.dc) (dst := R.sc) (scratch := R.s) (by decide) (by decide) (by decide)
    (P := fun r' => ∃ r, Work k L r ∧ r' = set (set r R.cE []) R.scan (r R.done)) (a := L) (b := L)
    (by rintro r' ⟨r, hr, rfl⟩; simp +decide [StackMachine.set, hr.base.s])
    (by rintro r' ⟨r, hr, rfl⟩; have := hr.size; have := hr.dc; have := hr.sc
        simp +decide [StackMachine.set]; omega)
  have s4 := Spec.repeat (j := R.sc) (body := Registered.scanStep i) (P := ScanInv k L)
    (Pb := fun r => Work k L r ∧ (r R.cE).length + (r R.sc).length + 1 ≤ L) (L := L)
    (scanStep_writes i R.sc (by decide))
    (by
      rintro r b tail ⟨hr, hce⟩ hsc
      rw [hsc] at hce
      simp only [List.length_cons] at hce
      obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
        h20, h21, h22, h23, h24, h25⟩ := hr
      refine ⟨?_, ?_⟩
      · work_fields
      · simp +decide [StackMachine.set]; omega)
    (fun _ b tail _ hr hsc hm => Work.scanStep b tail hr hsc hm)
    (fun _ hr => hr.1.sc)
    (Spec.scanStep i (P := fun r => Work k L r ∧ (r R.cE).length + (r R.sc).length + 1 ≤ L) (L := L)
      (fun _ hr => hr.1.base.s) (fun _ hr => hr.1.base.g) (fun _ hr => hr.1.base.t1)
      (fun _ hr => hr.1.base.t2) (fun _ hr => hr.1.sv) (fun _ hr => ⟨hr.1.scan, hr.1.v i⟩))
  have h := s1.seq (fun r r' hr hm => ⟨r, hr, by simpa using hm.symm⟩)
    (s2.seq (fun r' r'' hr' hm => by
      obtain ⟨r, hr, rfl⟩ := hr'
      refine ⟨r, hr, ?_⟩
      simp only [Option.some.injEq] at hm
      rw [← hm]
      simp +decide [StackMachine.set])
      (s3.seq (P₂ := ScanInv k L) (fun r' r'' hr' hm => by
        obtain ⟨r, hr, rfl⟩ := hr'
        simp only [Option.some.injEq] at hm
        subst hm
        have := ScanInv.start hr
        simpa +decide [scanStart, StackMachine.set] using this) s4))
  refine (h.mono (fun r hr => hr) ?_).congr ?_
  · simp only [scanLoopCost]; omega
  · intro r hr
    simp only [Option.bind_some, scanLoopModel, scanStart]
    simp +decide [StackMachine.set]

theorem scanLoop_writes (i : Nat) (j : Reg) (hj : j ≠ R.scan ∧ j ≠ R.sv ∧ j ≠ R.cE ∧ j ≠ R.g ∧
    j ≠ R.t1 ∧ j ≠ R.t2 ∧ j ≠ R.sc) : writes (scanLoop i) j = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hj
  simp [scanLoop, writes, h1, h3, h7, scanStep_writes i j ⟨h1, h2, h3, h4, h5, h6⟩]

/-! ### The port endpoints of the occurrence -/

/-- From the sign `s` and the count `c ≥ 1` of occurrences of the literal (itself included):
the port is `0` for a positive literal and `c` for a negative one; its endpoints
`variableEndpoint port false`, `variableEndpoint port true` go to `slotE i false`, `slotE i true`. -/
def portEndpoints (i : Nat) : Command K :=
  .seq (.clear (slotE i false)) (.seq (.clear (slotE i true))
    (.branch (slotS i) (.stop false)
      (.branch R.cE (.stop false) (.stop false)
        (.seq (.pop R.cE) (.branch R.cE
          (.seq (pushN (slotE i false) 4) (pushN (slotE i true) 5))
          (.stop false)
          (.seq (pushN (slotE i false) 0) (pushN (slotE i true) 3)))))
      (.seq (pushN (slotE i false) 2) (pushN (slotE i true) 6))))

/-- The endpoints written for sign `s` and count `c`. -/
def portState (i : Nat) (s : Bool) (c : Nat) (r : Regs) : Regs :=
  let port := if s then 0 else c
  set (set r (slotE i false) (unary (variableEndpoint port false)))
    (slotE i true) (unary (variableEndpoint port true))

def portModel (i : Nat) (r : Regs) : Option Regs :=
  match r (slotS i) with
  | [] => none
  | true :: _ => some (portState i true 0 r)
  | false :: _ =>
    match r R.cE with
    | [] => none
    | false :: _ => none
    | true :: tail =>
      match tail with
      | [] => some (portState i false 1 (set r R.cE []))
      | false :: _ => none
      | true :: _ => some (portState i false 2 (set r R.cE tail))

def portCost : Nat := 60

theorem portEndpoints_writes (i : Nat) (j : Reg) (hj : j ≠ R.cE ∧ j ≠ slotE i false ∧ j ≠ slotE i true) :
    writes (portEndpoints i) j = false := by
  obtain ⟨h1, h2, h3⟩ := hj
  simp [portEndpoints, writes, h1, h2, h3, pushN_writes _ _ _ h2, pushN_writes _ _ _ h3]

theorem Spec.portEndpoints (i : Nat) {P : Regs → Prop}
    (he : ∀ r, P r → (r (slotE i false)).length ≤ 6 ∧ (r (slotE i true)).length ≤ 6) :
    Spec (Registered.portEndpoints i) P portCost (portModel i) := by
  intro r hr
  obtain ⟨hef, het⟩ := he r hr
  have hfs := slotE_ne_slotE_side i i
  -- the two clears
  let r₀ := set r (slotE i false) []
  have hc₀ : Exec (.clear (slotE i false)) r ((r (slotE i false)).length + 2) (true, r₀) := Exec.clear _ r
  let r₁ := set r₀ (slotE i true) []
  have hc₁ : Exec (.clear (slotE i true)) r₀ ((r₀ (slotE i true)).length + 2) (true, r₁) := Exec.clear _ r₀
  have hl₀ : (r₀ (slotE i true)).length = (r (slotE i true)).length := by simp [r₀]
  rw [hl₀] at hc₁
  have hsg₁ : r₁ (slotS i) = r (slotS i) := by simp [r₁, r₀, StackMachine.set]
  have hce₁ : r₁ R.cE = r R.cE := by simp [r₁, r₀, StackMachine.set]
  have hf₁ : r₁ (slotE i false) = [] := by simp [r₁, r₀, StackMachine.set, hfs]
  have ht₁ : r₁ (slotE i true) = [] := by simp [r₁]
  -- the state written by two pushes
  have hpush : ∀ (a b : Nat) (q : Regs), ∃ t, t ≤ 2 * a + 2 * b + 2 ∧
      Exec (.seq (Registered.pushN (slotE i false) a) (Registered.pushN (slotE i true) b)) q t
        (true, set (set q (slotE i false) (unary a ++ q (slotE i false))) (slotE i true)
          (unary b ++ set q (slotE i false) (unary a ++ q (slotE i false)) (slotE i true))) := by
    intro a b q
    obtain ⟨t₁, res₁, e₁, ht₁, hr₁⟩ := Spec.pushN (slotE i false) a (fun q' => q' = q) q rfl
    simp only [Realizes] at hr₁
    subst hr₁
    obtain ⟨t₂, res₂, e₂, ht₂, hr₂⟩ := Spec.pushN (slotE i true) b (fun _ => True) _ trivial
    simp only [Realizes] at hr₂
    subst hr₂
    exact ⟨t₁ + t₂, by omega, Exec.seq e₁ e₂⟩
  -- the final states
  have hfinal : ∀ (a b : Nat) (q : Regs) (s : Bool) (c : Nat), q (slotE i false) = [] →
      q (slotE i true) = [] → unary a = unary (variableEndpoint (if s then 0 else c) false) →
      unary b = unary (variableEndpoint (if s then 0 else c) true) →
      set (set q (slotE i false) (unary a ++ q (slotE i false))) (slotE i true)
        (unary b ++ set q (slotE i false) (unary a ++ q (slotE i false)) (slotE i true)) =
      portState i s c q := by
    intro a b q s c hqf hqt ha hb
    simp only [portState, hqf, hqt, StackMachine.set, List.append_nil, ha, hb]
    funext j
    by_cases hj : j = slotE i true
    · subst hj; simp [hfs.symm]
    · simp [hj]
  cases hsg : r (slotS i) with
  | nil =>
    refine ⟨_, (false, r₁), Exec.seq hc₀ (Exec.seq hc₁ (Exec.branchEmpty (hsg₁.trans hsg) (Exec.stop false r₁))),
      ?_, by simp [portModel, hsg, Realizes]⟩
    simp only [portCost]; omega
  | cons sg stail =>
    cases sg with
    | true =>
      obtain ⟨t, ht, he⟩ := hpush 2 6 r₁
      refine ⟨_, _, Exec.seq hc₀ (Exec.seq hc₁ (Exec.branchOne (hsg₁.trans hsg) he)), ?_, ?_⟩
      · simp only [portCost]; omega
      · simp only [portModel, hsg, Realizes, Prod.mk.injEq, true_and]
        rw [hfinal 2 6 r₁ true 0 hf₁ ht₁ (by simp [variableEndpoint]) (by simp [variableEndpoint])]
        simp only [portState, r₁, r₀]
        funext j
        by_cases hj : j = slotE i true
        · subst hj; simp
        · by_cases hj' : j = slotE i false
          · subst hj'; simp [StackMachine.set, hfs]
          · simp [StackMachine.set, hj, hj']
    | false =>
      cases hce : r R.cE with
      | nil =>
        refine ⟨_, (false, r₁), Exec.seq hc₀ (Exec.seq hc₁ (Exec.branchZero (hsg₁.trans hsg)
          (Exec.branchEmpty (hce₁.trans hce) (Exec.stop false r₁)))), ?_, by simp [portModel, hsg, hce, Realizes]⟩
        simp only [portCost]; omega
      | cons c ctail =>
        cases c with
        | false =>
          refine ⟨_, (false, r₁), Exec.seq hc₀ (Exec.seq hc₁ (Exec.branchZero (hsg₁.trans hsg)
            (Exec.branchZero (hce₁.trans hce) (Exec.stop false r₁)))), ?_, by simp [portModel, hsg, hce, Realizes]⟩
          simp only [portCost]; omega
        | true =>
          let r₂ := set r₁ R.cE ctail
          have hp₂ : Exec (.pop R.cE) r₁ 2 (true, r₂) := by
            have := Exec.pop R.cE r₁
            rw [hce₁, hce] at this
            exact this
          have hce₂ : r₂ R.cE = ctail := by simp [r₂]
          have hf₂ : r₂ (slotE i false) = [] := by simp [r₂, hf₁]
          have ht₂ : r₂ (slotE i true) = [] := by simp [r₂, ht₁]
          have hr₂ : r₂ = set (set (set r R.cE ctail) (slotE i false) []) (slotE i true) [] := by
            funext j
            simp only [r₂, r₁, r₀, StackMachine.set]
            by_cases hj : j = slotE i true
            · subst hj; simp []
            · by_cases hj' : j = slotE i false
              · subst hj'; simp [hfs]
              · simp [hj, hj']
          cases ctail with
          | nil =>
            obtain ⟨t, ht, he⟩ := hpush 4 5 r₂
            refine ⟨_, _, Exec.seq hc₀ (Exec.seq hc₁ (Exec.branchZero (hsg₁.trans hsg)
              (Exec.branchOne (hce₁.trans hce) (Exec.seq hp₂ (Exec.branchEmpty hce₂ he))))), ?_, ?_⟩
            · simp only [portCost]; omega
            · simp only [portModel, hsg, hce, Realizes, Prod.mk.injEq, true_and]
              rw [hfinal 4 5 r₂ false 1 hf₂ ht₂ (by simp [variableEndpoint]) (by simp [variableEndpoint])]
              rw [hr₂]
              simp only [portState]
              funext j
              by_cases hj : j = slotE i true
              · subst hj; simp
              · by_cases hj' : j = slotE i false
                · subst hj'; simp [StackMachine.set, hfs]
                · simp [StackMachine.set, hj, hj']
          | cons c₂ ctail₂ =>
            cases c₂ with
            | false =>
              refine ⟨_, (false, r₂), Exec.seq hc₀ (Exec.seq hc₁ (Exec.branchZero (hsg₁.trans hsg)
                (Exec.branchOne (hce₁.trans hce) (Exec.seq hp₂ (Exec.branchZero hce₂ (Exec.stop false r₂)))))),
                ?_, by simp [portModel, hsg, hce, Realizes]⟩
              simp only [portCost]; omega
            | true =>
              obtain ⟨t, ht, he⟩ := hpush 0 3 r₂
              refine ⟨_, _, Exec.seq hc₀ (Exec.seq hc₁ (Exec.branchZero (hsg₁.trans hsg)
                (Exec.branchOne (hce₁.trans hce) (Exec.seq hp₂ (Exec.branchOne hce₂ he))))), ?_, ?_⟩
              · simp only [portCost]; omega
              · simp only [portModel, hsg, hce, Realizes, Prod.mk.injEq, true_and]
                rw [hfinal 0 3 r₂ false 2 hf₂ ht₂ (by simp [variableEndpoint]) (by simp [variableEndpoint])]
                rw [hr₂]
                simp only [portState]
                funext j
                by_cases hj : j = slotE i true
                · subst hj; simp
                · by_cases hj' : j = slotE i false
                  · subst hj'; simp [StackMachine.set, hfs]
                  · simp [StackMachine.set, hj, hj']

theorem Work.port {k L : Nat} {i : Nat} (hi : i < 3) {r r' : Regs} (h : Work k L r)
    (hm : portModel i r = some r') : Work k L r' := by
  obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  unfold portModel at hm
  cases hsg : r (slotS i) with
  | nil => rw [hsg] at hm; simp at hm
  | cons sg stail =>
    rw [hsg] at hm
    cases sg with
    | true =>
      simp only [Option.some.injEq] at hm
      subst hm
      simp +decide only [portState, variableEndpoint]
      rcases slot_cases hi with rfl | rfl | rfl <;> work_fields
    | false =>
      cases hce : r R.cE with
      | nil => rw [hce] at hm; simp at hm
      | cons c ctail =>
        rw [hce] at hm
        have h10' : ctail.length + 1 ≤ L := by rw [hce] at h10; simpa using h10
        have h10'' : ∀ c₂ ctail₂, ctail = c₂ :: ctail₂ → ctail₂.length + 2 ≤ L := by
          intro c₂ ctail₂ hc; subst hc; simpa using h10'
        cases c with
        | false => simp at hm
        | true =>
          cases ctail with
          | nil =>
            simp only [Option.some.injEq] at hm
            subst hm
            simp +decide only [portState, variableEndpoint]
            rcases slot_cases hi with rfl | rfl | rfl <;> work_fields
          | cons c₂ ctail₂ =>
            cases c₂ with
            | false => simp at hm
            | true =>
              have := h10'' true ctail₂ rfl
              simp only [Option.some.injEq] at hm
              subst hm
              simp +decide only [portState, variableEndpoint]
              rcases slot_cases hi with rfl | rfl | rfl <;> work_fields

/-! ### The block of the variable -/

/-- `slotB i := gadgetWidth k · slotV i`. -/
def mulW (i : Nat) : Command K := .multiply (slotV i) R.W (slotB i) R.mc R.s

def mulWModel (k : Nat) (i : Nat) (r : Regs) : Regs :=
  set r (slotB i) (unary (gadgetWidth k * (r (slotV i)).length))

def mulWCost (k L : Nat) : Nat :=
  gadgetWidth k * L + 5 * gadgetWidth k + gadgetWidth k * (5 * L + 5) + 10

theorem Spec.mulW (k : Nat) (i : Nat) {L : Nat} :
    Spec (Registered.mulW i) (Work k L) (mulWCost k L) (fun r => some (mulWModel k i r)) := by
  have h := Spec.multiply (src := slotV i) (factor := R.W) (dst := slotB i) (counter := R.mc)
    (scratch := R.s) (by simp) (by simp) (by simp) (by simp) (by simp) (by decide) (by decide) (by decide)
    (by simp) (P := Work k L) (w := gadgetWidth k) (a := L) (b := gadgetWidth k * L)
    (fun r hr => hr.base.s) (fun r hr => hr.base.W) (fun r hr => hr.base.mc)
    (fun r hr => ⟨hr.v i, hr.b i⟩)
  exact h.congr (fun r _ => rfl)

theorem Work.mulW {k L : Nat} {i : Nat} (hi : i < 3) {r : Regs} (h : Work k L r) :
    Work k L (mulWModel k i r) := by
  obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  rcases slot_cases hi with rfl | rfl | rfl <;>
  · simp only [mulWModel]
    work_fields
    all_goals exact Nat.mul_le_mul_left _ (by assumption)

/-! ### Reading one literal -/

def readLit (i : Nat) : Command K :=
  .seq (readLitCode i) (.seq (scanLoop i) (.seq (portEndpoints i) (mulW i)))

def readLitModel (k : Nat) (i : Nat) (r : Regs) : Option Regs :=
  (readLitCodeModel i r).bind fun r₁ => (scanLoopModel i r₁).bind fun r₂ =>
    (portModel i r₂).bind fun r₃ => some (mulWModel k i r₃)

def readLitCost (k L : Nat) : Nat := readLitCodeCost L + scanLoopCost L + portCost + mulWCost k L

theorem Work.readLit {k L : Nat} {i : Nat} (hi : i < 3) {r r' : Regs} (h : Work k L r)
    (hm : readLitModel k i r = some r') : Work k L r' := by
  unfold readLitModel at hm
  cases h₁ : readLitCodeModel i r with
  | none => rw [h₁] at hm; simp at hm
  | some r₁ =>
    rw [h₁, Option.bind_some] at hm
    cases h₂ : scanLoopModel i r₁ with
    | none => rw [h₂] at hm; simp at hm
    | some r₂ =>
      rw [h₂, Option.bind_some] at hm
      cases h₃ : portModel i r₂ with
      | none => rw [h₃] at hm; simp at hm
      | some r₃ =>
        rw [h₃, Option.bind_some] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        exact Work.mulW hi (Work.port hi (Work.scanLoop (Work.readLitCode hi h h₁) h₂) h₃)

theorem Spec.readLit (k : Nat) (i : Nat) (hi : i < 3) {L : Nat} :
    Spec (Registered.readLit i) (Work k L) (readLitCost k L) (readLitModel k i) := by
  have s1 := Spec.readLitCode i (P := Work k L) (L := L) (fun r hr => hr.base.s) (fun r hr => hr.base.g)
    (fun r hr => by have := hr.size; omega) (fun r hr => hr.v i) (fun r hr => hr.sg i)
  have s2 := Spec.scanLoop k i (L := L)
  have s3 := Spec.portEndpoints i (P := Work k L) (fun r hr => ⟨hr.e i false, hr.e i true⟩)
  have s4 := Spec.mulW k i (L := L)
  have h := s1.seq (P₂ := Work k L) (fun r r' hr hm => Work.readLitCode hi hr hm)
    (s2.seq (P₂ := Work k L) (fun r r' hr hm => Work.scanLoop hr hm)
      (s3.seq (P₂ := Work k L) (fun r r' hr hm => Work.port hi hr hm) s4))
  exact (h.mono (fun r hr => hr) (by simp only [readLitCost]; omega)).congr (fun r _ => rfl)

theorem readLit_writes (i : Nat) (j : Reg) (hj : j ≠ R.inB ∧ j ≠ slotS i ∧ j ≠ slotV i ∧ j ≠ R.done ∧
    j ≠ R.dc ∧ j ≠ R.g ∧ j ≠ R.scan ∧ j ≠ R.sv ∧ j ≠ R.cE ∧ j ≠ R.t1 ∧ j ≠ R.t2 ∧ j ≠ R.sc ∧
    j ≠ slotE i false ∧ j ≠ slotE i true ∧ j ≠ slotB i ∧ j ≠ R.mc) :
    writes (readLit i) j = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hj
  have hcode : writes (readLitCode i) j = false := by
    simp [readLitCode, setSign, litRest, writes, readUnary, Complexity.Restricted.readUnaryC,
      Complexity.Restricted.readUnaryBody, h1, h2, h3, h4, h5, h6]
  simp [readLit, writes, hcode, scanLoop_writes i j ⟨h7, h8, h9, h6, h10, h11, h12⟩,
    portEndpoints_writes i j ⟨h9, h13, h14⟩, mulW, h15, h16]

end STACS2027.Registered
