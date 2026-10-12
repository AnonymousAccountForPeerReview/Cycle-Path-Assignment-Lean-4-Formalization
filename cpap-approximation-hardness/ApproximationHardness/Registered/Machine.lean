module

public import ApproximationHardness.Registered.Program
import Lean.Elab.Tactic.Omega

/-!
# The complete machine and its polynomial time bound

`main k` initializes the registers, runs the three passes and prepends the record
count; `program k` is `main k` wrapped so that the decision is always `true`.
`machine k` is the registered foundation's compilation of `program k` to a finite
stack machine, and `instanceMapWord k` the word function it computes within
`bound k` steps. `polyTime_instanceMapWord` is the registered-model statement:
the function is `PolyTime` (computed by a single-tape machine within a polynomial
number of steps on every input).
-/

@[expose] public section

namespace STACS2027.Registered

open Complexity
open Complexity.SAT
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame)

/-! ### Initialization -/

/-- Copy the input to the two input registers, clear the output, write the constants. -/
def initPhase (k : Nat) : Command K :=
  .seq (.copy R.out R.inA R.s) (.seq (.copy R.out R.inB R.s) (.seq (.clear R.out)
    (.seq (pushN R.W (gadgetWidth k)) (pushN R.two 2))))

def initModel (k : Nat) (r : Regs) : Regs :=
  set (set (set (set (set r R.inA (r R.out)) R.inB (r R.out)) R.out []) R.W (unary (gadgetWidth k)))
    R.two [true, true]

def initCost (k L : Nat) : Nat := 2 * (L + 5 * L + 6) + (L + 2) + (2 * gadgetWidth k + 1) + 5

/-- The initial registers: the input in register `0`, every other register empty. -/
def initRegs (input : SAT.Word) : Regs := fun j => if j = 0 then input else []

/-- The registers that stay empty from the initialization to the end of the variable loop. -/
def zeroRegs₁ : List Reg :=
  [R.done, R.dc, R.j, R.nj, R.bnj, R.scan, R.sc, R.sv, R.cE, R.v0, R.v1, R.v2, R.sg0, R.sg1, R.sg2,
    R.b0, R.b1, R.b2, R.ef0, R.et0, R.ef1, R.et1, R.ef2, R.et2]

/-- The state after the initialization. -/
structure Initialized (k L : Nat) (r : Regs) : Prop where
  a : AInv k L r
  inB : (r R.inB).length ≤ L
  zero : ∀ j ∈ zeroRegs₁, r j = []
  out : r R.out = []
  cnt : r R.cnt = []
  vb : r R.vb = []
  vc : r R.vc = []

theorem initModel_initialized (k L : Nat) (input : SAT.Word) (hL : input.length ≤ L) :
    Initialized k L (initModel k (initRegs input)) := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp +decide [initModel, initRegs, StackMachine.set, zeroRegs₁, hL]

theorem Spec.initPhase (k : Nat) {L : Nat} (input : SAT.Word) (hL : input.length ≤ L) :
    Spec (Registered.initPhase k) (fun r => r = initRegs input) (initCost k L)
      (fun r => some (initModel k r)) := by
  let f₁ : Regs → Regs := fun r => set r R.inA (r R.out)
  let f₂ : Regs → Regs := fun r => set (f₁ r) R.inB (f₁ r R.out)
  let f₃ : Regs → Regs := fun r => set (f₂ r) R.out []
  let f₄ : Regs → Regs := fun r => set (f₃ r) R.W (List.replicate (gadgetWidth k) true ++ f₃ r R.W)
  have s1 := Spec.copy (src := R.out) (dst := R.inA) (scratch := R.s) (by decide) (by decide) (by decide)
    (P := fun r => r = initRegs input) (a := L) (b := 0) (fun r hr => by subst hr; rfl)
    (fun r hr => by subst hr; exact ⟨by simpa [initRegs] using hL, by simp [initRegs]⟩)
  have s2 := Spec.copy (src := R.out) (dst := R.inB) (scratch := R.s) (by decide) (by decide) (by decide)
    (P := fun r' => ∃ r, r = initRegs input ∧ r' = f₁ r) (a := L) (b := 0)
    (by rintro r' ⟨r, rfl, rfl⟩; simp +decide [f₁, initRegs])
    (by rintro r' ⟨r, rfl, rfl⟩; simp +decide [f₁, initRegs]; exact hL)
  have s3 := Spec.clear R.out (P := fun r' => ∃ r, r = initRegs input ∧ r' = f₂ r) (L := L)
    (by rintro r' ⟨r, rfl, rfl⟩; simp +decide [f₂, f₁, initRegs, StackMachine.set]; exact hL)
  have s4 := Spec.pushN R.W (gadgetWidth k) (fun r' => ∃ r, r = initRegs input ∧ r' = f₃ r)
  have s5 := Spec.pushN R.two 2 (fun r' => ∃ r, r = initRegs input ∧ r' = f₄ r)
  have h := s1.seq (fun r r' hr hm => ⟨r, hr, by simpa [f₁] using hm.symm⟩)
    (s2.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa [f₂] using hm.symm⟩)
      (s3.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa [f₃] using hm.symm⟩)
        (s4.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa [f₄] using hm.symm⟩)
          s5)))
  refine (h.mono (fun r hr => hr) ?_).congr ?_
  · simp only [initCost]; omega
  · rintro r rfl
    simp only [Option.bind_some, Option.some.injEq, initModel]
    funext j
    simp +decide [initRegs, StackMachine.set, unary]

/-! ### The main program -/

def main (k : Nat) : Command K :=
  .seq (initPhase k) (.seq passA (.seq (varLoop k) (.seq (passB k) (.prependNat R.cnt R.out R.s))))

def mainModel (k : Nat) (r : Regs) : Option Regs :=
  (passAModel (initModel k r)).bind fun r₁ => (varLoopModel k r₁).bind fun r₂ =>
    (passBModel k r₂).bind fun r₃ => some (set r₃ R.out (writeNat (r₃ R.cnt).length ++ r₃ R.out))

def mainCost (k L : Nat) : Nat :=
  initCost k L + passACost L + varLoopCost k L + passBCost k L + (5 * recordBudget k L + 6)

theorem varLoop_writes (k : Nat) (i : Reg) (hi : i ≠ R.out ∧ i ≠ R.tmp ∧ i ≠ R.cnt ∧ i ≠ R.vb ∧ i ≠ R.vc) :
    writes (varLoop k) i = false := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hi
  simp [varLoop, writes, h5, varBody_writes k i ⟨h1, h2, h3, h4⟩]

/-- After the first pass. -/
theorem Initialized.passA {k L : Nat} {r r' : Regs} (h : Initialized k L r) (hm : passAModel r = some r') :
    Initialized k L r' := by
  have hfr := (Spec.passA k (L := L)).frame h.a hm
  refine ⟨h.a.passA hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr R.inB (passA_writes R.inB (by decide))]; exact h.inB
  · intro j hj
    rw [hfr j (passA_writes j ?_)]
    · exact h.zero j hj
    · simp only [zeroRegs₁, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hfr R.out (passA_writes R.out (by decide))]; exact h.out
  · rw [hfr R.cnt (passA_writes R.cnt (by decide))]; exact h.cnt
  · rw [hfr R.vb (passA_writes R.vb (by decide))]; exact h.vb
  · rw [hfr R.vc (passA_writes R.vc (by decide))]; exact h.vc

theorem Initialized.varLoopPre {k L : Nat} {r : Regs} (h : Initialized k L r) : VarLoopPre k L r :=
  ⟨h.a.base, h.a.n, h.vb, by rw [h.vc]; simp, h.cnt⟩

/-- After the variable loop. -/
structure AfterVar (k L : Nat) (r : Regs) : Prop where
  var : VarInv k L r
  inB : (r R.inB).length ≤ L
  n : (r R.n).length ≤ L
  m : (r R.m).length ≤ L
  len : (r R.len).length ≤ L
  zero : ∀ j ∈ zeroRegs₁, r j = []

theorem Initialized.varLoop {k L : Nat} {r r' : Regs} (h : Initialized k L r)
    (hm : varLoopModel k r = some r') : AfterVar k L r' := by
  have hfr := (Spec.varLoop k (L := L)).frame h.varLoopPre hm
  refine ⟨h.varLoopPre.run hm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr R.inB (varLoop_writes k R.inB (by decide))]; exact h.inB
  · rw [hfr R.n (varLoop_writes k R.n (by decide))]; exact h.a.n
  · rw [hfr R.m (varLoop_writes k R.m (by decide))]; exact h.a.m
  · rw [hfr R.len (varLoop_writes k R.len (by decide))]; exact h.a.len
  · intro j hj
    rw [hfr j (varLoop_writes k j ?_)]
    · exact h.zero j hj
    · simp only [zeroRegs₁, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem AfterVar.passBPre {k L : Nat} {r : Regs} (h : AfterVar k L r) : PassBPre k L r := by
  have hz := h.zero
  simp only [zeroRegs₁, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20,
    z21, z22, z23, z24⟩ := hz
  have hvb := h.var.vb
  have hcnt := h.var.cnt
  have hinB := h.inB
  refine ⟨⟨h.var.base, ?_, ?_, h.n, h.len, ?_, ?_, ?_, ?_, z8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩, z3, h.m, ?_⟩
  all_goals (try simp only [z1, z2, z4, z5, z6, z7, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19,
    z20, z21, z22, z23, z24, List.length_nil])
  all_goals first | omega | exact Nat.zero_le _

theorem Spec.main (k : Nat) {L : Nat} (input : SAT.Word) (hL : input.length ≤ L) :
    Spec (Registered.main k) (fun r => r = initRegs input) (mainCost k L) (mainModel k) := by
  have s0 := Spec.initPhase k (L := L) input hL
  have s1 := (Spec.passA k (L := L)).mono (fun r (hr : Initialized k L r) => hr.a) (Nat.le_refl _)
  have s2 := (Spec.varLoop k (L := L)).mono (fun r (hr : Initialized k L r) => hr.varLoopPre) (Nat.le_refl _)
  have s3 := (Spec.passB k (L := L)).mono (fun r (hr : AfterVar k L r) => hr.passBPre) (Nat.le_refl _)
  have s4 := Spec.prependNat (number := R.cnt) (output := R.out) (scratch := R.s) (by decide) (by decide)
    (by decide) (P := ClauseInv k L (recordBudget k L)) (a := recordBudget k L)
    (fun r hr => hr.work.base.s) (fun r hr => by have := hr.cnt; omega)
  have h := s0.seq (P₂ := Initialized k L) (fun r r' hr hm => by
      simp only [Option.some.injEq] at hm; subst hm; subst hr; exact initModel_initialized k L input hL)
    (s1.seq (P₂ := Initialized k L) (fun r r' hr hm => hr.passA hm)
      (s2.seq (P₂ := AfterVar k L) (fun r r' hr hm => hr.varLoop hm)
        (s3.seq (P₂ := ClauseInv k L (recordBudget k L)) (fun r r' hr hm => by
          unfold passBModel at hm
          cases h₁ : readUnaryModel R.inB R.m r with
          | none => rw [h₁] at hm; simp at hm
          | some r₁ =>
            rw [h₁, Option.bind_some] at hm
            exact iter_invariant (j := R.m) (P := ClauseInv k L (recordBudget k L)) (m := clauseBodyModel k)
              (fun r b tail r' hr hmm hb => (hr.pop b tail hmm).clauseBody hb) _ _ _
              (hr.passBPre.start h₁) hm) s4)))
  refine (h.mono (fun r hr => hr) ?_).congr ?_
  · simp only [mainCost]; omega
  · intro r _
    simp only [Option.bind_some, mainModel]

/-- The program: `main k`, and the decision `true` whether or not it succeeded. -/
def program (k : Nat) : Command K := .ifThenElse (main k) (.stop true) (.stop true)

theorem exec_program (k : Nat) {L : Nat} (input : SAT.Word) (hL : input.length ≤ L) :
    ∃ t r', Exec (program k) (initRegs input) t (true, r') ∧ t ≤ mainCost k L + 1 ∧
      ∀ r'', mainModel k (initRegs input) = some r'' → r' = r'' := by
  obtain ⟨t, res, he, ht, hres⟩ := Spec.main k (L := L) input hL (initRegs input) rfl
  obtain ⟨b, r'⟩ := res
  cases b with
  | true =>
    refine ⟨t + 1, r', Exec.ifTrue he (Exec.stop true r'), by omega, ?_⟩
    intro r'' hm
    rw [hm] at hres
    simp only [Realizes, Prod.mk.injEq, true_and] at hres
    exact hres
  | false =>
    refine ⟨t + 1, r', Exec.ifFalse he (Exec.stop true r'), by omega, ?_⟩
    intro r'' hm
    rw [hm] at hres
    simp [Realizes] at hres

/-! ### The compiled machine -/

/-- The finite stack machine of the program (the registered foundation's compiler). -/
def machine (k : Nat) : StackMachine.Machine := StackTableauProgram.machine (program k)

/-- The step bound of the machine on inputs of length `L`. -/
def bound (k L : Nat) : Nat := mainCost k L + 1

theorem machine_run (k : Nat) (input : SAT.Word) :
    ∃ r', StackMachine.runInput (machine k) (bound k input.length) input = some (true, r') ∧
      ∀ r'', mainModel k (initRegs input) = some r'' → r' = r'' := by
  obtain ⟨t, r', he, ht, hres⟩ := exec_program k (L := input.length) input (Nat.le_refl _)
  refine ⟨r', ?_, hres⟩
  have hrun := he.machine_run
  change StackMachine.run (machine k) t (StackMachine.initial (machine k) input) = some (true, r') at hrun
  obtain ⟨extra, hextra⟩ : ∃ extra, bound k input.length = t + extra := ⟨bound k input.length - t, by
    simp only [bound]; omega⟩
  rw [StackMachine.runInput, hextra]
  exact StackMachine.run_add _ _ _ _ _ hrun

/-- The word function computed by the machine: the output register after `bound k |input|` steps. -/
def instanceMapWord (k : Nat) (input : SAT.Word) : SAT.Word :=
  match StackMachine.runInput (machine k) (bound k input.length) input with
  | some (_, r) => r 0
  | none => []

theorem instanceMapWord_eq (k : Nat) (input : SAT.Word) {r' : Regs}
    (h : StackMachine.runInput (machine k) (bound k input.length) input = some (true, r')) :
    instanceMapWord k input = r' 0 := by
  simp only [instanceMapWord, h]
  rfl

/-- On every input, the machine halts with decision `true` within `bound k |input|` steps and
its output register holds `instanceMapWord k input`. -/
theorem machine_computes (k : Nat) (input : SAT.Word) :
    ∃ time registers, time ≤ bound k input.length ∧
      StackMachine.runInput (machine k) time input = some (true, registers) ∧
      registers 0 = instanceMapWord k input := by
  obtain ⟨r', hrun, _⟩ := machine_run k input
  exact ⟨_, r', Nat.le_refl _, hrun, (instanceMapWord_eq k input hrun).symm⟩

/-! ### The polynomial bound -/

section Polynomial

open PolynomialBound

theorem pb_affine (a b : Nat) : PolynomialBound (fun L => a * L + b) :=
  ((constant a).mul identity).add (constant b)

theorem pb_edgeCost_W (k : Nat) :
    PolynomialBound (fun L => edgeCost (gadgetWidth k * L) 0 (gadgetWidth k)) :=
  ((((constant 22).mul ((constant (gadgetWidth k)).mul identity)).add ((constant 22).mul (constant 0))).add
    ((constant 16).mul (constant (gadgetWidth k)))).add (constant 58)

theorem pb_edgeCost_2W (k : Nat) :
    PolynomialBound (fun L => edgeCost (gadgetWidth k * (2 * L)) 6 (gadgetWidth k)) :=
  ((((constant 22).mul ((constant (gadgetWidth k)).mul ((constant 2).mul identity))).add
    ((constant 22).mul (constant 6))).add ((constant 16).mul (constant (gadgetWidth k)))).add (constant 58)

theorem pb_readLitCodeCost : PolynomialBound readLitCodeCost := pb_affine 14 40

theorem pb_scanStepCost : PolynomialBound scanStepCost := pb_affine 30 50

theorem pb_scanLoopCost : PolynomialBound scanLoopCost :=
  (pb_affine 14 16).add ((identity.mul (pb_scanStepCost.add (constant 1))).add (constant 2))

theorem pb_mulWCost (k : Nat) : PolynomialBound (mulWCost k) :=
  ((((constant (gadgetWidth k)).mul identity).add (constant (5 * gadgetWidth k))).add
    ((constant (gadgetWidth k)).mul (pb_affine 5 5))).add (constant 10)

theorem pb_readLitCost (k : Nat) : PolynomialBound (readLitCost k) :=
  ((pb_readLitCodeCost.add pb_scanLoopCost).add (constant portCost)).add (pb_mulWCost k)

theorem pb_setupCost (k : Nat) : PolynomialBound (setupCost k) :=
  (((((constant 2).mul identity).add ((constant 5).mul identity)).add (constant 6)).add (pb_affine 5 4)).add
    (((((constant (gadgetWidth k)).mul ((constant 2).mul identity)).add (constant (5 * gadgetWidth k))).add
      ((constant (gadgetWidth k)).mul (((constant 5).mul ((constant 2).mul identity)).add (constant 5)))).add
      (constant 10)) |>.add (pb_affine 2 2)

theorem pb_clauseEmitCost (k : Nat) : PolynomialBound (clauseEmitCost k) :=
  ((constant (recordBound k)).mul (pb_edgeCost_2W k)).add (constant 1)

theorem pb_finishCost (k : Nat) : PolynomialBound (finishCost k) :=
  (constant 2).add (((constant 17).mul ((((constant (gadgetWidth k)).mul ((constant 2).mul identity)).add
    (constant 6)).add (constant 2))).add (constant 1))

theorem pb_clauseKCost (k : Nat) : PolynomialBound (clauseKCost k) :=
  (((((constant 3).mul (pb_readLitCost k)).add (constant 1)).add (pb_setupCost k)).add
    (pb_clauseEmitCost k)).add (pb_finishCost k)

theorem pb_clauseBodyCost (k : Nat) : PolynomialBound (clauseBodyCost k) :=
  (pb_affine 9 10).add ((pb_clauseKCost k).add (constant 12))

theorem pb_passBCost (k : Nat) : PolynomialBound (passBCost k) :=
  (pb_affine 9 10).add ((identity.mul ((pb_clauseBodyCost k).add (constant 1))).add (constant 2))

theorem pb_varBodyCost (k : Nat) : PolynomialBound (varBodyCost k) :=
  (((constant (variableGraph k).length).mul (pb_edgeCost_W k)).add (constant 1)).add
    (constant (5 * gadgetWidth k + 4))

theorem pb_varLoopCost (k : Nat) : PolynomialBound (varLoopCost k) :=
  ((identity.add ((constant 5).mul identity)).add (constant 6)).add
    ((identity.mul ((pb_varBodyCost k).add (constant 1))).add (constant 2))

theorem pb_litACost : PolynomialBound litACost :=
  ((pb_affine 9 10).add (((constant 2).add
    ((((constant 15).mul (identity.add (constant 1))).add (constant 18)).add
      ((identity.add ((constant 5).mul (identity.add (constant 1)))).add (constant 6)))).add
    ((identity.add (constant 1)).add (constant 2)))).add (constant 5)

theorem pb_clauseACost : PolynomialBound clauseACost :=
  (pb_affine 9 10).add ((identity.mul (pb_litACost.add (constant 1))).add (constant 2))

theorem pb_passACost : PolynomialBound passACost :=
  (pb_affine 9 10).add ((identity.mul (pb_clauseACost.add (constant 1))).add (constant 2))

theorem pb_initCost (k : Nat) : PolynomialBound (initCost k) :=
  ((((constant 2).mul ((identity.add ((constant 5).mul identity)).add (constant 6))).add
    (identity.add (constant 2))).add (constant (2 * gadgetWidth k + 1))).add (constant 5)

theorem pb_recordBudget (k : Nat) : PolynomialBound (recordBudget k) :=
  ((constant (variableGraph k).length).mul identity).add ((constant (recordBound k)).mul identity)

theorem pb_mainCost (k : Nat) : PolynomialBound (mainCost k) :=
  ((((pb_initCost k).add pb_passACost).add (pb_varLoopCost k)).add (pb_passBCost k)).add
    (((constant 5).mul (pb_recordBudget k)).add (constant 6))

theorem polynomial_bound (k : Nat) : PolynomialBound (bound k) := (pb_mainCost k).add (constant 1)

end Polynomial

/-- **The instance map is computable in the registered model.** The word function
`instanceMapWord k` is computed by a single-tape machine of the registered foundation
within a polynomial number of steps on every input (`Complexity.PolyTime`). -/
theorem polyTime_instanceMapWord (k : Nat) : PolyTime (instanceMapWord k) :=
  StackCompile.polyTime_of_stack (machine k) (bound k) (polynomial_bound k) (machine_computes k)

end STACS2027.Registered
