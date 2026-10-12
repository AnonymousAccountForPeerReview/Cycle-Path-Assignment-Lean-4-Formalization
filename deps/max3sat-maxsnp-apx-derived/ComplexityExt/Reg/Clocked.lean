module

public import ComplexityExt.Reg.Closure
public import ComplexityExt.Reg.Decide
import Lean.Elab.Tactic.Omega

/-!
# Clocked simulation: from "polynomial time on some inputs" to a total `PolyTime` function

For a tape machine `M` and a polynomial clock `powerBound c e`, the function

`clockedOutput M (powerBound c e |x|) x`

returns the output of `M` on `x` when `M` halts with decision `true` within the clock, and
the empty word otherwise.  It is computed, on *every* input, by a polynomial-time machine:

* a register command copies the input and calls a polynomial-time *clock function* whose
  value has length exactly `powerBound c e |x|` (`exists_polyTime_clock`, obtained from the
  closure theorems by iterated unary multiplication);
* `clockedCore M` simulates `M` on two tape-half stacks as `TapeToStacks.core` does, but pops
  one cell of the clock register before each simulated instruction and gives up (decision
  `false`) when the clock is empty;
* on decision `true` the output is extracted with `TapeToStacks.extractor`; on decision
  `false` the (empty) input/output register is returned as it is.

Main results: `exists_polyTime_clocked`, `exists_polyTime_of_stack_run`,
`exists_polyTime_of_stack_on`.  This file is core-only (no Mathlib).
-/

@[expose] public section

namespace Complexity.Reg

open Complexity.StackMachine (set branch)
open Complexity.StackProgram (Program Op Encoding mapOp)
open Complexity.TapeToStacks (regs symbols high low pairSymbol readCost Label)

set_option backward.isDefEq.respectTransparency false

/-! ### A polynomial-time clock of length exactly `powerBound c e |x|` -/

/-- One round of unary multiplication on pairs: `(x, acc) ↦ (x, x ++ true :: acc)`. -/
def clockStep (w : Word) : Word :=
  pairWords (unpair w).1 ((unpair w).1 ++ ([true] ++ (unpair w).2))

theorem polyTime_clockStep : PolyTime clockStep :=
  polyTime_pair polyTime_pair_fst
    (polyTime_append polyTime_pair_fst (polyTime_append (polyTime_const [true]) polyTime_pair_snd))

theorem clockStep_pairWords (x acc : Word) :
    clockStep (pairWords x acc) = pairWords x (x ++ ([true] ++ acc)) := by
  simp [clockStep]

theorem iterate_clockStep (x : Word) (i : Nat) (acc : Word) :
    ∃ acc', iterate clockStep i (pairWords x acc) = pairWords x acc' ∧
      acc'.length = i * (x.length + 1) + acc.length := by
  induction i generalizing acc with
  | zero => exact ⟨acc, rfl, by simp⟩
  | succ i ih =>
    obtain ⟨acc', h1, h2⟩ := ih (x ++ ([true] ++ acc))
    refine ⟨acc', ?_, ?_⟩
    · show iterate clockStep i (clockStep (pairWords x acc)) = _
      rw [clockStep_pairWords]
      exact h1
    · rw [h2, Nat.succ_mul]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- For every polynomial `powerBound c e` there is a polynomial-time function whose value on
`x` has length exactly `powerBound c e |x|`. -/
theorem exists_polyTime_clock (c e : Nat) :
    ∃ g : Word → Word, PolyTime g ∧ ∀ x, (g x).length = powerBound c e x.length := by
  induction e with
  | zero =>
    refine ⟨fun _ => List.replicate c true, polyTime_const _, fun x => ?_⟩
    rw [List.length_replicate, powerBound_eq, Nat.pow_zero, Nat.mul_one]
  | succ e ih =>
    obtain ⟨g, hg, hlen⟩ := ih
    have hinit : PolyTime (fun x : Word => pairWords x []) :=
      polyTime_pair polyTime_id (polyTime_const [])
    have hbound : ∀ (x : Word) (i : Nat), i ≤ (g x).length →
        (iterate clockStep i (pairWords x [])).length ≤
          2 * x.length + 1 + powerBound c e x.length * (x.length + 1) := by
      intro x i hi
      obtain ⟨acc', h1, h2⟩ := iterate_clockStep x i []
      rw [h1, pairWords_length, h2]
      rw [hlen] at hi
      have hmul := Nat.mul_le_mul_right (x.length + 1) hi
      simp only [List.length_nil]
      omega
    have hiter := polyTime_iterate polyTime_clockStep hinit hg
      (fun n => 2 * n + 1 + powerBound c e n * (n + 1))
      ((((PolynomialBound.constant 2).mul PolynomialBound.identity).add
        (PolynomialBound.constant 1)).add ((PolynomialBound.power c e).mul
          (PolynomialBound.identity.add (PolynomialBound.constant 1)))) hbound
    refine ⟨fun x => (unpair (iterate clockStep (g x).length (pairWords x []))).2,
      polyTime_comp polyTime_pair_snd hiter, ?_⟩
    intro x
    obtain ⟨acc', h1, h2⟩ := iterate_clockStep x (g x).length []
    show (unpair (iterate clockStep (g x).length (pairWords x []))).2.length = _
    rw [h1, unpair_pairWords, h2, hlen]
    simp only [List.length_nil, powerBound_eq, Nat.pow_succ, Nat.mul_assoc, Nat.add_zero]

/-! ### Four registers: input/output, two tape halves, clock -/

/-- Register `0` is the input/output word, registers `1` and `2` the two tape halves and
register `3` the clock. -/
def regs4 (io left right clk : List Bool) : StackMachine.Registers 3 :=
  fun i => if i = 0 then io else if i = 1 then left else if i = 2 then right else clk

@[simp] theorem regs4_zero (io left right clk : List Bool) : regs4 io left right clk 0 = io := rfl
@[simp] theorem regs4_one (io left right clk : List Bool) : regs4 io left right clk 1 = left := rfl
@[simp] theorem regs4_two (io left right clk : List Bool) : regs4 io left right clk 2 = right := rfl
@[simp] theorem regs4_three (io left right clk : List Bool) : regs4 io left right clk 3 = clk := rfl

theorem fin_four_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi := i.isLt
  have hn : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hn with hn | hn | hn | hn
  · exact Or.inl (Fin.ext hn)
  · exact Or.inr (Or.inl (Fin.ext hn))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext hn)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext hn)))

@[simp] theorem set_regs4_zero (io left right clk xs : List Bool) :
    set (regs4 io left right clk) 0 xs = regs4 xs left right clk := by
  funext i
  rcases fin_four_cases i with rfl | rfl | rfl | rfl <;> simp [StackMachine.set]

@[simp] theorem set_regs4_one (io left right clk xs : List Bool) :
    set (regs4 io left right clk) 1 xs = regs4 io xs right clk := by
  funext i
  rcases fin_four_cases i with rfl | rfl | rfl | rfl <;> simp [StackMachine.set]

@[simp] theorem set_regs4_two (io left right clk xs : List Bool) :
    set (regs4 io left right clk) 2 xs = regs4 io left xs clk := by
  funext i
  rcases fin_four_cases i with rfl | rfl | rfl | rfl <;> simp [StackMachine.set]

@[simp] theorem set_regs4_three (io left right clk xs : List Bool) :
    set (regs4 io left right clk) 3 xs = regs4 io left right xs := by
  funext i
  rcases fin_four_cases i with rfl | rfl | rfl | rfl <;> simp [StackMachine.set]

/-- The three tape-simulation registers as registers of the four-register machine. -/
def tapeMap (i : Fin 3) : Fin 4 := ⟨i.val, by omega⟩

theorem tapeMap_injective : ∀ i j, tapeMap i = tapeMap j → i = j := by
  intro i j h
  have h' : (tapeMap i).val = (tapeMap j).val := congrArg Fin.val h
  exact Fin.ext h'

theorem pull_tapeMap (io left right clk : List Bool) :
    pull tapeMap (regs4 io left right clk) = regs io left right := by
  funext i
  rcases TapeToStacks.fin_three_cases i with rfl | rfl | rfl <;> rfl

theorem eq_regs4_of_pull (R : StackMachine.Registers 3) (io left right clk : List Bool)
    (h1 : pull tapeMap R = regs io left right) (h2 : R 3 = clk) :
    R = regs4 io left right clk := by
  funext i
  rcases fin_four_cases i with rfl | rfl | rfl | rfl
  · exact congrFun h1 0
  · exact congrFun h1 1
  · exact congrFun h1 2
  · exact h2

/-- A three-register tape program runs unchanged next to the clock register. -/
theorem exec_rename_tape {L : Type} {p : Program 2 L} {q : L}
    {io left right io' left' right' : List Bool} {t : Nat} {b : Bool}
    (h : StackProgram.Exec p q (regs io left right) t (b, regs io' left' right'))
    (clk : List Bool) :
    StackProgram.Exec (rename tapeMap p) q (regs4 io left right clk) t
      (b, regs4 io' left' right' clk) := by
  obtain ⟨R', he, hp, hf⟩ := exec_rename tapeMap tapeMap_injective h
    (regs4 io left right clk) (pull_tapeMap io left right clk)
  have h3 : R' 3 = clk := by
    apply hf 3
    intro i hi
    have hv : i.val = 3 := congrArg Fin.val hi
    have := i.isLt
    omega
  have hR : R' = regs4 io' left' right' clk := eq_regs4_of_pull R' _ _ _ _ hp h3
  rw [hR] at he
  exact he

/-! ### The clocked tape simulation -/

/-- Labels of the clocked simulation: those of `TapeToStacks.core`, and a clock test
`(q, a)` before the instruction of state `q` on scanned symbol `a` is executed. -/
abbrev ClockLabel (M : Machine) := Sum (Label M) (Fin (M.states + 1) × Symbol)

def clockEncoding (M : Machine) : Encoding (ClockLabel M) :=
  (TapeToStacks.labelEncoding M).sum
    ((Encoding.fin M.states).prod TapeToStacks.symbolEncoding)

/-- `TapeToStacks.core` with a clock: before each simulated instruction one cell of the clock
register `3` is popped; when the clock is empty the simulation stops with decision `false`. -/
def clockedCore (M : Machine) : Program 3 (ClockLabel M) where
  start := .inl (.read M.start false)
  code label := match label with
    | .inl (.read q side) =>
      .pop (if side then 1 else 2) (.inr (q, .blank))
        (.inl (.readLow q side false)) (.inl (.readLow q side true))
    | .inl (.readLow q side first) =>
      .pop (if side then 1 else 2) (.inl (.done false))
        (.inr (q, pairSymbol first false)) (.inr (q, pairSymbol first true))
    | .inr (q, a) => .pop 3 (.inl (.done false)) (.inl (.main q a)) (.inl (.main q a))
    | .inl (.main q a) => match M.code q a with
      | .halt b => .push 2 (low a) (.inl (.haltHigh b (high a)))
      | .step a .stay q' => .goto (.inr (q', a))
      | .step a .left q' => .push 2 (low a) (.inl (.writeHigh q' true (high a)))
      | .step a .right q' => .push 1 (low a) (.inl (.writeHigh q' false (high a)))
    | .inl (.writeHigh q side first) =>
      .push (if side then 2 else 1) first (.inl (.read q side))
    | .inl (.haltHigh b first) => .push 2 first (.inl (.done b))
    | .inl (.done b) => .halt b

theorem exec_clocked_read_right (M : Machine) (q : Fin (M.states + 1))
    (io left : List Bool) (right : List Symbol) (clk : List Bool) (time : Nat)
    (result : Bool × StackMachine.Registers 3)
    (h : StackProgram.Exec (clockedCore M) (.inr (q, right.headD .blank))
      (regs4 io left (symbols (right.drop 1)) clk) time result) :
    StackProgram.Exec (clockedCore M) (.inl (.read q false)) (regs4 io left (symbols right) clk)
      (time + readCost right) result := by
  cases right with
  | nil =>
    exact .next (by simp [StackProgram.step, clockedCore, symbols, StackMachine.branch]) h
  | cons a rest =>
    have hs : StackProgram.step (clockedCore M) (.inl (.read q false))
        (regs4 io left (symbols (a :: rest)) clk) =
        .inr (.inl (.readLow q false (high a)), regs4 io left (low a :: symbols rest) clk) := by
      cases hhigh : high a <;>
        simp [StackProgram.step, clockedCore, symbols, StackMachine.branch, hhigh]
    have ht : StackProgram.step (clockedCore M) (.inl (.readLow q false (high a)))
        (regs4 io left (low a :: symbols rest) clk) =
        .inr (.inr (q, a), regs4 io left (symbols rest) clk) := by
      cases hlow : low a <;>
        simpa [StackProgram.step, clockedCore, StackMachine.branch, hlow]
          using TapeToStacks.pairSymbol_bits a
    exact .next hs (.next ht h)

theorem exec_clocked_read_left (M : Machine) (q : Fin (M.states + 1))
    (io right : List Bool) (left : List Symbol) (clk : List Bool) (time : Nat)
    (result : Bool × StackMachine.Registers 3)
    (h : StackProgram.Exec (clockedCore M) (.inr (q, left.headD .blank))
      (regs4 io (symbols (left.drop 1)) right clk) time result) :
    StackProgram.Exec (clockedCore M) (.inl (.read q true)) (regs4 io (symbols left) right clk)
      (time + readCost left) result := by
  cases left with
  | nil =>
    exact .next (by simp [StackProgram.step, clockedCore, symbols, StackMachine.branch]) h
  | cons a rest =>
    have hs : StackProgram.step (clockedCore M) (.inl (.read q true))
        (regs4 io (symbols (a :: rest)) right clk) =
        .inr (.inl (.readLow q true (high a)), regs4 io (low a :: symbols rest) right clk) := by
      cases hhigh : high a <;>
        simp [StackProgram.step, clockedCore, symbols, StackMachine.branch, hhigh]
    have ht : StackProgram.step (clockedCore M) (.inl (.readLow q true (high a)))
        (regs4 io (low a :: symbols rest) right clk) =
        .inr (.inr (q, a), regs4 io (symbols rest) right clk) := by
      cases hlow : low a <;>
        simpa [StackProgram.step, clockedCore, StackMachine.branch, hlow]
          using TapeToStacks.pairSymbol_bits a
    exact .next hs (.next ht h)

theorem exec_clocked_halt (M : Machine) (q : Fin (M.states + 1)) (a : Symbol)
    (io left : List Bool) (right : List Symbol) (clk : List Bool) (b : Bool)
    (hc : M.code q a = .halt b) :
    StackProgram.Exec (clockedCore M) (.inl (.main q a)) (regs4 io left (symbols right) clk) 3
      (b, regs4 io left (symbols (a :: right)) clk) := by
  apply StackProgram.Exec.next (q' := .inl (.haltHigh b (high a)))
    (r' := regs4 io left (low a :: symbols right) clk)
  · simp [StackProgram.step, clockedCore, hc]
  apply StackProgram.Exec.next (q' := .inl (.done b))
    (r' := regs4 io left (symbols (a :: right)) clk)
  · simp [StackProgram.step, clockedCore, symbols]
  · exact .halt (by simp [StackProgram.step, clockedCore])

theorem exec_clocked_move_right (M : Machine) (q q' : Fin (M.states + 1))
    (scan a : Symbol) (hc : M.code q scan = .step a .right q')
    (io : List Bool) (left right : List Symbol) (clk : List Bool) (time : Nat)
    (result : Bool × StackMachine.Registers 3)
    (h : StackProgram.Exec (clockedCore M) (.inl (.read q' false))
      (regs4 io (symbols (a :: left)) (symbols right) clk) time result) :
    StackProgram.Exec (clockedCore M) (.inl (.main q scan))
      (regs4 io (symbols left) (symbols right) clk) (time + 2) result := by
  apply StackProgram.Exec.next (q' := .inl (.writeHigh q' false (high a)))
    (r' := regs4 io (low a :: symbols left) (symbols right) clk)
  · simp [StackProgram.step, clockedCore, hc]
  apply StackProgram.Exec.next (q' := .inl (.read q' false))
    (r' := regs4 io (symbols (a :: left)) (symbols right) clk)
  · simp [StackProgram.step, clockedCore, symbols]
  · exact h

theorem exec_clocked_move_left (M : Machine) (q q' : Fin (M.states + 1))
    (scan a : Symbol) (hc : M.code q scan = .step a .left q')
    (io : List Bool) (left right : List Symbol) (clk : List Bool) (time : Nat)
    (result : Bool × StackMachine.Registers 3)
    (h : StackProgram.Exec (clockedCore M) (.inl (.read q' true))
      (regs4 io (symbols left) (symbols (a :: right)) clk) time result) :
    StackProgram.Exec (clockedCore M) (.inl (.main q scan))
      (regs4 io (symbols left) (symbols right) clk) (time + 2) result := by
  apply StackProgram.Exec.next (q' := .inl (.writeHigh q' true (high a)))
    (r' := regs4 io (symbols left) (low a :: symbols right) clk)
  · simp [StackProgram.step, clockedCore, hc]
  apply StackProgram.Exec.next (q' := .inl (.read q' true))
    (r' := regs4 io (symbols left) (symbols (a :: right)) clk)
  · simp [StackProgram.step, clockedCore, symbols]
  · exact h

/-- The clock test with a nonempty clock: one instruction, one clock cell. -/
theorem step_clocked_tick (M : Machine) (q : Fin (M.states + 1)) (a : Symbol)
    (io left right : List Bool) (b : Bool) (clk : List Bool) :
    StackProgram.step (clockedCore M) (.inr (q, a)) (regs4 io left right (b :: clk)) =
      .inr (.inl (.main q a), regs4 io left right clk) := by
  cases b <;> simp [StackProgram.step, clockedCore, StackMachine.branch]

/-- One non-halting instruction of `M`, from clock test to clock test, costs at most five
stack instructions and exactly one clock cell. -/
theorem exec_clocked_step (M : Machine) (c : Config M) (a : Symbol) (d : Move)
    (q : Fin (M.states + 1)) (hc : M.code c.state c.tape.read = .step a d q)
    (io : List Bool) (b : Bool) (clk : List Bool) (time : Nat)
    (result : Bool × StackMachine.Registers 3)
    (h : StackProgram.Exec (clockedCore M) (.inr (q, ((c.tape.write a).move d).read))
      (regs4 io (symbols ((c.tape.write a).move d).left)
        (symbols (((c.tape.write a).move d).right.drop 1)) clk) time result) :
    ∃ s, s ≤ time + 5 ∧
      StackProgram.Exec (clockedCore M) (.inr (c.state, c.tape.read))
        (regs4 io (symbols c.tape.left) (symbols (c.tape.right.drop 1)) (b :: clk)) s result := by
  have htick := step_clocked_tick M c.state c.tape.read io (symbols c.tape.left)
    (symbols (c.tape.right.drop 1)) b clk
  cases d with
  | stay =>
    have he' : StackProgram.Exec (clockedCore M) (.inr (q, a))
        (regs4 io (symbols c.tape.left) (symbols (c.tape.right.drop 1)) clk) time result := by
      simpa only [Tape.move, Tape.write, Tape.read, List.headD_cons,
        List.drop_succ_cons, List.drop_zero] using h
    refine ⟨time + 1 + 1, by omega, .next htick (.next ?_ he')⟩
    simp [StackProgram.step, clockedCore, hc]
  | right =>
    have he' : StackProgram.Exec (clockedCore M)
        (.inr (q, (c.tape.right.drop 1).headD .blank))
        (regs4 io (symbols (a :: c.tape.left)) (symbols ((c.tape.right.drop 1).drop 1)) clk)
        time result := by
      simpa only [Tape.move, Tape.write, Tape.read] using h
    have hread := exec_clocked_read_right M q io (symbols (a :: c.tape.left))
      (c.tape.right.drop 1) clk time result he'
    have hp := exec_clocked_move_right M c.state q c.tape.read a hc io c.tape.left
      (c.tape.right.drop 1) clk _ _ hread
    have hcost := TapeToStacks.readCost_le (c.tape.right.drop 1)
    exact ⟨time + readCost (c.tape.right.drop 1) + 2 + 1, by omega, .next htick hp⟩
  | left =>
    have he' : StackProgram.Exec (clockedCore M) (.inr (q, c.tape.left.headD .blank))
        (regs4 io (symbols (c.tape.left.drop 1)) (symbols (a :: c.tape.right.drop 1)) clk)
        time result := by
      rw [Tape.move_left_eq] at h
      simpa only [Tape.write, Tape.read, List.headD_cons,
        List.drop_succ_cons, List.drop_zero] using h
    have hread := exec_clocked_read_left M q io (symbols (a :: c.tape.right.drop 1))
      c.tape.left clk time result he'
    have hp := exec_clocked_move_left M c.state q c.tape.read a hc io c.tape.left
      (c.tape.right.drop 1) clk _ _ hread
    have hcost := TapeToStacks.readCost_le c.tape.left
    exact ⟨time + readCost c.tape.left + 2 + 1, by omega, .next htick hp⟩

/-- What the clocked simulation returns, in terms of the fuelled run of `M`: on an accepting
halt the whole final tape (with the scanned symbol restored), otherwise decision `false` with
the input/output register untouched. -/
def ClockGood (io : List Bool) (o : Option (Bool × Tape))
    (result : Bool × StackMachine.Registers 3) : Prop :=
  match o with
  | some (true, out) => ∃ clk', result =
      (true, regs4 io (symbols out.left) (symbols (out.read :: out.right.drop 1)) clk')
  | _ => result.1 = false ∧ result.2 0 = io

/-- **Totality of the clocked simulation.** Whatever `M` does, the clocked simulation halts
within `5 |clk| + 2` instructions, and its result reflects `run M |clk|`. -/
theorem exec_clockedCore (M : Machine) (io clk : List Bool) (c : Config M) :
    ∃ time result, time ≤ 5 * clk.length + 2 ∧
      StackProgram.Exec (clockedCore M) (.inr (c.state, c.tape.read))
        (regs4 io (symbols c.tape.left) (symbols (c.tape.right.drop 1)) clk) time result ∧
      ClockGood io (run M clk.length c) result := by
  induction clk generalizing c with
  | nil =>
    refine ⟨2, (false, regs4 io (symbols c.tape.left) (symbols (c.tape.right.drop 1)) []),
      by omega, ?_, ?_⟩
    · exact .next (q' := .inl (.done false))
        (r' := regs4 io (symbols c.tape.left) (symbols (c.tape.right.drop 1)) [])
        (by simp [StackProgram.step, clockedCore, StackMachine.branch])
        (.halt (by simp [StackProgram.step, clockedCore]))
    · simp [ClockGood, Complexity.run]
  | cons b clk ih =>
    cases hc : M.code c.state c.tape.read with
    | halt d =>
      have hrun : run M (b :: clk).length c = some (d, c.tape) := by
        simp [Complexity.run, hc]
      refine ⟨3 + 1, (d, regs4 io (symbols c.tape.left)
        (symbols (c.tape.read :: c.tape.right.drop 1)) clk), ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · exact .next (step_clocked_tick M c.state c.tape.read io _ _ b clk)
          (exec_clocked_halt M c.state c.tape.read io (symbols c.tape.left)
            (c.tape.right.drop 1) clk d hc)
      · rw [hrun]
        cases d
        · simp [ClockGood]
        · exact ⟨clk, rfl⟩
    | step a d q =>
      have hrun : run M (b :: clk).length c =
          run M clk.length ⟨q, (c.tape.write a).move d⟩ := by
        simp [Complexity.run, hc]
      obtain ⟨time, result, ht, he, hgood⟩ := ih ⟨q, (c.tape.write a).move d⟩
      obtain ⟨s, hs, hexec⟩ := exec_clocked_step M c a d q hc io b clk time result he
      refine ⟨s, result, ?_, hexec, ?_⟩
      · simp only [List.length_cons]
        omega
      · rw [hrun]
        exact hgood

/-! ### Initialisation, clocked simulation, and output extraction -/

abbrev FinishLabel := Sum Unit TapeToStacks.ExtractLabel

/-- After the clocked simulation: extract the output on decision `true`, and simply return
(successfully) on decision `false`. -/
def finish (b : Bool) : Program 3 FinishLabel where
  start := if b then .inr TapeToStacks.extractor.start else .inl ()
  code := fun label => match label with
    | .inl _ => .halt true
    | .inr a => mapOp Sum.inr Op.halt ((rename tapeMap TapeToStacks.extractor).code a)

abbrev SimLabel (M : Machine) :=
  Sum (Sum (Fin 4) (Fin 6)) (Sum (ClockLabel M) (Bool × FinishLabel))

/-- The complete clocked simulator on registers `io`, `left`, `right`, `clock`. -/
def clockedSim (M : Machine) : Program 3 (SimLabel M) :=
  StackProgram.seq (rename tapeMap TapeToStacks.initializer) (bind (clockedCore M) finish)

def simEncoding (M : Machine) : Encoding (SimLabel M) :=
  Encoding.sum (Encoding.sum (Encoding.fin 3) (Encoding.fin 5))
    (Encoding.sum (clockEncoding M)
      (Encoding.bool.prod (Encoding.unit.sum
        (Encoding.sum Encoding.bool
          (Encoding.sum (Encoding.fin 5) (Encoding.sum Encoding.bool (Encoding.fin 3)))))))

/-- The total function computed by the clocked simulator: the output of `M` on `x` if `M`
halts with decision `true` within `fuel` steps, and the empty word otherwise. -/
def clockedOutput (M : Machine) (fuel : Nat) (x : Word) : Word :=
  match runInput M fuel x with
  | some (true, out) => out.output
  | _ => []

/-- If `M` accepts within the clock, `clockedOutput` is its output. -/
theorem clockedOutput_eq (M : Machine) {fuel time : Nat} (x : Word) (tape : Tape)
    (ht : time ≤ fuel) (hrun : runInput M time x = some (true, tape)) :
    clockedOutput M fuel x = tape.output := by
  have h : runInput M fuel x = some (true, tape) := run_mono M ht (initial M x) (true, tape) hrun
  simp [clockedOutput, h]

/-- The clocked simulator halts successfully on every input and every clock, in time linear
in the input and clock lengths, with `clockedOutput` in register `0`. -/
theorem exec_clockedSim (M : Machine) (x clk : List Bool) :
    ∃ time R', time ≤ 20 * (x.length + clk.length + 2) ∧
      StackProgram.Exec (clockedSim M) (clockedSim M).start (regs4 x [] [] clk) time (true, R') ∧
      R' 0 = clockedOutput M clk.length x := by
  have hinit := exec_rename_tape (TapeToStacks.exec_initializer x) clk
  obtain ⟨time, result, ht, he, hgood⟩ := exec_clockedCore M [] clk (initial M x)
  have hread := exec_clocked_read_right M M.start [] [] (x.map Symbol.bit) clk time result he
  have hcost := TapeToStacks.readCost_le (x.map Symbol.bit)
  have key : ∃ s R', s ≤ 14 * clk.length + 7 * x.length + 16 ∧
      StackProgram.Exec (finish result.1) (finish result.1).start result.2 s (true, R') ∧
      R' 0 = clockedOutput M clk.length x := by
    have hfail : result.1 = false ∧ result.2 0 = [] → clockedOutput M clk.length x = [] →
        ∃ s R', s ≤ 14 * clk.length + 7 * x.length + 16 ∧
          StackProgram.Exec (finish result.1) (finish result.1).start result.2 s (true, R') ∧
          R' 0 = clockedOutput M clk.length x := by
      intro ⟨hb, hio⟩ hout
      rw [hb, hout]
      exact ⟨1, result.2, by omega, .halt rfl, hio⟩
    cases ho : run M clk.length (initial M x) with
    | none =>
      rw [ho] at hgood
      exact hfail hgood (by simp [clockedOutput, runInput, ho])
    | some res =>
      obtain ⟨d, out⟩ := res
      rw [ho] at hgood
      cases d with
      | false => exact hfail hgood (by simp [clockedOutput, runInput, ho])
      | true =>
        obtain ⟨clk', hres⟩ := hgood
        rw [hres]
        have hext := exec_rename_tape
          (TapeToStacks.exec_extractor out.left (out.read :: out.right.drop 1)) clk'
        rw [TapeToStacks.bits_restore_head] at hext
        have hfin := StackProgram.exec_embed (rename tapeMap TapeToStacks.extractor)
          (finish true) Sum.inr (by intro a; rfl) hext
        have hc := TapeToStacks.extractCost_le out.left (out.read :: out.right.drop 1)
        have hlen := TapeToStacks.restore_head_length_le out
        have hsize := run_size_le M clk.length (initial M x) (true, out) ho
        simp only [initial, Tape.size_ofInput] at hsize
        simp only [Tape.size] at hsize
        refine ⟨_, _, ?_, hfin, ?_⟩
        · omega
        · simp [clockedOutput, runInput, ho]
  obtain ⟨s, R', hs, hfin, hout⟩ := key
  have hfull := StackProgram.exec_seq (rename tapeMap TapeToStacks.initializer)
    (bind (clockedCore M) finish) hinit (exec_bind (clockedCore M) finish hread hfin)
  exact ⟨_, R', by omega, hfull, hout⟩

/-! ### Computing the clock, then running the clocked simulator -/

/-- Registers: `0` the input, `1` the clock, `2` scratch. -/
def prepCmd (g : Word → Word) (t : Nat → Nat) : Cmd 2 :=
  .seq (copy 0 1 2) (.call g t 1)

theorem exec_prepCmd (g : Word → Word) (t : Nat → Nat) (x : Word) :
    Exec (prepCmd g t) (init x) (9 * x.length + 2 + (t x.length + x.length + 1))
      (ofList [x, g x]) := by
  rw [init_eq_ofList]
  have h1 : Exec (copy 0 1 2) (ofList [x] : Regs 2) (9 * x.length + 2) (ofList [x, x]) :=
    (exec_copy 0 1 2 (by decide) (by decide) (by decide) _ (by regs)).cast (by regs) (by regs)
  have h2 : Exec (.call g t 1) (ofList [x, x] : Regs 2) (t x.length + x.length + 1)
      (ofList [x, g x]) := Exec.call' (by regs) (by regs)
  exact .seq h1 h2

/-- Placement of the simulator's registers among the five registers of the compiled
`prepCmd`: input/output `0`, tape halves in the work registers `3`, `4`, clock `1`. -/
def simMap (i : Fin 4) : Fin 5 :=
  if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 4 else 1

theorem simMap_injective : ∀ i j, simMap i = simMap j → i = j := by
  intro i j
  rcases fin_four_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin_four_cases j with rfl | rfl | rfl | rfl <;> decide

theorem pull_simMap_lift (x w : Word) :
    pull simMap (lift (ofList [x, w] : Regs 2)) = regs4 x [] [] w := by
  funext i
  rcases fin_four_cases i with rfl | rfl | rfl | rfl <;> rfl

/-- **Clocked simulation.** For a tape machine `M` and a polynomial clock, there is a total
polynomial-time function that returns the output of `M` whenever `M` halts with decision
`true` within the clock. -/
theorem exists_polyTime_clocked (M : Machine) (c e : Nat) :
    ∃ F : Word → Word, PolyTime F ∧
      ∀ (x : Word) (time : Nat) (tape : Tape), time ≤ powerBound c e x.length →
        runInput M time x = some (true, tape) → F x = tape.output := by
  obtain ⟨g, hg, hlen⟩ := exists_polyTime_clock c e
  obtain ⟨cg, eg, hgt⟩ := TimeBounded.of_polyTime hg
  obtain ⟨L, p, enc, C, hp⟩ :=
    exists_program (prepCmd g (powerBound cg eg)) ⟨sound_copy 0 1 2, hgt⟩
  refine ⟨fun x => clockedOutput M (powerBound c e x.length) x, ?_,
    fun x time tape ht hrun => clockedOutput_eq M x tape ht hrun⟩
  apply StackCompile.polyTime_of_stack
    (StackProgram.compile (StackProgram.seq p (rename simMap (clockedSim M)))
      (enc.sum (simEncoding M)))
    (fun n => C * (9 * n + 2 + (powerBound cg eg n + n + 1)) + 20 * (n + powerBound c e n + 2))
    (((PolynomialBound.constant C).mul
      ((((PolynomialBound.constant 9).mul PolynomialBound.identity).add
        (PolynomialBound.constant 2)).add
        (((PolynomialBound.power cg eg).add PolynomialBound.identity).add
          (PolynomialBound.constant 1)))).add
      ((PolynomialBound.constant 20).mul
        ((PolynomialBound.identity.add (PolynomialBound.power c e)).add
          (PolynomialBound.constant 2))))
  intro x
  obtain ⟨t1, ht1, he1⟩ := hp _ _ _ (exec_prepCmd g (powerBound cg eg) x)
  obtain ⟨t2, R', ht2, he2, hout⟩ := exec_clockedSim M x (g x)
  obtain ⟨R'', he3, hpull, -⟩ := exec_rename simMap simMap_injective he2
    (lift (ofList [x, g x])) (pull_simMap_lift x (g x))
  have hrun := StackProgram.compile_exec (enc.sum (simEncoding M))
    (StackProgram.exec_seq p (rename simMap (clockedSim M)) he1 he3)
  rw [lift_init] at hrun
  rw [hlen] at ht2 hout
  refine ⟨t1 + t2, R'', by omega, hrun, ?_⟩
  have h0 : R'' 0 = R' 0 := congrFun hpull 0
  exact h0.trans hout

/-- The same for a Boolean-stack machine, in relational form: a total polynomial-time function
that returns register `0` of every accepting run of `S` within the polynomial bound. -/
theorem exists_polyTime_of_stack_run (S : StackMachine.Machine) (bound : Nat → Nat)
    (hb : PolynomialBound bound) :
    ∃ F : Word → Word, PolyTime F ∧
      ∀ (w : Word) (time : Nat) (registers : StackMachine.Registers S.stacks),
        time ≤ bound w.length →
        StackMachine.runInput S time w = some (true, registers) → F w = registers 0 := by
  obtain ⟨c, e, hce⟩ := StackCompile.polynomialBound_budget S bound hb
  obtain ⟨F, hF, hagree⟩ := exists_polyTime_clocked (StackCompile.compile S) c e
  refine ⟨F, hF, ?_⟩
  intro w time registers ht hrun
  obtain ⟨τ, tape, hτ, hrun', hout⟩ := StackCompile.simulate S time w (true, registers) hrun
  rw [hagree w τ tape
    (Nat.le_trans hτ (Nat.le_trans (StackCompile.budget_mono S w.length ht) (hce w.length)))
    hrun']
  exact hout

/-- Same for a Boolean-stack machine with a polynomial bound on a domain. -/
theorem exists_polyTime_of_stack_on (S : StackMachine.Machine) (bound : Nat → Nat)
    (hb : PolynomialBound bound) (D : Word → Prop) (g : Word → Word)
    (hS : ∀ w, D w → ∃ time registers, time ≤ bound w.length ∧
      StackMachine.runInput S time w = some (true, registers) ∧ registers 0 = g w) :
    ∃ F : Word → Word, PolyTime F ∧ ∀ w, D w → F w = g w := by
  obtain ⟨F, hF, hagree⟩ := exists_polyTime_of_stack_run S bound hb
  refine ⟨F, hF, ?_⟩
  intro w hw
  obtain ⟨time, registers, ht, hrun, hout⟩ := hS w hw
  exact (hagree w time registers ht hrun).trans hout

end Complexity.Reg
