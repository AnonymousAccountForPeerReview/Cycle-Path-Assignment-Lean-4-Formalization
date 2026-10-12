module

public import ApproximationHardness.Sim.Simulate
import Lean.Elab.Tactic.Omega

/-!
# Polynomial-time RAM programs are polynomial-time in the registered model

`xram_polyTime`: for every program `s` of the RAM with bit input and output (with registers below
`192` and loops nested at most `16` deep) and every polynomial time bound `c₀ (n + 1) ^ d₀`, there
is a word function `g`, computed in polynomial time by a single-tape machine of the registered
foundation `NPCompleteness-Lean4` (`Complexity.PolyTime`), such that `g w` is the output of `s`
on `w` whenever `s` halts on `w` within `c₀ (|w| + 1) ^ d₀` steps.

The machine computes the fuel `F = c₀ (|w| + 1) ^ d₀` in unary, runs `sim 0 s` (every loop for
at most `F` iterations) and moves the output to the output register.
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)

/-! ### Bookkeeping of the fuel semantics -/

theorem xrun_inp_length (F : Nat) : ∀ (s : XStmt) (c : XConfig), (xrun F s c).inp.length ≤ c.inp.length := by
  intro s
  induction s with
  | seq s t ihs iht => intro c; simp only [xrun]; exact Nat.le_trans (iht _) (ihs c)
  | ifz a s t ihs iht => intro c; simp only [xrun]; split; exact ihs c; exact iht c
  | loop a body ih =>
    intro c
    simp only [xrun]
    suffices h : ∀ n c, (iter (fun c => if c.reg a = 0 then c else xrun F body c) n c).inp.length ≤ c.inp.length from
      h F c
    intro n
    induction n with
    | zero => intro c; exact Nat.le_refl _
    | succ n ihn =>
      intro c
      simp only [iter]
      refine Nat.le_trans (ihn _) ?_
      split
      · exact Nat.le_refl _
      · exact ih c
  | getBit d => intro c; simp [xrun, XConfig.getBit]
  | _ => intro c; simp [xrun, XConfig.setReg, XConfig.setMem, XConfig.emit]

theorem xrun_out_length (F : Nat) : ∀ (s : XStmt) (c : XConfig),
    (xrun F s c).out.length ≤ c.out.length + icount F s := by
  intro s
  induction s with
  | seq s t ihs iht =>
    intro c; simp only [xrun, icount]; have := iht (xrun F s c); have := ihs c; omega
  | ifz a s t ihs iht =>
    intro c; simp only [xrun, icount]; split
    · have := ihs c; omega
    · have := iht c; omega
  | loop a body ih =>
    intro c
    simp only [xrun, icount]
    suffices h : ∀ n c, (iter (fun c => if c.reg a = 0 then c else xrun F body c) n c).out.length ≤
        c.out.length + n * icount F body by
      have h1 := h F c
      have h2 : F * icount F body ≤ F * (icount F body + 1) :=
        Nat.mul_le_mul_left _ (show icount F body ≤ icount F body + 1 by omega)
      omega
    intro n
    induction n with
    | zero => intro c; simp [iter]
    | succ n ihn =>
      intro c
      simp only [iter]
      refine Nat.le_trans (ihn _) ?_
      rw [Nat.succ_mul]
      split
      · omega
      · have := ih c; omega
  | emit a => intro c; simp [xrun, XConfig.emit, icount]
  | getBit d => intro c; simp [xrun, XConfig.getBit, icount]
  | _ => intro c; simp [xrun, XConfig.setReg, XConfig.setMem, icount]

/-! ### Computing the fuel -/

/-- Raise the fuel to the power `k` of `|XA|`. -/
def initPow : Nat → Command K
  | 0 => skipC
  | k + 1 => .seq (initPow k) (.seq (.multiply FUEL XA XB XC XU) (.seq (.copy XB FUEL XU) (.clear XB)))

/-- `FUEL := c₀ (|INP| + 1) ^ d₀` ones. -/
def initC (c₀ d₀ : Nat) : Command K :=
  .seq (.length INP XA XU) (.seq (.push XA true) (.seq (.push FUEL true) (.seq (initPow d₀)
    (.seq (pushList XZ (List.replicate c₀ true)) (.seq (.multiply FUEL XZ XB XC XU) (.seq (.copy XB FUEL XU)
      (.seq (.clear XB) (.seq (.clear XZ) (.clear XA)))))))))

/-- The registers at the start of the run on the input `w`. -/
def initRegs (w : List Bool) : Regs := fun j => if j = 0 then w else []

theorem ok_multiply {src factor dst counter scratch : Reg}
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ scratch)
    (hfc : factor ≠ counter) (hft : factor ≠ scratch) (hfd : factor ≠ dst) (r : Regs) (m : Nat)
    (hs : r scratch = []) (hm : r factor = List.replicate m true) :
    Ok (.multiply src factor dst counter scratch) r (set (set r counter []) dst (List.replicate (m * (r src).length) true))
      ((r dst).length + (r counter).length + 5 * m + m * (5 * (r src).length + 5) + 10) :=
  ⟨_, Exec.multiply hsd hst hdt hcs hcd hct hfc hft hfd hs hm, Nat.le_refl _⟩

/-- The state during the powers: everything empty but the input, `XA` and the fuel. -/
def PowAt (w : List Bool) (k : Nat) (q : Regs) : Prop :=
  q INP = w ∧ q XA = List.replicate (w.length + 1) true ∧ q FUEL = List.replicate ((w.length + 1) ^ k) true ∧
    ∀ i : Reg, i ≠ INP → i ≠ XA → i ≠ FUEL → q i = []

theorem ok_initPow (w : List Bool) : ∀ (k : Nat) (q : Regs), PowAt w 0 q →
    ∃ q', Ok (initPow k) q q' (1 + k * (40 * (w.length + 2) ^ (k + 1))) ∧ PowAt w k q' := by
  intro k
  induction k with
  | zero => intro q h; exact ⟨q, (ok_skip q).mono (by omega), h⟩
  | succ k ih =>
    intro q h
    obtain ⟨q1, s1, h1⟩ := ih q h
    obtain ⟨i1, a1, f1, e1⟩ := h1
    generalize hN : w.length = N at *
    generalize hP : (N + 1) ^ k = P at *
    have hpow : (N + 1) * P = (N + 1) ^ (k + 1) := by rw [← hP, Nat.pow_succ, Nat.mul_comm]
    generalize hP' : (N + 1) ^ (k + 1) = P' at hpow
    have s2 := ok_multiply (src := FUEL) (factor := XA) (dst := XB) (counter := XC) (scratch := XU)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      q1 (N + 1) (e1 XU (by decide) (by decide) (by decide)) a1
    rw [e1 XB (by decide) (by decide) (by decide), e1 XC (by decide) (by decide) (by decide), f1,
      List.length_replicate, hpow] at s2
    generalize hq2 : set (set q1 XC []) XB (List.replicate P' true) = q2 at s2
    have q2B : q2 XB = List.replicate P' true := by rw [← hq2]; simp
    have q2F : q2 FUEL = List.replicate P true := by rw [← hq2]; simp [f1]
    have s3 := ok_copy (s := XB) (d := FUEL) (t := XU) (by decide) (by decide) (by decide) q2
      (by rw [← hq2]; simp [e1 XU (by decide) (by decide) (by decide)])
    rw [q2B, q2F, List.length_replicate, List.length_replicate] at s3
    have s4 := ok_clear XB (set q2 FUEL (List.replicate P' true))
    have l4 : (set q2 FUEL (List.replicate P' true) XB).length = P' := by simp [q2B]
    rw [l4] at s4
    have hX : (N + 2) ^ (k + 1) ≤ (N + 2) ^ (k + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hPX : P ≤ (N + 2) ^ (k + 1 + 1) := by
      rw [← hP]
      calc (N + 1) ^ k ≤ (N + 2) ^ k := Nat.pow_le_pow_left (by omega) k
        _ ≤ (N + 2) ^ (k + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hP'X : P' ≤ (N + 2) ^ (k + 1 + 1) := by
      rw [← hP']
      calc (N + 1) ^ (k + 1) ≤ (N + 2) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
        _ ≤ (N + 2) ^ (k + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hNX : N + 2 ≤ (N + 2) ^ (k + 1 + 1) := by
      calc N + 2 = (N + 2) ^ 1 := (Nat.pow_one _).symm
        _ ≤ (N + 2) ^ (k + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hm : (N + 1) * (5 * P + 5) = 5 * P' + 5 * (N + 1) := by
      rw [Nat.mul_add, Nat.mul_left_comm, hpow, Nat.mul_comm (N + 1) 5]
    refine ⟨_, (s1.seq (s2.seq (s3.seq s4))).mono ?_, ?_⟩
    · rw [hm]
      have : k * (40 * (N + 2) ^ (k + 1)) ≤ k * (40 * (N + 2) ^ (k + 1 + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.add_mul, Nat.one_mul]
      simp only [List.length_nil]
      omega
    · refine ⟨by simp [← hq2, i1], by simp [← hq2, a1, hN], ?_, ?_⟩
      · simp [← hP', hN]
      · intro i h1 h2 h3
        by_cases hb : i = XB
        · subst hb; simp
        · rw [set_apply, ite_eq_right hb, set_apply, ite_eq_right h3, ← hq2, set_apply, ite_eq_right hb, set_apply]
          split
          · rfl
          · exact e1 i h1 h2 h3

/-- The cost bound of `initC`. -/
def initBound (c₀ d₀ n : Nat) : Nat :=
  40 * (d₀ * (n + 2) ^ (d₀ + 1)) + 40 * (c₀ * (n + 2) ^ (d₀ + 1)) + 60 * (n + 2) ^ (d₀ + 1)

theorem ok_initC (c₀ d₀ : Nat) (w : List Bool) :
    ∃ q', Ok (initC c₀ d₀) (initRegs w) q' (initBound c₀ d₀ w.length) ∧ q' INP = w ∧
      q' FUEL = List.replicate (c₀ * (w.length + 1) ^ d₀) true ∧ ∀ i : Reg, i ≠ INP → i ≠ FUEL → q' i = [] := by
  have hI : ∀ i : Reg, i ≠ INP → initRegs w i = [] := fun i hi => by simp [initRegs, hi]
  have hI0 : initRegs w INP = w := by simp [initRegs]
  have s1 := ok_length (s := INP) (d := XA) (t := XU) (by decide) (by decide) (by decide) (initRegs w)
    (hI XU (by decide))
  rw [hI XA (by decide), hI0] at s1
  have s2 := ok_push XA true (set (initRegs w) XA (List.replicate w.length true))
  have s3 := ok_push FUEL true (set (set (initRegs w) XA (List.replicate w.length true)) XA
    (true :: (set (initRegs w) XA (List.replicate w.length true)) XA))
  generalize hq3 : set (set (set (initRegs w) XA (List.replicate w.length true)) XA
    (true :: (set (initRegs w) XA (List.replicate w.length true)) XA)) FUEL
    (true :: (set (set (initRegs w) XA (List.replicate w.length true)) XA
    (true :: (set (initRegs w) XA (List.replicate w.length true)) XA)) FUEL) = q3 at s3
  have hp : PowAt w 0 q3 := by
    rw [← hq3]
    refine ⟨by simp [hI0], ?_, ?_, ?_⟩
    · simp [List.replicate_succ]
    · simp [hI FUEL (by decide)]
    · intro i h1 h2 h3; simp [h2, h3, hI i h1]
  obtain ⟨q4, s4, i4, a4, f4, e4⟩ := ok_initPow w d₀ q3 hp
  generalize hN : w.length = N at *
  generalize hP : (N + 1) ^ d₀ = P at *
  have s5 := ok_pushList XZ (List.replicate c₀ true) q4
  rw [e4 XZ (by decide) (by decide) (by decide), List.append_nil, List.length_replicate] at s5
  have s6 := ok_multiply (src := FUEL) (factor := XZ) (dst := XB) (counter := XC) (scratch := XU)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (set q4 XZ (List.replicate c₀ true)) c₀ (by simp [e4 XU (by decide) (by decide) (by decide)])
    (by simp [])
  have l6 : ((set q4 XZ (List.replicate c₀ true)) XB).length = 0 ∧ ((set q4 XZ (List.replicate c₀ true)) XC).length = 0 ∧
      ((set q4 XZ (List.replicate c₀ true)) FUEL).length = P := by
    simp [e4 XB (by decide) (by decide) (by decide), e4 XC (by decide) (by decide) (by decide), f4]
  rw [l6.1, l6.2.1, l6.2.2] at s6
  generalize hq6 : set (set (set q4 XZ (List.replicate c₀ true)) XC []) XB (List.replicate (c₀ * P) true) = q6 at s6
  have q6B : q6 XB = List.replicate (c₀ * P) true := by rw [← hq6]; simp
  have q6F : q6 FUEL = List.replicate P true := by rw [← hq6]; simp [f4]
  have q6Z : q6 XZ = List.replicate c₀ true := by rw [← hq6]; simp []
  have q6A : q6 XA = List.replicate (N + 1) true := by rw [← hq6]; simp [a4]
  have q6I : q6 INP = w := by rw [← hq6]; simp [i4]
  have q6e : ∀ i : Reg, i ≠ INP → i ≠ XA → i ≠ FUEL → i ≠ XB → i ≠ XZ → q6 i = [] := by
    intro i h1 h2 h3 h4 h5; rw [← hq6]; simp [set_apply, h4, h5]; intro _; exact e4 i h1 h2 h3
  have s7 := ok_copy (s := XB) (d := FUEL) (t := XU) (by decide) (by decide) (by decide) q6
    (q6e XU (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [q6F, q6B, List.length_replicate, List.length_replicate] at s7
  have s8 := ok_clear XB (set q6 FUEL (List.replicate (c₀ * P) true))
  have s9 := ok_clear XZ (set (set q6 FUEL (List.replicate (c₀ * P) true)) XB [])
  have s10 := ok_clear XA (set (set (set q6 FUEL (List.replicate (c₀ * P) true)) XB []) XZ [])
  have l8 : (set q6 FUEL (List.replicate (c₀ * P) true) XB).length = c₀ * P := by simp [q6B]
  have l9 : (set (set q6 FUEL (List.replicate (c₀ * P) true)) XB [] XZ).length = c₀ := by simp [q6Z]
  have l10 : (set (set (set q6 FUEL (List.replicate (c₀ * P) true)) XB []) XZ [] XA).length = N + 1 := by
    simp [q6A]
  rw [l8] at s8; rw [l9] at s9; rw [l10] at s10
  refine ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq s10))))))))).mono ?_, ?_, ?_, ?_⟩
  · unfold initBound
    generalize hX : (N + 2) ^ (d₀ + 1) = X at *
    have hX1 : N + 2 ≤ X := by
      rw [← hX]
      calc N + 2 = (N + 2) ^ 1 := (Nat.pow_one _).symm
        _ ≤ (N + 2) ^ (d₀ + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hPX : P ≤ X := by
      rw [← hX, ← hP]
      calc (N + 1) ^ d₀ ≤ (N + 2) ^ d₀ := Nat.pow_le_pow_left (by omega) d₀
        _ ≤ (N + 2) ^ (d₀ + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hcP : c₀ * P ≤ c₀ * X := Nat.mul_le_mul_left _ hPX
    have hc : c₀ ≤ c₀ * X := Nat.le_mul_of_pos_right _ (by omega)
    have hm : c₀ * (5 * P + 5) = 5 * (c₀ * P) + 5 * c₀ := by
      rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm c₀ 5]
    rw [hm, Nat.mul_left_comm d₀ 40 X]
    simp only [List.length_nil]
    omega
  · simp [q6I]
  · simp [← hP]
  · intro i h1 h2
    by_cases hA : i = XA; · subst hA; simp
    by_cases hZ : i = XZ; · subst hZ; simp []
    by_cases hB : i = XB; · subst hB; simp []
    simp only [set_apply, hA, hZ, hB, h2, ite_false]
    exact q6e i h1 hA h2 hB hZ

/-! ### The whole run -/

/-- Move the output to the output register `0`. -/
def finishC : Command K := .seq (.clear INP) (revOnto OUTB INP XT)

/-- The program: compute the fuel, simulate, move the output. -/
def progC (s : XStmt) (c₀ d₀ : Nat) : Command K := .seq (initC c₀ d₀) (.seq (sim 0 s) finishC)

/-- The fuel on inputs of length `n`. -/
def fuel (c₀ d₀ n : Nat) : Nat := c₀ * (n + 1) ^ d₀

/-- The bound on the instructions of `progC s c₀ d₀` on inputs of length `n`. -/
def totalBound (s : XStmt) (c₀ d₀ n : Nat) : Nat :=
  initBound c₀ d₀ n + icount (fuel c₀ d₀ n) s * per (constBits s + 2 + icount (fuel c₀ d₀ n) s)
    (icount (fuel c₀ d₀ n) s) (fuel c₀ d₀ n) + (n + 11 * icount (fuel c₀ d₀ n) s + 12)

theorem ok_progC (s : XStmt) (hR : RegsOK s) (hD : depth s ≤ 16) (c₀ d₀ : Nat) (w : List Bool) :
    ∃ q', Ok (progC s c₀ d₀) (initRegs w) q' (totalBound s c₀ d₀ w.length) ∧
      q' INP = (xrun (fuel c₀ d₀ w.length) s (xinit w)).out := by
  obtain ⟨q1, s1, i1, f1, e1⟩ := ok_initC c₀ d₀ w
  unfold totalBound
  generalize hF : fuel c₀ d₀ w.length = F
  have f1' : q1 FUEL = List.replicate F true := by rw [f1, ← hF]; rfl
  have hrep : Rep F (xinit w) q1 0 (constBits s + 2) 0 := by
    refine ⟨fun i h1 h2 => e1 i (fun e => by subst e; exact absurd h1 (by decide))
      (fun e => by subst e; exact absurd h1 (by decide)), i1,
      e1 OUTB (by decide) (by decide), f1', fun i _ => ?_, ⟨[], e1 MEM (by decide) (by decide), Nat.le_refl _,
      fun e he => by simp at he, fun a => rfl⟩, fun j _ hj => e1 _ (ctr_ne hj INP) (ctr_ne hj FUEL)⟩
    exact ⟨e1 _ (rr_ne i INP) (rr_ne i FUEL), by simp [xinit]⟩
  obtain ⟨q2, s2, h2, -⟩ := sim_correct F s 0 (xinit w) q1 (constBits s + 2) 0 hR (by omega) (by omega) (by omega) hrep
  obtain ⟨c2, ⟨I2, O2, -⟩, -⟩ : Clean q2 ∧ (q2 INP = (xrun F s (xinit w)).inp ∧ q2 OUTB = (xrun F s (xinit w)).out.reverse ∧ True) ∧ True :=
    ⟨h2.1, ⟨h2.2.1, h2.2.2.1, trivial⟩, trivial⟩
  have s3 := ok_clear INP q2
  obtain ⟨q4, s4, o4, i4, t4, -⟩ := ok_revOnto (src := OUTB) (dst := INP) (ct := XT) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (set q2 INP []) (by simp [c2.at XU])
  have hin : (xrun F s (xinit w)).inp.length ≤ w.length := xrun_inp_length F s (xinit w)
  have hout : (xrun F s (xinit w)).out.length ≤ icount F s := by
    have := xrun_out_length F s (xinit w); simpa [xinit] using this
  refine ⟨q4, (s1.seq (s2.seq (s3.seq s4))).mono ?_, ?_⟩
  · simp only [set_apply, ite_eq_right (show XT ≠ INP by decide), ite_eq_right (show OUTB ≠ INP by decide), c2.at XT, O2, I2,
      List.length_nil, List.length_reverse, Nat.zero_add]
    omega
  · rw [i4]; simp [O2]

/-- The finite stack machine of the program (the registered foundation's compiler). -/
def simMachine (s : XStmt) (c₀ d₀ : Nat) : StackMachine.Machine := StackTableauProgram.machine (progC s c₀ d₀)

/-- The word function computed by the machine. -/
def simFun (s : XStmt) (c₀ d₀ : Nat) (w : List Bool) : List Bool :=
  match StackMachine.runInput (simMachine s c₀ d₀) (totalBound s c₀ d₀ w.length) w with
  | some (_, r) => r 0
  | none => []

theorem simMachine_run (s : XStmt) (hR : RegsOK s) (hD : depth s ≤ 16) (c₀ d₀ : Nat) (w : List Bool) :
    ∃ r, StackMachine.runInput (simMachine s c₀ d₀) (totalBound s c₀ d₀ w.length) w = some (true, r) ∧
      r 0 = (xrun (fuel c₀ d₀ w.length) s (xinit w)).out := by
  obtain ⟨q', ⟨t, he, ht⟩, hq⟩ := ok_progC s hR hD c₀ d₀ w
  refine ⟨q', ?_, hq⟩
  have hrun := he.machine_run
  obtain ⟨extra, hextra⟩ : ∃ extra, totalBound s c₀ d₀ w.length = t + extra := ⟨_, (Nat.add_sub_cancel' ht).symm⟩
  rw [StackMachine.runInput, hextra]
  exact StackMachine.run_add _ _ _ _ _ hrun

theorem simFun_eq (s : XStmt) (hR : RegsOK s) (hD : depth s ≤ 16) (c₀ d₀ : Nat) (w : List Bool) :
    simFun s c₀ d₀ w = (xrun (fuel c₀ d₀ w.length) s (xinit w)).out := by
  obtain ⟨r, hr, h0⟩ := simMachine_run s hR hD c₀ d₀ w
  simp only [simFun, hr]; exact h0

/-! ### The polynomial bound -/

section Polynomial

open PolynomialBound

theorem pb_icount {G : Nat → Nat} (hG : PolynomialBound G) : ∀ s : XStmt, PolynomialBound (fun n => icount (G n) s) := by
  intro s
  induction s with
  | seq s t ihs iht => exact ihs.add iht
  | ifz a s t ihs iht => exact (ihs.add iht).add (constant 1)
  | loop a body ih => exact (hG.mul (ih.add (constant 1))).add (constant 1)
  | _ => exact constant 1

theorem pb_shift (k : Nat) : PolynomialBound (fun n => n + k) := identity.add (constant k)

theorem pb_fuel (c₀ d₀ : Nat) : PolynomialBound (fuel c₀ d₀) :=
  (constant c₀).mul ((pb_shift 1).pow d₀)

theorem pb_initBound (c₀ d₀ : Nat) : PolynomialBound (initBound c₀ d₀) := by
  have hX := (pb_shift 2).pow (d₀ + 1)
  exact (((constant 40).mul ((constant d₀).mul hX)).add ((constant 40).mul ((constant c₀).mul hX))).add
    ((constant 60).mul hX)

theorem pb_per {B E F : Nat → Nat} (hB : PolynomialBound B) (hE : PolynomialBound E) (hF : PolynomialBound F) :
    PolynomialBound (fun n => per (B n) (E n) (F n)) := by
  unfold per
  exact (((((hE.mul (((constant 4).mul hB).add (constant 4))).add (constant 1)).mul
    (((constant 24).mul hB).add (constant 60))).add ((constant 200).mul (hB.add (constant 1)))).add
    ((constant 10).mul hF)).add (constant 20)

theorem pb_totalBound (s : XStmt) (c₀ d₀ : Nat) : PolynomialBound (totalBound s c₀ d₀) := by
  have hI := pb_icount (pb_fuel c₀ d₀) s
  unfold totalBound
  exact ((pb_initBound c₀ d₀).add (hI.mul (pb_per ((constant (constBits s + 2)).add hI) hI (pb_fuel c₀ d₀)))).add
    ((identity.add ((constant 11).mul hI)).add (constant 12))

end Polynomial

theorem simMachine_computes (s : XStmt) (hR : RegsOK s) (hD : depth s ≤ 16) (c₀ d₀ : Nat) (w : List Bool) :
    ∃ time registers, time ≤ totalBound s c₀ d₀ w.length ∧
      StackMachine.runInput (simMachine s c₀ d₀) time w = some (true, registers) ∧ registers 0 = simFun s c₀ d₀ w := by
  obtain ⟨r, hr, -⟩ := simMachine_run s hR hD c₀ d₀ w
  exact ⟨_, r, Nat.le_refl _, hr, by simp only [simFun, hr]⟩

/-- **Polynomial-time RAM programs give registered polynomial-time word functions.** For every program
`s` of the RAM with bit input and output whose registers are below `192` and whose loops are nested
at most `16` deep, and for all `c₀, d₀`, there is a word function `g` computed in polynomial time by
a single-tape machine of the registered foundation (`Complexity.PolyTime`) such that `g w` is the
output of `s` on `w` whenever `s` halts on `w` within `c₀ (|w| + 1) ^ d₀` steps. -/
theorem xram_polyTime (s : XStmt) (hR : RegsOK s) (hD : depth s ≤ 16) (c₀ d₀ : Nat) :
    ∃ g : List Bool → List Bool, PolyTime g ∧
      ∀ w t c', XExec s (xinit w) t c' → t ≤ c₀ * (w.length + 1) ^ d₀ → g w = c'.out := by
  refine ⟨simFun s c₀ d₀, StackCompile.polyTime_of_stack (simMachine s c₀ d₀) (totalBound s c₀ d₀)
    (pb_totalBound s c₀ d₀) (simMachine_computes s hR hD c₀ d₀), ?_⟩
  intro w t c' he ht
  rw [simFun_eq s hR hD c₀ d₀ w, (xrun_of_exec he).1 (by unfold fuel; exact ht)]

end STACS2027.Sim
