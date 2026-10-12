module

public import ApproximationHardness.Sim.Basic
public import ApproximationHardness.Sim.Bits
import Lean.Elab.Tactic.Omega

/-!
# Binary arithmetic on stack registers

Numbers are held in stack registers as canonical binary numerals, least significant bit on top
(`bin`). This file gives commands for moving and reversing registers, and for the sum and the
truncated difference of two numerals, with their runs (`ok_addB`, `ok_subB`).
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame)

/-! ### Moving bits -/

/-- Move the top bit of `src` to `dst`. -/
def move (src dst : Reg) : Command K :=
  .branch src skipC (.seq (.pop src) (.push dst false)) (.seq (.pop src) (.push dst true))

/-- `move` on the contents of `src` and `dst`. -/
def moveStep : List Bool × List Bool → List Bool × List Bool
  | ([], d) => ([], d)
  | (b :: s, d) => (s, b :: d)

theorem ok_move {src dst : Reg} (h : src ≠ dst) (r : Regs) :
    ∃ r', Ok (move src dst) r r' 5 ∧ (r' src, r' dst) = moveStep (r src, r dst) ∧
      ∀ i, i ≠ src → i ≠ dst → r' i = r i := by
  apply ok_of_evalP 0
  cases hs : r src with
  | nil => simp [eval, move, skipC, hs, moveStep]
  | cons b s =>
    cases b <;> simp [eval, move, skipC, hs, moveStep, set_apply, h, Ne.symm h] <;> intro i h1 h2 <;> simp [h1, h2]

theorem iter_moveStep : ∀ (a d : List Bool) (n : Nat), a.length ≤ n → iter moveStep n (a, d) = ([], a.reverse ++ d) := by
  intro a
  induction a with
  | nil =>
    intro d n _
    induction n with
    | zero => rfl
    | succ n ih => simp only [iter, moveStep]; exact ih (by simp)
  | cons b a ih =>
    intro d n hn
    cases n with
    | zero => simp at hn
    | succ n => simp only [iter, moveStep]; rw [ih (b :: d) n (by simp at hn; omega)]; simp

/-- Reverse `src` onto `dst`, counting with `ct`. -/
def revOnto (src dst ct : Reg) : Command K := .seq (.length src ct XU) (.repeat ct (move src dst))

theorem ok_revOnto {src dst ct : Reg} (h1 : src ≠ dst) (h2 : src ≠ ct) (h3 : dst ≠ ct) (h4 : src ≠ XU)
    (_h5 : dst ≠ XU) (h6 : ct ≠ XU) (r : Regs) (hU : r XU = []) :
    ∃ r', Ok (revOnto src dst ct) r r' ((r ct).length + 11 * (r src).length + 8) ∧
      r' src = [] ∧ r' dst = (r src).reverse ++ r dst ∧ r' ct = [] ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ ct → r' i = r i := by
  have hlen : Ok (.length src ct XU) r (set r ct (List.replicate (r src).length true))
      ((r ct).length + 5 * (r src).length + 6) := ⟨_, Exec.length h2 h4 h6 hU, Nat.le_refl _⟩
  generalize hr1 : set r ct (List.replicate (r src).length true) = r1 at hlen
  have r1s : r1 src = r src := by rw [← hr1]; simp [h2]
  have r1d : r1 dst = r dst := by rw [← hr1]; simp [h3]
  have r1c : (r1 ct).length = (r src).length := by rw [← hr1]; simp
  have r1f : ∀ i, i ≠ ct → r1 i = r i := by intro i hi; rw [← hr1]; simp [hi]
  have hw : writes (move src dst) ct = false := by simp [move, skipC, writes, Ne.symm h2, Ne.symm h3]
  obtain ⟨r2, hok, hE, hct⟩ := ok_repeat hw (fun (s : List Bool × List Bool) (q : Regs) =>
      q src = s.1 ∧ q dst = s.2 ∧ ∀ i, i ≠ src → i ≠ dst → i ≠ ct → q i = r1 i) moveStep 5
    (by
      intro s q w ⟨a, b, c⟩
      refine ⟨by simp [h2, a], by simp [h3, b], fun i i1 i2 i3 => by simp [i3, c i i1 i2 i3]⟩)
    (by
      intro ⟨s1, s2⟩ q ⟨a, b, c⟩
      obtain ⟨q', hq, hst, hfr⟩ := ok_move h1 q
      rw [a, b] at hst
      refine ⟨q', hq, ?_, ?_, fun i i1 i2 i3 => by rw [hfr i i1 i2, c i i1 i2 i3]⟩
      · exact (congrArg Prod.fst hst)
      · exact (congrArg Prod.snd hst))
    ((r src).length) (r src, r dst) r1 ⟨r1s, r1d, fun _ _ _ _ => rfl⟩ r1c
  rw [iter_moveStep _ _ _ (Nat.le_refl _)] at hE
  obtain ⟨e1, e2, e3⟩ := hE
  refine ⟨r2, (hlen.seq hok).mono ?_, e1, e2, hct, fun i i1 i2 i3 => by rw [e3 i i1 i2 i3, r1f i i3]⟩
  omega

/-! ### Dropping leading zeros of a most-significant-first numeral -/

def strip : Command K := .branch XZ skipC (.pop XZ) skipC

def stripStep : List Bool → List Bool
  | false :: z => z
  | z => z

theorem iter_stripStep : ∀ (z : List Bool) (n : Nat), z.length ≤ n → iter stripStep n z = z.dropWhile (· == false) := by
  intro z n
  induction n generalizing z with
  | zero => intro h; have : z = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst this; rfl
  | succ n ih =>
    intro h
    cases z with
    | nil => simp only [iter, stripStep]; exact ih [] (by simp)
    | cons b z =>
      cases b with
      | false => simp only [iter, stripStep]; rw [ih z (by simp at h; omega)]; simp
      | true =>
        simp only [iter, stripStep]
        have : ∀ m, iter stripStep m (true :: z) = true :: z := by
          intro m; induction m with
          | zero => rfl
          | succ m ihm => simp only [iter, stripStep]; exact ihm
        rw [this]; simp

theorem ok_strip (r : Regs) :
    ∃ r', Ok strip r r' 3 ∧ r' XZ = stripStep (r XZ) ∧ ∀ i, i ≠ XZ → r' i = r i := by
  apply ok_of_evalP 0
  cases hs : r XZ with
  | nil => simp [eval, strip, skipC, hs, stripStep]
  | cons b s => cases b <;> simp [eval, strip, skipC, hs, stripStep, set_apply] <;> intro i h1 <;> simp [h1]

/-! ### The adder and the subtractor, bit by bit -/

/-- The digits (least significant first) and the final carry of `n` steps of binary addition. -/
def faRes : Nat → List Bool → List Bool → Bool → List Bool × Bool
  | 0, _, _, c => ([], c)
  | n + 1, xs, ys, c =>
    let s := (xs.headD false).toNat + (ys.headD false).toNat + c.toNat
    let r := faRes n xs.tail ys.tail (decide (2 ≤ s))
    ((s % 2 == 1) :: r.1, r.2)

theorem faRes_length : ∀ n xs ys c, (faRes n xs ys c).1.length = n := by
  intro n; induction n with
  | zero => intros; rfl
  | succ n ih => intro xs ys c; simp [faRes, ih]

theorem num_headD_tail (xs : List Bool) : num xs = (xs.headD false).toNat + 2 * num xs.tail := by
  cases xs <;> simp

theorem faRes_num : ∀ n xs ys c, xs.length ≤ n → ys.length ≤ n →
    num xs + num ys + c.toNat = num (faRes n xs ys c).1 + 2 ^ n * (faRes n xs ys c).2.toNat := by
  intro n
  induction n with
  | zero =>
    intro xs ys c hx hy
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs; subst ys; simp [faRes]
  | succ n ih =>
    intro xs ys c hx hy
    have h := ih xs.tail ys.tail (decide (2 ≤ (xs.headD false).toNat + (ys.headD false).toNat + c.toNat))
      (by simp; omega) (by simp; omega)
    rw [num_headD_tail xs, num_headD_tail ys]
    simp only [faRes, num_cons]
    revert h
    generalize faRes n xs.tail ys.tail (decide (2 ≤ (xs.headD false).toNat + (ys.headD false).toNat + c.toNat)) = R
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
    generalize 2 ^ n * R.2.toNat = P
    generalize xs.headD false = x
    generalize ys.headD false = y
    intro h
    cases x <;> cases y <;> cases c <;> simp at h ⊢ <;> omega

/-- The digits and the final borrow of `n` steps of binary subtraction. -/
def fsRes : Nat → List Bool → List Bool → Bool → List Bool × Bool
  | 0, _, _, c => ([], c)
  | n + 1, xs, ys, c =>
    let x := (xs.headD false).toNat
    let t := (ys.headD false).toNat + c.toNat
    let r := fsRes n xs.tail ys.tail (decide (x < t))
    (((x + t) % 2 == 1) :: r.1, r.2)

theorem fsRes_length : ∀ n xs ys c, (fsRes n xs ys c).1.length = n := by
  intro n; induction n with
  | zero => intros; rfl
  | succ n ih => intro xs ys c; simp [fsRes, ih]

theorem fsRes_num : ∀ n xs ys c, xs.length ≤ n → ys.length ≤ n →
    num xs + 2 ^ n * (fsRes n xs ys c).2.toNat = num (fsRes n xs ys c).1 + num ys + c.toNat := by
  intro n
  induction n with
  | zero =>
    intro xs ys c hx hy
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs; subst ys; simp [fsRes]
  | succ n ih =>
    intro xs ys c hx hy
    have h := ih xs.tail ys.tail (decide ((xs.headD false).toNat < (ys.headD false).toNat + c.toNat))
      (by simp; omega) (by simp; omega)
    rw [num_headD_tail xs, num_headD_tail ys]
    simp only [fsRes, num_cons]
    revert h
    generalize fsRes n xs.tail ys.tail (decide ((xs.headD false).toNat < (ys.headD false).toNat + c.toNat)) = R
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
    generalize 2 ^ n * R.2.toNat = P
    generalize xs.headD false = x
    generalize ys.headD false = y
    intro h
    cases x <;> cases y <;> cases c <;> simp at h ⊢ <;> omega

/-! ### The full adder and the full subtractor as commands -/

/-- Push the sum bit of `s ∈ {0, 1, 2, 3}` onto `XZ` and its carry onto `XC`. -/
def faOut (s : Nat) : Command K :=
  if 2 ≤ s then .seq (.push XZ (s % 2 == 1)) (.push XC true) else .push XZ (s % 2 == 1)
def faC (s : Nat) : Command K := .branch XC (faOut s) (faOut s) (.seq (.pop XC) (faOut (s + 1)))
def faB (s : Nat) : Command K :=
  .branch XB (faC s) (.seq (.pop XB) (faC s)) (.seq (.pop XB) (faC (s + 1)))
/-- One step of binary addition: the top bits of `XA`, `XB` and the carry `XC`. -/
def fa : Command K := .branch XA (faB 0) (.seq (.pop XA) (faB 0)) (.seq (.pop XA) (faB 1))

/-- Push the difference bit of `x - t` (`x ≤ 1`, `t ≤ 2`) onto `XZ` and its borrow onto `XC`. -/
def fsOut (x t : Nat) : Command K :=
  if x < t then .seq (.push XZ ((x + t) % 2 == 1)) (.push XC true) else .push XZ ((x + t) % 2 == 1)
def fsC (x t : Nat) : Command K := .branch XC (fsOut x t) (fsOut x t) (.seq (.pop XC) (fsOut x (t + 1)))
def fsB (x : Nat) : Command K :=
  .branch XB (fsC x 0) (.seq (.pop XB) (fsC x 0)) (.seq (.pop XB) (fsC x 1))
/-- One step of binary subtraction. -/
def fs : Command K := .branch XA (fsB 0) (.seq (.pop XA) (fsB 0)) (.seq (.pop XA) (fsB 1))

/-- The registers of the bit-serial arithmetic: `XA`, `XB`, the carry `XC`, the digits `XZ`. -/
abbrev ArithState := List Bool × List Bool × Bool × List Bool

def faStep : ArithState → ArithState
  | (xs, ys, c, zs) =>
    let s := (xs.headD false).toNat + (ys.headD false).toNat + c.toNat
    (xs.tail, ys.tail, decide (2 ≤ s), (s % 2 == 1) :: zs)

def fsStep : ArithState → ArithState
  | (xs, ys, c, zs) =>
    let x := (xs.headD false).toNat
    let t := (ys.headD false).toNat + c.toNat
    (xs.tail, ys.tail, decide (x < t), ((x + t) % 2 == 1) :: zs)

theorem iter_faStep : ∀ n xs ys c zs, iter faStep n (xs, ys, c, zs) =
    (xs.drop n, ys.drop n, (faRes n xs ys c).2, (faRes n xs ys c).1.reverse ++ zs) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro xs ys c zs
    simp only [iter, faStep, ih, faRes, List.reverse_cons, List.append_assoc, List.singleton_append]
    cases xs <;> cases ys <;> simp

theorem iter_fsStep : ∀ n xs ys c zs, iter fsStep n (xs, ys, c, zs) =
    (xs.drop n, ys.drop n, (fsRes n xs ys c).2, (fsRes n xs ys c).1.reverse ++ zs) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro xs ys c zs
    simp only [iter, fsStep, ih, fsRes, List.reverse_cons, List.append_assoc, List.singleton_append]
    cases xs <;> cases ys <;> simp

/-- The registers hold the arithmetic state `s`, and agree with `r0` elsewhere (but `XT`). -/
def ArithAt (r0 : Regs) (s : ArithState) (q : Regs) : Prop :=
  q XA = s.1 ∧ q XB = s.2.1 ∧ q XC = (if s.2.2.1 then [true] else []) ∧ q XZ = s.2.2.2 ∧
    ∀ i, i ≠ XA → i ≠ XB → i ≠ XC → i ≠ XZ → i ≠ XT → q i = r0 i

theorem ArithAt.setT {r0 : Regs} {s : ArithState} {q : Regs} (h : ArithAt r0 s q) (w : List Bool) :
    ArithAt r0 s (set q XT w) := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨by simp [a], by simp [b], by simp [c], by simp [d],
    fun i h1 h2 h3 h4 h5 => by simp [h5, e i h1 h2 h3 h4 h5]⟩

theorem ok_fa (r0 : Regs) (s : ArithState) (q : Regs) (h : ArithAt r0 s q) :
    ∃ q', Ok fa q q' 14 ∧ ArithAt r0 (faStep s) q' := by
  obtain ⟨xs, ys, c, zs⟩ := s
  obtain ⟨ha, hb, hc, hz, hf⟩ := h
  simp only at ha hb hc hz
  apply ok_of_evalP 0
  rcases xs with _ | ⟨_ | _, xs⟩ <;> rcases ys with _ | ⟨_ | _, ys⟩ <;> cases c <;>
    simp [eval, fa, faB, faC, faOut, ha, hb, hc, hz, faStep, ArithAt, set_apply] <;>
    intro i h1 h2 h3 h4 h5 <;> simp [h1, h2, h3, h4, hf i h1 h2 h3 h4 h5]

theorem ok_fs (r0 : Regs) (s : ArithState) (q : Regs) (h : ArithAt r0 s q) :
    ∃ q', Ok fs q q' 14 ∧ ArithAt r0 (fsStep s) q' := by
  obtain ⟨xs, ys, c, zs⟩ := s
  obtain ⟨ha, hb, hc, hz, hf⟩ := h
  simp only at ha hb hc hz
  apply ok_of_evalP 0
  rcases xs with _ | ⟨_ | _, xs⟩ <;> rcases ys with _ | ⟨_ | _, ys⟩ <;> cases c <;>
    simp [eval, fs, fsB, fsC, fsOut, ha, hb, hc, hz, fsStep, ArithAt, set_apply] <;>
    intro i h1 h2 h3 h4 h5 <;> simp [h1, h2, h3, h4, hf i h1 h2 h3 h4 h5]

/-! ### Sum and truncated difference -/

/-- A register that the arithmetic does not use as scratch. -/
abbrev ArithFree (i : Reg) : Prop := i ≠ XA ∧ i ≠ XB ∧ i ≠ XC ∧ i ≠ XZ ∧ i ≠ XT ∧ i ≠ XU

/-- The scratch registers of the arithmetic are empty. -/
def ArithEmpty (q : Regs) : Prop := q XA = [] ∧ q XB = [] ∧ q XC = [] ∧ q XZ = [] ∧ q XT = [] ∧ q XU = []

theorem length_dropWhile_le (p : Bool → Bool) (l : List Bool) : (l.dropWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.dropWhile_cons]; split <;> simp <;> omega

/-- Write the canonical numeral of the most-significant-first digits `XZ` into `d`. -/
def finishB (d : Reg) : Command K :=
  .seq (.length XZ XT XU) (.seq (.repeat XT strip) (.seq (.clear d) (revOnto XZ d XT)))

theorem ok_finishB {d : Reg} (hd : ArithFree d) (q : Regs) (hT : q XT = []) (hU : q XU = []) :
    ∃ q', Ok (finishB d) q q' (20 * (q XZ).length + (q d).length + 18) ∧
      q' d = ((q XZ).dropWhile (· == false)).reverse ∧ q' XZ = [] ∧ q' XT = [] ∧
      ∀ i, i ≠ d → i ≠ XZ → i ≠ XT → q' i = q i := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  have s1 := ok_length (s := XZ) (d := XT) (t := XU) (by decide) (by decide) (by decide) q hU
  generalize hq1 : set q XT (List.replicate (q XZ).length true) = q1 at s1
  have q1Z : q1 XZ = q XZ := by rw [← hq1]; simp []
  have q1T : (q1 XT).length = (q XZ).length := by rw [← hq1]; simp
  have q1f : ∀ i, i ≠ XT → q1 i = q i := by intro i hi; rw [← hq1]; simp [hi]
  have hw : writes strip XT = false := by simp [strip, skipC, writes]
  obtain ⟨q2, s2, hE2, q2T⟩ := ok_repeat hw (fun (z : List Bool) (p : Regs) =>
      p XZ = z ∧ ∀ i, i ≠ XZ → i ≠ XT → p i = q1 i) stripStep 3
    (by intro z p w ⟨a, b⟩; exact ⟨by simp [a], fun i i1 i2 => by simp [i2, b i i1 i2]⟩)
    (by
      intro z p ⟨a, b⟩
      obtain ⟨p', hp, hz, hf⟩ := ok_strip p
      exact ⟨p', hp, by rw [hz, a], fun i i1 i2 => by rw [hf i i1, b i i1 i2]⟩)
    _ (q XZ) q1 ⟨q1Z, fun _ _ _ => rfl⟩ q1T
  rw [iter_stripStep _ _ (Nat.le_refl _)] at hE2
  obtain ⟨q2Z, q2f⟩ := hE2
  have s3 := ok_clear d q2
  generalize hq3 : set q2 d [] = q3 at s3
  have q3Z : q3 XZ = (q XZ).dropWhile (· == false) := by rw [← hq3]; simp [Ne.symm d4, q2Z]
  have q3U : q3 XU = [] := by
    rw [← hq3]; simp [Ne.symm d6, q2f XU (by decide) (by decide), q1f XU (by decide), hU]
  obtain ⟨q4, s4, q4Z, q4d, q4T, q4f⟩ := ok_revOnto (src := XZ) (dst := d) (ct := XT) (Ne.symm d4) (by decide)
    d5 (by decide) d6 (by decide) q3 q3U
  have q3d : q3 d = [] := by rw [← hq3]; simp
  have q3T : q3 XT = [] := by rw [← hq3]; simp [Ne.symm d5, q2T]
  have q2d : q2 d = q d := by rw [q2f d d4 d5, q1f d d5]
  refine ⟨q4, ((s1.seq (s2.seq (s3.seq s4)))).mono ?_, by rw [q4d, q3Z, q3d, List.append_nil], q4Z, q4T, ?_⟩
  · rw [q3T, q3Z, q2d, hT]
    have := length_dropWhile_le (· == false) (q XZ)
    simp only [List.length_nil]
    omega
  · intro i i1 i2 i3
    rw [q4f i i2 i1 i3]
    rw [← hq3]; simp [i1, q2f i i2 i3, q1f i i3]

/-- Copy the operands to `XA`, `XB` and count `|a| + |b| + 1` in `XT`. -/
def arithPre (a b : Reg) : Command K :=
  .seq (.copy a XA XU) (.seq (.copy b XB XU) (.seq (.length XA XT XU) (.seq (.add XB XT XU) (.push XT true))))

/-- `d := a + b` on canonical numerals. -/
def addB (a b d : Reg) : Command K := .seq (arithPre a b) (.seq (.repeat XT fa) (finishB d))

/-- `d := a - b` (truncated) on canonical numerals. -/
def subB (a b d : Reg) : Command K :=
  .seq (arithPre a b) (.seq (.repeat XT fs) (.branch XC (finishB d) (finishB d) (.seq (.pop XC) (.seq (.clear XZ) (.clear d)))))

theorem two_pow_add_le (p q : Nat) : 2 ^ p + 2 ^ q ≤ 2 ^ (p + q + 1) := by
  have h1 : 2 ^ p ≤ 2 ^ (p + q) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ q ≤ 2 ^ (p + q) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.pow_succ]; omega

/-- The first five commands of `addB` and `subB`: copy the operands, count `|a| + |b| + 1`. -/
theorem ok_arithPre {a b : Reg} (ha : ArithFree a) (hb : ArithFree b) (q : Regs) (hs : ArithEmpty q) :
    ∃ q', Ok (arithPre a b) q q' (10 * (q a).length + 10 * (q b).length + 24) ∧
      ArithAt q (q a, q b, false, []) q' ∧ (q' XT).length = (q a).length + (q b).length + 1 ∧ q' XU = [] := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  obtain ⟨hA, hB, hC, hZ, hT, hU⟩ := hs
  have s1 := ok_copy (s := a) (d := XA) (t := XU) a1 a6 (by decide) q hU
  have s2 := ok_copy (s := b) (d := XB) (t := XU) b2 b6 (by decide) (set q XA (q a)) (by simp [hU])
  have s3 := ok_length (s := XA) (d := XT) (t := XU) (by decide) (by decide) (by decide)
    (set (set q XA (q a)) XB (set q XA (q a) b)) (by simp [set_apply, hU])
  have s4 := ok_addU (s := XB) (d := XT) (t := XU) (by decide) (by decide) (by decide)
    (set (set (set q XA (q a)) XB (set q XA (q a) b)) XT
      (List.replicate ((set (set q XA (q a)) XB (set q XA (q a) b)) XA).length true)) (by simp [set_apply, hU])
  have s5 := ok_push XT true (set (set (set (set q XA (q a)) XB (set q XA (q a) b)) XT
      (List.replicate ((set (set q XA (q a)) XB (set q XA (q a) b)) XA).length true)) XT
      (List.replicate ((set (set (set q XA (q a)) XB (set q XA (q a) b)) XT
      (List.replicate ((set (set q XA (q a)) XB (set q XA (q a) b)) XA).length true)) XB).length true ++
      (set (set (set q XA (q a)) XB (set q XA (q a) b)) XT
      (List.replicate ((set (set q XA (q a)) XB (set q XA (q a) b)) XA).length true)) XT))
  refine ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq s5)))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [b1, hA, hB, hT]; omega
  · simp [set_apply]
  · simp [b1]
  · simp [set_apply, hC]
  · simp [set_apply, hZ]
  · intro i i1 i2 _ _ i5; simp [set_apply, i1, i2, i5]
  · simp [b1]; omega
  · simp [set_apply, hU]

theorem ok_addB {a b d : Reg} (ha : ArithFree a) (hb : ArithFree b) (hd : ArithFree d) (q : Regs) (hs : ArithEmpty q)
    {x y B : Nat} (hx : q a = bin x) (hy : q b = bin y) (hxB : (bin x).length ≤ B) (hyB : (bin y).length ≤ B)
    (hdB : (q d).length ≤ B) :
    ∃ q', Ok (addB a b d) q q' (100 * (B + 1)) ∧ q' d = bin (x + y) ∧ ArithEmpty q' ∧
      ∀ i, ArithFree i → i ≠ d → q' i = q i := by
  obtain ⟨q5, s5, hA5, hT5, hU5⟩ := ok_arithPre ha hb q hs
  rw [hx, hy] at hA5 hT5
  have hw : writes fa XT = false := by simp [fa, faB, faC, faOut, writes]
  obtain ⟨q6, s6, hA6, hT6⟩ := ok_repeat hw (ArithAt q) faStep 14 (fun s p w h => h.setT w)
    (fun s p h => ok_fa q s p h) _ _ q5 hA5 hT5
  generalize hN : (bin x).length + (bin y).length + 1 = N at s6 hA6
  rw [iter_faStep] at hA6
  obtain ⟨a6, b6, c6, z6, f6⟩ := hA6
  simp only at a6 b6 c6 z6
  have hnum := faRes_num N (bin x) (bin y) false (by omega) (by omega)
  rw [num_bin, num_bin] at hnum
  have hlt : x + y < 2 ^ N := by
    have := lt_pow_bin_length x; have := lt_pow_bin_length y
    have := two_pow_add_le (bin x).length (bin y).length
    rw [hN] at this; omega
  have hcf : (faRes N (bin x) (bin y) false).2 = false := by
    cases h : (faRes N (bin x) (bin y) false).2
    · rfl
    · rw [h] at hnum; simp at hnum; omega
  have hU6 : q6 XU = [] := by rw [f6 _ (by decide) (by decide) (by decide) (by decide) (by decide), hs.2.2.2.2.2]
  obtain ⟨q7, s7, d7, z7, t7, f7⟩ := ok_finishB hd q6 hT6 hU6
  refine ⟨q7, (s5.seq (s6.seq s7)).mono ?_, ?_, ⟨?_, ?_, ?_, z7, t7, ?_⟩, ?_⟩
  · rw [z6, List.append_nil, List.length_reverse, faRes_length, hx, hy,
      f6 d hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1]
    have : N ≤ 2 * B + 1 := by omega
    omega
  · rw [d7, z6, List.append_nil, ← bin_num_reverse, List.reverse_reverse]
    have := hnum; simp only [hcf, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at this
    rw [← this]
  · rw [f7 _ (Ne.symm hd.1) (by decide) (by decide), a6, List.drop_eq_nil_of_le (by omega)]
  · rw [f7 _ (Ne.symm hd.2.1) (by decide) (by decide), b6, List.drop_eq_nil_of_le (by omega)]
  · rw [f7 _ (Ne.symm hd.2.2.1) (by decide) (by decide), c6, hcf]; rfl
  · rw [f7 _ (Ne.symm hd.2.2.2.2.2) (by decide) (by decide), hU6]
  · intro i hi hid
    rw [f7 i hid hi.2.2.2.1 hi.2.2.2.2.1, f6 i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1]

theorem ok_subB {a b d : Reg} (ha : ArithFree a) (hb : ArithFree b) (hd : ArithFree d) (q : Regs) (hs : ArithEmpty q)
    {x y B : Nat} (hx : q a = bin x) (hy : q b = bin y) (hxB : (bin x).length ≤ B) (hyB : (bin y).length ≤ B)
    (hdB : (q d).length ≤ B) :
    ∃ q', Ok (subB a b d) q q' (100 * (B + 1)) ∧ q' d = bin (x - y) ∧ ArithEmpty q' ∧
      ∀ i, ArithFree i → i ≠ d → q' i = q i := by
  obtain ⟨q5, s5, hA5, hT5, hU5⟩ := ok_arithPre ha hb q hs
  rw [hx, hy] at hA5 hT5
  have hw : writes fs XT = false := by
    simp [fs, fsB, fsC, fsOut, writes]
  obtain ⟨q6, s6, hA6, hT6⟩ := ok_repeat hw (ArithAt q) fsStep 14 (fun s p w h => h.setT w)
    (fun s p h => ok_fs q s p h) _ _ q5 hA5 hT5
  generalize hN : (bin x).length + (bin y).length + 1 = N at s6 hA6
  rw [iter_fsStep] at hA6
  obtain ⟨a6, b6, c6, z6, f6⟩ := hA6
  simp only at a6 b6 c6 z6
  have hnum := fsRes_num N (bin x) (bin y) false (by omega) (by omega)
  rw [num_bin, num_bin] at hnum
  have hdl := num_lt (fsRes N (bin x) (bin y) false).1
  rw [fsRes_length] at hdl
  have hU6 : q6 XU = [] := by rw [f6 _ (by decide) (by decide) (by decide) (by decide) (by decide), hs.2.2.2.2.2]
  have hd6 : q6 d = q d := f6 d hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1
  have hfr6 : ∀ i, ArithFree i → q6 i = q i := fun i hi => f6 i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1
  have hA0 : q6 XA = [] := by rw [a6, List.drop_eq_nil_of_le (by omega)]
  have hB0 : q6 XB = [] := by rw [b6, List.drop_eq_nil_of_le (by omega)]
  cases hcf : (fsRes N (bin x) (bin y) false).2 with
  | false =>
    rw [hcf] at c6 hnum
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hnum
    obtain ⟨q7, s7, d7, z7, t7, f7⟩ := ok_finishB hd q6 hT6 hU6
    have c6' : q6 XC = [] := by rw [c6]; rfl
    refine ⟨q7, (s5.seq (s6.seq (Ok.branch_nil c6' s7))).mono ?_, ?_, ⟨?_, ?_, ?_, z7, t7, ?_⟩, ?_⟩
    · rw [z6, List.append_nil, List.length_reverse, fsRes_length, hx, hy, hd6]
      have : N ≤ 2 * B + 1 := by omega
      omega
    · rw [d7, z6, List.append_nil, ← bin_num_reverse, List.reverse_reverse]
      congr 1; omega
    · rw [f7 _ (Ne.symm hd.1) (by decide) (by decide), hA0]
    · rw [f7 _ (Ne.symm hd.2.1) (by decide) (by decide), hB0]
    · rw [f7 _ (Ne.symm hd.2.2.1) (by decide) (by decide), c6']
    · rw [f7 _ (Ne.symm hd.2.2.2.2.2) (by decide) (by decide), hU6]
    · intro i hi hid; rw [f7 i hid hi.2.2.2.1 hi.2.2.2.2.1, hfr6 i hi]
  | true =>
    rw [hcf] at c6 hnum
    simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.add_zero] at hnum
    have c6' : q6 XC = true :: [] := by rw [c6]; rfl
    have s7 := (ok_pop XC q6).seq ((ok_clear XZ _).seq (ok_clear d _))
    refine ⟨_, (s5.seq (s6.seq (Ok.branch_true c6' s7))).mono ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [set_apply, ite_eq_right (show XZ ≠ XC by decide), ite_eq_right hd.2.2.2.1, ite_eq_right hd.2.2.1]
      rw [z6, List.append_nil, List.length_reverse, fsRes_length, hx, hy, hd6]
      have : N ≤ 2 * B + 1 := by omega
      omega
    · simp only [set_same']
      have : x - y = 0 := by omega
      rw [this]; rfl
    all_goals (try intro i hi hid)
    all_goals simp [set_apply, hA0, hB0, hU6, hT6, c6', 
      Ne.symm hd.1, Ne.symm hd.2.1, Ne.symm hd.2.2.1, Ne.symm hd.2.2.2.1, Ne.symm hd.2.2.2.2.1,
      Ne.symm hd.2.2.2.2.2]
    all_goals (try (simp [hid, hi.2.2.1, hi.2.2.2.1]; exact hfr6 i hi))

end STACS2027.Sim
