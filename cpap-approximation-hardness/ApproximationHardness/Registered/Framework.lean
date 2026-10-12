module

public import Complexity.StackTableauProgram
public import Complexity.Restricted.Commands
public import Complexity.Restricted.LeExtract
public import Complexity.StackCompile
public import Complexity.PolynomialBound
import Lean.Elab.Tactic.Omega

/-!
# Specifications of structured stack commands

The registered foundation's structured stack language
(`Complexity.StackTableauProgram.Command`) compiles, with exact instruction
counts, to the single-tape machines of the registered model
(`Exec.machine_run`, `StackCompile.polyTime_of_stack`). This file gives a small
specification calculus for it: a command `c` satisfies `Spec c P cost m` when,
from every register state satisfying `P`, it halts within `cost` elementary
instructions and its result is predicted by the partial model `m` (`none` is
failure, `some r'` success in state `r'`). The calculus has composition rules
for sequencing, counted loops, three-way branches and tests, and the
specifications of the primitive commands on concrete registers.
-/

@[expose] public section

namespace STACS2027.Registered

open Complexity
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame)

/-- The number of stack registers is `K + 1`. -/
abbrev K : Nat := 41
abbrev Regs := Registers K
abbrev Reg := Fin (K + 1)

/-- The partial model `m` predicts the execution result `res`. -/
def Realizes (m : Option Regs) (res : Bool × Regs) : Prop :=
  match m with
  | some r' => res = (true, r')
  | none => res.1 = false

/-- From every state satisfying `P`, `c` halts within `cost` instructions with the
result predicted by `m`. -/
def Spec (c : Command K) (P : Regs → Prop) (cost : Nat) (m : Regs → Option Regs) : Prop :=
  ∀ r, P r → ∃ t res, Exec c r t res ∧ t ≤ cost ∧ Realizes (m r) res

/-- A total specification: the decision and the state are both predicted. -/
def SpecT (c : Command K) (P : Regs → Prop) (cost : Nat) (m : Regs → Bool × Regs) : Prop :=
  ∀ r, P r → ∃ t, Exec c r t (m r) ∧ t ≤ cost

theorem Spec.of_total {c : Command K} {P : Regs → Prop} {cost : Nat} {m : Regs → Bool × Regs}
    (h : SpecT c P cost m) :
    Spec c P cost (fun r => if (m r).1 then some (m r).2 else none) := by
  intro r hr
  obtain ⟨t, he, ht⟩ := h r hr
  refine ⟨t, m r, he, ht, ?_⟩
  cases hm : m r with
  | mk b r' =>
    cases b <;> simp [Realizes, hm]

theorem Spec.mono {c : Command K} {P P' : Regs → Prop} {cost cost' : Nat} {m : Regs → Option Regs}
    (h : Spec c P cost m) (hP : ∀ r, P' r → P r) (hc : cost ≤ cost') : Spec c P' cost' m := by
  intro r hr
  obtain ⟨t, res, he, ht, hm⟩ := h r (hP r hr)
  exact ⟨t, res, he, Nat.le_trans ht hc, hm⟩

theorem Spec.congr {c : Command K} {P : Regs → Prop} {cost : Nat} {m m' : Regs → Option Regs}
    (h : Spec c P cost m) (hm : ∀ r, P r → m r = m' r) : Spec c P cost m' := by
  intro r hr
  obtain ⟨t, res, he, ht, hr'⟩ := h r hr
  exact ⟨t, res, he, ht, by rw [← hm r hr]; exact hr'⟩

/-- A successful model agrees with the frame of the command. -/
theorem Spec.frame {c : Command K} {P : Regs → Prop} {cost : Nat} {m : Regs → Option Regs}
    (h : Spec c P cost m) {r r' : Regs} (hr : P r) (hm : m r = some r') :
    ∀ i, writes c i = false → r' i = r i := by
  obtain ⟨t, res, he, _, hres⟩ := h r hr
  rw [hm] at hres
  simp only [Realizes] at hres
  subst hres
  exact exec_frame he

/-- Sequencing: the second command starts in the state predicted by the first. -/
theorem Spec.seq {c₁ c₂ : Command K} {P P₂ : Regs → Prop} {cost₁ cost₂ : Nat}
    {m₁ m₂ : Regs → Option Regs} (h₁ : Spec c₁ P cost₁ m₁)
    (hP : ∀ r r', P r → m₁ r = some r' → P₂ r') (h₂ : Spec c₂ P₂ cost₂ m₂) :
    Spec (.seq c₁ c₂) P (cost₁ + cost₂) (fun r => (m₁ r).bind m₂) := by
  intro r hr
  obtain ⟨t, res, he, ht, hres⟩ := h₁ r hr
  cases hm : m₁ r with
  | none =>
    rw [hm] at hres
    simp only [Realizes] at hres
    obtain ⟨b, r'⟩ := res
    simp only at hres
    subst hres
    exact ⟨t, (false, r'), Exec.seqFailure he, by omega, by simp [Realizes, hm]⟩
  | some r' =>
    rw [hm] at hres
    simp only [Realizes] at hres
    subst hres
    obtain ⟨s, res₂, he₂, hs, hres₂⟩ := h₂ r' (hP r r' hr hm)
    exact ⟨t + s, res₂, Exec.seq he he₂, by omega, by simpa [hm] using hres₂⟩

/-- The model of a counted loop: `fuel` bounds the iterations; each iteration pops
the counter, runs the body model, and continues while it succeeds. -/
def iter (m : Regs → Option Regs) (j : Reg) : Nat → Regs → Option Regs
  | 0, r => some r
  | n + 1, r =>
    match r j with
    | [] => some r
    | _ :: tail => (m (set r j tail)).bind (iter m j n)

theorem iter_nil (m : Regs → Option Regs) (j : Reg) (n : Nat) (r : Regs) (h : r j = []) :
    iter m j n r = some r := by
  cases n with
  | zero => rfl
  | succ n => simp [iter, h]

theorem iter_cons (m : Regs → Option Regs) (j : Reg) (n : Nat) (r : Regs) (b : Bool)
    (tail : List Bool) (h : r j = b :: tail) :
    iter m j (n + 1) r = (m (set r j tail)).bind (iter m j n) := by
  simp [iter, h]

/-- Counted loops. The body does not write the counter; popping the counter from a
state satisfying the loop invariant `P` gives a state satisfying the body's
precondition `Pb`; the body model re-establishes `P`; and the counter has at most
`L` bits in every state satisfying `P`. -/
theorem Spec.repeat {j : Reg} {body : Command K} {P Pb : Regs → Prop} {cost L : Nat}
    {m : Regs → Option Regs} (hw : writes body j = false)
    (hset : ∀ r b tail, P r → r j = b :: tail → Pb (set r j tail))
    (hm : ∀ r b tail r', P r → r j = b :: tail → m (set r j tail) = some r' → P r')
    (hL : ∀ r, P r → (r j).length ≤ L) (h : Spec body Pb cost m) :
    Spec (.repeat j body) P (L * (cost + 1) + 2) (fun r => iter m j (r j).length r) := by
  have key : ∀ n r, P r → (r j).length = n → ∃ t res, Exec (.repeat j body) r t res ∧
      t ≤ n * (cost + 1) + 2 ∧ Realizes (iter m j n r) res := by
    intro n
    induction n with
    | zero =>
      intro r hr hn
      have hj : r j = [] := List.eq_nil_of_length_eq_zero hn
      exact ⟨2, (true, r), Exec.repeatDone hj, by omega, by simp [iter_nil m j 0 r hj, Realizes]⟩
    | succ n ih =>
      intro r hr hn
      cases hj : r j with
      | nil => rw [hj] at hn; simp at hn
      | cons b tail =>
        rw [hj] at hn
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
        have hr₁ : Pb (set r j tail) := hset r b tail hr hj
        obtain ⟨t, res, he, ht, hres⟩ := h (set r j tail) hr₁
        rw [iter_cons m j n r b tail hj]
        cases hmb : m (set r j tail) with
        | none =>
          rw [hmb] at hres
          simp only [Realizes] at hres
          obtain ⟨bb, out⟩ := res
          simp only at hres
          subst hres
          exact ⟨t + 1, (false, out), Exec.repeatFailure hj he, by
            simp only [Nat.succ_mul]; omega, by simp [Realizes]⟩
        | some middle =>
          rw [hmb] at hres
          simp only [Realizes] at hres
          subst hres
          have hmid : middle j = tail := by
            have := exec_frame he j hw
            simpa using this
          obtain ⟨s, res₂, he₂, hs, hres₂⟩ := ih middle (hm r b tail middle hr hj hmb)
            (by rw [hmid]; exact hn)
          exact ⟨t + s + 1, res₂, Exec.repeatNext hj he he₂, by
            simp only [Nat.succ_mul]; omega, by simpa using hres₂⟩
  intro r hr
  obtain ⟨t, res, he, ht, hres⟩ := key (r j).length r hr rfl
  refine ⟨t, res, he, ?_, hres⟩
  have := hL r hr
  have h1 : (r j).length * (cost + 1) ≤ L * (cost + 1) := Nat.mul_le_mul_right _ this
  omega

/-- The invariant of a counted loop is preserved by its model. -/
theorem iter_invariant {j : Reg} {P : Regs → Prop} {m : Regs → Option Regs}
    (hm : ∀ r b tail r', P r → r j = b :: tail → m (set r j tail) = some r' → P r') :
    ∀ n r r', P r → iter m j n r = some r' → P r' := by
  intro n
  induction n with
  | zero => intro r r' hr h; simp [iter] at h; subst h; exact hr
  | succ n ih =>
    intro r r' hr h
    cases hj : r j with
    | nil => rw [iter_nil m j _ r hj] at h; simp at h; subst h; exact hr
    | cons b tail =>
      rw [iter_cons m j n r b tail hj] at h
      cases hmb : m (set r j tail) with
      | none => rw [hmb] at h; simp at h
      | some middle =>
        rw [hmb] at h
        simp only [Option.bind_some] at h
        exact ih middle r' (hm r b tail middle hr hj hmb) h

/-- Three-way branch on the top bit of register `j`. -/
theorem Spec.branch {j : Reg} {e z o : Command K} {P : Regs → Prop} {ce cz co : Nat}
    {me mz mo : Regs → Option Regs}
    (he : Spec e (fun r => P r ∧ r j = []) ce me)
    (hz : Spec z (fun r => P r ∧ ∃ tail, r j = false :: tail) cz mz)
    (ho : Spec o (fun r => P r ∧ ∃ tail, r j = true :: tail) co mo) :
    Spec (.branch j e z o) P (max ce (max cz co) + 1)
      (fun r => match r j with
        | [] => me r
        | false :: _ => mz r
        | true :: _ => mo r) := by
  intro r hr
  cases hj : r j with
  | nil =>
    obtain ⟨t, res, hex, ht, hres⟩ := he r ⟨hr, hj⟩
    refine ⟨t + 1, res, Exec.branchEmpty hj hex, ?_, by simp only [hj]; exact hres⟩
    have := Nat.le_max_left ce (max cz co)
    omega
  | cons b tail =>
    cases b with
    | false =>
      obtain ⟨t, res, hex, ht, hres⟩ := hz r ⟨hr, tail, hj⟩
      refine ⟨t + 1, res, Exec.branchZero hj hex, ?_, by simp only [hj]; exact hres⟩
      have := Nat.le_max_right ce (max cz co)
      have := Nat.le_max_left cz co
      omega
    | true =>
      obtain ⟨t, res, hex, ht, hres⟩ := ho r ⟨hr, tail, hj⟩
      refine ⟨t + 1, res, Exec.branchOne hj hex, ?_, by simp only [hj]; exact hres⟩
      have := Nat.le_max_right ce (max cz co)
      have := Nat.le_max_right cz co
      omega

/-- A test with a total model, followed by one of two commands. -/
theorem Spec.ifThenElse {test yes no : Command K} {P Py Pn : Regs → Prop} {ct cy cn : Nat}
    {mt : Regs → Bool × Regs} {my mn : Regs → Option Regs}
    (ht : SpecT test P ct mt)
    (hPy : ∀ r, P r → (mt r).1 = true → Py (mt r).2)
    (hPn : ∀ r, P r → (mt r).1 = false → Pn (mt r).2)
    (hy : Spec yes Py cy my) (hn : Spec no Pn cn mn) :
    Spec (.ifThenElse test yes no) P (ct + max cy cn)
      (fun r => if (mt r).1 then my (mt r).2 else mn (mt r).2) := by
  intro r hr
  obtain ⟨t, he, htl⟩ := ht r hr
  cases hmt : mt r with
  | mk b r' =>
    rw [hmt] at he
    cases b with
    | true =>
      obtain ⟨s, res, hey, hs, hres⟩ := hy r' (by have := hPy r hr; rw [hmt] at this; exact this rfl)
      refine ⟨t + s, res, Exec.ifTrue he hey, ?_, ?_⟩
      · have := Nat.le_max_left cy cn; omega
      · simpa [hmt] using hres
    | false =>
      obtain ⟨s, res, hen, hs, hres⟩ := hn r' (by have := hPn r hr; rw [hmt] at this; exact this rfl)
      refine ⟨t + s, res, Exec.ifFalse he hen, ?_, ?_⟩
      · have := Nat.le_max_right cy cn; omega
      · simpa [hmt] using hres

/-! ### Primitive commands -/

theorem Spec.stop_true (P : Regs → Prop) : Spec (.stop true) P 1 (fun r => some r) := by
  intro r _
  exact ⟨1, (true, r), Exec.stop true r, Nat.le_refl _, by simp [Realizes]⟩

theorem Spec.stop_false (P : Regs → Prop) : Spec (.stop false) P 1 (fun _ => none) := by
  intro r _
  exact ⟨1, (false, r), Exec.stop false r, Nat.le_refl _, by simp [Realizes]⟩

theorem Spec.push (j : Reg) (b : Bool) (P : Regs → Prop) :
    Spec (.push j b) P 2 (fun r => some (set r j (b :: r j))) := by
  intro r _
  exact ⟨2, _, Exec.push j b r, Nat.le_refl _, by simp [Realizes]⟩

theorem Spec.pop (j : Reg) (P : Regs → Prop) :
    Spec (.pop j) P 2 (fun r => some (set r j (r j).tail)) := by
  intro r _
  exact ⟨2, _, Exec.pop j r, Nat.le_refl _, by simp [Realizes]⟩

theorem Spec.clear (j : Reg) {P : Regs → Prop} {L : Nat} (hL : ∀ r, P r → (r j).length ≤ L) :
    Spec (.clear j) P (L + 2) (fun r => some (set r j [])) := by
  intro r hr
  exact ⟨_, _, Exec.clear j r, by have := hL r hr; omega, by simp [Realizes]⟩

theorem Spec.copy {src dst scratch : Reg} (hsd : src ≠ dst) (hst : src ≠ scratch)
    (hdt : dst ≠ scratch) {P : Regs → Prop} {a b : Nat}
    (hs : ∀ r, P r → r scratch = [])
    (hL : ∀ r, P r → (r src).length ≤ a ∧ (r dst).length ≤ b) :
    Spec (.copy src dst scratch) P (b + 5 * a + 6) (fun r => some (set r dst (r src))) := by
  intro r hr
  refine ⟨_, _, Exec.copy hsd hst hdt (hs r hr), ?_, by simp [Realizes]⟩
  have := hL r hr
  omega

theorem Spec.length {src dst scratch : Reg} (hsd : src ≠ dst) (hst : src ≠ scratch)
    (hdt : dst ≠ scratch) {P : Regs → Prop} {a b : Nat}
    (hs : ∀ r, P r → r scratch = [])
    (hL : ∀ r, P r → (r src).length ≤ a ∧ (r dst).length ≤ b) :
    Spec (.length src dst scratch) P (b + 5 * a + 6)
      (fun r => some (set r dst (List.replicate (r src).length true))) := by
  intro r hr
  refine ⟨_, _, Exec.length hsd hst hdt (hs r hr), ?_, by simp [Realizes]⟩
  have := hL r hr
  omega

theorem Spec.add {src dst scratch : Reg} (hsd : src ≠ dst) (hst : src ≠ scratch)
    (hdt : dst ≠ scratch) {P : Regs → Prop} {a : Nat}
    (hs : ∀ r, P r → r scratch = [])
    (hL : ∀ r, P r → (r src).length ≤ a) :
    Spec (.add src dst scratch) P (5 * a + 4)
      (fun r => some (set r dst (List.replicate (r src).length true ++ r dst))) := by
  intro r hr
  refine ⟨_, _, Exec.add hsd hst hdt (hs r hr), ?_, by simp [Realizes]⟩
  have := hL r hr
  omega

theorem Spec.multiply {src factor dst counter scratch : Reg}
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ scratch)
    (hfc : factor ≠ counter) (hft : factor ≠ scratch) (hfd : factor ≠ dst)
    {P : Regs → Prop} {w a b : Nat}
    (hs : ∀ r, P r → r scratch = [])
    (hf : ∀ r, P r → r factor = List.replicate w true)
    (hc : ∀ r, P r → r counter = [])
    (hL : ∀ r, P r → (r src).length ≤ a ∧ (r dst).length ≤ b) :
    Spec (.multiply src factor dst counter scratch) P (b + 5 * w + w * (5 * a + 5) + 10)
      (fun r => some (set r dst (List.replicate (w * (r src).length) true))) := by
  intro r hr
  have hfac := hf r hr
  have hcnt := hc r hr
  refine ⟨_, _, Exec.multiply hsd hst hdt hcs hcd hct hfc hft hfd (hs r hr) hfac, ?_, ?_⟩
  · have := hL r hr
    rw [hcnt]
    simp only [List.length_nil]
    have hm : w * (5 * (r src).length + 5) ≤ w * (5 * a + 5) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · simp only [Realizes]
    congr 2
    funext i
    by_cases hi : i = counter
    · subst hi
      simp [StackMachine.set, hcnt]
    · simp [StackMachine.set, hi]

theorem Spec.prependNat {number output scratch : Reg} (hno : number ≠ output)
    (hns : number ≠ scratch) (hos : output ≠ scratch) {P : Regs → Prop} {a : Nat}
    (hs : ∀ r, P r → r scratch = [])
    (hL : ∀ r, P r → (r number).length ≤ a) :
    Spec (.prependNat number output scratch) P (5 * a + 6)
      (fun r => some (set r output (SAT.writeNat (r number).length ++ r output))) := by
  intro r hr
  refine ⟨_, _, Exec.prependNat hno hns hos (hs r hr), ?_, by simp [Realizes]⟩
  have := hL r hr
  omega

theorem Spec.prependLiteral {number output scratch : Reg} (sign : Bool) (hno : number ≠ output)
    (hns : number ≠ scratch) (hos : output ≠ scratch) {P : Regs → Prop} {a : Nat}
    (hs : ∀ r, P r → r scratch = [])
    (hL : ∀ r, P r → (r number).length ≤ a) :
    Spec (.prependLiteral number output scratch sign) P (5 * a + 8)
      (fun r => some (set r output (SAT.encodeLiteral ⟨(r number).length, sign⟩ ++ r output))) := by
  intro r hr
  refine ⟨_, _, Exec.prependLiteral (sign := sign) hno hns hos (hs r hr), ?_, by simp [Realizes]⟩
  have := hL r hr
  omega

/-- `n` pushes of `true` onto `j`. -/
def pushN (j : Reg) : Nat → Command K
  | 0 => .stop true
  | n + 1 => .seq (.push j true) (pushN j n)

theorem Spec.pushN (j : Reg) (n : Nat) (P : Regs → Prop) :
    Spec (pushN j n) P (2 * n + 1) (fun r => some (set r j (List.replicate n true ++ r j))) := by
  induction n generalizing P with
  | zero =>
    apply (Spec.stop_true P).congr
    intro r _
    simp only [List.replicate_zero, List.nil_append]
    congr
    funext i
    by_cases hi : i = j
    · subst hi; simp [StackMachine.set]
    · simp [StackMachine.set, hi]
  | succ n ih =>
    have h := (Spec.push j true P).seq (P₂ := fun _ => True) (fun _ _ _ _ => trivial) (ih (fun _ => True))
    apply (h.mono (fun r hr => hr) (by omega)).congr
    intro r _
    simp only [Option.bind_some, List.replicate_succ, List.cons_append]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi; simp [StackMachine.set, Complexity.Restricted.replicate_append_cons]
    · simp [StackMachine.set, hi]

end STACS2027.Registered
