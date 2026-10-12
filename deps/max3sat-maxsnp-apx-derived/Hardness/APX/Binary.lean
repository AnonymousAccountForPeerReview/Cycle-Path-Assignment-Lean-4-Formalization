module

public import PT.Words
public import PT.SAT
import Lean.Elab.Tactic.Omega

/-!
# Polynomial-time arithmetic on binary numerals

Numbers of the `PT` framework are in unary; the values of optimization problems are in binary
(`natBits`, least significant digit first; `SAT.binaryValue` is the value of such a word).
This file provides the operations on binary words needed for the APX-hardness proof, with
specifications in terms of the represented numbers, and proves them polynomial-time:

* `isNat u`: `u` is a canonical numeral, i.e. `u = natBits v` for some `v` (`isNat_iff`);
* `solOut r`: `r = true :: natBits v` for some `v` (`solOut_iff`), the shape of the output of
  the feasibility function of an `NPO` problem on a solution;
* `addBits u v` (`binaryValue_addBits`), ripple-carry addition;
* `mulSmall n w` (`binaryValue_mulSmall`), multiplication by a unary number;
* `leBits u v` (`leBits_iff`), comparison.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT

/-! ### Canonical numerals -/

theorem natBitsFuel_eq_of_le : ∀ (fuel fuel' n : Nat), n ≤ fuel → n ≤ fuel' →
    natBitsFuel fuel n = natBitsFuel fuel' n
  | 0, fuel', n, h, _ => by
    obtain rfl : n = 0 := by omega
    rw [natBitsFuel_zero, natBitsFuel_zero]
  | fuel + 1, 0, n, _, h => by
    obtain rfl : n = 0 := by omega
    rw [natBitsFuel_zero, natBitsFuel_zero]
  | fuel + 1, fuel' + 1, n, h, h' => by
    simp only [natBitsFuel]
    split
    · rfl
    · rw [natBitsFuel_eq_of_le fuel fuel' (n / 2) (by omega) (by omega)]

@[simp] theorem natBits_zero : natBits 0 = [] := rfl

theorem natBits_of_ne_zero {n : Nat} (h : n ≠ 0) :
    natBits n = decide (n % 2 = 1) :: natBits (n / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show natBitsFuel (m + 1) (m + 1) = _
  simp only [natBitsFuel, natBits]
  split
  · omega
  · rw [natBitsFuel_eq_of_le m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)]

/-- A word without a trailing zero is the canonical numeral of its value. -/
theorem natBits_binaryValue : ∀ {u : Word}, u.getLast? ≠ some false →
    natBits (SAT.binaryValue u) = u
  | [], _ => rfl
  | b :: u, h => by
    have hu : u.getLast? ≠ some false := by
      cases u with
      | nil => simp
      | cons a u => simpa [List.getLast?_cons_cons] using h
    have ih := natBits_binaryValue hu
    have hpos : SAT.binaryValue (b :: u) ≠ 0 := by
      intro h0
      simp only [SAT.binaryValue] at h0
      have hu0 : SAT.binaryValue u = 0 := by omega
      rw [hu0] at ih
      have hnil : u = [] := ih.symm
      subst hnil
      cases b
      · simp at h
      · simp [SAT.binaryValue] at h0
    rw [natBits_of_ne_zero hpos]
    have e : SAT.binaryValue (b :: u) = b.toNat + 2 * SAT.binaryValue u := rfl
    have h1 : SAT.binaryValue (b :: u) / 2 = SAT.binaryValue u := by
      rw [e]
      cases b
      · simp
      · simp only [Bool.toNat_true]
        omega
    have h2 : decide (SAT.binaryValue (b :: u) % 2 = 1) = b := by
      rw [e]
      cases b <;> simp
    rw [h1, h2, ih]

/-- Canonical numerals have no trailing zero. -/
theorem getLast?_natBits (n : Nat) : (natBits n).getLast? ≠ some false := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · subst h
      simp
    · rw [natBits_of_ne_zero h]
      have ih' := ih (n / 2) (by omega)
      cases hq : natBits (n / 2) with
      | nil =>
        have h0 : n / 2 = 0 := by
          have := binaryValue_natBits (n / 2)
          rw [hq] at this
          exact this.symm
        have h1 : n % 2 = 1 := by omega
        simp [h1]
      | cons a u =>
        rw [hq] at ih'
        rwa [List.getLast?_cons_cons]

/-- `u` is a canonical binary numeral: it has no trailing zero. -/
def isNat (u : Word) : Bool := u.getLast? != some false

theorem isNat_iff {u : Word} : isNat u = true ↔ ∃ v, u = natBits v := by
  constructor
  · intro h
    exact ⟨SAT.binaryValue u, (natBits_binaryValue (by simpa [isNat] using h)).symm⟩
  · rintro ⟨v, rfl⟩
    simpa [isNat] using getLast?_natBits v

@[simp] theorem isNat_natBits (v : Nat) : isNat (natBits v) = true := isNat_iff.mpr ⟨v, rfl⟩

theorem natBits_injective {m n : Nat} (h : natBits m = natBits n) : m = n := by
  have := congrArg SAT.binaryValue h
  simpa using this

/-- `r` has the form `true :: natBits v`. -/
def solOut (r : Word) : Bool := r.head? == some true && isNat r.tail

theorem solOut_iff {r : Word} : solOut r = true ↔ ∃ v, r = true :: natBits v := by
  constructor
  · intro h
    simp only [solOut, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨v, hv⟩ := isNat_iff.mp h.2
    refine ⟨v, ?_⟩
    cases r with
    | nil => simp at h
    | cons b r =>
      simp only [List.head?_cons, Option.some.injEq, List.tail_cons] at h hv
      rw [h.1, hv]
  · rintro ⟨v, rfl⟩
    simp [solOut]

/-- The value of an output of the form `true :: natBits v`. -/
theorem solOut_eq {r : Word} (h : solOut r = true) :
    r = true :: natBits (SAT.binaryValue r.tail) := by
  obtain ⟨v, rfl⟩ := solOut_iff.mp h
  simp

/-! ### Padding -/

theorem binaryValue_replicate_false (k : Nat) :
    SAT.binaryValue (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, SAT.binaryValue, ih]

theorem binaryValue_append_replicate_false (u : Word) (k : Nat) :
    SAT.binaryValue (u ++ List.replicate k false) = SAT.binaryValue u := by
  induction u with
  | nil => simpa [SAT.binaryValue] using binaryValue_replicate_false k
  | cons b u ih => simp [SAT.binaryValue, ih]

/-- The two words padded with zeros to the same length, digit by digit. -/
def zipBits (u v : Word) : List (Bool × Bool) :=
  (u ++ List.replicate (v.length - u.length) false).zip
    (v ++ List.replicate (u.length - v.length) false)

theorem length_zipBits (u v : Word) : (zipBits u v).length = max u.length v.length := by
  simp only [zipBits, List.length_zip, List.length_append, List.length_replicate]
  omega

theorem binaryValue_map_fst_zipBits (u v : Word) :
    SAT.binaryValue ((zipBits u v).map Prod.fst) = SAT.binaryValue u := by
  rw [zipBits, List.map_fst_zip (by simp only [List.length_append, List.length_replicate]; omega),
    binaryValue_append_replicate_false]

theorem binaryValue_map_snd_zipBits (u v : Word) :
    SAT.binaryValue ((zipBits u v).map Prod.snd) = SAT.binaryValue v := by
  rw [zipBits, List.map_snd_zip (by simp only [List.length_append, List.length_replicate]; omega),
    binaryValue_append_replicate_false]

/-! ### Addition -/

/-- Ripple-carry addition of the two numerals given digit by digit, with incoming carry. -/
def addPairs : Bool → List (Bool × Bool) → Word
  | carry, [] => [carry]
  | carry, p :: ps =>
    (p.1 != (p.2 != carry)) :: addPairs ((p.1 && p.2) || (carry && (p.1 || p.2))) ps

theorem length_addPairs (carry : Bool) (ps : List (Bool × Bool)) :
    (addPairs carry ps).length = ps.length + 1 := by
  induction ps generalizing carry with
  | nil => rfl
  | cons p ps ih => simp [addPairs, ih]

theorem binaryValue_addPairs (carry : Bool) (ps : List (Bool × Bool)) :
    SAT.binaryValue (addPairs carry ps) =
      carry.toNat + SAT.binaryValue (ps.map Prod.fst) + SAT.binaryValue (ps.map Prod.snd) := by
  induction ps generalizing carry with
  | nil => simp [addPairs, SAT.binaryValue]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp only [addPairs, SAT.binaryValue, ih, List.map_cons]
    cases a <;> cases b <;> cases carry <;> simp <;> omega

/-- The sum of two binary numerals. -/
def addBits (u v : Word) : Word := addPairs false (zipBits u v)

@[simp] theorem binaryValue_addBits (u v : Word) :
    SAT.binaryValue (addBits u v) = SAT.binaryValue u + SAT.binaryValue v := by
  simp [addBits, binaryValue_addPairs, binaryValue_map_fst_zipBits, binaryValue_map_snd_zipBits]

theorem length_addBits (u v : Word) : (addBits u v).length = max u.length v.length + 1 := by
  rw [addBits, length_addPairs, length_zipBits]

/-- Both possible carries at once, to compute `addPairs` by structural recursion. -/
theorem PT.addPairs_both :
    PT (fun ps : List (Bool × Bool) => (addPairs false ps, addPairs true ps)) := by
  refine PT.of_listRec (g := fun (_ : List (Bool × Bool)) t => (addPairs false t, addPairs true t))
    (base := fun _ => ([false], [true]))
    (step := fun _ p _ r =>
      ((p.1 != (p.2 != false)) :: (if (p.1 && p.2) || (false && (p.1 || p.2)) then r.2 else r.1),
        (p.1 != (p.2 != true)) :: (if (p.1 && p.2) || (true && (p.1 || p.2)) then r.2 else r.1)))
    (l := fun ps => ps) (by fun_prop) (by fun_prop) (by fun_prop) (fun _ => rfl) ?_
    (fun N => 4 * N + 6)
    (((PolynomialBound.constant 4).mul PolynomialBound.identity).add
      (PolynomialBound.constant 6)) ?_
  · intro _ p ps
    obtain ⟨a, b⟩ := p
    cases a <;> cases b <;> simp [addPairs]
  · intro ps suf hsuf
    have h1 := hsuf.length_le
    have h2 := length_lt_size ps
    simp only [size_prod, size_word, length_addPairs]
    omega

@[fun_prop] protected theorem PT.addBits {α : Type} [Code α] {u v : α → Word}
    (hu : PT u) (hv : PT v) : PT (fun a => addBits (u a) (v a)) := by
  have h : PT (fun ps : List (Bool × Bool) => addPairs false ps) := PT.fst PT.addPairs_both
  unfold addBits zipBits
  exact h.comp (by fun_prop)

/-! ### Multiplication by a unary number -/

/-- `n` times the numeral `w`. -/
def mulSmall : Nat → Word → Word
  | 0, _ => []
  | n + 1, w => addBits w (mulSmall n w)

@[simp] theorem binaryValue_mulSmall (n : Nat) (w : Word) :
    SAT.binaryValue (mulSmall n w) = n * SAT.binaryValue w := by
  induction n with
  | zero => simp [mulSmall, SAT.binaryValue]
  | succ n ih => simp [mulSmall, ih, Nat.succ_mul, Nat.add_comm]

theorem length_mulSmall_le (n : Nat) (w : Word) : (mulSmall n w).length ≤ n + w.length := by
  induction n with
  | zero => simp [mulSmall]
  | succ n ih =>
    rw [mulSmall, length_addBits]
    omega

protected theorem PT.mulSmall' : PT (fun p : Nat × Word => mulSmall p.1 p.2) := by
  refine PT.of_natRec (g := fun (p : Nat × Word) i => mulSmall i p.2) (base := fun _ => [])
    (step := fun p _ s => addBits p.2 s) (n := fun p => p.1) (by fun_prop) (by fun_prop)
    (by fun_prop) (fun _ => rfl) (fun _ _ => rfl) (fun N => 2 * N + 1)
    (((PolynomialBound.constant 2).mul PolynomialBound.identity).add
      (PolynomialBound.constant 1)) ?_
  intro p i hi
  have h1 := length_mulSmall_le i p.2
  simp only [size_word, size_prod, size_nat]
  omega

@[fun_prop] protected theorem PT.mulSmall {α : Type} [Code α] {n : α → Nat} {w : α → Word}
    (hn : PT n) (hw : PT w) : PT (fun a => mulSmall (n a) (w a)) :=
  PT.mulSmall'.comp (hn.pair hw)

/-! ### Comparison -/

/-- One step of the comparison, from the least significant digit: the higher digits decide
unless they are equal. -/
def leStep (s : Bool) (p : Bool × Bool) : Bool := if p.1 == p.2 then s else p.2

theorem foldl_leStep (ps : List (Bool × Bool)) (s : Bool) :
    ps.foldl leStep s = true ↔
      SAT.binaryValue (ps.map Prod.fst) < SAT.binaryValue (ps.map Prod.snd) ∨
        (SAT.binaryValue (ps.map Prod.fst) = SAT.binaryValue (ps.map Prod.snd) ∧ s = true) := by
  induction ps generalizing s with
  | nil => simp [SAT.binaryValue]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, SAT.binaryValue, leStep]
    cases a <;> cases b <;> cases s <;> simp <;> omega

/-- Comparison of binary numerals. -/
def leBits (u v : Word) : Bool := (zipBits u v).foldl leStep true

theorem leBits_iff {u v : Word} :
    leBits u v = true ↔ SAT.binaryValue u ≤ SAT.binaryValue v := by
  rw [leBits, foldl_leStep, binaryValue_map_fst_zipBits, binaryValue_map_snd_zipBits]
  simp only [and_true]
  omega

@[fun_prop] protected theorem PT.leBits {α : Type} [Code α] {u v : α → Word}
    (hu : PT u) (hv : PT v) : PT (fun a => leBits (u a) (v a)) := by
  have h : PT (fun ps : List (Bool × Bool) => ps.foldl leStep true) := by
    refine PT.foldl_of_size_le (f := fun _ s p => leStep s p) (init := fun _ => true)
      (l := fun ps => ps) (by unfold leStep; fun_prop) (by fun_prop) (by fun_prop) (fun _ => 1)
      (PolynomialBound.constant 1) ?_
    intro _ s p _
    simp
  unfold leBits zipBits
  exact h.comp (by fun_prop)

@[fun_prop] protected theorem PT.isNat {α : Type} [Code α] {u : α → Word} (hu : PT u) :
    PT (fun a => isNat (u a)) := by
  unfold isNat
  fun_prop

@[fun_prop] protected theorem PT.solOut {α : Type} [Code α] {u : α → Word} (hu : PT u) :
    PT (fun a => solOut (u a)) := by
  unfold solOut
  fun_prop

end Complexity
