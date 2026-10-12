module

public import NPHardness.LinearPreprocessPadding

/-!
An unrolled, bounded-clause normalization pass.  Its local-word transitions
only inspect a fixed number of literal/cons cells, test equality of words and
polarity bits, and allocate a fixed number of cells.  The list-valued state
fields denote pointers, as in `LinearPreprocessPadding`.

The output is exactly `normalizeClauses`, so its already checked semantic and
deletion theorems apply.  No unit propagation is performed or charged here.
-/

@[expose] public section
namespace STACS2027.LinearPreprocessNormalize
open Complexity.SAT

def opposite (l r : Literal) : Bool := l.var == r.var && l.positive != r.positive

theorem opposite_self (l : Literal) : opposite l l = false := by simp [opposite]

theorem opposite_comm (l r : Literal) : opposite l r = opposite r l := by
  simp only [opposite, BEq.comm, bne_comm]

theorem opposite_eq (l r : Literal) : opposite l r = (l.var == r.var && l.positive != r.positive) := rfl

/-- This decision tree has a fixed number of comparisons on every input. -/
def smallTaut : Clause → Bool
  | [a,b] => opposite a b
  | [a,b,c] => opposite a b || opposite a c || opposite b c
  | _ => false

theorem smallTaut_eq {c : Clause} (hc : c.length ≤ 3) : smallTaut c = tautological c := by
  cases c with
  | nil => rfl
  | cons a c => cases c with
    | nil => simp [smallTaut, tautological]
    | cons b c => cases c with
      | nil =>
        simp [smallTaut, tautological, ← opposite_eq, opposite_self, opposite_comm b a]
      | cons d c => cases c with
        | nil =>
          simp only [smallTaut, tautological, List.any_cons, List.any_nil,
            Bool.or_false, ← opposite_eq, opposite_self, Bool.false_or,
            opposite_comm b a, opposite_comm d a, opposite_comm d b]
          cases opposite a b <;> cases opposite a d <;> cases opposite b d <;> rfl
        | cons e c => simp only [List.length_cons] at hc; omega

def pairDistinct (a b : Literal) : Clause := if a = b then [b] else [a,b]

/-- Last occurrences are retained, exactly as by `distinctLiterals`. -/
def smallDistinct : Clause → Clause
  | [] => []
  | [a] => [a]
  | [a,b] => pairDistinct a b
  | [a,b,c] => if a = b ∨ a = c then pairDistinct b c else a :: pairDistinct b c
  | _ => []

theorem smallDistinct_eq {c : Clause} (hc : c.length ≤ 3) :
    smallDistinct c = distinctLiterals c := by
  cases c with
  | nil => rfl
  | cons a c => cases c with
    | nil => simp [smallDistinct, distinctLiterals]
    | cons b c => cases c with
      | nil => simp [smallDistinct, pairDistinct, distinctLiterals]
      | cons d c => cases c with
        | nil => simp [smallDistinct, pairDistinct, distinctLiterals]
        | cons e c => simp only [List.length_cons] at hc; omega

def normalizeOne (c : Clause) : Option Clause :=
  let d := smallDistinct c
  if smallTaut d then none else some d

theorem normalizeOne_eq {c : Clause} (hc : c.length ≤ 3) :
    normalizeOne c = if tautological (distinctLiterals c) then none else some (distinctLiterals c) := by
  have hd : (distinctLiterals c).length ≤ 3 :=
    Nat.le_trans (distinctLiterals_sublist c).length_le hc
  simp only [normalizeOne, smallDistinct_eq hc, smallTaut_eq hd]

theorem normalizeClauses_cons (c : Clause) (f : CNF) :
    normalizeClauses (c :: f) =
      if tautological (distinctLiterals c) then normalizeClauses f
      else distinctLiterals c :: normalizeClauses f := by
  cases h : tautological (distinctLiterals c) <;>
    simp [normalizeClauses, removeTautologies, h]

inductive State where
  | scan (remaining reversed : CNF)
  | reverse (remaining output : CNF)
  | done (output : CNF)

/-- Fixed-size macro steps: `normalizeOne` is a finite decision tree, not a
traversal over an arbitrary clause.  Each `scan` step consumes one clause. -/
def step : State → State
  | .scan [] acc => .reverse acc []
  | .scan (c :: f) acc =>
      match normalizeOne c with
      | none => .scan f acc
      | some d => .scan f (d :: acc)
  | .reverse [] acc => .done acc
  | .reverse (c :: f) acc => .reverse f (c :: acc)
  | .done f => .done f

inductive Executes : Nat → State → State → Prop where
  | refl (s) : Executes 0 s s
  | next {t s u} : Executes t (step s) u → Executes (t+1) s u

theorem Executes.trans {t u s mid dest}
    (h : Executes t s mid) (h' : Executes u mid dest) : Executes (t+u) s dest := by
  induction h with
  | refl => simpa using h'
  | next h ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Executes.next (ih h')

theorem run_scan (f : CNF) (hf : IsThreeCNF f) (acc : CNF) :
    Executes (f.length+1) (.scan f acc) (.reverse ((normalizeClauses f).reverse ++ acc) []) := by
  induction f generalizing acc with
  | nil =>
    have h := Executes.next (s := .scan [] acc) (Executes.refl (.reverse acc []))
    simpa [normalizeClauses, removeTautologies] using h
  | cons c f ih =>
    have hc := hf c (by simp)
    have ht : IsThreeCNF f := fun d hd => hf d (by simp [hd])
    cases h : tautological (distinctLiterals c) with
    | false =>
      have hs : step (.scan (c :: f) acc) = .scan f (distinctLiterals c :: acc) := by
        simp [step, normalizeOne_eq hc, h]
      have hh := ih ht (distinctLiterals c :: acc)
      rw [← hs] at hh
      have he := Executes.next hh
      simpa [normalizeClauses_cons, h, List.reverse_cons, List.append_assoc, Nat.add_assoc] using he
    | true =>
      have hs : step (.scan (c :: f) acc) = .scan f acc := by
        simp [step, normalizeOne_eq hc, h]
      have hh := ih ht acc
      rw [← hs] at hh
      have he := Executes.next hh
      simpa [normalizeClauses_cons, h, Nat.add_assoc] using he

theorem run_reverse (f acc : CNF) :
    Executes (f.length+1) (.reverse f acc) (.done (f.reverse ++ acc)) := by
  induction f generalizing acc with
  | nil => simpa [step] using Executes.next (Executes.refl (.done acc))
  | cons c f ih =>
    have h := Executes.next (s := .reverse (c :: f) acc) (ih (c :: acc))
    simpa [step, List.reverse_cons, List.append_assoc, Nat.add_assoc] using h

theorem executes_normalizeClauses (f : CNF) (hf : IsThreeCNF f) :
    Executes (f.length+(normalizeClauses f).length+2) (.scan f []) (.done (normalizeClauses f)) := by
  have hs := run_scan f hf []
  simp only [List.append_nil] at hs
  have hr := run_reverse (normalizeClauses f).reverse []
  have h := hs.trans hr
  have he : f.length+1 + ((normalizeClauses f).reverse.length+1) =
      f.length+(normalizeClauses f).length+2 := by simp only [List.length_reverse]; omega
  rw [he] at h
  simpa only [List.reverse_reverse, List.append_nil] using h

end STACS2027.LinearPreprocessNormalize
