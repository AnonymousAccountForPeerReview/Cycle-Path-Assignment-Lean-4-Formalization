module

public import NPHardness.GlobalSize

/-!
A local-word implementation of the existing padding operation.  The state
machine scans the input once to find the fresh-variable bound, constructs each
fresh two-literal clause in one fixed-size macro step, and reverses the clause
pointer list once.  In particular no transition computes `variableBound`,
appends a list, or traverses an unbounded list.

A list in a state is a pointer into an immutable linked list.  A transition
reads or allocates a bounded number of cells.  This is a pointer/word machine,
not a claim about the time taken by Lean's evaluator or the foundation's unary
input Turing machine.  The unit-propagation pass is not covered by this file.
-/

@[expose] public section
namespace STACS2027.LinearPreprocessPadding
open Complexity.SAT

def freshClauses : Nat → Nat → CNF
  | _, 0 => []
  | n, r+1 => paddingClause n :: freshClauses (n+2) r

theorem freshClauses_length (n r : Nat) : (freshClauses n r).length = r := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih => simp [freshClauses, ih]

theorem freshClauses_snoc (n r : Nat) :
    freshClauses n (r+1) = freshClauses n r ++ [paddingClause (n+2*r)] := by
  induction r generalizing n with
  | zero => simp [freshClauses]
  | succ r ih =>
    change paddingClause n :: freshClauses (n+2) (r+1) =
      (paddingClause n :: freshClauses (n+2) r) ++ [paddingClause (n+2*(r+1))]
    rw [List.cons_append, ih]
    have he : n+2+2*r = n+2*(r+1) := by omega
    rw [he]

/-- Exact equality, not just equisatisfiability, with the old padding pass. -/
theorem padFormula_eq (r : Nat) (f : CNF) :
    padFormula r f = f ++ freshClauses (variableBound f) r := by
  induction r with
  | zero => simp [padFormula, freshClauses]
  | succ r ih =>
    rw [padFormula, addPaddingClause, padFormula_variableBound, ih,
      freshClauses_snoc, List.append_assoc]

inductive State where
  | scanFormula (remaining : CNF) (maximum : Nat) (reversed : CNF)
  | scanClause (remaining : Clause) (tail : CNF) (maximum : Nat) (reversed : CNF)
  | pad (remaining nextVariable : Nat) (reversed : CNF)
  | reverse (remaining output : CNF)
  | done (output : CNF)

/-- `padding` is a read-only counter supplied to the program.  All accesses in
one transition are local; `paddingClause` allocates exactly two literal cells. -/
def step (padding : Nat) : State → State
  | .scanFormula [] n acc => .pad padding n acc
  | .scanFormula (c :: f) n acc => .scanClause c f n (c :: acc)
  | .scanClause [] f n acc => .scanFormula f n acc
  | .scanClause (l :: c) f n acc => .scanClause c f (max (l.var+1) n) acc
  | .pad 0 _n acc => .reverse acc []
  | .pad (r+1) n acc => .pad r (n+2) (paddingClause n :: acc)
  | .reverse [] acc => .done acc
  | .reverse (c :: f) acc => .reverse f (c :: acc)
  | .done f => .done f

inductive Executes (padding : Nat) : Nat → State → State → Prop where
  | refl (s) : Executes padding 0 s s
  | next {t s u} : Executes padding t (step padding s) u →
      Executes padding (t+1) s u

theorem Executes.trans {r t u s mid dest}
    (h : Executes r t s mid) (h' : Executes r u mid dest) :
    Executes r (t+u) s dest := by
  induction h with
  | refl => simpa using h'
  | next h ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Executes.next (ih h')

theorem run_clause (padding : Nat) (c : Clause) (f : CNF) (n : Nat) (acc : CNF) :
    Executes padding (c.length+1) (.scanClause c f n acc)
      (.scanFormula f (max (clauseBound c) n) acc) := by
  induction c generalizing n with
  | nil => simpa [clauseBound, step] using Executes.next (Executes.refl (.scanFormula f n acc))
  | cons l c ih =>
    have h := Executes.next (s := .scanClause (l :: c) f n acc) (ih (max (l.var+1) n))
    simpa [step, clauseBound, Nat.max_assoc, Nat.max_comm, Nat.max_left_comm,
      Nat.add_assoc] using h

theorem run_scan (padding : Nat) (f : CNF) (n : Nat) (acc : CNF) :
    Executes padding (f.flatten.length+2*f.length+1) (.scanFormula f n acc)
      (.pad padding (max (variableBound f) n) (f.reverse ++ acc)) := by
  induction f generalizing n acc with
  | nil => simpa [step, variableBound] using Executes.next (Executes.refl (.pad padding n acc))
  | cons c f ih =>
    have h := Executes.next (s := .scanFormula (c :: f) n acc) ((run_clause padding c f n (c :: acc)).trans
      (ih (max (clauseBound c) n) (c :: acc)))
    have he : c.length+1 + (f.flatten.length+2*f.length+1) + 1 =
        (c :: f).flatten.length+2*(c :: f).length+1 := by
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega
    rw [he] at h
    simpa [step, variableBound, Nat.max_assoc, Nat.max_comm, Nat.max_left_comm,
      List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using h

theorem run_pad (padding remaining n : Nat) (acc : CNF) :
    Executes padding (remaining+1) (.pad remaining n acc)
      (.reverse ((freshClauses n remaining).reverse ++ acc) []) := by
  induction remaining generalizing n acc with
  | zero => simpa [freshClauses, step] using Executes.next (Executes.refl (.reverse acc []))
  | succ r ih =>
    have h := Executes.next (s := .pad (r+1) n acc) (ih (n+2) (paddingClause n :: acc))
    simpa [step, freshClauses, List.reverse_cons, List.append_assoc, Nat.add_assoc] using h

theorem run_reverse (padding : Nat) (f acc : CNF) :
    Executes padding (f.length+1) (.reverse f acc) (.done (f.reverse ++ acc)) := by
  induction f generalizing acc with
  | nil => simpa [step] using Executes.next (Executes.refl (.done acc))
  | cons c f ih =>
    have h := Executes.next (s := .reverse (c :: f) acc) (ih (c :: acc))
    simpa [step, List.reverse_cons, List.append_assoc, Nat.add_assoc] using h

/-- Number of actual local-word transitions in the constructed run. -/
def transitionCount (padding : Nat) (f : CNF) : Nat :=
  f.flatten.length + 3*f.length + 2*padding + 3

/-- This bound is derived from a terminating run, not from output size. -/
theorem executes_padFormula (padding : Nat) (f : CNF) :
    Executes padding (transitionCount padding f) (.scanFormula f 0 [])
      (.done (padFormula padding f)) := by
  have hs := run_scan padding f 0 []
  simp only [Nat.max_zero, List.append_nil] at hs
  have hp := run_pad padding padding (variableBound f) f.reverse
  have hr := run_reverse padding ((freshClauses (variableBound f) padding).reverse ++ f.reverse) []
  have h := hs.trans (hp.trans hr)
  have he : f.flatten.length+2*f.length+1 +
      (padding+1 + (((freshClauses (variableBound f) padding).reverse ++ f.reverse).length+1)) =
      transitionCount padding f := by
    simp only [List.length_append, List.length_reverse, freshClauses_length, transitionCount]
    omega
  rw [he] at h
  simpa only [padFormula_eq, List.reverse_append, List.reverse_reverse, List.append_nil] using h

end STACS2027.LinearPreprocessPadding
