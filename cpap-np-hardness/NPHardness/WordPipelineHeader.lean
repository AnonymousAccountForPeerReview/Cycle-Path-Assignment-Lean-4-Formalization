module

public import NPHardness.WordPipelineCore

/-! The constructor's dimension header is computed by this charged scan.
This prevents pipeline composition from hiding a `variableBound` traversal in
the transition that launches graph construction. -/

@[expose] public section
namespace STACS2027.WordPipeline.Header
open Complexity.SAT

inductive State where
  | formula (remaining : CNF) (maximum : Nat)
  | clause (remaining : Clause) (tail : CNF) (maximum : Nat)
  | done (maximum : Nat)

def step : State → State
  | .formula [] n => .done n
  | .formula (c::f) n => .clause c f n
  | .clause [] f n => .formula f n
  | .clause (l::c) f n => .clause c f (max (l.var+1) n)
  | .done n => .done n

theorem run_clause (c : Clause) (f : CNF) (n : Nat) :
    Runs step (c.length+1) (.clause c f n) (.formula f (max (clauseBound c) n)) := by
  induction c generalizing n with
  | nil => simpa [step,clauseBound] using Runs.next (Runs.refl (State.formula f n))
  | cons l c ih =>
    have h := Runs.next (s := State.clause (l::c) f n) (ih (max (l.var+1) n))
    simpa [step,clauseBound,Nat.max_assoc,Nat.max_comm,Nat.max_left_comm] using h

theorem run_formula (f : CNF) (n : Nat) :
    Runs step (f.flatten.length+2*f.length+1) (.formula f n) (.done (max (variableBound f) n)) := by
  induction f generalizing n with
  | nil => simpa [step,variableBound] using Runs.next (Runs.refl (State.done n))
  | cons c f ih =>
    have h := Runs.next (s := State.formula (c::f) n)
      ((run_clause c f n).trans (ih (max (clauseBound c) n)))
    have ht : c.length+1+(f.flatten.length+2*f.length+1)+1 =
        (c::f).flatten.length+2*(c::f).length+1 := by
      simp only [List.flatten_cons,List.length_append,List.length_cons]
      omega
    rw [ht] at h
    simpa [step,variableBound,Nat.max_assoc,Nat.max_comm,Nat.max_left_comm] using h

theorem computes_bound (f : CNF) :
    Runs step (f.flatten.length+2*f.length+1) (.formula f 0) (.done (variableBound f)) := by
  simpa using run_formula f 0

end STACS2027.WordPipeline.Header
