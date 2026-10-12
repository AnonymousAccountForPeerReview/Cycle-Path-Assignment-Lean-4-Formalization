module

public import NPHardness.OccurrencePorts

/-!
Random-access implementation of occurrence allocation. `CounterMemory` is
the semantic contents of signed-literal cells; an update is one RAM store,
not evaluation of a chain of Lean function closures. The refinement below
connects this implementation to the existing, history-counting specification.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

abbrev CounterMemory := Literal → Nat

def incrementCounter (m : CounterMemory) (l : Literal) : CounterMemory :=
  fun q => if q = l then m l + 1 else m q

def historyMemory (past : List Literal) : CounterMemory := past.count

def allocateLiterals (m : CounterMemory) : List Literal → List PlacedLiteral × CounterMemory
  | [] => ([], m)
  | l :: ls =>
    let rest := allocateLiterals (incrementCounter m l) ls
    (⟨l,m l⟩ :: rest.1, rest.2)

def allocateFormula (m : CounterMemory) : CNF → List (List PlacedLiteral) × CounterMemory
  | [] => ([], m)
  | c :: f =>
    let placed := allocateLiterals m c
    let rest := allocateFormula placed.2 f
    (placed.1 :: rest.1, rest.2)

theorem increment_history (past : List Literal) (l : Literal) :
    incrementCounter (historyMemory past) l = historyMemory (past ++ [l]) := by
  funext q
  by_cases h : q = l
  · subst q
    simp [incrementCounter, historyMemory, List.count_append]
  · have h' : l ≠ q := Ne.symm h
    simp [incrementCounter, historyMemory, List.count_append, h, h']

theorem allocateLiterals_refines (past ls : List Literal) :
    allocateLiterals (historyMemory past) ls =
      (placeLiterals past ls, historyMemory (past ++ ls)) := by
  induction ls generalizing past with
  | nil => simp [allocateLiterals, placeLiterals]
  | cons l ls ih =>
    simp [allocateLiterals, increment_history, ih, placeLiterals, historyMemory,
      List.append_assoc]

theorem allocateFormula_refines (past : List Literal) (f : CNF) :
    allocateFormula (historyMemory past) f =
      (placeFormula past f, historyMemory (past ++ f.flatten)) := by
  induction f generalizing past with
  | nil => simp [allocateFormula, placeFormula]
  | cons c f ih =>
    simp [allocateFormula, allocateLiterals_refines, ih, placeFormula, List.append_assoc]

theorem allocateLiterals_length (m : CounterMemory) (ls : List Literal) :
    (allocateLiterals m ls).1.length = ls.length := by
  induction ls generalizing m with
  | nil => rfl
  | cons l ls ih => simp [allocateLiterals, ih]

end STACS2027
