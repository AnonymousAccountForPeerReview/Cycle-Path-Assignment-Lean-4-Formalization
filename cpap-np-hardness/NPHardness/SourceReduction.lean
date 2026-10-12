module

public import NPHardness.SourceSemantics
public import NPHardness.GlobalReduction

/-! Doubling the literal of a unit clause (`expandSourceUnit`) preserves the value
of every clause and formula and gives clauses of two or three literals. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def expandSourceUnit : Clause → Clause
  | [l] => [l,l]
  | c => c

theorem expandSourceUnit_eval (a : Assignment) (c : Clause) :
    evalClause a (expandSourceUnit c) = evalClause a c := by
  cases c with
  | nil => rfl
  | cons l ls => cases ls with
    | nil => simp [expandSourceUnit]
    | cons r rs => rfl

theorem expandSourceUnits_eval (a : Assignment) (f : CNF) :
    evalCNF a (f.map expandSourceUnit) = evalCNF a f := by
  induction f with
  | nil => rfl
  | cons c f ih => simp only [List.map_cons,evalCNF_cons,expandSourceUnit_eval,ih]

theorem expandSourceUnit_size {c : Clause} (hn : c ≠ []) (hc : c.length ≤ 3) :
    (expandSourceUnit c).length = 2 ∨ (expandSourceUnit c).length = 3 := by
  cases c with
  | nil => exact False.elim (hn rfl)
  | cons l ls => cases ls with
    | nil => exact Or.inl rfl
    | cons r rs =>
      change (l :: r :: rs).length = 2 ∨ (l :: r :: rs).length = 3
      simp only [List.length_cons] at *
      omega

end STACS2027
