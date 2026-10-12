module

public import Complexity.Restricted.Counting

/-! Literal negation and the counts of opposite literals, used by the
occurrence rings. -/

@[expose] public section

namespace STACS2027.PlanarSource
open Complexity.SAT Complexity.Restricted

def negate (l : Literal) : Literal := ⟨l.var, !l.positive⟩

theorem opposite_counts (ls : List Literal) (v : Nat) (s : Bool) :
    (ls.map negate).count ⟨v, s⟩ + ls.count ⟨v, s⟩ = (ls.map Literal.var).count v := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    cases l with
    | mk w t =>
      by_cases hw : w = v
      · subst w
        cases t <;> cases s <;> simp_all [negate] <;> omega
      · cases t <;> cases s <;> simp_all [negate]

end STACS2027.PlanarSource
