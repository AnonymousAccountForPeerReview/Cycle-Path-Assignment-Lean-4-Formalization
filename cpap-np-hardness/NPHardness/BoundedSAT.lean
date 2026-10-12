module

public import Complexity.SAT

/-!
Definition 7 of the STACS 2027 manuscript, without its distinct-variable
clause (`Paper.LeOneLeTwoCNF` adds it), using the foundation's
list-of-clauses representation. Literal occurrences are counted with multiplicity.
This is the registered `(≤1,≤2)`-CNF restriction (`boundedOccurrence_iff_registered`).
-/

@[expose] public section

namespace STACS2027
open Complexity.SAT

def occurrences (f : CNF) (v : Nat) (positive : Bool) : Nat :=
  (f.flatten.filter fun l => l.var == v && l.positive == positive).length

/-- Exact clause-size and signed-occurrence restrictions in Definition 7. -/
def BoundedOccurrence (f : CNF) : Prop :=
  (∀ c ∈ f, c.length = 2 ∨ c.length = 3) ∧
  (∀ v, occurrences f v true ≤ 1) ∧
  (∀ v, occurrences f v false ≤ 2)

theorem BoundedOccurrence.isThreeCNF {f : CNF} (h : BoundedOccurrence f) :
    IsThreeCNF f := by
  intro c hc
  rcases h.1 c hc with h | h <;> omega

end STACS2027
