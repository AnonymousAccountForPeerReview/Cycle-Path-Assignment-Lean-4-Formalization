module

public import NPHardness.OrientedGlobalReduction
public import NPHardness.OrientedVertexGluing

/-!
An explicit, reusable interface for occurrence-dependent endpoint choices.
All Boolean choices are admitted: semantic correctness and cycle localization
are proved uniformly, so choosing the signs later from an incidence embedding
adds no semantic proof obligation. Planarity and the time needed to compute
those choices are separate obligations, not hypotheses hidden in this API.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def EndpointChoices := PlacedLiteral → Bool

def orientedClauseVertex (flips : EndpointChoices) (width n j : Nat)
    (c : List PlacedLiteral) (v : Nat) : Nat :=
  @Oriented.clauseVertex ⟨flips⟩ width n j c v

def orientedPlacedClauseGraph (flips : EndpointChoices) (k n j : Nat)
    (c : List PlacedLiteral) : Graph :=
  @Oriented.placedClauseGraph ⟨flips⟩ k n j c

def orientedFormulaGraph (flips : EndpointChoices) (k : Nat) (f : CNF) : Graph :=
  @Oriented.formulaGraph ⟨flips⟩ k f

def orientedGlobalReductionGraph (flips : EndpointChoices) (k : Nat) (f : CNF) : Graph :=
  @Oriented.globalReductionGraph ⟨flips⟩ k f

theorem orientedClauseVertex_injective (flips : EndpointChoices)
    {width n j : Nat} {c : List PlacedLiteral}
    (hw : 7 ≤ width) (hc : (c.map PlacedLiteral.key).Nodup)
    (hb : ∀ p ∈ c, p.literal.var < n ∧ p.port < 3)
    {u v : Nat} (hu : u < width) (hv : v < width)
    (he : orientedClauseVertex flips width n j c u =
      orientedClauseVertex flips width n j c v) : u = v := by
  letI : Oriented.Orientation := ⟨flips⟩
  exact Oriented.clauseVertex_injective hw hc hb hu hv he

theorem orientedFormulaGraph_cycle_local (flips : EndpointChoices)
    {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) {c : Cycle}
    (hc : IsCycle (orientedFormulaGraph flips k f) k c) :
    (∃ v, v < variableBound f ∧ IsCycle (placedVariableGraph k v) k c) ∨
    (∃ j : Fin (placeFormula [] f).length,
      IsCycle (orientedPlacedClauseGraph flips k (variableBound f) j.val
        (placeFormula [] f)[j.val]) k c) := by
  letI : Oriented.Orientation := ⟨flips⟩
  exact Oriented.formulaGraph_cycle_local hk hf hd hc

theorem orientedFormulaGraph_sat_iff_assignment (flips : EndpointChoices)
    {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) :
    Satisfiable f ↔ HasAssignment (orientedFormulaGraph flips k f) k f.length := by
  letI : Oriented.Orientation := ⟨flips⟩
  exact Oriented.formulaGraph_sat_iff_assignment hk hf hd

/-- The full Definition 7 domain, with its original clause-count budget.
No distinct-variable or absence-of-tautology condition is imposed on input f. -/
theorem orientedGlobalReduction_sat_iff_assignment (flips : EndpointChoices)
    {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f) :
    Satisfiable f ↔ HasAssignment (orientedGlobalReductionGraph flips k f) k f.length := by
  letI : Oriented.Orientation := ⟨flips⟩
  exact Oriented.globalReduction_sat_iff_assignment hk hf

end STACS2027
