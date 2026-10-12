module

public import NPHardness.OrientedGlobalGraph

/-! Distinct variable gadgets, and distinct clause gadgets, have disjoint
vertex images. These are concrete facts about formulaGraph, not promises
assumed of an unspecified reduction. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

theorem formulaGraph_clause_vertices_disjoint {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {i j : Nat} (hi : i < (placeFormula [] f).length) (hj : j < (placeFormula [] f).length)
    (hne : i ≠ j) {u v : Nat} (hu : u < gadgetWidth k) (hv : v < gadgetWidth k) :
    clauseVertex (gadgetWidth k) (variableBound f) i (placeFormula [] f)[i] u ≠
      clauseVertex (gadgetWidth k) (variableBound f) j (placeFormula [] f)[j] v := by
  intro he
  have hci := List.getElem_mem hi
  have hcj := List.getElem_mem hj
  have hw : 7 ≤ gadgetWidth k := by have := gadgetWidth_ge k; omega
  cases hau : attachmentAt (placeFormula [] f)[i] u with
  | none =>
    cases hav : attachmentAt (placeFormula [] f)[j] v with
    | none =>
      have htag := (blockVertex_injective hu hv (by simpa [clauseVertex, hau, hav] using he)).1
      exact hne (by omega)
    | some ps =>
      obtain ⟨p, side⟩ := ps
      obtain ⟨a, _, hap, _⟩ := attachmentAt_spec.mp hav
      have hpm := List.mem_of_getElem? hap
      have hpv := (hf.placed_clause_bounds hcj p hpm).1
      have hep : variableEndpoint p.port (orientSide p side) < gadgetWidth k :=
        Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
      have htag := (blockVertex_injective hu hep (by simpa [clauseVertex, hau, hav] using he)).1
      omega
  | some ps =>
    obtain ⟨p, side⟩ := ps
    obtain ⟨a, _, hap, _⟩ := attachmentAt_spec.mp hau
    have hpm := List.mem_of_getElem? hap
    have hpv := (hf.placed_clause_bounds hci p hpm).1
    have hep : variableEndpoint p.port (orientSide p side) < gadgetWidth k :=
      Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
    cases hav : attachmentAt (placeFormula [] f)[j] v with
    | none =>
      have htag := (blockVertex_injective hep hv (by simpa [clauseVertex, hau, hav] using he)).1
      omega
    | some qs =>
      obtain ⟨q, side'⟩ := qs
      obtain ⟨b, _, hbq, _⟩ := attachmentAt_spec.mp hav
      have hqm := List.mem_of_getElem? hbq
      have heq : variableEndpoint q.port (orientSide q side') < gadgetWidth k :=
        Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
      obtain ⟨hvar, hend⟩ := blockVertex_injective hep heq (by simpa [clauseVertex, hau, hav] using he)
      have hport := (variableEndpoint_injective (hf.placed_clause_bounds hci p hpm).2
        (hf.placed_clause_bounds hcj q hqm).2 _ _ hend).1
      exact hf.placed_clauses_keys_disjoint hi hj hne hpm hqm (Prod.ext hvar hport)

theorem formulaGraph_clause_edges_disjoint {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {i j : Nat} (hi : i < (placeFormula [] f).length) (hj : j < (placeFormula [] f).length)
    (hne : i ≠ j) :
    ∀ e ∈ placedClauseGraph k (variableBound f) i (placeFormula [] f)[i],
      e ∉ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j] :=
  mapGraph_disjoint (clauseGraph_below k _) (clauseGraph_below k _) _ _
    (fun _ hu _ hv => formulaGraph_clause_vertices_disjoint hf hi hj hne hu hv)

end STACS2027.Oriented
