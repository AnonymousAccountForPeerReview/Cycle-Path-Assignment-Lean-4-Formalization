module

public import NPHardness.OrientedGlobalSeparation

/-! No edge between a variable copy and a clause copy is shared accidentally:
shared edges are exactly allocated literal ports. -/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

theorem variable_clause_vertex_intersection {width n j v a b : Nat} {c : List PlacedLiteral}
    (hw : 7 ≤ width) (hv : v < n) (ha : a < width) (hb : b < width)
    (he : blockVertex width v a = clauseVertex width n j c b) :
    ∃ p side, attachmentAt c b = some (p,side) ∧ v = p.literal.var ∧ a = variableEndpoint p.port (orientSide p side) := by
  cases h : attachmentAt c b with
  | none =>
    have ht := (blockVertex_injective ha hb (by simpa [clauseVertex, h] using he)).1
    omega
  | some ps =>
    obtain ⟨p, side⟩ := ps
    have hep := Nat.lt_of_lt_of_le (variableEndpoint_bound p.port (orientSide p side)) hw
    have hx := blockVertex_injective ha hep (by simpa [clauseVertex, h] using he)
    exact ⟨p, side, rfl, hx⟩

theorem formulaGraph_shared_edge {k : Nat} {f : CNF} {v j : Nat}
    (hv : v < variableBound f) (hj : j < (placeFormula [] f).length) {e : Edge}
    (heV : e ∈ placedVariableGraph k v)
    (heC : e ∈ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j]) :
    ∃ i p, i < 3 ∧ (placeFormula [] f)[j][i]? = some p ∧ v = p.literal.var ∧
      e = mapEdge (blockVertex (gadgetWidth k) v)
        (edge (variableEndpoint p.port false) (variableEndpoint p.port true)) := by
  let c := (placeFormula [] f)[j]
  obtain ⟨de, hd, hde⟩ := List.mem_map.mp heV
  obtain ⟨ce, hc, hce⟩ := List.mem_map.mp heC
  have hbV := variableGraph_below k de hd
  have hbC := clauseGraph_below k c ce hc
  have hw : 7 ≤ gadgetWidth k := by have := gadgetWidth_ge k; omega
  have heq : edge (blockVertex (gadgetWidth k) v de.1) (blockVertex (gadgetWidth k) v de.2) =
      edge (clauseVertex (gadgetWidth k) (variableBound f) j c ce.1)
        (clauseVertex (gadgetWidth k) (variableBound f) j c ce.2) := hde.trans hce.symm
  have ha : ∃ p a, attachmentAt c ce.1 = some (p,a) ∧ v = p.literal.var := by
    rcases (edge_eq_iff ..).mp heq with ⟨h1, _⟩ | ⟨_, h1⟩
    · obtain ⟨p,a,hp,hvar,_⟩ := variable_clause_vertex_intersection hw hv hbV.1 hbC.1 h1
      exact ⟨p,a,hp,hvar⟩
    · obtain ⟨p,a,hp,hvar,_⟩ := variable_clause_vertex_intersection hw hv hbV.2 hbC.1 h1
      exact ⟨p,a,hp,hvar⟩
  have hb : ∃ q b, attachmentAt c ce.2 = some (q,b) := by
    rcases (edge_eq_iff ..).mp heq with ⟨_, h2⟩ | ⟨h2, _⟩
    · obtain ⟨q,b,hq,_,_⟩ := variable_clause_vertex_intersection hw hv hbV.2 hbC.2 h2
      exact ⟨q,b,hq⟩
    · obtain ⟨q,b,hq,_,_⟩ := variable_clause_vertex_intersection hw hv hbV.1 hbC.2 h2
      exact ⟨q,b,hq⟩
  obtain ⟨p,a,hp,hvar⟩ := ha
  obtain ⟨q,b,hq⟩ := hb
  have hm := clauseGraph_attachment_edge hc hp hq
  have hports : ∃ i : Fin 3, ce = edge (clauseEndpoint i.val false) (clauseEndpoint i.val true) ∧
      ce.1 = clauseEndpoint i.val false :=
    (by decide : ∀ e ∈ clausePorts, ∃ i : Fin 3,
      e = edge (clauseEndpoint i.val false) (clauseEndpoint i.val true) ∧ e.1 = clauseEndpoint i.val false) ce hm
  obtain ⟨i, heport, hleft⟩ := hports
  rw [hleft, attachmentAt_endpoint i.isLt false] at hp
  have hcp : c[i.val]? = some p := by
    cases h : c[i.val]? with
    | none => simp [h] at hp
    | some r =>
      have hsame : r = p := by simpa [h] using congrArg (Option.map Prod.fst) hp
      simp [hsame]
  refine ⟨i.val, p, i.isLt, hcp, hvar, ?_⟩
  rw [← hce, heport, mapped_attachment_edge i.isLt hcp, ← hvar]

end STACS2027.Oriented
