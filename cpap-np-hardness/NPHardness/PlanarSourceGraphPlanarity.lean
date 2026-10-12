module

public import NPHardness.PlanarSourceSignedRing
public import NPHardness.PlanarSourceClausePortRotation
public import NPHardness.PlanarSourceGraphGrid

/-! Planarity of the actual graph emitted from every registered source grid.
The endpoint rule is the executable literal-sign comparison; all local
rotations and their geometric compatibility are discharged here. -/

@[expose] public section
namespace STACS2027.PlanarSource
open Complexity Complexity.SAT Complexity.Planar PlanarGluing PlanarAssembly
open Embedding Embedding.BipartiteRotation

namespace Formula

/-- A supplied planar bipartite rotation with the natural cyclic clause order
produces the actual planar graph with the explicit sign-only endpoint rule. -/
theorem ringFormulaGraph_planar (k:Nat) (f:CNF)
    (hlen:∀c∈f,c.length=2∨c.length=3)
    (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (clause:Fin f.flatten.length→Fin f.length)
    (hc:∀i:Fin f.flatten.length,
      ((incidenceGraph f)[i.val]'(by rw [incidenceGraph_length_flatten];exact i.isLt)).2=Sum.inr (clause i).val)
    (horbit:∀i j,Reaches B.clause.toFun i j ↔ clause i=clause j)
    (hp:B.original.Planar) (hrotation:CanonicalClauseRotation f B) :
    PlanarGraph (orientedFormulaGraph (sourceEndpointChoices signs) k (ringFormula f (nextIndex B) signs)) :=
  ringFormulaGraph_planar_of_odd_predecessor k f hlen B signs clause hc horbit hp
    (placedRingMap_odd_predecessor f B signs hrotation)

end Formula

namespace Packed
open Grid

/-- The exact emitted graph is planar for every source grid and every natural
gadget parameter, including the empty grid. No orientation, embedding, or
port-order premise occurs in this exported source theorem. -/
theorem ringGrid_graph_planar (k W m:Nat) (bits:Nat→Nat→Bool×Bool) :
    let f:=gridCNF W m bits
    PlanarGraph (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k
      (Formula.ringFormula f (incidenceNext f) (Formula.sourceSigns f))) := by
  cases m with
  | zero => exact ringGrid_graph_planar_empty k W bits
  | succ m =>
    let f:=gridCNF W (m+1) bits
    let G:=ComputableComb.gridIncidenceEmbedding W (m+1) bits (by omega)
    let D:=ComputableFormula.formulaData f G
    have he:Formula.ringFormula f (incidenceNext f) (Formula.sourceSigns f)=
        Formula.ringFormula f (Formula.nextIndex D.rotation) (Formula.sourceSigns f):=by
      apply Formula.ringFormula_next_congr
      intro i hi
      exact incidenceNext_grid W (m+1) bits (by omega) ⟨i,hi⟩
    change PlanarGraph (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k
      (Formula.ringFormula f (incidenceNext f) (Formula.sourceSigns f)))
    rw [he]
    refine Formula.ringFormulaGraph_planar k f ?_ D.rotation (Formula.sourceSigns f) D.clause ?_ ?_ ?_ ?_
    · intro c hc
      have h2:2≤c.length:=by
        have h:2≤(Comb.svars c).length:=(grid_clause_ok hc).1
        simpa only [Comb.svars_length] using h
      have h3:=grid_threeCNF W (m+1) bits c hc
      omega
    · intro i
      have hi:i.val<(incidenceGraph f).length:=by
        rw [Formula.incidenceGraph_length_flatten];exact i.isLt
      have h:=D.clause_endpoint i
      simpa only [List.getElem?_eq_getElem hi,Option.map_some,Option.some.injEq] using h
    · exact D.clause_orbit
    · exact D.original_planar
    · intro i
      exact ComputableComb.gridIncidenceEmbedding_formulaData_clause_prev W (m+1) bits (by omega) i

end Packed
end STACS2027.PlanarSource
