module

public import NPHardness.PlanarSourceVariableRotation
public import NPHardness.PlanarAssemblySourceRule

/-! Assemble the actual occurrence-ring source with the explicit sign-only
endpoint rule. The variable predecessor is proved by the concrete role table;
only the source clause rotation remains as the local input here. -/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar PlanarGluing PlanarAssembly
open Embedding Embedding.BipartiteRotation

theorem ringFormulaGraph_planar_of_odd_predecessor (k:Nat) (f:CNF)
    (hlen:∀c∈f,c.length=2∨c.length=3)
    (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (clause:Fin f.flatten.length→Fin f.length)
    (hc:∀i:Fin f.flatten.length,
      ((incidenceGraph f)[i.val]'(by rw [incidenceGraph_length_flatten];exact i.isLt)).2=Sum.inr (clause i).val)
    (horbit:∀i j,Reaches B.clause.toFun i j ↔ clause i=clause j)
    (hp:B.original.Planar)
    (hodd:∀d:Fin (2*(placeFormula [] (ringFormula f (nextIndex B) signs)).flatten.length),
      d.val%2≠0 →
      sourcePortNumber (ringFormula f (nextIndex B) signs)
        ((placedRingMap f B signs).face ((placedRingMap f B signs).edge d))=
      if sourceForward signs (ringFormula f (nextIndex B) signs) d then
        (sourcePortNumber (ringFormula f (nextIndex B) signs) d+1)%
          sourcePortCount (ringFormula f (nextIndex B) signs) d
      else (sourcePortNumber (ringFormula f (nextIndex B) signs) d+
          sourcePortCount (ringFormula f (nextIndex B) signs) d-1)%
          sourcePortCount (ringFormula f (nextIndex B) signs) d) :
    PlanarGraph (orientedFormulaGraph (sourceEndpointChoices signs) k (ringFormula f (nextIndex B) signs)) := by
  apply orientedFormulaGraph_planar_source_rule k
    (ringFormula_bounded hlen B.varRot (nextIndex B) signs (nextIndex_at B)) signs
    (placedRingMap f B signs)
  · intro d
    exact Fin.ext (placedRingMap_edge f B signs d)
  · exact occurrence_node_semantics _ _ (placedRingMap_nodes f B signs clause hc horbit)
  · exact placedRingMap_planar f B signs hp
  · intro d
    by_cases hd:d.val%2=0
    · exact placedRingMap_even_predecessor f B signs d hd
    · exact hodd d hd

end STACS2027.PlanarSource.Formula
