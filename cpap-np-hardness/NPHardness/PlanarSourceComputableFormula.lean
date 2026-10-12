module

public import NPHardness.PlanarSourceComputableComb
public import NPHardness.PlanarSourceFromFormula

/-!
The occurrence-ring construction retaining an input embedding as executable
data. No `Classical.choose` selects a rotation. The implementation uses the
source node permutation directly. This closes the distinction between an
existential planar witness and an executable reference construction, but does
not assert that the construction has been compiled to a bounded-time machine.
-/

@[expose] public section
namespace STACS2027.PlanarSource.ComputableFormula
open Complexity Complexity.SAT Complexity.Planar
open STACS2027.PlanarSource.Embedding STACS2027.PlanarSource.Embedding.BipartiteRotation
open STACS2027.PlanarSource.Formula STACS2027.PlanarSource.FromFormula
open STACS2027.PlanarSource.ComputableComb

/-- Rotation data, retaining the source hypermap rather than choosing an
embedding from a proposition. The separate dimension makes reindexing exact. -/
structure RotationData (f : CNF) (E : Nat) where
  rotation : BipartiteRotation E
  clause : Fin E → Fin f.length
  original_planar : rotation.original.Planar
  variable_orbit : ∀ i j, STACS2027.PlanarGluing.Reaches rotation.varRot.toFun i j ↔
    variableAt f i.val = variableAt f j.val
  clause_orbit : ∀ i j, STACS2027.PlanarGluing.Reaches rotation.clause.toFun i j ↔
    clause i = clause j
  clause_endpoint : ∀ i : Fin E,
    ((incidenceGraph f)[i.val]?).map Prod.snd = some (Sum.inr (clause i).val)

/-- Read the two rotations directly from a supplied incidence embedding. -/
def edgeData (f : CNF) (G : GraphEmbedding (incidenceGraph f)) :
    RotationData f (incidenceGraph f).length := by
  let hpar := incidence_node_parity (incidenceGraph f)
    (fun i => variableAt f i.val) (fun i => clauseAt f i.val)
    (incidence_labels f) G.map G.node_orbit
  let B := fromHypermap G.map hpar
  let clause : Fin (incidenceGraph f).length → Fin f.length :=
    fun i => ⟨clauseAt f i.val, (incidence_second f i).2⟩
  refine ⟨B, clause, ?_, ?_, ?_, ?_⟩
  · rw [show B.original = G.map from fromHypermap_original G.map hpar G.edge_pair]
    exact G.planar
  · intro i j
    change STACS2027.PlanarGluing.Reaches (blockRotation G.map hpar 0).toFun i j ↔ _
    rw [blockRotation_orbit, G.node_orbit, halfEdgeEnd_d2_zero, halfEdgeEnd_d2_zero,
      incidence_labels f, incidence_labels f]
    simp
  · intro i j
    change STACS2027.PlanarGluing.Reaches (blockRotation G.map hpar 1).toFun i j ↔ _
    rw [blockRotation_orbit, G.node_orbit, halfEdgeEnd_d2_one, halfEdgeEnd_d2_one,
      incidence_labels f, incidence_labels f]
    simp only [Option.some.injEq, Sum.inr.injEq]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  · intro i
    simp only [List.getElem?_eq_getElem i.isLt, Option.map_some]
    exact congrArg some (incidence_second f i).1

/-- The successor simply reads the original variable dart and divides by two. -/
theorem edgeData_next (f : CNF) (G : GraphEmbedding (incidenceGraph f))
    (i : Fin (incidenceGraph f).length) :
    ((edgeData f G).rotation.varRot.toFun i).val = (G.map.node (d2 i 0)).val / 2 := rfl

/-- Transport from the incidence edge count to the identical literal count. -/
def formulaData (f : CNF) (G : GraphEmbedding (incidenceGraph f)) :
    RotationData f f.flatten.length :=
  (incidenceGraph_length_flatten f) ▸ edgeData f G

def output (f : CNF) (G : GraphEmbedding (incidenceGraph f)) : CNF :=
  embeddedRingFormula f (formulaData f G).rotation

theorem formulaData_variable_orbit (f : CNF) (G : GraphEmbedding (incidenceGraph f))
    (i j : Fin f.flatten.length) :
    STACS2027.PlanarGluing.Reaches (formulaData f G).rotation.varRot.toFun i j ↔
      (f.flatten[i.val]).var = (f.flatten[j.val]).var := by
  simpa only [variableAt_get] using (formulaData f G).variable_orbit i j

theorem output_planar (f : CNF) (G : GraphEmbedding (incidenceGraph f)) :
    PlanarGraph (incidenceGraph (output f G)) := by
  let D := formulaData f G
  apply embeddedRingFormula_planar f D.rotation D.clause
  · intro i
    have hi : i.val < (incidenceGraph f).length := by
      rw [incidenceGraph_length_flatten]; exact i.isLt
    have he := D.clause_endpoint i
    simpa only [List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] using he
  · exact D.rotation.expandedEdges_planar D.clause D.clause_orbit D.original_planar

theorem output_bounded {f : CNF} (G : GraphEmbedding (incidenceGraph f))
    (hlen : ∀ c ∈ f, c.length = 2 ∨ c.length = 3) : BoundedOccurrence (output f G) :=
  embeddedRingFormula_bounded hlen (formulaData f G).rotation

theorem output_satisfiable (f : CNF) (G : GraphEmbedding (incidenceGraph f)) :
    Satisfiable (output f G) ↔ Satisfiable f :=
  embeddedRingFormula_satisfiable f (formulaData f G).rotation (formulaData_variable_orbit f G)

/-- A supplied explicit embedding yields a concrete planar Definition 7
formula with equivalent satisfiability. No existential elimination into data
and no target-planarity premise occur in this construction. -/
theorem output_correct {f : CNF} (G : GraphEmbedding (incidenceGraph f))
    (hlen : ∀ c ∈ f, c.length = 2 ∨ c.length = 3) :
    BoundedOccurrence (output f G) ∧ PlanarGraph (incidenceGraph (output f G)) ∧
      (Satisfiable (output f G) ↔ Satisfiable f) :=
  ⟨output_bounded G hlen, output_planar f G, output_satisfiable f G⟩

end STACS2027.PlanarSource.ComputableFormula
