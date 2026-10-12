module

public import NPHardness.OrientedVertexGluing
public import NPHardness.GraphRelabel

/-!
The actual formula-to-graph map. Each variable occupies its own vertex block.
Each clause occupies a new block except at literal-port endpoints, which are
identified with the occurrence's allocated variable port. Repeated edge-list
entries denote the same undirected edge, as in the existing Graph semantics.
This module proves that every placed gadget is a subgraph of the result.
-/

@[expose] public section
namespace STACS2027.Oriented

variable [Orientation]

set_option linter.unusedSectionVars false
open Complexity.SAT

def placedClauseGraph (k n j : Nat) (c : List PlacedLiteral) : Graph :=
  mapGraph (clauseVertex (gadgetWidth k) n j c) (clauseGraph k c)

def formulaGraph (k : Nat) (f : CNF) : Graph :=
  ((List.range (variableBound f)).flatMap (placedVariableGraph k)) ++
    ((placeFormula [] f).mapIdx (fun j c => placedClauseGraph k (variableBound f) j c)).flatten

theorem formulaGraph_variable_contains (k : Nat) (f : CNF) {v : Nat} (hv : v < variableBound f) :
    placedVariableGraph k v ⊆ formulaGraph k f := by
  intro e he
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, he⟩

theorem formulaGraph_clause_contains (k : Nat) (f : CNF) (j : Nat)
    (hj : j < (placeFormula [] f).length) :
    placedClauseGraph k (variableBound f) j (placeFormula [] f)[j] ⊆ formulaGraph k f := by
  intro e he
  apply List.mem_append_right
  apply List.mem_flatten.mpr
  exact ⟨_, List.mem_mapIdx.mpr ⟨j, hj, rfl⟩, he⟩

theorem mapped_attachment_edge {width n j : Nat} {c : List PlacedLiteral}
    {i : Nat} (hi : i < 3) {p : PlacedLiteral} (hp : c[i]? = some p) :
    mapEdge (clauseVertex width n j c) (edge (clauseEndpoint i false) (clauseEndpoint i true)) =
      mapEdge (blockVertex width p.literal.var) (edge (variableEndpoint p.port false) (variableEndpoint p.port true)) := by
  rw [mapEdge_edge, mapEdge_edge, clauseVertex_attachment hi hp false, clauseVertex_attachment hi hp true]
  unfold orientSide
  cases Orientation.flip p
  · rfl
  · exact edge_comm _ _

end STACS2027.Oriented
