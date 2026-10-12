module

public import NPHardness.PlanarAssemblyChooseOrder
public import NPHardness.PlanarAssemblySourceMatch
public import NPHardness.PlanarAssemblyGlobal

/-! Global planar gluing for the actual oriented formula graph. Each source
node determines a cyclic order of at most three used ports. Actual spherical
gadget embeddings are reflected when needed, then assembled on their real
edge-list darts. Endpoint flips come from the chosen boundary directions. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

theorem piecePortIndex_injective {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    (j : PieceIndex k f) (a b : Fin (pieceUsedCount k f j))
    (h : piecePortIndex hf j a=piecePortIndex hf j b) : a=b := by
  have hv := congrArg Fin.val h
  exact pieceUsedPort_injective hf j a b (Fin.ext hv)

/-- Planarity of the actual global graph for every natural gadget parameter.
The endpoint choices are constructed from spherical local embeddings ordered
by the given registered source incidence embedding. -/
theorem orientedFormulaGraph_planar_exists (k : Nat) {f : CNF}
    (hf : BoundedOccurrence f) (hp : PlanarGraph (incidenceGraph f)) :
    ∃ flips : EndpointChoices, PlanarGraph (orientedFormulaGraph flips k f) := by
  classical
  unfold PlanarGraph at hp
  rw [← placed_occurrence_count f] at hp
  obtain ⟨I,hIe,hIn,hIp⟩ := hp
  have hIedge : ∀ d, I.edge d=graphEdge d := fun d => Fin.ext (hIe d)
  have hnode := occurrence_node_semantics f I hIn
  obtain ⟨L,horder⟩ := chosenPieces_with_source_orders k hf I hnode
    (piecePortIndex hf) (piecePortIndex_injective hf)
  let C := L.choices hf
  let O := L.orderedPorts hf I hIedge hnode (piecePortIndex hf) horder (L.sourcePort_piece_match hf)
  refine ⟨C.assemblyFlips hf,?_⟩
  apply C.orientedFormulaGraph_planar_of_orderedPorts hf
    (piecesMap (ungluedFormulaPieces k f) L.maps) L.embedding L.spherical I hIp O
  intro a b hab
  exact C.sourcePort_source_nodes_separate hf L.maps I hIn a b hab

end STACS2027.PlanarAssembly
