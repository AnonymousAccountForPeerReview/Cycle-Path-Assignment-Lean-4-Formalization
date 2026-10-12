module

public import NPHardness.PlanarAssemblyChosenMaps
public import NPHardness.PlanarAssemblySourcePieces
public import NPHardness.PlanarAssemblyPieceOrder

/-! Simultaneously choose actual spherical local embeddings in the cyclic
orders of the registered source nodes, and assemble their first-hit data. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

def ChosenPieces.HasSourceOrders {k : Nat} {f : CNF} (L : ChosenPieces k f)
    (I : Hypermap (2*(placeFormula [] f).flatten.length))
    (hnode : ∀ a b, Reaches I.node a b ↔ occurrenceVertex f a=occurrenceVertex f b)
    (use : ∀ j : PieceIndex k f, Fin (pieceUsedCount k f j) → Fin (piecePorts k f j).length) : Prop :=
  ∀ j i, NextSelected (L j).map.face (fun t => (L j).port (use j t)) i
    ((pieceNodeIndex k f j).order I hnode i)

theorem chosenPieces_with_source_orders (k : Nat) {f : CNF} (hf : BoundedOccurrence f)
    (I : Hypermap (2*(placeFormula [] f).flatten.length))
    (hnode : ∀ a b, Reaches I.node a b ↔ occurrenceVertex f a=occurrenceVertex f b)
    (use : ∀ j : PieceIndex k f, Fin (pieceUsedCount k f j) → Fin (piecePorts k f j).length)
    (huse : ∀ j a b, use j a=use j b → a=b) :
    ∃ L : ChosenPieces k f, L.HasSourceOrders I hnode use := by
  classical
  have hex : ∀ j : PieceIndex k f, ∃ E : EmbeddingPorts (ungluedFormulaPieces k f)[j.val] (piecePorts k f j),
      ∀ i, NextSelected E.map.face (fun t => E.port (use j t)) i
        ((pieceNodeIndex k f j).order I hnode i) := by
    intro j
    obtain ⟨G,hG,hs,port,hp,he,ho⟩ := spherical_cofacial_subset_ordered
      (piecePorts_nodup j) (piecePorts_spherical hf j) (use j) (huse j)
      (pieceUsedCount_le_three hf j) ((pieceNodeIndex k f j).order I hnode)
      ((pieceNodeIndex k f j).order_injective I hnode) ((pieceNodeIndex k f j).order_cyclic I hnode)
    exact ⟨⟨G,hG,hs,port,hp,he⟩,ho⟩
  exact ⟨fun j => Classical.choose (hex j),fun j => Classical.choose_spec (hex j)⟩

/-- All local face witnesses now inhabit the concrete `PieceSourceOrders`
record; source coverage and block membership follow from occurrence indexing. -/
noncomputable def ChosenPieces.pieceSourceOrders {k : Nat} {f : CNF}
    (L : ChosenPieces k f) (hf : BoundedOccurrence f)
    (I : Hypermap (2*(placeFormula [] f).flatten.length))
    (hnode : ∀ a b, Reaches I.node a b ↔ occurrenceVertex f a=occurrenceVertex f b)
    (use : ∀ j : PieceIndex k f, Fin (pieceUsedCount k f j) → Fin (piecePorts k f j).length)
    (horder : L.HasSourceOrders I hnode use)
    (hmatch : ∀ j i, (L.choices hf).sourcePort hf ((pieceNodeIndex k f j).dart i) =
      blockDart (ungluedFormulaPieces k f) j ((L j).port (use j i))) :
    PieceSourceOrders (ungluedFormulaPieces k f) L.maps I ((L.choices hf).sourcePort hf) where
  count := pieceUsedCount k f
  source j := (pieceNodeIndex k f j).dart
  localPort j i := (L j).port (use j i)
  next j := (pieceNodeIndex k f j).order I hnode
  all_source := pieceNodeIndex_complete hf
  match_port := hmatch
  covers_piece j d e h := (L.choices hf).sourcePort_piece_complete hf d j e h
  next_source j := (pieceNodeIndex k f j).order_spec I hnode
  local_order := horder

/-- Exact global ordered incidence ports from the chosen local maps. -/
noncomputable def ChosenPieces.orderedPorts {k : Nat} {f : CNF}
    (L : ChosenPieces k f) (hf : BoundedOccurrence f)
    (I : Hypermap (2*(placeFormula [] f).flatten.length))
    (hIedge : ∀ d, I.edge d=graphEdge d)
    (hnode : ∀ a b, Reaches I.node a b ↔ occurrenceVertex f a=occurrenceVertex f b)
    (use : ∀ j : PieceIndex k f, Fin (pieceUsedCount k f j) → Fin (piecePorts k f j).length)
    (horder : L.HasSourceOrders I hnode use)
    (hmatch : ∀ j i, (L.choices hf).sourcePort hf ((pieceNodeIndex k f j).dart i) =
      blockDart (ungluedFormulaPieces k f) j ((L j).port (use j i))) :
    OrderedIncidencePorts ((L.choices hf).geometricPairing hf _ L.embedding) I :=
  (L.choices hf).orderedFromPieces hf L.maps L.embedding I hIedge
    (L.pieceSourceOrders hf I hnode use horder hmatch)

end STACS2027.PlanarAssembly
