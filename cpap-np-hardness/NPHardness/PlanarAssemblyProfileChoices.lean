module

public import NPHardness.PlanarAssemblyPortProfilePlacement
public import NPHardness.PlanarAssemblyChooseOrder
public import NPHardness.PlanarAssemblySourceMatch

/-! Choose actual local embeddings with prescribed finite boundary profiles.
Only the proof witnesses are chosen; all boundary orders and endpoint sides
are explicit parameters that can come from an executable Boolean rule. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

theorem NextSelected.restrict {n m r : Nat} {p:Fin n→Fin n} {port:Fin m→Fin n}
    {next:Fin m→Fin m} (use:Fin r→Fin m) (q:Fin r→Fin r)
    (hnext:∀i,NextSelected p port i (next i))
    (horder:∀i,next (use i)=use (q i)) (i:Fin r) :
    NextSelected p (fun t=>port (use t)) i (q i) := by
  obtain ⟨k,hk,he,hn⟩:=hnext (use i)
  refine ⟨k,hk,?_,?_⟩
  · rw [horder] at he
    exact he
  · intro j hj hjk t
    exact hn j hj hjk (use t)

def ChosenPieces.HasProfiles {k:Nat} {f:CNF} (L:ChosenPieces k f)
    (next:∀j:PieceIndex k f,Fin (piecePorts k f j).length→Fin (piecePorts k f j).length)
    (side:∀j:PieceIndex k f,Fin (piecePorts k f j).length→Bool) : Prop :=
  (∀j i,NextSelected (L j).map.face (L j).port i (next j i)) ∧
  (∀j i,dartSide ((L j).port i)=side j i)

theorem chosenPieces_with_profiles {k:Nat} {f:CNF}
    (next:∀j:PieceIndex k f,Fin (piecePorts k f j).length→Fin (piecePorts k f j).length)
    (side:∀j:PieceIndex k f,Fin (piecePorts k f j).length→Bool)
    (hprofiles:∀j:PieceIndex k f,SphericalPortProfile (ungluedFormulaPieces k f)[j.val]
      (fun i=>(piecePorts k f j)[i.val]) (next j) (side j)) :
    ∃L:ChosenPieces k f,L.HasProfiles next side := by
  have hex:∀j:PieceIndex k f,∃E:EmbeddingPorts (ungluedFormulaPieces k f)[j.val] (piecePorts k f j),
      (∀i,NextSelected E.map.face E.port i (next j i)) ∧ (∀i,dartSide (E.port i)=side j i) := by
    intro j
    obtain ⟨G,hG,hs,p,hi,he,hn,hside⟩:=hprofiles j
    exact ⟨⟨G,hG,hs,p,hi,he⟩,hn,hside⟩
  exact ⟨fun j=>Classical.choose (hex j),
    fun j=> (Classical.choose_spec (hex j)).1,
    fun j=> (Classical.choose_spec (hex j)).2⟩

theorem ChosenPieces.HasProfiles.source_orders {k:Nat} {f:CNF} {L:ChosenPieces k f}
    {next:∀j:PieceIndex k f,Fin (piecePorts k f j).length→Fin (piecePorts k f j).length}
    {side:∀j:PieceIndex k f,Fin (piecePorts k f j).length→Bool}
    (h:L.HasProfiles next side)
    (I:Hypermap (2*(placeFormula [] f).flatten.length))
    (hnode:∀a b,Reaches I.node a b ↔ occurrenceVertex f a=occurrenceVertex f b)
    (use:∀j:PieceIndex k f,Fin (pieceUsedCount k f j)→Fin (piecePorts k f j).length)
    (horder:∀j i,next j (use j i)=use j ((pieceNodeIndex k f j).order I hnode i)) :
    L.HasSourceOrders I hnode use := by
  intro j i
  exact NextSelected.restrict (use j) ((pieceNodeIndex k f j).order I hnode) (h.1 j) (horder j) i

theorem ChosenPieces.variableOccurrence_side {k:Nat} {f:CNF} (L:ChosenPieces k f)
    (hf:BoundedOccurrence f) (i:OccurrenceIndex f) :
    dartSide ((L.choices hf).variableOccurrencePort hf i)=
      dartSide ((L (variablePieceIndex k f (occurrenceVariable hf i))).port
        (variablePortIndex k f (occurrenceVariable hf i) (occurrenceLocalPort hf i))) := by
  unfold LocalPortChoices.variableOccurrencePort
  rw [L.variable_global_port]
  unfold dartSide
  rw [blockDart_side]

theorem ChosenPieces.clauseOccurrence_side {k:Nat} {f:CNF} (L:ChosenPieces k f)
    (hf:BoundedOccurrence f) (i:OccurrenceIndex f) :
    dartSide ((L.choices hf).clauseOccurrencePort i)=
      dartSide ((L (clausePieceIndex k f (occurrencePosition f i).clause)).port
        (clausePortIndex k f hf (occurrencePosition f i).clause (occurrencePosition f i).slot)) := by
  unfold LocalPortChoices.clauseOccurrencePort
  rw [L.clause_global_port]
  unfold dartSide
  rw [blockDart_side]

theorem ChosenPieces.HasProfiles.occurrence_sides {k:Nat} {f:CNF} {L:ChosenPieces k f}
    {next:∀j:PieceIndex k f,Fin (piecePorts k f j).length→Fin (piecePorts k f j).length}
    {side:∀j:PieceIndex k f,Fin (piecePorts k f j).length→Bool}
    (h:L.HasProfiles next side) (hf:BoundedOccurrence f) (i:OccurrenceIndex f) :
    dartSide ((L.choices hf).variableOccurrencePort hf i)=
      side (variablePieceIndex k f (occurrenceVariable hf i))
        (variablePortIndex k f (occurrenceVariable hf i) (occurrenceLocalPort hf i)) ∧
    dartSide ((L.choices hf).clauseOccurrencePort i)=
      side (clausePieceIndex k f (occurrencePosition f i).clause)
        (clausePortIndex k f hf (occurrencePosition f i).clause (occurrencePosition f i).slot) := by
  rw [L.variableOccurrence_side,L.clauseOccurrence_side,h.2,h.2]
  exact ⟨rfl,rfl⟩

end STACS2027.PlanarAssembly
