module

public import NPHardness.PlanarAssemblySourcePortNumbers
public import NPHardness.PlanarAssemblyPrescribedChoices
public import NPHardness.PlanarSourceEndpointChoices

/-! A fully explicit Boolean endpoint rule produces the actual planar graph
when the source rotation has the certified arithmetic port order. Geometric
choices remain proof witnesses and do not occur in the output graph. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

@[simp] theorem placedLiteral_port_zero (p:PlacedLiteral) :
    (p.port==0)=p.literal.positive := by
  unfold PlacedLiteral.port
  cases p.literal.positive <;> simp

theorem ChosenPieces.HasProfiles.source_rule_sides {k:Nat} {f:CNF}
    {L:ChosenPieces k f} {signs:Nat→Bool}
    (h:L.HasProfiles (pieceProfileNext signs) (pieceProfileSide signs))
    (hf:BoundedOccurrence f) (i:OccurrenceIndex f) :
    PlanarSource.sourceEndpointChoices signs (occurrence f i)=
      (dartSide ((L.choices hf).variableOccurrencePort hf i)==
        dartSide ((L.choices hf).clauseOccurrencePort i)) := by
  obtain ⟨hv,hc⟩:=h.occurrence_sides hf i
  rw [hv,hc]
  change PlanarSource.sourceEndpointChoices signs (occurrence f i)=
    ((if (occurrence f i).literal.var<variableBound f then
      (((occurrence f i).port==0)==!(signs (occurrence f i).literal.var)) else true)==
      (if variableBound f+(occurrencePosition f i).clause.val<variableBound f then _ else true))
  rw [ite_eq_left (occurrence_variable_lt hf i),ite_eq_right (by omega),placedLiteral_port_zero]
  simp only [PlanarSource.sourceEndpointChoices]
  cases (occurrence f i).literal.positive <;> cases signs (occurrence f i).literal.var <;> rfl

/-- The output endpoint choices are the explicit sign rule. A source embedding
with the stated arithmetic predecessor action certifies its actual planarity. -/
theorem orientedFormulaGraph_planar_source_rule (k:Nat) {f:CNF}
    (hf:BoundedOccurrence f) (signs:Nat→Bool)
    (I:Hypermap (2*(placeFormula [] f).flatten.length))
    (hIedge:∀d,I.edge d=graphEdge d)
    (hnode:∀a b,Reaches I.node a b ↔ occurrenceVertex f a=occurrenceVertex f b)
    (hI:I.Planar)
    (hpred:∀d,sourcePortNumber f (I.face (I.edge d))=
      if sourceForward signs f d then (sourcePortNumber f d+1)%sourcePortCount f d
      else (sourcePortNumber f d+sourcePortCount f d-1)%sourcePortCount f d) :
    PlanarGraph (orientedFormulaGraph (PlanarSource.sourceEndpointChoices signs) k f) := by
  obtain ⟨L,hprofile⟩:=chosenPieces_with_profiles
    (pieceProfileNext (k:=k) (f:=f) signs) (pieceProfileSide signs) (piece_signed_profile hf signs)
  let C:=L.choices hf
  have horder:=hprofile.source_orders I hnode (piecePortIndex hf)
    (piece_profile_source_order hf signs I hnode hpred)
  let O:=L.orderedPorts hf I hIedge hnode (piecePortIndex hf) horder (L.sourcePort_piece_match hf)
  apply C.orientedFormulaGraph_planar_prescribed hf (PlanarSource.sourceEndpointChoices signs)
    (hprofile.source_rule_sides hf) (piecesMap (ungluedFormulaPieces k f) L.maps)
    L.embedding L.spherical I hI O
  intro a b hab
  exact (hnode a b).mpr (C.sourcePort_connected_vertex hf L.maps a b hab)

end STACS2027.PlanarAssembly
