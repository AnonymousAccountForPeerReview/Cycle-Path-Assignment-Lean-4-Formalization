module

public import NPHardness.PlanarAssemblyGlobal

/-! Relate the endpoint choices computed from actual selected dart directions
to a prescribed executable choice function. Only choices on real allocated
occurrences affect the concrete output edge list. -/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT

theorem orientedClauseVertex_congr_choices {a b : EndpointChoices}
    {c : List PlacedLiteral} (h:∀p∈c,a p=b p) (width n j v:Nat) :
    orientedClauseVertex a width n j c v=orientedClauseVertex b width n j c v := by
  unfold orientedClauseVertex Oriented.clauseVertex
  cases he:attachmentAt c v with
  | none => rfl
  | some z =>
    rcases z with ⟨p,s⟩
    obtain ⟨i,_,hi,_⟩:=attachmentAt_spec.mp he
    have hp:=h p (List.mem_of_getElem? hi)
    simp only [Oriented.orientSide,hp]

theorem orientedPlacedClauseGraph_congr_choices {a b : EndpointChoices}
    {c : List PlacedLiteral} (h:∀p∈c,a p=b p) (k n j:Nat) :
    orientedPlacedClauseGraph a k n j c=orientedPlacedClauseGraph b k n j c := by
  have he:orientedClauseVertex a (gadgetWidth k) n j c=orientedClauseVertex b (gadgetWidth k) n j c :=
    funext (orientedClauseVertex_congr_choices h (gadgetWidth k) n j)
  change mapGraph (orientedClauseVertex a (gadgetWidth k) n j c) (clauseGraph k c)=
    mapGraph (orientedClauseVertex b (gadgetWidth k) n j c) (clauseGraph k c)
  rw [he]

theorem orientedFormulaGraph_congr_choices {a b : EndpointChoices} {f : CNF}
    (h:∀p∈(placeFormula [] f).flatten,a p=b p) (k:Nat) :
    orientedFormulaGraph a k f=orientedFormulaGraph b k f := by
  unfold orientedFormulaGraph Oriented.formulaGraph
  congr 2
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hv:j<(placeFormula [] f).length:=by simpa using hj
    simp only [List.getElem_mapIdx]
    apply orientedPlacedClauseGraph_congr_choices
    intro p hp
    exact h p (List.mem_flatten.mpr ⟨(placeFormula [] f)[j],List.getElem_mem hv,hp⟩)

namespace PlanarAssembly.LocalPortChoices
open Complexity.Planar
variable {k:Nat} {f:CNF} (C:LocalPortChoices k f) (hf:BoundedOccurrence f)

/-- An executable endpoint rule with the certified local boundary directions
produces exactly the same edge list as geometric dart assembly. -/
theorem formulaGraph_prescribed_choices (flips:EndpointChoices)
    (hflip:∀i:OccurrenceIndex f,flips (occurrence f i)=
      (dartSide (C.variableOccurrencePort hf i)==dartSide (C.clauseOccurrencePort i))) :
    orientedFormulaGraph flips k f=orientedFormulaGraph (C.assemblyFlips hf) k f := by
  apply orientedFormulaGraph_congr_choices
  intro p hp
  obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hp
  have hocc:occurrence f (⟨i,hi⟩:OccurrenceIndex f)=p:=he
  rw [←hocc,hflip,C.assemblyFlips_occurrence]

/-- Upgrade the full geometric assembly theorem to an explicitly prescribed
choice function after checking its Boolean boundary-direction equation. -/
theorem orientedFormulaGraph_planar_prescribed (flips:EndpointChoices)
    (hflip:∀i:OccurrenceIndex f,flips (occurrence f i)=
      (dartSide (C.variableOccurrencePort hf i)==dartSide (C.clauseOccurrencePort i)))
    (G:Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hG:IsGraphEmbedding (ungluedFormulaPieces k f).flatten G)
    (hstrict:2*G.componentCount+2*(ungluedFormulaPieces k f).flatten.length≤G.eulerRhs)
    {m:Nat} (I:Hypermap m) (hI:I.Planar)
    (O:OrderedIncidencePorts (C.geometricPairing hf G hG) I)
    (hseparate:O.SourceNodesSeparate) : PlanarGraph (orientedFormulaGraph flips k f) := by
  rw [C.formulaGraph_prescribed_choices hf flips hflip]
  exact C.orientedFormulaGraph_planar_of_orderedPorts hf G hG hstrict I hI O hseparate

end PlanarAssembly.LocalPortChoices
end STACS2027
