module

public import NPHardness.PlanarAssemblyPortEnds
public import NPHardness.PlanarAssemblyEndpoints

/-!
The endpoint flips forced by the chosen outer-face darts. Equal boundary
orientations use the reversed endpoint identification; opposite orientations
use the direct identification. The resulting quotient is exactly the existing
oriented formula graph, including both copies of each attachment edge.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

namespace LocalPortChoices
variable {k : Nat} {f : CNF} (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
include C hf

noncomputable def assemblyFlips : EndpointChoices := by
  classical
  exact fun p=>if h:∃i:OccurrenceIndex f,occurrence f i=p then
    dartSide (C.variableOccurrencePort hf (Classical.choose h)) ==
      dartSide (C.clauseOccurrencePort (Classical.choose h)) else false

theorem assemblyFlips_occurrence (i : OccurrenceIndex f) :
    C.assemblyFlips hf (occurrence f i)=
      (dartSide (C.variableOccurrencePort hf i)==dartSide (C.clauseOccurrencePort i)) := by
  have he : ∃j:OccurrenceIndex f,occurrence f j=occurrence f i := ⟨i,rfl⟩
  rw [assemblyFlips,dite_eq_left he]
  have hi := occurrence_injective f (Classical.choose_spec he)
  rw [hi]

omit C in theorem assemblyVertex_variableOccurrenceEnd (flips : EndpointChoices)
    (i : OccurrenceIndex f) (side : Bool) :
    assemblyVertex flips k f (variableOccurrenceEnd k f i side)=variableOccurrenceEnd k f i side := by
  exact assemblyVertex_variable flips k f (occurrence_variable_lt hf i)
    (Nat.lt_of_lt_of_le (variableEndpoint_bound _ _)
      (show 7≤gadgetWidth k by have := gadgetWidth_ge k; omega))

omit C in theorem assemblyVertex_clauseOccurrenceEnd (flips : EndpointChoices)
    (i : OccurrenceIndex f) (side : Bool) :
    assemblyVertex flips k f (clauseOccurrenceEnd k f i side)=
      variableOccurrenceEnd k f i (if flips (occurrence f i) then !side else side) := by
  let j := (occurrencePosition f i).clause
  let s : Fin 3 := ⟨(occurrencePosition f i).slot.val,occurrence_slot_lt hf i⟩
  rw [clauseOccurrenceEnd,assemblyVertex_clause flips k f j.val j.isLt
    (clauseEndpoint_lt_gadgetWidth k s side)]
  exact @Oriented.clauseVertex_attachment ⟨flips⟩ (gadgetWidth k) (variableBound f)
    j.val (placeFormula [] f)[j.val] s.val s.isLt (occurrence f i)
    (occurrencePosition_get f i) side

/-- Matched opposite clause and variable darts are identified by exactly the
flip read from their selected boundary directions. -/
theorem assemblyVertex_opposite_clause (i : OccurrenceIndex f) :
    assemblyVertex (C.assemblyFlips hf) k f
      (clauseOccurrenceEnd k f i (!dartSide (C.clauseOccurrencePort i))) =
      variableOccurrenceEnd k f i (dartSide (C.variableOccurrencePort hf i)) := by
  rw [assemblyVertex_clauseOccurrenceEnd hf,C.assemblyFlips_occurrence hf,
    (assembly_side_alignment _ _).1]

theorem assemblyVertex_marked_clause (i : OccurrenceIndex f) :
    assemblyVertex (C.assemblyFlips hf) k f
      (clauseOccurrenceEnd k f i (dartSide (C.clauseOccurrencePort i))) =
      variableOccurrenceEnd k f i (!dartSide (C.variableOccurrencePort hf i)) := by
  rw [assemblyVertex_clauseOccurrenceEnd hf,C.assemblyFlips_occurrence hf,
    (assembly_side_alignment _ _).2]

/-- The two endpoint identifications on a matched pair of port edges. -/
theorem assemblyVertex_port_sides (i : OccurrenceIndex f) (side : Bool) :
    Option.map (assemblyVertex (C.assemblyFlips hf) k f)
      (halfEdgeEnd (ungluedFormulaPieces k f).flatten
        (atSide (C.variableOccurrencePort hf i) side).val) =
    Option.map (assemblyVertex (C.assemblyFlips hf) k f)
      (halfEdgeEnd (ungluedFormulaPieces k f).flatten
        (atSide (C.clauseOccurrencePort i) (!side)).val) := by
  rw [C.variableOccurrencePort_end hf,C.clauseOccurrencePort_end]
  simp only [Option.map_some]
  rw [assemblyVertex_variableOccurrenceEnd hf]
  cases side
  · exact congrArg some (C.assemblyVertex_opposite_clause hf i).symm
  · exact congrArg some (C.assemblyVertex_marked_clause hf i).symm

omit C in theorem attachment_occurrence {flips : EndpointChoices} {x y : Nat}
    (h : AssemblyAttachment flips k f x y) :
    ∃i:OccurrenceIndex f,∃s:Bool,
      x=variableOccurrenceEnd k f i (if flips (occurrence f i) then !s else s) ∧
      y=clauseOccurrenceEnd k f i s := by
  obtain ⟨j,t,p,s,hp,hx,hy⟩ := h
  have hmem : p∈(placeFormula [] f).flatten :=
    List.mem_flatten.mpr ⟨(placeFormula [] f)[j.val],List.getElem_mem j.isLt,List.mem_of_getElem? hp⟩
  obtain ⟨iv,hiv,hi⟩ := List.mem_iff_getElem.mp hmem
  let i : OccurrenceIndex f := ⟨iv,hiv⟩
  have hip : occurrence f i=p := hi
  have hnew : AssemblyAttachment flips k f x (clauseOccurrenceEnd k f i s) := by
    refine ⟨(occurrencePosition f i).clause,
      ⟨(occurrencePosition f i).slot.val,occurrence_slot_lt hf i⟩,
      occurrence f i,s,occurrencePosition_get f i,?_,rfl⟩
    simpa only [hip] using hx
  have hold : AssemblyAttachment flips k f x y := ⟨j,t,p,s,hp,hx,hy⟩
  refine ⟨i,s,?_,hold.target_unique hf hnew⟩
  simpa only [variableOccurrenceEnd,hip] using hx

/-- Every actual quotient attachment is one of the two endpoint pairs named
by the selected variable and clause boundary darts. -/
theorem attachment_port_endpoints {x y : Nat}
    (h : AssemblyAttachment (C.assemblyFlips hf) k f x y) :
    ∃i:OccurrenceIndex f,
      (some x=halfEdgeEnd (ungluedFormulaPieces k f).flatten (C.variableOccurrencePort hf i).val ∧
       some y=halfEdgeEnd (ungluedFormulaPieces k f).flatten (graphEdge (C.clauseOccurrencePort i)).val) ∨
      (some y=halfEdgeEnd (ungluedFormulaPieces k f).flatten (C.clauseOccurrencePort i).val ∧
       some x=halfEdgeEnd (ungluedFormulaPieces k f).flatten (graphEdge (C.variableOccurrencePort hf i)).val) := by
  obtain ⟨i,s,rfl,rfl⟩ := attachment_occurrence hf h
  refine ⟨i,?_⟩
  rw [C.assemblyFlips_occurrence hf]
  by_cases hs : s=dartSide (C.clauseOccurrencePort i)
  · right
    subst s
    rw [(assembly_side_alignment _ _).2]
    constructor
    · exact (C.clauseOccurrencePort_end i false).symm
    · exact (C.variableOccurrencePort_end hf i true).symm
  · have he : s= !dartSide (C.clauseOccurrencePort i) := by
      cases hb : dartSide (C.clauseOccurrencePort i) <;> cases s <;> simp_all
    left
    rw [he,(assembly_side_alignment _ _).1]
    constructor
    · exact (C.variableOccurrencePort_end hf i false).symm
    · exact (C.clauseOccurrencePort_end i true).symm

/-- The actual simultaneous pairing identifies its matched endpoints under
the chosen quotient map. -/
theorem geometricPairing_glue
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hG : IsGraphEmbedding (ungluedFormulaPieces k f).flatten G)
    (d : Fin (2*(ungluedFormulaPieces k f).flatten.length))
    (hd : (C.geometricPairing hf G hG).marked d=true) :
    Option.map (assemblyVertex (C.assemblyFlips hf) k f)
      (halfEdgeEnd (ungluedFormulaPieces k f).flatten d.val) =
    Option.map (assemblyVertex (C.assemblyFlips hf) k f)
      (halfEdgeEnd (ungluedFormulaPieces k f).flatten
        (G.edge ((C.geometricPairing hf G hG).pair d)).val) := by
  have hE : ∀d,G.edge d=graphEdge d := fun d=>Fin.ext (hG.1 d)
  obtain ⟨s,hs⟩ := (C.pairing_marked hf G _ d).mp hd
  subst d
  unfold sourcePort
  dsimp only
  split
  · rw [show (C.geometricPairing hf G hG).pair (C.variableOccurrencePort hf _) =
      C.clauseOccurrencePort _ from C.pairing_variable hf G _ _,hE]
    exact C.assemblyVertex_port_sides hf _ false
  · rw [show (C.geometricPairing hf G hG).pair (C.clauseOccurrencePort _) =
      C.variableOccurrencePort hf _ from C.pairing_clause hf G _ _,hE]
    exact (C.assemblyVertex_port_sides hf _ true).symm

/-- Exact quotient fibers for all darts in the allocated graph, expressed in
the old endpoint labels and actual matched port pairing. -/
theorem geometricPairing_fibers
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hG : IsGraphEmbedding (ungluedFormulaPieces k f).flatten G) :
    (C.geometricPairing hf G hG).MatchedEndpointFibers
      (fun d=>halfEdgeEnd (ungluedFormulaPieces k f).flatten d.val)
      (Option.map (assemblyVertex (C.assemblyFlips hf) k f)) := by
  have hE : ∀d,G.edge d=graphEdge d := fun d=>Fin.ext (hG.1 d)
  have hb : VerticesBelow (ungluedFormulaPieces k f).flatten
      ((variableBound f+(placeFormula [] f).length)*gadgetWidth k) := by
    rw [ungluedFormulaPieces_flatten]
    exact ungluedFormulaGraph_below k f
  intro a b hab
  dsimp only at hab ⊢
  obtain ⟨x,hx,hax⟩ := halfEdgeEnd_bound hb a.isLt
  obtain ⟨y,hy,hby⟩ := halfEdgeEnd_bound hb b.isLt
  rw [hax,hby,Option.map_some,Option.map_some] at hab
  rcases (assemblyVertex_fiber (C.assemblyFlips hf) hf hx hy).mp (Option.some.inj hab) with he | he | he
  · left
    rw [hax,hby,he]
  · obtain ⟨i,he | he⟩ := C.attachment_port_endpoints hf he
    · refine Or.inr ⟨C.variableOccurrencePort hf i,?_,Or.inl ?_⟩
      · exact (C.pairing_marked hf G _ _).mpr ⟨occurrenceDart i false,C.sourcePort_even hf i⟩
      · rw [show (C.geometricPairing hf G hG).pair (C.variableOccurrencePort hf i)=
          C.clauseOccurrencePort i from C.pairing_variable hf G _ i,hE,hax,hby]
        exact he
    · refine Or.inr ⟨C.clauseOccurrencePort i,?_,Or.inr ?_⟩
      · exact (C.pairing_marked hf G _ _).mpr ⟨occurrenceDart i true,C.sourcePort_odd hf i⟩
      · rw [show (C.geometricPairing hf G hG).pair (C.clauseOccurrencePort i)=
          C.variableOccurrencePort hf i from C.pairing_clause hf G _ i,hE,hax,hby]
        exact he
  · obtain ⟨i,he | he⟩ := C.attachment_port_endpoints hf he
    · refine Or.inr ⟨C.variableOccurrencePort hf i,?_,Or.inr ?_⟩
      · exact (C.pairing_marked hf G _ _).mpr ⟨occurrenceDart i false,C.sourcePort_even hf i⟩
      · rw [show (C.geometricPairing hf G hG).pair (C.variableOccurrencePort hf i)=
          C.clauseOccurrencePort i from C.pairing_variable hf G _ i,hE,hax,hby]
        exact he
    · refine Or.inr ⟨C.clauseOccurrencePort i,?_,Or.inl ?_⟩
      · exact (C.pairing_marked hf G _ _).mpr ⟨occurrenceDart i true,C.sourcePort_odd hf i⟩
      · rw [show (C.geometricPairing hf G hG).pair (C.clauseOccurrencePort i)=
          C.variableOccurrencePort hf i from C.pairing_clause hf G _ i,hE,hax,hby]
        exact he

end LocalPortChoices
end STACS2027.PlanarAssembly
