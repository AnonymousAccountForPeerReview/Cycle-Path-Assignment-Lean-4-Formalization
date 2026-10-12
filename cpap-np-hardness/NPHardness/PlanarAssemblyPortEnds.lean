module

public import NPHardness.PlanarAssemblySelectedPairing
public import NPHardness.PlanarAssemblyNodes
public import NPHardness.PlanarAssemblyEndpoints

/-! Actual endpoint separation of the selected occurrence port edges. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

def variableOccurrenceEnd (k : Nat) (f : CNF) (i : OccurrenceIndex f) (side : Bool) : Nat :=
  blockVertex (gadgetWidth k) (occurrence f i).literal.var (variableEndpoint (occurrence f i).port side)

noncomputable def clauseOccurrenceEnd (k : Nat) (f : CNF) (i : OccurrenceIndex f) (side : Bool) : Nat :=
  blockVertex (gadgetWidth k) (variableBound f+(occurrencePosition f i).clause.val)
    (clauseEndpoint (occurrencePosition f i).slot.val side)

theorem variableOccurrenceEnd_injective {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {i j : OccurrenceIndex f} {a b : Bool}
    (h : variableOccurrenceEnd k f i a=variableOccurrenceEnd k f j b) : i=j ∧ a=b := by
  have hwide : 7 ≤ gadgetWidth k := by have := gadgetWidth_ge k; omega
  have he := blockVertex_injective (Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hwide)
    (Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hwide) h
  have hp := variableEndpoint_injective (hf.placement_port_lt (occurrence_mem f i))
    (hf.placement_port_lt (occurrence_mem f j)) a b he.2
  exact ⟨occurrence_injective f (hf.placement_key_injective
    (occurrence_mem f i) (occurrence_mem f j) (Prod.ext he.1 hp.1)),hp.2⟩

theorem occurrence_slot_lt {f : CNF} (hf : BoundedOccurrence f) (i : OccurrenceIndex f) :
    (occurrencePosition f i).slot.val < 3 := by
  have hs := hf.placed_clause_size (List.getElem_mem (occurrencePosition f i).clause.isLt)
  have hi := (occurrencePosition f i).slot.isLt
  omega

theorem clauseEndpoint_injective {i j : Nat} (hi : i<3) (hj : j<3) {a b : Bool}
    (h : clauseEndpoint i a=clauseEndpoint j b) : i=j ∧ a=b := by
  have ht := congrArg clausePortAt h
  rw [clausePortAt_endpoint hi,clausePortAt_endpoint hj] at ht
  exact Prod.mk.inj (Option.some.inj ht)

theorem occurrencePosition_injective {f : CNF} {i j : OccurrenceIndex f}
    (hc : (occurrencePosition f i).clause.val=(occurrencePosition f j).clause.val)
    (hs : (occurrencePosition f i).slot.val=(occurrencePosition f j).slot.val) : i=j := by
  have hi := occurrencePosition_get f i
  have hj := occurrencePosition_get f j
  simp only [← hc,← hs] at hj
  exact occurrence_injective f (Option.some.inj (hi.symm.trans hj))

theorem clauseOccurrenceEnd_injective {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    {i j : OccurrenceIndex f} {a b : Bool}
    (h : clauseOccurrenceEnd k f i a=clauseOccurrenceEnd k f j b) : i=j ∧ a=b := by
  have he := blockVertex_injective
    (clauseEndpoint_lt_gadgetWidth k ⟨_,occurrence_slot_lt hf i⟩ a)
    (clauseEndpoint_lt_gadgetWidth k ⟨_,occurrence_slot_lt hf j⟩ b) h
  have hp := clauseEndpoint_injective (occurrence_slot_lt hf i) (occurrence_slot_lt hf j) he.2
  exact ⟨occurrencePosition_injective (by omega) hp.1,hp.2⟩

theorem variableOccurrenceEnd_ne_clauseOccurrenceEnd {k : Nat} {f : CNF}
    (hf : BoundedOccurrence f) (i j : OccurrenceIndex f) (a b : Bool) :
    variableOccurrenceEnd k f i a≠clauseOccurrenceEnd k f j b := by
  intro h
  have hwide : 7 ≤ gadgetWidth k := by have := gadgetWidth_ge k; omega
  have he := blockVertex_injective (Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hwide)
    (clauseEndpoint_lt_gadgetWidth k ⟨_,occurrence_slot_lt hf j⟩ b) h
  have hi := occurrence_variable_lt hf i
  omega

def dartSide {n : Nat} (d : Fin (2*n)) : Bool := !(d.val%2==0)

theorem dartSide_graphEdge {n : Nat} (d : Fin (2*n)) : dartSide (graphEdge d)=!(dartSide d) := by
  rcases Nat.mod_two_eq_zero_or_one d.val with hm | hm
  · simp [dartSide,graphEdge,ed,hm,show (d.val+1)%2=1 by omega]
  · simp [dartSide,graphEdge,ed,hm,show (d.val-1)%2=0 by omega]

theorem graphEdge_index {n : Nat} (d : Fin (2*n)) : (graphEdge d).val/2=d.val/2 := by
  rcases Nat.mod_two_eq_zero_or_one d.val with hm | hm <;>
    simp only [graphEdge,ed,hm] <;> simp <;> omega

theorem halfEdgeEnd_lookup {g : Graph} {d : Fin (2*g.length)} {a b : Nat}
    (h : g[d.val/2]?=some (a,b)) :
    halfEdgeEnd g d.val=some (if dartSide d then b else a) := by
  by_cases hz : d.val%2=0 <;> simp [halfEdgeEnd,h,dartSide,hz]

theorem mapEdge_variablePort (width tag port : Nat) :
    mapEdge (blockVertex width tag) (edge (variableEndpoint port false) (variableEndpoint port true)) =
      (blockVertex width tag (variableEndpoint port false),blockVertex width tag (variableEndpoint port true)) := by
  have hle : variableEndpoint port false ≤ variableEndpoint port true := by
    unfold variableEndpoint
    split <;> try split <;> decide
  have hb : blockVertex width tag (variableEndpoint port false) ≤
      blockVertex width tag (variableEndpoint port true) := by unfold blockVertex; omega
  rw [mapEdge_edge]
  exact Prod.ext (Nat.min_eq_left hb) (Nat.max_eq_right hb)

theorem mapEdge_clausePort (width tag port : Nat) :
    mapEdge (blockVertex width tag) (edge (clauseEndpoint port false) (clauseEndpoint port true)) =
      (blockVertex width tag (clauseEndpoint port false),blockVertex width tag (clauseEndpoint port true)) := by
  have hle : clauseEndpoint port false ≤ clauseEndpoint port true := by
    unfold clauseEndpoint
    split <;> try split <;> decide
  have hb : blockVertex width tag (clauseEndpoint port false) ≤
      blockVertex width tag (clauseEndpoint port true) := by unfold blockVertex; omega
  rw [mapEdge_edge]
  exact Prod.ext (Nat.min_eq_left hb) (Nat.max_eq_right hb)

def atSide {n : Nat} (d : Fin (2*n)) (opposite : Bool) : Fin (2*n) :=
  if opposite then graphEdge d else d

def endpointSide (side opposite : Bool) : Bool := if opposite then !side else side

theorem endpointSide_injective (side : Bool) {a b : Bool}
    (h : endpointSide side a=endpointSide side b) : a=b := by
  cases side <;> cases a <;> cases b <;> simp_all [endpointSide]

theorem halfEdgeEnd_atSide {g : Graph} {d : Fin (2*g.length)} {a b : Nat}
    (h : g[d.val/2]?=some (a,b)) (side : Bool) :
    halfEdgeEnd g (atSide d side).val=some (if endpointSide (dartSide d) side then b else a) := by
  cases side
  · exact halfEdgeEnd_lookup h
  · have he : g[(graphEdge d).val/2]?=some (a,b) := by rw [graphEdge_index]; exact h
    simpa only [atSide,endpointSide,↓reduceIte,dartSide_graphEdge] using halfEdgeEnd_lookup he

theorem LocalPortChoices.variableOccurrencePort_lookup {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f) (i : OccurrenceIndex f) :
    (ungluedFormulaPieces k f).flatten[(C.variableOccurrencePort hf i).val/2]? =
      some (variableOccurrenceEnd k f i false,variableOccurrenceEnd k f i true) := by
  simp only [ungluedFormulaPieces_flatten]
  unfold variableOccurrencePort
  rw [variableGlobalDart_lookup,C.variable_edge,mapEdge_variablePort]
  rfl

theorem LocalPortChoices.clauseOccurrencePort_lookup {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (i : OccurrenceIndex f) :
    (ungluedFormulaPieces k f).flatten[(C.clauseOccurrencePort i).val/2]? =
      some (clauseOccurrenceEnd k f i false,clauseOccurrenceEnd k f i true) := by
  simp only [ungluedFormulaPieces_flatten]
  unfold clauseOccurrencePort
  rw [clauseGlobalDart_lookup,C.clause_edge,mapEdge_clausePort]
  rfl

theorem LocalPortChoices.variableOccurrencePort_end {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f) (i : OccurrenceIndex f) (side : Bool) :
    halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.variableOccurrencePort hf i) side).val =
      some (variableOccurrenceEnd k f i (endpointSide (dartSide (C.variableOccurrencePort hf i)) side)) := by
  have he := halfEdgeEnd_atSide (C.variableOccurrencePort_lookup hf i) side
  cases h : endpointSide (dartSide (C.variableOccurrencePort hf i)) side <;> simpa only [h,Bool.false_eq_true,↓reduceIte] using he

theorem LocalPortChoices.clauseOccurrencePort_end {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (i : OccurrenceIndex f) (side : Bool) :
    halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.clauseOccurrencePort i) side).val =
      some (clauseOccurrenceEnd k f i (endpointSide (dartSide (C.clauseOccurrencePort i)) side)) := by
  have he := halfEdgeEnd_atSide (C.clauseOccurrencePort_lookup i) side
  cases h : endpointSide (dartSide (C.clauseOccurrencePort i)) side <;> simpa only [h,Bool.false_eq_true,↓reduceIte] using he

theorem LocalPortChoices.variablePort_end_injective {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f) {i j : OccurrenceIndex f} {a b : Bool}
    (h : halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.variableOccurrencePort hf i) a).val =
      halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.variableOccurrencePort hf j) b).val) :
    i=j ∧ a=b := by
  rw [C.variableOccurrencePort_end,C.variableOccurrencePort_end] at h
  obtain ⟨hi,hs⟩ := variableOccurrenceEnd_injective hf (Option.some.inj h)
  subst j
  exact ⟨rfl,endpointSide_injective _ hs⟩

theorem LocalPortChoices.clausePort_end_injective {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f) {i j : OccurrenceIndex f} {a b : Bool}
    (h : halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.clauseOccurrencePort i) a).val =
      halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.clauseOccurrencePort j) b).val) :
    i=j ∧ a=b := by
  rw [C.clauseOccurrencePort_end,C.clauseOccurrencePort_end] at h
  obtain ⟨hi,hs⟩ := clauseOccurrenceEnd_injective hf (Option.some.inj h)
  subst j
  exact ⟨rfl,endpointSide_injective _ hs⟩

theorem LocalPortChoices.variablePort_end_ne_clausePort_end {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f) (i j : OccurrenceIndex f) (a b : Bool) :
    halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.variableOccurrencePort hf i) a).val ≠
      halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.clauseOccurrencePort j) b).val := by
  rw [C.variableOccurrencePort_end,C.clauseOccurrencePort_end]
  intro h
  exact variableOccurrenceEnd_ne_clauseOccurrenceEnd hf i j _ _ (Option.some.inj h)

/-- Every selected port edge has its own two old graph vertices. This covers
distinct occurrences at one variable, different clauses, and both sides. -/
theorem LocalPortChoices.sourcePort_end_injective {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    {d e : Fin (2*(placeFormula [] f).flatten.length)} {a b : Bool}
    (h : halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.sourcePort hf d) a).val =
      halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.sourcePort hf e) b).val) :
    d=e ∧ a=b := by
  unfold sourcePort at h
  dsimp only at h
  split at h <;> split at h
  · obtain ⟨hi,hs⟩ := C.variablePort_end_injective hf h
    have hv := congrArg Fin.val hi
    exact ⟨Fin.ext (by dsimp only at hv; omega),hs⟩
  · exact False.elim (C.variablePort_end_ne_clausePort_end hf _ _ _ _ h)
  · exact False.elim (C.variablePort_end_ne_clausePort_end hf _ _ _ _ h.symm)
  · obtain ⟨hi,hs⟩ := C.clausePort_end_injective hf h
    have hv := congrArg Fin.val hi
    exact ⟨Fin.ext (by dsimp only at hv; omega),hs⟩

/-- The selected actual graph edges satisfy the geometric disjointness API. -/
theorem LocalPortChoices.disjointPortEndpoints {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hE : ∀ d, G.edge d=graphEdge d) :
    DisjointPortEndpoints G (fun d => halfEdgeEnd (ungluedFormulaPieces k f).flatten d.val)
      (SelectedPairing.marked (C.sourcePort hf)) := by
  intro a b ha hb s t he
  obtain ⟨i,rfl⟩ := (SelectedPairing.marked_iff _ _).mp ha
  obtain ⟨j,rfl⟩ := (SelectedPairing.marked_iff _ _).mp hb
  have hend : halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.sourcePort hf i) s).val =
      halfEdgeEnd (ungluedFormulaPieces k f).flatten (atSide (C.sourcePort hf j) t).val := by
    cases s <;> cases t <;> simpa only [portEndpoint,atSide,hE,Bool.false_eq_true,↓reduceIte] using he
  obtain ⟨hi,hs⟩ := C.sourcePort_end_injective hf hend
  exact ⟨congrArg (C.sourcePort hf) hi,hs⟩

theorem LocalPortChoices.sourcePort_face_separated {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hG : IsGraphEmbedding (ungluedFormulaPieces k f).flatten G) :
    ∀ i j, G.face (C.sourcePort hf i)≠C.sourcePort hf j := by
  have hE : ∀ d, G.edge d=graphEdge d := fun d => Fin.ext (hG.1 d)
  have hE2 : ∀ d, G.edge (G.edge d)=d := by intro d; rw [hE,hE,graphEdge_twice]
  have hN : ∀ d, halfEdgeEnd (ungluedFormulaPieces k f).flatten (G.node d).val =
      halfEdgeEnd (ungluedFormulaPieces k f).flatten d.val := by
    intro d
    exact ((hG.2.1 d (G.node d)).mp ⟨1,rfl⟩).symm
  intro i j he
  have hm := face_marked_false G (fun d => halfEdgeEnd (ungluedFormulaPieces k f).flatten d.val)
    (SelectedPairing.marked (C.sourcePort hf)) hE2 hN (C.disjointPortEndpoints hf G hE)
    ((SelectedPairing.marked_iff _ _).mpr ⟨i,rfl⟩)
  rw [he] at hm
  have hj := (SelectedPairing.marked_iff (C.sourcePort hf) (C.sourcePort hf j)).mpr ⟨j,rfl⟩
  rw [hm] at hj
  contradiction

/-- Actual local choices and an embedding of the disjoint gadget graph now
construct a separated global pairing without any extra geometric hypothesis. -/
noncomputable def LocalPortChoices.geometricPairing {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hG : IsGraphEmbedding (ungluedFormulaPieces k f).flatten G) : PortPairing G :=
  C.pairing hf G (C.sourcePort_face_separated hf G hG)

theorem LocalPortChoices.geometricPairing_disjoint {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hG : IsGraphEmbedding (ungluedFormulaPieces k f).flatten G) :
    (C.geometricPairing hf G hG).DisjointNodeSwitches := by
  have hE : ∀ d, G.edge d=graphEdge d := fun d => Fin.ext (hG.1 d)
  apply PortPairing.disjoint_node_switches _
    (fun d => halfEdgeEnd (ungluedFormulaPieces k f).flatten d.val)
  · intro d
    rw [hE,hE,graphEdge_twice]
  · intro d
    exact ((hG.2.1 d (G.node d)).mp ⟨1,rfl⟩).symm
  · exact C.disjointPortEndpoints hf G hE

end STACS2027.PlanarAssembly
