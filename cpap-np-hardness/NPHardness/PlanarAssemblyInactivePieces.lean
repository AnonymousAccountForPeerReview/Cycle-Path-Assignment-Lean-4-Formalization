module

public import NPHardness.PlanarAssemblyInactive
public import NPHardness.PlanarAssemblyPieces
public import NPHardness.PlanarAssemblyOccurrencePorts
public import Complexity.Planar.Incidence

/-! Exact source-incidence vertices and separation of their selected ports in
the actual concatenation of variable and clause gadget hypermaps. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

theorem placed_clause_lengths (f : CNF) :
    (placeFormula [] f).map List.length = f.map List.length := by
  conv => rhs; rw [← placeFormula_forget [] f]
  simp only [List.map_map,Function.comp_def,List.length_map]

theorem placed_occurrence_count (f : CNF) :
    (placeFormula [] f).flatten.length = (incidenceGraph f).length := by
  rw [length_flatten',placed_clause_lengths,incidenceGraph_length]

theorem occurrencePosition_offset (f : CNF) (i : OccurrenceIndex f) :
    (((placeFormula [] f).map List.length).take (occurrencePosition f i).clause.val).sum +
      (occurrencePosition f i).slot.val = i.val := by
  have ho := getElem?_flatten_offset (placeFormula [] f)
    (occurrencePosition f i).clause.val (occurrencePosition f i).slot.val
    (occurrencePosition f i).clause.isLt (occurrencePosition f i).slot.isLt
  rw [occurrencePosition_get] at ho
  obtain ⟨hlt,hget⟩ := List.getElem?_eq_some_iff.mp ho
  exact ((placedOccurrences_nodup f).getElem_inj (hi := hlt) (hj := i.isLt)).mp hget

theorem occurrence_incidence_lookup (f : CNF) (i : OccurrenceIndex f) :
    (incidenceGraph f)[i.val]? =
      some (Sum.inl (occurrence f i).literal.var,Sum.inr (occurrencePosition f i).clause.val) := by
  let j := (occurrencePosition f i).clause
  let s := (occurrencePosition f i).slot
  have hj : j.val < f.length := by
    simpa only [← placeFormula_length [] f] using j.isLt
  have hc : f[j.val] = ((placeFormula [] f)[j.val]).map PlacedLiteral.literal := by
    have he := congrArg (fun xs : CNF => xs[j.val]?) (placeFormula_forget [] f)
    rw [List.getElem?_map,List.getElem?_eq_getElem j.isLt,List.getElem?_eq_getElem hj] at he
    exact (Option.some.inj he).symm
  have hs : s.val < f[j.val].length := by rw [hc,List.length_map]; exact s.isLt
  have hv : f[j.val][s.val].var = (occurrence f i).literal.var := by
    simp only [hc,List.getElem_map]
    exact congrArg (fun p : PlacedLiteral => p.literal.var) (occurrencePosition f i).value
  have ho := occurrencePosition_offset f i
  rw [placed_clause_lengths] at ho
  conv => lhs; rw [← ho]
  simpa only [hv] using incidenceGraph_getElem? f j.val s.val hj hs

noncomputable def occurrenceVertex (f : CNF) (d : Fin (2*(placeFormula [] f).flatten.length)) : Sum Nat Nat :=
  let i : OccurrenceIndex f := ⟨d.val/2,by have := d.isLt; omega⟩
  if d.val%2=0 then Sum.inl (occurrence f i).literal.var
  else Sum.inr (occurrencePosition f i).clause.val

theorem occurrence_incidence_end (f : CNF) (d : Fin (2*(placeFormula [] f).flatten.length)) :
    halfEdgeEnd (incidenceGraph f) d.val = some (occurrenceVertex f d) := by
  unfold halfEdgeEnd occurrenceVertex
  rw [occurrence_incidence_lookup f ⟨d.val/2,by have := d.isLt; omega⟩]
  by_cases h : d.val%2=0 <;> simp [h]

/-- Two selected ports connected before assembly come from the same actual
source vertex. This uses only the disjoint block construction, and does not
assume that every local gadget is connected. -/
theorem LocalPortChoices.sourcePort_connected_vertex {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (H : LocalMaps (ungluedFormulaPieces k f))
    (d e : Fin (2*(placeFormula [] f).flatten.length))
    (h : Connected (piecesMap (ungluedFormulaPieces k f) H) (C.sourcePort hf d) (C.sourcePort hf e)) :
    occurrenceVertex f d = occurrenceVertex f e := by
  unfold LocalPortChoices.sourcePort occurrenceVertex at *
  dsimp only at *
  by_cases hd : d.val%2=0 <;> by_cases he : e.val%2=0 <;>
    simp only [hd,he,↓reduceIte] at h ⊢
  · have hi := congrArg Fin.val (piecesMap_path_same_piece _ H _ _ _ _ h)
    exact congrArg Sum.inl hi
  · have hi := congrArg Fin.val (piecesMap_path_same_piece _ H _ _ _ _ h)
    have hb := occurrence_variable_lt hf (⟨d.val/2,by have := d.isLt; omega⟩ : OccurrenceIndex f)
    change (occurrence f _).literal.var = variableBound f + (occurrencePosition f _).clause.val at hi
    omega
  · have hi := congrArg Fin.val (piecesMap_path_same_piece _ H _ _ _ _ h)
    have hb := occurrence_variable_lt hf (⟨e.val/2,by have := e.isLt; omega⟩ : OccurrenceIndex f)
    change variableBound f + (occurrencePosition f _).clause.val = (occurrence f _).literal.var at hi
    omega
  · have hi := congrArg Fin.val (piecesMap_path_same_piece _ H _ _ _ _ h)
    change variableBound f + (occurrencePosition f _).clause.val =
      variableBound f + (occurrencePosition f _).clause.val at hi
    exact congrArg Sum.inr (Nat.add_left_cancel hi)

/-- Actual registered incidence-node semantics discharge the sole component
separation input of the automatic inactive-root argument. -/
theorem LocalPortChoices.sourcePort_source_nodes_separate {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (H : LocalMaps (ungluedFormulaPieces k f))
    (I : Hypermap (2*(placeFormula [] f).flatten.length))
    (hI : ∀ d e, Reaches I.node d e ↔
      halfEdgeEnd (incidenceGraph f) d.val = halfEdgeEnd (incidenceGraph f) e.val)
    (d e : Fin (2*(placeFormula [] f).flatten.length))
    (h : Connected (piecesMap (ungluedFormulaPieces k f) H) (C.sourcePort hf d) (C.sourcePort hf e)) :
    Reaches I.node d e := by
  apply (hI d e).mpr
  rw [occurrence_incidence_end,occurrence_incidence_end,
    C.sourcePort_connected_vertex hf H d e h]

end STACS2027.PlanarAssembly
