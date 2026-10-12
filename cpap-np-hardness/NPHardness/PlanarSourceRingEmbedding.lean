module

public import NPHardness.PlanarSourceRingDarts
public import NPHardness.PlanarOperationsPorts

/-! Executable dart coordinates for the incidence graph of the occurrence-ring
CNF, in its edge order. -/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar STACS2027.PlanarGluing
open STACS2027.PlanarSource.Embedding
open STACS2027.PlanarSource.Embedding.BipartiteRotation
open STACS2027.PlanarSource.ComputableComb

theorem implicationEdges_succ (start E : Nat) (next : Nat → Nat) :
    implicationEdges start (E+1) next=implicationEdges start E next++
      [(Sum.inl E,Sum.inr (start+E)),(Sum.inl (next E),Sum.inr (start+E))] := by
  simp [implicationEdges,List.range_succ]

@[simp] theorem implicationEdges_length (start E : Nat) (next : Nat → Nat) :
    (implicationEdges start E next).length=2*E := by
  induction E with
  | zero => rfl
  | succ E ih => rw [implicationEdges_succ,List.length_append,ih]; simp; omega

theorem implicationEdges_get (start E : Nat) (next : Nat → Nat) (i : Nat) (hi : i<E) :
    (implicationEdges start E next)[2*i]?=some (Sum.inl i,Sum.inr (start+i)) ∧
    (implicationEdges start E next)[2*i+1]?=some (Sum.inl (next i),Sum.inr (start+i)) := by
  induction E with
  | zero => omega
  | succ E ih =>
    rw [implicationEdges_succ]
    by_cases hi' : i<E
    · rw [List.getElem?_append_left (by rw [implicationEdges_length]; omega),
        List.getElem?_append_left (by rw [implicationEdges_length]; omega)]
      exact ih hi'
    · have he : i=E := by omega
      subst i
      rw [List.getElem?_append_right (by rw [implicationEdges_length]; omega),
        List.getElem?_append_right (by rw [implicationEdges_length]; omega),implicationEdges_length]
      simp

theorem ringFormula_incidence_get (f : CNF) (next signs)
    (clause : Fin f.flatten.length → Fin f.length)
    (hc : ∀ i : Fin f.flatten.length,
      ((incidenceGraph f)[i.val]'(by rw [incidenceGraph_length_flatten]; exact i.isLt)).2 =
        Sum.inr (clause i).val)
    (i : Fin f.flatten.length) :
    (incidenceGraph (ringFormula f next signs))[i.val]?=
      some (Sum.inl i.val,Sum.inr (clause i).val) ∧
    (incidenceGraph (ringFormula f next signs))[f.flatten.length+2*i.val]?=
      some (Sum.inl i.val,Sum.inr (f.length+i.val)) ∧
    (incidenceGraph (ringFormula f next signs))[f.flatten.length+2*i.val+1]?=
      some (Sum.inl (next i.val),Sum.inr (f.length+i.val)) := by
  rw [ringFormula_incidence,copyIncidence_eq_range f clause hc]
  have hlen : ((List.range f.flatten.length).map
      (fun i => (Sum.inl i,Sum.inr (clauseIndex clause i)) : Nat → IncidenceEdge)).length=f.flatten.length := by simp
  rw [List.getElem?_append_left (by rw [hlen]; exact i.isLt)]
  constructor
  · rw [List.getElem?_map,List.getElem?_range i.isLt]
    simp only [Option.map_some,clauseIndex,dite_eq_left i.isLt]
  · rw [List.getElem?_append_right (by rw [hlen]; omega),
      List.getElem?_append_right (by rw [hlen]; omega),hlen]
    have he := implicationEdges_get f.length f.flatten.length next i.val i.isLt
    simpa only [Nat.add_sub_cancel_left,show f.flatten.length+2*i.val+1-f.flatten.length=2*i.val+1 by omega]
      using he

def ringFormulaDarts (f : CNF) (next : Nat → Nat) (signs : Nat → Bool) :
    DartEquiv (6*f.flatten.length) (2*(incidenceGraph (ringFormula f next signs)).length) :=
  (ringDarts f.flatten.length).trans (DartEquiv.cast (by
    rw [incidenceGraph_length_flatten,ringFormula_flatten_length]
    omega))

theorem ringFormulaDarts_val_eq (f : CNF) (next : Nat → Nat) (signs : Nat → Bool)
    (d : Fin (6*f.flatten.length)) :
    ((ringFormulaDarts f next signs).toFun d).val=((ringDarts f.flatten.length).toFun d).val := rfl

theorem ringFormulaDarts_ends (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat → Bool) (clause : Fin f.flatten.length → Fin f.length)
    (hc : ∀ i : Fin f.flatten.length,
      ((incidenceGraph f)[i.val]'(by rw [incidenceGraph_length_flatten]; exact i.isLt)).2 =
        Sum.inr (clause i).val) (d : Fin (6*f.flatten.length)) :
    halfEdgeEnd (incidenceGraph (ringFormula f (nextIndex B) signs))
      ((ringFormulaDarts f (nextIndex B) signs).toFun d).val =
        some (encodeExpanded (expandedVertex B clause d)) := by
  apply six_cases (fun d => _) ?_ d
  intro i
  obtain ⟨hc0,hc1,hc2⟩ := ringFormula_incidence_get f (nextIndex B) signs clause hc i
  obtain ⟨h0,h1⟩ := halfEdgeEnd_of_getElem? _ _ _ _ hc0
  obtain ⟨h2,h3⟩ := halfEdgeEnd_of_getElem? _ _ _ _ hc1
  obtain ⟨h5,h4⟩ := halfEdgeEnd_of_getElem? _ _ _ _ hc2
  have h2' : 2*(f.flatten.length+2*i.val)=2*f.flatten.length+4*i.val := by omega
  have h3' : 2*(f.flatten.length+2*i.val)+1=2*f.flatten.length+4*i.val+1 := by omega
  have h4' : 2*(f.flatten.length+2*i.val+1)+1=2*f.flatten.length+4*i.val+3 := by omega
  have h5' : 2*(f.flatten.length+2*i.val+1)=2*f.flatten.length+4*i.val+2 := by omega
  rw [h2'] at h2
  rw [h3'] at h3
  rw [h4'] at h4
  rw [h5',nextIndex_at B i] at h5
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [ringFormulaDarts_val_eq,ringDarts_zero]
    simpa [expandedVertex,d6,encodeExpanded] using h0
  · rw [ringFormulaDarts_val_eq,ringDarts_one]
    simpa [expandedVertex,d6,encodeExpanded] using h1
  · rw [ringFormulaDarts_val_eq,ringDarts_two]
    simpa [expandedVertex,d6,encodeExpanded] using h2
  · rw [ringFormulaDarts_val_eq,ringDarts_three]
    simpa [expandedVertex,d6,encodeExpanded] using h3
  · rw [ringFormulaDarts_val_eq,ringDarts_four]
    simpa [expandedVertex,d6,encodeExpanded] using h4
  · rw [ringFormulaDarts_val_eq,ringDarts_five]
    simpa [expandedVertex,d6,encodeExpanded] using h5

end STACS2027.PlanarSource.Formula
