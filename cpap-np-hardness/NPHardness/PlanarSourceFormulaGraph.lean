module

public import NPHardness.PlanarSourceFormula

/-! Concrete relabeling and edge-order correspondence for the occurrence-ring
embedding. Parallel incidences are retained; the reversed third edge in each
three-edge block is corrected by the checked edge-orientation theorem. -/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar
open STACS2027.PlanarSource.Embedding
open STACS2027.PlanarSource.Embedding.BipartiteRotation
open STACS2027.PlanarGluing

def encodeExpanded {E m : Nat} : ExpandedVertex E (Fin m) → Sum Nat Nat
  | .inl i => .inl i.val
  | .inr (.inl j) => .inr j.val
  | .inr (.inr i) => .inr (m+i.val)

theorem encodeExpanded_injective {E m : Nat} (a b : ExpandedVertex E (Fin m))
    (h : encodeExpanded a = encodeExpanded b) : a = b := by
  cases a with
  | inl a => cases b with
    | inl b => simp only [encodeExpanded,Sum.inl.injEq] at h; exact congrArg Sum.inl (Fin.ext h)
    | inr b => cases b <;> cases h
  | inr a => cases a with
    | inl a => cases b with
      | inl b => cases h
      | inr b => cases b with
        | inl b => simp only [encodeExpanded,Sum.inr.injEq] at h; exact congrArg (Sum.inr ∘ Sum.inl) (Fin.ext h)
        | inr b => simp only [encodeExpanded,Sum.inr.injEq] at h; have := a.isLt; omega
    | inr a => cases b with
      | inl b => cases h
      | inr b => cases b with
        | inl b => simp only [encodeExpanded,Sum.inr.injEq] at h; have := b.isLt; omega
        | inr b => simp only [encodeExpanded,Sum.inr.injEq] at h; exact congrArg (Sum.inr ∘ Sum.inr) (Fin.ext (by omega))

def nextIndex {E : Nat} (B : BipartiteRotation E) (i : Nat) : Nat :=
  if hi : i < E then (B.varRot.toFun ⟨i,hi⟩).val else i

def clauseIndex {E m : Nat} (clause : Fin E → Fin m) (i : Nat) : Nat :=
  if hi : i < E then (clause ⟨i,hi⟩).val else 0

def expandedPair (m : Nat) (next clause : Nat → Nat) (j : Nat) : IncidenceEdge :=
  let i := j / 3
  match j % 3 with
  | 0 => (.inl i,.inr (clause i))
  | 1 => (.inl i,.inr (m+i))
  | _ => (.inr (m+i),.inl (next i))

theorem expandedPair_at {E m : Nat} (B : BipartiteRotation E) (clause : Fin E → Fin m)
    (j : Fin (3*E)) :
    (encodeExpanded (expandedVertex B clause ⟨2*j.val,by have := j.isLt; omega⟩),
     encodeExpanded (expandedVertex B clause ⟨2*j.val+1,by have := j.isLt; omega⟩)) =
      expandedPair m (nextIndex B) (clauseIndex clause) j.val := by
  have hj : j.val/3 < E := by have := j.isLt; omega
  have hd : (2*j.val)/6 = j.val/3 := by omega
  have hd' : (2*j.val+1)/6 = j.val/3 := by omega
  rcases (show j.val%3 = 0 ∨ j.val%3 = 1 ∨ j.val%3 = 2 by omega) with h | h | h
  · have hm : (2*j.val)%6 = 0 := by omega
    have hm' : (2*j.val+1)%6 = 1 := by omega
    simp [expandedPair,expandedVertex,encodeExpanded,index,hd,hd',hm,hm',h,clauseIndex,hj]
  · have hm : (2*j.val)%6 = 2 := by omega
    have hm' : (2*j.val+1)%6 = 3 := by omega
    simp [expandedPair,expandedVertex,encodeExpanded,index,hd,hd',hm,hm',h]
  · have hm : (2*j.val)%6 = 4 := by omega
    have hm' : (2*j.val+1)%6 = 5 := by omega
    simp [expandedPair,expandedVertex,encodeExpanded,index,hd,hd',hm,hm',h,nextIndex,hj]

theorem expandedEdges_encoded {E m : Nat} (B : BipartiteRotation E) (clause : Fin E → Fin m) :
    ((expandedEdges B clause).map fun e => (encodeExpanded e.1,encodeExpanded e.2)) =
      (List.range (3*E)).map (expandedPair m (nextIndex B) (clauseIndex clause)) := by
  rw [expandedEdges,List.map_map]
  calc
    _ = (List.finRange (3*E)).map (fun j => expandedPair m (nextIndex B) (clauseIndex clause) j.val) := by
      apply List.map_congr_left
      intro j _
      exact expandedPair_at B clause j
    _ = _ := by
      simpa only [List.map_map,Function.comp_def] using congrArg (List.map (expandedPair m (nextIndex B) (clauseIndex clause))) (Complexity.Planar.map_val_finRange (3*E))

def correctedTriples (E m : Nat) (next clause : Nat → Nat) : List IncidenceEdge :=
  (List.range E).flatMap fun i =>
    [(.inl i,.inr (clause i)),(.inl i,.inr (m+i)),(.inl (next i),.inr (m+i))]

theorem expandedEdges_corrected {E m : Nat} (B : BipartiteRotation E) (clause : Fin E → Fin m) :
    flipEdges ((expandedEdges B clause).map fun e => (encodeExpanded e.1,encodeExpanded e.2))
      (fun j => j%3 == 2) = correctedTriples E m (nextIndex B) (clauseIndex clause) := by
  rw [expandedEdges_encoded]
  simp only [flipEdges,Complexity.Planar.Grid.zipIdx_map_range,List.map_map,Nat.zero_add]
  rw [map_range_triples]
  apply congrArg (List.flatMap · (List.range E))
  funext i
  simp [expandedPair,flipEdge,Nat.mul_add_div]

theorem incidenceGraph_length_flatten (f : CNF) :
    (incidenceGraph f).length = f.flatten.length := incidenceAt_length 0 f

theorem copyIncidence_eq_range (f : CNF) (clause : Fin f.flatten.length → Fin f.length)
    (hc : ∀ i : Fin f.flatten.length,
      ((incidenceGraph f)[i.val]'(by rw [incidenceGraph_length_flatten]; exact i.isLt)).2 =
        Sum.inr (clause i).val) :
    (incidenceGraph f).mapIdx (fun i e => ((Sum.inl i,e.2) : IncidenceEdge)) =
      (List.range f.flatten.length).map (fun i => (Sum.inl i,Sum.inr (clauseIndex clause i))) := by
  apply List.ext_getElem
  · simp [incidenceGraph_length_flatten]
  · intro i hi hj
    have hb : i < f.flatten.length := by simpa only [List.length_map,List.length_range] using hj
    simp only [List.getElem_mapIdx,List.getElem_map,List.getElem_range]
    rw [hc ⟨i,hb⟩]
    simp only [clauseIndex,dite_eq_left hb]

theorem ringFormula_incidence_perm (f : CNF) (next : Nat → Nat) (signs : Nat → Bool)
    (clause : Fin f.flatten.length → Fin f.length)
    (hc : ∀ i : Fin f.flatten.length,
      ((incidenceGraph f)[i.val]'(by rw [incidenceGraph_length_flatten]; exact i.isLt)).2 =
        Sum.inr (clause i).val) :
    (incidenceGraph (ringFormula f next signs)).Perm
      (correctedTriples f.flatten.length f.length next (clauseIndex clause)) := by
  rw [ringFormula_incidence,copyIncidence_eq_range f clause hc]
  exact map_flatMap_interleave (List.range f.flatten.length)
    (fun i => (Sum.inl i,Sum.inr (clauseIndex clause i)))
    (fun i => [(Sum.inl i,Sum.inr (f.length+i)),(Sum.inl (next i),Sum.inr (f.length+i))])

/-- The dart-level expansion is the incidence graph of the actual CNF, up to
an injective vertex encoding, endpoint reversal, and an edge-list permutation.
No duplicate incidences are removed. -/
theorem ringFormula_planar_of_expanded (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat → Bool) (clause : Fin f.flatten.length → Fin f.length)
    (hc : ∀ i : Fin f.flatten.length,
      ((incidenceGraph f)[i.val]'(by rw [incidenceGraph_length_flatten]; exact i.isLt)).2 =
        Sum.inr (clause i).val)
    (hp : PlanarGraph (expandedEdges B clause)) :
    PlanarGraph (incidenceGraph (ringFormula f (nextIndex B) signs)) := by
  have henc := planarGraph_relabel encodeExpanded encodeExpanded_injective hp
  have hflip := (planarGraph_flipEdges
    ((expandedEdges B clause).map fun e => (encodeExpanded e.1,encodeExpanded e.2))
    (fun j => j%3 == 2)).mpr henc
  rw [expandedEdges_corrected] at hflip
  exact (planarGraph_perm (ringFormula_incidence_perm f (nextIndex B) signs clause hc)).mpr hflip

end STACS2027.PlanarSource.Formula
