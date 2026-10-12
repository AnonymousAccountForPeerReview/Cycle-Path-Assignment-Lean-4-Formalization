module

public import NPHardness.PlanarSourceDeletionRotation
public import NPHardness.PlanarSourceRotationTable

/-!
The executable incidence-only comb embedding retains exactly the registered
clockwise occurrence order after its spine is deleted. This identifies the
rotation used by the computable occurrence-ring construction with the list
order used by the polynomial source emitter.
-/

@[expose] public section
namespace STACS2027.PlanarSource.ComputableComb
open Complexity Complexity.SAT Complexity.Planar Comb
open STACS2027.PlanarGluing
open STACS2027.PlanarSource.Embedding

/-- Injective relabeling commutes with cyclic successor on a nonempty orbit. -/
theorem rnext_map_injective (f : Nat → Nat) (hf : ∀ a b, f a=f b → a=b)
    {xs : List Nat} (hn : xs.Nodup) {x : Nat} (hx : x∈xs) :
    rnext (xs.map f) (f x)=f (rnext xs x) := by
  obtain ⟨i,hi,rfl⟩ := mem_getElem hx
  have hn' : (xs.map f).Nodup := nodup_map_of_injOn' f hn (fun a _ b _ h => hf a b h)
  have hi' : i<(xs.map f).length := by simpa using hi
  rw [show f xs[i]=(xs.map f)[i] from (List.getElem_map f).symm,
    rnext_getElem hn' hi',rnext_getElem hn hi]
  simp only [List.length_map,List.getElem_map]

theorem incidence_length_nM (f : CNF) : (incidenceGraph f).length=nM f := by
  rw [incidenceGraph_length]
  rfl

/-- Precisely the two spine darts are removed from each variable rotation. -/
theorem rot_filter_incidence (f : CNF) (v : Nat) :
    (rot f v).filter (fun d => decide (d<2*(incidenceGraph f).length)) =
      (RotationTable.incidenceOrder f v).map (2*·) := by
  have hlegs (s : Bool) (w : Nat) :
      (legs f s w).filter (fun d => decide (d<2*nM f))=legs f s w := by
    apply List.filter_eq_self.mpr
    intro d hd
    obtain ⟨e,he,rfl⟩ := legs_mem.mp hd
    apply decide_eq_true
    have := he.1
    omega
  rw [incidence_length_nM]
  simp only [rot,List.filter_append,List.filter_cons,List.filter_nil]
  have he : ¬spE f v<2*nM f := by unfold spE; omega
  have hw : ¬spW f v<2*nM f := by unfold spW; omega
  simp only [he,hw,decide_false,Bool.false_eq_true,ite_false,List.nil_append,List.append_nil,hlegs]
  simp only [RotationTable.incidenceOrder,List.map_append,legs]

theorem variableAt_eq_vr {f : CNF} {i : Nat} (hi : i<nM f) :
    FromFormula.variableAt f i=vr f (oj f i) (ot f i) := by
  obtain ⟨hj,ht,hoff⟩ := occ_spec f i hi
  have ht' : ot f i<f[oj f i].length := by rw [←kl_of_lt f _ hj]; exact ht
  have hget := getElem?_flatten_offset f (oj f i) (ot f i) hj ht'
  change f.flatten[off f (oj f i)+ot f i]?=f[oj f i][ot f i]? at hget
  rw [hoff,List.getElem?_eq_getElem ht'] at hget
  rw [FromFormula.variableAt,hget,vr_of_lt f _ _ hj ht]
  rfl

/-- The node successor of the concrete restricted comb embedding is the
successor of the top-then-bottom incident-occurrence list. -/
theorem incidenceEmbedding_node {f : CNF} (h : CombOK f)
    (i : Fin (incidenceGraph f).length) :
    (((embedding h).prefix (incidenceGraph f) (variableCycle f)).map.node (d2 i 0)).val =
      2*rnext (RotationTable.incidenceOrder f (FromFormula.variableAt f i.val)) i.val := by
  have hi : i.val<nM f := by simpa only [incidence_length_nM] using i.isLt
  have hleg := leg_in_rot h hi
  have hv : FromFormula.variableAt f i.val=vtx f (2*i.val) := by
    rw [variableAt_eq_vr hi,vtx_leg hi]
  have hmem : i.val∈RotationTable.incidenceOrder f (vtx f (2*i.val)) := by
    apply (RotationTable.mem_incidenceOrder f hleg.2).mpr
    exact ⟨hi,(vtx_leg hi).symm⟩
  have hr := GraphEmbedding.prefix_rnext (incidenceGraph f) (variableCycle f) (embedding h)
    (rot f (vtx f (2*i.val))) (rot_nodup h)
    (by
      intro d hd
      rw [es_length]
      exact (rot_mem h hleg.2 hd).1)
    (by
      intro d hd
      obtain ⟨_,hc,hv'⟩ := rot_mem h hleg.2 hd
      rw [embedding_node,next_eq,nxt_rot h hc,hv'])
    (d2 i 0) (by simpa only [d2,dart,Fin.val_zero,Nat.add_zero] using hleg.1)
  have hd0 : (d2 i 0).val=2*i.val := by simp [d2,dart]
  rw [rot_filter_incidence,hd0,rnext_map_injective (2*·) (by intro a b hab; omega)
    (RotationTable.incidenceOrder_nodup h _) hmem] at hr
  rw [hv]
  exact hr

/-- The exact list-order successor read by the computational rotation extractor. -/
theorem incidenceEmbedding_edgeData_next {f : CNF} (h : CombOK f)
    (i : Fin (incidenceGraph f).length) :
    ((ComputableFormula.edgeData f ((embedding h).prefix (incidenceGraph f) (variableCycle f))).rotation.varRot.toFun i).val =
      rnext (RotationTable.incidenceOrder f (FromFormula.variableAt f i.val)) i.val := by
  rw [ComputableFormula.edgeData_next,incidenceEmbedding_node]
  omega

theorem rotationData_cast_next {f : CNF} {n m : Nat} (h : n=m)
    (D : ComputableFormula.RotationData f n) (i : Fin m) :
    (((h ▸ D) : ComputableFormula.RotationData f m).rotation.varRot.toFun i).val =
      (D.rotation.varRot.toFun ⟨i.val,by have := i.isLt; omega⟩).val := by
  cases h
  rfl

/-- The concrete occurrence-ring reduction and the source emitter use precisely
the same variable successor, including the flatten/incidence index transport. -/
theorem incidenceEmbedding_formulaData_next {f : CNF} (h : CombOK f)
    (i : Fin f.flatten.length) :
    ((ComputableFormula.formulaData f ((embedding h).prefix (incidenceGraph f) (variableCycle f))).rotation.varRot.toFun i).val =
      rnext (RotationTable.incidenceOrder f (FromFormula.variableAt f i.val)) i.val := by
  rw [ComputableFormula.formulaData,rotationData_cast_next]
  exact incidenceEmbedding_edgeData_next h _

theorem gridIncidenceEmbedding_formulaData_next (W m : Nat)
    (bits : Nat → Nat → Bool×Bool) (hm : 1≤m)
    (i : Fin (Grid.gridCNF W m bits).flatten.length) :
    ((ComputableFormula.formulaData (Grid.gridCNF W m bits)
      (gridIncidenceEmbedding W m bits hm)).rotation.varRot.toFun i).val =
      rnext (RotationTable.incidenceOrder (Grid.gridCNF W m bits)
        (FromFormula.variableAt (Grid.gridCNF W m bits) i.val)) i.val :=
  incidenceEmbedding_formulaData_next (Grid.gridCNF_combOK hm bits) i

end STACS2027.PlanarSource.ComputableComb
