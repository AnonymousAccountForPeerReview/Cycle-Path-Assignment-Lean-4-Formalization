module

public import NPHardness.PlanarAssemblyRouting

/-!
At most one original face is consumed per source incidence vertex. This follows
from actual first-hit boundary order: source-node walks become old local-face
walks. The other original face minima are precisely untouched interior roots.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly.OrderedIncidencePorts
open Complexity Complexity.Planar PlanarGluing
attribute [local instance] Classical.propDecidable
variable {n m : Nat} {G : Hypermap n} {P : PortPairing G} {I : Hypermap m}
  (O : OrderedIncidencePorts P I)

/-- Adjacent darts in a source node cycle lie on one actual old gadget face. -/
theorem source_node_step_face (i : Fin m) :
    Reaches G.face (O.port i) (O.port (I.node i)) := by
  have he : I.face (I.edge (I.node i))=i := hm_node_inj I _ _ (I.edgeK (I.node i))
  obtain ⟨k,_,hk,_⟩ := O.order (I.node i)
  rw [he] at hk
  exact (show Reaches G.face (O.port (I.node i)) (O.port i) from ⟨k+1,hk⟩).symm (hm_face_inj G)

/-- Source node orbits are realized as old local face orbits. -/
theorem source_node_face {i j : Fin m} (h : Reaches I.node i j) :
    Reaches G.face (O.port i) (O.port j) := by
  obtain ⟨k,rfl⟩ := h
  induction k generalizing i with
  | zero => exact Reaches.refl _ _
  | succ k ih => exact (O.source_node_step_face i).trans (ih (i:=I.node i))

/-- A non-interior old face root reaches a selected port on its actual face. -/
theorem noninterior_has_port {d : Fin n} (hroot : CycleMin G.face d=true)
    (hi : O.routing.interiorRoot d=false) : ∃i,Reaches G.face d (O.port i) := by
  cases hm : P.marked d
  · by_cases hn : ∃ i, NextPort P O.port d i
    · obtain ⟨i,k,_,hk,_⟩ := hn
      exact ⟨i,k,hk⟩
    · have hb : O.boundary d=none := by simp only [boundary,dite_eq_right hn]
      change (CycleMin G.face d && !P.marked d && decide (O.boundary d=none))=false at hi
      simp [hroot,hm,hb] at hi
  · obtain ⟨i,he⟩ := O.every_marked d hm
    exact ⟨i,0,he.symm⟩

/-- The old faces that meet the assembled boundary inject into source node
cycles; distinct old faces cannot consume the same source incidence vertex. -/
theorem consumed_faces_le :
    (List.finRange n).countP (fun d => CycleMin G.face d && !O.routing.interiorRoot d) ≤
      cycleCount I.node := by
  let roots := (List.finRange n).filter fun d => CycleMin G.face d && !O.routing.interiorRoot d
  have hex : ∀d∈roots,∃i,Reaches G.face d (O.port i) := by
    intro d hd
    have hh := (List.mem_filter.mp hd).2
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hh
    exact O.noninterior_has_port hh.1 hh.2
  let witnesses := roots.attach.map fun d => cmin I.node (Classical.choose (hex d.val d.property))
  have hnd : witnesses.Nodup := by
    apply nodup_map_of_injOn' _ (nodup_of_map Subtype.val (by
      change (roots.attach.map (fun x => id x.val)).Nodup
      rw [List.attach_map_val,List.map_id]
      exact (List.nodup_finRange n).filter _))
    intro a _ b _ he
    apply Subtype.ext
    have ha := Classical.choose_spec (hex a.val a.property)
    have hb := Classical.choose_spec (hex b.val b.property)
    have hij : Reaches I.node (Classical.choose (hex a.val a.property))
        (Classical.choose (hex b.val b.property)) := by
      exact (reaches_cmin I.node _).trans (by
        rw [he]
        exact (reaches_cmin I.node _).symm (hm_node_inj I))
    have hab := ha.trans ((O.source_node_face hij).trans (hb.symm (hm_face_inj G)))
    have hca : CycleMin G.face a.val=true := by
      have h := (List.mem_filter.mp a.property).2
      simp only [Bool.and_eq_true] at h
      exact h.1
    have hcb : CycleMin G.face b.val=true := by
      have h := (List.mem_filter.mp b.property).2
      simp only [Bool.and_eq_true] at h
      exact h.1
    obtain ⟨k,hk⟩ := hab
    have hc := cmin_iterate (hm_face_inj G) a.val k
    rw [hk,(cmin_eq_iff (hm_face_inj G) a.val).mpr hca,
      (cmin_eq_iff (hm_face_inj G) b.val).mpr hcb] at hc
    exact hc.symm
  have hb := length_le_countP (CycleMin I.node) witnesses hnd (by
    intro i hi
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp hi
    exact (List.mem_filter.mp (cmin_mem_cycleRoots (hm_node_inj I)
      (Classical.choose (hex d.val d.property)))).2)
  simpa only [witnesses,List.length_map,List.length_attach,roots,
    ←List.countP_eq_length_filter,cycleCount_eq] using hb

/-- All original faces except at most one per source node remain interior. -/
theorem interior_face_loss :
    cycleCount G.face ≤ O.routing.interiorFaceCount + cycleCount I.node := by
  have hs := PortPairing.countP_split (CycleMin G.face) O.routing.interiorRoot (List.finRange n)
  have he : (fun d => CycleMin G.face d && O.routing.interiorRoot d)=O.routing.interiorRoot := by
    funext d
    unfold BoundaryRouting.interiorRoot
    cases CycleMin G.face d <;> simp
  rw [he] at hs
  have hb := O.consumed_faces_le
  change (List.finRange n).countP (CycleMin G.face) ≤
    (List.finRange n).countP O.routing.interiorRoot + cycleCount I.node
  omega
end STACS2027.PlanarAssembly.OrderedIncidencePorts
