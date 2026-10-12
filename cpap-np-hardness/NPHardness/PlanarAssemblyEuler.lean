module

public import NPHardness.PlanarAssemblyNodeCount
public import NPHardness.PlanarAssemblyFaceCount
public import NPHardness.PlanarAssemblyComponents

/-!
Euler's inequality for the actual simultaneous port-assembly hypermap.
The theorem combines proved node loss, retained-port digons, untouched
interior faces, source-face routing, and actual component connectivity.
It requires strict spherical input gadgets and a planar incidence rotation.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

/-- A fixed-point-free involution has exactly one cycle per pair of darts. -/
theorem involution_cycles_twice {m : Nat} (p : Fin m → Fin m)
    (hp : ∀d,p (p d)=d) (hne : ∀d,p d≠d) : 2*cycleCount p=m := by
  have hinj : ∀a b,p a=p b→a=b := by
    intro a b h
    have hh := congrArg p h
    simpa only [hp] using hh
  have hiter : ∀k d,iterate p k d=d ∨ iterate p k d=p d := by
    intro k
    induction k with
    | zero => intro d; exact Or.inl rfl
    | succ k ih =>
      intro d
      rw [iterate_succ']
      rcases ih d with h | h
      · exact Or.inr (congrArg p h)
      · exact Or.inl (by rw [h,hp])
  have hcyc : ∀d,CycleMin p d=decide (d.val<(p d).val) := by
    intro d
    have hm : 1<m := by
      have hd := d.isLt
      have hpd := (p d).isLt
      apply Classical.byContradiction
      intro h
      exact hne d (Fin.ext (by omega))
    have hneq : d.val≠(p d).val := fun h => hne d (Fin.ext h.symm)
    apply Bool.eq_iff_iff.mpr
    simp only [CycleMin,List.all_eq_true,List.mem_range,Nat.ble_eq,decide_eq_true_eq]
    constructor
    · intro h
      have hh := h 1 hm
      change d.val≤(p d).val at hh
      omega
    · intro h k _
      rcases hiter k d with he | he
      · rw [he]; exact Nat.le_refl _
      · rw [he]; omega
  let asc : Fin m → Bool := fun d => decide (d.val<(p d).val)
  let desc : Fin m → Bool := fun d => decide ((p d).val<d.val)
  have hperm : ((List.finRange m).map p).Perm (List.finRange m) := by
    apply (List.perm_ext_iff_of_nodup
      (nodup_map_of_injOn' p (List.nodup_finRange m) (fun a _ b _ h=>hinj a b h))
      (List.nodup_finRange m)).mpr
    intro d
    constructor
    · intro _; exact List.mem_finRange d
    · intro _; exact List.mem_map.mpr ⟨p d,List.mem_finRange _,hp d⟩
  have heq := hperm.countP_eq asc
  rw [List.countP_map] at heq
  have hfun : (fun d=>asc (p d))=desc := by
    funext d
    simp only [asc,desc,hp]
  change (List.finRange m).countP (fun d=>asc (p d)) = _ at heq
  rw [hfun] at heq
  have htotal : ∀xs:List (Fin m),xs.length=xs.countP asc+xs.countP desc := by
    intro xs
    induction xs with
    | nil => simp
    | cons d xs ih =>
      have hneq : d.val≠(p d).val := fun h=>hne d (Fin.ext h.symm)
      rcases Nat.lt_or_gt_of_ne hneq with h | h
      · have hn : ¬(p d).val<d.val := by omega
        simp [asc,desc,h,hn] at *
        omega
      · have hn : ¬d.val<(p d).val := by omega
        simp [asc,desc,h,hn] at *
        omega
  have ht := htotal (List.finRange m)
  rw [List.length_finRange] at ht
  rw [cycleCount_eq]
  have hc : CycleMin p=asc := funext hcyc
  rw [hc]
  omega

namespace OrderedIncidencePorts
variable {n m : Nat} {G : Hypermap n} {P : PortPairing G} {I : Hypermap m}
  (O : OrderedIncidencePorts P I)
include O

/-- Selected port darts form a bijection with source incidence darts. -/
theorem marked_count : (List.finRange n).countP P.marked=m := by
  have hp : ((List.finRange m).map O.port).Perm ((List.finRange n).filter P.marked) := by
    apply (List.perm_ext_iff_of_nodup
      (nodup_map_of_injOn' O.port (List.nodup_finRange m)
        (fun a _ b _ h=>O.injective a b h)) ((List.nodup_finRange n).filter _)).mpr
    intro d
    constructor
    · intro hd
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hd
      exact List.mem_filter.mpr ⟨List.mem_finRange _,O.marked_port i⟩
    · intro hd
      obtain ⟨i,hi⟩ := O.every_marked d (List.mem_filter.mp hd).2
      exact List.mem_map.mpr ⟨i,List.mem_finRange _,hi⟩
  have hl := hp.length_eq
  simpa only [List.length_map,List.length_finRange,←List.countP_eq_length_filter] using hl.symm

theorem source_edge_no_fixed (i : Fin m) : I.edge i≠i := by
  intro hi
  have he := O.pair_port i
  rw [hi] at he
  exact P.pair_ne (O.port i) (O.marked_port i) he

/-- The retained parallel-port digons are in bijection with source edges. -/
theorem digon_count : P.digonCount=cycleCount I.edge := by
  have hp := P.digonCount_twice
  have hi := involution_cycles_twice I.edge O.edge_involution O.source_edge_no_fixed
  rw [O.marked_count] at hp
  omega

/-- Actual global rotation surgery preserves planarity. Every geometric input
is expressed before assembly: local endpoint separation, ordered outer-face
ports, planar source incidence, strict spherical old pieces, and a cover of
unused old components. The conclusion is registered hypermap planarity. -/
theorem assembled_planar (hdisj : P.DisjointNodeSwitches)
    (hE : ∀d,G.edge (G.edge d)=d)
    (hG : 2*G.componentCount+n≤G.eulerRhs)
    (hI : I.Planar) (spare : List (Fin n))
    (hcover : ∀d,(∃r∈spare,Connected G d r) ∨ ∃i,Connected G d (O.port i))
    (hspare : spare.length+cycleCount I.node≤G.componentCount) : P.assembled.Planar := by
  have hn := P.node_count_loss hdisj
  have hf := O.face_count_lower_bound
  have hfi := O.interior_face_loss
  have hc := O.component_count_bound hdisj hE spare hcover
  have hm := O.marked_count
  have hd := O.digon_count
  rw [planar_iff] at hI ⊢
  unfold Hypermap.eulerRhs at hG hI ⊢
  have he : cycleCount P.assembled.edge=cycleCount G.edge := rfl
  rw [he]
  omega

end OrderedIncidencePorts
end STACS2027.PlanarAssembly
