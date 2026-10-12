module

public import NPHardness.PlanarAssemblyInactivePieces
public import NPHardness.PlanarGluingReflection

/-!
Reindex a source incidence node cycle onto a finite local port set. The desired
local outer-face successor is exactly the inverse source-node step, namely
face after edge. Its injectivity and cyclic reachability follow from the
registered source endpoint/node-orbit equivalence.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

/-- A complete finite enumeration of the darts with one source vertex label. -/
structure NodeDartIndex {n : Nat} {V : Type} (label : Fin n→V) (v : V) (m : Nat) where
  dart : Fin m→Fin n
  injective : ∀i j,dart i=dart j→i=j
  vertex : ∀i,label (dart i)=v
  complete : ∀d,label d=v→∃i,dart i=d

namespace NodeDartIndex

def transport {n m r : Nat} {V : Type} {label : Fin n→V} {v w : V}
    (D : NodeDartIndex label v m) (hm : m=r) (hv : v=w) : NodeDartIndex label w r where
  dart i := D.dart ⟨i.val,by rw [hm]; exact i.isLt⟩
  injective i j h := by
    have he := D.injective _ _ h
    exact Fin.ext (congrArg (fun x:Fin m=>x.val) he)
  vertex i := (D.vertex _).trans hv
  complete d hd := by
    obtain ⟨i,hi⟩ := D.complete d (hd.trans hv.symm)
    exact ⟨⟨i.val,by rw [←hm]; exact i.isLt⟩,hi⟩

variable {n m : Nat} {V : Type} {label : Fin n→V} {v : V}
  (D : NodeDartIndex label v m) (I : Hypermap n)
  (hnode : ∀a b,Reaches I.node a b ↔ label a=label b)

include D hnode in
theorem predecessor_vertex (i : Fin m) : label (I.face (I.edge (D.dart i)))=v := by
  have he : I.node (I.face (I.edge (D.dart i)))=D.dart i := I.edgeK _
  have hh := (hnode (I.face (I.edge (D.dart i))) (D.dart i)).mp ⟨1,he⟩
  exact hh.trans (D.vertex i)

noncomputable def order (i : Fin m) : Fin m :=
  Classical.choose (D.complete _ (D.predecessor_vertex I hnode i))

theorem order_spec (i : Fin m) : D.dart (D.order I hnode i)=I.face (I.edge (D.dart i)) :=
  Classical.choose_spec (D.complete _ (D.predecessor_vertex I hnode i))

theorem order_injective (i j : Fin m) (h : D.order I hnode i=D.order I hnode j) : i=j := by
  apply D.injective
  have hh := congrArg D.dart h
  rw [D.order_spec,D.order_spec] at hh
  exact hm_edge_inj I _ _ (hm_face_inj I _ _ hh)

theorem order_iterate (k : Nat) (i : Fin m) :
    D.dart (iterate (D.order I hnode) k i)=iterate (fun d=>I.face (I.edge d)) k (D.dart i) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [iterate,ih,D.order_spec]
    rfl

/-- The desired local order is one complete cycle, including the singleton
case; empty node enumerations satisfy the statement vacuously. -/
theorem order_cyclic (i j : Fin m) : Reaches (D.order I hnode) i j := by
  have hh : Reaches I.node (D.dart i) (D.dart j) :=
    (hnode _ _).mpr ((D.vertex i).trans (D.vertex j).symm)
  have hp : ∀a b,I.face (I.edge a)=I.face (I.edge b)→a=b :=
    fun a b h=>hm_edge_inj I a b (hm_face_inj I _ _ h)
  have hr := (Reflection.inverse_reaches I.node (fun d=>I.face (I.edge d))
    (hm_node_inj I) hp (nodePredecessor_node I) I.edgeK _ _).mp hh
  obtain ⟨k,hk⟩ := hr
  refine ⟨k,D.injective _ _ ?_⟩
  rw [D.order_iterate,hk]

end NodeDartIndex
end STACS2027.PlanarAssembly
