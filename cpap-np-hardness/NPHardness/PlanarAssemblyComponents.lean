module

public import NPHardness.PlanarAssemblyNodes
public import NPHardness.PlanarAssemblyRouting

/-!
Connectivity of simultaneous port assembly. Original gadget paths survive;
source incidence paths connect their selected port darts in the assembled
hypermap. A finite cover by untouched components and source component roots
gives the component bound used in the Euler calculation.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

/-- Connectivity through actual hypermap edge, node, and face steps. -/
def Connected {n : Nat} (G : Hypermap n) (a b : Fin n) : Prop :=
  ∃ k, G.linked k a b = true

namespace Connected
variable {n : Nat} {G : Hypermap n} {a b c : Fin n}
theorem refl (G : Hypermap n) (a : Fin n) : Connected G a a :=
  ⟨0,Linked.linked_refl G 0 a⟩
theorem trans (h : Connected G a b) (h' : Connected G b c) : Connected G a c := by
  obtain ⟨k,hk⟩ := h
  obtain ⟨l,hl⟩ := h'
  exact ⟨k+l,Linked.linked_trans G hk hl⟩
theorem symm (h : Connected G a b) : Connected G b a := by
  obtain ⟨k,hk⟩ := h
  exact hm_linked_symm G hk

theorem step (G : Hypermap n) {a b : Fin n} (h : Linked.Step G a b) : Connected G a b :=
  ⟨1,Linked.linked_step G (Linked.linked_refl G 0 a) h⟩

theorem of_node (h : Reaches G.node a b) : Connected G a b := by
  obtain ⟨k,rfl⟩ := h
  induction k generalizing a with
  | zero => exact refl G a
  | succ k ih => exact (step G (Or.inr (Or.inl rfl))).trans (ih (a:=G.node a))

theorem of_face (h : Reaches G.face a b) : Connected G a b := by
  obtain ⟨k,rfl⟩ := h
  induction k generalizing a with
  | zero => exact refl G a
  | succ k ih => exact (step G (Or.inr (Or.inr rfl))).trans (ih (a:=G.face a))
end Connected

/-- A path simulation may replace one step by any finite nonempty or empty path. -/
theorem connected_simulation {n m : Nat} (G : Hypermap n) (H : Hypermap m)
    (f : Fin n → Fin m)
    (hstep : ∀ a b, Linked.Step G a b → Connected H (f a) (f b))
    {a b : Fin n} (h : Connected G a b) : Connected H (f a) (f b) := by
  obtain ⟨k,hk⟩ := h
  induction k generalizing b with
  | zero =>
    have he := (Linked.linked_zero G a b).mp hk
    subst b
    exact Connected.refl H (f a)
  | succ k ih =>
    rcases (Linked.linked_succ G k a b).mp hk with h | ⟨z,hz,hs⟩
    · exact ih h
    · exact (ih hz).trans (hstep z b hs)

/-- Counting connected components needs only a finite list meeting every
component, without any requirement that its members are least-numbered darts. -/
theorem componentCount_le_cover {n : Nat} (G : Hypermap n) (xs : List (Fin n))
    (hcover : ∀ d, ∃ r ∈ xs, Connected G d r) : G.componentCount ≤ xs.length := by
  let pick : Fin n → Fin n := fun d => Classical.choose (hcover d)
  have hpick : ∀ d, pick d ∈ xs ∧ Connected G d (pick d) :=
    fun d => Classical.choose_spec (hcover d)
  let roots := (List.finRange n).filter (ComponentRoot G)
  have hnd : (roots.map pick).Nodup := by
    apply nodup_map_of_injOn' pick ((List.nodup_finRange n).filter _)
    intro a ha b hb he
    have hc := (hpick a).2.trans (by rw [he]; exact (hpick b).2.symm)
    obtain ⟨k,hk⟩ := hc
    exact componentRoot_eq G (List.mem_filter.mp ha).2 (List.mem_filter.mp hb).2 hk
  have hlen := List.Nodup.length_le_of_subset hnd (l₂:=xs) (by
    intro d hd
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hd
    exact (hpick r).1)
  change (List.finRange n).countP (ComponentRoot G) ≤ xs.length
  simpa only [List.length_map,roots,←List.countP_eq_length_filter] using hlen

namespace PortPairing
variable {n : Nat} {G : Hypermap n} (P : PortPairing G)

/-- Every original connected component remains connected after the endpoint
switches. Other components may become joined. -/
theorem connected_transfer (hdisj : P.DisjointNodeSwitches)
    (hE : ∀ d, G.edge (G.edge d)=d) {a b : Fin n}
    (h : Connected G a b) : Connected P.assembled a b := by
  apply connected_simulation G P.assembled id ?_ h
  intro x y hs
  rcases hs with rfl | rfl | rfl
  · exact Connected.step _ (Or.inl rfl)
  · exact Connected.of_node (P.node_step_transfer hdisj x)
  · have he : G.node (G.face x)=G.edge x := node_face_eq_edge hE x
    have hn : Connected P.assembled (G.face x) (G.edge x) := by
      rw [←he]
      exact Connected.of_node (P.node_step_transfer hdisj (G.face x))
    exact (Connected.step P.assembled (Or.inl rfl)).trans hn.symm

/-- Each paired port lies in a real two-dart assembled face, hence in the same
assembled component. -/
theorem connected_pair {d : Fin n} (hd : P.marked d=true) :
    Connected P.assembled d (P.pair d) :=
  Connected.step _ (Or.inr (Or.inr (P.assembled_face_marked hd)))
end PortPairing

namespace OrderedIncidencePorts
variable {n m : Nat} {G : Hypermap n} {P : PortPairing G} {I : Hypermap m}
  (O : OrderedIncidencePorts P I)

/-- The prescribed boundary order puts ports of one source node in one old
local face, and therefore in one original gadget component. -/
theorem local_node_connected (i : Fin m) :
    Connected G (O.port i) (O.port (I.node i)) := by
  have he : I.face (I.edge (I.node i))=i := by
    exact hm_node_inj I _ _ (I.edgeK (I.node i))
  obtain ⟨k,_,hk,_⟩ := O.order (I.node i)
  rw [he] at hk
  have hr : Reaches G.face (O.port (I.node i)) (O.port i) := ⟨k+1,hk⟩
  exact (Connected.of_face hr).symm

/-- Connectivity of the source incidence hypermap is realized by actual paths
between the selected global port darts. -/
theorem source_connected (hdisj : P.DisjointNodeSwitches)
    (hE : ∀ d, G.edge (G.edge d)=d) {i j : Fin m}
    (h : Connected I i j) : Connected P.assembled (O.port i) (O.port j) := by
  apply connected_simulation I P.assembled O.port ?_ h
  intro a b hs
  rcases hs with rfl | rfl | rfl
  · rw [←O.pair_port]
    exact P.connected_pair (O.marked_port a)
  · exact P.connected_transfer hdisj hE (O.local_node_connected a)
  · have he : I.node (I.face a)=I.edge a := PortPairing.node_face_eq_edge O.edge_involution a
    have hn := P.connected_transfer hdisj hE (O.local_node_connected (I.face a))
    rw [he] at hn
    have hp : Connected P.assembled (O.port a) (O.port (I.edge a)) := by
      rw [←O.pair_port]
      exact P.connected_pair (O.marked_port a)
    exact hp.trans hn.symm

/-- The untouched local components plus one representative of each source
component cover the assembled hypermap. All hypotheses concern the input
hypermap and the actual local port routing. -/
theorem component_count_bound (hdisj : P.DisjointNodeSwitches)
    (hE : ∀ d, G.edge (G.edge d)=d) (spare : List (Fin n))
    (hcover : ∀ d, (∃ r ∈ spare, Connected G d r) ∨
      ∃ i, Connected G d (O.port i)) :
    P.assembled.componentCount ≤ spare.length + I.componentCount := by
  let sourceRoots := (List.finRange m).filter (ComponentRoot I)
  have hb := componentCount_le_cover P.assembled (spare ++ sourceRoots.map O.port) (by
    intro d
    rcases hcover d with ⟨r,hr,hdr⟩ | ⟨i,hi⟩
    · exact ⟨r,List.mem_append.mpr (Or.inl hr),P.connected_transfer hdisj hE hdr⟩
    · refine ⟨O.port (componentRep I i),List.mem_append.mpr (Or.inr ?_),?_⟩
      · exact List.mem_map.mpr ⟨componentRep I i,
          List.mem_filter.mpr ⟨List.mem_finRange _,componentRep_root I i⟩,rfl⟩
      · exact (P.connected_transfer hdisj hE hi).trans
          (O.source_connected hdisj hE ⟨m,componentRep_linked I i⟩))
  have hl : sourceRoots.length=I.componentCount := by
    change ((List.finRange m).filter (ComponentRoot I)).length =
      (List.finRange m).countP (ComponentRoot I)
    exact List.countP_eq_length_filter.symm
  simpa only [List.length_append,List.length_map,hl] using hb
end OrderedIncidencePorts
end STACS2027.PlanarAssembly
