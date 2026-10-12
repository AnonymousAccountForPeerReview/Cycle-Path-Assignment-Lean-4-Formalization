module

public import NPHardness.PlanarPreprocessDeletionMap

/-! Excision after cutting an edge: removing a dart fixed by the edge
permutation preserves all surviving permutation orbits.  The explicit map
and cycle-count identities below are used with the component-count lemma. -/

@[expose] public section
namespace STACS2027.PlanarPreprocess.Deletion
open Complexity Complexity.Planar STACS2027.PlanarGluing

def shrinkLast {n : Nat} (G : Hypermap (n+1)) (he : G.edge (last n) = last n) : Hypermap n where
  edge := removeLast G.edge (hm_edge_inj G)
  node := removeLast G.node (hm_node_inj G)
  face := removeLast G.face (hm_face_inj G)
  edgeK := by
    intro x
    have hf : removeLast (nodeInverse G) (nodeInverse_injective G) x =
        removeLast G.face (hm_face_inj G) (removeLast G.edge (hm_edge_inj G) x) :=
      removeLast_comp_fixed (hm_face_inj G) (hm_edge_inj G) he x
    rw [← hf]
    exact removeLast_inverse (nodeInverse_injective G) (hm_node_inj G) (node_nodeInverse G) x

theorem shrinkLast_node_orbit {n : Nat} (G : Hypermap (n+1)) (he : G.edge (last n) = last n)
    (x y : Fin n) :
    Reaches (shrinkLast G he).node x y ↔ Reaches G.node (embed x) (embed y) :=
  removeLast_orbit (hm_node_inj G) x y

theorem shrinkLast_face_orbit {n : Nat} (G : Hypermap (n+1)) (he : G.edge (last n) = last n)
    (x y : Fin n) :
    Reaches (shrinkLast G he).face x y ↔ Reaches G.face (embed x) (embed y) :=
  removeLast_orbit (hm_face_inj G) x y

theorem shrinkLast_edge_orbit {n : Nat} (G : Hypermap (n+1)) (he : G.edge (last n) = last n)
    (x y : Fin n) :
    Reaches (shrinkLast G he).edge x y ↔ Reaches G.edge (embed x) (embed y) :=
  removeLast_orbit (hm_edge_inj G) x y

theorem shrinkLast_edge_lift {n : Nat} (G : Hypermap (n+1)) (he : G.edge (last n) = last n)
    (x : Fin n) : embed ((shrinkLast G he).edge x) = G.edge (embed x) := by
  have hne : G.edge (embed x) ≠ last n := fun h =>
    embed_ne_last x (hm_edge_inj G _ _ (h.trans he.symm))
  change embed (removeLast G.edge (hm_edge_inj G) x) = G.edge (embed x)
  simp only [embed_removeLast,skipLast,hne,↓reduceIte]

theorem edge_fixed_face_node_fixed {n : Nat} (G : Hypermap (n+1))
    (he : G.edge (last n) = last n) : G.face (last n) = last n ↔ G.node (last n) = last n := by
  have hk := G.edgeK (last n)
  rw [he] at hk
  constructor
  · intro hf
    simpa only [hf] using hk
  · intro hn
    exact hm_node_inj G _ _ (hk.trans hn.symm)

def singletonLoss {n : Nat} (G : Hypermap (n+1)) : Nat := if G.node (last n) = last n then 1 else 0

theorem shrinkLast_edge_cycles {n : Nat} (G : Hypermap (n+1)) (he : G.edge (last n) = last n) :
    cycleCount G.edge = cycleCount (shrinkLast G he).edge + 1 := by
  have h := removeLast_cycleCount (hm_edge_inj G)
  simpa only [he,↓reduceIte,shrinkLast] using h

theorem shrinkLast_node_cycles {n : Nat} (G : Hypermap (n+1)) (he : G.edge (last n) = last n) :
    cycleCount G.node = cycleCount (shrinkLast G he).node + singletonLoss G :=
  removeLast_cycleCount (hm_node_inj G)

theorem shrinkLast_face_cycles {n : Nat} (G : Hypermap (n+1)) (he : G.edge (last n) = last n) :
    cycleCount G.face = cycleCount (shrinkLast G he).face + singletonLoss G := by
  have h := removeLast_cycleCount (hm_face_inj G)
  have hiff := edge_fixed_face_node_fixed G he
  simpa only [hiff,singletonLoss,shrinkLast] using h

theorem shrinkLast_eulerRhs {n : Nat} (G : Hypermap (n+1)) (he : G.edge (last n) = last n) :
    G.eulerRhs = (shrinkLast G he).eulerRhs + 1 + 2*singletonLoss G := by
  have hec := shrinkLast_edge_cycles G he
  have hnc := shrinkLast_node_cycles G he
  have hfc := shrinkLast_face_cycles G he
  unfold Hypermap.eulerRhs
  omega

end STACS2027.PlanarPreprocess.Deletion
