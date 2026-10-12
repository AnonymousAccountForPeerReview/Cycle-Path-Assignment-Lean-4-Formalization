module

public import NPHardness.PlanarPreprocessDeletionShrink
public import NPHardness.PlanarGluingCut
public import NPHardness.PlanarGluingOrientation
public import Complexity.Planar.Incidence

/-! Cutting a final paired edge, then explicitly removing its two now-fixed
darts.  This file identifies the surviving graph endpoints and rotations. -/

@[expose] public section
namespace STACS2027.PlanarPreprocess.Deletion
open Complexity Complexity.Planar STACS2027.PlanarGluing

def cutLast {n : Nat} (G : Hypermap (n+2))
    (ha : G.edge (penultimate n) = last (n+1)) (hb : G.edge (last (n+1)) = penultimate n) : Hypermap (n+2) :=
  cut G (penultimate n) (last (n+1)) (penultimate_ne_last n) ha hb

theorem cutLast_last_fixed {n : Nat} (G : Hypermap (n+2))
    (ha : G.edge (penultimate n) = last (n+1)) (hb : G.edge (last (n+1)) = penultimate n) :
    (cutLast G ha hb).edge (last (n+1)) = last (n+1) := by
  change transpose G.edge (penultimate n) (last (n+1)) (last (n+1)) = last (n+1)
  rw [transpose_b _ (penultimate_ne_last n),ha]

theorem cutLast_penultimate_fixed {n : Nat} (G : Hypermap (n+2))
    (ha : G.edge (penultimate n) = last (n+1)) (hb : G.edge (last (n+1)) = penultimate n) :
    (cutLast G ha hb).edge (penultimate n) = penultimate n := by
  change transpose G.edge (penultimate n) (last (n+1)) (penultimate n) = penultimate n
  rw [transpose_a,hb]

theorem cutLast_shrink_last_fixed {n : Nat} (G : Hypermap (n+2))
    (ha : G.edge (penultimate n) = last (n+1)) (hb : G.edge (last (n+1)) = penultimate n) :
    (shrinkLast (cutLast G ha hb) (cutLast_last_fixed G ha hb)).edge (last n) = last n := by
  apply embed_injective
  rw [shrinkLast_edge_lift]
  exact cutLast_penultimate_fixed G ha hb

def cutThenShrink {n : Nat} (G : Hypermap (n+2))
    (ha : G.edge (penultimate n) = last (n+1)) (hb : G.edge (last (n+1)) = penultimate n) : Hypermap n :=
  shrinkLast (shrinkLast (cutLast G ha hb) (cutLast_last_fixed G ha hb)) (cutLast_shrink_last_fixed G ha hb)

theorem cutThenShrink_edge_lift {n : Nat} (G : Hypermap (n+2))
    (ha : G.edge (penultimate n) = last (n+1)) (hb : G.edge (last (n+1)) = penultimate n)
    (x : Fin n) : embedPair ((cutThenShrink G ha hb).edge x) = G.edge (embedPair x) := by
  unfold cutThenShrink embedPair
  rw [shrinkLast_edge_lift,shrinkLast_edge_lift]
  exact transpose_other G.edge (embedPair_ne_penultimate x) (embedPair_ne_last x)

theorem cutThenShrink_node_orbit {n : Nat} (G : Hypermap (n+2))
    (ha : G.edge (penultimate n) = last (n+1)) (hb : G.edge (last (n+1)) = penultimate n)
    (x y : Fin n) :
    Reaches (cutThenShrink G ha hb).node x y ↔ Reaches G.node (embedPair x) (embedPair y) := by
  rw [cutThenShrink,shrinkLast_node_orbit,shrinkLast_node_orbit]
  rfl

theorem graphEdge_last_pair {E : Nat} (G : Hypermap (2*E+2))
    (he : ∀ d, (G.edge d).val = ed d.val) :
    G.edge (penultimate (2*E)) = last (2*E+1) ∧ G.edge (last (2*E+1)) = penultimate (2*E) := by
  constructor
  · apply Fin.ext
    rw [he]
    simp [penultimate,embed,last,ed]
  · apply Fin.ext
    rw [he]
    simp [penultimate,embed,last,ed]

/-- The explicitly deleted rotation has the exact standard dart pairing of
the prefix graph. -/
theorem cutThenShrink_graphEdge {E : Nat} (G : Hypermap (2*E+2))
    (he : ∀ d, (G.edge d).val = ed d.val) (d : Fin (2*E)) :
    ((cutThenShrink G (graphEdge_last_pair G he).1 (graphEdge_last_pair G he).2).edge d).val = ed d.val := by
  have h := congrArg Fin.val (cutThenShrink_edge_lift G (graphEdge_last_pair G he).1 (graphEdge_last_pair G he).2 d)
  rw [he] at h
  exact h

/-- No vertex identification is introduced when removing the final edge:
surviving node cycles are precisely the prefix graph's endpoint classes. -/
theorem cutThenShrink_graphNodes {V : Type} (es : List (V×V)) (e : V×V)
    (G : Hypermap (2*es.length+2)) (he : ∀ d, (G.edge d).val = ed d.val)
    (hn : ∀ d d', Reaches G.node d d' ↔ halfEdgeEnd (es++[e]) d.val = halfEdgeEnd (es++[e]) d'.val)
    (d d' : Fin (2*es.length)) :
    Reaches (cutThenShrink G (graphEdge_last_pair G he).1 (graphEdge_last_pair G he).2).node d d' ↔
      halfEdgeEnd es d.val = halfEdgeEnd es d'.val := by
  rw [cutThenShrink_node_orbit,hn]
  change halfEdgeEnd (es++[e]) d.val = halfEdgeEnd (es++[e]) d'.val ↔ _
  rw [halfEdgeEnd_append_left es [e] d.val d.isLt,halfEdgeEnd_append_left es [e] d'.val d'.isLt]

end STACS2027.PlanarPreprocess.Deletion
