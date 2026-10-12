module

public import Outerplanar.HypermapEulerFaces
public import Outerplanar.Defs
public import Outerplanar.OuterplanarMinor
import Mathlib.Tactic

@[expose] public section
namespace STACS2027.PlanarTriangleGeometry
open Complexity Complexity.Planar STACS2027.HypEuler

/-- The complete graph on five vertices, written as a cone over the four-vertex clique. -/
def completeFive : Graph := k4 ++ [(0,4),(1,4),(2,4),(3,4)]

/-- The complete bipartite graph with three vertices on each side. -/
def bipartiteThree : Graph := k23 ++ [(2,5),(3,5),(4,5)]

theorem simpleEdges_completeFive : simpleEdges completeFive = completeFive := by decide
theorem simpleEdges_bipartiteThree : simpleEdges bipartiteThree = bipartiteThree := by decide

/-- Euler's formula excludes the complete five-vertex graph from planar embeddings. -/
theorem completeFive_not_planar : ¬ PlanarGraph completeFive := by
  rintro ⟨G,he,hn,hp⟩
  have hG : IsGraphEmbedding completeFive G := ⟨he,hn⟩
  have hface := three_mul_faces_le hG (by unfold SimpleEdgeList; decide) (by decide)
  have hnode := node_cycleCount_le hG [0,1,2,3,4] (by decide)
  have hcomp := componentCount_pos G ⟨0,by decide⟩
  have heuler := euler_graph hG hp
  simp only [List.length_cons,List.length_nil] at hnode
  change 3 * cycleCount G.face ≤ 20 at hface
  change 2 * G.componentCount + 10 = cycleCount G.node + cycleCount G.face at heuler
  omega

/-- Euler's formula and bipartite face parity exclude the three-by-three biclique. -/
theorem bipartiteThree_not_planar : ¬ PlanarGraph bipartiteThree := by
  rintro ⟨G,he,hn,hp⟩
  have hG : IsGraphEmbedding bipartiteThree G := ⟨he,hn⟩
  have hface := four_mul_faces_le hG (by unfold SimpleEdgeList; decide) (by decide)
    (fun v : Nat => decide (v=0 ∨ v=1 ∨ v=5)) (by decide)
  have hnode := node_cycleCount_le hG [0,1,2,3,4,5] (by decide)
  have hcomp := componentCount_pos G ⟨0,by decide⟩
  have heuler := euler_graph hG hp
  simp only [List.length_cons,List.length_nil] at hnode
  change 4 * cycleCount G.face ≤ 18 at hface
  change 2 * G.componentCount + 9 = cycleCount G.node + cycleCount G.face at heuler
  omega

end STACS2027.PlanarTriangleGeometry
