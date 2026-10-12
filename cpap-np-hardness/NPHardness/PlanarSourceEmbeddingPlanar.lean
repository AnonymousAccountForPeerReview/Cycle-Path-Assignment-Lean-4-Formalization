module

public import NPHardness.PlanarSourceEmbeddingCounts
public import NPHardness.PlanarSourceComponents

/-!
Planarity of the explicit incidence-ring expansion. This theorem concerns
the actual expanded hypermap, with all edge, node, face, and component
count bounds proved from its permutations. It has no unproved graph-surgery
hypothesis. Connecting it to a particular CNF's indexed incidence edges is
a separate representation theorem.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Embedding.BipartiteRotation
open Complexity Complexity.Planar

/-- Replacing every variable rotation by a ring of occurrence copies and
two-literal implication clauses preserves the registered hypermap planarity. -/
theorem expanded_planar {E : Nat} (B : BipartiteRotation E) (h : B.original.Planar) :
    B.expanded.Planar := by
  rw [planar_iff] at h ⊢
  unfold Hypermap.eulerRhs at h ⊢
  have heOld := B.original_edge_count_le
  have hnOld := B.original_node_count_le
  have heNew := B.expanded_edge_count_ge
  have hnNew := B.expanded_node_count_ge
  have hfNew := B.expanded_face_count_ge
  have hc := B.expanded_componentCount_le
  omega

end STACS2027.PlanarSource.Embedding.BipartiteRotation
