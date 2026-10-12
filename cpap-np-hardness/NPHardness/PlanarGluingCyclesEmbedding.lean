module

public import NPHardness.PlanarGluingUnion
public import NPHardness.PlanarGluingOrientation
import Lean.Elab.Tactic.Omega

/-! A spherical embedding assembled from explicit hypermap data
(`SphericalEmbedding.of_data`). -/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

def SphericalEmbedding.of_data {V : Type} {es : List (V × V)} {n : Nat}
    (hlen : es.length = n) (G : Hypermap (2 * n))
    (hedge : ∀ d, G.edge d = graphEdge d)
    (hnode : ∀ d d', (∃ k, iterate G.node k d = d') ↔ halfEdgeEnd es d.val = halfEdgeEnd es d'.val)
    (heuler : 2 * G.componentCount + 2 * n ≤ G.eulerRhs) : SphericalEmbedding es := by
  subst n
  exact ⟨G, hedge, hnode, heuler⟩

end STACS2027.PlanarGluing
