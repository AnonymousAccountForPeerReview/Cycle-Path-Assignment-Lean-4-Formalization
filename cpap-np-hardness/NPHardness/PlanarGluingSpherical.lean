module

public import NPHardness.PlanarGluingCyclesEmbedding
public import NPHardness.PlanarRelabel
import Lean.Elab.Tactic.Omega

/-! Transport of exact spherical embeddings. These lemmas retain the
strict Euler inequality needed when adding disjoint components. -/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

theorem DartEquiv.spherical {n m : Nat} (e : DartEquiv n m) (G : Hypermap n)
    (h : 2 * G.componentCount + n ≤ G.eulerRhs) :
    2 * (e.hypermap G).componentCount + m ≤ (e.hypermap G).eulerRhs := by
  have hc := e.components_le G
  have he := e.cycles_eq (hm_edge_inj G)
  have hn := e.cycles_eq (hm_node_inj G)
  have hf := e.cycles_eq (hm_face_inj G)
  have hm := e.card_eq
  unfold Hypermap.eulerRhs at h ⊢
  change 2 * (e.hypermap G).componentCount + m ≤
    cycleCount (e.conjugate G.edge) + cycleCount (e.conjugate G.node) +
      cycleCount (e.conjugate G.face)
  omega

def DartEquiv.cast {n m : Nat} (h : n = m) : DartEquiv n m where
  toFun x := ⟨x.val, by have := x.isLt; omega⟩
  invFun y := ⟨y.val, by have := y.isLt; omega⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

/-- Vertex names need only be injective on the ends of actual darts. -/
def SphericalEmbedding.relabel_ends {V W : Type} {es : List (V × V)}
    (h : SphericalEmbedding es) (f : V → W)
    (hf : ∀ d d' : Fin (2 * es.length),
      (halfEdgeEnd es d.val).map f = (halfEdgeEnd es d'.val).map f →
        halfEdgeEnd es d.val = halfEdgeEnd es d'.val) :
    SphericalEmbedding (es.map fun e => (f e.1, f e.2)) :=
  SphericalEmbedding.of_data (List.length_map _) h.map h.edge (fun d d' => by
    rw [STACS2027.halfEdgeEnd_relabel, STACS2027.halfEdgeEnd_relabel, h.nodes]
    exact ⟨congrArg (Option.map f), hf d d'⟩) h.euler

end STACS2027.PlanarGluing
