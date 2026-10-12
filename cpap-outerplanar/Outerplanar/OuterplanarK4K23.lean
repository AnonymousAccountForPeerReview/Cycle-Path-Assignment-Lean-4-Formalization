module

public import Outerplanar.HypermapEulerFaces
import Lean.Elab.Tactic.Omega

/-!
# `K₄` and `K_{2,3}` have no outerplanar drawing

`not_outerplanarDrawing_k4 : ¬ OuterplanarDrawing k4` and
`not_outerplanarDrawing_k23 : ¬ OuterplanarDrawing k23`, the easy direction of Lemma 19 for
the two excluded minors, by counting faces with Euler's formula.

The general criterion `not_outerplanarEmbedding_of_girth`: let the edge list `es` have its
vertices among the distinct `vs`, be connected (from some dart every vertex is reached), and
let every face cycle of every embedding have at least `g` darts. In a planar embedding,
Euler's formula (`hypermapEuler`) with one component, `|es|` edges and at most `|vs|` nodes
gives at least `2 + |es| − |vs|` faces; an outerplanar embedding has a face meeting all
`|vs|` vertices, hence with at least `|vs|` darts. As the face cycles partition the
`2 |es|` darts (`orbit_count`), `g · (1 + |es| − |vs|) + |vs| ≤ 2 |es|`.

* `K₄` (6 edges, 4 vertices, simple, every vertex of degree 3): faces have at least `3`
  darts, and `3 · 3 + 4 = 13 > 12`.
* `K_{2,3}` (6 edges, 5 vertices, simple, bipartite, every vertex of degree at least 2):
  faces have at least `4` darts, and `4 · 2 + 5 = 13 > 12`.
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar STACS2027.PlanarGluing STACS2027.HypEuler

namespace HypEuler

theorem exists_list_of_forall_mem {α β : Type} (f : α → β) (P : α → Prop) :
    ∀ vs : List β, (∀ v ∈ vs, ∃ a, P a ∧ f a = v) →
      ∃ ys : List α, ys.map f = vs ∧ ∀ y ∈ ys, P y
  | [], _ => ⟨[], rfl, by simp⟩
  | v :: vs, h => by
    obtain ⟨a, ha, rfl⟩ := h v List.mem_cons_self
    obtain ⟨ys, hys, hP⟩ := exists_list_of_forall_mem f P vs
      (fun w hw => h w (List.mem_cons_of_mem _ hw))
    refine ⟨a :: ys, by rw [List.map_cons, hys], ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ha
    · exact hP y hy

end HypEuler

/-- **No outerplanar embedding, by counting faces** (see the module docstring). -/
theorem not_outerplanarEmbedding_of_girth {V : Type} (es : List (V × V)) (vs : List V)
    (g : Nat) (hvs : ∀ d, dartEnd es d ∈ vs) (hnd : vs.Nodup)
    (hgirth : ∀ G : Hypermap (2 * es.length), IsGraphEmbedding es G →
      ∀ y i, 0 < i → i < g → iterate G.face i y ≠ y)
    (hconn : ∀ G : Hypermap (2 * es.length), IsGraphEmbedding es G →
      ∃ d0, ∀ v ∈ vs, ∃ d, LinkedPath G d0 d ∧ dartEnd es d = v)
    (hbig : 2 * es.length < g * (1 + es.length - vs.length) + vs.length) :
    ¬ OuterplanarEmbedding es := by
  rintro ⟨G, he, hn, hp, hout⟩
  have hG : IsGraphEmbedding es G := ⟨he, hn⟩
  obtain ⟨d0, hd0⟩ := hconn G hG
  obtain ⟨x, hx⟩ := hout d0
  -- the face of `x` meets every vertex
  have hy : ∀ v ∈ vs, ∃ y, cmin G.face y = cmin G.face x ∧ dartEnd es y = v := by
    intro v hv
    obtain ⟨d, ⟨k, hk⟩, hdv⟩ := hd0 v hv
    obtain ⟨j, k', hjk⟩ := hx d (Linked.linked_stable G hk)
    refine ⟨iterate G.face j x, cmin_iterate (hm_face_inj G) x j, ?_⟩
    rw [hjk, dartEnd_iterate_node hG, hdv]
  obtain ⟨ys, hmap, hys⟩ := exists_list_of_forall_mem (dartEnd es) _ vs hy
  have hysnd : ys.Nodup := nodup_of_map _ (hmap ▸ hnd)
  have hlen : ys.length = vs.length := by rw [← hmap, List.length_map]
  have hcount := orbit_count (hm_face_inj G) g (hgirth G hG) x ys hysnd hys
  have hE := edge_cycleCount hG
  have hN := node_cycleCount_le hG vs hvs
  have hC := componentCount_pos G d0
  have hP := (Hypermap.planar_iff_euler_eq G).mp hp
  unfold Hypermap.eulerLhs Hypermap.eulerRhs at hP
  have hF : 1 + es.length - vs.length ≤ cycleCount G.face - 1 := by omega
  have := Nat.mul_le_mul_left g hF
  omega

/-- The simple graph of `K₄` is `K₄`. -/
theorem simpleEdges_k4 : simpleEdges k4 = k4 := by decide

/-- The simple graph of `K_{2,3}` is `K_{2,3}`. -/
theorem simpleEdges_k23 : simpleEdges k23 = k23 := by decide

/-- **`K₄` has no outerplanar drawing.** -/
theorem not_outerplanarDrawing_k4 : ¬ OuterplanarDrawing k4 := by
  unfold OuterplanarDrawing
  rw [simpleEdges_k4]
  apply not_outerplanarEmbedding_of_girth k4 [0, 1, 2, 3] 3 (by decide) (by decide)
  · intro G hG
    exact face_girth_three hG (by unfold SimpleEdgeList; decide) (by decide)
  · intro G hG
    refine ⟨⟨0, by decide⟩, ?_⟩
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨_, LinkedPath.refl G _, by decide⟩
    · exact ⟨G.edge ⟨0, by decide⟩, linkedPath_edge _, by rw [dartEnd_edge hG]; decide⟩
    · exact ⟨G.edge ⟨2, by decide⟩, (linkedPath_of_dartEnd hG (by decide)).trans
        (linkedPath_edge _), by rw [dartEnd_edge hG]; decide⟩
    · exact ⟨G.edge ⟨4, by decide⟩, (linkedPath_of_dartEnd hG (by decide)).trans
        (linkedPath_edge _), by rw [dartEnd_edge hG]; decide⟩
  · decide

/-- **`K_{2,3}` has no outerplanar drawing.** -/
theorem not_outerplanarDrawing_k23 : ¬ OuterplanarDrawing k23 := by
  unfold OuterplanarDrawing
  rw [simpleEdges_k23]
  apply not_outerplanarEmbedding_of_girth k23 [0, 1, 2, 3, 4] 4 (by decide) (by decide)
  · intro G hG
    exact face_girth_four hG (by unfold SimpleEdgeList; decide) (by decide)
      (fun v => decide (v < 2)) (by decide)
  · intro G hG
    refine ⟨⟨0, by decide⟩, ?_⟩
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, LinkedPath.refl G _, by decide⟩
    · -- vertex 1: from vertex 2 (dart `edge 0`) to the dart 7 at vertex 2, then along its edge
      exact ⟨G.edge ⟨7, by decide⟩, ((linkedPath_edge _).trans (linkedPath_of_dartEnd hG
        (by rw [dartEnd_edge hG]; decide))).trans (linkedPath_edge _),
        by rw [dartEnd_edge hG]; decide⟩
    · exact ⟨G.edge ⟨0, by decide⟩, linkedPath_edge _, by rw [dartEnd_edge hG]; decide⟩
    · exact ⟨G.edge ⟨2, by decide⟩, (linkedPath_of_dartEnd hG (by decide)).trans
        (linkedPath_edge _), by rw [dartEnd_edge hG]; decide⟩
    · exact ⟨G.edge ⟨4, by decide⟩, (linkedPath_of_dartEnd hG (by decide)).trans
        (linkedPath_edge _), by rw [dartEnd_edge hG]; decide⟩
  · decide

end STACS2027
