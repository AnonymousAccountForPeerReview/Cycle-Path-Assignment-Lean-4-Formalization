module

public import Outerplanar.OuterplanarBasic

/-!
# Spherical outerplanar embeddings (the invariant of the construction)

The construction of outerplanar embeddings (minor-free graphs ⇒ `OuterplanarDrawing`) glues
explicit embeddings. `Hypermap.Planar` only says `eulerLhs ≤ eulerRhs + 1`, which is not
preserved by disjoint unions without Euler's parity theorem; the construction therefore
keeps the exact spherical inequality `2 · components + darts ≤ edges + nodes + faces` as an
invariant (`SphOuter`), which implies `OuterplanarEmbedding` (`SphOuter.outerplanarEmbedding`)
and is carried by edge permutations (`SphOuter.perm`) and vertex renamings
(`SphOuter.map_injOn`). The empty edge list has one (`sphOuter_nil`).
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar PlanarGluing

/-- A spherical outerplanar embedding of `es`: an embedding of `es` (as in
`OuterplanarEmbedding`) with the exact spherical Euler inequality and the outer-face
condition. -/
def SphOuter {V : Type} (es : List (V × V)) : Prop :=
  ∃ G : Hypermap (2 * es.length),
    (∀ d, (G.edge d).val = ed d.val) ∧
    (∀ d d', (∃ k, iterate G.node k d = d') ↔ halfEdgeEnd es d.val = halfEdgeEnd es d'.val) ∧
    2 * G.componentCount + 2 * es.length ≤ G.eulerRhs ∧
    OuterFaceCond G

/-- A spherical outerplanar embedding is an outerplanar embedding. -/
theorem SphOuter.outerplanarEmbedding {V : Type} {es : List (V × V)} (h : SphOuter es) :
    OuterplanarEmbedding es := by
  obtain ⟨G, hE, hN, hS, hO⟩ := h
  refine ⟨G, hE, hN, ?_, hO⟩
  rw [planar_iff]
  omega

/-- Renumbering the edges preserves spherical outerplanar embeddings. -/
theorem SphOuter.of_graphDartEquiv {V : Type} {es ts : List (V × V)}
    (e : GraphDartEquiv es ts) (h : SphOuter es) : SphOuter ts := by
  obtain ⟨G, hE, hN, hS, hO⟩ := h
  obtain ⟨hE', hN'⟩ := graphDartEquiv_embedding e hE hN
  refine ⟨e.darts.hypermap G, hE', hN', ?_,
    OuterFaceCond.dartEquiv e.darts hO⟩
  exact e.darts.spherical G hS

/-- A permutation of the edge list. -/
theorem SphOuter.perm {V : Type} {es es' : List (V × V)} (hp : es.Perm es')
    (h : SphOuter es) : SphOuter es' := by
  obtain ⟨e⟩ := IndexEquiv.of_perm hp
  exact h.of_graphDartEquiv e.graphDarts

/-- Renaming the vertices by a map injective on the ends of the edges. -/
theorem SphOuter.map_injOn {V W : Type} {es : List (V × V)} (f : V → W)
    (hf : ∀ a b, (∃ e ∈ es, a = e.1 ∨ a = e.2) → (∃ e ∈ es, b = e.1 ∨ b = e.2) →
      f a = f b → a = b)
    (h : SphOuter es) : SphOuter (es.map fun e => (f e.1, f e.2)) := by
  have hi : ∀ d d' : Fin (2 * es.length),
      (halfEdgeEnd es d.val).map f = (halfEdgeEnd es d'.val).map f ↔
        halfEdgeEnd es d.val = halfEdgeEnd es d'.val := by
    intro d d'
    obtain ⟨v, hv, hve⟩ := halfEdgeEnd_isEnd es d.isLt
    obtain ⟨v', hv', hve'⟩ := halfEdgeEnd_isEnd es d'.isLt
    rw [hv, hv']
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨hf v v' hve hve', congrArg f⟩
  unfold SphOuter
  simp only [STACS2027.halfEdgeEnd_relabel]
  rw [List.length_map]
  obtain ⟨G, hE, hN, hS, hO⟩ := h
  exact ⟨G, hE, fun d d' => (hN d d').trans (hi d d').symm, hS, hO⟩

/-- The hypermap without darts. -/
def emptyHypermap : Hypermap 0 where
  edge x := x
  node x := x
  face x := x
  edgeK _ := rfl

/-- The empty edge list. -/
theorem sphOuter_nil {V : Type} : SphOuter ([] : List (V × V)) :=
  ⟨emptyHypermap, fun d => d.elim0, fun d => d.elim0,
    by change 2 * emptyHypermap.componentCount + 2 * 0 ≤ emptyHypermap.eulerRhs; decide,
    fun d => d.elim0⟩

end STACS2027
