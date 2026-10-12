module

public import Outerplanar.Defs
public import Complexity.Planarity

/-!
# Outerplanar graphs, by drawings (the definition of Lemma 19)

Lemma 19 of the manuscript *defines* a graph to be outerplanar if it has a planar drawing with
every vertex on the outer face, and states that this is equivalent to having neither `K₄` nor
`K_{2,3}` as a minor. The minor condition is `Outerplanar` (`Outerplanar/Defs.lean`). This file
gives the drawing definition, in the combinatorial form of planarity used throughout the
formalization (the NP-completeness foundation's `Complexity.PlanarGraph`: rotation systems,
i.e. planar hypermaps on the half-edges, following ANONYMIZED's proof of the Four Colour
Theorem):

* `simpleEdges g`: the simple graph of `g` as an edge list — the entries written smaller end
  first (the entries `Adj g` reads), each once (first occurrences). Its adjacency is `Adj g`.
* `OuterplanarEmbedding es`: a planar embedding of the edge list `es` (exactly the data of
  `Complexity.PlanarGraph es`) in which every connected component has a face — a cycle of the
  `face` permutation — passing through every vertex of that component (a dart of the face
  and a dart of the vertex's `node` cycle coincide). For a connected graph this is a planar
  drawing with every vertex on one face, which can be taken as the outer face; components
  are drawn next to each other, each with its own outer face on the unbounded one.
* `OuterplanarDrawing g := OuterplanarEmbedding (simpleEdges g)`.
-/

@[expose] public section

namespace STACS2027

/-- The simple graph of `g` as an edge list: the entries written smaller end first (exactly the
entries that `Adj g` reads), each kept once (at its first occurrence). Its adjacency is
`Adj g` (`mem_simpleEdges`). -/
def simpleEdges (g : Graph) : List Edge :=
  (g.filter fun e => decide (e.1 < e.2)).eraseDups

/-- An **outerplanar embedding** of the edge list `es`: a planar embedding of `es` in the sense
of `Complexity.PlanarGraph` (a planar hypermap on the half-edges `0, …, 2|es| − 1`, half-edges
`2i`, `2i + 1` the two ends of edge `i`, whose `edge` permutation pairs the two ends of every
edge and whose `node` cycles are the sets of half-edges at a common vertex) such that every
connected component has a face passing through all its vertices: for every dart `d` there is
a dart `x` whose face meets the vertex (`node` cycle) of every dart `d'` linked to `d`. -/
def OuterplanarEmbedding {V : Type} (es : List (V × V)) : Prop :=
  ∃ G : Complexity.Hypermap (2 * es.length),
    (∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)) ∧
    (∀ d d', (∃ k, Complexity.iterate G.node k d = d') ↔
      Complexity.halfEdgeEnd es d.val = Complexity.halfEdgeEnd es d'.val) ∧
    G.Planar ∧
    ∀ d, ∃ x, ∀ d', G.linked (2 * es.length) d d' = true →
      ∃ j k, Complexity.iterate G.face j x = Complexity.iterate G.node k d'

/-- **Outerplanar** (the definition of Lemma 19): the simple graph of `g` has a planar drawing
with every vertex on the outer face, in the combinatorial form `OuterplanarEmbedding`. -/
def OuterplanarDrawing (g : Graph) : Prop := OuterplanarEmbedding (simpleEdges g)

/-- **Euler's inequality and the parity of the Euler characteristic for hypermaps** (ANONYMIZED):
for every hypermap, `eulerRhs ≤ eulerLhs`, and the difference is even, so that the genus is a
natural number and a hypermap is `Planar` exactly when `eulerLhs = eulerRhs`. A proposition,
to be proved once (`Outerplanar/HypermapEuler.lean`). -/
def HypermapEuler : Prop :=
  ∀ (n : Nat) (G : Complexity.Hypermap n),
    G.eulerRhs ≤ G.eulerLhs ∧ (G.eulerLhs - G.eulerRhs) % 2 = 0

/-- An outerplanar embedding is in particular a planar embedding. -/
theorem OuterplanarEmbedding.planarGraph {V : Type} {es : List (V × V)}
    (h : OuterplanarEmbedding es) : Complexity.PlanarGraph es := by
  obtain ⟨G, he, hn, hp, -⟩ := h
  exact ⟨G, he, hn, hp⟩

end STACS2027
