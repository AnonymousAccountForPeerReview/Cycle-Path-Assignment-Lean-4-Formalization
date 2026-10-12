module

public import Outerplanar.OuterplanarConstructInduction

/-!
# Lemma 19: graphs without `K₄` and `K_{2,3}` minors are outerplanar

The construction direction of Lemma 19 and its 2-connected sentence, for every edge list
`es` listing the simple graph of `g` (`RepEdges g es`, `Outerplanar/OuterplanarBasic.lean`):

* `outerplanarEmbedding_of_minorFree`: if `g` has neither a `K₄` nor a `K_{2,3}` minor, then
  `es` has an outerplanar embedding (a planar drawing with every vertex on the outer face);
* `OuterplanarHam.outerplanarEmbedding`: so does the edge list of a graph with an outerplanar
  Hamiltonian cycle (the polygon embedding);
* `twoConnected_outerplanar_or_k4_of_rep`: every 2-connected `K_{2,3}`-minor-free graph is outerplanar
  or a `K₄` (from `twoConnectedK23_structure`).

The proofs build spherical outerplanar embeddings (`SphOuter`): explicit polygon embeddings
of the 2-connected pieces (`Outerplanar/OuterplanarConstructPoly.lean`), glued at cut vertices
and put side by side (`Outerplanar/OuterplanarConstructGlueSph.lean`), by induction on the
number of vertices (`Outerplanar/OuterplanarConstructInduction.lean`).
-/

@[expose] public section

namespace STACS2027

/-- **Lemma 19, construction direction.** A graph with neither a `K₄` nor a `K_{2,3}` minor
has an outerplanar embedding of (any edge list of) its simple graph. -/
theorem outerplanarEmbedding_of_minorFree {g : Graph} {es : List Edge} (hes : RepEdges g es)
    (h4 : ¬ HasMinor g 4 k4) (h23 : ¬ HasMinor g 5 k23) : OuterplanarEmbedding es :=
  (sphOuter_of_minorFree _ g es le_rfl hes h4 h23).outerplanarEmbedding

/-- **The polygon embedding.** A graph with an outerplanar Hamiltonian cycle has an
outerplanar embedding of its simple graph: the cycle as the outer face, chords inside. -/
theorem OuterplanarHam.outerplanarEmbedding {g : Graph} {ham : List ℕ} {es : List Edge}
    (h : OuterplanarHam g ham) (hes : RepEdges g es) : OuterplanarEmbedding es :=
  (h.sphOuter hes).outerplanarEmbedding

/-- **Lemma 19, 1-connected sentence.** Every 2-connected `K_{2,3}`-minor-free graph has an
outerplanar embedding of its simple graph or is a `K₄`. -/
theorem twoConnected_outerplanar_or_k4_of_rep (g : Graph) {es : List Edge} (hes : RepEdges g es)
    (h2 : TwoConnected g) (hg : K23MinorFree g) : OuterplanarEmbedding es ∨ IsK4Graph g := by
  rcases twoConnectedK23_structure g h2 hg with hk | ⟨ham, hham⟩
  · exact Or.inr hk
  · exact Or.inl (hham.outerplanarEmbedding hes)

/-- **Lemma 19, construction direction.** A graph with neither a `K₄` nor a `K_{2,3}` minor
is outerplanar: its simple graph has a planar drawing with every vertex on the outer face. -/
theorem outerplanarDrawing_of_minorFree {g : Graph} (h4 : ¬ HasMinor g 4 k4)
    (h23 : ¬ HasMinor g 5 k23) : OuterplanarDrawing g :=
  outerplanarEmbedding_of_minorFree (simpleEdges_rep g) h4 h23

/-- A graph with an outerplanar Hamiltonian cycle is outerplanar (the polygon drawing). -/
theorem OuterplanarHam.outerplanarDrawing {g : Graph} {ham : List ℕ}
    (h : OuterplanarHam g ham) : OuterplanarDrawing g :=
  h.outerplanarEmbedding (simpleEdges_rep g)

/-- **Lemma 19, last sentence.** Every 2-connected `K_{2,3}`-minor-free graph is outerplanar
or a `K₄`. -/
theorem twoConnected_outerplanar_or_k4 (g : Graph) (h2 : TwoConnected g) (hg : K23MinorFree g) :
    OuterplanarDrawing g ∨ IsK4Graph g :=
  twoConnected_outerplanar_or_k4_of_rep g (simpleEdges_rep g) h2 hg

end STACS2027
