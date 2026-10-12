module

public import Outerplanar.OuterplanarConstruct
public import Outerplanar.OuterplanarMinor
public import Outerplanar.OuterplanarK4K23
public import Outerplanar.HypermapEuler

/-!
# Lemma 19, complete

Lemma 19 of the manuscript : *"A graph is outerplanar if it
has a planar drawing with every vertex on the outer face. Equivalently, it contains neither
`K₄` nor `K_{2,3}` as a minor. Every 2-connected `K_{2,3}`-minor-free graph is either
outerplanar or isomorphic to `K₄`."*

Outerplanarity is `OuterplanarDrawing` (`Outerplanar/OuterplanarDef.lean`): the simple graph has
a planar embedding (a planar hypermap on the half-edges, the foundation's notion of planarity)
with, in every connected component, a face through every vertex of that component.

* `outerplanarDrawing_iff_minorFree`: `OuterplanarDrawing g ↔ ¬ HasMinor g 4 k4 ∧ ¬ HasMinor g 5 k23`
  (ANONYMIZED–ANONYMIZED). `⇐`: `outerplanarDrawing_of_minorFree` (blocks: `twoConnectedK23_structure` and the polygon
  embedding of an outerplanar Hamiltonian cycle; gluing at cut vertices; disjoint unions).
  `⇒`: outerplanar drawings are closed under minors (`OuterplanarDrawing.of_hasMinor`: edge
  deletion, using Euler's inequality and parity for hypermaps, `hypermapEuler`, and edge
  contraction), and `K₄`, `K_{2,3}` have none (`not_outerplanarDrawing_k4`, `_k23`: face
  counting with Euler's formula).
* `twoConnected_outerplanar_or_k4`: every 2-connected `K_{2,3}`-minor-free graph is outerplanar or a `K₄`.
* `outerplanar_block_structure`: both statements together.
* `outerplanarDrawing_iff_outerplanar`: the drawing definition agrees with the minor
  characterization `Outerplanar` used elsewhere in the library.
-/

@[expose] public section

namespace STACS2027

/-- **Lemma 19, the equivalence** (ANONYMIZED and ANONYMIZED): a graph has a planar drawing with
every vertex on the outer face if and only if it has neither `K₄` nor `K_{2,3}` as a minor. -/
theorem outerplanarDrawing_iff_minorFree (g : Graph) :
    OuterplanarDrawing g ↔ (¬ HasMinor g 4 k4 ∧ ¬ HasMinor g 5 k23) :=
  ⟨fun h => h.outerplanar hypermapEuler not_outerplanarDrawing_k4 not_outerplanarDrawing_k23,
    fun h => outerplanarDrawing_of_minorFree h.1 h.2⟩

/-- The drawing definition of outerplanarity agrees with the minor characterization
`Outerplanar` (no `K₄` and no `K_{2,3}` minor) used by the rest of the library. -/
theorem outerplanarDrawing_iff_outerplanar (g : Graph) : OuterplanarDrawing g ↔ Outerplanar g :=
  outerplanarDrawing_iff_minorFree g

/-- **Lemma 19** (ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED; ANONYMIZED, ANONYMIZED), complete: a graph
is outerplanar (has a planar drawing with every vertex on the outer face) if and only if it has
neither `K₄` nor `K_{2,3}` as a minor, and every 2-connected `K_{2,3}`-minor-free graph is
outerplanar or isomorphic to `K₄`. -/
theorem outerplanar_block_structure (g : Graph) :
    (OuterplanarDrawing g ↔ (¬ HasMinor g 4 k4 ∧ ¬ HasMinor g 5 k23)) ∧
      (TwoConnected g → K23MinorFree g → OuterplanarDrawing g ∨ IsK4Graph g) :=
  ⟨outerplanarDrawing_iff_minorFree g, twoConnected_outerplanar_or_k4 g⟩

end STACS2027
