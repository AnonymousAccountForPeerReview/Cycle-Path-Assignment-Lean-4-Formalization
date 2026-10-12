module

public import Outerplanar.PlanarLightEdge
public import Outerplanar.TrianglePlanarContract
public import Outerplanar.TriangleContractionBounds
import Mathlib.Tactic

/-! Every family of distinct triangles in a planar graph has at most as many
members as the union of its edges. The proof contracts a light edge and uses
the exact losses in edge and triangle cardinalities. -/

@[expose] public section
namespace STACS2027.TriangleMatching

theorem planar_vertexFamily_card {E : Finset Edge}
    (hcanonical : ∀ e∈E,e.1<e.2) (hp : Complexity.PlanarGraph E.toList)
    {S : Finset (Finset Nat)} (hS : VertexTriangleFamily S)
    (hE : vertexSideUnion S⊆E) : S.card≤E.card := by
  classical
  suffices h : ∀ n : Nat, ∀ E : Finset Edge, E.card=n →
      (∀ e∈E,e.1<e.2) → Complexity.PlanarGraph E.toList →
      ∀ S : Finset (Finset Nat), VertexTriangleFamily S →
      vertexSideUnion S⊆E → S.card≤E.card by
    exact h E.card E rfl hcanonical hp S hS hE
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E hcard hcanonical hp S hS hE
    by_cases hnil : S=∅
    · simp [hnil]
    · obtain ⟨T,hT⟩ := Finset.nonempty_iff_ne_empty.mpr hnil
      have hsize : 1<T.card := by rw [hS T hT];omega
      obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hsize
      have hedge : edge a b∈E := hE (Finset.mem_biUnion.mpr
        ⟨T,hT,edge_mem_vertexSides ha hb hab⟩)
      obtain ⟨u,v,huv,huve,hsmall⟩ :=
        PlanarTriangleGeometry.planar_light_edge hp hcanonical ⟨edge a b,hedge⟩
      have hne : u≠v := Nat.ne_of_lt huv
      have hloss := identifyEdges_card hcanonical hne huve
      have hdrop : (identifyEdges u v E).card<n := by omega
      have hcontract := identifyEdges_planar hp huv huve
      have hproper := identifyEdges_proper hcanonical hne
      have htriangles := identifyFamily_isTriangles (u:=u) (v:=v) hS
      have hedges := identifyFamily_sideUnion_subset (u:=u) (v:=v) hE
      have hind := ih (identifyEdges u v E).card hdrop
        (identifyEdges u v E) rfl hproper hcontract
        (identifyFamily u v S) htriangles hedges
      have hbound := identifyFamily_card_bound hne hS hE hsmall
      omega

end STACS2027.TriangleMatching
