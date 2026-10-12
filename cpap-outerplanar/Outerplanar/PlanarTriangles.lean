module

public import Outerplanar.PlanarTriangleCardinality
public import Outerplanar.TriangleRepresentation
import Mathlib.Tactic

/-! Planarity alone implies the triangle-side Hall inequalities and a perfect
cycle-to-path assignment for triangles. -/

@[expose] public section
namespace STACS2027.TriangleMatching

/-- Every selected family of planar triangles has at least as many distinct
sides as members. -/
theorem planar_triangle_hall {g : Graph} (hp : Complexity.PlanarGraph g) :
    TriangleSideHall g := by
  classical
  intro S
  have hproper : ∀ e∈vertexSideUnion (enumeratedFamily g S),e.1<e.2 := by
    intro e he
    obtain ⟨T,_hT,he⟩ := Finset.mem_biUnion.mp he
    exact vertexSides_proper he
  have hplanar := enumeratedFamily_graph_planar hp S
  have hbound := planar_vertexFamily_card hproper hplanar
    (enumeratedFamily_triangles g S) (fun _ h=>h)
  rw [enumeratedFamily_card,enumeratedFamily_edges] at hbound
  exact hbound

/-- Every planar graph has a zero-cost cycle-to-path assignment of its
enumerated triangles. -/
theorem planar_triangle_perfect_assignment {g : Graph} (hp : Complexity.PlanarGraph g) :
    HasAssignment g 3 0 := triangle_perfect_of_hall (planar_triangle_hall hp)

end STACS2027.TriangleMatching
