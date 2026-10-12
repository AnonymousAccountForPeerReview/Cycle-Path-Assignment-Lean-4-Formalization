module

public import Outerplanar.NeighbourConeMinor
public import Outerplanar.PlanarMinorClosure
import Mathlib.Tactic

/-! Removing an apex from its planar neighbour cone gives an outerplanar graph. -/

@[expose] public section
namespace STACS2027.PlanarTriangleGeometry
open Complexity

theorem hasMinor_target_subset {g h h' : Graph} {size : Nat}
    (hm : HasMinor g size h) (hs : ∀ e∈h',e∈h) : HasMinor g size h' := by
  obtain ⟨B,hne,hdisj,hconn,hedges⟩ := hm
  exact ⟨B,hne,hdisj,hconn,fun e he => hedges e (hs e he)⟩

theorem clique_vertex (i : Nat) (hi : i<4) : ∃ j,Adj k4 i j := by
  interval_cases i
  · exact ⟨1,by decide⟩
  · exact ⟨0,by decide⟩
  · exact ⟨0,by decide⟩
  · exact ⟨0,by decide⟩

theorem biclique_vertex (i : Nat) (hi : i<5) : ∃ j,Adj k23 i j := by
  interval_cases i
  · exact ⟨2,by decide⟩
  · exact ⟨2,by decide⟩
  · exact ⟨0,by decide⟩
  · exact ⟨0,by decide⟩
  · exact ⟨0,by decide⟩

/-- The neighbours of any vertex of a planar graph induce an outerplanar graph. -/
theorem planar_neighbours_outerplanar {g : Graph} (hp : PlanarGraph g) (apex : Nat) :
    OuterplanarDrawing (neighbourGraph g apex) := by
  apply (outerplanarDrawing_iff_minorFree _).mpr
  constructor
  · intro hm
    have hc := neighbour_minor_cone hm (by decide) clique_vertex
    have heq : cone k4 4 = completeFive := by decide
    rw [heq] at hc
    have hg := hp.of_hasMinor hc (by decide)
    rw [simpleEdges_completeFive] at hg
    exact completeFive_not_planar hg
  · intro hm
    have hc := neighbour_minor_cone hm (by decide) biclique_vertex
    have hs : ∀ e∈bipartiteThree,e∈cone k23 5 := by decide
    have hb := hasMinor_target_subset hc hs
    have hg := hp.of_hasMinor hb (by decide)
    rw [simpleEdges_bipartiteThree] at hg
    exact bipartiteThree_not_planar hg

end STACS2027.PlanarTriangleGeometry
