module

public import NPHardness.SubdivisionPrograms
public import NPHardness.ClauseThree5

/-! All-k projection of the actual Figure 4 constructors onto their finite skeletons. -/

@[expose] public section
namespace STACS2027

theorem IsCycle.length_le_bound {g : Graph} {n r : Nat} {c : Cycle}
    (hb : VerticesBelow g n) (hc : IsCycle g r c) : r ≤ n := by
  have hsub : c ⊆ List.range n := by
    intro v hv
    obtain ⟨w, _, he⟩ := hc.vertex_incident hv
    exact List.mem_range.mpr ((edge_below v w n).mp (hb _ (hc.2.2.2 _ he))).1
  have h := hc.2.2.1.length_le_of_subset hsub
  simpa only [hc.2.1, List.length_range] using h

def variableSkeleton : Graph := linkEdges (variableLinks 0)
def clauseTwoSkeleton : Graph := linkEdges (clauseTwoLinks 5)

theorem variable_links_wellformed (k : Nat) :
    VerticesBelow (linkEdges (variableLinks k)) 7 ∧
    (linkEdges (variableLinks k)).Nodup ∧
    (∀ l ∈ variableLinks k, l.source ≠ l.target) := by
  simp [VerticesBelow, linkEdges, variableLinks, edge]

theorem clauseThree_links_wellformed (k : Nat) :
    VerticesBelow (linkEdges (clauseThreeLinks k)) 18 ∧
    (linkEdges (clauseThreeLinks k)).Nodup ∧
    (∀ l ∈ clauseThreeLinks k, l.source ≠ l.target) := by
  simp [VerticesBelow, linkEdges, clauseThreeLinks, edge]

theorem clauseTwo_links_wellformed (k : Nat) :
    VerticesBelow (linkEdges (clauseTwoLinks k)) 24 ∧
    (linkEdges (clauseTwoLinks k)).Nodup ∧
    (∀ l ∈ clauseTwoLinks k, l.source ≠ l.target) := by
  simp [VerticesBelow, linkEdges, clauseTwoLinks, clauseThreeLinks, edge]

theorem variable_cycle_projection {k r : Nat} {c : Cycle} (hc : IsCycle (variableGraph k) r c) :
    ∃ l d, IsCycle variableSkeleton l d ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 7 (variableLinks k)))) := by
  obtain ⟨hb, hn, hp⟩ := variable_links_wellformed k
  exact realizeLinks_cycle_projection 7 (variableLinks k) hb hn hp hc

theorem clauseThree_cycle_projection {k r : Nat} {c : Cycle} (hc : IsCycle (clauseThreeGraph k) r c) :
    ∃ l d, IsCycle clauseThree5 l d ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 18 (clauseThreeLinks k)))) := by
  obtain ⟨hb, hn, hp⟩ := clauseThree_links_wellformed k
  exact realizeLinks_cycle_projection 18 (clauseThreeLinks k) hb hn hp hc

theorem clauseTwo_cycle_projection {k r : Nat} {c : Cycle} (hc : IsCycle (clauseTwoGraph k) r c) :
    ∃ l d, IsCycle clauseTwoSkeleton l d ∧
      (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge (linkSteps 24 (clauseTwoLinks k)))) := by
  obtain ⟨hb, hn, hp⟩ := clauseTwo_links_wellformed k
  exact realizeLinks_cycle_projection 24 (clauseTwoLinks k) hb hn hp hc

end STACS2027
