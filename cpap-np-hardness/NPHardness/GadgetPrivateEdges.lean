module

public import NPHardness.VariableGeneral
public import NPHardness.ClauseTwoGeneral
public import NPHardness.ExpansionCost

/-! The subdivided edges are private to their intended cycle, apart from
the separately certified k=6 auxiliary gadget. Literal ports remain edges. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

def variablePrivate : List Edge := [(0,1), (1,2), (3,4), (5,6)]
def clauseTwoPrivate : List Edge := clauseTwoGreen ++ clauseTwoOrange ++ clauseTwoBlue

theorem variable_private_certificate : ∀ c ∈ variableSkeletonInputs,
    ∀ d ∈ variableSkeletonInputs, c ≠ d →
      ∀ e ∈ cycleEdges c, e ∈ cycleEdges d → e ∉ variablePrivate := by decide

theorem clauseThree_private_certificate : ∀ c ∈ clauseThreeCycles5,
    ∀ d ∈ clauseThreeCycles5, c ≠ d →
      ∀ e ∈ cycleEdges c, e ∈ cycleEdges d → e ∉ clauseThreeGreen := by decide

theorem clauseTwo_private_certificate : ∀ c ∈ clauseTwoCycles5,
    ∀ d ∈ clauseTwoCycles5, c ≠ d →
      ∀ e ∈ cycleEdges c, e ∈ cycleEdges d → e ∉ clauseTwoPrivate := by decide

theorem variable_uncoloured_unchanged (k : Nat) (e : Edge)
    (he : e ∈ variableSkeleton) (hp : e ∉ variablePrivate) :
    expandedEdge (linkSteps 7 (variableLinks k)) e = [e] := by
  obtain ⟨hb, hn, hne⟩ := variable_links_wellformed k
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (show e ∈ linkEdges (variableLinks k) from he)
  apply linkSteps_zero 7 (variableLinks k) hb hn hne l hl
  simp only [variableLinks, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [variablePrivate, edge] at hp ⊢

theorem clauseThree_uncoloured_unchanged (k : Nat) (e : Edge)
    (he : e ∈ clauseThree5) (hp : e ∉ clauseThreeGreen) :
    expandedEdge (linkSteps 18 (clauseThreeLinks k)) e = [e] := by
  obtain ⟨hb, hn, hne⟩ := clauseThree_links_wellformed k
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (show e ∈ linkEdges (clauseThreeLinks k) from he)
  apply linkSteps_zero 18 (clauseThreeLinks k) hb hn hne l hl
  simp only [clauseThreeLinks, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [clauseThreeGreen, edge] at hp ⊢

theorem clauseTwo_uncoloured_unchanged {k : Nat} (hk : k ≠ 6) (e : Edge)
    (he : e ∈ clauseTwoSkeleton) (hp : e ∉ clauseTwoPrivate) :
    expandedEdge (linkSteps 24 (clauseTwoLinks k)) e = [e] := by
  obtain ⟨hb, hn, hne⟩ := clauseTwo_links_wellformed k
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (show e ∈ linkEdges (clauseTwoLinks k) from he)
  apply linkSteps_zero 24 (clauseTwoLinks k) hb hn hne l hl
  simp only [clauseTwoLinks, clauseThreeLinks, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp [clauseTwoPrivate, clauseTwoGreen, clauseThreeGreen,
    clauseTwoOrange, clauseTwoBlue, edge, redSubdivisions, hk] at hp ⊢

theorem variable_shared_unchanged (k : Nat) {c d : Cycle}
    (hc : c ∈ variableSkeletonInputs) (hd : d ∈ variableSkeletonInputs) (hne : c ≠ d)
    (e : Edge) (hec : e ∈ cycleEdges c) (hed : e ∈ cycleEdges d) :
    expandedEdge (linkSteps 7 (variableLinks k)) e = [e] := by
  apply variable_uncoloured_unchanged k e
  · have hv : ∀ c ∈ variableSkeletonInputs, ∀ e ∈ cycleEdges c, e ∈ variableSkeleton := by decide
    exact hv c hc e hec
  · exact variable_private_certificate c hc d hd hne e hec hed

theorem clauseThree_shared_unchanged (k : Nat) {c d : Cycle}
    (hc : c ∈ clauseThreeCycles5) (hd : d ∈ clauseThreeCycles5) (hne : c ≠ d)
    (e : Edge) (hec : e ∈ cycleEdges c) (hed : e ∈ cycleEdges d) :
    expandedEdge (linkSteps 18 (clauseThreeLinks k)) e = [e] :=
  clauseThree_uncoloured_unchanged k e ((clauseThree5_cycles_valid c hc).2.2.2 e hec)
    (clauseThree_private_certificate c hc d hd hne e hec hed)

theorem clauseTwo_shared_unchanged {k : Nat} (hk : k ≠ 6) {c d : Cycle}
    (hc : c ∈ clauseTwoCycles5) (hd : d ∈ clauseTwoCycles5) (hne : c ≠ d)
    (e : Edge) (hec : e ∈ cycleEdges c) (hed : e ∈ cycleEdges d) :
    expandedEdge (linkSteps 24 (clauseTwoLinks k)) e = [e] :=
  clauseTwo_uncoloured_unchanged hk e ((clauseTwo5_cycles_valid c hc).2.2.2 e hec)
    (clauseTwo_private_certificate c hc d hd hne e hec hed)

theorem variable_ports_unchanged (k : Nat) :
    ∀ e ∈ variablePorts, expandedEdge (linkSteps 7 (variableLinks k)) e = [e] := by
  intro e he
  apply variable_uncoloured_unchanged k e
  · exact (by decide : ∀ e ∈ variablePorts, e ∈ variableSkeleton) e he
  · exact (by decide : ∀ e ∈ variablePorts, e ∉ variablePrivate) e he

theorem clauseThree_ports_unchanged (k : Nat) :
    ∀ e ∈ clausePorts, expandedEdge (linkSteps 18 (clauseThreeLinks k)) e = [e] := by
  intro e he
  apply clauseThree_uncoloured_unchanged k e
  · exact (by decide : ∀ e ∈ clausePorts, e ∈ clauseThree5) e he
  · exact (by decide : ∀ e ∈ clausePorts, e ∉ clauseThreeGreen) e he

theorem clauseTwo_ports_unchanged {k : Nat} (hk : k ≠ 6) :
    ∀ e ∈ [(0,1),(4,5)], expandedEdge (linkSteps 24 (clauseTwoLinks k)) e = [e] := by
  intro e he
  apply clauseTwo_uncoloured_unchanged hk e
  · exact (by decide : ∀ e ∈ [(0,1),(4,5)], e ∈ clauseTwoSkeleton) e he
  · exact (by decide : ∀ e ∈ [(0,1),(4,5)], e ∉ clauseTwoPrivate) e he

end STACS2027
