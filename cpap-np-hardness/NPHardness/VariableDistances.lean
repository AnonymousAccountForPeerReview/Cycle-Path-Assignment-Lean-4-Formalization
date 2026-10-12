module

public import NPHardness.PathProjection
public import NPHardness.VariableGeneral
public import NPHardness.GlobalGraph

/-! The separation estimates used to exclude cycles crossing gadget boundaries. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

def variablePotential (k port v : Nat) : Nat :=
  if port = 0 then
    if v = 2 ∨ v = 6 then 0 else if v = 1 then (k-3)/2 else (k-2)/2
  else if port = 1 then
    if v = 4 ∨ v = 5 then 0 else if v = 1 then 1 else (k-2)/2
  else
    if v = 0 ∨ v = 3 then 0 else (k-2)/2

theorem variablePotential_lipschitz {k port : Nat} (hk : 5 ≤ k) (hp : port < 3) :
    ∀ a b, edge a b ∈ variableSkeleton →
      variablePotential k port b ≤ variablePotential k port a + variableWeight k (edge a b) := by
  intro a b he
  have hc : port = 0 ∨ port = 1 ∨ port = 2 := by omega
  obtain ⟨l, hl, heq⟩ := List.mem_map.mp (show edge a b ∈ linkEdges (variableLinks k) from he)
  simp only [variableLinks, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals have hends := (edge_eq_iff ..).mp heq
  all_goals rcases hends with ⟨ha,hb⟩ | ⟨hb,ha⟩
  all_goals subst a; subst b
  all_goals rcases hc with rfl | rfl | rfl
  all_goals simp [variablePotential, variableWeight, edge]
  all_goals omega

theorem variablePotential_source (k : Nat) {port : Nat} (hp : port < 3) (side : Bool) :
    variablePotential k port (variableEndpoint port side) = 0 := by
  have hc : port = 0 ∨ port = 1 ∨ port = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> cases side <;> simp [variablePotential, variableEndpoint]

theorem variablePotential_other (k : Nat) {p q : Nat} (hp : p < 3) (hq : q < 3)
    (hne : p ≠ q) (side : Bool) :
    variablePotential k p (variableEndpoint q side) = (k-2)/2 := by
  have hp' : p = 0 ∨ p = 1 ∨ p = 2 := by omega
  have hq' : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hp' with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl <;>
    cases side <;> simp_all [variablePotential, variableEndpoint]

/-- Every path crossing a variable gadget between distinct ports has at least
floor((k-2)/2) edges, for all prescribed subdivisions. -/
theorem variableGraph_port_distance {k p q : Nat} (hk : 5 ≤ k)
    (hp : p < 3) (hq : q < 3) (hne : p ≠ q) (a b : Bool) {vs : List Nat}
    (hpath : IsSimplePath (variableGraph k) (variableEndpoint p a) (variableEndpoint q b) vs) :
    (k-2)/2 ≤ (pathEdges vs).length := by
  obtain ⟨hb,hn,hl⟩ := variable_links_wellformed k
  obtain ⟨ds,hd,hperm⟩ := realizeLinks_path_projection 7 (variableLinks k) hb hn hl
    (variableEndpoint_bound p a) (variableEndpoint_bound q b) hpath
  have hlen := hperm.length_eq
  rw [List.length_flatMap] at hlen
  have hm : (pathEdges ds).map (fun e => (expandedEdge (linkSteps 7 (variableLinks k)) e).length) =
      (pathEdges ds).map (variableWeight k) := by
    apply List.map_congr_left
    intro e he
    exact variable_edge_expanded_length hk e (hd.2.2.2 e he)
  rw [hm] at hlen
  have hdistance := pathWeight_endpoint_bound variableSkeleton (variableWeight k)
    (variablePotential k p) (variablePotential_lipschitz hk hp) hd
  rw [variablePotential_source k hp a, variablePotential_other k hp hq hne b, Nat.zero_add] at hdistance
  exact hlen ▸ hdistance

theorem variableGraph_girth {k : Nat} (hk : 5 ≤ k) {r : Nat} {c : Cycle}
    (hc : IsCycle (variableGraph k) r c) : k ≤ r := by
  obtain ⟨s,d,hd,hp⟩ := variable_cycle_projection hc
  obtain ⟨e,he,hec,hs⟩ := variableSkeleton_represents hd
  have hperm := hp.trans ((hs.edge_perm hd hec).flatMap_right (expandedEdge (linkSteps 7 (variableLinks k))))
  have hlen := hperm.length_eq
  simp only [hc.edge_length, List.length_flatMap] at hlen
  change r = expandedLength (linkSteps 7 (variableLinks k)) e at hlen
  simp only [variableSkeletonCycles, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · rw [variable_input_lengths hk _ (by simp [variableSkeletonInputs])] at hlen
    omega
  · rw [variable_input_lengths hk _ (by simp [variableSkeletonInputs])] at hlen
    omega
  · rw [variable_outer_length hk] at hlen
    omega

end STACS2027
