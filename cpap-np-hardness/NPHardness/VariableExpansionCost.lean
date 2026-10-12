module

public import NPHardness.GadgetPortCost

/-! Truth states and zero-cost normalization for every k ≥ 5. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

def variableStateVertex (truth : Bool) (c : Cycle) : Nat :=
  if c = [0,1,4,3] then (if truth then 4 else 3) else (if truth then 2 else 4)

def variableSkeletonState (truth : Bool) : List (List Edge) :=
  variableSkeletonInputs.map fun c => selectedAt c (variableStateVertex truth c)

noncomputable def variableExpandedState (k : Nat) (hk : 5 ≤ k) (truth : Bool) : List (List Edge) :=
  variableSkeletonInputs.map fun c => selectedAt (variableExpansion k hk c) (variableStateVertex truth c)

theorem variable_inputs_valid : ∀ c ∈ variableSkeletonInputs, IsCycle variableSkeleton c.length c :=
  fun c hc => variableSkeleton_cycles_valid c (variableSkeletonInputs_subset hc)

theorem variableStateVertex_valid : ∀ t : Bool, ∀ c ∈ variableSkeletonInputs,
    variableStateVertex t c ∈ c := by decide

theorem variableSkeletonState_zero : ∀ t : Bool, cost (variableSkeletonState t) = 0 := by decide

theorem variableSkeletonState_loads : ∀ t : Bool,
    load (variableSkeletonState t) (2,6) = (if t then 0 else 1) ∧
    load (variableSkeletonState t) (0,3) = (if t then 1 else 0) ∧
    load (variableSkeletonState t) (4,5) = (if t then 1 else 0) := by decide

theorem variableSkeleton_normalizes : ∀ u ∈ ([0,1,4,3] : Cycle), ∀ v ∈ ([1,2,6,5,4] : Cycle),
    cost [selectedAt [0,1,4,3] u, selectedAt [1,2,6,5,4] v] = 0 →
      ∃ t : Bool, ∀ e ∈ variablePorts, load (variableSkeletonState t) e ≤
        load [selectedAt [0,1,4,3] u, selectedAt [1,2,6,5,4] v] e := by decide

theorem variableExpandedState_valid {k : Nat} (hk : 5 ≤ k) (t : Bool) :
    ∀ c ∈ variableSkeletonInputs, variableStateVertex t c ∈ variableExpansion k hk c := by
  intro c hc
  exact expanded_cycle_vertices (variable_inputs_valid c hc) (variableExpansion_spec hk hc).1
    (variableExpansion_spec hk hc).2 (variableStateVertex_valid t c hc)

theorem variableExpandedState_zero {k : Nat} (hk : 5 ≤ k) (t : Bool) :
    cost (variableExpandedState k hk t) = 0 := by
  obtain ⟨hb, hn, hnl⟩ := variable_links_wellformed k
  unfold variableExpandedState
  rw [← expanded_family_cost_eq (linkSteps_from_base_valid 7 (variableLinks k) hb hn hnl)
    variableSkeletonInputs (variableExpansion k hk) variable_inputs_valid
    (fun c hc => (variableExpansion_spec hk hc).1)
    (fun c hc => (variableExpansion_spec hk hc).2) (variable_expansion_shared k)]
  exact variableSkeletonState_zero t

theorem variableExpandedState_port {k : Nat} (hk : 5 ≤ k) (t : Bool) (e : Edge)
    (he : e ∈ variablePorts) : load (variableExpandedState k hk t) e = load (variableSkeletonState t) e := by
  obtain ⟨hb, hn, hnl⟩ := variable_links_wellformed k
  exact expanded_family_port_eq (linkSteps_from_base_valid 7 (variableLinks k) hb hn hnl)
    variableSkeletonInputs (variableExpansion k hk) variable_inputs_valid
    (fun c hc => (variableExpansion_spec hk hc).1)
    (fun c hc => (variableExpansion_spec hk hc).2)
    ((by decide : ∀ e ∈ variablePorts, e ∈ variableSkeleton) e he)
    (variable_ports_unchanged k e he) (variableStateVertex t)

theorem variableExpandedState_loads {k : Nat} (hk : 5 ≤ k) (t : Bool) :
    load (variableExpandedState k hk t) (2,6) = (if t then 0 else 1) ∧
    load (variableExpandedState k hk t) (0,3) = (if t then 1 else 0) ∧
    load (variableExpandedState k hk t) (4,5) = (if t then 1 else 0) := by
  rw [variableExpandedState_port hk t (2,6) (by decide),
    variableExpandedState_port hk t (0,3) (by decide),
    variableExpandedState_port hk t (4,5) (by decide)]
  exact variableSkeletonState_loads t

theorem variableExpansion_zero_normalizes {k : Nat} (hk : 5 ≤ k) (choose : Cycle → Nat)
    (hz : cost (variableSkeletonInputs.map fun c => selectedAt (variableExpansion k hk c) (choose c)) = 0) :
    ∃ t : Bool, ∀ e ∈ variablePorts, load (variableExpandedState k hk t) e ≤
      load (variableSkeletonInputs.map fun c => selectedAt (variableExpansion k hk c) (choose c)) e := by
  obtain ⟨hb, hn, hnl⟩ := variable_links_wellformed k
  have hv := linkSteps_from_base_valid 7 (variableLinks k) hb hn hnl
  have hnorm := expanded_family_normalizes hv variableSkeletonInputs (variableExpansion k hk)
    variable_inputs_valid (fun c hc => (variableExpansion_spec hk hc).1)
    (fun c hc => (variableExpansion_spec hk hc).2) (variable_expansion_shared k) choose
  rw [hz] at hnorm
  have hzero : cost (variableSkeletonInputs.map fun c => selectedAt c (originalChoice c (choose c))) = 0 := by omega
  have hu := originalChoice_mem (variable_inputs_valid [0,1,4,3] (by decide)) (choose [0,1,4,3])
  have hw := originalChoice_mem (variable_inputs_valid [1,2,6,5,4] (by decide)) (choose [1,2,6,5,4])
  obtain ⟨t, ht⟩ := variableSkeleton_normalizes _ hu _ hw hzero
  refine ⟨t, ?_⟩
  intro e he
  rw [variableExpandedState_port hk t e he]
  apply Nat.le_trans (ht e he)
  exact expanded_family_port_normalizes hv variableSkeletonInputs (variableExpansion k hk)
    variable_inputs_valid (fun c hc => (variableExpansion_spec hk hc).1)
    (fun c hc => (variableExpansion_spec hk hc).2)
    ((by decide : ∀ e ∈ variablePorts, e ∈ variableSkeleton) e he)
    (variable_ports_unchanged k e he) choose

end STACS2027
