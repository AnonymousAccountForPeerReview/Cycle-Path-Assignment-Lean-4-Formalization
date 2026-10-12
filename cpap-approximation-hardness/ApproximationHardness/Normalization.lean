module

public import ApproximationHardness.PortLoads

/-!
# Normalizing a variable gadget without increasing the cost

"Normalize the variable-gadget paths without increasing the cost, as in Theorem 8"
(proof of Theorem 11). For any choice of paths in a variable gadget, and any weights
`w ≤ 1` on its three ports (the loads the clause gadgets put there), one of the two
truth states has weighted port load at most the gadget's own cost plus its weighted
port load. The finite check is on the unsubdivided skeleton; it transfers to every
subdivision and to every placed copy.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

/-- The weighted load at the three ports `port 0`, `port 1`, `port 2`. -/
def weightedLoad (ps : List (List Edge)) (port : Nat → Edge) (w : Nat → Nat) : Nat :=
  ((List.range 3).map fun i => load ps (port i) * w i).sum

theorem weightedLoad_eq (ps : List (List Edge)) (port : Nat → Edge) (w : Nat → Nat) :
    weightedLoad ps port w =
      load ps (port 0) * w 0 + load ps (port 1) * w 1 + load ps (port 2) * w 2 := by
  simp [weightedLoad, List.range_succ]
  omega

theorem variablePortEdge_values :
    variablePortEdge 0 = (2, 6) ∧ variablePortEdge 1 = (4, 5) ∧ variablePortEdge 2 = (0, 3) := by
  decide

/-- The finite check on the skeleton: for every choice of omitted vertices and every
`0/1` weights, one truth state is at least as good. -/
theorem variableSkeleton_weighted_normalizes :
    ∀ u ∈ ([0, 1, 4, 3] : Cycle), ∀ v ∈ ([1, 2, 6, 5, 4] : Cycle), ∀ b0 b1 b2 : Bool,
      ∃ t ∈ [false, true],
        load (variableSkeletonState t) (2, 6) * b0.toNat +
          load (variableSkeletonState t) (4, 5) * b1.toNat +
          load (variableSkeletonState t) (0, 3) * b2.toNat ≤
        cost [selectedAt [0, 1, 4, 3] u, selectedAt [1, 2, 6, 5, 4] v] +
          (load [selectedAt [0, 1, 4, 3] u, selectedAt [1, 2, 6, 5, 4] v] (2, 6) * b0.toNat +
            load [selectedAt [0, 1, 4, 3] u, selectedAt [1, 2, 6, 5, 4] v] (4, 5) * b1.toNat +
            load [selectedAt [0, 1, 4, 3] u, selectedAt [1, 2, 6, 5, 4] v] (0, 3) * b2.toNat) := by
  decide

theorem weight_eq_toNat {w : Nat} (hw : w ≤ 1) : w = (decide (w = 1)).toNat := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hw with h | h <;> simp [h]

/-- Normalization for every subdivision `k ≥ 5`. -/
theorem variableExpansion_weighted_normalizes {k : Nat} (hk : 5 ≤ k) (choose : Cycle → Nat)
    (w : Nat → Nat) (hw : ∀ i, w i ≤ 1) :
    ∃ t : Bool, weightedLoad (variableExpandedState k hk t) variablePortEdge w ≤
      cost (variableSkeletonInputs.map fun c => selectedAt (variableExpansion k hk c) (choose c)) +
        weightedLoad (variableSkeletonInputs.map fun c => selectedAt (variableExpansion k hk c) (choose c))
          variablePortEdge w := by
  obtain ⟨hb, hn, hnl⟩ := variable_links_wellformed k
  have hv := linkSteps_from_base_valid 7 (variableLinks k) hb hn hnl
  have hcost := expanded_family_normalizes hv variableSkeletonInputs (variableExpansion k hk)
    variable_inputs_valid (fun c hc => (variableExpansion_spec hk hc).1)
    (fun c hc => (variableExpansion_spec hk hc).2) (variable_expansion_shared k) choose
  have hport : ∀ e ∈ variablePorts,
      load (variableSkeletonInputs.map fun c => selectedAt c (originalChoice c (choose c))) e ≤
        load (variableSkeletonInputs.map fun c => selectedAt (variableExpansion k hk c) (choose c)) e := by
    intro e he
    exact expanded_family_port_normalizes hv variableSkeletonInputs (variableExpansion k hk)
      variable_inputs_valid (fun c hc => (variableExpansion_spec hk hc).1)
      (fun c hc => (variableExpansion_spec hk hc).2)
      ((by decide : ∀ e ∈ variablePorts, e ∈ variableSkeleton) e he)
      (variable_ports_unchanged k e he) choose
  have hu := originalChoice_mem (variable_inputs_valid [0,1,4,3] (by decide)) (choose [0,1,4,3])
  have hw' := originalChoice_mem (variable_inputs_valid [1,2,6,5,4] (by decide)) (choose [1,2,6,5,4])
  obtain ⟨t, _, ht⟩ := variableSkeleton_weighted_normalizes _ hu _ hw'
    (decide (w 0 = 1)) (decide (w 1 = 1)) (decide (w 2 = 1))
  refine ⟨t, ?_⟩
  obtain ⟨p0, p1, p2⟩ := variablePortEdge_values
  rw [weightedLoad_eq, weightedLoad_eq, p0, p1, p2,
    variableExpandedState_port hk t (2, 6) (by decide), variableExpandedState_port hk t (4, 5) (by decide),
    variableExpandedState_port hk t (0, 3) (by decide)]
  have h0 := hport (2, 6) (by decide)
  have h1 := hport (4, 5) (by decide)
  have h2 := hport (0, 3) (by decide)
  change load [selectedAt [0,1,4,3] (originalChoice [0,1,4,3] (choose [0,1,4,3])),
    selectedAt [1,2,6,5,4] (originalChoice [1,2,6,5,4] (choose [1,2,6,5,4]))] (2, 6) ≤ _ at h0
  change load [selectedAt [0,1,4,3] (originalChoice [0,1,4,3] (choose [0,1,4,3])),
    selectedAt [1,2,6,5,4] (originalChoice [1,2,6,5,4] (choose [1,2,6,5,4]))] (4, 5) ≤ _ at h1
  change load [selectedAt [0,1,4,3] (originalChoice [0,1,4,3] (choose [0,1,4,3])),
    selectedAt [1,2,6,5,4] (originalChoice [1,2,6,5,4] (choose [1,2,6,5,4]))] (0, 3) ≤ _ at h2
  change cost [selectedAt [0,1,4,3] (originalChoice [0,1,4,3] (choose [0,1,4,3])),
    selectedAt [1,2,6,5,4] (originalChoice [1,2,6,5,4] (choose [1,2,6,5,4]))] ≤ _ at hcost
  rw [weight_eq_toNat (hw 0), weight_eq_toNat (hw 1), weight_eq_toNat (hw 2)]
  have hm0 := Nat.mul_le_mul_right (decide (w 0 = 1)).toNat h0
  have hm1 := Nat.mul_le_mul_right (decide (w 1 = 1)).toNat h1
  have hm2 := Nat.mul_le_mul_right (decide (w 2 = 1)).toNat h2
  omega

/-- Normalization of the placed variable gadget `v`: the weighted load of one truth state at
the local ports is at most the cost of the placed gadget plus its weighted load at the placed
ports. -/
theorem variableChosen_weighted_normalizes {k : Nat} (hk : 5 ≤ k) (v : Nat) (choose : Cycle → Nat)
    (hv : ∀ c ∈ placedVariableFamily k hk v, choose c ∈ c) (w : Nat → Nat) (hw : ∀ i, w i ≤ 1) :
    ∃ t : Bool, weightedLoad (variableExpandedState k hk t) variablePortEdge w ≤
      cost (variableChosen k hk choose v) +
        weightedLoad (variableChosen k hk choose v)
          (fun i => mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i)) w := by
  obtain ⟨pick, hpick, hpaths, hcost⟩ := mapped_choice_cost (variableGraph_below k)
    (realizeLinks_normalized 7 (variableLinks k)) (variableFamily_valid hk)
    (blockVertex (gadgetWidth k) v) (fun _ ha _ hb he => (blockVertex_injective ha hb he).2) choose hv
  have hload : ∀ i, i < 3 → load (variableChosen k hk choose v)
      (mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i)) =
      load (chosenFamily (variableFamily k hk) pick) (variablePortEdge i) := by
    intro i hi
    change load (chosenFamily ((variableFamily k hk).map (List.map (blockVertex (gadgetWidth k) v))) choose) _ = _
    rw [hpaths]
    exact load_relabel (variableGraph_below k) (realizeLinks_normalized 7 (variableLinks k))
      (blockVertex (gadgetWidth k) v) (fun _ ha _ hb he => (blockVertex_injective ha hb he).2)
      (chosenFamily_supported (variableFamily_valid hk) pick)
      (show variablePortEdge i ∈ variableGraph k from variableGraph_ports k hi)
  have hcost' : cost (variableChosen k hk choose v) = cost (chosenFamily (variableFamily k hk) pick) := hcost
  obtain ⟨t, ht⟩ := variableExpansion_weighted_normalizes hk (fun c => pick (variableExpansion k hk c)) w hw
  refine ⟨t, ?_⟩
  have hfam : chosenFamily (variableFamily k hk) pick =
      variableSkeletonInputs.map fun c => selectedAt (variableExpansion k hk c) (pick (variableExpansion k hk c)) := by
    simp [chosenFamily, variableFamily, List.map_map, Function.comp_def]
  rw [hcost', hfam]
  have hwl : weightedLoad (variableChosen k hk choose v)
      (fun i => mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i)) w =
      weightedLoad (variableSkeletonInputs.map fun c =>
        selectedAt (variableExpansion k hk c) (pick (variableExpansion k hk c))) variablePortEdge w := by
    rw [weightedLoad_eq, weightedLoad_eq, hload 0 (by omega), hload 1 (by omega), hload 2 (by omega), hfam]
  rw [hwl]
  exact ht

end STACS2027
