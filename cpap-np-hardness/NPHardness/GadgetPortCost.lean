module

public import NPHardness.GadgetExpansionCost
public import NPHardness.ExpansionPorts

/-! A blocked literal adds one unit of load at its port. The local clause
inequalities and witnesses are transported to every nonexceptional subdivision. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

theorem clauseThreeExpansion_blocked_lower {k : Nat} (hk : 5 ≤ k) (choose : Cycle → Nat) :
    2 ≤ costWithPorts (clauseThreeCycles5.map fun c =>
      selectedAt (clauseThreeExpansion k hk c) (choose c)) clauseThreePorts5 := by
  obtain ⟨hb, hn, hnl⟩ := clauseThree_links_wellformed k
  have hv := linkSteps_from_base_valid 18 (clauseThreeLinks k) hb hn hnl
  have hports : ∀ e ∈ clauseThreePorts5, e ∈ clauseThree5 ∧
      expandedEdge (linkSteps 18 (clauseThreeLinks k)) e = [e] := by
    intro e he
    exact ⟨(by decide : ∀ e ∈ clauseThreePorts5, e ∈ clauseThree5) e he,
      clauseThree_ports_unchanged k e he⟩
  have hnorm := expanded_family_costWithPorts_normalizes hv clauseThreeCycles5
    (clauseThreeExpansion k hk) clauseThree5_cycles_self
    (fun c hc => (clauseThreeExpansion_spec hk hc).1)
    (fun c hc => (clauseThreeExpansion_spec hk hc).2)
    (clauseThree_expansion_shared k) clauseThreePorts5 hports choose
  obtain ⟨ps, hps, hp⟩ := vertex_choices_have_options clauseThree5_cycles_self
    (fun c => originalChoice c (choose c))
    (fun c hc => originalChoice_mem (clauseThree5_cycles_self c hc) (choose c))
  have hpos := clauseThree5_blocked_lower ps hps
  rw [← costWithPorts_eq_append ps clauseThreePorts5 (by decide), hp.costWithPorts_eq] at hpos
  exact Nat.le_trans hpos hnorm

theorem clauseTwoExpansion_blocked_lower {k : Nat} (hk : 5 ≤ k) (h6 : k ≠ 6)
    (choose : Cycle → Nat) :
    2 ≤ costWithPorts (clauseTwoCycles5.map fun c =>
      selectedAt (clauseTwoExpansion k hk c) (choose c)) [(0,1),(4,5)] := by
  obtain ⟨hb, hn, hnl⟩ := clauseTwo_links_wellformed k
  have hv := linkSteps_from_base_valid 24 (clauseTwoLinks k) hb hn hnl
  have hports : ∀ e ∈ [(0,1),(4,5)], e ∈ clauseTwoSkeleton ∧
      expandedEdge (linkSteps 24 (clauseTwoLinks k)) e = [e] := by
    intro e he
    exact ⟨(by decide : ∀ e ∈ [(0,1),(4,5)], e ∈ clauseTwoSkeleton) e he,
      clauseTwo_ports_unchanged h6 e he⟩
  have hnorm := expanded_family_costWithPorts_normalizes hv clauseTwoCycles5
    (clauseTwoExpansion k hk) clauseTwo5_cycles_self
    (fun c hc => (clauseTwoExpansion_spec hk hc).1)
    (fun c hc => (clauseTwoExpansion_spec hk hc).2)
    (clauseTwo_expansion_shared h6) [(0,1),(4,5)] hports choose
  obtain ⟨ps, hps, hp⟩ := vertex_choices_have_options clauseTwo5_cycles_self
    (fun c => originalChoice c (choose c))
    (fun c hc => originalChoice_mem (clauseTwo5_cycles_self c hc) (choose c))
  have hpos := clauseTwo5_blocked_lower ps hps
  change 2 ≤ cost (ps.reverse ++ [(0,1),(4,5)].map (fun e => [e])) at hpos
  rw [← costWithPorts_eq_append ps [(0,1),(4,5)] (by decide), hp.costWithPorts_eq] at hpos
  exact Nat.le_trans hpos hnorm

theorem clauseThreeWitnessVertex_avoids : ∀ p i : Fin 3, i ≠ p →
    ∀ c ∈ clauseThreeCycles5, clauseThreePorts5[i.val]! ∉ selectedAt c (clauseThreeWitnessVertex p c) := by decide

theorem clauseTwoWitnessVertex_avoids : ∀ p : Bool, ∀ c ∈ clauseTwoCycles5,
    (if p then (0,1) else (4,5)) ∉ selectedAt c (clauseTwoWitnessVertex p c) := by decide

theorem clauseThreeExpansion_witness_avoids {k : Nat} (hk : 5 ≤ k) (p i : Fin 3) (hi : i ≠ p)
    (c : Cycle) (hc : c ∈ clauseThreeCycles5) :
    clauseThreePorts5[i.val]! ∉ selectedAt (clauseThreeExpansion k hk c) (clauseThreeWitnessVertex p c) := by
  obtain ⟨hb, hn, hnl⟩ := clauseThree_links_wellformed k
  have he : clauseThreePorts5[i.val]! ∈ clausePorts :=
    (by decide : ∀ i : Fin 3, clauseThreePorts5[i.val]! ∈ clausePorts) i
  have heg : clauseThreePorts5[i.val]! ∈ clauseThree5 :=
    (by decide : ∀ i : Fin 3, clauseThreePorts5[i.val]! ∈ clauseThree5) i
  rw [expanded_selectedAt_port_mem (linkSteps_from_base_valid 18 (clauseThreeLinks k) hb hn hnl)
    (clauseThree5_cycles_self c hc) (clauseThreeExpansion_spec hk hc).2 heg
    (clauseThree_ports_unchanged k _ he)]
  exact clauseThreeWitnessVertex_avoids p i hi c hc

theorem clauseTwoExpansion_witness_avoids {k : Nat} (hk : 5 ≤ k) (h6 : k ≠ 6) (p : Bool)
    (c : Cycle) (hc : c ∈ clauseTwoCycles5) :
    (if p then (0,1) else (4,5)) ∉ selectedAt (clauseTwoExpansion k hk c) (clauseTwoWitnessVertex p c) := by
  obtain ⟨hb, hn, hnl⟩ := clauseTwo_links_wellformed k
  have he : (if p then (0,1) else (4,5)) ∈ [(0,1),(4,5)] := by cases p <;> simp
  have heg : (if p then (0,1) else (4,5)) ∈ clauseTwoSkeleton :=
    (by decide : ∀ e ∈ [(0,1),(4,5)], e ∈ clauseTwoSkeleton) _ he
  rw [expanded_selectedAt_port_mem (linkSteps_from_base_valid 24 (clauseTwoLinks k) hb hn hnl)
    (clauseTwo5_cycles_self c hc) (clauseTwoExpansion_spec hk hc).2 heg
    (clauseTwo_ports_unchanged h6 _ he)]
  exact clauseTwoWitnessVertex_avoids p c hc

end STACS2027
