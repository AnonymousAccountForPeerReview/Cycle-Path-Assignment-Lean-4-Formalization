module

public import NPHardness.GadgetFamilies

/-!
General-k internal-cost certificates on the complete, pairwise distinct cycle
families above. The two-literal k=6 case has its separate finite certificates.
These local results do not assert the global gluing or planarity theorem.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

theorem variable_expansion_shared (k : Nat) : variableSkeletonInputs.Pairwise
    (fun c d => ∀ e ∈ cycleEdges c, e ∈ cycleEdges d →
      expandedEdge (linkSteps 7 (variableLinks k)) e = [e]) := by
  have hn : variableSkeletonInputs.Nodup := by decide
  exact hn.imp_of_mem (fun {c d} hc hd hne => variable_shared_unchanged k hc hd hne)

theorem clauseThree_expansion_shared (k : Nat) : clauseThreeCycles5.Pairwise
    (fun c d => ∀ e ∈ cycleEdges c, e ∈ cycleEdges d →
      expandedEdge (linkSteps 18 (clauseThreeLinks k)) e = [e]) := by
  have hn : clauseThreeCycles5.Nodup := by decide
  exact hn.imp_of_mem (fun {c d} hc hd hne => clauseThree_shared_unchanged k hc hd hne)

theorem clauseTwo_expansion_shared {k : Nat} (hk : k ≠ 6) : clauseTwoCycles5.Pairwise
    (fun c d => ∀ e ∈ cycleEdges c, e ∈ cycleEdges d →
      expandedEdge (linkSteps 24 (clauseTwoLinks k)) e = [e]) := by
  have hn : clauseTwoCycles5.Nodup := by decide
  exact hn.imp_of_mem (fun {c d} hc hd hne => clauseTwo_shared_unchanged hk hc hd hne)

theorem clauseThree5_cycles_self : ∀ c ∈ clauseThreeCycles5, IsCycle clauseThree5 c.length c := by
  intro c hc
  have h := clauseThree5_cycles_valid c hc
  simpa only [h.2.1] using h

theorem clauseTwo5_cycles_self : ∀ c ∈ clauseTwoCycles5, IsCycle clauseTwoSkeleton c.length c := by
  intro c hc
  rw [clauseTwo_skeleton_eq_five]
  have h := clauseTwo5_cycles_valid c hc
  simpa only [h.2.1] using h

theorem clauseThreeExpansion_cost_positive {k : Nat} (hk : 5 ≤ k) (choose : Cycle → Nat) :
    1 ≤ cost (clauseThreeCycles5.map fun c => selectedAt (clauseThreeExpansion k hk c) (choose c)) := by
  obtain ⟨hb, hn, hnl⟩ := clauseThree_links_wellformed k
  have hv := linkSteps_from_base_valid 18 (clauseThreeLinks k) hb hn hnl
  have hnorm := expanded_family_normalizes hv clauseThreeCycles5 (clauseThreeExpansion k hk)
    clauseThree5_cycles_self (fun c hc => (clauseThreeExpansion_spec hk hc).1)
    (fun c hc => (clauseThreeExpansion_spec hk hc).2) (clauseThree_expansion_shared k) choose
  obtain ⟨ps, hps, hp⟩ := vertex_choices_have_options clauseThree5_cycles_self
    (fun c => originalChoice c (choose c))
    (fun c hc => originalChoice_mem (clauseThree5_cycles_self c hc) (choose c))
  have hpos := clauseThree5_cost_positive ps hps
  rw [hp.cost_eq] at hpos
  exact Nat.le_trans hpos hnorm

theorem clauseTwoExpansion_cost_positive {k : Nat} (hk : 5 ≤ k) (h6 : k ≠ 6)
    (choose : Cycle → Nat) :
    1 ≤ cost (clauseTwoCycles5.map fun c => selectedAt (clauseTwoExpansion k hk c) (choose c)) := by
  obtain ⟨hb, hn, hnl⟩ := clauseTwo_links_wellformed k
  have hv := linkSteps_from_base_valid 24 (clauseTwoLinks k) hb hn hnl
  have hnorm := expanded_family_normalizes hv clauseTwoCycles5 (clauseTwoExpansion k hk)
    clauseTwo5_cycles_self (fun c hc => (clauseTwoExpansion_spec hk hc).1)
    (fun c hc => (clauseTwoExpansion_spec hk hc).2) (clauseTwo_expansion_shared h6) choose
  obtain ⟨ps, hps, hp⟩ := vertex_choices_have_options clauseTwo5_cycles_self
    (fun c => originalChoice c (choose c))
    (fun c hc => originalChoice_mem (clauseTwo5_cycles_self c hc) (choose c))
  have hpos := clauseTwo5_cost_positive ps hps
  rw [hp.cost_eq] at hpos
  exact Nat.le_trans hpos hnorm

def clauseThreeWitnessVertex (p : Fin 3) (c : Cycle) : Nat :=
  c[(clauseThreeWitness5 p)[clauseThreeCycles5.idxOf c]!]!

def clauseTwoWitnessVertex (p : Bool) (c : Cycle) : Nat :=
  c[(clauseTwoWitness5 p)[clauseTwoCycles5.idxOf c]!]!

theorem clauseThreeWitnessVertex_valid : ∀ p : Fin 3, ∀ c ∈ clauseThreeCycles5,
    clauseThreeWitnessVertex p c ∈ c := by decide

theorem clauseTwoWitnessVertex_valid : ∀ p : Bool, ∀ c ∈ clauseTwoCycles5,
    clauseTwoWitnessVertex p c ∈ c := by decide

theorem clauseThreeWitnessVertex_cost : ∀ p : Fin 3,
    cost (clauseThreeCycles5.map fun c => selectedAt c (clauseThreeWitnessVertex p c)) = 1 := by decide

theorem clauseTwoWitnessVertex_cost : ∀ p : Bool,
    cost (clauseTwoCycles5.map fun c => selectedAt c (clauseTwoWitnessVertex p c)) = 1 := by decide

theorem clauseThreeExpansion_witness_valid {k : Nat} (hk : 5 ≤ k) (p : Fin 3) :
    ∀ c ∈ clauseThreeCycles5, clauseThreeWitnessVertex p c ∈ clauseThreeExpansion k hk c := by
  intro c hc
  exact expanded_cycle_vertices (clauseThree5_cycles_self c hc)
    (clauseThreeExpansion_spec hk hc).1 (clauseThreeExpansion_spec hk hc).2
    (clauseThreeWitnessVertex_valid p c hc)

theorem clauseTwoExpansion_witness_valid {k : Nat} (hk : 5 ≤ k) (p : Bool) :
    ∀ c ∈ clauseTwoCycles5, clauseTwoWitnessVertex p c ∈ clauseTwoExpansion k hk c := by
  intro c hc
  exact expanded_cycle_vertices (clauseTwo5_cycles_self c hc)
    (clauseTwoExpansion_spec hk hc).1 (clauseTwoExpansion_spec hk hc).2
    (clauseTwoWitnessVertex_valid p c hc)

theorem clauseThreeExpansion_witness_cost {k : Nat} (hk : 5 ≤ k) (p : Fin 3) :
    cost (clauseThreeCycles5.map fun c =>
      selectedAt (clauseThreeExpansion k hk c) (clauseThreeWitnessVertex p c)) = 1 := by
  obtain ⟨hb, hn, hnl⟩ := clauseThree_links_wellformed k
  rw [← expanded_family_cost_eq
    (linkSteps_from_base_valid 18 (clauseThreeLinks k) hb hn hnl)
    clauseThreeCycles5 (clauseThreeExpansion k hk) clauseThree5_cycles_self
    (fun c hc => (clauseThreeExpansion_spec hk hc).1)
    (fun c hc => (clauseThreeExpansion_spec hk hc).2) (clauseThree_expansion_shared k)]
  exact clauseThreeWitnessVertex_cost p

theorem clauseTwoExpansion_witness_cost {k : Nat} (hk : 5 ≤ k) (h6 : k ≠ 6) (p : Bool) :
    cost (clauseTwoCycles5.map fun c =>
      selectedAt (clauseTwoExpansion k hk c) (clauseTwoWitnessVertex p c)) = 1 := by
  obtain ⟨hb, hn, hnl⟩ := clauseTwo_links_wellformed k
  rw [← expanded_family_cost_eq
    (linkSteps_from_base_valid 24 (clauseTwoLinks k) hb hn hnl)
    clauseTwoCycles5 (clauseTwoExpansion k hk) clauseTwo5_cycles_self
    (fun c hc => (clauseTwoExpansion_spec hk hc).1)
    (fun c hc => (clauseTwoExpansion_spec hk hc).2) (clauseTwo_expansion_shared h6)]
  exact clauseTwoWitnessVertex_cost p

end STACS2027
