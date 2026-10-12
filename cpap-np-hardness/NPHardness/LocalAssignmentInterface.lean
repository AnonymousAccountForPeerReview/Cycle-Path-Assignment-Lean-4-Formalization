module

public import NPHardness.GlobalFamilyUnique

/-! Uniform local assignment interfaces, including the exceptional k=6
two-literal gadget. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

@[expose] public section
namespace STACS2027

def chosenFamily (cs : List Cycle) (choose : Cycle → Nat) : List (List Edge) :=
  cs.map fun c => selectedAt c (choose c)

def activeClausePorts (c : List PlacedLiteral) : List Edge :=
  if c.length = 2 then [(0,1),(4,5)] else clauseThreePorts5

theorem chosenFamily_supported {g : Graph} {k : Nat} {cs : List Cycle}
    (hc : ∀ c ∈ cs, IsCycle g k c) (choose : Cycle → Nat) :
    ∀ p ∈ chosenFamily cs choose, p ⊆ g := by
  intro p hp
  obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hp
  intro e he
  exact (hc c hc').2.2.2 e (List.mem_filter.mp he).1

theorem clauseFamily_cost_positive {k : Nat} (hk : 5 ≤ k) (c : List PlacedLiteral)
    (choose : Cycle → Nat) (hv : ∀ d ∈ clauseFamily k hk c, choose d ∈ d) :
    1 ≤ cost (chosenFamily (clauseFamily k hk c) choose) := by
  unfold chosenFamily
  unfold clauseFamily at hv ⊢
  split at hv
  · next hc =>
      rw [ite_eq_left hc]
      split at hv
      · next h6 =>
          subst k
          simp only [↓reduceIte]
          have hvalid : ∀ d ∈ clauseTwoCycles6, IsCycle (clauseTwoGraph 6) d.length d := by
            intro d hd; have h := clauseTwo6_cycles_valid d hd; simpa only [h.2.1] using h
          obtain ⟨ps,hps,hperm⟩ := vertex_choices_have_options hvalid choose hv
          rw [← hperm.cost_eq]
          exact clauseTwo6_cost_positive ps hps
      · next h6 =>
          rw [ite_eq_right h6,List.map_map]
          exact clauseTwoExpansion_cost_positive hk h6 (fun d => choose (clauseTwoExpansion k hk d))
  · next hc =>
      rw [ite_eq_right hc,List.map_map]
      exact clauseThreeExpansion_cost_positive hk (fun d => choose (clauseThreeExpansion k hk d))

theorem clauseFamily_blocked_lower {k : Nat} (hk : 5 ≤ k) (c : List PlacedLiteral)
    (choose : Cycle → Nat) (hv : ∀ d ∈ clauseFamily k hk c, choose d ∈ d) :
    2 ≤ costWithPorts (chosenFamily (clauseFamily k hk c) choose) (activeClausePorts c) := by
  unfold chosenFamily
  unfold clauseFamily at hv ⊢
  unfold activeClausePorts
  split at hv
  · next hc =>
      simp only [hc,↓reduceIte]
      split at hv
      · next h6 =>
          subst k
          simp only [↓reduceIte]
          have hvalid : ∀ d ∈ clauseTwoCycles6, IsCycle (clauseTwoGraph 6) d.length d := by
            intro d hd; have h := clauseTwo6_cycles_valid d hd; simpa only [h.2.1] using h
          obtain ⟨ps,hps,hperm⟩ := vertex_choices_have_options hvalid choose hv
          have h := clauseTwo6_blocked_lower ps hps
          change 2 ≤ cost (ps.reverse ++ [(0,1),(4,5)].map (fun e => [e])) at h
          rw [← costWithPorts_eq_append ps [(0,1),(4,5)] (by decide),hperm.costWithPorts_eq] at h
          exact h
      · next h6 =>
          rw [ite_eq_right h6,List.map_map]
          exact clauseTwoExpansion_blocked_lower hk h6 (fun d => choose (clauseTwoExpansion k hk d))
  · next hc =>
      simp only [hc,↓reduceIte,List.map_map]
      exact clauseThreeExpansion_blocked_lower hk (fun d => choose (clauseThreeExpansion k hk d))

theorem image_choice_function {α β : Type} (xs : List α) (expand : α → β) (v : α → Nat)
    (hi : ∀ a ∈ xs, ∀ b ∈ xs, expand a = expand b → a = b) :
    ∃ choose : β → Nat, ∀ a ∈ xs, choose (expand a) = v a := by
  classical
  let choose := fun b => if h : ∃ a ∈ xs, expand a = b then v (Classical.choose h) else 0
  refine ⟨choose,?_⟩
  intro a ha
  have h : ∃ d ∈ xs, expand d = expand a := ⟨a,ha,rfl⟩
  have he := hi _ (Classical.choose_spec h).1 a ha (Classical.choose_spec h).2
  simp only [choose,dite_eq_left h,he]

theorem image_choice_for_nodup {α β : Type} (xs : List α) (expand : α → β) (v : α → Nat)
    (hn : (xs.map expand).Nodup) :
    ∃ choose : β → Nat, ∀ a ∈ xs, choose (expand a) = v a :=
  image_choice_function xs expand v (fun _ ha _ hb he => nodup_map_injective_on expand hn ha hb he)

theorem variableFamily_state {k : Nat} (hk : 5 ≤ k) (truth : Bool) :
    ∃ choose : Cycle → Nat, (∀ c ∈ variableFamily k hk, choose c ∈ c) ∧
      chosenFamily (variableFamily k hk) choose = variableExpandedState k hk truth := by
  obtain ⟨choose,hchoose⟩ := image_choice_for_nodup variableSkeletonInputs (variableExpansion k hk)
    (variableStateVertex truth) (distinctCycles_nodup (variableExpansion_distinct hk))
  refine ⟨choose,?_,?_⟩
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    rw [hchoose d hd]
    exact variableExpandedState_valid hk truth d hd
  · unfold chosenFamily variableFamily variableExpandedState
    rw [List.map_map]
    exact List.map_congr_left (fun d hd => congrArg _ (hchoose d hd))

theorem variableFamily_zero_normalizes {k : Nat} (hk : 5 ≤ k) (choose : Cycle → Nat)
    (hz : cost (chosenFamily (variableFamily k hk) choose) = 0) :
    ∃ t : Bool, ∀ e ∈ variablePorts, load (variableExpandedState k hk t) e ≤
      load (chosenFamily (variableFamily k hk) choose) e := by
  unfold chosenFamily variableFamily at hz ⊢
  simp only [List.map_map] at hz ⊢
  exact variableExpansion_zero_normalizes hk (fun c => choose (variableExpansion k hk c)) hz

def clauseTwoWitnessVertex6 (p : Bool) (c : Cycle) : Nat :=
  c[(clauseTwoWitness6 p)[clauseTwoCycles6.idxOf c]!]!

theorem clauseTwoWitnessVertex6_valid : ∀ p : Bool, ∀ c ∈ clauseTwoCycles6,
    clauseTwoWitnessVertex6 p c ∈ c := by decide

theorem clauseTwoWitnessVertex6_cost : ∀ p : Bool,
    cost (chosenFamily clauseTwoCycles6 (clauseTwoWitnessVertex6 p)) = 1 := by decide

theorem clauseTwoWitnessVertex6_avoids : ∀ p : Bool, ∀ c ∈ clauseTwoCycles6,
    (if p then (0,1) else (4,5)) ∉ selectedAt c (clauseTwoWitnessVertex6 p c) := by decide

theorem clauseThreeFamily_witness {k : Nat} (hk : 5 ≤ k) (p : Fin 3) :
    ∃ choose : Cycle → Nat,
      (∀ c ∈ clauseThreeCycles5.map (clauseThreeExpansion k hk), choose c ∈ c) ∧
      cost (chosenFamily (clauseThreeCycles5.map (clauseThreeExpansion k hk)) choose) = 1 ∧
      (∀ i : Fin 3, i ≠ p → ∀ c ∈ clauseThreeCycles5.map (clauseThreeExpansion k hk),
        clauseThreePorts5[i.val]! ∉ selectedAt c (choose c)) := by
  obtain ⟨choose,hchoose⟩ := image_choice_for_nodup clauseThreeCycles5 (clauseThreeExpansion k hk)
    (clauseThreeWitnessVertex p) (distinctCycles_nodup (clauseThreeExpansion_distinct hk))
  refine ⟨choose,?_,?_,?_⟩
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    rw [hchoose d hd]
    exact clauseThreeExpansion_witness_valid hk p d hd
  · have he : chosenFamily (clauseThreeCycles5.map (clauseThreeExpansion k hk)) choose =
        clauseThreeCycles5.map (fun d => selectedAt (clauseThreeExpansion k hk d) (clauseThreeWitnessVertex p d)) := by
      unfold chosenFamily
      rw [List.map_map]
      exact List.map_congr_left (fun d hd => congrArg _ (hchoose d hd))
    rw [he]
    exact clauseThreeExpansion_witness_cost hk p
  · intro i hi c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    rw [hchoose d hd]
    exact clauseThreeExpansion_witness_avoids hk p i hi d hd

theorem clauseTwoFamily_witness {k : Nat} (hk : 5 ≤ k) (h6 : k ≠ 6) (p : Bool) :
    ∃ choose : Cycle → Nat,
      (∀ c ∈ clauseTwoCycles5.map (clauseTwoExpansion k hk), choose c ∈ c) ∧
      cost (chosenFamily (clauseTwoCycles5.map (clauseTwoExpansion k hk)) choose) = 1 ∧
      (∀ c ∈ clauseTwoCycles5.map (clauseTwoExpansion k hk),
        (if p then (0,1) else (4,5)) ∉ selectedAt c (choose c)) := by
  obtain ⟨choose,hchoose⟩ := image_choice_for_nodup clauseTwoCycles5 (clauseTwoExpansion k hk)
    (clauseTwoWitnessVertex p) (distinctCycles_nodup (clauseTwoExpansion_distinct hk))
  refine ⟨choose,?_,?_,?_⟩
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    rw [hchoose d hd]
    exact clauseTwoExpansion_witness_valid hk p d hd
  · have he : chosenFamily (clauseTwoCycles5.map (clauseTwoExpansion k hk)) choose =
        clauseTwoCycles5.map (fun d => selectedAt (clauseTwoExpansion k hk d) (clauseTwoWitnessVertex p d)) := by
      unfold chosenFamily
      rw [List.map_map]
      exact List.map_congr_left (fun d hd => congrArg _ (hchoose d hd))
    rw [he]
    exact clauseTwoExpansion_witness_cost hk h6 p
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    rw [hchoose d hd]
    exact clauseTwoExpansion_witness_avoids hk h6 p d hd

end STACS2027
