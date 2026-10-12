module

public import NPHardness.GlobalSoundness

/-! Uniform choice of a single usable literal port in either clause gadget. -/

@[expose] public section
namespace STACS2027

theorem clauseFamily_witness {k : Nat} (hk : 5 ≤ k) (c : List PlacedLiteral)
    (hc : c.length = 2 ∨ c.length = 3) (i : Nat) (hi : i < c.length) :
    ∃ choose : Cycle → Nat, (∀ d ∈ clauseFamily k hk c, choose d ∈ d) ∧
      cost (chosenFamily (clauseFamily k hk c) choose) = 1 ∧
      (∀ j, j < c.length → j ≠ i → ∀ d ∈ clauseFamily k hk c,
        edge (clauseEndpoint j false) (clauseEndpoint j true) ∉ selectedAt d (choose d)) := by
  rcases hc with hc | hc
  · have hi2 : i = 0 ∨ i = 1 := by omega
    have hwitness : ∀ p : Bool, ∃ choose : Cycle → Nat,
        (∀ d ∈ clauseFamily k hk c, choose d ∈ d) ∧
        cost (chosenFamily (clauseFamily k hk c) choose) = 1 ∧
        (∀ d ∈ clauseFamily k hk c, (if p then (0,1) else (4,5)) ∉ selectedAt d (choose d)) := by
      intro p
      unfold clauseFamily
      rw [ite_eq_left hc]
      by_cases h6 : k = 6
      · subst k
        simp only [↓reduceIte]
        exact ⟨clauseTwoWitnessVertex6 p,clauseTwoWitnessVertex6_valid p,
          clauseTwoWitnessVertex6_cost p,clauseTwoWitnessVertex6_avoids p⟩
      · rw [ite_eq_right h6]
        exact clauseTwoFamily_witness hk h6 p
    rcases hi2 with rfl | rfl
    · obtain ⟨choose,hv,hcost,havoid⟩ := hwitness false
      refine ⟨choose,hv,hcost,?_⟩
      intro j hj hji d hd
      have he : j = 1 := by omega
      subst j
      exact havoid d hd
    · obtain ⟨choose,hv,hcost,havoid⟩ := hwitness true
      refine ⟨choose,hv,hcost,?_⟩
      intro j hj hji d hd
      have he : j = 0 := by omega
      subst j
      exact havoid d hd
  · have hi3 : i < 3 := by omega
    obtain ⟨choose,hv,hcost,havoid⟩ := clauseThreeFamily_witness hk ⟨i,hi3⟩
    have hfamily : clauseFamily k hk c = clauseThreeCycles5.map (clauseThreeExpansion k hk) := by
      simp [clauseFamily,hc]
    rw [hfamily]
    refine ⟨choose,hv,hcost,?_⟩
    intro j hj hji d hd
    have hj3 : j < 3 := by omega
    have he : edge (clauseEndpoint j false) (clauseEndpoint j true) = clauseThreePorts5[j]! :=
      (by decide : ∀ j : Fin 3, edge (clauseEndpoint j.val false) (clauseEndpoint j.val true) = clauseThreePorts5[j.val]!) ⟨j,hj3⟩
    rw [he]
    exact havoid ⟨j,hj3⟩ (fun h => hji (congrArg Fin.val h)) d hd

theorem load_zero_of_port_avoided {cs : List Cycle} {choose : Cycle → Nat} {e : Edge}
    (h : ∀ c ∈ cs, e ∉ selectedAt c (choose c)) : load (chosenFamily cs choose) e = 0 := by
  apply (load_zero_iff _ _).mpr
  intro p hp
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
  exact h c hc

end STACS2027
