module

public import NPHardness.PlacedWitnesses

/-! Assignment feasibility depends only on the undirected graph, and is
preserved by injective renaming on its finite vertex support. -/

@[expose] public section
namespace STACS2027

theorem hasAssignment_graph_equiv {g h : Graph}
    (he : ∀ e, e ∈ g ↔ e ∈ h) (k budget : Nat) :
    HasAssignment g k budget ↔ HasAssignment h k budget := by
  have hv : ∀ c ∈ cycles g k, IsCycle h k c :=
    fun c hc => (enumerated_isCycle hc).graph_mono (fun _ hm => (he _).mp hm)
  have hcover : ∀ c, IsCycle h k c → ∃ d ∈ cycles g k, SameCycle c d := by
    intro c hc
    exact isCycle_represented (hc.graph_mono (fun _ hm => (he _).mpr hm))
  exact (hasAssignment_iff_enumerated_family g k budget).trans
    (hasAssignment_iff_complete_family hv (cycles_pairwise_different g k) hcover).symm

theorem hasAssignment_graph_perm {g h : Graph} (hp : g.Perm h) (k budget : Nat) :
    HasAssignment g k budget ↔ HasAssignment h k budget :=
  hasAssignment_graph_equiv (fun _ => hp.mem_iff) k budget

theorem familyAssignment_relabel {g : Graph} {n k budget : Nat} {cs : List Cycle}
    (hb : VerticesBelow g n) (hn : ∀ e ∈ g, edge e.1 e.2 = e)
    (hc : ∀ c ∈ cs, IsCycle g k c)
    (hd : cs.Pairwise (fun c d => ¬ SameCycle c d))
    (t : Nat → Nat) (hi : ∀ a, a < n → ∀ b, b < n → t a = t b → a = b) :
    FamilyAssignment (cs.map (List.map t)) budget ↔ FamilyAssignment cs budget := by
  constructor
  · rintro ⟨choose,hchoose,hcost⟩
    obtain ⟨pick,hpick,_,he⟩ := mapped_choice_cost hb hn hc t hi choose hchoose
    exact ⟨pick,hpick,by change cost (chosenFamily cs pick) ≤ budget; rw [← he]; exact hcost⟩
  · rintro ⟨pick,hpick,hcost⟩
    obtain ⟨choose,hchoose,he⟩ := mapped_choice_push hb hc t hi
      (distinctCycles_nodup (mapped_family_distinct hb hn hc hd t hi)) pick hpick
    refine ⟨choose,hchoose,?_⟩
    change cost (chosenFamily (cs.map (List.map t)) choose) ≤ budget
    rw [he,cost_relabel hb hn t hi (chosenFamily_supported hc pick)]
    exact hcost

theorem hasAssignment_relabel {g : Graph} {n : Nat}
    (hb : VerticesBelow g n) (hn : ∀ e ∈ g, edge e.1 e.2 = e)
    (t : Nat → Nat) (hi : ∀ a, a < n → ∀ b, b < n → t a = t b → a = b)
    (k budget : Nat) : HasAssignment (mapGraph t g) k budget ↔ HasAssignment g k budget := by
  let cs := cycles g k
  have hc : ∀ c ∈ cs, IsCycle g k c := fun _ hm => enumerated_isCycle hm
  have hd := cycles_pairwise_different g k
  have hv : ∀ c ∈ cs.map (List.map t), IsCycle (mapGraph t g) k c := by
    intro c hm
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hm
    exact (hc d hd).map t (fun a ha b hb' he => hi a ((hc d hd).vertex_bound hb a ha)
      b ((hc d hd).vertex_bound hb b hb') he)
  have hcover : ∀ c, IsCycle (mapGraph t g) k c →
      ∃ d ∈ cs.map (List.map t), SameCycle c d := by
    intro c hcm
    obtain ⟨d,hd,rfl⟩ := IsCycle.unmap hb hn t hi hcm
    obtain ⟨e,he,hs⟩ := isCycle_represented hd
    exact ⟨e.map t,List.mem_map.mpr ⟨e,he,rfl⟩,hs.map t⟩
  rw [hasAssignment_iff_complete_family hv (mapped_family_distinct hb hn hc hd t hi) hcover]
  exact (familyAssignment_relabel hb hn hc hd t hi).trans
    (hasAssignment_iff_enumerated_family g k budget).symm

end STACS2027
