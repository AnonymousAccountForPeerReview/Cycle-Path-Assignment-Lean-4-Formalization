module

public import NPHardness.Subdivision

/-! A finite rank certificate for acyclicity, used for the green-edge complement. -/

@[expose] public section
namespace STACS2027

theorem IsCycle.two_neighbors {g : Graph} {k : Nat} {c : Cycle}
    (hc : IsCycle g k c) {v : Nat} (hv : v ∈ c) :
    ∃ a b, a ∈ c ∧ b ∈ c ∧ a ≠ b ∧ edge v a ∈ g ∧ edge v b ∈ g := by
  obtain ⟨tail, hr, _, hp⟩ := hc.rotate_to_vertex hv
  have hk := hr.1
  have hl := hr.2.1
  cases tail with
  | nil => simp at hl; omega
  | cons a tail =>
    obtain h | ⟨middle, b, h⟩ := List.eq_nil_or_concat tail
    · subst tail; simp at hl; omega
    · simp only [List.concat_eq_append] at h
      subst tail
      have hn := (List.nodup_cons.mp (List.nodup_cons.mp hr.2.2.1).2).1
      refine ⟨a, b, hp.symm.subset (by simp), hp.symm.subset (by simp), ?_, ?_, ?_⟩
      · intro h; apply hn; simp [h]
      · exact hr.2.2.2 _ (by simp [cycleEdges_leading])
      · rw [edge_comm v b]
        exact hr.2.2.2 _ (by simp [cycleEdges_leading])

theorem exists_rank_max (rank : Nat → Nat) (vs : List Nat) (hn : vs ≠ []) :
    ∃ v ∈ vs, ∀ w ∈ vs, rank w ≤ rank v := by
  induction vs with
  | nil => exact False.elim (hn rfl)
  | cons v vs ih =>
    by_cases ht : vs = []
    · subst vs; exact ⟨v, by simp, by simp⟩
    · obtain ⟨u, hu, hm⟩ := ih ht
      by_cases h : rank v ≤ rank u
      · refine ⟨u, by simp [hu], ?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact h
        · exact hm w hw
      · refine ⟨v, by simp, ?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · omega
        · have h' := hm w hw; omega

/-- Each vertex has at most one neighbor of no greater rank. -/
def AcyclicRank (g : Graph) (rank : Nat → Nat) : Prop :=
  ∀ v a b, edge v a ∈ g → edge v b ∈ g →
    rank a ≤ rank v → rank b ≤ rank v → a = b

theorem AcyclicRank.no_cycle {g : Graph} {rank : Nat → Nat} (hr : AcyclicRank g rank) :
    ∀ k c, ¬ IsCycle g k c := by
  intro k c hc
  have hn : c ≠ [] := by
    intro he; have hk := hc.1; have hl := hc.2.1; simp [he] at hl; omega
  obtain ⟨v, hv, hm⟩ := exists_rank_max rank c hn
  obtain ⟨a, b, ha, hb, hab, hea, heb⟩ := hc.two_neighbors hv
  exact hab (hr v a b hea heb (hm a ha) (hm b hb))

/-- Vertices of positive rank form trees leading into the rank-zero core. -/
def CycleCoreRank (g : Graph) (rank : Nat → Nat) : Prop :=
  ∀ v a b, rank v ≠ 0 → edge v a ∈ g → edge v b ∈ g →
    rank a ≤ rank v → rank b ≤ rank v → a = b

theorem CycleCoreRank.cycle_zero {g : Graph} {rank : Nat → Nat} (hr : CycleCoreRank g rank)
    {k : Nat} {c : Cycle} (hc : IsCycle g k c) : ∀ v ∈ c, rank v = 0 := by
  have hn : c ≠ [] := by
    intro he; have hk := hc.1; have hl := hc.2.1; simp [he] at hl; omega
  obtain ⟨u, hu, hm⟩ := exists_rank_max rank c hn
  have hz : rank u = 0 := by
    by_cases hz : rank u = 0
    · exact hz
    obtain ⟨a, b, ha, hb, hab, hea, heb⟩ := hc.two_neighbors hu
    exact False.elim (hab (hr u a b hz hea heb (hm a ha) (hm b hb)))
  intro v hv
  have h := hm v hv
  omega

end STACS2027
