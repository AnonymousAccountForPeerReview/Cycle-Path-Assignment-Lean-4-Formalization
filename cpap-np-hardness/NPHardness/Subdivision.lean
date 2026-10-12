module

public import NPHardness.CycleStructure

/-!
One-edge subdivision, with a fresh internal vertex. All graph membership,
freshness, and endpoint-identification hypotheses are explicit.
-/

@[expose] public section
namespace STACS2027

def FreshVertex (g : Graph) (z : Nat) : Prop :=
  ∀ a b, edge a b ∈ g → a ≠ z ∧ b ≠ z

def subdivideOnce (g : Graph) (a b z : Nat) : Graph :=
  edge a z :: edge z b :: g.filter (fun e => e != edge a b)

theorem mem_subdivideOnce {g : Graph} {a b z : Nat} {e : Edge} :
    e ∈ subdivideOnce g a b z ↔
      e = edge a z ∨ e = edge z b ∨ (e ∈ g ∧ e ≠ edge a b) := by
  simp [subdivideOnce]

theorem cycleEdges_endpoints {c : Cycle} {e : Edge} (he : e ∈ cycleEdges c) :
    e.1 ∈ c ∧ e.2 ∈ c := by
  have h := pathEdges_endpoints he
  have hs : ∀ v ∈ c ++ c.take 1, v ∈ c := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hv
    · exact List.mem_of_mem_take hv
  exact ⟨hs _ h.1, hs _ h.2⟩

theorem cycleEdge_vertices {c : Cycle} {a b : Nat} (he : edge a b ∈ cycleEdges c) :
    a ∈ c ∧ b ∈ c := by
  have h := cycleEdges_endpoints he
  by_cases hab : a ≤ b
  · simpa [edge, Nat.min_eq_left hab, Nat.max_eq_right hab] using h
  · have hba : b ≤ a := by omega
    simpa [edge, Nat.min_eq_right hba, Nat.max_eq_left hba, and_comm] using h

theorem FreshVertex.not_mem_cycle {g : Graph} {z k : Nat} {c : Cycle}
    (hz : FreshVertex g z) (hc : IsCycle g k c) : z ∉ c := by
  intro hm
  obtain ⟨w, _, he⟩ := hc.vertex_incident hm
  exact (hz z w (hc.2.2.2 _ he)).1 rfl

theorem subdivideOnce_neighbor {g : Graph} {a b z w : Nat}
    (hz : FreshVertex g z) (he : edge z w ∈ subdivideOnce g a b z) : w = a ∨ w = b := by
  rcases mem_subdivideOnce.mp he with he | he | ⟨he, _⟩
  · rw [edge_comm a z, edge_left_inj] at he
    exact Or.inl he
  · exact Or.inr ((edge_left_inj z w b).mp he)
  · exact False.elim ((hz z w he).1 rfl)

theorem subdivideOnce_old_edge_absent {g : Graph} {a b z : Nat}
    (hz : FreshVertex g z) (he : edge a b ∈ g) :
    edge a b ∉ subdivideOnce g a b z := by
  obtain ⟨ha, hb⟩ := hz a b he
  intro h
  rcases mem_subdivideOnce.mp h with h | h | ⟨_, h⟩
  · exact hb ((edge_left_inj a b z).mp h)
  · rw [edge_comm z b, edge_comm a b, edge_left_inj] at h
    exact ha h
  · exact h rfl

theorem subdivideOnce_old_of_avoids {g : Graph} {a b z k : Nat} {c : Cycle}
    (hc : IsCycle (subdivideOnce g a b z) k c) (hz : z ∉ c) : IsCycle g k c := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
  intro e he
  rcases mem_subdivideOnce.mp (hc.2.2.2 e he) with rfl | rfl | ⟨hg, _⟩
  · exact False.elim (hz (cycleEdge_vertices he).2)
  · exact False.elim (hz (cycleEdge_vertices he).1)
  · exact hg

/-- The edge set before/after removing the leading subdivision vertex. -/
theorem cycleEdges_leading (z u v : Nat) (middle : List Nat) :
    cycleEdges (z :: u :: (middle ++ [v])) =
      edge z u :: (pathEdges (u :: (middle ++ [v])) ++ [edge v z]) := by
  change cycleEdges (z :: ((u :: middle) ++ [v])) = _
  rw [cycleEdges_snoc]
  rfl

theorem IsCycle.rotate_to_edge {g : Graph} {k a b : Nat} {c : Cycle}
    (hc : IsCycle g k c) (he : edge a b ∈ cycleEdges c) :
    ∃ rest, IsCycle g k (a :: b :: rest) ∧ SameCycle c (a :: b :: rest) := by
  obtain ⟨tail, hr, hs, _⟩ := hc.rotate_to_vertex (cycleEdge_vertices he).1
  have hk := hr.1
  have hl := hr.2.1
  cases tail with
  | nil => simp at hl; omega
  | cons u tail =>
    obtain h | ⟨middle, v, h⟩ := List.eq_nil_or_concat tail
    · subst tail; simp at hl; omega
    · simp only [List.concat_eq_append] at h
      subst tail
      have hrot := hs.1 _ he
      rw [cycleEdges_leading] at hrot
      rcases List.mem_cons.mp hrot with hfirst | hrest
      · have hbu := (edge_left_inj a b u).mp hfirst
        subst u
        exact ⟨middle ++ [v], hr, hs⟩
      · rcases List.mem_append.mp hrest with hmiddle | hlast
        · have hm := (pathEdge_vertices hmiddle).1
          exact False.elim ((List.nodup_cons.mp hr.2.2.1).1 hm)
        · have hlast : edge a b = edge v a := by simpa using hlast
          rw [edge_comm v a, edge_left_inj] at hlast
          subst v
          refine ⟨middle.reverse ++ [u], ?_, ?_⟩
          · simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using hr.reverse_tail
          · have h := hs.trans (sameCycle_reverse_tail a (u :: (middle ++ [b])))
            simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using h

theorem subdivideOnce_lift_head {g : Graph} {a b z k : Nat} {rest : Cycle}
    (hc : IsCycle g k (a :: b :: rest)) (hz : FreshVertex g z) :
    IsCycle (subdivideOnce g a b z) (k + 1) (a :: z :: b :: rest) := by
  have hn := hc.2.2.1
  have hzn : z ∉ a :: b :: rest := hz.not_mem_cycle hc
  have hzhead : z ≠ a := by intro h; apply hzn; simp [h]
  have hzr : z ∉ b :: rest := fun h => hzn (List.mem_cons_of_mem a h)
  have ha : a ∉ z :: b :: rest := by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact hzhead h.symm
    · exact (List.nodup_cons.mp hn).1 h
  refine ⟨by have := hc.1; omega, ?_, ?_, ?_⟩
  · have h := hc.2.1; simp only [List.length_cons] at h ⊢; omega
  · exact List.nodup_cons.mpr ⟨ha, List.nodup_cons.mpr ⟨hzr, (List.nodup_cons.mp hn).2⟩⟩
  · intro e he
    change e ∈ edge a z :: edge z b :: pathEdges ((b :: rest) ++ [a]) at he
    rcases List.mem_cons.mp he with rfl | he
    · exact mem_subdivideOnce.mpr (Or.inl rfl)
    rcases List.mem_cons.mp he with rfl | he
    · exact mem_subdivideOnce.mpr (Or.inr (Or.inl rfl))
    · have hold : e ∈ cycleEdges (a :: b :: rest) := by
        change e ∈ edge a b :: pathEdges ((b :: rest) ++ [a])
        exact List.mem_cons_of_mem _ he
      have hno : edge a b ∉ pathEdges ((b :: rest) ++ [a]) :=
        (List.nodup_cons.mp hc.edges_nodup).1
      refine mem_subdivideOnce.mpr (Or.inr (Or.inr ⟨hc.2.2.2 _ hold, ?_⟩))
      intro h; subst e; exact hno he

theorem subdivideOnce_preserve_avoiding {g : Graph} {a b z k : Nat} {c : Cycle}
    (hc : IsCycle g k c) (he : edge a b ∉ cycleEdges c) :
    IsCycle (subdivideOnce g a b z) k c := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
  intro e h
  refine mem_subdivideOnce.mpr (Or.inr (Or.inr ⟨hc.2.2.2 _ h, ?_⟩))
  intro h'; subst e; exact he h

/-- A cycle through the new vertex contracts to a genuine simple cycle.
In particular, subdivision cannot turn an edge into a spurious two-cycle. -/
theorem subdivideOnce_contract {g : Graph} {a b z k : Nat} {c : Cycle}
    (he : edge a b ∈ g) (hz : FreshVertex g z)
    (hc : IsCycle (subdivideOnce g a b z) k c) (hzc : z ∈ c) :
    ∃ u v middle,
      edge u v = edge a b ∧
      IsCycle g (k - 1) (u :: (middle ++ [v])) ∧
      SameCycle c (z :: u :: (middle ++ [v])) ∧
      c.Perm (z :: u :: (middle ++ [v])) := by
  obtain ⟨rest, hr, hsame, hperm⟩ := hc.rotate_to_vertex hzc
  have hlen := hr.2.1
  have hk := hr.1
  cases rest with
  | nil => simp at hlen; omega
  | cons u tail =>
    have htail : tail ≠ [] := by intro h; subst tail; simp at hlen; omega
    obtain h | ⟨middle, v, h⟩ := List.eq_nil_or_concat tail
    · exact False.elim (htail h)
    · simp only [List.concat_eq_append] at h
      subst tail
      have hedge1 : edge z u ∈ subdivideOnce g a b z :=
        hr.2.2.2 _ (by simp [cycleEdges_leading])
      have hedge2 : edge z v ∈ subdivideOnce g a b z := by
        rw [edge_comm z v]
        exact hr.2.2.2 _ (by simp [cycleEdges_leading])
      have hu := subdivideOnce_neighbor hz hedge1
      have hv := subdivideOnce_neighbor hz hedge2
      have hn := (List.nodup_cons.mp hr.2.2.1).2
      have huv : u ≠ v := by
        have h := (List.nodup_cons.mp hn).1
        intro heq; apply h; simp [heq]
      have huvEdge : edge u v = edge a b := by
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact False.elim (huv rfl)
        · rfl
        · exact edge_comm _ _
        · exact False.elim (huv rfl)
      have hmid : middle ≠ [] := by
        intro hm
        subst middle
        have hbad : edge u v ∈ subdivideOnce g a b z :=
          hr.2.2.2 _ (by simp [cycleEdges, pathEdges])
        rw [huvEdge] at hbad
        exact subdivideOnce_old_edge_absent hz he hbad
      have hzrest : z ∉ u :: (middle ++ [v]) := (List.nodup_cons.mp hr.2.2.1).1
      refine ⟨u, v, middle, huvEdge, ⟨?_, ?_, hn, ?_⟩, hsame, hperm⟩
      · have hm : 0 < middle.length := List.length_pos_iff.mpr hmid
        simp only [List.length_cons, List.length_append, List.length_nil] at hlen
        omega
      · simp only [List.length_cons, List.length_append, List.length_nil] at hlen ⊢
        omega
      · intro e hec
        rw [cycleEdges_snoc] at hec
        rcases List.mem_append.mp hec with hp | hp
        · have hes : e ∈ subdivideOnce g a b z :=
            hr.2.2.2 _ (by simp [cycleEdges_leading, hp])
          have hsmall : e ∈ cycleEdges (u :: (middle ++ [v])) := by
            rw [cycleEdges_snoc]; simp [hp]
          rcases mem_subdivideOnce.mp hes with rfl | rfl | ⟨h, _⟩
          · exact False.elim (hzrest (cycleEdge_vertices hsmall).2)
          · exact False.elim (hzrest (cycleEdge_vertices hsmall).1)
          · exact h
        · have h : e = edge v u := by simpa using hp
          rw [h, edge_comm v u, huvEdge]
          exact he

end STACS2027
