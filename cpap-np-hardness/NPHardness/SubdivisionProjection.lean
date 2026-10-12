module

public import NPHardness.Subdivision

/-! Exact cycle edge-set projection through a one-edge subdivision. -/

@[expose] public section
namespace STACS2027

def splitEdge (a b z : Nat) (e : Edge) : List Edge :=
  if e = edge a b then [edge a z, edge z b] else [e]

def liftEdges (a b z : Nat) (es : List Edge) : List Edge :=
  es.flatMap (splitEdge a b z)

theorem mem_liftEdges {a b z : Nat} {es : List Edge} {e : Edge} :
    e ∈ liftEdges a b z es ↔
      (e ∈ es ∧ e ≠ edge a b) ∨
      (edge a b ∈ es ∧ (e = edge a z ∨ e = edge z b)) := by
  constructor
  · intro h
    obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp h
    by_cases hsplit : d = edge a b
    · subst d
      exact Or.inr ⟨hd, by simpa [splitEdge] using he⟩
    · have heq : e = d := by simpa [splitEdge, hsplit] using he
      subst e
      exact Or.inl ⟨hd, hsplit⟩
  · rintro (⟨he, hne⟩ | ⟨ho, he⟩)
    · exact List.mem_flatMap.mpr ⟨e, he, by simp [splitEdge, hne]⟩
    · exact List.mem_flatMap.mpr ⟨edge a b, ho, by simpa [splitEdge] using he⟩

theorem liftEdges_of_absent (a b z : Nat) (es : List Edge) (h : edge a b ∉ es) :
    liftEdges a b z es = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he : e ≠ edge a b := by intro he; apply h; simp [he]
    have ht : edge a b ∉ es := fun hm => h (List.mem_cons_of_mem e hm)
    change splitEdge a b z e ++ liftEdges a b z es = e :: es
    simp [splitEdge, he, ih ht]

theorem FreshVertex.edge_left_absent {g : Graph} {z : Nat} (hz : FreshVertex g z) (a : Nat) :
    edge a z ∉ g := fun h => (hz a z h).2 rfl

theorem FreshVertex.edge_right_absent {g : Graph} {z : Nat} (hz : FreshVertex g z) (b : Nat) :
    edge z b ∉ g := fun h => (hz z b h).1 rfl

theorem liftEdges_nodup {g : Graph} {a b z : Nat} {es : List Edge}
    (hab : a ≠ b) (hz : FreshVertex g z) (hn : es.Nodup) (hs : ∀ e ∈ es, e ∈ g) :
    (liftEdges a b z es).Nodup := by
  induction es with
  | nil => simp [liftEdges]
  | cons e es ih =>
    obtain ⟨he, ht⟩ := List.nodup_cons.mp hn
    have heg : e ∈ g := hs e (by simp)
    have hsg : ∀ d ∈ es, d ∈ g := fun d hd => hs d (by simp [hd])
    have hit := ih ht hsg
    by_cases h : e = edge a b
    · subst e
      have habz : edge a z ≠ edge z b := by
        intro h
        rw [edge_comm a z, edge_left_inj] at h
        exact hab h
      rw [liftEdges, List.flatMap_cons]
      simp only [splitEdge, ↓reduceIte]
      change ([edge a z, edge z b] ++ liftEdges a b z es).Nodup
      rw [liftEdges_of_absent a b z es he]
      simp only [List.cons_append, List.nil_append, List.nodup_cons]
      refine ⟨?_, ?_, ht⟩
      · intro hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact habz hm
        · exact hz.edge_left_absent a (hsg _ hm)
      · intro hm; exact hz.edge_right_absent b (hsg _ hm)
    · simp only [liftEdges, List.flatMap_cons, splitEdge, h, ↓reduceIte,
        List.singleton_append]
      apply List.nodup_cons.mpr
      refine ⟨?_, hit⟩
      intro hm
      rcases mem_liftEdges.mp hm with ⟨hm, _⟩ | ⟨_, hm | hm⟩
      · exact he hm
      · exact hz.edge_left_absent a (hm ▸ heg)
      · exact hz.edge_right_absent b (hm ▸ heg)

theorem IsCycle.edge_length {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) :
    (cycleEdges c).length = k := by
  have hk := hc.1
  simp only [cycleEdges, pathEdges_length, List.length_append, List.length_take, hc.2.1]
  omega

theorem SameCycle.edge_perm {g h : Graph} {k l : Nat} {c d : Cycle}
    (hc : IsCycle g k c) (hd : IsCycle h l d) (he : SameCycle c d) :
    (cycleEdges c).Perm (cycleEdges d) := by
  apply (List.perm_ext_iff_of_nodup hc.edges_nodup hd.edges_nodup).mpr
  intro e
  exact ⟨he.1 e, he.2 e⟩

theorem liftEdges_contract_membership {g : Graph} {a b z u v : Nat} {middle : Cycle}
    (he : edge u v = edge a b)
    (hd : IsCycle g (u :: (middle ++ [v])).length (u :: (middle ++ [v]))) :
    ∀ e, e ∈ cycleEdges (z :: u :: (middle ++ [v])) ↔
      e ∈ liftEdges a b z (cycleEdges (u :: (middle ++ [v]))) := by
  have hother : edge a b ∉ pathEdges (u :: (middle ++ [v])) := by
    have h := hd.edges_nodup
    rw [cycleEdges_snoc] at h
    have hne := (List.nodup_append.mp h).2.2
    intro hm
    exact hne _ hm _ (by simp) (he.symm.trans (edge_comm u v))
  intro e
  rw [cycleEdges_leading, mem_liftEdges, cycleEdges_snoc]
  have hlast : edge v u = edge a b := (edge_comm v u).trans he
  have hnew : edge z u = edge a z ∧ edge v z = edge z b ∨
      edge z u = edge z b ∧ edge v z = edge a z := by
    rcases (edge_eq_iff u v a b).mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨edge_comm _ _, edge_comm _ _⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hmem : ∀ e ∈ pathEdges (u :: (middle ++ [v])), e ≠ edge a b := by
    intro e hm heq; subst e; exact hother hm
  rcases hnew with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    by_cases hp : e ∈ pathEdges (u :: (middle ++ [v]))
  · simp [hp, hlast, h1, h2, hmem e hp]
  · simp [hp, hlast, h1, h2, or_comm]
  · simp [hp, hlast, h1, h2, hmem e hp]
  · simp [hp, hlast, h1, h2, or_comm]

/-- Every cycle after subdivision is the edgewise expansion of a base cycle. -/
theorem subdivideOnce_cycle_projection {g : Graph} {a b z k : Nat} {c : Cycle}
    (hab : a ≠ b) (he : edge a b ∈ g) (hz : FreshVertex g z)
    (hc : IsCycle (subdivideOnce g a b z) k c) :
    ∃ l d, IsCycle g l d ∧ (cycleEdges c).Perm (liftEdges a b z (cycleEdges d)) := by
  by_cases hzc : z ∈ c
  · obtain ⟨u, v, middle, huv, hd, hs, _⟩ := subdivideOnce_contract he hz hc hzc
    refine ⟨k - 1, u :: (middle ++ [v]), hd, ?_⟩
    apply (List.perm_ext_iff_of_nodup hc.edges_nodup
      (liftEdges_nodup hab hz hd.edges_nodup hd.2.2.2)).mpr
    intro e
    have hd' : IsCycle g (u :: (middle ++ [v])).length (u :: (middle ++ [v])) := by
      simpa only [hd.2.1] using hd
    exact (Iff.intro (hs.1 e) (hs.2 e)).trans
      (liftEdges_contract_membership huv hd' e)
  · have hd := subdivideOnce_old_of_avoids hc hzc
    refine ⟨k, c, hd, ?_⟩
    have ha : edge a b ∉ cycleEdges c := fun h => subdivideOnce_old_edge_absent hz he (hc.2.2.2 _ h)
    rw [liftEdges_of_absent a b z (cycleEdges c) ha]

/-- Every base cycle expands to a cycle with precisely the expanded edge set. -/
theorem subdivideOnce_cycle_lift {g : Graph} {a b z k : Nat} {c : Cycle}
    (hc : IsCycle g k c) (hz : FreshVertex g z) :
    ∃ l d, IsCycle (subdivideOnce g a b z) l d ∧
      (cycleEdges d).Perm (liftEdges a b z (cycleEdges c)) := by
  by_cases he : edge a b ∈ cycleEdges c
  · obtain ⟨rest, hr, hs⟩ := hc.rotate_to_edge he
    have hn := hr.edges_nodup
    have hnot : edge a b ∉ pathEdges ((b :: rest) ++ [a]) := (List.nodup_cons.mp hn).1
    refine ⟨k + 1, a :: z :: b :: rest, subdivideOnce_lift_head hr hz, ?_⟩
    have hEq : cycleEdges (a :: z :: b :: rest) =
        liftEdges a b z (cycleEdges (a :: b :: rest)) := by
      change edge a z :: edge z b :: pathEdges ((b :: rest) ++ [a]) =
        splitEdge a b z (edge a b) ++ liftEdges a b z (pathEdges ((b :: rest) ++ [a]))
      rw [liftEdges_of_absent a b z _ hnot]
      simp [splitEdge]
    rw [hEq]
    exact (hs.edge_perm hc hr).symm.flatMap_right (splitEdge a b z)
  · refine ⟨k, c, subdivideOnce_preserve_avoiding hc he, ?_⟩
    rw [liftEdges_of_absent a b z _ he]

end STACS2027
