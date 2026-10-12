module

public import MinorFree.FourCycles

/-!
Algorithm 4 and Lemma 25: on a graph with a degree-two elimination order
(every vertex has at most two neighbours later in the order, as the vertices
deleted by Algorithm 4) in which two distinct vertices have at most two common
neighbours (Lemma 24), assigning every four-cycle to the two edges at its
earliest vertex is a perfect cycle-path assignment.
-/

@[expose] public section
namespace STACS2027

/-- `rank` is a degree-two elimination order of `g`: it is injective, and every vertex has at
most two neighbours of larger rank. The order in which Algorithm 4 deletes the vertices of an
outerplanar graph (each of degree at most two at its deletion) is such an order. -/
def EliminationOrder (g : Graph) (rank : Nat → Nat) : Prop :=
  (∀ a b, rank a = rank b → a = b) ∧
  ∀ v a b c, edge v a ∈ g → edge v b ∈ g → edge v c ∈ g →
    rank v < rank a → rank v < rank b → rank v < rank c → a = b ∨ a = c ∨ b = c

/-- Lemma 24's conclusion for `g`: two distinct vertices have at most two common neighbours
(as in every `K_{2,3}`-minor-free graph). -/
def CommonNeighbourBound (g : Graph) : Prop :=
  ∀ u w a b c, u ≠ w → edge u a ∈ g → edge w a ∈ g → edge u b ∈ g → edge w b ∈ g →
    edge u c ∈ g → edge w c ∈ g → a = b ∨ a = c ∨ b = c

/-- The position in `c` of its vertex of minimum rank (the first such position). -/
def earliestIndex (rank : Nat → Nat) : List Nat → Nat
  | [] => 0
  | a :: tail =>
    match tail with
    | [] => 0
    | b :: rest =>
      if rank a ≤ rank ((b :: rest)[earliestIndex rank (b :: rest)]?.getD a) then 0
      else earliestIndex rank (b :: rest) + 1

/-- Algorithm 4's assignment: every four-cycle receives the two edges at its earliest vertex,
the path omitting the vertex opposite to it. -/
def algorithm4 (rank : Nat → Nat) (g : Graph) : List (List Edge) :=
  (cycles g 4).map fun c => selected c ((earliestIndex rank c + 2) % 4)

theorem earliestIndex_spec (rank : Nat → Nat) (c : List Nat) (hc : c ≠ []) :
    earliestIndex rank c < c.length ∧
      ∀ j, (hj : j < c.length) → ∀ v, c[earliestIndex rank c]? = some v → rank v ≤ rank c[j] := by
  induction c with
  | nil => exact absurd rfl hc
  | cons a rest ih =>
    cases rest with
    | nil =>
      refine ⟨by simp [earliestIndex], ?_⟩
      intro j hj v hv
      simp only [List.length_cons, List.length_nil] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp [earliestIndex] at hv
      subst hv
      exact Nat.le_refl _
    | cons b rest =>
      obtain ⟨hlt, hmin⟩ := ih (by simp)
      simp only [List.length_cons] at hlt
      obtain ⟨m, hm⟩ : ∃ m, (b :: rest)[earliestIndex rank (b :: rest)]? = some m :=
        ⟨_, List.getElem?_eq_getElem (by simp only [List.length_cons]; omega)⟩
      simp only [earliestIndex, hm, Option.getD_some]
      by_cases hle : rank a ≤ rank m
      · simp only [hle, ↓reduceIte]
        refine ⟨by simp, ?_⟩
        intro j hj v hv
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
        subst hv
        cases j with
        | zero => exact Nat.le_refl _
        | succ j =>
          simp only [List.length_cons] at hj
          have := hmin j (by simp only [List.length_cons]; omega) m hm
          simp only [List.getElem_cons_succ]
          exact Nat.le_trans hle this
      · simp only [hle, ↓reduceIte]
        refine ⟨by simp only [List.length_cons]; omega, ?_⟩
        intro j hj v hv
        simp only [List.getElem?_cons_succ] at hv
        rw [hm] at hv
        simp only [Option.some.injEq] at hv
        subst hv
        cases j with
        | zero => exact Nat.le_of_lt (Nat.lt_of_not_le hle)
        | succ j =>
          simp only [List.length_cons] at hj
          simp only [List.getElem_cons_succ]
          exact hmin j (by simp only [List.length_cons]; omega) _ hm

/-- A four-cycle of `g`, seen from its earliest vertex `v`: vertices `v, u, x, w`, edges
`vu, ux, xw, wv`, `v` strictly earliest, and Algorithm 4's path for it is `{wv, vu}`. -/
structure EarliestView (g : Graph) (rank : Nat → Nat) (c : Cycle) (v u x w : Nat) : Prop where
  mem : ∀ y, y ∈ c ↔ y = v ∨ y = u ∨ y = x ∨ y = w
  edges : ∀ e, e ∈ cycleEdges c ↔ e = edge v u ∨ e = edge u x ∨ e = edge x w ∨ e = edge w v
  path : ∀ e, e ∈ selected c ((earliestIndex rank c + 2) % 4) ↔ e = edge v u ∨ e = edge w v
  distinct : v ≠ u ∧ v ≠ x ∧ v ≠ w ∧ u ≠ x ∧ u ≠ w ∧ x ≠ w
  inGraph : edge v u ∈ g ∧ edge u x ∈ g ∧ edge x w ∈ g ∧ edge w v ∈ g
  earliest : rank v < rank u ∧ rank v < rank x ∧ rank v < rank w

theorem earliestView {g : Graph} {rank : Nat → Nat} (hinj : ∀ a b, rank a = rank b → a = b)
    {c : Cycle} (hc : IsCycle g 4 c) : ∃ v u x w, EarliestView g rank c v u x w := by
  have hl := hc.2.1
  have hne : c ≠ [] := by intro h; subst h; simp at hl
  obtain ⟨hi, hmin⟩ := earliestIndex_spec rank c hne
  rw [hl] at hi
  obtain ⟨v, u, x, w, hrot, hv, hx⟩ := four_cycle_rotation hl hi
  have hr : IsCycle g 4 [v, u, x, w] := hrot ▸ hc.rotation _
  have hs : SameCycle c [v, u, x, w] := hrot ▸ sameCycle_rotation c _
  have hd := nodup_four hr.2.2.1
  have hmem : ∀ y, y ∈ c ↔ y = v ∨ y = u ∨ y = x ∨ y = w := by
    intro y
    rw [hs.vertices hc hr y]
    simp
  have hedges : ∀ e, e ∈ cycleEdges c ↔ e = edge v u ∨ e = edge u x ∨ e = edge x w ∨ e = edge w v := by
    intro e
    rw [← mem_cycleEdges_four]
    exact ⟨hs.1 e, hs.2 e⟩
  have hx' : (earliestIndex rank c + 2) % 4 < c.length := by rw [hl]; exact Nat.mod_lt _ (by decide)
  have hpath : ∀ e, e ∈ selected c ((earliestIndex rank c + 2) % 4) ↔ e = edge v u ∨ e = edge w v := by
    intro e
    rw [(selected_perm_selectedAt hc hx').mem_iff]
    have hcx : c[(earliestIndex rank c + 2) % 4] = x := by
      have := List.getElem?_eq_getElem hx'
      rw [this] at hx
      exact Option.some.inj hx
    rw [hcx, (hs.selectedAt_perm hc hr x).mem_iff]
    exact mem_selectedAt_four hd.2.1 hd.2.2.2.1 (Ne.symm hd.2.2.2.2.2) e
  have hin : edge v u ∈ g ∧ edge u x ∈ g ∧ edge x w ∈ g ∧ edge w v ∈ g :=
    ⟨hr.2.2.2 _ (by simp [cycleEdges_four]), hr.2.2.2 _ (by simp [cycleEdges_four]),
      hr.2.2.2 _ (by simp [cycleEdges_four]), hr.2.2.2 _ (by simp [cycleEdges_four])⟩
  have hle : ∀ y ∈ c, rank v ≤ rank y := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    exact hmin j hj v hv
  have hlt : ∀ y ∈ c, y ≠ v → rank v < rank y := by
    intro y hy hne
    exact Nat.lt_of_le_of_ne (hle y hy) (fun h => hne (hinj _ _ h.symm))
  refine ⟨v, u, x, w, ⟨hmem, hedges, hpath, hd, hin, ?_⟩⟩
  exact ⟨hlt u ((hmem u).mpr (by simp)) hd.1.symm, hlt x ((hmem x).mpr (by simp)) hd.2.1.symm,
    hlt w ((hmem w).mpr (by simp)) hd.2.2.1.symm⟩

/-- Two distinct four-cycles receive edge-disjoint paths from Algorithm 4. -/
theorem algorithm4_disjoint {g : Graph} {rank : Nat → Nat} (ho : EliminationOrder g rank)
    (hb : CommonNeighbourBound g) {c d : Cycle} (hc : IsCycle g 4 c) (hd : IsCycle g 4 d)
    (hne : ¬ SameCycle c d) :
    overlap (selected c ((earliestIndex rank c + 2) % 4))
      (selected d ((earliestIndex rank d + 2) % 4)) = 0 := by
  apply overlap_eq_zero_of_disjoint
  intro e hec hed
  obtain ⟨v, u, x, w, Hc⟩ := earliestView ho.1 hc
  obtain ⟨v', u', x', w', Hd⟩ := earliestView ho.1 hd
  obtain ⟨hvu, hvx, hvw, hux, huw, hxw⟩ := Hc.distinct
  obtain ⟨hvu', hvx', hvw', hux', huw', hxw'⟩ := Hd.distinct
  obtain ⟨gvu, gux, gxw, gwv⟩ := Hc.inGraph
  obtain ⟨gvu', gux', gxw', gwv'⟩ := Hd.inGraph
  obtain ⟨rvu, rvx, rvw⟩ := Hc.earliest
  obtain ⟨rvu', rvx', rvw'⟩ := Hd.earliest
  -- The shared edge is `edge v y` with `y ∈ {u, w}` and `edge v' y'` with `y' ∈ {u', w'}`.
  have hvy : ∃ y, (y = u ∨ y = w) ∧ e = edge v y := by
    rcases (Hc.path e).mp hec with rfl | rfl
    · exact ⟨u, Or.inl rfl, rfl⟩
    · exact ⟨w, Or.inr rfl, edge_comm w v⟩
  have hvy' : ∃ y', (y' = u' ∨ y' = w') ∧ e = edge v' y' := by
    rcases (Hd.path e).mp hed with rfl | rfl
    · exact ⟨u', Or.inl rfl, rfl⟩
    · exact ⟨w', Or.inr rfl, edge_comm w' v'⟩
  obtain ⟨y, hy, rfl⟩ := hvy
  obtain ⟨y', hy', he⟩ := hvy'
  have hy_in : y ∈ c := (Hc.mem y).mpr (by rcases hy with rfl | rfl <;> simp)
  have hy'_in : y' ∈ d := (Hd.mem y').mpr (by rcases hy' with rfl | rfl <;> simp)
  have hyv : y ≠ v := by rcases hy with rfl | rfl <;> omega
  have hy'v' : y' ≠ v' := by rcases hy' with rfl | rfl <;> omega
  have hry : rank v < rank y := by rcases hy with rfl | rfl <;> assumption
  have hry' : rank v' < rank y' := by rcases hy' with rfl | rfl <;> assumption
  rcases (edge_eq_iff v y v' y').mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- Same earliest vertex `v`: `u, w, u', w'` are later neighbours of `v`, so `{u', w'} = {u, w}`.
    have h1 := ho.2 v u w u' gvu (edge_comm v w ▸ gwv) gvu' rvu rvw rvu'
    have h2 := ho.2 v u w w' gvu (edge_comm v w ▸ gwv) (edge_comm v w' ▸ gwv') rvu rvw rvw'
    have hset : (u' = u ∧ w' = w) ∨ (u' = w ∧ w' = u) := by
      rcases h1 with h1 | h1 | h1
      · exact absurd h1 huw
      · rcases h2 with h2 | h2 | h2
        · exact absurd h2 huw
        · exact absurd (h1.symm.trans h2) huw'
        · exact Or.inl ⟨h1.symm, h2.symm⟩
      · rcases h2 with h2 | h2 | h2
        · exact absurd h2 huw
        · exact Or.inr ⟨h1.symm, h2.symm⟩
        · exact absurd (h1.symm.trans h2) huw'
    -- `x` and `x'` are both common neighbours of `u` and `w`, other than `v`; so `x = x'`.
    have hxx : x = x' := by
      have gux'' : edge u x' ∈ g := by
        rcases hset with ⟨h1, _⟩ | ⟨_, h2⟩
        · rw [← h1]; exact gux'
        · rw [edge_comm, ← h2]; exact gxw'
      have gwx'' : edge w x' ∈ g := by
        rcases hset with ⟨_, h2⟩ | ⟨h1, _⟩
        · rw [edge_comm, ← h2]; exact gxw'
        · rw [← h1]; exact gux'
      have h := hb u w v x x' huw (edge_comm u v ▸ gvu) (edge_comm w v ▸ gwv) gux
        (edge_comm w x ▸ gxw) gux'' gwx''
      rcases h with h | h | h
      · exact absurd h hvx
      · exact absurd h hvx'
      · exact h
    subst hxx
    -- Then `c` and `d` have the same edges.
    apply hne
    have key : ∀ e, (e = edge v u ∨ e = edge u x ∨ e = edge x w ∨ e = edge w v) ↔
        (e = edge v u' ∨ e = edge u' x ∨ e = edge x w' ∨ e = edge w' v) := by
      intro e
      rcases hset with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, edge_comm v w, edge_comm w x, edge_comm x u, edge_comm u v]
        constructor <;> rintro (h | h | h | h) <;> simp [h]
    exact ⟨fun e he => (Hd.edges e).mpr ((key e).mp ((Hc.edges e).mp he)),
      fun e he => (Hc.edges e).mpr ((key e).mpr ((Hd.edges e).mp he))⟩
  · -- `v' = y` is a later vertex of `c` and `v = y'` a later vertex of `d`: impossible.
    have h1 : rank v < rank y := hry
    have h2 : rank y < rank v := by
      have := Hd.earliest
      rcases hy' with rfl | rfl <;> omega
    omega

/-- Algorithm 4's assignment chooses an option for every four-cycle. -/
theorem algorithm4_valid (rank : Nat → Nat) (g : Graph) :
    ValidChoices ((cycles g 4).map selectedOptions) (algorithm4 rank g) := by
  unfold algorithm4
  have h : ∀ c ∈ cycles g 4, selected c ((earliestIndex rank c + 2) % 4) ∈ selectedOptions c := by
    intro c hc
    have hl := (enumerated_isCycle hc).2.1
    apply List.mem_map.mpr
    refine ⟨(earliestIndex rank c + 2) % 4, List.mem_range.mpr ?_, rfl⟩
    rw [hl]; exact Nat.mod_lt _ (by decide)
  generalize hcs : cycles g 4 = cs at h ⊢
  clear hcs
  induction cs with
  | nil => trivial
  | cons c cs ih => exact ⟨h c (by simp), ih (fun d hd => h d (by simp [hd]))⟩

/-- Algorithm 4's assignment is perfect. -/
theorem algorithm4_cost {g : Graph} {rank : Nat → Nat} (ho : EliminationOrder g rank)
    (hb : CommonNeighbourBound g) : cost (algorithm4 rank g) = 0 := by
  apply cost_eq_zero_of_pairwise
  unfold algorithm4
  rw [List.pairwise_map]
  apply (cycles_pairwise_different g 4).imp_of_mem
  intro c d hc hd hne
  exact algorithm4_disjoint ho hb (enumerated_isCycle hc) (enumerated_isCycle hd) hne

/-- **Lemma 25** (on the elimination order): on a graph with a degree-two elimination order
in which two distinct vertices have at most two common neighbours — every outerplanar graph —
Algorithm 4 outputs a cycle-path assignment for `k = 4` of cost zero. -/
theorem algorithm4_perfect {g : Graph} {rank : Nat → Nat} (ho : EliminationOrder g rank)
    (hb : CommonNeighbourBound g) :
    ValidChoices ((cycles g 4).map selectedOptions) (algorithm4 rank g) ∧
      cost (algorithm4 rank g) = 0 :=
  ⟨algorithm4_valid rank g, algorithm4_cost ho hb⟩

/-- Such a graph admits a perfect cycle-path assignment for `k = 4`. -/
theorem perfect_four_cycle_assignment {g : Graph} {rank : Nat → Nat} (ho : EliminationOrder g rank)
    (hb : CommonNeighbourBound g) : HasAssignment g 4 0 :=
  ⟨algorithm4 rank g, algorithm4_valid rank g, Nat.le_of_eq (algorithm4_cost ho hb)⟩

end STACS2027
