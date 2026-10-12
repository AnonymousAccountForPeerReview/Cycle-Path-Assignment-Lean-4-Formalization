module

public import MinorFree.LoadBounds

/-!
The counts and cost bounds of Lemma 23: the graphs `K_{2,r}` (`n = r + 2` vertices, `m = 2r`
edges) have `binom(r, 2)` four-cycles, and every four-cycle assignment has cost between
`r(r − 1)(r − 3)/4` and `r(r − 1)(r − 2)`: the optimal cost is `Θ(n³)`. Their planarity,
and `biclique_planar_family`, which combines both, are in `MinorFree.BicliquePlanar`.
-/

@[expose] public section
namespace STACS2027

/-- `K_{2,r}`: the vertices `0` and `1` joined to each of `2, …, r + 1`. -/
def biclique (r : Nat) : Graph :=
  (List.range r).flatMap fun j => [(0, j + 2), (1, j + 2)]

/-- The pairs `(i, j)` with `i < j < r`, in lexicographic order of `(j, i)`. -/
def pairs (r : Nat) : List (Nat × Nat) :=
  (List.range r).flatMap fun j => (List.range j).map fun i => (i, j)

/-- The canonical four-cycles `[0, i + 2, 1, j + 2]` of `K_{2,r}`, one per pair `i < j`. -/
def canonicalCycles (r : Nat) : List Cycle :=
  (pairs r).map fun p => [0, p.1 + 2, 1, p.2 + 2]

theorem mem_biclique {r : Nat} {e : Edge} :
    e ∈ biclique r ↔ ∃ j, j < r ∧ (e = (0, j + 2) ∨ e = (1, j + 2)) := by
  simp only [biclique, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false]

theorem biclique_length (r : Nat) : (biclique r).length = 2 * r := by
  unfold biclique
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil]
  rw [sum_map_const, List.length_range]
  omega

theorem biclique_nodup (r : Nat) : (biclique r).Nodup := by
  induction r with
  | zero => simp [biclique]
  | succ r ih =>
    have hsplit : biclique (r + 1) = biclique r ++ [(0, r + 2), (1, r + 2)] := by
      simp [biclique, List.range_succ]
    rw [hsplit, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    obtain ⟨j, hj, hab⟩ := mem_biclique.mp ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hab with rfl | rfl <;> rcases hb with rfl | rfl <;> simp <;> omega

theorem edge_mem_biclique {r a b : Nat} (h : edge a b ∈ biclique r) :
    (a ≤ 1 ∧ 2 ≤ b ∧ b < r + 2) ∨ (b ≤ 1 ∧ 2 ≤ a ∧ a < r + 2) := by
  obtain ⟨j, hj, hab⟩ := mem_biclique.mp h
  rcases hab with hab | hab
  · rcases (edge_eq_iff a b 0 (j + 2)).mp (by rw [hab]; rfl) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; omega
    · right; omega
  · rcases (edge_eq_iff a b 1 (j + 2)).mp (by rw [hab]; rfl) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; omega
    · right; omega

theorem edge_zero_mem {r j : Nat} (hj : 2 ≤ j) (hr : j < r + 2) : edge 0 j ∈ biclique r :=
  mem_biclique.mpr ⟨j - 2, by omega, Or.inl (by simp [edge]; omega)⟩

theorem edge_one_mem {r j : Nat} (hj : 2 ≤ j) (hr : j < r + 2) : edge 1 j ∈ biclique r :=
  mem_biclique.mpr ⟨j - 2, by omega, Or.inr (by simp [edge]; omega)⟩

/-- The canonical cycles are four-cycles of `K_{2,r}`. -/
theorem canonical_isCycle {r x y : Nat} (hx : 2 ≤ x) (hxr : x < r + 2) (hy : 2 ≤ y) (hyr : y < r + 2)
    (hxy : x ≠ y) : IsCycle (biclique r) 4 [0, x, 1, y] := by
  refine ⟨by decide, rfl, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]
    omega
  · intro e he
    rw [mem_cycleEdges_four] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact edge_zero_mem hx hxr
    · rw [edge_comm]; exact edge_one_mem hx hxr
    · exact edge_one_mem hy hyr
    · rw [edge_comm]; exact edge_zero_mem hy hyr

/-- The edge set of `[0, x, 1, y]` and of each of its rotations and reversals. -/
theorem sameCycle_shapes (x y : Nat) :
    SameCycle [1, x, 0, y] [0, x, 1, y] ∧ SameCycle [x, 0, y, 1] [0, x, 1, y] ∧
      SameCycle [x, 1, y, 0] [0, x, 1, y] ∧ SameCycle [0, y, 1, x] [0, x, 1, y] := by
  have key : ∀ c d : Cycle, (∀ e, e ∈ cycleEdges c ↔ e ∈ cycleEdges d) → SameCycle c d :=
    fun c d h => ⟨fun e he => (h e).mp he, fun e he => (h e).mpr he⟩
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_⟩ <;> intro e <;>
    rw [mem_cycleEdges_four, mem_cycleEdges_four] <;>
    constructor <;> rintro (h | h | h | h) <;> subst h <;>
    simp only [edge_eq_iff, true_and, and_true, or_true, true_or] <;> omega

/-- Every four-cycle of `K_{2,r}` is `[0, x, 1, y]` up to rotation and reversal, with
`2 ≤ x < y < r + 2`. -/
theorem biclique_cycle_shape {r : Nat} {c : Cycle} (hc : IsCycle (biclique r) 4 c) :
    ∃ x y, 2 ≤ x ∧ x < y ∧ y < r + 2 ∧ SameCycle c [0, x, 1, y] := by
  have hl := hc.2.1
  obtain ⟨a, b, u, v, rfl⟩ : ∃ a b u v, c = [a, b, u, v] := by
    match c, hl with
    | [a, b, u, v], _ => exact ⟨a, b, u, v, rfl⟩
  obtain ⟨hab, hau, hav, hbu, hbv, huv⟩ := nodup_four hc.2.2.1
  have e1 := edge_mem_biclique (hc.2.2.2 (edge a b) (by simp [cycleEdges_four]))
  have e2 := edge_mem_biclique (hc.2.2.2 (edge b u) (by simp [cycleEdges_four]))
  have e3 := edge_mem_biclique (hc.2.2.2 (edge u v) (by simp [cycleEdges_four]))
  have e4 := edge_mem_biclique (hc.2.2.2 (edge v a) (by simp [cycleEdges_four]))
  have S1 : ∀ x y, SameCycle [1, x, 0, y] [0, x, 1, y] := fun x y => (sameCycle_shapes x y).1
  have S2 : ∀ x y, SameCycle [x, 0, y, 1] [0, x, 1, y] := fun x y => (sameCycle_shapes x y).2.1
  have S3 : ∀ x y, SameCycle [x, 1, y, 0] [0, x, 1, y] := fun x y => (sameCycle_shapes x y).2.2.1
  have S4 : ∀ x y, SameCycle [0, y, 1, x] [0, x, 1, y] := fun x y => (sameCycle_shapes x y).2.2.2
  -- Sort out which vertices are `0, 1` and which are large.
  rcases Nat.lt_or_ge a 2 with ha | ha
  · -- `a ∈ {0, 1}`, `b ≥ 2`, `u ∈ {0, 1}`, `v ≥ 2`.
    have hb : 2 ≤ b ∧ b < r + 2 := by omega
    have hu : u ≤ 1 := by omega
    have hv : 2 ≤ v ∧ v < r + 2 := by omega
    rcases Nat.lt_or_ge b v with hbv' | hbv'
    · refine ⟨b, v, hb.1, hbv', hv.2, ?_⟩
      rcases (show (a = 0 ∧ u = 1) ∨ (a = 1 ∧ u = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact SameCycle.refl _
      · exact S1 b v
    · refine ⟨v, b, hv.1, by omega, hb.2, ?_⟩
      rcases (show (a = 0 ∧ u = 1) ∨ (a = 1 ∧ u = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact S4 v b
      · exact (S1 b v).trans (S4 v b)
  · -- `a ≥ 2`, `b ∈ {0, 1}`, `u ≥ 2`, `v ∈ {0, 1}`.
    have ha' : a < r + 2 := by omega
    have hb : b ≤ 1 := by omega
    have hu : 2 ≤ u ∧ u < r + 2 := by omega
    have hv : v ≤ 1 := by omega
    rcases Nat.lt_or_ge a u with hau' | hau'
    · refine ⟨a, u, ha, hau', hu.2, ?_⟩
      rcases (show (b = 0 ∧ v = 1) ∨ (b = 1 ∧ v = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact S2 a u
      · exact S3 a u
    · refine ⟨u, a, hu.1, by omega, ha', ?_⟩
      rcases (show (b = 0 ∧ v = 1) ∨ (b = 1 ∧ v = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (S2 a u).trans (S4 u a)
      · exact (S3 a u).trans (S4 u a)

theorem mem_pairs {r : Nat} {p : Nat × Nat} : p ∈ pairs r ↔ p.1 < p.2 ∧ p.2 < r := by
  obtain ⟨i, j⟩ := p
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨j', hj', i', hi', rfl, rfl⟩
    exact ⟨hi', hj'⟩
  · rintro ⟨hij, hj⟩
    exact ⟨j, hj, i, hij, rfl, rfl⟩

theorem pairs_succ (r : Nat) : pairs (r + 1) = pairs r ++ (List.range r).map fun i => (i, r) := by
  simp [pairs, List.range_succ]

theorem pairs_length (r : Nat) : (pairs r).length = pairCount r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [pairs_succ, ih, pairCount]

theorem pairs_nodup (r : Nat) : (pairs r).Nodup := by
  induction r with
  | zero => simp [pairs]
  | succ r ih =>
    rw [pairs_succ, List.nodup_append]
    refine ⟨ih, ?_, ?_⟩
    · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp (fun h he => h (by simpa using he))
    · intro a ha b hb hab
      subst hab
      have := (mem_pairs.mp ha).2
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      simp at this

/-- Two canonical cycles with the same edges are the same pair. -/
theorem canonical_injective {x y x' y' : Nat} (hx : 2 ≤ x) (hxy : x < y) (hx' : 2 ≤ x')
    (hxy' : x' < y') (hs : SameCycle [0, x, 1, y] [0, x', 1, y']) : x = x' ∧ y = y' := by
  have h1 := hs.1 (edge 0 x) (by rw [mem_cycleEdges_four]; exact Or.inl rfl)
  have h2 := hs.1 (edge 1 y) (by rw [mem_cycleEdges_four]; exact Or.inr (Or.inr (Or.inl rfl)))
  rw [mem_cycleEdges_four] at h1 h2
  have k1 : x = x' ∨ x = y' := by
    rcases h1 with h | h | h | h <;> rcases (edge_eq_iff _ _ _ _).mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
  have k2 : y = x' ∨ y = y' := by
    rcases h2 with h | h | h | h <;> rcases (edge_eq_iff _ _ _ _).mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
  omega

theorem canonical_pairwise (r : Nat) : (canonicalCycles r).Pairwise fun c d => ¬ SameCycle c d := by
  unfold canonicalCycles
  rw [List.pairwise_map]
  apply (pairs_nodup r).imp_of_mem
  intro p q hp hq hne hs
  have hp' := mem_pairs.mp hp
  have hq' := mem_pairs.mp hq
  obtain ⟨h1, h2⟩ := canonical_injective (by omega) (by omega : p.1 + 2 < p.2 + 2) (by omega)
    (by omega : q.1 + 2 < q.2 + 2) hs
  apply hne
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  simp only [Prod.mk.injEq]
  omega

theorem canonical_cover {r : Nat} {c : Cycle} (hc : IsCycle (biclique r) 4 c) :
    ∃ d ∈ canonicalCycles r, SameCycle c d := by
  obtain ⟨x, y, hx, hxy, hyr, hs⟩ := biclique_cycle_shape hc
  refine ⟨[0, x, 1, y], ?_, hs⟩
  unfold canonicalCycles
  apply List.mem_map.mpr
  refine ⟨(x - 2, y - 2), mem_pairs.mpr ⟨show x - 2 < y - 2 by omega, show y - 2 < r by omega⟩, ?_⟩
  show [0, x - 2 + 2, 1, y - 2 + 2] = [0, x, 1, y]
  have e1 : x - 2 + 2 = x := by omega
  have e2 : y - 2 + 2 = y := by omega
  rw [e1, e2]

theorem canonical_isCycle' {r : Nat} {d : Cycle} (hd : d ∈ canonicalCycles r) :
    IsCycle (biclique r) 4 d := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
  have := mem_pairs.mp hp
  exact canonical_isCycle (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The enumerated four-cycles of `K_{2,r}`, up to the choice of representatives, are the
canonical ones. -/
theorem biclique_cycles_perm (r : Nat) :
    ((canonicalCycles r).map (representativeIn (cycles (biclique r) 4))).Perm
      (cycles (biclique r) 4) :=
  representatives_perm (canonical_pairwise r) (cycles_pairwise_different _ 4)
    (fun _ hc => isCycle_represented (canonical_isCycle' hc))
    (fun _ hd => canonical_cover (enumerated_isCycle hd))

/-- `K_{2,r}` has `binom(r, 2)` four-cycles. -/
theorem biclique_cycle_count (r : Nat) : (cycles (biclique r) 4).length = pairCount r := by
  rw [← (biclique_cycles_perm r).length_eq, List.length_map, canonicalCycles, List.length_map,
    pairs_length]

/-- The lower bound of Lemma 23: every four-cycle assignment of `K_{2,r}` has cost at least
`r (r − 1)(r − 3) / 4`. -/
theorem biclique_cost_lower {r : Nat} {ps : List (List Edge)}
    (hv : ValidChoices ((cycles (biclique r) 4).map selectedOptions) ps) :
    r * (r - 1) * (r - 3) ≤ 4 * cost ps := by
  have h := cost_lower_bound (biclique_nodup r) hv
  rw [biclique_cycle_count, biclique_length] at h
  have hQ : (4 - 2) * pairCount r = r * (r - 1) := two_mul_pairCount r
  rw [hQ] at h
  -- `(r(r−1))² ≤ 2r (2c + r(r−1))`.
  rcases Nat.lt_or_ge r 3 with hr | hr
  · have : r - 3 = 0 := by omega
    rw [this]; simp
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
    simp only [Nat.add_sub_cancel] at h ⊢
    have e1 : s + 3 - 1 = s + 2 := by omega
    rw [e1] at h ⊢
    -- `h : (s+3)(s+2) (s+3)(s+2) ≤ 2(s+3) (2c + (s+3)(s+2))`; goal `(s+3)(s+2) s ≤ 4c`.
    have hpos : 0 < s + 3 := by omega
    have key : (s + 3) * ((s + 2) * (s + 2) * (s + 3)) ≤ (s + 3) * (2 * (2 * cost ps + (s + 3) * (s + 2))) := by
      calc (s + 3) * ((s + 2) * (s + 2) * (s + 3)) = (s + 3) * (s + 2) * ((s + 3) * (s + 2)) := by grind
        _ ≤ 2 * (s + 3) * (2 * cost ps + (s + 3) * (s + 2)) := h
        _ = (s + 3) * (2 * (2 * cost ps + (s + 3) * (s + 2))) := by grind
    have h2 := Nat.le_of_mul_le_mul_left key hpos
    -- `(s+2)²(s+3) ≤ 4c + 2(s+3)(s+2)`, i.e. `(s+3)(s+2)s ≤ 4c`.
    have e2 : (s + 2) * (s + 2) * (s + 3) = (s + 3) * (s + 2) * s + 2 * ((s + 3) * (s + 2)) := by grind
    rw [e2] at h2
    omega

/-- Each edge of `K_{2,r}` lies on exactly `r − 1` four-cycles. -/
theorem biclique_edge_cycles {r : Nat} {e : Edge} (he : e ∈ biclique r) :
    ((cycles (biclique r) 4).filter fun c => decide (e ∈ cycleEdges c)).length = r - 1 := by
  -- Pass to the canonical cycles, which have the same edge sets as their representatives.
  have hperm := (biclique_cycles_perm r).filter fun c => decide (e ∈ cycleEdges c)
  rw [← hperm.length_eq, List.filter_map]
  have hrep : ∀ d ∈ canonicalCycles r,
      decide (e ∈ cycleEdges (representativeIn (cycles (biclique r) 4) d)) = decide (e ∈ cycleEdges d) := by
    intro d hd
    have hs := (representativeIn_spec (isCycle_represented (canonical_isCycle' hd))).2
    by_cases hm : e ∈ cycleEdges d
    · simp [hm, hs.1 e hm]
    · have : e ∉ cycleEdges (representativeIn (cycles (biclique r) 4) d) := fun h => hm (hs.2 e h)
      simp [hm, this]
  rw [List.filter_congr (fun d hd => by rw [Function.comp_apply, hrep d hd])]
  -- Count the pairs containing the large endpoint of `e`.
  obtain ⟨j, hj, hej⟩ := mem_biclique.mp he
  have hmem : ∀ p ∈ pairs r, decide (e ∈ cycleEdges [0, p.1 + 2, 1, p.2 + 2]) =
      decide (p.1 = j ∨ p.2 = j) := by
    intro p hp
    have hp' := mem_pairs.mp hp
    apply decide_eq_decide.mpr
    rw [mem_cycleEdges_four]
    rcases hej with rfl | rfl
    · constructor
      · rintro (h | h | h | h) <;> rcases (edge_eq_iff _ _ _ _).mp (by rw [← h]; rfl : edge 0 (j + 2) = _) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
      · rintro (h | h)
        · left; simp [edge]; omega
        · right; right; right; rw [edge_comm]; simp [edge]; omega
    · constructor
      · rintro (h | h | h | h) <;> rcases (edge_eq_iff _ _ _ _).mp (by rw [← h]; rfl : edge 1 (j + 2) = _) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
      · rintro (h | h)
        · right; left; rw [edge_comm]; simp [edge]; omega
        · right; right; left; simp [edge]; omega
  unfold canonicalCycles
  rw [List.filter_map, List.length_map, List.length_map, List.filter_congr (fun p hp => by
    rw [Function.comp_apply, hmem p hp])]
  -- `|{p ∈ pairs r : j ∈ p}| = r − 1`.
  clear hmem hrep hperm he hej
  induction r with
  | zero => simp at hj
  | succ r ih =>
    rw [pairs_succ, List.filter_append, List.length_append, List.filter_map, List.length_map]
    have hcomp : ((fun p : Nat × Nat => decide (p.1 = j ∨ p.2 = j)) ∘ fun i => (i, r)) =
        fun i => decide (i = j ∨ r = j) := by
      funext i; rfl
    rw [hcomp]
    by_cases hjr : j = r
    · subst hjr
      have h0 : ((pairs j).filter fun p => decide (p.1 = j ∨ p.2 = j)).length = 0 := by
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro p hp
        have := mem_pairs.mp hp
        simp; omega
      have h1 : ((List.range j).filter fun i => decide (i = j ∨ j = j)).length = j := by
        rw [List.filter_eq_self.mpr (fun i _ => by simp)]
        exact List.length_range
      rw [h0, h1]; omega
    · have hj' : j < r := by omega
      rw [ih hj']
      have h1 : ((List.range r).filter fun i => decide (i = j ∨ r = j)).length = 1 := by
        have hrj : ¬ r = j := fun h => hjr h.symm
        have : ((List.range r).filter fun i => decide (i = j ∨ r = j)) =
            (List.range r).filter fun i => decide (i = j) :=
          List.filter_congr (fun i _ => by simp [hrj])
        rw [this, ← List.countP_eq_length_filter]
        have hc : (List.range r).countP (fun i => decide (i = j)) = (List.range r).count j := by
          simp only [List.count]
          exact List.countP_congr (fun i _ => by cases h : decide (i = j) <;> simp_all)
        rw [hc]
        exact List.Nodup.count_of_mem List.nodup_range (List.mem_range.mpr hj')
      rw [h1]; omega

/-- The upper bound of Lemma 23: every four-cycle assignment of `K_{2,r}` has cost at most
`m binom(r − 1, 2) = r (r − 1)(r − 2)`. -/
theorem biclique_cost_upper {r : Nat} {ps : List (List Edge)}
    (hv : ValidChoices ((cycles (biclique r) 4).map selectedOptions) ps) :
    cost ps ≤ r * (r - 1) * (r - 2) := by
  have h := cost_le_of_load_le (biclique_nodup r) hv (L := r - 1) (fun e he => by
    have := load_le_cycle_count hv e
    rw [biclique_edge_cycles he] at this
    exact this)
  rw [biclique_length] at h
  have h2 := two_mul_pairCount (r - 1)
  rcases Nat.lt_or_ge r 2 with hr | hr
  · have : r - 2 = 0 := by omega
    rw [this, Nat.mul_zero]
    have hp : pairCount (r - 1) = 0 := by
      have : r - 1 = 0 ∨ r - 1 = 1 := by omega
      rcases this with h0 | h1
      · rw [h0]; rfl
      · rw [h1]; rfl
    rw [hp] at h
    omega
  · have e : r - 1 - 1 = r - 2 := by omega
    rw [e] at h2
    calc cost ps ≤ 2 * r * pairCount (r - 1) := h
      _ = r * (2 * pairCount (r - 1)) := by grind
      _ = r * ((r - 1) * (r - 2)) := by rw [h2]
      _ = r * (r - 1) * (r - 2) := by rw [Nat.mul_assoc]

end STACS2027
