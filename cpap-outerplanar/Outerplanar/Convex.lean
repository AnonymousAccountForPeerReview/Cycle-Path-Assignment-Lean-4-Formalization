module

public import Outerplanar.Polygon
import Mathlib.Tactic

/-!
# Every cycle of a polygon is convex

In a polygon with non-crossing chords (`IsPolygon g n`), every simple cycle visits its
vertices in increasing cyclic order: an edge `pq` of a cycle has all other vertices of the
cycle on one side (a walk from inside `(p, q)` to outside would cross `pq`), so it joins
two vertices consecutive in the sorted vertex list, or its smallest and largest vertex.
Hence the cycle has the edges of its sorted vertex list (`convex_of_isCycle`), and the
simple cycles of `g` are, up to their edge sets, the *convex cycles*: strictly increasing
lists of at least three positions, cyclically consecutive entries adjacent.
-/

@[expose] public section

namespace STACS2027

/-- `u` is a convex cycle of `g`: strictly increasing, at least three entries, cyclically
consecutive entries joined by edges of `g`. -/
def ConvexCycle (g : Graph) (u : List ℕ) : Prop :=
  u.Pairwise (· < ·) ∧ 3 ≤ u.length ∧ ∀ e ∈ cycleEdges u, e ∈ g

theorem ConvexCycle.isCycle {g : Graph} {u : List ℕ} (h : ConvexCycle g u) :
    IsCycle g u.length u :=
  ⟨h.2.1, rfl, h.1.imp (fun h => Nat.ne_of_lt h), h.2.2⟩

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- An edge between vertices other than `a`, `b` does not cross the edge `ab`. -/
theorem step_side (hP : IsPolygon g n) {a b : ℕ} (hab : Adj g a b) (hlt : a < b) {x y : ℕ}
    (hxy : edge x y ∈ g) (hx : x ≠ a ∧ x ≠ b) (hy : y ≠ a ∧ y ≠ b) :
    (a < x ∧ x < b ↔ a < y ∧ y < b) := by
  by_cases hne : x = y
  · subst hne; exact Iff.rfl
  have hA : Adj g x y := ⟨hne, hxy⟩
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hc
    rcases (show y < a ∨ b < y by omega) with h | h
    · exact hP.noncross h h1 h2 hA.symm hab
    · exact hP.noncross h1 h2 h hab hA
  · rintro ⟨h1, h2⟩
    by_contra hc
    rcases (show x < a ∨ b < x by omega) with h | h
    · exact hP.noncross h h1 h2 hA hab
    · exact hP.noncross h1 h2 h hab hA.symm

/-- A walk avoiding `a` and `b` stays on one side of the edge `ab`. -/
theorem walk_side (hP : IsPolygon g n) {a b : ℕ} (hab : Adj g a b) (hlt : a < b) :
    ∀ (w : List ℕ) (x : ℕ), (∀ e ∈ pathEdges (x :: w), e ∈ g) →
      (∀ y ∈ x :: w, y ≠ a ∧ y ≠ b) → ∀ y ∈ x :: w, (a < y ∧ y < b ↔ a < x ∧ x < b) := by
  intro w
  induction w with
  | nil =>
    intro x _ _ y hy
    simp only [List.mem_singleton] at hy
    subst hy; exact Iff.rfl
  | cons z w ih =>
    intro x he hv y hy
    have hxz : (a < z ∧ z < b ↔ a < x ∧ x < b) :=
      (hP.step_side hab hlt (he _ (by simp [pathEdges]))
        (hv x (by simp)) (hv z (by simp))).symm
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Iff.rfl
    · have := ih z (fun e h => he e (by simp only [pathEdges]; exact List.mem_cons_of_mem _ h))
        (fun y hy => hv y (List.mem_cons_of_mem _ hy)) y hy
      exact this.trans hxz

/-- One-sidedness: for a cycle `p :: mid ++ [q]`, all vertices of `mid` lie strictly between
`p` and `q`, or none does. -/
theorem cycle_side (hP : IsPolygon g n) {k p q : ℕ} {mid : List ℕ}
    (hc : IsCycle g k (p :: (mid ++ [q]))) :
    (∀ y ∈ mid, min p q < y ∧ y < max p q) ∨ (∀ y ∈ mid, ¬ (min p q < y ∧ y < max p q)) := by
  obtain ⟨hk, hl, hnd, he⟩ := hc
  have hpq : p ≠ q := by
    intro h; subst h
    simp [List.nodup_cons] at hnd
  have hadj : Adj g (min p q) (max p q) := by
    refine ⟨by omega, ?_⟩
    have : edge q p ∈ cycleEdges (p :: (mid ++ [q])) := by
      rw [cycleEdges_snoc]; simp
    have h := he _ this
    simpa [edge, Nat.min_comm, Nat.max_comm] using h
  rcases mid with _ | ⟨x, w⟩
  · exact Or.inl (by simp)
  · have hpe : ∀ e ∈ pathEdges (x :: w), e ∈ g := by
      intro e hm
      apply he
      rw [cycleEdges_snoc]
      apply List.mem_append_left
      exact pathEdges_infix ⟨[p], [q], by simp⟩ hm
    have hav : ∀ y ∈ x :: w, y ≠ min p q ∧ y ≠ max p q := by
      intro y hy
      have hyp : y ≠ p := by
        intro h; subst h
        simp only [List.nodup_cons] at hnd
        exact hnd.1 (List.mem_append_left _ hy)
      have hyq : y ≠ q := by
        intro h; subst h
        have := (List.nodup_cons.mp hnd).2
        rw [List.nodup_append] at this
        exact this.2.2 y hy y (by simp) rfl
      omega
    have hs := hP.walk_side hadj (by omega) w x hpe hav
    by_cases hx : min p q < x ∧ x < max p q
    · exact Or.inl (fun y hy => (hs y hy).mpr hx)
    · exact Or.inr (fun y hy h => hx ((hs y hy).mp h))

end IsPolygon

/-! ### Sorted lists -/

/-- In a strictly increasing list, two entries with no entry strictly between them are
consecutive. -/
theorem edge_mem_pathEdges_of_gap :
    ∀ {u : List ℕ}, u.Pairwise (· < ·) → ∀ {p q : ℕ}, p ∈ u → q ∈ u → p < q →
      (∀ y ∈ u, ¬ (p < y ∧ y < q)) → edge p q ∈ pathEdges u
  | [], _, _, _, hp, _, _, _ => by simp at hp
  | x :: u, hs, p, q, hp, hq, hpq, hgap => by
    obtain ⟨hx, hs'⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp hp with rfl | hp'
    · rcases List.mem_cons.mp hq with rfl | hq'
      · omega
      · cases u with
        | nil => simp at hq'
        | cons y u =>
          have hy : y = q := by
            rcases List.mem_cons.mp hq' with h | h
            · exact h.symm
            · have h1 := hx y (by simp)
              have h2 := (List.pairwise_cons.mp hs').1 q h
              exact absurd ⟨h1, h2⟩ (hgap y (by simp))
          subst hy
          simp [pathEdges]
    · have hq' : q ∈ u := by
        rcases List.mem_cons.mp hq with rfl | h
        · have := hx p hp'; omega
        · exact h
      have := edge_mem_pathEdges_of_gap hs' hp' hq' hpq (fun y hy => hgap y (by simp [hy]))
      cases u with
      | nil => simp at hp'
      | cons y u => simp only [pathEdges]; exact List.mem_cons_of_mem _ this

/-- The closing edge of a list joins its last and its first entry. -/
theorem edge_last_head_mem_cycleEdges {u : List ℕ} (hu : u ≠ []) :
    edge (u.getLast hu) (u.head hu) ∈ cycleEdges u := by
  obtain ⟨x, w, rfl⟩ : ∃ x w, u = x :: w := by
    cases u with
    | nil => exact absurd rfl hu
    | cons x w => exact ⟨x, w, rfl⟩
  simp only [List.head_cons]
  rcases List.eq_nil_or_concat w with rfl | ⟨w', z, rfl⟩
  · simp [cycleEdges, pathEdges, edge]
  · simp only [List.concat_eq_append]
    have : cycleEdges (x :: (w' ++ [z])) = pathEdges (x :: (w' ++ [z])) ++ [edge z x] :=
      cycleEdges_snoc x z w'
    rw [this]
    simp

theorem pathEdges_subset_cycleEdges (u : List ℕ) : ∀ e ∈ pathEdges u, e ∈ cycleEdges u := by
  intro e he
  exact pathEdges_infix ⟨[], u.take 1, by simp⟩ he

/-- In a strictly increasing list, an entry that is at most every entry is the first, and an
entry at least every entry is the last. -/
theorem head_eq_of_le {u : List ℕ} (hs : u.Pairwise (· < ·)) (hu : u ≠ []) {p : ℕ}
    (hp : p ∈ u) (hle : ∀ y ∈ u, p ≤ y) : u.head hu = p := by
  cases u with
  | nil => exact absurd rfl hu
  | cons x w =>
    simp only [List.head_cons]
    rcases List.mem_cons.mp hp with rfl | h
    · rfl
    · have h1 := (List.pairwise_cons.mp hs).1 p h
      have h2 := hle x (by simp)
      omega

theorem getLast_eq_of_le {u : List ℕ} (hs : u.Pairwise (· < ·)) (hu : u ≠ []) {q : ℕ}
    (hq : q ∈ u) (hle : ∀ y ∈ u, y ≤ q) : u.getLast hu = q := by
  have hmem := List.getLast_mem hu
  by_contra hne
  obtain ⟨xs, hxs⟩ : ∃ xs, u = xs ++ [u.getLast hu] := ⟨u.dropLast, (List.dropLast_append_getLast hu).symm⟩
  have hq' : q ∈ xs := by
    rw [hxs] at hq
    rcases List.mem_append.mp hq with h | h
    · exact h
    · simp at h; exact absurd h.symm hne
  rw [hxs] at hs
  have h1 := (List.pairwise_append.mp hs).2.2 q hq' (u.getLast hu) (List.mem_singleton_self _)
  have h2 := hle _ hmem
  omega

/-! ### The convexity theorem -/

theorem edge_max_min (p q : ℕ) : edge (max p q) (min p q) = edge q p := by
  simp only [edge, Prod.mk.injEq]; omega

theorem edge_min_max (p q : ℕ) : edge (min p q) (max p q) = edge q p := by
  simp only [edge, Prod.mk.injEq]; omega

/-- The vertices of a cycle are the endpoints of its edges. -/
theorem mem_of_mem_cycleEdges {u : List ℕ} {a b : ℕ} (h : edge a b ∈ cycleEdges u) :
    a ∈ u ∧ b ∈ u := by
  have := pathEdge_vertices h
  simp only [List.mem_append] at this
  constructor
  · rcases this.1 with h | h
    · exact h
    · exact List.mem_of_mem_take h
  · rcases this.2 with h | h
    · exact h
    · exact List.mem_of_mem_take h

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- **Every cycle of a polygon is convex**: a simple cycle has the edges of its sorted
vertex list, which is a convex cycle. -/
theorem convex_of_isCycle (hP : IsPolygon g n) {k : ℕ} {c : Cycle} (hc : IsCycle g k c) :
    ConvexCycle g (c.insertionSort (· ≤ ·)) ∧ (c.insertionSort (· ≤ ·)).length = k ∧
      SameCycle c (c.insertionSort (· ≤ ·)) := by
  set u := c.insertionSort (· ≤ ·) with hu_def
  have hperm : u.Perm c := List.perm_insertionSort _ _
  have hlen : u.length = k := hperm.length_eq.trans hc.2.1
  have hnd : u.Nodup := hperm.nodup_iff.mpr hc.2.2.1
  have hsorted : u.Pairwise (· < ·) := by
    have h1 : u.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
    have h2 := hnd
    rw [List.Nodup] at h2
    exact (h1.and h2).imp (fun ⟨h, h'⟩ => lt_of_le_of_ne h h')
  have hk := hc.1
  have hune : u ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  -- every edge of `c` is an edge of `u`
  have hsub : ∀ e ∈ cycleEdges c, e ∈ cycleEdges u := by
    intro e he
    obtain ⟨p, mid, q, hc', hp', -, rfl⟩ := hc.rotate_edge he
    have hmemc : ∀ y, y ∈ c ↔ y ∈ p :: (mid ++ [q]) := fun y => hp'.mem_iff
    have hmemu : ∀ y, y ∈ u ↔ y ∈ p :: (mid ++ [q]) := fun y => (hperm.mem_iff).trans (hmemc y)
    have hpq : p ≠ q := by
      intro h; subst h
      have := hc'.2.2.1
      simp [List.nodup_cons] at this
    have hpu : p ∈ u := (hmemu p).mpr (by simp)
    have hqu : q ∈ u := (hmemu q).mpr (by simp)
    rcases hP.cycle_side hc' with hin | hout
    · -- `p`, `q` are the smallest and largest vertex
      have hall : ∀ y ∈ u, min p q ≤ y ∧ y ≤ max p q := by
        intro y hy
        rcases List.mem_cons.mp ((hmemu y).mp hy) with rfl | hy'
        · omega
        · rcases List.mem_append.mp hy' with hm | hm
          · have := hin y hm; omega
          · simp at hm; subst hm; omega
      have hmin : u.head hune = min p q := head_eq_of_le hsorted hune
        (by rcases Nat.le_total p q with h | h <;> simp [h, hpu, hqu])
        (fun y hy => (hall y hy).1)
      have hmax : u.getLast hune = max p q := getLast_eq_of_le hsorted hune
        (by rcases Nat.le_total p q with h | h <;> simp [h, hpu, hqu])
        (fun y hy => (hall y hy).2)
      have := edge_last_head_mem_cycleEdges hune
      rw [hmin, hmax, edge_max_min] at this
      exact this
    · -- `p`, `q` are consecutive in `u`
      have hgap : ∀ y ∈ u, ¬ (min p q < y ∧ y < max p q) := by
        intro y hy
        rcases List.mem_cons.mp ((hmemu y).mp hy) with rfl | hy'
        · omega
        · rcases List.mem_append.mp hy' with hm | hm
          · exact hout y hm
          · simp at hm; subst hm; omega
      have hmn : min p q ∈ u := by
        rcases Nat.le_total p q with h | h <;> simp [h, hpu, hqu]
      have hmx : max p q ∈ u := by
        rcases Nat.le_total p q with h | h <;> simp [h, hpu, hqu]
      have := edge_mem_pathEdges_of_gap hsorted hmn hmx (by omega) hgap
      have h' := pathEdges_subset_cycleEdges u _ this
      rw [edge_min_max] at h'
      exact h'
  -- the edge lists have the same length, so the same members
  have hcnd := hc.edges_nodup
  have hlc : (cycleEdges c).length = k := by
    simp [cycleEdges, pathEdges_length, hc.2.1]; omega
  have hlu : (cycleEdges u).length = k := by
    simp [cycleEdges, pathEdges_length, hlen]; omega
  have hsp : (cycleEdges c).Subperm (cycleEdges u) := hcnd.subperm hsub
  have hpe : (cycleEdges c).Perm (cycleEdges u) := hsp.perm_of_length_le (by omega)
  have hsame : SameCycle c u := ⟨hsub, fun e he => hpe.symm.subset he⟩
  refine ⟨⟨hsorted, by omega, fun e he => hc.2.2.2 e (hsame.2 e he)⟩, hlen, hsame⟩

end IsPolygon

/-- Two convex cycles with the same edges are equal. -/
theorem ConvexCycle.eq_of_sameCycle {g : Graph} {u v : List ℕ} (hu : ConvexCycle g u)
    (hv : ConvexCycle g v) (h : SameCycle u v) : u = v := by
  have hmem : ∀ x, x ∈ u ↔ x ∈ v := by
    intro x
    constructor
    · intro hx
      obtain ⟨w, -, hw⟩ := hu.isCycle.vertex_incident hx
      exact (mem_of_mem_cycleEdges (h.1 _ hw)).1
    · intro hx
      obtain ⟨w, -, hw⟩ := hv.isCycle.vertex_incident hx
      exact (mem_of_mem_cycleEdges (h.2 _ hw)).1
  exact hu.1.eq_of_mem_iff hv.1 hmem

end STACS2027
