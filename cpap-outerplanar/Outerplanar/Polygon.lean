module

public import Outerplanar.Defs
public import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Polygons with non-crossing chords

`IsPolygon g n`: the positions `0, …, n - 1` in order form a Hamiltonian cycle of `g` with
respect to which no two edges of `g` cross (`OuterplanarHam g (List.range n)`): the
2-connected outerplanar graphs with an outerplanar embedding, written in the positions of
their outer cycle (Appendix F: "there exists a Hamiltonian cycle `H` consisting only of
edges that touch the outer unbounded face. We call the internal edges `E \ E(H)` chords").

Basic facts: adjacency is symmetric, positions are below `n`, consecutive positions and
`0, n - 1` are adjacent, no two edges cross; a walk avoiding the ends of an edge stays on
one side of it.
-/

@[expose] public section

namespace STACS2027

/-- `g` is a polygon with non-crossing chords on the positions `0, …, n - 1`. -/
def IsPolygon (g : Graph) (n : ℕ) : Prop := OuterplanarHam g (List.range n)

instance (g : Graph) (a b : ℕ) : Decidable (Adj g a b) :=
  decidable_of_iff (a ≠ b ∧ g.contains (edge a b) = true) (by simp [Adj])

theorem Adj.symm {g : Graph} {a b : ℕ} (h : Adj g a b) : Adj g b a :=
  ⟨h.1.symm, by rw [edge_comm]; exact h.2⟩

theorem adj_iff_edge {g : Graph} {a b : ℕ} (hab : a ≠ b) : Adj g a b ↔ edge a b ∈ g :=
  ⟨fun h => h.2, fun h => ⟨hab, h⟩⟩

/-! ### Edges of walks and cycles -/

theorem mem_pathEdges_iff {l : List ℕ} {e : Edge} :
    e ∈ pathEdges l ↔ ∃ xs a b ys, l = xs ++ a :: b :: ys ∧ e = edge a b := by
  induction l with
  | nil => simp [pathEdges]
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [pathEdges, List.not_mem_nil, false_iff, not_exists, not_and]
      intro xs a b ys h
      have := congrArg List.length h
      simp at this
      omega
    | cons y l =>
      simp only [pathEdges, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact ⟨[], x, y, l, rfl, rfl⟩
        · obtain ⟨xs, a, b, ys, hl, rfl⟩ := ih.mp h
          exact ⟨x :: xs, a, b, ys, by rw [hl]; rfl, rfl⟩
      · rintro ⟨xs, a, b, ys, hl, rfl⟩
        cases xs with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hl
          obtain ⟨rfl, rfl, rfl⟩ := hl
          exact Or.inl rfl
        | cons z xs =>
          simp only [List.cons_append, List.cons.injEq] at hl
          obtain ⟨rfl, hl⟩ := hl
          exact Or.inr (ih.mpr ⟨xs, a, b, ys, hl, rfl⟩)

theorem edge_mem_pathEdges (xs ys : List ℕ) (a b : ℕ) :
    edge a b ∈ pathEdges (xs ++ a :: b :: ys) :=
  mem_pathEdges_iff.mpr ⟨xs, a, b, ys, rfl, rfl⟩

/-- Every edge of a cycle is the closing edge of a rotation of it. -/
theorem IsCycle.rotate_edge {g : Graph} {k : ℕ} {c : Cycle} (hc : IsCycle g k c) {e : Edge}
    (he : e ∈ cycleEdges c) :
    ∃ p mid q, IsCycle g k (p :: (mid ++ [q])) ∧ c.Perm (p :: (mid ++ [q])) ∧
      SameCycle c (p :: (mid ++ [q])) ∧ e = edge q p := by
  have hk := hc.1
  have hl := hc.2.1
  obtain ⟨x, c', rfl⟩ : ∃ x c', c = x :: c' := by
    cases c with
    | nil => simp at hl; omega
    | cons x c' => exact ⟨x, c', rfl⟩
  have hce : cycleEdges (x :: c') = pathEdges (x :: c' ++ [x]) := by
    simp [cycleEdges]
  rw [hce] at he
  obtain ⟨xs, a, b, ys, hsplit, rfl⟩ := mem_pathEdges_iff.mp he
  have hsplit' : (x :: c') ++ [x] = xs ++ a :: b :: ys := by simpa using hsplit
  rcases List.eq_nil_or_concat ys with hys | ⟨ys', z, rfl⟩
  · -- the closing edge of `c` itself
    subst hys
    have h2 : (x :: c') ++ [x] = (xs ++ [a]) ++ [b] := by simpa using hsplit'
    obtain ⟨h1, hb⟩ := List.append_inj' h2 rfl
    simp only [List.cons.injEq, and_true] at hb
    subst hb
    obtain ⟨mid, hmid⟩ : ∃ mid, c' = mid ++ [a] := by
      cases xs with
      | nil =>
        simp at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp at hl; omega
      | cons y xs =>
        simp only [List.cons_append, List.cons.injEq] at h1
        exact ⟨xs, h1.2⟩
    subst hmid
    exact ⟨x, mid, a, hc, List.Perm.refl _, SameCycle.refl _, rfl⟩
  · -- an inner edge: rotate
    have h2 : (x :: c') ++ [x] = (xs ++ a :: b :: ys') ++ [z] := by simpa using hsplit'
    obtain ⟨h1, -⟩ := List.append_inj' h2 rfl
    have hsw : (xs ++ [a]) ++ (b :: ys') = x :: c' := by rw [h1]; simp
    have hc' : IsCycle g k ((xs ++ [a]) ++ (b :: ys')) := by rw [hsw]; exact hc
    have hrot := hc'.append_swap
    have hform : (b :: ys') ++ (xs ++ [a]) = b :: (ys' ++ xs ++ [a]) := by simp
    refine ⟨b, ys' ++ xs, a, ?_, ?_, ?_, rfl⟩
    · rw [← hform]; exact hrot
    · rw [← hsw, ← hform]; exact List.perm_append_comm
    · rw [← hsw, ← hform]; exact sameCycle_append_swap _ _

/-! ### The polygon -/

namespace IsPolygon

variable {g : Graph} {n : ℕ}

theorem three_le (hP : IsPolygon g n) : 3 ≤ n := by
  have h := hP.1.1
  simpa using h

theorem lt_of_adj (hP : IsPolygon g n) {a b : ℕ} (h : Adj g a b) : a < n ∧ b < n := by
  have ha : a ∈ List.range n := hP.2.1 a ⟨b, h.symm⟩
  have hb : b ∈ List.range n := hP.2.1 b ⟨a, h⟩
  simp only [List.mem_range] at ha hb
  exact ⟨ha, hb⟩

theorem getD_range {i : ℕ} (h : i < n) : (List.range n).getD i 0 = i := by
  simp [List.getD_eq_getElem?_getD, h]

/-- No two edges cross. -/
theorem noncross (hP : IsPolygon g n) {i j k l : ℕ} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (h1 : Adj g i k) (h2 : Adj g j l) : False := by
  have hl : l < n := (hP.lt_of_adj h2).2
  have := hP.2.2 i j k l hij hjk hkl (by simpa using hl)
  apply this
  rw [getD_range (by omega), getD_range (by omega), getD_range (by omega), getD_range hl]
  exact ⟨h1, h2⟩

theorem range_split {i : ℕ} (h : i + 1 < n) :
    List.range n = List.range i ++ i :: (i + 1) :: List.range' (i + 2) (n - (i + 2)) := by
  rw [List.range_eq_range', List.range_eq_range']
  have : n = i + (1 + (1 + (n - (i + 2)))) := by omega
  conv_lhs => rw [this]
  rw [← List.range'_append_1, show 1 + (1 + (n - (i + 2))) = (n - (i + 2)) + 1 + 1 by omega,
    List.range'_succ, List.range'_succ]
  simp [Nat.add_assoc]

/-- Consecutive positions are adjacent. -/
theorem adj_succ (hP : IsPolygon g n) {i : ℕ} (h : i + 1 < n) : Adj g i (i + 1) := by
  refine ⟨by omega, hP.1.2.2.2 _ ?_⟩
  simp only [cycleEdges]
  rw [range_split h]
  have : List.range i ++ i :: (i + 1) :: List.range' (i + 2) (n - (i + 2)) ++
      List.take 1 (List.range i ++ i :: (i + 1) :: List.range' (i + 2) (n - (i + 2))) =
      List.range i ++ i :: (i + 1) :: (List.range' (i + 2) (n - (i + 2)) ++
        List.take 1 (List.range i ++ i :: (i + 1) :: List.range' (i + 2) (n - (i + 2)))) := by
    simp
  rw [this]
  exact edge_mem_pathEdges _ _ _ _

/-- The first and last positions are adjacent. -/
theorem adj_wrap (hP : IsPolygon g n) : Adj g 0 (n - 1) := by
  have h3 := hP.three_le
  refine ⟨by omega, ?_⟩
  rw [edge_comm]
  apply hP.1.2.2.2
  have hr : List.range n = List.range (n - 1) ++ [n - 1] := by
    rw [← List.range_succ]; congr 1; omega
  simp only [cycleEdges]
  rw [hr]
  have h0 : List.take 1 (List.range (n - 1) ++ [n - 1]) = [0] := by
    rw [← hr]
    cases n with
    | zero => omega
    | succ m => simp [List.range_succ_eq_map]
  rw [h0]
  have : List.range (n - 1) ++ [n - 1] ++ [0] = List.range (n - 1) ++ (n - 1) :: 0 :: [] := by simp
  rw [this]
  exact edge_mem_pathEdges _ _ _ _

end IsPolygon

end STACS2027
