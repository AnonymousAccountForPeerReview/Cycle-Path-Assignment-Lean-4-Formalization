module

public import Outerplanar.Reach
public import Mathlib.Data.List.Chain
import Mathlib.Tactic

/-!
# Lemma 19 (third sentence), tools: chains, paths, cycles and `K_{2,3}` minors from five lists

Tools for the proof of the third sentence of Lemma 19 in `Outerplanar/TwoConnectedK23Structure.lean`.

* `walkWithin_iff`: a walk within `S` is a list of vertices satisfying `S` that is a chain
  (`List.IsChain`) of the adjacency `Adj g`, so that Mathlib's chain lemmas apply. A chain is
  a connected vertex set (`connectedWithin_of_isChain`), and two consecutive pieces of a chain
  are joined by an edge (`exists_adj_of_infix`).
* `Reach.exit`: a walk from a vertex satisfying `Q` to one that does not leaves `Q` through an
  edge `ab` with `a` reachable within `Q`. `Reach.exists_path`: a walk shortens to a path
  (a chain without repetitions) with the same ends.
* `IsCyc g K`: `K` is a cycle of `g` — at least three distinct vertices, cyclically
  consecutive ones adjacent (the chain `K ++ K.take 1`). Cycles are invariant under rotation
  (`IsCyc.append_comm`), consist of vertices (`IsCyc.isVertex`), are at most as long as the
  list `vertList g` of the edge ends (`IsCyc.length_le`), and are cycles in the sense of
  Section 5 (`IsCyc.isCycle`). `IsCyc.extend`: replacing the edge `uv` of a cycle by a path
  from `u` to `v` through vertices off the cycle gives a longer cycle.
* `hasMinor_k23_of`: five pairwise disjoint connected vertex lists, each of the first two
  joined by an edge to each of the last three, are the branch sets of a `K_{2,3}` minor.
-/

@[expose] public section

namespace STACS2027

namespace K23Struct

/-! ### Walks as chains -/

theorem walkWithin_iff {g : Graph} {S : ℕ → Prop} :
    ∀ {w : List ℕ}, WalkWithin g S w ↔ (∀ x ∈ w, S x) ∧ w.IsChain (Adj g)
  | [] => by simp [WalkWithin]
  | [a] => by simp [WalkWithin]
  | a :: b :: rest => by
    rw [WalkWithin, walkWithin_iff, List.isChain_cons_cons]
    simp only [List.forall_mem_cons]
    tauto

theorem reach_head_of_isChain {g : Graph} :
    ∀ {a : ℕ} {w : List ℕ}, (a :: w).IsChain (Adj g) →
      ∀ x ∈ a :: w, Reach g (· ∈ a :: w) x a
  | a, [], _, x, hx => by
    rw [List.mem_singleton] at hx
    subst hx
    exact .refl (by simp)
  | a, b :: rest, h, x, hx => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .refl (by simp)
    · have hb : Reach g (· ∈ a :: b :: rest) x b :=
        (reach_head_of_isChain h.2 x hx).mono fun v hv => List.mem_cons_of_mem _ hv
      exact hb.trans (.edge (by simp) (by simp) h.1.symm)

/-- The vertices of a chain of the adjacency form a connected set. -/
theorem connectedWithin_of_isChain {g : Graph} {w : List ℕ} (h : w.IsChain (Adj g)) :
    ConnectedWithin g (· ∈ w) := by
  cases w with
  | nil => intro u _ hu; simp at hu
  | cons a w => exact connectedWithin_of_hub (c := a) (reach_head_of_isChain h)

/-- Two consecutive nonempty pieces of a chain are related by the chain relation. -/
theorem exists_adj_of_infix {R : ℕ → ℕ → Prop} {L w1 w2 : List ℕ} (hL : L.IsChain R)
    (hi : w1 ++ w2 <:+: L) (h1 : w1 ≠ []) (h2 : w2 ≠ []) : ∃ u ∈ w1, ∃ v ∈ w2, R u v :=
  ⟨_, List.getLast_mem h1, _, List.head_mem h2, (hL.infix hi).rel_getLast_head_of_append h1 h2⟩

/-- `exists_adj_of_infix` for the adjacency, in the other direction. -/
theorem exists_adj_of_infix_rev {g : Graph} {L w1 w2 : List ℕ} (hL : L.IsChain (Adj g))
    (hi : w1 ++ w2 <:+: L) (h1 : w1 ≠ []) (h2 : w2 ≠ []) : ∃ u ∈ w2, ∃ v ∈ w1, Adj g u v := by
  obtain ⟨u, hu, v, hv, h⟩ := exists_adj_of_infix hL hi h1 h2
  exact ⟨v, hv, u, hu, h.symm⟩

end K23Struct

/-! ### Leaving a set, and paths -/

/-- A walk from a vertex satisfying `Q` to a vertex not satisfying `Q` leaves `Q` through an
edge `ab`, `a` reachable from the start within `Q`. -/
theorem Reach.exit {g : Graph} {S Q : ℕ → Prop} {u v : ℕ} (h : Reach g S u v) (hu : Q u)
    (hv : ¬ Q v) : ∃ a b, Reach g (fun x => S x ∧ Q x) u a ∧ Adj g a b ∧ S b ∧ ¬ Q b := by
  induction h with
  | refl _ => exact absurd hu hv
  | @step u v' w hu' hadj hr ih =>
    by_cases hq : Q v'
    · obtain ⟨a, b, h1, h2, h3, h4⟩ := ih hq hv
      exact ⟨a, b, .step ⟨hu', hu⟩ hadj h1, h2, h3, h4⟩
    · exact ⟨u, v', .refl ⟨hu', hu⟩, hadj, hr.left, hq⟩

/-- A walk within `S` shortens to a path within `S` with the same ends. -/
theorem Reach.exists_path {g : Graph} {S : ℕ → Prop} {u v : ℕ} (h : Reach g S u v) :
    ∃ p : List ℕ, p.head? = some u ∧ p.getLast? = some v ∧ (∀ x ∈ p, S x) ∧
      p.IsChain (Adj g) ∧ p.Nodup := by
  induction h with
  | @refl u hu =>
    exact ⟨[u], rfl, rfl, by simpa using hu, List.isChain_singleton u, List.nodup_singleton u⟩
  | @step u v' w hu hadj _ ih =>
    obtain ⟨p, h1, h2, h3, h4, h5⟩ := ih
    by_cases hm : u ∈ p
    · obtain ⟨s, t, rfl⟩ := List.append_of_mem hm
      refine ⟨u :: t, rfl, ?_, fun x hx => h3 x (List.mem_append_right _ hx),
        h4.right_of_append, (List.nodup_append.mp h5).2.1⟩
      simpa using h2
    · obtain ⟨p', rfl⟩ : ∃ p', p = v' :: p' := by
        cases p with
        | nil => simp at h1
        | cons z p' =>
          simp only [List.head?_cons, Option.some.injEq] at h1
          exact ⟨p', by rw [h1]⟩
      refine ⟨u :: v' :: p', rfl, by simpa [List.getLast?_cons_cons] using h2, ?_,
        List.IsChain.cons_cons hadj h4, List.nodup_cons.mpr ⟨hm, h5⟩⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hu
      · exact h3 x hx

namespace K23Struct

theorem mem_of_head? {l : List ℕ} {a : ℕ} (h : l.head? = some a) : a ∈ l :=
  List.mem_of_mem_head? h

theorem mem_of_getLast? {l : List ℕ} {a : ℕ} (h : l.getLast? = some a) : a ∈ l :=
  List.mem_of_mem_getLast? h

/-- A path from `a` to `b`, preceded by `u` and followed by `v`. -/
theorem isChain_cons_append_singleton {R : ℕ → ℕ → Prop} {Q : List ℕ} {u v a b : ℕ}
    (hQ : Q.IsChain R) (ha : Q.head? = some a) (hb : Q.getLast? = some b) (hua : R u a)
    (hbv : R b v) : (u :: (Q ++ [v])).IsChain R := by
  refine List.IsChain.cons (hQ.append (List.isChain_singleton v) ?_) ?_
  · intro x hx y hy
    rw [hb, Option.mem_some_iff] at hx
    simp only [List.head?_cons, Option.mem_some_iff] at hy
    subst hx
    subst hy
    exact hbv
  · intro y hy
    rw [List.head?_append, ha] at hy
    simp only [Option.some_or, Option.mem_some_iff] at hy
    subst hy
    exact hua

/-! ### Cycles -/

/-- The ends of the edges of `g` (a list containing every vertex). -/
def vertList (g : Graph) : List ℕ := g.flatMap fun e => [e.1, e.2]

theorem mem_vertList {g : Graph} {v : ℕ} (hv : IsVertex g v) : v ∈ vertList g := by
  obtain ⟨u, -, he⟩ := hv
  refine List.mem_flatMap.mpr ⟨edge u v, he, ?_⟩
  simp only [edge, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- `K` is a cycle of `g`: at least three distinct vertices, cyclically consecutive ones
adjacent. -/
def IsCyc (g : Graph) (K : List ℕ) : Prop :=
  3 ≤ K.length ∧ K.Nodup ∧ (K ++ K.take 1).IsChain (Adj g)

theorem isCyc_cons {g : Graph} {a : ℕ} {T : List ℕ} :
    IsCyc g (a :: T) ↔ 2 ≤ T.length ∧ (a :: T).Nodup ∧ (a :: (T ++ [a])).IsChain (Adj g) := by
  simp only [IsCyc, List.length_cons, List.take_succ_cons, List.take_zero, List.cons_append]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, h3⟩

/-- **Rotation invariance** of cycles. -/
theorem IsCyc.append_comm {g : Graph} {X Y : List ℕ} (h : IsCyc g (X ++ Y)) :
    IsCyc g (Y ++ X) := by
  obtain ⟨h3, hnd, hc⟩ := h
  refine ⟨by simpa [Nat.add_comm] using h3, List.perm_append_comm.nodup_iff.mp hnd, ?_⟩
  rcases X with _ | ⟨x, X⟩
  · simpa using hc
  rcases Y with _ | ⟨y, Y⟩
  · simpa using hc
  simp only [List.cons_append, List.append_assoc, List.take_succ_cons, List.take_zero]
    at hc ⊢
  rw [List.isChain_cons_split] at hc ⊢
  exact ⟨hc.2, hc.1⟩

theorem isVertex_of_isChain {g : Graph} :
    ∀ {a b : ℕ} {l : List ℕ}, (a :: b :: l).IsChain (Adj g) → ∀ v ∈ a :: b :: l, IsVertex g v
  | a, b, [], h, v, hv => by
    rw [List.isChain_pair] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨b, h.symm⟩
    · exact ⟨a, h⟩
  | a, b, c :: l, h, v, hv => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨b, h.1.symm⟩
    · exact isVertex_of_isChain h.2 v hv

/-- The entries of a cycle are vertices. -/
theorem IsCyc.isVertex {g : Graph} {K : List ℕ} (h : IsCyc g K) : ∀ v ∈ K, IsVertex g v := by
  obtain ⟨a, b, l, rfl⟩ : ∃ a b l, K = a :: b :: l := by
    match K, h.1 with
    | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
  have hc := (isCyc_cons.mp h).2.2
  simp only [List.cons_append] at hc
  intro v hv
  exact isVertex_of_isChain hc v (by simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto)

/-- A cycle is at most as long as the list of the ends of the edges. -/
theorem IsCyc.length_le {g : Graph} {K : List ℕ} (h : IsCyc g K) :
    K.length ≤ (vertList g).length :=
  (h.2.1.subperm fun v hv => mem_vertList (h.isVertex v hv)).length_le

theorem pathEdges_mem_of_isChain {g : Graph} :
    ∀ {w : List ℕ}, w.IsChain (Adj g) → ∀ e ∈ pathEdges w, e ∈ g
  | [], _, e, he => by simp [pathEdges] at he
  | [_], _, e, he => by simp [pathEdges] at he
  | a :: b :: rest, h, e, he => by
    rw [List.isChain_cons_cons] at h
    simp only [pathEdges, List.mem_cons] at he
    rcases he with rfl | he
    · exact h.1.2
    · exact pathEdges_mem_of_isChain h.2 e he

/-- A cycle is a cycle in the sense of Section 5. -/
theorem IsCyc.isCycle {g : Graph} {K : List ℕ} (h : IsCyc g K) : IsCycle g K.length K :=
  ⟨h.1, rfl, h.2.1, pathEdges_mem_of_isChain h.2.2⟩

/-- **Extension**: replacing the edge `uv` of a cycle `u :: v :: R` by a path `Q` from a
neighbour of `u` to a neighbour of `v` through vertices off the cycle gives the longer cycle
`v :: R ++ u :: Q`. -/
theorem IsCyc.extend {g : Graph} {u v : ℕ} {R Q : List ℕ} (hC : IsCyc g (u :: v :: R))
    (hQ : Q.IsChain (Adj g)) (hQnd : Q.Nodup) (hdisj : ∀ z ∈ Q, z ∉ u :: v :: R) {a b : ℕ}
    (ha : Q.head? = some a) (hb : Q.getLast? = some b) (hua : Adj g u a) (hbv : Adj g b v) :
    IsCyc g (v :: (R ++ u :: Q)) := by
  obtain ⟨-, hnd, hc⟩ := isCyc_cons.mp hC
  have hQne : Q ≠ [] := by rintro rfl; simp at ha
  refine isCyc_cons.mpr ⟨?_, ?_, ?_⟩
  · have := List.length_pos_of_ne_nil hQne
    simp only [List.length_append, List.length_cons]
    omega
  · simp only [List.nodup_cons, List.nodup_append, List.mem_cons] at hnd ⊢
    grind
  · simp only [List.append_assoc, List.cons_append]
    rw [List.isChain_cons_split]
    exact ⟨(List.isChain_cons_cons.mp hc).2, isChain_cons_append_singleton hQ ha hb hua hbv⟩

/-! ### `K_{2,3}` minors from five lists -/

/-- Five pairwise disjoint connected vertex lists, each of the first two joined by an edge to
each of the last three, are the branch sets of a `K_{2,3}` minor. -/
theorem hasMinor_k23_of {g : Graph} (b0 b1 b2 b3 b4 : List ℕ)
    (hd : ∀ v, (v ∈ b0 → v ∉ b1 ∧ v ∉ b2 ∧ v ∉ b3 ∧ v ∉ b4) ∧
      (v ∈ b1 → v ∉ b2 ∧ v ∉ b3 ∧ v ∉ b4) ∧ (v ∈ b2 → v ∉ b3 ∧ v ∉ b4) ∧ (v ∈ b3 → v ∉ b4))
    (c0 : ConnectedWithin g (· ∈ b0)) (c1 : ConnectedWithin g (· ∈ b1))
    (c2 : ConnectedWithin g (· ∈ b2)) (c3 : ConnectedWithin g (· ∈ b3))
    (c4 : ConnectedWithin g (· ∈ b4))
    (e02 : ∃ u ∈ b0, ∃ v ∈ b2, Adj g u v) (e03 : ∃ u ∈ b0, ∃ v ∈ b3, Adj g u v)
    (e04 : ∃ u ∈ b0, ∃ v ∈ b4, Adj g u v) (e12 : ∃ u ∈ b1, ∃ v ∈ b2, Adj g u v)
    (e13 : ∃ u ∈ b1, ∃ v ∈ b3, Adj g u v) (e14 : ∃ u ∈ b1, ∃ v ∈ b4, Adj g u v) :
    HasMinor g 5 k23 := by
  have ne : ∀ l l' : List ℕ, (∃ u ∈ l, ∃ v ∈ l', Adj g u v) → l ≠ [] ∧ l' ≠ [] := by
    rintro l l' ⟨u, hu, v, hv, -⟩
    exact ⟨List.ne_nil_of_mem hu, List.ne_nil_of_mem hv⟩
  refine ⟨fun i => [b0, b1, b2, b3, b4].getD i [], ?_, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · exact (ne _ _ e02).1
    · exact (ne _ _ e12).1
    · exact (ne _ _ e02).2
    · exact (ne _ _ e03).2
    · exact (ne _ _ e04).2
  · intro i j hi hj hij v hvi hvj
    obtain ⟨h0, h1, h2, h3⟩ := hd v
    interval_cases i <;> interval_cases j <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hvi hvj <;>
      first
        | exact hij rfl
        | exact (h0 hvi).1 hvj | exact (h0 hvi).2.1 hvj | exact (h0 hvi).2.2.1 hvj
        | exact (h0 hvi).2.2.2 hvj | exact (h1 hvi).1 hvj | exact (h1 hvi).2.1 hvj
        | exact (h1 hvi).2.2 hvj | exact (h2 hvi).1 hvj | exact (h2 hvi).2 hvj
        | exact h3 hvi hvj
        | exact (h0 hvj).1 hvi | exact (h0 hvj).2.1 hvi | exact (h0 hvj).2.2.1 hvi
        | exact (h0 hvj).2.2.2 hvi | exact (h1 hvj).1 hvi | exact (h1 hvj).2.1 hvi
        | exact (h1 hvj).2.2 hvi | exact (h2 hvj).1 hvi | exact (h2 hvj).2 hvi
        | exact h3 hvj hvi
  · intro i hi
    interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ]
    · exact c0
    · exact c1
    · exact c2
    · exact c3
    · exact c4
  · have conv : ∀ l l' : List ℕ, (∃ u ∈ l, ∃ v ∈ l', Adj g u v) →
        ∃ u v, u ∈ l ∧ v ∈ l' ∧ Adj g u v := by
      rintro l l' ⟨u, hu, v, hv, h⟩
      exact ⟨u, v, hu, hv, h⟩
    intro e he
    simp only [k23, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ]
    · exact conv _ _ e02
    · exact conv _ _ e03
    · exact conv _ _ e04
    · exact conv _ _ e12
    · exact conv _ _ e13
    · exact conv _ _ e14

end K23Struct

end STACS2027
