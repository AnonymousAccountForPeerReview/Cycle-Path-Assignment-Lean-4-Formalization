module

public import Outerplanar.WeakDualBij
public import Outerplanar.DPCorrect
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# legacy cycle-count bound: few `k`-cycles enclose a face or contain an edge

Appendix F, legacy cycle-count bound (`lem:face_cycle_bound`): for `k ≥ 3`, every bounded face is enclosed by
at most `4^k` simple `k`-cycles and every edge lies on at most `2 · 4^k` of them. In the polygon
model the simple `k`-cycles are the convex `k`-cycles (`convexList g n k`, each simple
`k`-cycle once up to its edge set), a face is a segment `s`, and a cycle `u` encloses `s` when
`s ∈ encl g n u` (`encl u = ψ⁻¹(u)` by Lemma 29, `IsPolygon.cycle_subtree_bij`).

Instead of the paper's breadth-first bit-string encoding of the subtrees `ψ⁻¹(u) ∋ s`, we bound
a generating function, following the face decomposition of region paths
(`IsPolygon.isRPath_iff_joins`): with the weight `wt p = (1/4)^(|p| - 1)` of a path with
`|p| - 1` edges,

* the region paths of an edge `(a, b)` have total weight at most `1/2` (`sum_rpSet_le`): a side
  has one region path, of weight `1/4`; the region paths of a segment are the edge itself
  (weight `1/4`) and the concatenations along the `d - 1 ≥ 2` slots of its face, whose total
  weight is the product of the slot weights (`sum_jpSet_le`), at most `(1/2)^2`;
* the region paths of a segment `t ⊋ s` enclosing `s` descend into the child `c` of `t` above
  `s`, so their weight is at most half of that of the region paths of `c` enclosing `s`
  (`encSum_le_child`); the region paths of `s` enclosing `s` weigh at most `1/4`;
* summing over the chain of segments from `s` up to the root, the convex cycles enclosing `s`
  (each a region path of its top) weigh at most `1/2` in total (`chainSum_add_le`), so there
  are at most `4^(k-1)/2 ≤ 4^k` of length `k` (`face_cycle_bound`);
* an edge lies on at most two faces, and a cycle through it encloses one of them
  (`bdry_encl`), whence `edge_cycle_bound`.
-/

@[expose] public section

namespace STACS2027

open IsPolygon

variable {g : Graph} {n : ℕ}

instance (g : Graph) (a b : ℕ) (p : List ℕ) : Decidable (IsRPath g a b p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The weight `(1/4)^(|p| - 1)` of a path with `|p| - 1` edges. -/
def wt (p : List ℕ) : ℚ := (1 / 4 : ℚ) ^ (p.length - 1)

theorem wt_nonneg (p : List ℕ) : 0 ≤ wt p := by unfold wt; positivity

/-- The region paths from `a` to `b`, as a finite set. -/
def rpSet (g : Graph) (a b : ℕ) : Finset (List ℕ) :=
  ((List.range' a (b + 1 - a)).sublists.filter fun p => decide (IsRPath g a b p)).toFinset

theorem mem_rpSet {a b : ℕ} {p : List ℕ} : p ∈ rpSet g a b ↔ IsRPath g a b p := by
  simp only [rpSet, List.mem_toFinset, List.mem_filter, List.mem_sublists, decide_eq_true_eq]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hnd : p.Nodup := h.pairwise.imp fun h => Nat.ne_of_lt h
  have hsub : p ⊆ List.range' a (b + 1 - a) := by
    intro x hx
    have := h.bounds hx
    rw [List.mem_range'_1]
    omega
  exact List.sublist_of_subperm_of_pairwise (hnd.subperm hsub) h.pairwise
    (List.pairwise_lt_range' 1 (by omega))

/-- The concatenations of region paths along consecutive entries of `vs`, as a finite set. -/
def jpSet (g : Graph) : List ℕ → Finset (List ℕ)
  | [] => ∅
  | [x] => {[x]}
  | x :: y :: rest =>
    ((rpSet g x y) ×ˢ (jpSet g (y :: rest))).image fun pq => pq.1 ++ pq.2.tail

theorem mem_jpSet : ∀ {vs p : List ℕ}, p ∈ jpSet g vs ↔ Joins g vs p
  | [], p => by simp [jpSet, Joins]
  | [x], p => by simp [jpSet, Joins]
  | x :: y :: rest, p => by
    simp only [jpSet, Finset.mem_image, Finset.mem_product, Joins, mem_rpSet, Prod.exists]
    constructor
    · rintro ⟨p₀, q, ⟨hp, hq⟩, rfl⟩
      exact ⟨p₀, q, hp, mem_jpSet.mp hq, rfl⟩
    · rintro ⟨p₀, q, hp, hq, rfl⟩
      exact ⟨p₀, q, ⟨hp, mem_jpSet.mpr hq⟩, rfl⟩

/-- A concatenation along `y :: rest` is a strictly increasing list starting at `y`. -/
theorem Joins.head_pairwise {y : ℕ} {rest q : List ℕ} (hq : Joins g (y :: rest) q) :
    q = y :: q.tail ∧ q.Pairwise (· < ·) := by
  have hh := hq.head?
  have hr : IsRPath g y ((y :: rest).getLast (List.cons_ne_nil _ _)) q :=
    hq.isRPath rfl (List.getLast?_eq_some_getLast _)
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hh
  exact ⟨rfl, hr.pairwise⟩

/-- The weight of a concatenation is the product of the weights. -/
theorem wt_append {p q : List ℕ} (hp : p ≠ []) (hq : q ≠ []) :
    wt (p ++ q.tail) = wt p * wt q := by
  unfold wt
  rw [← pow_add]
  congr 1
  have h1 := List.length_pos_iff.mpr hp
  have h2 := List.length_pos_iff.mpr hq
  simp only [List.length_append, List.length_tail]
  omega

theorem sum_insert_le {s : Finset (List ℕ)} {a : List ℕ} {f : List ℕ → ℚ}
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ insert a s, f x ≤ f a + ∑ x ∈ s, f x := by
  by_cases h : a ∈ s
  · rw [Finset.insert_eq_of_mem h]
    linarith [hf a]
  · rw [Finset.sum_insert h]

/-- **The weight of the concatenations** along `vs` is at most `(1/2)^(|vs| - 1)` when every
slot has region paths of total weight at most `1/2`. -/
theorem sum_jpSet_le : ∀ (vs : List ℕ), vs ≠ [] →
    (∀ x y, [x, y] <:+: vs → ∑ p ∈ rpSet g x y, wt p ≤ 1 / 2) →
    ∑ p ∈ jpSet g vs, wt p ≤ (1 / 2) ^ (vs.length - 1)
  | [], h, _ => absurd rfl h
  | [x], _, _ => by simp [jpSet, wt]
  | x :: y :: rest, _, h => by
    simp only [jpSet]
    have ih := sum_jpSet_le (y :: rest) (List.cons_ne_nil _ _)
      (fun x' y' hi => h x' y' (List.infix_cons hi))
    calc ∑ p ∈ ((rpSet g x y) ×ˢ (jpSet g (y :: rest))).image (fun pq => pq.1 ++ pq.2.tail),
          wt p
        ≤ ∑ pq ∈ (rpSet g x y) ×ˢ (jpSet g (y :: rest)), wt (pq.1 ++ pq.2.tail) :=
          Finset.sum_image_le_of_nonneg fun _ _ => wt_nonneg _
      _ = ∑ pq ∈ (rpSet g x y) ×ˢ (jpSet g (y :: rest)), wt pq.1 * wt pq.2 := by
          refine Finset.sum_congr rfl fun pq hpq => ?_
          rw [Finset.mem_product] at hpq
          have hp := mem_rpSet.mp hpq.1
          have hq := (mem_jpSet.mp hpq.2).head_pairwise.1
          exact wt_append (List.ne_nil_of_mem hp.head_mem) (by rw [hq]; simp)
      _ = (∑ p ∈ rpSet g x y, wt p) * ∑ q ∈ jpSet g (y :: rest), wt q := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ (1 / 2) * (1 / 2) ^ ((y :: rest).length - 1) :=
          mul_le_mul (h x y ⟨[], rest, rfl⟩) ih (Finset.sum_nonneg fun _ _ => wt_nonneg _)
            (by norm_num)
      _ = (1 / 2) ^ ((x :: y :: rest).length - 1) := by
          simp only [List.length_cons, Nat.add_sub_cancel]
          ring

namespace IsPolygon

/-- **The region paths of an edge weigh at most `1/2`.** -/
theorem sum_rpSet_le (hP : IsPolygon g n) :
    ∀ a b, a < b → Adj g a b → ∑ p ∈ rpSet g a b, wt p ≤ 1 / 2 := by
  intro a b
  induction hm : b - a using Nat.strong_induction_on generalizing a b with
  | _ m ih =>
    intro hab hadj
    by_cases hside : b = a + 1
    · subst hside
      have : rpSet g a (a + 1) = {[a, a + 1]} := by
        ext p
        rw [mem_rpSet, isRPath_side_iff, Finset.mem_singleton]
        exact ⟨fun h => h.1, fun h => ⟨h, hadj⟩⟩
      rw [this, Finset.sum_singleton]
      norm_num [wt]
    · have hs : (a, b) ∈ segs g n := hP.mem_segs.mpr ⟨hadj, by simp only; omega⟩
      have hsub : rpSet g a b ⊆ insert [a, b] (jpSet g (faceVerts g n (a, b))) := by
        intro p hp
        rcases (hP.isRPath_iff_joins hs).mp (mem_rpSet.mp hp) with h | h
        · rw [h]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (mem_jpSet.mpr h)
      have hd := hP.three_le_length_faceVerts hs
      have hJ := sum_jpSet_le (g := g) (faceVerts g n (a, b))
        (List.ne_nil_of_length_pos (by omega)) (fun x y hi => by
          have hlt := hP.infix_faceVerts_lt hs hi
          exact ih (y - x) (by simp only at hlt; omega) x y rfl hlt.2.1
            (hP.adj_of_infix_faceVerts hs hi))
      have hpow : ((1 : ℚ) / 2) ^ ((faceVerts g n (a, b)).length - 1) ≤ (1 / 2) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      calc ∑ p ∈ rpSet g a b, wt p
          ≤ ∑ p ∈ insert [a, b] (jpSet g (faceVerts g n (a, b))), wt p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => wt_nonneg _
        _ ≤ wt [a, b] + ∑ p ∈ jpSet g (faceVerts g n (a, b)), wt p := sum_insert_le wt_nonneg
        _ ≤ 1 / 4 + (1 / 2) ^ 2 := by
            have : wt [a, b] = 1 / 4 := by norm_num [wt]
            linarith
        _ = 1 / 2 := by norm_num

end IsPolygon

/-! ### Region paths enclosing a face -/

/-- The weight of the region paths of the segment `t` enclosing the face `s`. -/
def encSum (g : Graph) (n : ℕ) (s t : ℕ × ℕ) : ℚ :=
  ∑ p ∈ (rpSet g t.1 t.2).filter (fun p => s ∈ encl g n p), wt p

theorem encSum_nonneg (s t : ℕ × ℕ) : 0 ≤ encSum g n s t :=
  Finset.sum_nonneg fun _ _ => wt_nonneg _

namespace IsPolygon

/-- A path enclosing a face has at least three entries. -/
theorem three_le_of_mem_encl (hP : IsPolygon g n) {s : ℕ × ℕ} {p : List ℕ}
    (h : s ∈ encl g n p) : 3 ≤ p.length ∨ ¬ p.Nodup := by
  by_cases hnd : p.Nodup
  · left
    have hsub := (mem_encl.mp h).2
    have hs := (mem_encl.mp h).1
    obtain ⟨z, hz, hz1, hz2⟩ := hP.exists_inner_faceVert hs
    have hs' := hP.mem_segs.mp hs
    have h3 : [s.1, z, s.2] ⊆ p := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hsub _ (left_mem_faceVerts (by omega))
      · exact hsub _ hz
      · exact hsub _ (right_mem_faceVerts (by omega))
    have hnd3 : [s.1, z, s.2].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true]
      omega
    simpa using hnd3.length_le_of_subset h3
  · exact Or.inr hnd

/-- A region path of a segment `t` enclosing a face is a concatenation along the face of `t`. -/
theorem filter_rpSet_subset (hP : IsPolygon g n) {s t : ℕ × ℕ} (ht : t ∈ segs g n) :
    (rpSet g t.1 t.2).filter (fun p => s ∈ encl g n p) ⊆
      (jpSet g (faceVerts g n t)).filter (fun p => s ∈ encl g n p) := by
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨?_, hp.2⟩
  have hr := mem_rpSet.mp hp.1
  rcases (hP.isRPath_iff_joins ht).mp hr with h | h
  · exfalso
    rcases hP.three_le_of_mem_encl hp.2 with h3 | h3
    · rw [h] at h3
      simp at h3
    · exact h3 (hr.pairwise.imp fun h => Nat.ne_of_lt h)
  · exact mem_jpSet.mpr h

end IsPolygon

/-- **Concatenations enclosing a face** weigh at most `C (1/2)^(|vs| - 2)`, when the face `s`
lies within a slot of `vs` whose region paths enclosing `s` weigh at most `C`. -/
theorem sum_jpSet_encl_le (s : ℕ × ℕ) (C : ℚ) (hC : 0 ≤ C) : ∀ (vs : List ℕ),
    vs.Pairwise (· < ·) →
    (∀ x y, [x, y] <:+: vs → ∑ p ∈ rpSet g x y, wt p ≤ 1 / 2) →
    (∀ x y, [x, y] <:+: vs → Within s (x, y) →
      ∑ p ∈ (rpSet g x y).filter (fun p => s ∈ encl g n p), wt p ≤ C) →
    (∃ x y, [x, y] <:+: vs ∧ Within s (x, y)) →
    ∑ p ∈ (jpSet g vs).filter (fun p => s ∈ encl g n p), wt p ≤ C * (1 / 2) ^ (vs.length - 2)
  | [], _, _, _, ⟨x, y, hi, _⟩ => by
    have := hi.length_le
    simp at this
  | [_], _, _, _, ⟨x, y, hi, _⟩ => by
    have := hi.length_le
    simp at this
  | x :: y :: rest, hs, h1, h2, hex => by
    simp only [jpSet]
    rw [Finset.filter_image]
    refine (Finset.sum_image_le_of_nonneg fun _ _ => wt_nonneg _).trans ?_
    have hxy : x < y := (List.pairwise_cons.mp hs).1 y (by simp)
    have hrest := (List.pairwise_cons.mp hs).2
    have hJ1 := sum_jpSet_le (g := g) (y :: rest) (List.cons_ne_nil _ _)
      (fun x' y' hi => h1 x' y' (List.infix_cons hi))
    have hR := h1 x y ⟨[], rest, rfl⟩
    -- the weight of a product filtered by a condition on one factor
    have hprod : ∀ (P Q : List ℕ → Prop) [DecidablePred P] [DecidablePred Q],
        (∀ pq ∈ (rpSet g x y) ×ˢ (jpSet g (y :: rest)), s ∈ encl g n (pq.1 ++ pq.2.tail) →
          P pq.1 ∧ Q pq.2) →
        ∑ pq ∈ ((rpSet g x y) ×ˢ (jpSet g (y :: rest))).filter
            (fun pq => s ∈ encl g n (pq.1 ++ pq.2.tail)), wt (pq.1 ++ pq.2.tail) ≤
          (∑ p ∈ (rpSet g x y).filter P, wt p) * ∑ q ∈ (jpSet g (y :: rest)).filter Q, wt q := by
      intro P Q _ _ hPQ
      rw [Finset.sum_mul_sum, ← Finset.sum_product' (f := fun p q => wt p * wt q)]
      calc _ = ∑ pq ∈ ((rpSet g x y) ×ˢ (jpSet g (y :: rest))).filter
            (fun pq => s ∈ encl g n (pq.1 ++ pq.2.tail)), wt pq.1 * wt pq.2 := by
            refine Finset.sum_congr rfl fun pq hpq => ?_
            rw [Finset.mem_filter, Finset.mem_product] at hpq
            have hp := mem_rpSet.mp hpq.1.1
            have hq := (mem_jpSet.mp hpq.1.2).head_pairwise.1
            exact wt_append (List.ne_nil_of_mem hp.head_mem) (by rw [hq]; simp)
        _ ≤ _ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro pq hpq
              rw [Finset.mem_filter, Finset.mem_product] at hpq
              rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
              have := hPQ pq (Finset.mem_product.mpr hpq.1) hpq.2
              exact ⟨⟨hpq.1.1, this.1⟩, hpq.1.2, this.2⟩
            · intro _ _ _
              exact mul_nonneg (wt_nonneg _) (wt_nonneg _)
    by_cases hA : Within s (x, y)
    · -- the face lies in the first slot
      refine (hprod (fun p => s ∈ encl g n p) (fun _ => True) ?_).trans ?_
      · intro pq hpq henc
        rw [Finset.mem_product] at hpq
        obtain ⟨hq0, hqs⟩ := (mem_jpSet.mp hpq.2).head_pairwise
        refine ⟨mem_encl.mpr ⟨(mem_encl.mp henc).1, fun z hz => ?_⟩, trivial⟩
        have hz' := (mem_encl.mp henc).2 z hz
        have hzb := (mem_faceVerts.mp hz).2.1
        simp only [Within] at hA
        rcases List.mem_append.mp hz' with h | h
        · exact h
        · exfalso
          rw [hq0] at hqs
          have := (List.pairwise_cons.mp hqs).1 z h
          omega
      · rw [Finset.filter_true_of_mem (fun _ _ => trivial)]
        calc (∑ p ∈ (rpSet g x y).filter (fun p => s ∈ encl g n p), wt p) *
              ∑ q ∈ jpSet g (y :: rest), wt q
            ≤ C * (1 / 2) ^ ((y :: rest).length - 1) :=
              mul_le_mul (h2 x y ⟨[], rest, rfl⟩ hA) hJ1
                (Finset.sum_nonneg fun _ _ => wt_nonneg _) hC
          _ = C * (1 / 2) ^ ((x :: y :: rest).length - 2) := by simp
    · -- the face lies in a later slot
      obtain ⟨x', y', hi, hw⟩ := hex
      have hi' : [x', y'] <:+: y :: rest := by
        rcases List.infix_cons_iff.mp hi with h | h
        · exfalso
          obtain ⟨t, ht⟩ := h
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
          obtain ⟨rfl, rfl, -⟩ := ht
          exact hA hw
        · exact h
      have hx'y : y ≤ x' := by
        have hx'm : x' ∈ y :: rest := hi'.subset (by simp)
        rcases List.mem_cons.mp hx'm with h | h
        · omega
        · exact ((List.pairwise_cons.mp hrest).1 x' h).le
      have hsy : y ≤ s.1 := by simp only [Within] at hw; omega
      have hlen : 2 ≤ (y :: rest).length := hi'.length_le
      have ih := sum_jpSet_encl_le s C hC (y :: rest) hrest
        (fun x' y' hi => h1 x' y' (List.infix_cons hi))
        (fun x' y' hi => h2 x' y' (List.infix_cons hi)) ⟨x', y', hi', hw⟩
      refine (hprod (fun _ => True) (fun q => s ∈ encl g n q) ?_).trans ?_
      · intro pq hpq henc
        rw [Finset.mem_product] at hpq
        obtain ⟨hq0, -⟩ := (mem_jpSet.mp hpq.2).head_pairwise
        have hp := mem_rpSet.mp hpq.1
        refine ⟨trivial, mem_encl.mpr ⟨(mem_encl.mp henc).1, fun z hz => ?_⟩⟩
        have hz' := (mem_encl.mp henc).2 z hz
        have hza := (mem_faceVerts.mp hz).1
        rcases List.mem_append.mp hz' with h | h
        · have := (hp.bounds h).2
          have hzy : z = y := by omega
          rw [hq0, hzy]
          exact List.mem_cons_self
        · exact List.mem_of_mem_tail h
      · rw [Finset.filter_true_of_mem (fun _ _ => trivial)]
        calc (∑ p ∈ rpSet g x y, wt p) *
              ∑ q ∈ (jpSet g (y :: rest)).filter (fun q => s ∈ encl g n q), wt q
            ≤ (1 / 2) * (C * (1 / 2) ^ ((y :: rest).length - 2)) :=
              mul_le_mul hR ih (Finset.sum_nonneg fun _ _ => wt_nonneg _) (by norm_num)
          _ = C * (1 / 2) ^ ((x :: y :: rest).length - 2) := by
              simp only [List.length_cons] at hlen ⊢
              obtain ⟨j, hj⟩ : ∃ j, rest.length = j + 1 := ⟨rest.length - 1, by omega⟩
              rw [hj, show j + 1 + 1 + 1 - 2 = j + 1 by omega,
                show j + 1 + 1 - 2 = j by omega, pow_succ]
              ring

namespace IsPolygon

/-- The region paths of a segment `s` enclosing `s` weigh at most `1/4`. -/
theorem encSum_self_le (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    encSum g n s s ≤ 1 / 4 := by
  have hd := hP.three_le_length_faceVerts hs
  have hJ := sum_jpSet_le (g := g) (faceVerts g n s)
    (List.ne_nil_of_length_pos (by omega)) (fun x y hi => hP.sum_rpSet_le x y
      (hP.infix_faceVerts_lt hs hi).2.1 (hP.adj_of_infix_faceVerts hs hi))
  have hpow : ((1 : ℚ) / 2) ^ ((faceVerts g n s).length - 1) ≤ (1 / 2) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc encSum g n s s
      ≤ ∑ p ∈ (jpSet g (faceVerts g n s)).filter (fun p => s ∈ encl g n p), wt p :=
        Finset.sum_le_sum_of_subset_of_nonneg (hP.filter_rpSet_subset hs)
          fun _ _ _ => wt_nonneg _
    _ ≤ ∑ p ∈ jpSet g (faceVerts g n s), wt p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => wt_nonneg _
    _ ≤ 1 / 4 := by norm_num at hpow ⊢; linarith

/-- **Descending to the child above `s` halves the weight**: the region paths of a segment `t`
enclosing a face `s` strictly below it weigh at most half as much as the region paths of the
child `c` of `t` containing `s` that enclose `s`. -/
theorem encSum_le_child (hP : IsPolygon g n) {s t c : ℕ × ℕ} (hs : s ∈ segs g n)
    (ht : t ∈ segs g n) (hc : c ∈ segs g n) (hch : IsChild g n t c) (hsc : Within s c) :
    encSum g n s t ≤ encSum g n s c / 2 := by
  have hd := hP.three_le_length_faceVerts ht
  have hs' := hP.mem_segs.mp hs
  have hci := hP.infix_faceVerts_of_child hc hch
  have hJ := sum_jpSet_encl_le (g := g) (n := n) s (encSum g n s c) (encSum_nonneg _ _)
    (faceVerts g n t) faceVerts_pairwise
    (fun x y hi => hP.sum_rpSet_le x y (hP.infix_faceVerts_lt ht hi).2.1
      (hP.adj_of_infix_faceVerts ht hi))
    (fun x y hi hw => by
      obtain ⟨hx, hy, hxy, hgap⟩ := (infix_pair_iff faceVerts_pairwise).mp hi
      rcases hP.face_gap hx hy hxy hgap with h | ⟨hxyseg, hxych⟩
      · simp only [Within] at hw
        omega
      · have : (x, y) = c := by
          by_contra hne
          exact hP.child_disjoint hxyseg hc hxych hch hne hs hw hsc
        rw [← this]
        exact le_rfl)
    ⟨c.1, c.2, hci, hsc⟩
  have hpow : ((1 : ℚ) / 2) ^ ((faceVerts g n t).length - 2) ≤ 1 / 2 := by
    calc ((1 : ℚ) / 2) ^ ((faceVerts g n t).length - 2) ≤ (1 / 2) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  calc encSum g n s t
      ≤ ∑ p ∈ (jpSet g (faceVerts g n t)).filter (fun p => s ∈ encl g n p), wt p :=
        Finset.sum_le_sum_of_subset_of_nonneg (hP.filter_rpSet_subset ht)
          fun _ _ _ => wt_nonneg _
    _ ≤ encSum g n s c * (1 / 2) ^ ((faceVerts g n t).length - 2) := hJ
    _ ≤ encSum g n s c * (1 / 2) :=
        mul_le_mul_of_nonneg_left hpow (encSum_nonneg _ _)
    _ = encSum g n s c / 2 := by ring

end IsPolygon

/-- The weight of the region paths enclosing `s` of all segments from `s` up to `t`. -/
def chainSum (g : Graph) (n : ℕ) (s t : ℕ × ℕ) : ℚ :=
  ∑ t' ∈ (segs g n).filter (fun t' => Within s t' ∧ Within t' t), encSum g n s t'

namespace IsPolygon

/-- **The chain bound**: for segments `s ⊆ t`, the region paths enclosing `s` of the
segments between `s` and `t`, together with those of `t` once more, weigh at most `1/2`. -/
theorem chainSum_add_le (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    ∀ t ∈ segs g n, Within s t → chainSum g n s t + encSum g n s t ≤ 1 / 2 := by
  intro t
  induction hm : segSize t using Nat.strong_induction_on generalizing t with
  | _ m ih =>
    intro ht hst
    have hs' := hP.mem_segs.mp hs
    by_cases hts : t = s
    · subst hts
      have : (segs g n).filter (fun t' => Within t t' ∧ Within t' t) = {t} := by
        ext t'
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h1, h2⟩
          exact Within.antisymm h2 h1
        · rintro rfl
          exact ⟨ht, Within.refl _, Within.refl _⟩
      rw [chainSum, this, Finset.sum_singleton]
      have := hP.encSum_self_le ht
      linarith
    · obtain ⟨c, hc, hch, hsc⟩ := hP.exists_child ht hs hst (Ne.symm hts)
      have hsplit : (segs g n).filter (fun t' => Within s t' ∧ Within t' t) =
          insert t ((segs g n).filter (fun t' => Within s t' ∧ Within t' c)) := by
        ext t'
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨ht', h1, h2⟩
          rcases hP.nested_of_within ht' hc (by omega) h1 hsc with w | w
          · exact Or.inr ⟨ht', h1, w⟩
          · rcases hch.2.2 t' ht' w h2 with e | e
            · exact Or.inr ⟨ht', h1, by rw [e]; exact Within.refl _⟩
            · exact Or.inl e
        · rintro (rfl | ⟨ht', h1, h2⟩)
          · exact ⟨ht, hst, Within.refl _⟩
          · exact ⟨ht', h1, h2.trans hch.2.1⟩
      have hnot : t ∉ (segs g n).filter (fun t' => Within s t' ∧ Within t' c) := by
        simp only [Finset.mem_filter, not_and]
        intro _ _ h
        exact hch.1 (Within.antisymm hch.2.1 h)
      have hchain : chainSum g n s t = encSum g n s t + chainSum g n s c := by
        rw [chainSum, hsplit, Finset.sum_insert hnot]
        rfl
      have hih := ih (segSize c) (by rw [← hm]; exact hP.child_size_lt hc hch) c rfl hc hsc
      have hhalf := hP.encSum_le_child hs ht hc hch hsc
      rw [hchain]
      linarith

/-! ### legacy cycle-count bound -/

/-- A filter by a disjunction is at most the sum of the filters. -/
theorem length_filter_le_add {α : Type*} (L : List α) (P Q R : α → Bool)
    (h : ∀ x ∈ L, P x = true → Q x = true ∨ R x = true) :
    (L.filter P).length ≤ (L.filter Q).length + (L.filter R).length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.filter_cons]
    by_cases hP : P x = true <;> by_cases hQ : Q x = true <;> by_cases hR : R x = true <;>
      simp_all <;> omega

/-- The generating-function bound: twice the number of convex `k`-cycles enclosing a
bounded face is at most `4^(k-1)`. -/
theorem face_cycle_half_bound (hP : IsPolygon g n) {k : ℕ} (_hk : 3 ≤ k) (s : ℕ × ℕ) :
    ((convexList g n k).filter fun u => s ∈ encl g n u).length * 2 ≤ 4 ^ (k - 1) := by
  classical
  by_cases hs : s ∈ segs g n
  swap
  · have : (convexList g n k).filter (fun u => s ∈ encl g n u) = [] := by
      rw [List.filter_eq_nil_iff]
      intro u _ h
      exact hs (encl_subset (of_decide_eq_true h))
    rw [this]
    simp
  set L := (convexList g n k).filter fun u => s ∈ encl g n u
  have hL : L.Nodup := convexList_nodup.filter _
  have hmemL : ∀ u ∈ L, ConvexCycle g u ∧ u.length = k ∧ s ∈ encl g n u := by
    intro u hu
    rw [List.mem_filter] at hu
    exact ⟨(hP.mem_convexList.mp hu.1).1, (hP.mem_convexList.mp hu.1).2, of_decide_eq_true hu.2⟩
  let T := (segs g n).filter (fun t' => Within s t' ∧ Within t' (0, n - 1))
  have hsub : L.toFinset ⊆ T.biUnion fun t => (rpSet g t.1 t.2).filter (fun p => s ∈ encl g n p) := by
    intro u hu
    rw [List.mem_toFinset] at hu
    obtain ⟨hc, -, he⟩ := hmemL u hu
    obtain ⟨a, b, hr, hab, hl⟩ := hP.exists_top hc
    have hseg := (hP.top_mem_encl hr hab hl).1
    rw [Finset.mem_biUnion]
    refine ⟨(a, b), ?_, ?_⟩
    · simp only [T, Finset.mem_filter]
      exact ⟨hseg, ((hP.mem_encl_iff hr hab hs).mp he).1, hP.within_root hseg⟩
    · rw [Finset.mem_filter]
      exact ⟨mem_rpSet.mpr hr, he⟩
  have hdisj : (T : Set (ℕ × ℕ)).PairwiseDisjoint
      fun t => (rpSet g t.1 t.2).filter (fun p => s ∈ encl g n p) := by
    intro t _ t' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    have h1 := mem_rpSet.mp (Finset.mem_filter.mp hp).1
    have h2 := mem_rpSet.mp (Finset.mem_filter.mp hp').1
    apply hne
    have e1 : t.1 = t'.1 := Option.some.inj (h1.1.symm.trans h2.1)
    have e2 : t.2 = t'.2 := Option.some.inj (h1.2.1.symm.trans h2.2.1)
    exact Prod.ext e1 e2
  have hroot := hP.chainSum_add_le hs (0, n - 1) hP.root_mem_segs (hP.within_root hs)
  have hsum : (L.length : ℚ) * (1 / 4) ^ (k - 1) ≤ 1 / 2 := by
    calc (L.length : ℚ) * (1 / 4) ^ (k - 1) = ∑ u ∈ L.toFinset, wt u := by
          rw [Finset.sum_congr rfl (g := fun _ => (1 / 4 : ℚ) ^ (k - 1)), Finset.sum_const,
            List.toFinset_card_of_nodup hL, nsmul_eq_mul]
          intro u hu
          rw [List.mem_toFinset] at hu
          rw [wt, (hmemL u hu).2.1]
      _ ≤ ∑ u ∈ T.biUnion (fun t => (rpSet g t.1 t.2).filter (fun p => s ∈ encl g n p)), wt u :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => wt_nonneg _
      _ = chainSum g n s (0, n - 1) := by
          rw [Finset.sum_biUnion hdisj]
          rfl
      _ ≤ 1 / 2 := by linarith [encSum_nonneg (g := g) (n := n) s (0, n - 1)]
  have hpos : (0 : ℚ) < 4 ^ (k - 1) := by positivity
  have h' : (L.length : ℚ) * (1 / 4) ^ (k - 1) * 4 ^ (k - 1) ≤ 1 / 2 * 4 ^ (k - 1) :=
    mul_le_mul_of_nonneg_right hsum hpos.le
  rw [mul_assoc, ← mul_pow, show (1 / 4 : ℚ) * 4 = 1 by norm_num, one_pow, mul_one] at h'
  have hfinal : (L.length : ℚ) * 2 ≤ 4 ^ (k - 1) := by linarith
  exact_mod_cast hfinal

/-- Every bounded face is enclosed by at most `4^k` simple `k`-cycles. -/
theorem face_cycle_bound (hP : IsPolygon g n) {k : ℕ} (hk : 3 ≤ k) (s : ℕ × ℕ) :
    ((convexList g n k).filter fun u => s ∈ encl g n u).length ≤ 4 ^ k := by
  have hh := hP.face_cycle_half_bound hk s
  have hp : 4 ^ (k - 1) ≤ (4 : ℕ) ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- An edge of `g` lies on at most two faces. -/
theorem faces_le_two (hP : IsPolygon g n) {e : ℕ × ℕ} (he : Adj g e.1 e.2 ∧ e.1 < e.2) :
    ∃ f₁ f₂, ∀ s ∈ segs g n, e ∈ faceEdges g n s → s = f₁ ∨ s = f₂ := by
  by_cases hside : e.2 = e.1 + 1
  · obtain ⟨o, ho, hoW, homin⟩ := hP.exists_own he.1 he.2
    refine ⟨o, o, fun s hs hes => Or.inl ?_⟩
    obtain ⟨a, b⟩ := e
    simp only at hside
    subst hside
    have h' := (hP.faces_of_side hs).mp hes
    exact Within.antisymm (h'.2 o ho hoW) (homin s hs h'.1)
  · have hes : e ∈ segs g n := hP.mem_segs.mpr ⟨he.1, by omega⟩
    by_cases hroot : e = (0, n - 1)
    · refine ⟨e, e, fun s hs h => Or.inl ?_⟩
      rcases (hP.faces_of_seg hes hs).mp h with h | h
      · exact h
      · rw [hroot] at h
        exact absurd h (hP.not_isChild_root hs)
    · obtain ⟨p, hp, hc⟩ := hP.exists_parent hes hroot
      refine ⟨e, p, fun s hs h => ?_⟩
      rcases (hP.faces_of_seg hes hs).mp h with h | h
      · exact Or.inl h
      · exact Or.inr (hP.parent_unique hes hs hp h hc)

/-- **legacy cycle-count bound, edges** (`lem:edge_cycle_bound`): for `k ≥ 3`, every edge `e` of `g` lies on at
most `2 · 4^k` simple `k`-cycles (convex `k`-cycles): a cycle through `e` encloses one of the
at most two faces incident to `e` (`bdry_encl`). -/
theorem edge_cycle_bound (hP : IsPolygon g n) {k : ℕ} (hk : 3 ≤ k) {e : ℕ × ℕ}
    (he : e ∈ polyEdges g n) :
    ((convexList g n k).filter fun u => e ∈ cycleEdges u).length ≤ 2 * 4 ^ k := by
  obtain ⟨f₁, f₂, hf⟩ := hP.faces_le_two ((hP.mem_polyEdges).mp he)
  have h1 := hP.face_cycle_bound hk f₁
  have h2 := hP.face_cycle_bound hk f₂
  refine le_trans (length_filter_le_add _ _ (fun u => decide (f₁ ∈ encl g n u))
    (fun u => decide (f₂ ∈ encl g n u)) ?_) (by omega)
  intro u hu heu
  have hc := (hP.mem_convexList.mp hu).1
  have hb : e ∈ bdry g n (encl g n u) := by
    rw [hP.bdry_encl hc, List.mem_toFinset]
    exact of_decide_eq_true heu
  rw [mem_bdry] at hb
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hb
    exact Nat.not_odd_zero hb)
  rw [Finset.mem_filter] at hs
  rcases hf s (encl_subset hs.1) hs.2 with rfl | rfl
  · exact Or.inl (decide_eq_true hs.1)
  · exact Or.inr (decide_eq_true hs.1)

end IsPolygon

end STACS2027
