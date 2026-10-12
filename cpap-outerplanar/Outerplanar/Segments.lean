module

public import Outerplanar.Convex
public import Outerplanar.TreeDP
import Mathlib.Tactic

/-!
# The segment tree of a polygon (the rooted weak dual)

The *segments* of a polygon `g` on `0, …, n - 1` are its edges `(a, b)`, `a + 2 ≤ b`: the
chords and the outer edge `(0, n - 1)`. Each bounds one bounded face from above (the face
of Appendix F whose parent chord it is; the root `(0, n - 1)` for the root face). Edges
are laminar: two edges are nested or have disjoint interiors (`laminar`), since edges do
not cross. Ordered by containment, the segments form a rooted tree (`segTree`): the
children of a segment are its maximal proper sub-segments. This is the weak dual of
Appendix F, rooted at the face on the outer edge `(0, n - 1)`.

* The top of a convex cycle `u` is the segment `(u₀, u_last)`: the face of minimum depth
  that it encloses (Appendix F: `top(c)`).
* An edge is owned by the deepest face it bounds (Appendix F: `E_{v_f}`): a segment owns
  itself, and a side `(a, a + 1)` is owned by the smallest segment containing it (`own`).
* A cycle through an edge owned by `s` has its top at `s` or above: the owner lies within every
  segment containing the edge (`own_spec`; this gives the hypothesis `scope_top` of
  `polygonProblem` in `DPCorrect`).
-/

@[expose] public section

namespace STACS2027

/-- `s` lies within `t`: `t.1 ≤ s.1 ≤ s.2 ≤ t.2`. -/
def Within (s t : ℕ × ℕ) : Prop := t.1 ≤ s.1 ∧ s.2 ≤ t.2

instance (s t : ℕ × ℕ) : Decidable (Within s t) := inferInstanceAs (Decidable (_ ∧ _))

theorem Within.refl (s : ℕ × ℕ) : Within s s := ⟨le_rfl, le_rfl⟩

theorem Within.trans {s t u : ℕ × ℕ} (h1 : Within s t) (h2 : Within t u) : Within s u :=
  ⟨le_trans h2.1 h1.1, le_trans h1.2 h2.2⟩

theorem Within.antisymm {s t : ℕ × ℕ} (h1 : Within s t) (h2 : Within t s) : s = t :=
  Prod.ext (le_antisymm h2.1 h1.1) (le_antisymm h1.2 h2.2)

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- **Laminarity**: two edges are nested or have disjoint interiors. -/
theorem laminar (hP : IsPolygon g n) {a b c d : ℕ} (h1 : Adj g a b) (h2 : Adj g c d)
    (_hab : a < b) (_hcd : c < d) :
    Within (a, b) (c, d) ∨ Within (c, d) (a, b) ∨ b ≤ c ∨ d ≤ a := by
  simp only [Within]
  by_contra h
  rcases (show (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b) by omega) with h' | h'
  · exact hP.noncross h'.1 h'.2.1 h'.2.2 h1 h2
  · exact hP.noncross h'.1 h'.2.1 h'.2.2 h2 h1

/-- The segments: edges `(a, b)` with `a + 2 ≤ b`. -/
def segs (g : Graph) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter fun s => Adj g s.1 s.2 ∧ s.1 + 2 ≤ s.2

theorem mem_segs (hP : IsPolygon g n) {s : ℕ × ℕ} :
    s ∈ segs g n ↔ Adj g s.1 s.2 ∧ s.1 + 2 ≤ s.2 := by
  simp only [segs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨hP.lt_of_adj h.1, h⟩

theorem root_mem_segs (hP : IsPolygon g n) : (0, n - 1) ∈ segs g n := by
  rw [hP.mem_segs]
  have := hP.three_le
  exact ⟨hP.adj_wrap, by simp; omega⟩

theorem within_root (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    Within s (0, n - 1) := by
  rw [hP.mem_segs] at hs
  have := (hP.lt_of_adj hs.1).2
  exact ⟨Nat.zero_le _, by simp; omega⟩

/-- Two segments containing a common edge are nested. -/
theorem nested_of_within (hP : IsPolygon g n) {s t e : ℕ × ℕ} (hs : s ∈ segs g n)
    (ht : t ∈ segs g n) (he : e.1 < e.2) (hes : Within e s) (het : Within e t) :
    Within s t ∨ Within t s := by
  rw [hP.mem_segs] at hs ht
  rcases hP.laminar hs.1 ht.1 (by omega) (by omega) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso; simp only [Within] at hes het; omega
  · exfalso; simp only [Within] at hes het; omega

/-! ### The tree -/

/-- The segments, as a type. -/
abbrev Seg (g : Graph) (n : ℕ) := {s : ℕ × ℕ // s ∈ segs g n}

/-- `t` is a child of `s`: a maximal proper sub-segment. -/
def IsChild (g : Graph) (n : ℕ) (s t : ℕ × ℕ) : Prop :=
  t ≠ s ∧ Within t s ∧ ∀ t' ∈ segs g n, Within t t' → Within t' s → t' = t ∨ t' = s

instance (s t : ℕ × ℕ) : Decidable (IsChild g n s t) := by
  unfold IsChild; infer_instance

/-- The size of a segment. -/
def segSize (s : ℕ × ℕ) : ℕ := s.2 - s.1

theorem exists_child (hP : IsPolygon g n) {s t : ℕ × ℕ} (_hs : s ∈ segs g n)
    (ht : t ∈ segs g n) (hts : Within t s) (hne : t ≠ s) :
    ∃ c ∈ segs g n, IsChild g n s c ∧ Within t c := by
  classical
  let S := (segs g n).filter fun c => Within t c ∧ Within c s ∧ c ≠ s
  have htS : t ∈ S := by simp [S, ht, Within.refl, hts, hne]
  obtain ⟨c, hcS, hmax⟩ := S.exists_max_image segSize ⟨t, htS⟩
  simp only [S, Finset.mem_filter] at hcS
  refine ⟨c, hcS.1, ⟨hcS.2.2.2, hcS.2.2.1, ?_⟩, hcS.2.1⟩
  intro t' ht' hct' ht's
  by_cases h : t' = s
  · exact Or.inr h
  · left
    have h1 := hmax t' (by simp [S, ht', hcS.2.1.trans hct', ht's, h])
    have hc2 := (hP.mem_segs.mp hcS.1).2
    have ht2 := (hP.mem_segs.mp ht').2
    simp only [segSize] at h1
    apply Within.antisymm _ hct'
    simp only [Within] at hct' ⊢
    omega

theorem child_size_lt (hP : IsPolygon g n) {s t : ℕ × ℕ} (ht : t ∈ segs g n)
    (h : IsChild g n s t) : segSize t < segSize s := by
  have ht2 := (hP.mem_segs.mp ht).2
  obtain ⟨hne, hw, -⟩ := h
  simp only [segSize]
  by_contra hc
  apply hne
  simp only [Within] at hw
  exact Prod.ext (by omega) (by omega)

theorem child_disjoint (hP : IsPolygon g n) {s c c' : ℕ × ℕ} (hc : c ∈ segs g n)
    (hc' : c' ∈ segs g n) (h : IsChild g n s c) (h' : IsChild g n s c') (hne : c ≠ c')
    {t : ℕ × ℕ} (ht : t ∈ segs g n) (htc : Within t c) (htc' : Within t c') : False := by
  have hcs := hc
  have hcs' := hc'
  rw [hP.mem_segs] at hc hc' ht
  rcases hP.laminar hc.1 hc'.1 (by omega) (by omega) with w | w | w | w
  · rcases h.2.2 c' hcs' w h'.2.1 with e | e
    · exact hne e.symm
    · exact h'.1 e
  · rcases h'.2.2 c hcs w h.2.1 with e | e
    · exact hne e
    · exact h.1 e
  · simp only [Within] at htc htc'; omega
  · simp only [Within] at htc htc'; omega

open TreeDP in
/-- The segment tree. -/
def segTree (hP : IsPolygon g n) : Tree (Seg g n) where
  sub v := Finset.univ.filter fun t => Within t.1 v.1
  children v := Finset.univ.filter fun t => IsChild g n v.1 t.1
  size v := segSize v.1
  mem_sub v := by simp [Within.refl]
  sub_trans := by
    intro v w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ht.trans hw
  child_mem := by
    intro v w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact hw.2.1
  not_mem_child := by
    intro v w hw hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hv
    exact hw.1 (Within.antisymm hw.2.1 hv)
  sub_eq := by
    intro v
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_biUnion]
    constructor
    · intro ht
      by_cases h : t = v
      · exact Or.inl h
      · right
        have hne : t.1 ≠ v.1 := fun e => h (Subtype.ext e)
        obtain ⟨c, hc, hch, htc⟩ := hP.exists_child v.2 t.2 ht hne
        exact ⟨⟨c, hc⟩, hch, htc⟩
    · rintro (rfl | ⟨c, hc, htc⟩)
      · exact Within.refl _
      · exact htc.trans hc.2.1
  disj := by
    intro v w w' hw hw' hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    rw [Finset.disjoint_left]
    intro t ht ht'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    exact hP.child_disjoint w.2 w'.2 hw hw' (fun e => hne (Subtype.ext e)) t.2 ht ht'
  size_lt := by
    intro v w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact hP.child_size_lt w.2 hw

/-- The root segment `(0, n - 1)`. -/
def root (hP : IsPolygon g n) : Seg g n := ⟨(0, n - 1), hP.root_mem_segs⟩

theorem mem_sub_root (hP : IsPolygon g n) (v : Seg g n) : v ∈ (segTree hP).sub (root hP) := by
  simp only [segTree, root, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hP.within_root v.2

theorem mem_sub_iff (hP : IsPolygon g n) (v w : Seg g n) :
    w ∈ (segTree hP).sub v ↔ Within w.1 v.1 := by
  simp [segTree]

theorem mem_children_iff (hP : IsPolygon g n) (v w : Seg g n) :
    w ∈ (segTree hP).children v ↔ IsChild g n v.1 w.1 := by
  simp [segTree]

end IsPolygon

/-! ### Tops of convex cycles -/

theorem ConvexCycle.head_lt_getLast {g : Graph} {u : List ℕ} (h : ConvexCycle g u) (hu : u ≠ []) :
    u.head hu + 2 ≤ u.getLast hu := by
  obtain ⟨hs, hl, -⟩ := h
  obtain ⟨x, y, w, rfl⟩ : ∃ x y w, u = x :: y :: w := by
    match u, hl with
    | x :: y :: w, _ => exact ⟨x, y, w, rfl⟩
  have hw : w ≠ [] := by rintro rfl; simp at hl
  simp only [List.head_cons]
  have hlast : (x :: y :: w).getLast hu = w.getLast hw := by
    simp [List.getLast_cons, hw]
  rw [hlast]
  have h1 := (List.pairwise_cons.mp hs).1 y (by simp)
  have h2 := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 _ (List.getLast_mem hw)
  omega

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- The top segment of a convex cycle: its first and last entry. -/
theorem top_mem_segs (hP : IsPolygon g n) {u : List ℕ} (h : ConvexCycle g u) (hu : u ≠ []) :
    (u.head hu, u.getLast hu) ∈ segs g n := by
  rw [hP.mem_segs]
  have h2 := h.head_lt_getLast hu
  refine ⟨⟨by omega, ?_⟩, h2⟩
  rw [edge_comm]
  exact h.2.2 _ (edge_last_head_mem_cycleEdges hu)

/-- Every entry of a strictly increasing list lies between its first and last entry. -/
theorem mem_within_head_last {u : List ℕ} (hs : u.Pairwise (· < ·)) (hu : u ≠ []) {x : ℕ}
    (hx : x ∈ u) : u.head hu ≤ x ∧ x ≤ u.getLast hu := by
  constructor
  · cases u with
    | nil => exact absurd rfl hu
    | cons y w =>
      simp only [List.head_cons]
      rcases List.mem_cons.mp hx with rfl | h
      · exact le_rfl
      · exact le_of_lt ((List.pairwise_cons.mp hs).1 x h)
  · obtain ⟨xs, hxs⟩ : ∃ xs, u = xs ++ [u.getLast hu] :=
      ⟨u.dropLast, (List.dropLast_append_getLast hu).symm⟩
    have hx' := hx
    rw [hxs] at hx' hs
    rcases List.mem_append.mp hx' with h | h
    · exact le_of_lt ((List.pairwise_append.mp hs).2.2 x h _ (List.mem_singleton_self _))
    · simp at h; omega

/-! ### Ownership of edges -/

/-- The segments containing the edge `e`. -/
def containing (g : Graph) (n : ℕ) (e : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (segs g n).filter fun s => Within e s

theorem exists_own (hP : IsPolygon g n) {e : ℕ × ℕ} (he : Adj g e.1 e.2) (hlt : e.1 < e.2) :
    ∃ s ∈ segs g n, Within e s ∧ ∀ t ∈ segs g n, Within e t → Within s t := by
  classical
  have hne : (containing g n e).Nonempty := by
    refine ⟨(0, n - 1), ?_⟩
    simp only [containing, Finset.mem_filter]
    have := hP.lt_of_adj he
    exact ⟨hP.root_mem_segs, Nat.zero_le _, by omega⟩
  obtain ⟨s, hs, hmin⟩ := (containing g n e).exists_min_image segSize hne
  simp only [containing, Finset.mem_filter] at hs
  refine ⟨s, hs.1, hs.2, ?_⟩
  intro t ht het
  rcases hP.nested_of_within hs.1 ht hlt hs.2 het with h | h
  · exact h
  · have h1 := hmin t (by simp [containing, ht, het])
    have hs2 := (hP.mem_segs.mp hs.1).2
    have ht2 := (hP.mem_segs.mp ht).2
    simp only [segSize] at h1
    have : t = s := Within.antisymm h (by simp only [Within] at h ⊢; omega)
    rw [this]; exact Within.refl _

open Classical in
/-- The owner of an edge `e = (a, b)`, `a < b`: the smallest segment containing it (the
edge itself if it is a segment); the root for other pairs. -/
noncomputable def own (hP : IsPolygon g n) (e : ℕ × ℕ) : Seg g n :=
  if h : Adj g e.1 e.2 ∧ e.1 < e.2 then ⟨(hP.exists_own h.1 h.2).choose, (hP.exists_own h.1 h.2).choose_spec.1⟩
  else root hP

theorem own_spec (hP : IsPolygon g n) {e : ℕ × ℕ} (he : Adj g e.1 e.2) (hlt : e.1 < e.2) :
    Within e (own hP e).1 ∧ ∀ t ∈ segs g n, Within e t → Within (own hP e).1 t := by
  simp only [own, he, hlt, and_self, dite_true]
  exact (hP.exists_own he hlt).choose_spec.2

theorem own_of_seg (hP : IsPolygon g n) {e : ℕ × ℕ} (he : e ∈ segs g n) : (own hP e).1 = e := by
  have he' := (hP.mem_segs).mp he
  obtain ⟨h1, h2⟩ := hP.own_spec he'.1 (by omega)
  exact Within.antisymm (h2 e he (Within.refl e)) h1

/-- An edge lies in the subtree of `s` exactly when it lies within `s`. -/
theorem own_within_iff (hP : IsPolygon g n) {e : ℕ × ℕ} (he : Adj g e.1 e.2) (hlt : e.1 < e.2)
    {s : ℕ × ℕ} (hs : s ∈ segs g n) : Within (own hP e).1 s ↔ Within e s := by
  obtain ⟨h1, h2⟩ := hP.own_spec he hlt
  exact ⟨fun h => h1.trans h, fun h => h2 s hs h⟩

end IsPolygon

end STACS2027
