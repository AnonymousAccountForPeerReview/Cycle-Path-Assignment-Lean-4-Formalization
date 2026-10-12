module

public import Outerplanar.Segments
import Mathlib.Tactic

/-!
# The bounded faces of a polygon (Lemma 27)

For a polygon `g` on `0, …, n - 1` (`IsPolygon g n`), the bounded face directly below a
segment `s = (a, b)` (a chord or the outer edge `(0, n - 1)`, see `Segments`) has as its
vertices the positions `x ∈ [a, b]` that lie strictly inside no other segment `t` within
`s` (`IsFaceVert`, `faceVerts`). This file proves the facts of Appendix F, Lemma 27
(face boundaries are cycles, and the faces correspond to the nodes of the weak dual) in
the form used by the region-path decomposition:

* `faceVerts g n s` is strictly increasing, from `s.1` to `s.2` (`faceVerts_pairwise`,
  `faceVerts_head?`, `faceVerts_getLast?`);
* two consecutive face vertices are adjacent (`adj_of_infix_faceVerts`): they form a side
  `(x, x + 1)` of the outer cycle or a child segment of `s` (`face_gap`); conversely every
  child segment of `s` is a pair of consecutive face vertices (`child_iff`), so the children
  of a node of the weak dual are the chords on the boundary of its face;
* a face has at least three vertices (`three_le_length_faceVerts`).

That the boundary is a convex cycle is `faceVerts_convexCycle` in `RegionPaths`.
-/

@[expose] public section

namespace STACS2027

open IsPolygon

/-- `x` is a vertex of the face of the segment `s`: no segment `t ≠ s` within `s` has `x`
strictly inside. (Together with `s.1 ≤ x ≤ s.2`, see `faceVerts`.) -/
def IsFaceVert (g : Graph) (n : ℕ) (s : ℕ × ℕ) (x : ℕ) : Prop :=
  ∀ t ∈ segs g n, Within t s → t ≠ s → ¬ (t.1 < x ∧ x < t.2)

instance (g : Graph) (n : ℕ) (s : ℕ × ℕ) (x : ℕ) : Decidable (IsFaceVert g n s x) := by
  unfold IsFaceVert; infer_instance

/-- The vertices of the face below the segment `s`, in increasing order: the positions
`x ∈ [s.1, s.2]` strictly inside no other segment within `s`. -/
def faceVerts (g : Graph) (n : ℕ) (s : ℕ × ℕ) : List ℕ :=
  (List.range' s.1 (s.2 + 1 - s.1)).filter fun x => decide (IsFaceVert g n s x)

/-! ### Strictly increasing lists -/

/-- In a strictly increasing list, an entry at most every entry is the first. -/
theorem head?_eq_of_le {l : List ℕ} (hs : l.Pairwise (· < ·)) {a : ℕ} (ha : a ∈ l)
    (hle : ∀ z ∈ l, a ≤ z) : l.head? = some a := by
  rw [List.head?_eq_some_head (List.ne_nil_of_mem ha), head_eq_of_le hs _ ha hle]

/-- In a strictly increasing list, an entry at least every entry is the last. -/
theorem getLast?_eq_of_le {l : List ℕ} (hs : l.Pairwise (· < ·)) {b : ℕ} (hb : b ∈ l)
    (hle : ∀ z ∈ l, z ≤ b) : l.getLast? = some b := by
  rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hb), getLast_eq_of_le hs _ hb hle]

/-- In a strictly increasing list, `x, y` are consecutive entries exactly when they are
entries, `x < y`, and no entry lies strictly between them. -/
theorem infix_pair_iff {l : List ℕ} (hs : l.Pairwise (· < ·)) {x y : ℕ} :
    [x, y] <:+: l ↔ x ∈ l ∧ y ∈ l ∧ x < y ∧ ∀ z ∈ l, ¬ (x < z ∧ z < y) := by
  constructor
  · rintro ⟨s, t, rfl⟩
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hs ⊢
    rw [List.pairwise_append] at hs
    obtain ⟨-, hs2, hs3⟩ := hs
    rw [List.pairwise_cons, List.pairwise_cons] at hs2
    refine ⟨by simp, by simp, hs2.1 y (by simp), ?_⟩
    rintro z hz ⟨h1, h2⟩
    rcases List.mem_append.mp hz with hz | hz
    · have := hs3 z hz x (by simp); omega
    · rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · rcases List.mem_cons.mp hz with rfl | hz
        · omega
        · have := hs2.2.1 z hz; omega
  · rintro ⟨hx, hy, hxy, hgap⟩
    induction l with
    | nil => simp at hx
    | cons v l ih =>
      obtain ⟨hv, hl⟩ := List.pairwise_cons.mp hs
      by_cases hvx : v = x
      · subst hvx
        cases l with
        | nil => simp at hy; omega
        | cons w l =>
          have hwy : w = y := by
            rcases List.mem_cons.mp hy with h | h
            · omega
            rcases List.mem_cons.mp h with h | h
            · exact h.symm
            · have h1 := hv w (by simp)
              have h2 := (List.pairwise_cons.mp hl).1 y h
              exact absurd ⟨h1, h2⟩ (hgap w (by simp))
          subst hwy
          exact ⟨[], l, rfl⟩
      · have hx' : x ∈ l := (List.mem_cons.mp hx).resolve_left (Ne.symm hvx)
        have hy' : y ∈ l := by
          rcases List.mem_cons.mp hy with h | h
          · subst h; have := hv x hx'; omega
          · exact h
        exact List.infix_cons (ih hl hx' hy' fun z hz => hgap z (by simp [hz]))

/-! ### Face vertices -/

variable {g : Graph} {n : ℕ}

/-- The face vertices of `s` are the positions in `[s.1, s.2]` satisfying `IsFaceVert`. -/
theorem mem_faceVerts {s : ℕ × ℕ} {x : ℕ} :
    x ∈ faceVerts g n s ↔ s.1 ≤ x ∧ x ≤ s.2 ∧ IsFaceVert g n s x := by
  simp only [faceVerts, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

/-- The face vertices are listed in increasing order. -/
theorem faceVerts_pairwise {s : ℕ × ℕ} : (faceVerts g n s).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range'

/-- The left end of `s` is a face vertex of `s`. -/
theorem isFaceVert_left (s : ℕ × ℕ) : IsFaceVert g n s s.1 := by
  intro t _ hts _ h
  have := hts.1
  omega

/-- The right end of `s` is a face vertex of `s`. -/
theorem isFaceVert_right (s : ℕ × ℕ) : IsFaceVert g n s s.2 := by
  intro t _ hts _ h
  have := hts.2
  omega

/-- The left end of `s` is listed in `faceVerts g n s`. -/
theorem left_mem_faceVerts {s : ℕ × ℕ} (h : s.1 ≤ s.2) : s.1 ∈ faceVerts g n s :=
  mem_faceVerts.mpr ⟨le_rfl, h, isFaceVert_left s⟩

/-- The right end of `s` is listed in `faceVerts g n s`. -/
theorem right_mem_faceVerts {s : ℕ × ℕ} (h : s.1 ≤ s.2) : s.2 ∈ faceVerts g n s :=
  mem_faceVerts.mpr ⟨h, le_rfl, isFaceVert_right s⟩

/-- The face below `s` starts at `s.1`. -/
theorem faceVerts_head? {s : ℕ × ℕ} (h : s.1 ≤ s.2) : (faceVerts g n s).head? = some s.1 :=
  head?_eq_of_le faceVerts_pairwise (left_mem_faceVerts h)
    (fun _ hz => (mem_faceVerts.mp hz).1)

/-- The face below `s` ends at `s.2`. -/
theorem faceVerts_getLast? {s : ℕ × ℕ} (h : s.1 ≤ s.2) :
    (faceVerts g n s).getLast? = some s.2 :=
  getLast?_eq_of_le faceVerts_pairwise (right_mem_faceVerts h)
    (fun _ hz => (mem_faceVerts.mp hz).2.1)

/-- Segments are edges `(a, b)` with `a + 2 ≤ b` (without the polygon hypothesis). -/
theorem of_mem_segs {s : ℕ × ℕ} (hs : s ∈ segs g n) : Adj g s.1 s.2 ∧ s.1 + 2 ≤ s.2 := by
  simp only [segs, Finset.mem_filter] at hs
  exact hs.2

namespace IsPolygon

/-- **Consecutive face vertices** (Lemma 27): two face vertices `x < y` of `s` with no face
vertex between them form a side `(x, x + 1)` of the outer cycle or a child segment of `s`. -/
theorem face_gap (hP : IsPolygon g n) {s : ℕ × ℕ} {x y : ℕ}
    (hx : x ∈ faceVerts g n s) (hy : y ∈ faceVerts g n s) (hxy : x < y)
    (hgap : ∀ z ∈ faceVerts g n s, ¬ (x < z ∧ z < y)) :
    y = x + 1 ∨ ((x, y) ∈ segs g n ∧ IsChild g n s (x, y)) := by
  classical
  rw [mem_faceVerts] at hx hy
  by_cases hy1 : y = x + 1
  · exact Or.inl hy1
  right
  -- positions strictly between `x` and `y` are strictly inside a segment within `s`
  have hcov : ∀ z, x < z → z < y →
      ∃ t ∈ segs g n, Within t s ∧ t ≠ s ∧ t.1 < z ∧ z < t.2 := by
    intro z h1 h2
    by_contra hc
    apply hgap z _ ⟨h1, h2⟩
    rw [mem_faceVerts]
    refine ⟨by omega, by omega, ?_⟩
    intro t ht hts hne hz
    exact hc ⟨t, ht, hts, hne, hz⟩
  let T := (segs g n).filter fun t => Within t s ∧ t ≠ s ∧ t.1 ≤ x ∧ x + 1 < t.2
  obtain ⟨t0, ht0, hts0, hne0, h10, h20⟩ := hcov (x + 1) (by omega) (by omega)
  have hT : t0 ∈ T := by
    simp only [T, Finset.mem_filter]
    exact ⟨ht0, hts0, hne0, by omega, h20⟩
  obtain ⟨t, htT, hmax⟩ := T.exists_max_image (fun t => t.2) ⟨t0, hT⟩
  simp only [T, Finset.mem_filter] at htT
  obtain ⟨ht, hts, hne, h1, h2⟩ := htT
  have ht1 : t.1 = x := by
    by_contra h
    exact hx.2.2 t ht hts hne ⟨by omega, by omega⟩
  have ht2le : t.2 ≤ y := by
    by_contra h
    exact hy.2.2 t ht hts hne ⟨by omega, by omega⟩
  have ht2 : t.2 = y := by
    by_contra h
    obtain ⟨t', ht', hts', hne', h1', h2'⟩ := hcov t.2 (by omega) (by omega)
    have htseg := hP.mem_segs.mp ht
    have htseg' := hP.mem_segs.mp ht'
    rcases hP.laminar htseg.1 htseg'.1 (by omega) (by omega) with w | w | w | w
    · have hw1 := w.1
      have hT' : t' ∈ T := by
        simp only [T, Finset.mem_filter]
        exact ⟨ht', hts', hne', by omega, by omega⟩
      have := hmax t' hT'
      omega
    · have := w.2; omega
    · omega
    · omega
  have hteq : t = (x, y) := Prod.ext ht1 ht2
  subst hteq
  refine ⟨ht, hne, hts, ?_⟩
  intro t' ht' hw hw'
  by_contra hc
  simp only [not_or] at hc
  have hw1 : t'.1 ≤ x := hw.1
  have hw2 : y ≤ t'.2 := hw.2
  by_cases h : t'.1 < x
  · exact hx.2.2 t' ht' hw' hc.2 ⟨h, by omega⟩
  · have : y < t'.2 := by
      by_contra h'
      exact hc.1 (Prod.ext (by simp only; omega) (by simp only; omega))
    exact hy.2.2 t' ht' hw' hc.2 ⟨by omega, this⟩

/-- Every child segment of `s` is a pair of consecutive face vertices of `s`. -/
theorem infix_faceVerts_of_child (hP : IsPolygon g n) {s t : ℕ × ℕ} (ht : t ∈ segs g n)
    (hc : IsChild g n s t) : [t.1, t.2] <:+: faceVerts g n s := by
  obtain ⟨hne, hts, hmax⟩ := hc
  have htseg := hP.mem_segs.mp ht
  have hw1 := hts.1
  have hw2 := hts.2
  rw [infix_pair_iff faceVerts_pairwise]
  refine ⟨?_, ?_, by omega, ?_⟩
  · rw [mem_faceVerts]
    refine ⟨by omega, by omega, ?_⟩
    rintro t' ht' hts' hne' ⟨h1, h2⟩
    have htseg' := hP.mem_segs.mp ht'
    rcases hP.laminar htseg.1 htseg'.1 (by omega) (by omega) with w | w | w | w
    · rcases hmax t' ht' w hts' with e | e
      · rw [e] at h1; omega
      · exact hne' e
    · have := w.1; omega
    · omega
    · omega
  · rw [mem_faceVerts]
    refine ⟨by omega, by omega, ?_⟩
    rintro t' ht' hts' hne' ⟨h1, h2⟩
    have htseg' := hP.mem_segs.mp ht'
    rcases hP.laminar htseg.1 htseg'.1 (by omega) (by omega) with w | w | w | w
    · rcases hmax t' ht' w hts' with e | e
      · rw [e] at h2; omega
      · exact hne' e
    · have := w.2; omega
    · omega
    · omega
  · rintro z hz ⟨h1, h2⟩
    exact (mem_faceVerts.mp hz).2.2 t ht hts hne ⟨h1, h2⟩

/-- **The children of a node of the weak dual** (Lemma 27): the child segments of `s` are
exactly the pairs of consecutive face vertices of `s` that are not sides. -/
theorem child_iff (hP : IsPolygon g n) {s t : ℕ × ℕ} :
    (t ∈ segs g n ∧ IsChild g n s t) ↔ ([t.1, t.2] <:+: faceVerts g n s ∧ t.1 + 2 ≤ t.2) := by
  constructor
  · rintro ⟨ht, hc⟩
    exact ⟨hP.infix_faceVerts_of_child ht hc, (hP.mem_segs.mp ht).2⟩
  · rintro ⟨hi, h2⟩
    obtain ⟨hx, hy, hxy, hgap⟩ := (infix_pair_iff faceVerts_pairwise).mp hi
    rcases hP.face_gap hx hy hxy hgap with h | h
    · omega
    · exact h

/-- **Consecutive face vertices are adjacent** (Lemma 27: the boundary of a face is a
cycle of `g`). -/
theorem adj_of_infix_faceVerts (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    {x y : ℕ} (h : [x, y] <:+: faceVerts g n s) : Adj g x y := by
  obtain ⟨hx, hy, hxy, hgap⟩ := (infix_pair_iff faceVerts_pairwise).mp h
  rcases hP.face_gap hx hy hxy hgap with h | h
  · subst h
    have := (hP.lt_of_adj (hP.mem_segs.mp hs).1).2
    exact hP.adj_succ (by rw [mem_faceVerts] at hy; omega)
  · exact (hP.mem_segs.mp h.1).1

/-- Consecutive face vertices of `s` span a strictly smaller interval than `s`. -/
theorem infix_faceVerts_lt (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    {x y : ℕ} (h : [x, y] <:+: faceVerts g n s) :
    s.1 ≤ x ∧ x < y ∧ y ≤ s.2 ∧ y - x < s.2 - s.1 := by
  have hs' := hP.mem_segs.mp hs
  obtain ⟨hx, hy, hxy, hgap⟩ := (infix_pair_iff faceVerts_pairwise).mp h
  have hx' := mem_faceVerts.mp hx
  have hy' := mem_faceVerts.mp hy
  refine ⟨hx'.1, hxy, hy'.2.1, ?_⟩
  rcases hP.face_gap hx hy hxy hgap with h | h
  · omega
  · have hne := h.2.1
    by_contra hc
    exact hne (Prod.ext (by simp only; omega) (by simp only; omega))

/-- **A face has at least three vertices.** -/
theorem three_le_length_faceVerts (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    3 ≤ (faceVerts g n s).length := by
  have hs' := hP.mem_segs.mp hs
  have ha := left_mem_faceVerts (g := g) (n := n) (s := s) (by omega)
  have hb := right_mem_faceVerts (g := g) (n := n) (s := s) (by omega)
  by_cases hz : ∃ z ∈ faceVerts g n s, s.1 < z ∧ z < s.2
  · obtain ⟨z, hz, h1, h2⟩ := hz
    have hsub : [s.1, z, s.2] ⊆ faceVerts g n s := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have hnd : [s.1, z, s.2].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, not_false_eq_true, and_true]
      omega
    simpa using hnd.length_le_of_subset hsub
  · rcases hP.face_gap ha hb (by omega) (fun z hz' h => hz ⟨z, hz', h⟩) with h | h
    · omega
    · exact absurd rfl h.2.1

end IsPolygon

end STACS2027
