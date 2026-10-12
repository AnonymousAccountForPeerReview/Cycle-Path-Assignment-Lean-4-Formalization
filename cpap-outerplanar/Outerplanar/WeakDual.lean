module

public import Outerplanar.RegionPaths
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# The weak dual of a polygon: face boundaries, the boundary map, subtrees

Definitions for Appendix F, "Cycles and the weak dual" (Definition 26 and the notation before
Lemma 27), in the polygon model: `g` is a 2-connected outerplanar graph written in the
positions `0, …, n - 1` of its outer Hamiltonian cycle (`IsPolygon g n`).

* The bounded faces are the segments `s ∈ segs g n` (the chords and the outer edge
  `(0, n - 1)`), the face of `s` being the one directly below `s`, with the vertices
  `faceVerts g n s` (see `Faces`).
* `faceEdges g n s`: the edge set `∂f` of the face of `s` (the edges of the cycle
  `faceVerts g n s`); `d_f = (faceVerts g n s).length`.
* `bdry g n T`: the boundary `∂T = Δ_{f ∈ fc(T)} ∂f` of a set `T` of faces, the symmetric
  difference of their edge sets (`mem_bdry`: the edges on an odd number of the faces of `T`).
* `encl g n u`: the faces enclosed by a cycle `u`, those all of whose vertices lie on `u`.
* `DualAdj g n s t`: the faces `s ≠ t` are adjacent in the weak dual `D` (Definition 26): they
  share an edge. `IsSubtree g n S`: `S` is a nonempty set of nodes of `D` inducing a connected
  subgraph (the paper's `𝒮`).

Basic facts proved here:

* `mem_faceEdges_iff`: the edges of the face of `s` are `s` itself, the child segments of `s`
  (the chords to the children in the segment tree), and sides `(x, x + 1)` of the outer cycle;
* `faces_of_seg`, `faces_of_side`: a segment `e` lies on the faces `e` and its parent, a side
  on exactly one face (the smallest segment containing it);
* `exists_parent`, `parent_unique`: every segment other than the root `(0, n - 1)` has exactly
  one parent;
* `dualAdj_iff`: two faces are adjacent in the weak dual exactly when one is a child of the
  other in the segment tree (so the segment tree is the weak dual, rooted at `(0, n - 1)`);
* `isSubtree_iff`: a set of faces is a subtree exactly when it is *rooted*: it contains a node
  `r` such that every other node of it has its parent in it (`IsRooted`).
-/

@[expose] public section

namespace STACS2027

open IsPolygon
open scoped symmDiff

variable {g : Graph} {n : ℕ}

/-! ### Definitions -/

/-- The edges `∂f` of the face below the segment `s`: the edges of the cycle
`faceVerts g n s` (consecutive face vertices, and `s` itself closing it). -/
def faceEdges (g : Graph) (n : ℕ) (s : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (cycleEdges (faceVerts g n s)).toFinset

/-- The boundary `∂T = Δ_{f ∈ fc(T)} ∂f` of a set `T` of faces (Appendix F): the symmetric
difference of the edge sets of the faces in `T`. -/
def bdry (g : Graph) (n : ℕ) (T : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  T.fold (· ∆ ·) ∅ (faceEdges g n)

/-- The faces enclosed by the cycle `u`: the segments all of whose face vertices lie on `u`
(for a convex cycle `u`, the faces inside the polygon `u`; `encl g n u = ψ⁻¹(u)` by
Lemma 29). -/
def encl (g : Graph) (n : ℕ) (u : List ℕ) : Finset (ℕ × ℕ) :=
  (segs g n).filter fun s => ∀ x ∈ faceVerts g n s, x ∈ u

/-- **The weak dual** (Definition 26): the bounded faces `s ≠ t` are adjacent when they share
an edge, `∂s ∩ ∂t ≠ ∅`. -/
def DualAdj (g : Graph) (n : ℕ) (s t : ℕ × ℕ) : Prop :=
  s ∈ segs g n ∧ t ∈ segs g n ∧ s ≠ t ∧ (faceEdges g n s ∩ faceEdges g n t).Nonempty

/-- `S` is a **subtree** of the weak dual (the paper's `𝒮`): a nonempty set of bounded faces
inducing a connected subgraph `D(S)` of the weak dual: any two of its nodes are joined by a
walk of adjacent faces in `S`. -/
def IsSubtree (g : Graph) (n : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  S.Nonempty ∧ S ⊆ segs g n ∧
    ∀ s ∈ S, ∀ t ∈ S, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ DualAdj g n x y) s t

/-- `S` is a rooted subtree of the segment tree with root `r`: every node of `S` other than `r`
has its parent in `S` (equivalent to `IsSubtree`, `isSubtree_iff`). -/
def IsRooted (g : Graph) (n : ℕ) (S : Finset (ℕ × ℕ)) (r : ℕ × ℕ) : Prop :=
  r ∈ S ∧ S ⊆ segs g n ∧ ∀ s ∈ S, s ≠ r → ∃ p ∈ S, IsChild g n p s

/-! ### The boundary as a parity -/

/-- **The boundary consists of the edges lying on an odd number of the faces of `T`.** -/
theorem mem_bdry {T : Finset (ℕ × ℕ)} {e : ℕ × ℕ} :
    e ∈ bdry g n T ↔ Odd (T.filter fun s => e ∈ faceEdges g n s).card := by
  induction T using Finset.induction_on with
  | empty => simp [bdry]
  | insert a T ha ih =>
    rw [bdry, Finset.fold_insert ha, Finset.mem_symmDiff, ← bdry, ih, Finset.filter_insert]
    by_cases h : e ∈ faceEdges g n a
    · simp only [h, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp [ha]), Nat.odd_add_one]
      tauto
    · simp only [h, ↓reduceIte]
      tauto

/-! ### Lists -/

/-- An edge of a strictly increasing list is a pair `(x, y)` of consecutive entries. -/
theorem mem_pathEdges_of_pairwise {l : List ℕ} (hs : l.Pairwise (· < ·)) {e : ℕ × ℕ} :
    e ∈ pathEdges l ↔ ∃ x y, [x, y] <:+: l ∧ e = (x, y) := by
  rw [mem_pathEdges_iff]
  constructor
  · rintro ⟨xs, a, b, ys, hl, rfl⟩
    have hi : [a, b] <:+: l := ⟨xs, ys, by rw [hl]; simp⟩
    have hab := ((infix_pair_iff hs).mp hi).2.2.1
    exact ⟨a, b, hi, by simp [edge, Nat.min_eq_left hab.le, Nat.max_eq_right hab.le]⟩
  · rintro ⟨x, y, ⟨xs, ys, h⟩, rfl⟩
    have hxy := ((infix_pair_iff hs).mp ⟨xs, ys, h⟩).2.2.1
    exact ⟨xs, x, y, ys, by rw [← h]; simp,
      by simp [edge, Nat.min_eq_left hxy.le, Nat.max_eq_right hxy.le]⟩

/-- The edges of a strictly increasing cycle `a :: (mid ++ [b])`: its consecutive pairs and
the closing pair `(a, b)`. -/
theorem mem_cycleEdges_of_pairwise {a b : ℕ} {mid : List ℕ}
    (hs : (a :: (mid ++ [b])).Pairwise (· < ·)) {e : ℕ × ℕ} :
    e ∈ cycleEdges (a :: (mid ++ [b])) ↔
      e = (a, b) ∨ ∃ x y, [x, y] <:+: a :: (mid ++ [b]) ∧ e = (x, y) := by
  have hab : a < b := (List.pairwise_cons.mp hs).1 b (by simp)
  rw [cycleEdges_snoc, List.mem_append, mem_pathEdges_of_pairwise hs, List.mem_singleton]
  have : edge b a = (a, b) := by simp [edge, Nat.min_eq_right hab.le, Nat.max_eq_left hab.le]
  rw [this, or_comm]

/-- A region path with at least two entries is `a :: (mid ++ [b])`. -/
theorem IsRPath.eq_cons_snoc {a b : ℕ} {u : List ℕ} (hu : IsRPath g a b u) (hl : 2 ≤ u.length) :
    ∃ mid, u = a :: (mid ++ [b]) := by
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hu.1
  rcases List.eq_nil_or_concat t with rfl | ⟨mid, c, rfl⟩
  · simp at hl
  · obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hu.2.1
    have h3 : (a :: mid) ++ [c] = ys ++ [b] := by rw [← hys]; simp
    have h4 := (List.append_inj' h3 rfl).2
    simp only [List.cons.injEq, and_true] at h4
    subst h4
    exact ⟨mid, by simp⟩

/-- A region path with at least three entries has an entry strictly between its ends. -/
theorem IsRPath.exists_inner {a b : ℕ} {u : List ℕ} (hu : IsRPath g a b u) (hl : 3 ≤ u.length) :
    ∃ z ∈ u, a < z ∧ z < b := by
  obtain ⟨mid, rfl⟩ := hu.eq_cons_snoc (by omega)
  obtain ⟨z, hz⟩ : ∃ z, z ∈ mid := by
    cases mid with
    | nil => simp at hl
    | cons z _ => exact ⟨z, by simp⟩
  have hs := hu.pairwise
  refine ⟨z, by simp [hz], (List.pairwise_cons.mp hs).1 z (by simp [hz]), ?_⟩
  exact (List.pairwise_append.mp (List.pairwise_cons.mp hs).2).2.2 z hz b (by simp)

/-! ### The edges of a face -/

namespace IsPolygon

/-- The vertices of the face below a segment `s`: `s.1 :: (mid ++ [s.2])`. -/
theorem faceVerts_eq (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    ∃ mid, faceVerts g n s = s.1 :: (mid ++ [s.2]) :=
  (hP.faceVerts_isRPath hs).eq_cons_snoc (by have := hP.three_le_length_faceVerts hs; omega)

/-- A face has a vertex strictly between the ends of its segment. -/
theorem exists_inner_faceVert (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    ∃ z ∈ faceVerts g n s, s.1 < z ∧ z < s.2 :=
  (hP.faceVerts_isRPath hs).exists_inner (hP.three_le_length_faceVerts hs)

/-- **The edges of a face**: the segment `s` itself and the pairs of consecutive face
vertices. -/
theorem mem_faceEdges (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) {e : ℕ × ℕ} :
    e ∈ faceEdges g n s ↔ e = s ∨ ∃ x y, [x, y] <:+: faceVerts g n s ∧ e = (x, y) := by
  obtain ⟨mid, hmid⟩ := hP.faceVerts_eq hs
  have hpw : (s.1 :: (mid ++ [s.2])).Pairwise (· < ·) := hmid ▸ faceVerts_pairwise
  rw [faceEdges, List.mem_toFinset, hmid, mem_cycleEdges_of_pairwise hpw]

/-- **Classification of the edges of a face**: the edges of the face of `s` are `s`, the
child segments of `s`, and sides `(x, x + 1)` of the outer cycle between consecutive face
vertices. -/
theorem mem_faceEdges_iff (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) {e : ℕ × ℕ} :
    e ∈ faceEdges g n s ↔ e = s ∨ (e ∈ segs g n ∧ IsChild g n s e) ∨
      (e.2 = e.1 + 1 ∧ [e.1, e.2] <:+: faceVerts g n s) := by
  rw [hP.mem_faceEdges hs]
  constructor
  · rintro (rfl | ⟨x, y, hi, rfl⟩)
    · exact Or.inl rfl
    · obtain ⟨hx, hy, hxy, hgap⟩ := (infix_pair_iff faceVerts_pairwise).mp hi
      rcases hP.face_gap hx hy hxy hgap with h | h
      · exact Or.inr (Or.inr ⟨h, hi⟩)
      · exact Or.inr (Or.inl h)
  · rintro (rfl | ⟨he, hc⟩ | ⟨-, hi⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨e.1, e.2, hP.infix_faceVerts_of_child he hc, rfl⟩
    · exact Or.inr ⟨e.1, e.2, hi, rfl⟩

/-- The edges of a face are edges `(a, b)`, `a < b`, of `g`. -/
theorem adj_of_mem_faceEdges (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    {e : ℕ × ℕ} (he : e ∈ faceEdges g n s) : Adj g e.1 e.2 ∧ e.1 < e.2 := by
  rcases (hP.mem_faceEdges hs).mp he with rfl | ⟨x, y, hi, rfl⟩
  · have := (hP.mem_segs.mp hs); exact ⟨this.1, by omega⟩
  · exact ⟨hP.adj_of_infix_faceVerts hs hi, ((infix_pair_iff faceVerts_pairwise).mp hi).2.2.1⟩

/-- A side `(a, a + 1)` joins consecutive face vertices of `s` exactly when `s` is the
smallest segment containing it. -/
theorem side_infix_iff (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n) {a : ℕ} :
    [a, a + 1] <:+: faceVerts g n s ↔
      Within (a, a + 1) s ∧ ∀ t ∈ segs g n, Within (a, a + 1) t → Within s t := by
  constructor
  · intro hi
    obtain ⟨hx, hy, -, -⟩ := (infix_pair_iff faceVerts_pairwise).mp hi
    have hx' := mem_faceVerts.mp hx
    have hy' := mem_faceVerts.mp hy
    refine ⟨⟨hx'.1, hy'.2.1⟩, fun t ht het => ?_⟩
    rcases hP.nested_of_within hs ht (show (a, a + 1).1 < (a, a + 1).2 by simp)
      ⟨hx'.1, hy'.2.1⟩ het with h | h
    · exact h
    · by_cases hts : t = s
      · rw [hts]; exact Within.refl _
      · exfalso
        have ht2 := (hP.mem_segs.mp ht).2
        simp only [Within] at het
        by_cases h1 : t.1 < a
        · exact hx'.2.2 t ht h hts ⟨h1, by omega⟩
        · exact hy'.2.2 t ht h hts ⟨by omega, by omega⟩
  · rintro ⟨hw, hmin⟩
    simp only [Within] at hw
    rw [infix_pair_iff faceVerts_pairwise]
    refine ⟨mem_faceVerts.mpr ⟨hw.1, by omega, ?_⟩, mem_faceVerts.mpr ⟨by omega, hw.2, ?_⟩,
      by omega, fun z _ hz => by omega⟩
    · intro t ht hts hne h
      exact hne (Within.antisymm hts (hmin t ht ⟨by simp only; omega, by simp only; omega⟩))
    · intro t ht hts hne h
      exact hne (Within.antisymm hts (hmin t ht ⟨by simp only; omega, by simp only; omega⟩))

/-! ### Parents -/

/-- **Every segment other than the root has a parent.** -/
theorem exists_parent (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    (hr : s ≠ (0, n - 1)) : ∃ p ∈ segs g n, IsChild g n p s := by
  classical
  let F := (segs g n).filter fun t => Within s t ∧ t ≠ s
  have hF : (0, n - 1) ∈ F := by
    simp only [F, Finset.mem_filter]
    exact ⟨hP.root_mem_segs, hP.within_root hs, fun h => hr h.symm⟩
  obtain ⟨p, hpF, hmin⟩ := F.exists_min_image segSize ⟨_, hF⟩
  simp only [F, Finset.mem_filter] at hpF
  refine ⟨p, hpF.1, hpF.2.2.symm, hpF.2.1, fun t ht hst htp => ?_⟩
  by_cases h : t = s
  · exact Or.inl h
  · right
    have := (hP.mem_segs.mp ht).2
    have := (hP.mem_segs.mp hpF.1).2
    have h1 := hmin t (by simp [F, ht, hst, h])
    simp only [segSize] at h1
    simp only [Within] at htp
    exact Prod.ext (by omega) (by omega)

/-- **The parent is unique.** -/
theorem parent_unique (hP : IsPolygon g n) {s p p' : ℕ × ℕ} (hs : s ∈ segs g n)
    (hp : p ∈ segs g n) (hp' : p' ∈ segs g n) (h : IsChild g n p s) (h' : IsChild g n p' s) :
    p = p' := by
  have hs' := hP.mem_segs.mp hs
  rcases hP.nested_of_within hp hp' (by omega) h.2.1 h'.2.1 with w | w
  · rcases h'.2.2 p hp h.2.1 w with e | e
    · exact absurd e.symm h.1
    · exact e
  · rcases h.2.2 p' hp' h'.2.1 w with e | e
    · exact absurd e.symm h'.1
    · exact e.symm

/-- The parent of a segment `s` strictly within a segment `t` lies within `t`. -/
theorem parent_within (hP : IsPolygon g n) {s p t : ℕ × ℕ} (hs : s ∈ segs g n)
    (hp : p ∈ segs g n) (ht : t ∈ segs g n) (h : IsChild g n p s) (hst : Within s t)
    (hne : s ≠ t) : Within p t := by
  have hs' := hP.mem_segs.mp hs
  rcases hP.nested_of_within hp ht (by omega) h.2.1 hst with w | w
  · exact w
  · rcases h.2.2 t ht hst w with e | e
    · exact absurd e.symm hne
    · rw [e]; exact Within.refl _

/-- The root has no parent. -/
theorem not_isChild_root (hP : IsPolygon g n) {p : ℕ × ℕ} (hp : p ∈ segs g n) :
    ¬ IsChild g n p (0, n - 1) := fun h =>
  h.1 (Within.antisymm h.2.1 (hP.within_root hp))

/-! ### The faces of an edge -/

/-- **A segment `e` lies on the faces `e` and its parent.** -/
theorem faces_of_seg (hP : IsPolygon g n) {e s : ℕ × ℕ} (he : e ∈ segs g n) (hs : s ∈ segs g n) :
    e ∈ faceEdges g n s ↔ s = e ∨ IsChild g n s e := by
  have he' := (hP.mem_segs.mp he).2
  rw [hP.mem_faceEdges_iff hs]
  constructor
  · rintro (rfl | ⟨-, hc⟩ | ⟨h, -⟩)
    · exact Or.inl rfl
    · exact Or.inr hc
    · omega
  · rintro (rfl | hc)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨he, hc⟩)

/-- **A side `(a, a + 1)` lies on exactly one face**: that of the smallest segment
containing it. -/
theorem faces_of_side (hP : IsPolygon g n) {a : ℕ} {s : ℕ × ℕ} (hs : s ∈ segs g n) :
    (a, a + 1) ∈ faceEdges g n s ↔
      Within (a, a + 1) s ∧ ∀ t ∈ segs g n, Within (a, a + 1) t → Within s t := by
  rw [hP.mem_faceEdges_iff hs, ← hP.side_infix_iff hs]
  have hs' := (hP.mem_segs.mp hs).2
  constructor
  · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
    · rw [← h] at hs'; simp at hs'
    · have := (hP.mem_segs.mp h).2; simp at this
    · exact h
  · intro h
    exact Or.inr (Or.inr ⟨rfl, h⟩)

/-- Two segments whose faces both contain a side are equal. -/
theorem eq_of_side_mem (hP : IsPolygon g n) {a : ℕ} {s t : ℕ × ℕ} (hs : s ∈ segs g n)
    (ht : t ∈ segs g n) (h1 : (a, a + 1) ∈ faceEdges g n s) (h2 : (a, a + 1) ∈ faceEdges g n t) :
    s = t := by
  rw [hP.faces_of_side hs] at h1
  rw [hP.faces_of_side ht] at h2
  exact Within.antisymm (h1.2 t ht h2.1) (h2.2 s hs h1.1)

/-! ### The weak dual is the segment tree -/

/-- **Adjacent faces** (Definition 26): two faces are adjacent in the weak dual exactly when
one is a child of the other in the segment tree; the shared edge is the child segment. -/
theorem dualAdj_iff (hP : IsPolygon g n) {s t : ℕ × ℕ} :
    DualAdj g n s t ↔ s ∈ segs g n ∧ t ∈ segs g n ∧ (IsChild g n s t ∨ IsChild g n t s) := by
  constructor
  · rintro ⟨hs, ht, hne, e, he⟩
    rw [Finset.mem_inter] at he
    refine ⟨hs, ht, ?_⟩
    obtain ⟨hadj, hlt⟩ := hP.adj_of_mem_faceEdges hs he.1
    by_cases h1 : e.2 = e.1 + 1
    · exfalso
      obtain ⟨a, b⟩ := e
      simp only at h1
      subst h1
      exact hne (hP.eq_of_side_mem hs ht he.1 he.2)
    · have hes : e ∈ segs g n := hP.mem_segs.mpr ⟨hadj, by omega⟩
      rcases (hP.faces_of_seg hes hs).mp he.1 with rfl | hc
      · rcases (hP.faces_of_seg hes ht).mp he.2 with rfl | hc'
        · exact absurd rfl hne
        · exact Or.inr hc'
      · rcases (hP.faces_of_seg hes ht).mp he.2 with rfl | hc'
        · exact Or.inl hc
        · exact absurd (hP.parent_unique hes hs ht hc hc') hne
  · rintro ⟨hs, ht, hc | hc⟩
    · exact ⟨hs, ht, hc.1.symm, t, Finset.mem_inter.mpr
        ⟨(hP.faces_of_seg ht hs).mpr (Or.inr hc), (hP.faces_of_seg ht ht).mpr (Or.inl rfl)⟩⟩
    · exact ⟨hs, ht, hc.1, s, Finset.mem_inter.mpr
        ⟨(hP.faces_of_seg hs hs).mpr (Or.inl rfl), (hP.faces_of_seg hs ht).mpr (Or.inr hc)⟩⟩

/-! ### Subtrees -/

/-- Every node of a rooted subtree lies within its root. -/
theorem rooted_within (hP : IsPolygon g n) {S : Finset (ℕ × ℕ)} {r : ℕ × ℕ}
    (h : IsRooted g n S r) {s : ℕ × ℕ} (hs : s ∈ S) : Within s r := by
  induction hm : n - segSize s using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    by_cases hsr : s = r
    · rw [hsr]; exact Within.refl _
    · obtain ⟨p, hp, hc⟩ := h.2.2 s hs hsr
      have hlt := hP.child_size_lt (h.2.1 hs) hc
      have hpn := (hP.lt_of_adj (hP.mem_segs.mp (h.2.1 hp)).1).2
      have : segSize p ≤ n := by simp only [segSize]; omega
      exact (hc.2.1).trans (ih _ (by omega) hp rfl)

/-- The symmetric closure of a symmetric relation is symmetric. -/
theorem reflTransGen_symm {α : Type*} {R : α → α → Prop} (hR : ∀ x y, R x y → R y x)
    {a b : α} (h : Relation.ReflTransGen R a b) : Relation.ReflTransGen R b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hR _ _ hbc) ih

/-- **Subtrees are rooted**: a set of faces is a subtree of the weak dual (nonempty and
connected) exactly when it has a node `r` such that every other node has its parent in the
set. -/
theorem isSubtree_iff (hP : IsPolygon g n) {S : Finset (ℕ × ℕ)} :
    IsSubtree g n S ↔ ∃ r, IsRooted g n S r := by
  constructor
  · rintro ⟨hne, hsub, hconn⟩
    obtain ⟨r, hr, hmax⟩ := S.exists_max_image segSize hne
    refine ⟨r, hr, hsub, fun s hs hsr => ?_⟩
    by_contra hno
    have key : ∀ y, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ DualAdj g n x y) s y →
        Within y s := by
      intro y hy
      induction hy with
      | refl => exact Within.refl _
      | @tail x y _ hxy ih =>
        obtain ⟨hx, hy, had⟩ := hxy
        rcases ((hP.dualAdj_iff).mp had).2.2 with hc | hc
        · exact hc.2.1.trans ih
        · by_cases hxs : x = s
          · subst hxs
            exact absurd ⟨y, hy, hc⟩ hno
          · exact hP.parent_within (hsub hx) (hsub hy) (hsub hs) hc ih hxs
    have hw := key r (hconn s hs r hr)
    have h1 := hmax s hs
    have := (hP.mem_segs.mp (hsub hs)).2
    have := (hP.mem_segs.mp (hsub hr)).2
    simp only [segSize] at h1
    simp only [Within] at hw
    exact hsr (Prod.ext (by omega) (by omega)).symm
  · rintro ⟨r, hr, hsub, hpar⟩
    refine ⟨⟨r, hr⟩, hsub, ?_⟩
    have hsymm : ∀ x y, (x ∈ S ∧ y ∈ S ∧ DualAdj g n x y) → (y ∈ S ∧ x ∈ S ∧ DualAdj g n y x) := by
      rintro x y ⟨hx, hy, h⟩
      refine ⟨hy, hx, (hP.dualAdj_iff).mpr ?_⟩
      obtain ⟨h1, h2, h3⟩ := (hP.dualAdj_iff).mp h
      exact ⟨h2, h1, h3.symm⟩
    have hto : ∀ s ∈ S, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ DualAdj g n x y) s r := by
      intro s hs
      induction hm : n - segSize s using Nat.strong_induction_on generalizing s with
      | _ m ih =>
        by_cases hsr : s = r
        · rw [hsr]
        · obtain ⟨p, hp, hc⟩ := hpar s hs hsr
          have hlt := hP.child_size_lt (hsub hs) hc
          have hpn := (hP.lt_of_adj (hP.mem_segs.mp (hsub hp)).1).2
          have : segSize p ≤ n := by simp only [segSize]; omega
          refine Relation.ReflTransGen.head ⟨hs, hp, (hP.dualAdj_iff).mpr
            ⟨hsub hs, hsub hp, Or.inr hc⟩⟩ (ih _ (by omega) p hp rfl)
    intro s hs t ht
    exact (hto s hs).trans (reflTransGen_symm hsymm (hto t ht))

end IsPolygon

end STACS2027
