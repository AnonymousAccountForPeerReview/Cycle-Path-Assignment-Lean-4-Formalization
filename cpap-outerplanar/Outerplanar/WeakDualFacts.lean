module

public import Outerplanar.WeakDualBij
public import Outerplanar.DPCorrect
import Mathlib.Tactic

/-!
# Lemmas 27 and 28: the weak dual and its leaves

Appendix F, Lemma 27 (`lem:face_boundary`) and Lemma 28 (`lem:dual_leaf`), in the polygon model
(`IsPolygon g n`: the positions `0, …, n - 1` in order form the outer Hamiltonian cycle `H`).
The bounded faces are the segments (`segs g n`, `r = |segs g n|`), the edges are `polyEdges g n`
(`m = |polyEdges g n|`), the chords `E \ E(H)` are the segments other than the outer edge
`(0, n - 1)` (`chords g n`), and the edges of the weak dual are the parent–child pairs of the
segment tree (`dualEdges g n`, each edge `{v_f, v_g}` once, as the pair (parent, child);
`dualAdj_iff_dualEdges`).

* `euler_face_count`: `r = m - n + 1`, as `r + n = m + 1` (Euler's formula; in the model the
  edges are the `n - 1` sides `(i, i + 1)` and the segments);
* `chord_dualEdge_bij`: the dual edge `(p, c)` is the pair of faces sharing the chord `c` (the only
  common edge of the two faces), and `(p, c) ↦ c` is a bijection from the dual edges onto the
  chords; in particular the weak dual has `r - 1` edges;
* `weakDual_tree`: the weak dual is connected with `r - 1` edges, a tree;
* `bdry_ne_empty`: `∂T ≠ ∅` for every nonempty set `T` of faces;
* `bdry_deg`: every vertex has degree `0` or `2` in `∂S` for a subtree `S` (a consequence
  of Lemma 29 here: `∂S` is the edge set of a cycle);
* `leaf_face`: a segment `s` without children (a leaf of the weak dual other than the root; one
  exists when `r ≥ 2`, `exists_leaf`) has a face whose only chord is `s` (its only neighbour
  in the weak dual is its parent), whose other boundary edges are the sides
  `(x, x + 1)`, `s.1 ≤ x < s.2` (the path `P` of the paper, with `s.2 - s.1 ≥ 2` edges), and
  whose inner vertices `s.1 < x < s.2` have degree `2` in `g`. Deletion of these vertices,
  with exact bounded-face and weak-dual transport including the root-leaf case, is proved
  in `LeafFaceDeletion.lean`.
-/

@[expose] public section

namespace STACS2027

open IsPolygon

variable {g : Graph} {n : ℕ}

/-- The chords: the edges of `g` not on the outer cycle, i.e. the segments other than the
outer edge `(0, n - 1)`. -/
def chords (g : Graph) (n : ℕ) : Finset (ℕ × ℕ) := (segs g n).erase (0, n - 1)

/-- The edges of the weak dual, each as the pair (parent, child) of the segment tree. -/
def dualEdges (g : Graph) (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((segs g n) ×ˢ (segs g n)).filter fun pc => IsChild g n pc.1 pc.2

/-- The degree `deg_F(w)` of `w` in an edge set `F`: the number of edges of `F` at `w`. -/
def degIn (F : Finset (ℕ × ℕ)) (w : ℕ) : ℕ := (F.filter fun e => e.1 = w ∨ e.2 = w).card

theorem mem_dualEdges {p c : ℕ × ℕ} :
    (p, c) ∈ dualEdges g n ↔ p ∈ segs g n ∧ c ∈ segs g n ∧ IsChild g n p c := by
  simp only [dualEdges, Finset.mem_filter, Finset.mem_product]
  tauto

namespace IsPolygon

/-! ### Lemma 27 (1) -/

/-- The edges of a polygon are the sides `(i, i + 1)` and the segments. -/
theorem polyEdges_eq (hP : IsPolygon g n) :
    polyEdges g n = (Finset.range (n - 1)).image (fun i => (i, i + 1)) ∪ segs g n := by
  ext e
  rw [hP.mem_polyEdges, Finset.mem_union, Finset.mem_image, hP.mem_segs]
  constructor
  · rintro ⟨hadj, hlt⟩
    by_cases h : e.2 = e.1 + 1
    · left
      have := (hP.lt_of_adj hadj).2
      exact ⟨e.1, Finset.mem_range.mpr (by omega), Prod.ext rfl h.symm⟩
    · exact Or.inr ⟨hadj, by omega⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨hadj, h⟩)
    · rw [Finset.mem_range] at hi
      exact ⟨hP.adj_succ (by omega), by simp⟩
    · exact ⟨hadj, by omega⟩

/-- **Lemma 27 (1), Euler's formula** (`r = m - n + 1`): the number `r` of bounded faces (the
segments) and the number `m` of edges satisfy `r + n = m + 1`. -/
theorem euler_face_count (hP : IsPolygon g n) : (segs g n).card + n = (polyEdges g n).card + 1 := by
  have h3 := hP.three_le
  rw [hP.polyEdges_eq, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_range]
  · omega
  · intro i j h
    simpa using congrArg Prod.fst h
  · rw [Finset.disjoint_left]
    intro e he hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
    have := (hP.mem_segs.mp hs).2
    simp at this

/-- The edges of the weak dual (Definition 26) are the parent–child pairs. -/
theorem dualAdj_iff_dualEdges (hP : IsPolygon g n) {s t : ℕ × ℕ} :
    DualAdj g n s t ↔ (s, t) ∈ dualEdges g n ∨ (t, s) ∈ dualEdges g n := by
  rw [hP.dualAdj_iff, mem_dualEdges, mem_dualEdges]
  tauto

/-- **Lemma 27 (1), chords and dual edges**: the two faces `p`, `c` of a dual edge share
exactly one edge, the chord `c`; and sending a dual edge to its chord, `(p, c) ↦ c`, is a
bijection from the edges of the weak dual onto the chords. In particular the weak dual has
`r - 1` edges. -/
theorem chord_dualEdge_bij (hP : IsPolygon g n) :
    (∀ p c, (p, c) ∈ dualEdges g n → faceEdges g n p ∩ faceEdges g n c = {c}) ∧
    Set.BijOn Prod.snd (dualEdges g n : Set ((ℕ × ℕ) × (ℕ × ℕ))) (chords g n : Set (ℕ × ℕ)) ∧
    (dualEdges g n).card + 1 = (segs g n).card := by
  have hmaps : Set.MapsTo Prod.snd (dualEdges g n : Set ((ℕ × ℕ) × (ℕ × ℕ)))
      (chords g n : Set (ℕ × ℕ)) := by
    rintro ⟨p, c⟩ h
    rw [Finset.mem_coe, mem_dualEdges] at h
    rw [Finset.mem_coe, chords, Finset.mem_erase]
    refine ⟨fun hc => ?_, h.2.1⟩
    have hc' : c = (0, n - 1) := hc
    rw [hc'] at h
    exact hP.not_isChild_root h.1 h.2.2
  have hinj : Set.InjOn Prod.snd (dualEdges g n : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
    rintro ⟨p, c⟩ h ⟨p', c'⟩ h' (he : c = c')
    subst he
    rw [Finset.mem_coe, mem_dualEdges] at h h'
    rw [hP.parent_unique h.2.1 h.1 h'.1 h.2.2 h'.2.2]
  have hsurj : Set.SurjOn Prod.snd (dualEdges g n : Set ((ℕ × ℕ) × (ℕ × ℕ)))
      (chords g n : Set (ℕ × ℕ)) := by
    intro c hc
    rw [Finset.mem_coe, chords, Finset.mem_erase] at hc
    obtain ⟨p, hp, hpc⟩ := hP.exists_parent hc.2 hc.1
    exact ⟨(p, c), by rw [Finset.mem_coe, mem_dualEdges]; exact ⟨hp, hc.2, hpc⟩, rfl⟩
  refine ⟨fun p c h => ?_, ⟨hmaps, hinj, hsurj⟩, ?_⟩
  · rw [mem_dualEdges] at h
    obtain ⟨hp, hc, hpc⟩ := h
    ext e
    rw [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨hadj, hlt⟩ := hP.adj_of_mem_faceEdges hp h1
      by_cases hside : e.2 = e.1 + 1
      · exfalso
        obtain ⟨a, b⟩ := e
        simp only at hside
        subst hside
        exact hpc.1 (hP.eq_of_side_mem hp hc h1 h2).symm
      · have hes : e ∈ segs g n := hP.mem_segs.mpr ⟨hadj, by omega⟩
        rcases (hP.faces_of_seg hes hc).mp h2 with h | h
        · exact h.symm
        · exfalso
          rcases (hP.faces_of_seg hes hp).mp h1 with h' | h'
          · subst h'
            exact hpc.1 (Within.antisymm hpc.2.1 h.2.1)
          · exact hpc.1 (hP.parent_unique hes hc hp h h')
    · rintro rfl
      exact ⟨(hP.faces_of_seg hc hp).mpr (Or.inr hpc), (hP.faces_of_seg hc hc).mpr (Or.inl rfl)⟩
  · rw [Finset.card_nbij Prod.snd hmaps hinj hsurj, chords,
      Finset.card_erase_of_mem hP.root_mem_segs]
    have := Finset.card_pos.mpr ⟨_, hP.root_mem_segs⟩
    omega

/-- **The weak dual is a tree** (Appendix F, citing ANONYMIZED): it is connected (the set of
all bounded faces is a subtree) and has `r - 1` edges. -/
theorem weakDual_tree (hP : IsPolygon g n) :
    IsSubtree g n (segs g n) ∧ (dualEdges g n).card + 1 = (segs g n).card :=
  ⟨(hP.isSubtree_iff).mpr ⟨(0, n - 1), hP.root_mem_segs, subset_refl _,
    fun _ hs hne => hP.exists_parent hs hne⟩, hP.chord_dualEdge_bij.2.2⟩

/-! ### Lemma 27 (2) -/

/-- **Lemma 27 (2)**: `∂T ≠ ∅` for every nonempty set `T` of bounded faces: the segment of a
largest face of `T` lies on that face and on no other face of `T`. -/
theorem bdry_ne_empty (hP : IsPolygon g n) {T : Finset (ℕ × ℕ)} (hne : T.Nonempty)
    (hT : T ⊆ segs g n) : bdry g n T ≠ ∅ := by
  obtain ⟨s, hs, hmax⟩ := T.exists_max_image segSize hne
  have hsseg := hT hs
  have hF : T.filter (fun t => s ∈ faceEdges g n t) = {s} := by
    ext t
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, h⟩
      rcases (hP.faces_of_seg hsseg (hT ht)).mp h with h | h
      · exact h
      · have h1 := hP.child_size_lt hsseg h
        have h2 := hmax t ht
        omega
    · rintro rfl
      exact ⟨hs, (hP.faces_of_seg hsseg hsseg).mpr (Or.inl rfl)⟩
  intro h
  have hmem : s ∈ bdry g n T := by
    rw [mem_bdry, hF, Finset.card_singleton]
    exact odd_one
  rw [h] at hmem
  simp at hmem

/-! ### Lemma 27 (3) -/

/-- Every vertex of a simple cycle lies on exactly two of its edges, and other vertices on
none. -/
theorem degIn_cycleEdges {k : ℕ} {c : Cycle} (hc : IsCycle g k c) (v : ℕ) :
    degIn (cycleEdges c).toFinset v = if v ∈ c then 2 else 0 := by
  have hev : ∀ a b, ((edge a b).1 = v ∨ (edge a b).2 = v) ↔ (a = v ∨ b = v) := by
    intro a b
    simp only [edge]
    omega
  split_ifs with hv
  · obtain ⟨rest, hr, hsame, -⟩ := hc.rotate_to_vertex hv
    have hfin : (cycleEdges c).toFinset = (cycleEdges (v :: rest)).toFinset := by
      ext e
      simp only [List.mem_toFinset]
      exact ⟨hsame.1 e, hsame.2 e⟩
    rw [hfin]
    have hl := hr.2.1
    have hk := hr.1
    obtain ⟨w, rest', rfl⟩ : ∃ w rest', rest = w :: rest' := by
      cases rest with
      | nil => simp at hl; omega
      | cons w rest' => exact ⟨w, rest', rfl⟩
    obtain ⟨mid, z, rfl⟩ : ∃ mid z, rest' = mid ++ [z] := by
      rcases List.eq_nil_or_concat rest' with h | ⟨mid, z, h⟩
      · subst h
        simp at hl
        omega
      · exact ⟨mid, z, by simpa using h⟩
    have hnd := hr.2.2.1
    have hvl : v ∉ w :: (mid ++ [z]) := (List.nodup_cons.mp hnd).1
    have hwz : w ≠ z := by
      intro h
      subst h
      have := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      exact this (by simp)
    have hvw : v ≠ w := fun h => hvl (by simp [h])
    have hvz : v ≠ z := fun h => hvl (by simp [h])
    have hce : cycleEdges (v :: (w :: (mid ++ [z]))) =
        edge v w :: (pathEdges (w :: (mid ++ [z])) ++ [edge z v]) := by
      rw [show v :: (w :: (mid ++ [z])) = v :: ((w :: mid) ++ [z]) by simp, cycleEdges_snoc]
      simp [pathEdges]
    have hF : (cycleEdges (v :: (w :: (mid ++ [z])))).toFinset.filter
        (fun e => e.1 = v ∨ e.2 = v) = {edge v w, edge z v} := by
      ext e
      rw [Finset.mem_filter, List.mem_toFinset, hce, Finset.mem_insert, Finset.mem_singleton]
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨h | h | h, hv'⟩
        · exact Or.inl h
        · exfalso
          obtain ⟨xs, a, b, ys, hsplit, rfl⟩ := mem_pathEdges_iff.mp h
          have ha : a ∈ w :: (mid ++ [z]) := by rw [hsplit]; simp
          have hb : b ∈ w :: (mid ++ [z]) := by rw [hsplit]; simp
          rcases (hev a b).mp hv' with rfl | rfl
          · exact hvl ha
          · exact hvl hb
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, (hev v w).mpr (Or.inl rfl)⟩
        · exact ⟨Or.inr (Or.inr rfl), (hev z v).mpr (Or.inr rfl)⟩
    rw [degIn, hF, Finset.card_insert_of_notMem, Finset.card_singleton]
    rw [Finset.mem_singleton, edge_eq_iff]
    omega
  · rw [degIn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hev'
    rw [List.mem_toFinset] at he
    obtain ⟨xs, a, b, ys, hsplit, rfl⟩ := mem_pathEdges_iff.mp he
    have := mem_of_mem_cycleEdges (show edge a b ∈ cycleEdges c from he)
    rcases (hev a b).mp hev' with rfl | rfl
    · exact hv this.1
    · exact hv this.2

/-- **Lemma 27 (3)**: for every subtree `S` of the weak dual and every vertex `v`,
`deg_{∂S}(v) ∈ {0, 2}`. -/
theorem bdry_deg (hP : IsPolygon g n) {S : Finset (ℕ × ℕ)} (hS : IsSubtree g n S) (v : ℕ) :
    degIn (bdry g n S) v = 0 ∨ degIn (bdry g n S) v = 2 := by
  obtain ⟨u, ⟨hu, hb, -⟩, -⟩ := hP.cycle_subtree_bij.2.1 S hS
  rw [← hb, degIn_cycleEdges hu.isCycle]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ### Lemma 28 -/

/-- When there are at least two bounded faces, some segment other than the root has no
children: a leaf of the weak dual other than the root. -/
theorem exists_leaf (hP : IsPolygon g n) (h2 : 2 ≤ (segs g n).card) :
    ∃ s ∈ segs g n, s ≠ (0, n - 1) ∧ ∀ t ∈ segs g n, ¬ IsChild g n s t := by
  obtain ⟨s, hs, hmin⟩ := (segs g n).exists_min_image segSize
    (Finset.card_pos.mp (by omega))
  refine ⟨s, hs, fun hr => ?_, fun t ht hc => ?_⟩
  · obtain ⟨t, ht, hne⟩ := Finset.exists_mem_ne h2 s
    have hw := hP.within_root ht
    have h1 := hmin t ht
    have h2 := (hP.mem_segs.mp ht).2
    rw [hr] at h1 hne
    simp only [segSize, Within] at h1 hw
    exact hne (Prod.ext (by omega) (by omega))
  · have := hP.child_size_lt ht hc
    have := hmin t ht
    omega

/-- **Lemma 28** (`lem:dual_leaf`), in the polygon model: let `s` be a segment without children
(a leaf `v_f` of the weak dual other than the root, see `exists_leaf`). Then

1. the face of `s` has the vertices `s.1, s.1 + 1, …, s.2`; its edges are `s` and the sides
   `(x, x + 1)`, `s.1 ≤ x < s.2`, of the outer cycle, so `s` is its only chord and `∂f \ {s}`
   is the path `P` of the `s.2 - s.1 ≥ 2` sides from `s.1` to `s.2`; the only neighbour of
   `s` in the weak dual is its parent;
2. every inner vertex `x` of `P` (`s.1 < x < s.2`) has degree `2` in `g`: its neighbours are
   `x - 1` and `x + 1`. -/
theorem leaf_face (hP : IsPolygon g n) {s : ℕ × ℕ} (hs : s ∈ segs g n)
    (hleaf : ∀ t ∈ segs g n, ¬ IsChild g n s t) :
    faceVerts g n s = List.range' s.1 (s.2 + 1 - s.1) ∧
    (∀ e, e ∈ faceEdges g n s ↔ e = s ∨ (e.2 = e.1 + 1 ∧ s.1 ≤ e.1 ∧ e.2 ≤ s.2)) ∧
    (∀ t, DualAdj g n s t ↔ t ∈ segs g n ∧ IsChild g n t s) ∧
    (∀ x, s.1 < x → x < s.2 → ∀ y, Adj g x y ↔ y + 1 = x ∨ y = x + 1) := by
  have hs' := hP.mem_segs.mp hs
  have hsn := (hP.lt_of_adj hs'.1).2
  -- no segment lies strictly within `s`
  have hnone : ∀ t ∈ segs g n, Within t s → t = s := by
    intro t ht hts
    by_contra hne
    obtain ⟨c, hc, hch, -⟩ := hP.exists_child hs ht hts hne
    exact hleaf c hc hch
  have hfv : ∀ x, IsFaceVert g n s x := fun x t ht hts hne => absurd (hnone t ht hts) hne
  have hverts : faceVerts g n s = List.range' s.1 (s.2 + 1 - s.1) := by
    rw [faceVerts, List.filter_eq_self]
    intro x _
    exact decide_eq_true (hfv x)
  refine ⟨hverts, fun e => ?_, fun t => ?_, fun x hx1 hx2 y => ?_⟩
  · rw [hP.mem_faceEdges_iff hs]
    constructor
    · rintro (h | ⟨he, hc⟩ | ⟨h, hi⟩)
      · exact Or.inl h
      · exact absurd hc (hleaf e he)
      · obtain ⟨hx, hy, -, -⟩ := (infix_pair_iff faceVerts_pairwise).mp hi
        exact Or.inr ⟨h, (mem_faceVerts.mp hx).1, (mem_faceVerts.mp hy).2.1⟩
    · rintro (h | ⟨h, h1, h2⟩)
      · exact Or.inl h
      · refine Or.inr (Or.inr ⟨h, ?_⟩)
        rw [infix_pair_iff faceVerts_pairwise, mem_faceVerts, mem_faceVerts]
        exact ⟨⟨h1, by omega, hfv _⟩, ⟨by omega, h2, hfv _⟩, by omega, fun z _ hz => by omega⟩
  · rw [hP.dualAdj_iff]
    constructor
    · rintro ⟨-, ht, hc | hc⟩
      · exact absurd hc (hleaf t ht)
      · exact ⟨ht, hc⟩
    · rintro ⟨ht, hc⟩
      exact ⟨hs, ht, Or.inr hc⟩
  · constructor
    · intro hxy
      by_contra hne
      have hxy' := hxy
      have hab : Adj g (min x y) (max x y) := by
        rcases Nat.le_total x y with h | h
        · rw [Nat.min_eq_left h, Nat.max_eq_right h]
          exact hxy
        · rw [Nat.min_eq_right h, Nat.max_eq_left h]
          exact hxy.symm
      have hne' : x ≠ y := hxy'.1
      have hseg : (min x y, max x y) ∈ segs g n := hP.mem_segs.mpr ⟨hab, by simp only; omega⟩
      rcases hP.laminar hab hs'.1 (by omega) (by omega) with w | w | w | w
      · have := hnone _ hseg w
        rw [Prod.ext_iff] at this
        simp only at this
        omega
      · simp only [Within] at w
        omega
      · omega
      · omega
    · rintro (h | h)
      · rw [← h]
        exact (hP.adj_succ (by omega)).symm
      · rw [h]
        exact hP.adj_succ (by omega)

end IsPolygon

end STACS2027
