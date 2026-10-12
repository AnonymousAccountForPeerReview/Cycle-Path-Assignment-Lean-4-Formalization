module

public import Outerplanar.OuterplanarConstructGlue

/-!
# Gluing spherical outerplanar embeddings at a common vertex

`SphOuter.append_glue`: spherical outerplanar embeddings of two edge lists whose only
common vertex is `c` give one of their concatenation, by `glueMap` at a half-edge at `c` on
the outer face of each (`outer_dart_at`). `SphOuter.append_cut` combines it with the
disjoint union: at most one common vertex.
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar PlanarGluing

section DisjointSum

variable {n m : Nat} (G : Hypermap n) (H : Hypermap m)

theorem disjointSum_node_reaches_left {x y : Fin n} :
    Reaches (disjointSum G H).node (left x) (left y) ↔ Reaches G.node x y := by
  constructor
  · rintro ⟨k, hk⟩
    rw [disjointSum_iterate_node_left] at hk
    exact ⟨k, left_injective hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [disjointSum_iterate_node_left, hk]⟩

theorem disjointSum_node_reaches_right {x y : Fin m} :
    Reaches (disjointSum G H).node (right x) (right y) ↔ Reaches H.node x y := by
  constructor
  · rintro ⟨k, hk⟩
    rw [disjointSum_iterate_node_right] at hk
    exact ⟨k, right_injective hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [disjointSum_iterate_node_right, hk]⟩

theorem disjointSum_node_not_lr (x : Fin n) (y : Fin m) :
    ¬ Reaches (disjointSum G H).node (left x) (right y) := by
  rintro ⟨k, hk⟩
  rw [disjointSum_iterate_node_left] at hk
  exact left_ne_right _ _ hk

theorem disjointSum_node_not_rl (x : Fin m) (y : Fin n) :
    ¬ Reaches (disjointSum G H).node (right x) (left y) := by
  rintro ⟨k, hk⟩
  rw [disjointSum_iterate_node_right] at hk
  exact left_ne_right _ _ hk.symm

theorem disjointSum_node_sep (a : Fin n) (b : Fin m) :
    cmin (disjointSum G H).node (left a) ≠ cmin (disjointSum G H).node (right b) := fun h =>
  disjointSum_node_not_lr G H a b ((cmin_eq_iff_reaches (hm_node_inj _) _ _).mp h)

theorem disjointSum_face_sep (a : Fin n) (b : Fin m) :
    cmin (disjointSum G H).face (left a) ≠ cmin (disjointSum G H).face (right b) := by
  intro h
  obtain ⟨k, hk⟩ := (cmin_eq_iff_reaches (hm_face_inj _) _ _).mp h
  rw [disjointSum_iterate_face_left] at hk
  exact left_ne_right _ _ hk

end DisjointSum

/-- A half-edge at a vertex `c` on the outer face of its component. -/
theorem outer_dart_at {V : Type} {es : List (V × V)} {G : Hypermap (2 * es.length)}
    (hN : ∀ d d', (∃ k, iterate G.node k d = d') ↔ halfEdgeEnd es d.val = halfEdgeEnd es d'.val)
    (hO : OuterFaceCond G) {c : V} {a0 : Fin (2 * es.length)}
    (ha0 : halfEdgeEnd es a0.val = some c) :
    ∃ a x : Fin (2 * es.length), halfEdgeEnd es a.val = some c ∧ Reaches G.face x a ∧
      ∀ d', LinkedPath G a d' → ∃ j k, iterate G.face j x = iterate G.node k d' := by
  obtain ⟨x, hx⟩ := hO a0
  obtain ⟨j0, k0, h0⟩ := hx a0 (Linked.linked_refl G _ a0)
  refine ⟨iterate G.face j0 x, x, ?_, ⟨j0, rfl⟩, fun d' hd' => ?_⟩
  · rw [← ha0]
    exact ((hN a0 _).mp ⟨k0, h0.symm⟩).symm
  · have h1 : LinkedPath G a0 (iterate G.face j0 x) := by
      rw [h0]; exact nodeOrbit_linked G ⟨k0, rfl⟩
    obtain ⟨k1, hk1⟩ := h1.trans hd'
    exact hx d' (Linked.linked_stable G hk1)

/-- The dart `x` of the outer-face condition at `d` is linked to `d`. -/
theorem outer_linked {n : Nat} {G : Hypermap n} {d x : Fin n}
    (hx : ∀ d', G.linked n d d' = true → ∃ j k, iterate G.face j x = iterate G.node k d') :
    LinkedPath G d x := by
  obtain ⟨j, k, h⟩ := hx d (Linked.linked_refl G _ d)
  have h1 : LinkedPath G d (iterate G.face j x) := by
    rw [h]; exact nodeOrbit_linked G ⟨k, rfl⟩
  exact h1.trans (faceOrbit_linked G ⟨j, rfl⟩).symm

/-- **Gluing at a vertex.** Spherical outerplanar embeddings of two edge lists whose only
common vertex is `c` (an end of both) give one of their concatenation. -/
theorem SphOuter.append_glue {V : Type} {es ts : List (V × V)} (h1 : SphOuter es)
    (h2 : SphOuter ts) (c : V)
    (hc1 : ∃ d : Fin (2 * es.length), halfEdgeEnd es d.val = some c)
    (hc2 : ∃ d : Fin (2 * ts.length), halfEdgeEnd ts d.val = some c)
    (hcom : ∀ (d : Fin (2 * es.length)) (d' : Fin (2 * ts.length)),
      halfEdgeEnd es d.val = halfEdgeEnd ts d'.val → halfEdgeEnd es d.val = some c) :
    SphOuter (es ++ ts) := by
  obtain ⟨G, hE, hN, hS, hO⟩ := h1
  obtain ⟨H, hE', hN', hS', hO'⟩ := h2
  obtain ⟨a0, ha0⟩ := hc1
  obtain ⟨b0, hb0⟩ := hc2
  obtain ⟨a, x1, ha, hxa, hla⟩ := outer_dart_at hN hO ha0
  obtain ⟨b, x2, hb, hxb, hlb⟩ := outer_dart_at hN' hO' hb0
  unfold SphOuter
  rw [List.length_append, Nat.mul_add]
  have hsepN := disjointSum_node_sep G H a b
  have hsepF := disjointSum_face_sep G H a b
  have hsepC := disjointSum_left_ne_right G H a b
  have hab : LinkedPath (glueMap (disjointSum G H) (left a) (right b)) (left a) (right b) :=
    nodeOrbit_linked _ (transpose_merge_markers (hm_node_inj _) _ _ hsepN)
  have hl : ∀ d : Fin (2 * es.length),
      halfEdgeEnd (es ++ ts) (left (m := 2 * ts.length) d).val = halfEdgeEnd es d.val :=
    fun d => halfEdgeEnd_append_left es ts d.val d.isLt
  have hr : ∀ d : Fin (2 * ts.length),
      halfEdgeEnd (es ++ ts) (right (n := 2 * es.length) d).val = halfEdgeEnd ts d.val := by
    intro d
    rw [halfEdgeEnd_append_right es ts _ (by simp [right])]
    simp [right]
  refine ⟨glueMap (disjointSum G H) (left a) (right b),
    disjointSum_graphEdge G H (fun d => Fin.ext (hE d)) (fun d => Fin.ext (hE' d)), ?_, ?_, ?_⟩
  · -- the node condition
    intro x y
    change Reaches (transpose (disjointSum G H).node (left a) (right b)) x y ↔ _
    rw [transpose_reaches_iff (hm_node_inj _) hsepN]
    -- the merged class consists of the half-edges at `c`
    have hmerged : ∀ z, (Reaches (disjointSum G H).node z (left a) ∨
        Reaches (disjointSum G H).node z (right b)) ↔
        halfEdgeEnd (es ++ ts) z.val = some c := by
      intro z
      rcases cases_dart z with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · rw [disjointSum_node_reaches_left, hl, ← ha]
        constructor
        · rintro (h | h)
          · exact (hN z a).mp h
          · exact absurd h (disjointSum_node_not_lr G H z b)
        · exact fun h => Or.inl ((hN z a).mpr h)
      · rw [disjointSum_node_reaches_right, hr, ← hb]
        constructor
        · rintro (h | h)
          · exact absurd h (disjointSum_node_not_rl G H z a)
          · exact (hN' z b).mp h
        · exact fun h => Or.inr ((hN' z b).mpr h)
    have hsame : ∀ x y, Reaches (disjointSum G H).node x y →
        halfEdgeEnd (es ++ ts) x.val = halfEdgeEnd (es ++ ts) y.val := by
      intro x y h
      rcases cases_dart x with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rcases cases_dart y with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [hl, hl]; exact (hN x y).mp ((disjointSum_node_reaches_left G H).mp h)
      · exact absurd h (disjointSum_node_not_lr G H x y)
      · exact absurd h (disjointSum_node_not_rl G H x y)
      · rw [hr, hr]; exact (hN' x y).mp ((disjointSum_node_reaches_right G H).mp h)
    constructor
    · rintro (h | ⟨hx, hy⟩)
      · exact hsame x y h
      · rw [(hmerged x).mp hx, (hmerged y).mp hy]
    · intro he
      rcases cases_dart x with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rcases cases_dart y with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [hl, hl] at he
        exact Or.inl ((disjointSum_node_reaches_left G H).mpr ((hN x y).mpr he))
      · rw [hl, hr] at he
        have hc := hcom x y he
        right
        exact ⟨(hmerged _).mpr (by rw [hl, hc]), (hmerged _).mpr (by rw [hr, ← he, hc])⟩
      · rw [hr, hl] at he
        have hc := hcom y x he.symm
        right
        exact ⟨(hmerged _).mpr (by rw [hr, he, hc]), (hmerged _).mpr (by rw [hl, hc])⟩
      · rw [hr, hr] at he
        exact Or.inl ((disjointSum_node_reaches_right G H).mpr ((hN' x y).mpr he))
  · -- the spherical inequality
    have hC := glue_components hab hsepC
    have hCD := disjointSum_components_le G H
    have hNc := transpose_merge_cycles (hm_node_inj _) _ _ hsepN
    have hFc := swapComp_cycles (hm_face_inj _) hsepF
    have hEs : cycleCount G.edge + cycleCount H.edge ≤ cycleCount (disjointSum G H).edge :=
      sumPerm_cycles_ge (hm_edge_inj G) (hm_edge_inj H)
    have hNs : cycleCount G.node + cycleCount H.node ≤ cycleCount (disjointSum G H).node :=
      sumPerm_cycles_ge (hm_node_inj G) (hm_node_inj H)
    have hFs : cycleCount G.face + cycleCount H.face ≤ cycleCount (disjointSum G H).face :=
      sumPerm_cycles_ge (hm_face_inj G) (hm_face_inj H)
    unfold Hypermap.eulerRhs at hS hS' ⊢
    change 2 * (glueMap (disjointSum G H) (left a) (right b)).componentCount +
        (2 * es.length + 2 * ts.length) ≤
      cycleCount (disjointSum G H).edge +
        cycleCount (transpose (disjointSum G H).node (left a) (right b)) +
        cycleCount (fun y => swap (left a) (right b) ((disjointSum G H).face y))
    omega
  · -- the outer face
    intro d
    by_cases hM : LinkedPath (disjointSum G H) d (left a) ∨
      LinkedPath (disjointSum G H) d (right b)
    · refine ⟨left a, fun d' hd' => ?_⟩
      have hM' : LinkedPath (disjointSum G H) d' (left a) ∨
          LinkedPath (disjointSum G H) d' (right b) := by
        rcases glue_linked_cases _ _ _ ⟨_, hd'⟩ with h | ⟨_, h⟩
        · rcases hM with hM | hM
          · exact Or.inl (h.symm.trans hM)
          · exact Or.inr (h.symm.trans hM)
        · exact h
      rcases hM' with hM' | hM'
      · obtain ⟨a', rfl, ha'⟩ := disjointSum_linked_left G H hM'.symm
        obtain ⟨j, k, hjk⟩ := hla a' ha'
        obtain ⟨i, hi⟩ := (hxa.symm (hm_face_inj G)).trans (⟨j, rfl⟩ : Reaches G.face x1 _)
        obtain ⟨j', hj'⟩ := swapComp_reaches (hm_face_inj _) hsepF
          (Or.inl ⟨i, by rw [disjointSum_iterate_face_left, hi]⟩)
        obtain ⟨k', hk'⟩ := transpose_merge_orbit (hm_node_inj _) _ _ hsepN
          (⟨k, disjointSum_iterate_node_left G H k a'⟩ :
            Reaches (disjointSum G H).node (left a') (left (iterate G.node k a')))
        exact ⟨j', k', hj'.trans (hjk ▸ hk'.symm)⟩
      · obtain ⟨b', rfl, hb'⟩ := disjointSum_linked_right G H hM'.symm
        obtain ⟨j, k, hjk⟩ := hlb b' hb'
        obtain ⟨i, hi⟩ := (hxb.symm (hm_face_inj H)).trans (⟨j, rfl⟩ : Reaches H.face x2 _)
        obtain ⟨j', hj'⟩ := swapComp_reaches (hm_face_inj _) hsepF
          (Or.inr ⟨i, by rw [disjointSum_iterate_face_right, hi]⟩)
        obtain ⟨k', hk'⟩ := transpose_merge_orbit (hm_node_inj _) _ _ hsepN
          (⟨k, disjointSum_iterate_node_right G H k b'⟩ :
            Reaches (disjointSum G H).node (right b') (right (iterate H.node k b')))
        exact ⟨j', k', hj'.trans (hjk ▸ hk'.symm)⟩
    · -- away from the glued components nothing changes
      have hface : ∀ z, LinkedPath (disjointSum G H) d z →
          (glueMap (disjointSum G H) (left a) (right b)).face z = (disjointSum G H).face z := by
        intro z hz
        rw [glueMap_face]
        apply swap_other
        · intro he
          exact hM (Or.inl (he ▸ hz.trans (LinkedPath.step _ (Or.inr (Or.inr rfl)))))
        · intro he
          exact hM (Or.inr (he ▸ hz.trans (LinkedPath.step _ (Or.inr (Or.inr rfl)))))
      have hnode : ∀ z, LinkedPath (disjointSum G H) d z →
          (glueMap (disjointSum G H) (left a) (right b)).node z = (disjointSum G H).node z := by
        intro z hz
        rw [glueMap_node, swap_other]
        · intro he; exact hM (Or.inl (he ▸ hz))
        · intro he; exact hM (Or.inr (he ▸ hz))
      have hfi := iterate_eq_of_closed
        (fun z hz => hz.trans (LinkedPath.step _ (Or.inr (Or.inr rfl)))) hface
      have hni := iterate_eq_of_closed
        (fun z hz => hz.trans (LinkedPath.step _ (Or.inr (Or.inl rfl)))) hnode
      have hD : ∀ d', (glueMap (disjointSum G H) (left a) (right b)).linked
          (2 * es.length + 2 * ts.length) d d' = true → LinkedPath (disjointSum G H) d d' := by
        intro d' hd'
        rcases glue_linked_cases _ _ _ ⟨_, hd'⟩ with h | ⟨h, _⟩
        · exact h
        · exact absurd h hM
      rcases cases_dart d with ⟨a1, rfl⟩ | ⟨b1, rfl⟩
      · obtain ⟨x, hx⟩ := hO a1
        refine ⟨left x, fun d' hd' => ?_⟩
        have hdd' := hD d' hd'
        obtain ⟨a', rfl, k0, hk0⟩ := disjointSum_linked_left G H hdd'
        obtain ⟨j, k, hjk⟩ := hx a' (Linked.linked_stable G hk0)
        have hx1 : LinkedPath (disjointSum G H) (left a1) (left x) :=
          disjointSum_left_path G H (outer_linked hx)
        refine ⟨j, k, ?_⟩
        rw [hfi j _ hx1, hni k _ hdd', disjointSum_iterate_face_left,
          disjointSum_iterate_node_left, hjk]
      · obtain ⟨x, hx⟩ := hO' b1
        refine ⟨right x, fun d' hd' => ?_⟩
        have hdd' := hD d' hd'
        obtain ⟨b', rfl, k0, hk0⟩ := disjointSum_linked_right G H hdd'
        obtain ⟨j, k, hjk⟩ := hx b' (Linked.linked_stable H hk0)
        have hx1 : LinkedPath (disjointSum G H) (right b1) (right x) :=
          disjointSum_right_path G H (outer_linked hx)
        refine ⟨j, k, ?_⟩
        rw [hfi j _ hx1, hni k _ hdd', disjointSum_iterate_face_right,
          disjointSum_iterate_node_right, hjk]

/-- Every end of an edge is the end of a half-edge. -/
theorem exists_dart_of_isEnd {V : Type} {es : List (V × V)} {v : V}
    (h : ∃ e ∈ es, v = e.1 ∨ v = e.2) :
    ∃ d : Fin (2 * es.length), halfEdgeEnd es d.val = some v := by
  obtain ⟨e, he, hv⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hh := halfEdgeEnd_of_getElem? es i es[i].1 es[i].2 (by simp [hi])
  rcases hv with rfl | rfl
  · exact ⟨⟨2 * i, by omega⟩, hh.1⟩
  · exact ⟨⟨2 * i + 1, by omega⟩, hh.2⟩

/-- **At most one common vertex.** Spherical outerplanar embeddings of two edge lists all of
whose common vertices are `c` give one of their concatenation. -/
theorem SphOuter.append_cut {V : Type} {es ts : List (V × V)} (h1 : SphOuter es)
    (h2 : SphOuter ts) (c : V)
    (hc : ∀ v, (∃ e ∈ es, v = e.1 ∨ v = e.2) → (∃ e ∈ ts, v = e.1 ∨ v = e.2) → v = c) :
    SphOuter (es ++ ts) := by
  have hcom : ∀ (d : Fin (2 * es.length)) (d' : Fin (2 * ts.length)),
      halfEdgeEnd es d.val = halfEdgeEnd ts d'.val → halfEdgeEnd es d.val = some c := by
    intro d d' he
    obtain ⟨v, hv, hve⟩ := halfEdgeEnd_isEnd es d.isLt
    obtain ⟨v', hv', hve'⟩ := halfEdgeEnd_isEnd ts d'.isLt
    rw [hv, hv', Option.some.injEq] at he
    subst he
    rw [hv, hc v hve hve']
  by_cases h : (∃ e ∈ es, c = e.1 ∨ c = e.2) ∧ (∃ e ∈ ts, c = e.1 ∨ c = e.2)
  · exact h1.append_glue h2 c (exists_dart_of_isEnd h.1) (exists_dart_of_isEnd h.2) hcom
  · refine h1.append_disjoint h2 (fun d d' he => ?_)
    have hc' := hcom d d' he
    obtain ⟨v, hv, hve⟩ := halfEdgeEnd_isEnd es d.isLt
    obtain ⟨v', hv', hve'⟩ := halfEdgeEnd_isEnd ts d'.isLt
    rw [hv, Option.some.injEq] at hc'
    rw [hv, hv', Option.some.injEq] at he
    subst hc' he
    exact h ⟨hve, hve'⟩

end STACS2027
