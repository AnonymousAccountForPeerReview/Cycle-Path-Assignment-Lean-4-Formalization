module

public import Outerplanar.OuterplanarDef
public import NPHardness.PlanarPreprocessDeletionGraph
public import NPHardness.PlanarPreprocessDeletionComponents

/-!
# Outerplanar embeddings are closed under edge deletion

The hypermap-level half of the closure of outerplanar drawings under minors (Lemma 19).
`OuterFaces G` says that every connected component of the hypermap `G` has a face meeting
every vertex (`node` cycle) of the component — the extra condition of `OuterplanarEmbedding`
(`outerFaces_iff`). Deleting an edge is Section 5's surgery `cut` (the edge pair becomes two
fixed darts, the face permutation is composed with the transposition of the two darts)
followed by the excision `shrinkLast` of the two fixed darts. We show:

* `outerFaces_shrinkLast`: excising a dart fixed by `edge` keeps `OuterFaces` (a removed
  incidence of a face with a vertex is witnessed again by the next dart of the face);
* `outerFaces_cut`: cutting an edge of a planar hypermap keeps `OuterFaces`, given Euler's
  inequality for hypermaps (`HypermapEuler`). If the two darts of the edge lie on different
  faces, these faces merge and components do not change. If they lie on the same face, Euler's
  inequality for the cut map shows that the edge was a bridge (the two darts are no longer
  linked, `cut_not_linked_of_same_face`); then that face was the outer face of the component,
  and each of its two parts meets every vertex of its new component.
* `OuterplanarEmbedding.dropLast`: deleting the last edge of an outerplanar embedding.
-/

@[expose] public section

namespace STACS2027.OuterplanarMinor
open Complexity Complexity.Planar STACS2027.PlanarGluing STACS2027.PlanarPreprocess
open STACS2027.PlanarPreprocess.Deletion

/-- Every connected component of `G` has a face (the orbit of `x` under `face`) meeting the
vertex (`node` orbit) of every dart of the component. -/
def OuterFaces {n : Nat} (G : Hypermap n) : Prop :=
  ∀ d, ∃ x, ∀ d', LinkedPath G d d' → ∃ y, Reaches G.face x y ∧ Reaches G.node d' y

/-- `OuterFaces` is the face condition of `OuterplanarEmbedding`. -/
theorem outerFaces_iff {n : Nat} (G : Hypermap n) :
    OuterFaces G ↔ ∀ d, ∃ x, ∀ d', G.linked n d d' = true →
      ∃ j k, iterate G.face j x = iterate G.node k d' := by
  constructor
  · intro h d
    obtain ⟨x, hx⟩ := h d
    refine ⟨x, fun d' hl => ?_⟩
    obtain ⟨y, ⟨j, hj⟩, ⟨k, hk⟩⟩ := hx d' ⟨n, hl⟩
    exact ⟨j, k, hj.trans hk.symm⟩
  · intro h d
    obtain ⟨x, hx⟩ := h d
    refine ⟨x, fun d' hd' => ?_⟩
    obtain ⟨k, hl⟩ := hd'
    obtain ⟨j, k, hjk⟩ := hx d' (Linked.linked_stable G hl)
    exact ⟨_, ⟨j, rfl⟩, ⟨k, hjk.symm⟩⟩

/-! ## Generic facts on orbits and paths -/

theorem iterate_fixed {α : Type} {p : α → α} {x : α} (h : p x = x) (k : Nat) :
    iterate p k x = x := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [iterate, h] using ih

theorem reaches_of_ne {α : Type} {p : α → α} {x y : α} (h : Reaches p x y) (hne : y ≠ x) :
    Reaches p (p x) y := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => exact absurd hk.symm hne
  | succ k => exact ⟨k, hk⟩

/-- Paths transfer between hypermaps on the same darts when every step does. -/
theorem linkedPath_of_steps {n : Nat} {G H : Hypermap n}
    (hs : ∀ x y, Linked.Step G x y → LinkedPath H x y) {x y : Fin n}
    (h : LinkedPath G x y) : LinkedPath H x y := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at hk; subst y; exact LinkedPath.refl _ _
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp hk with h | ⟨z, hz, hst⟩
    · exact ih h
    · exact (ih hz).trans (hs z y hst)

/-- Components do not multiply when every step of `G` is a path of `H`. -/
theorem componentCount_le_of_steps {n : Nat} {G H : Hypermap n}
    (hs : ∀ x y, Linked.Step G x y → LinkedPath H x y) :
    H.componentCount ≤ G.componentCount := by
  have h := componentCount_le H (ComponentRoot G) (by
    intro x hx
    have hx' : compMin G x ≠ x.val := by
      intro he
      have hroot := (componentRoot_iff G x).mpr he
      rw [hroot] at hx
      contradiction
    have hle := (compMin_spec G x).2 x (Linked.linked_refl G n x)
    obtain ⟨k, hk⟩ := linkedPath_of_steps hs ⟨n, componentRep_linked G x⟩
    exact ⟨componentRep G x, by change compMin G x < x.val; omega, k, hk⟩)
  exact h

/-- Along an orbit of `p`, every dart is reached by `transpose p a b` from the start or from
one of the two marked darts. -/
theorem transpose_reaches_three {n : Nat} {p : Fin n → Fin n} {a b : Fin n} (hab : a ≠ b)
    {x y : Fin n} (h : Reaches p x y) :
    Reaches (transpose p a b) x y ∨ Reaches (transpose p a b) a y ∨
      Reaches (transpose p a b) b y := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => exact Or.inl (Reaches.refl _ _)
  | succ k ih =>
    rw [iterate_succ']
    by_cases hza : iterate p k x = a
    · rw [hza]
      exact Or.inr (Or.inr ⟨1, transpose_b p hab⟩)
    · by_cases hzb : iterate p k x = b
      · rw [hzb]
        exact Or.inr (Or.inl ⟨1, transpose_a p a b⟩)
      · have hs : Reaches (transpose p a b) (iterate p k x) (p (iterate p k x)) :=
          ⟨1, transpose_other p hza hzb⟩
        rcases ih with h | h | h
        · exact Or.inl (h.trans hs)
        · exact Or.inr (Or.inl (h.trans hs))
        · exact Or.inr (Or.inr (h.trans hs))

/-! ## Excising a dart fixed by `edge` -/

/-- Excising a dart fixed by `edge` keeps a face on every vertex of every component. -/
theorem outerFaces_shrinkLast {n : Nat} (G : Hypermap (n + 1)) (he : G.edge (last n) = last n)
    (h : OuterFaces G) : OuterFaces (shrinkLast G he) := by
  have hk : G.node (G.face (last n)) = last n := by
    have := G.edgeK (last n)
    rwa [he] at this
  -- an incidence at the removed dart is also witnessed by the next dart of its face
  have hsurv : ∀ (x : Fin (n + 1)) (d' : Fin n) (y : Fin (n + 1)), Reaches G.face x y →
      Reaches G.node (embed d') y →
      ∃ y' : Fin n, Reaches G.face x (embed y') ∧ Reaches G.node (embed d') (embed y') := by
    intro x d' y hxy hdy
    rcases old_dart_cases y with ⟨y', rfl⟩ | rfl
    · exact ⟨y', hxy, hdy⟩
    · rcases old_dart_cases (G.face (last n)) with ⟨y', hy'⟩ | hl
      · refine ⟨y', ?_, ?_⟩
        · rw [hy']; exact hxy.trans (Reaches.step _ _)
        · rw [hy']
          exact hdy.trans ((show Reaches G.node (G.face (last n)) (last n) from ⟨1, hk⟩).symm
            (hm_node_inj G))
      · exfalso
        have hn : G.node (last n) = last n := by rw [hl] at hk; exact hk
        obtain ⟨k, hk'⟩ := hdy.symm (hm_node_inj G)
        rw [iterate_fixed hn k] at hk'
        exact embed_ne_last d' hk'.symm
  intro d
  obtain ⟨x, hx⟩ := h (embed d)
  have hx' : ∃ x' : Fin n, ∀ y' : Fin n, Reaches G.face x (embed y') →
      Reaches G.face (embed x') (embed y') := by
    rcases old_dart_cases x with ⟨x0, rfl⟩ | rfl
    · exact ⟨x0, fun _ h => h⟩
    · obtain ⟨y, hy1, hy2⟩ := hx (embed d) (LinkedPath.refl _ _)
      obtain ⟨y0, hy0, -⟩ := hsurv _ d y hy1 hy2
      rcases old_dart_cases (G.face (last n)) with ⟨x0, hx0⟩ | hl
      · refine ⟨x0, fun y' h' => ?_⟩
        rw [hx0]
        exact reaches_of_ne h' (embed_ne_last y')
      · exfalso
        obtain ⟨k, hk'⟩ := hy0
        rw [iterate_fixed hl k] at hk'
        exact embed_ne_last y0 hk'.symm
  obtain ⟨x', hx'⟩ := hx'
  refine ⟨x', fun d' hd' => ?_⟩
  obtain ⟨y, hy1, hy2⟩ := hx (embed d') ((shrinkLast_linked G he d d').mp hd')
  obtain ⟨y', hy1', hy2'⟩ := hsurv x d' y hy1 hy2
  exact ⟨y', (shrinkLast_face_orbit G he x' y').mpr (hx' y' hy1'),
    (shrinkLast_node_orbit G he d' y').mpr hy2'⟩

/-! ## Cutting an edge -/

section Cut

variable {n : Nat} (G : Hypermap n) (a b : Fin n) (hab : a ≠ b) (ha : G.edge a = b)
  (hb : G.edge b = a)

/-- Away from the two cut darts, the steps of `G` are steps of the cut map. -/
theorem cut_step_off {x y : Fin n} (hxa : x ≠ a) (hxb : x ≠ b) (hs : Linked.Step G x y) :
    Linked.Step (cut G a b hab ha hb) x y := by
  rcases hs with hs | hs | hs
  · exact Or.inl ((transpose_other G.edge hxa hxb).trans hs)
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr ((transpose_other G.face hxa hxb).trans hs))

/-- Every step of the cut map is a path of `G`. -/
theorem cut_step_lift {x y : Fin n} (hs : Linked.Step (cut G a b hab ha hb) x y) :
    LinkedPath G x y := by
  rcases hs with hs | hs | hs
  · change transpose G.edge a b x = y at hs
    by_cases hxa : x = a
    · subst x; rw [transpose_a, hb] at hs; subst hs; exact LinkedPath.refl _ _
    · by_cases hxb : x = b
      · subst x; rw [transpose_b _ hab, ha] at hs; subst hs; exact LinkedPath.refl _ _
      · rw [transpose_other _ hxa hxb] at hs; exact LinkedPath.step G (Or.inl hs)
  · exact LinkedPath.step G (Or.inr (Or.inl hs))
  · change transpose G.face a b x = y at hs
    by_cases hxa : x = a
    · subst x; rw [transpose_a] at hs; subst hs
      exact (LinkedPath.step G (Or.inl ha)).trans (LinkedPath.step G (Or.inr (Or.inr rfl)))
    · by_cases hxb : x = b
      · subst x; rw [transpose_b _ hab] at hs; subst hs
        exact (LinkedPath.step G (Or.inl hb)).trans (LinkedPath.step G (Or.inr (Or.inr rfl)))
      · rw [transpose_other _ hxa hxb] at hs; exact LinkedPath.step G (Or.inr (Or.inr hs))

theorem cut_path_lift {x y : Fin n} (h : LinkedPath (cut G a b hab ha hb) x y) :
    LinkedPath G x y :=
  linkedPath_of_steps (fun _ _ hs => cut_step_lift G a b hab ha hb hs) h

/-- A path of `G` from `d` stays in the cut map until it first meets a cut dart. -/
theorem cut_linked_three {d z : Fin n} (h : LinkedPath G d z) :
    LinkedPath (cut G a b hab ha hb) d z ∨ LinkedPath (cut G a b hab ha hb) d a ∨
      LinkedPath (cut G a b hab ha hb) d b := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing z with
  | zero => rw [Linked.linked_zero] at hk; subst z; exact Or.inl (LinkedPath.refl _ _)
  | succ k ih =>
    rcases (Linked.linked_succ G k d z).mp hk with h | ⟨w, hw, hst⟩
    · exact ih h
    · rcases ih hw with h | h | h
      · by_cases hwa : w = a
        · subst w; exact Or.inr (Or.inl h)
        · by_cases hwb : w = b
          · subst w; exact Or.inr (Or.inr h)
          · exact Or.inl (h.trans (LinkedPath.step _ (cut_step_off G a b hab ha hb hwa hwb hst)))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

theorem cut_linked_of_linked_a {d : Fin n} (h : LinkedPath G d a) :
    LinkedPath (cut G a b hab ha hb) d a ∨ LinkedPath (cut G a b hab ha hb) d b := by
  rcases cut_linked_three G a b hab ha hb h with h | h | h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr h

/-- If the two cut darts stay linked, every step of `G` is a path of the cut map. -/
theorem cut_step_of_linked (hl : LinkedPath (cut G a b hab ha hb) a b) {x y : Fin n}
    (hs : Linked.Step G x y) : LinkedPath (cut G a b hab ha hb) x y := by
  by_cases hxa : x = a
  · subst x
    rcases hs with hs | hs | hs
    · rw [ha] at hs; subst hs; exact hl
    · exact LinkedPath.step _ (Or.inr (Or.inl hs))
    · exact hl.trans (LinkedPath.step _ (Or.inr (Or.inr ((transpose_b G.face hab).trans hs))))
  · by_cases hxb : x = b
    · subst x
      rcases hs with hs | hs | hs
      · rw [hb] at hs; subst hs; exact hl.symm
      · exact LinkedPath.step _ (Or.inr (Or.inl hs))
      · exact hl.symm.trans
          (LinkedPath.step _ (Or.inr (Or.inr ((transpose_a G.face a b).trans hs))))
    · exact LinkedPath.step _ (cut_step_off G a b hab ha hb hxa hxb hs)

/-- **A cut edge on a single face is a bridge**: by Euler's inequality for the cut map, its
two darts are no longer linked. -/
theorem cut_not_linked_of_same_face (hE : HypermapEuler) (hP : G.Planar)
    (hF : cmin G.face a = cmin G.face b) : ¬ LinkedPath (cut G a b hab ha hb) a b := by
  intro hl
  have hC := componentCount_le_of_steps
    (fun _ _ hs => cut_step_of_linked G a b hab ha hb hl hs)
  have heSame : cmin G.edge a = cmin G.edge b :=
    (cmin_eq_iff_reaches (hm_edge_inj G) a b).mpr ⟨1, ha⟩
  have hEc := transpose_split_cycles (hm_edge_inj G) a b hab heSame
  have hFc := transpose_split_cycles (hm_face_inj G) a b hab hF
  have hK := (hE n (cut G a b hab ha hb)).1
  rw [planar_iff] at hP
  unfold Hypermap.eulerRhs Hypermap.eulerLhs at hK
  unfold Hypermap.eulerRhs at hP
  change cycleCount (transpose G.edge a b) + cycleCount G.node +
    cycleCount (transpose G.face a b) ≤ 2 * (cut G a b hab ha hb).componentCount + n at hK
  omega

/-- Off the two cut darts, the faces are unchanged. -/
theorem cut_face_iterate {x : Fin n}
    (hx : ∀ j, iterate G.face j x ≠ a ∧ iterate G.face j x ≠ b) (j : Nat) :
    iterate (cut G a b hab ha hb).face j x = iterate G.face j x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    have h0 : (cut G a b hab ha hb).face x = G.face x :=
      transpose_other G.face (hx 0).1 (hx 0).2
    change iterate (cut G a b hab ha hb).face j ((cut G a b hab ha hb).face x) =
      iterate G.face j (G.face x)
    rw [h0]
    exact ih (fun i => hx (i + 1))

/-- **Cutting an edge of a planar hypermap keeps a face on every vertex of every
component** (given Euler's inequality). -/
theorem outerFaces_cut (hE : HypermapEuler) (hP : G.Planar) (h : OuterFaces G) :
    OuterFaces (cut G a b hab ha hb) := by
  intro d
  by_cases hF : cmin G.face a = cmin G.face b
  · have hnl := cut_not_linked_of_same_face G a b hab ha hb hE hP hF
    have hba : Reaches G.face b a := (cmin_eq_iff_reaches (hm_face_inj G) b a).mp hF.symm
    have hab' : Reaches G.face a b := hba.symm (hm_face_inj G)
    by_cases hda : LinkedPath G d a
    · obtain ⟨x0, hx0⟩ := h d
      have hdb : LinkedPath G d b := hda.trans (LinkedPath.step G (Or.inl ha))
      -- the face of `x0` is the face of the cut edge
      have hax0 : Reaches G.face a x0 := by
        apply Classical.byContradiction
        intro hno
        have hoff : ∀ j, iterate G.face j x0 ≠ a ∧ iterate G.face j x0 ≠ b := by
          intro j
          constructor
          · intro hj
            exact hno ((show Reaches G.face x0 a from ⟨j, hj⟩).symm (hm_face_inj G))
          · intro hj
            exact hno (((show Reaches G.face x0 b from ⟨j, hj⟩).trans hba).symm
              (hm_face_inj G))
        obtain ⟨ya, ⟨ja, hja⟩, hna⟩ := hx0 a hda
        obtain ⟨yb, ⟨jb, hjb⟩, hnb⟩ := hx0 b hdb
        apply hnl
        have h1 : LinkedPath (cut G a b hab ha hb) a ya := nodeOrbit_linked _ hna
        have h2 : LinkedPath (cut G a b hab ha hb) x0 ya :=
          faceOrbit_linked _ ⟨ja, (cut_face_iterate G a b hab ha hb hoff ja).trans hja⟩
        have h3 : LinkedPath (cut G a b hab ha hb) x0 yb :=
          faceOrbit_linked _ ⟨jb, (cut_face_iterate G a b hab ha hb hoff jb).trans hjb⟩
        have h4 : LinkedPath (cut G a b hab ha hb) b yb := nodeOrbit_linked _ hnb
        exact h1.trans (h2.symm.trans (h3.trans h4.symm))
      rcases cut_linked_of_linked_a G a b hab ha hb hda with hKa | hKb
      · refine ⟨a, fun d' hd' => ?_⟩
        obtain ⟨y, hy, hny⟩ := hx0 d' (cut_path_lift G a b hab ha hb hd')
        rcases transpose_reaches_three hab (hax0.trans hy) with h1 | h1 | h1
        · exact ⟨y, h1, hny⟩
        · exact ⟨y, h1, hny⟩
        · exfalso
          apply hnl
          exact hKa.symm.trans (hd'.trans ((nodeOrbit_linked (cut G a b hab ha hb) hny).trans
            (faceOrbit_linked (cut G a b hab ha hb) h1).symm))
      · refine ⟨b, fun d' hd' => ?_⟩
        obtain ⟨y, hy, hny⟩ := hx0 d' (cut_path_lift G a b hab ha hb hd')
        rcases transpose_reaches_three hab (hba.trans (hax0.trans hy)) with h1 | h1 | h1
        · exact ⟨y, h1, hny⟩
        · exfalso
          apply hnl
          exact ((faceOrbit_linked (cut G a b hab ha hb) h1).trans
            ((nodeOrbit_linked (cut G a b hab ha hb) hny).symm.trans hd'.symm)).trans hKb
        · exact ⟨y, h1, hny⟩
    · obtain ⟨x0, hx0⟩ := h d
      refine ⟨x0, fun d' hd' => ?_⟩
      obtain ⟨y, ⟨j, hj⟩, hny⟩ := hx0 d' (cut_path_lift G a b hab ha hb hd')
      obtain ⟨y0, hy0, hny0⟩ := hx0 d (LinkedPath.refl _ _)
      have hdx0 : LinkedPath G d x0 :=
        (nodeOrbit_linked G hny0).trans (faceOrbit_linked G hy0).symm
      have hoff : ∀ i, iterate G.face i x0 ≠ a ∧ iterate G.face i x0 ≠ b := by
        intro i
        have hl : LinkedPath G d (iterate G.face i x0) :=
          hdx0.trans (faceOrbit_linked G ⟨i, rfl⟩)
        constructor
        · intro hi; rw [hi] at hl; exact hda hl
        · intro hi; rw [hi] at hl; exact hda (hl.trans (LinkedPath.step G (Or.inl hb)))
      exact ⟨y, ⟨j, (cut_face_iterate G a b hab ha hb hoff j).trans hj⟩, hny⟩
  · obtain ⟨x0, hx0⟩ := h d
    refine ⟨x0, fun d' hd' => ?_⟩
    obtain ⟨y, hy, hny⟩ := hx0 d' (cut_path_lift G a b hab ha hb hd')
    exact ⟨y, transpose_merge_orbit (hm_face_inj G) a b hF hy, hny⟩

end Cut

/-- Cutting the last edge and excising its two darts keeps `OuterFaces`. -/
theorem outerFaces_cutThenShrink (hE : HypermapEuler) {n : Nat} (G : Hypermap (n + 2))
    (ha : G.edge (penultimate n) = last (n + 1)) (hb : G.edge (last (n + 1)) = penultimate n)
    (hP : G.Planar) (h : OuterFaces G) : OuterFaces (cutThenShrink G ha hb) :=
  outerFaces_shrinkLast _ _ (outerFaces_shrinkLast _ _
    (outerFaces_cut G _ _ (penultimate_ne_last n) ha hb hE hP h))

end STACS2027.OuterplanarMinor

namespace STACS2027
open Complexity Complexity.Planar STACS2027.PlanarGluing STACS2027.PlanarPreprocess
open STACS2027.PlanarPreprocess.Deletion STACS2027.OuterplanarMinor

/-- **Deleting the last edge of an outerplanar embedding** gives an outerplanar embedding
(loops and parallel edges allowed), given Euler's inequality for hypermaps. -/
theorem OuterplanarEmbedding.dropLast (hE : HypermapEuler) {V : Type} {es : List (V × V)}
    {e : V × V} (h : OuterplanarEmbedding (es ++ [e])) : OuterplanarEmbedding es := by
  unfold OuterplanarEmbedding at h ⊢
  rw [List.length_append] at h
  simp only [List.length_cons, List.length_nil] at h
  obtain ⟨G, he, hn, hp, ho⟩ := h
  change (∀ d, (G.edge d).val = ed d.val) at he
  refine ⟨cutThenShrink G (graphEdge_last_pair G he).1 (graphEdge_last_pair G he).2,
    cutThenShrink_graphEdge G he, cutThenShrink_graphNodes es e G he hn,
    shrinkLast_planar _ _ (shrinkLast_planar _ _ (cut_planar G _ _ (penultimate_ne_last _) _ _ hp)),
    ?_⟩
  exact (outerFaces_iff _).mp
    (outerFaces_cutThenShrink hE G _ _ hp ((outerFaces_iff G).mpr ho))

end STACS2027
