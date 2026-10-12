module

public import NPHardness.PlanarGluingCut
import Lean.Elab.Tactic.Omega

/-!
# Euler's inequality for hypermaps, I: the edge transposition

The step of the proof of Euler's inequality and of the parity of the Euler characteristic
(`Outerplanar/HypermapEuler.lean`). For a hypermap `G` and a dart `b` that is not a fixed point
of `edge`, `moveE G b` composes `edge` with the transposition of `b` and `edge b` (which makes
`edge b` a fixed point and leaves the other edge cycles alone), keeps `node`, and composes
`face` with the transposition of `edge b` and `edge (edge b)`, so that the composite
`node ∘ face ∘ edge` stays the identity. It generalizes the Section 5 edge cut
(`PlanarGluing.cut`, the case of a 2-cycle of `edge`), with the same proofs:

* `moveE_edge_cycles`: the edge cycle of `b` splits, `edge` gains exactly one cycle;
* `moveE_face_split` / `moveE_face_merge`: the face permutation gains one cycle when
  `edge b` and `edge (edge b)` are on the same face, and loses one otherwise;
* `moveE_components_le_add_one`: at most one more component; `moveE_components_le_of_faces_ne`:
  no more components when the two darts are on different faces;
* `moveE_nonFixed_lt`: fewer darts are moved by `edge`.
-/

@[expose] public section

namespace STACS2027.HypEuler

open Complexity Complexity.Planar STACS2027.PlanarGluing

variable {n : Nat}

theorem swap_b (a b : Fin n) : swap a b b = a := by
  unfold swap
  by_cases h : b = a
  · simp [h]
  · simp [h]

theorem transpose_b' (p : Fin n → Fin n) (a b : Fin n) : transpose p a b b = p a := by
  simp only [transpose, swap_b]

/-- The **edge transposition** at `b` (see the module docstring). -/
def moveE (G : Hypermap n) (b : Fin n) : Hypermap n where
  edge := transpose G.edge (G.edge b) b
  node := G.node
  face := transpose G.face (G.edge (G.edge b)) (G.edge b)
  edgeK x := by
    by_cases hxa : x = G.edge b
    · subst hxa
      rw [transpose_a, transpose_b']
      exact G.edgeK _
    · by_cases hxb : x = b
      · subst hxb
        rw [transpose_b', transpose_a]
        exact G.edgeK _
      · have h1 : G.edge x ≠ G.edge (G.edge b) := fun h => hxa (hm_edge_inj G _ _ h)
        have h2 : G.edge x ≠ G.edge b := fun h => hxb (hm_edge_inj G _ _ h)
        rw [transpose_other _ hxa hxb, transpose_other _ h1 h2]
        exact G.edgeK x

section

variable (G : Hypermap n) (b : Fin n)

theorem moveE_edge_a : (moveE G b).edge (G.edge b) = G.edge b := transpose_a _ _ _

theorem moveE_edge_b : (moveE G b).edge b = G.edge (G.edge b) := transpose_b' _ _ _

theorem moveE_edge_other {x : Fin n} (ha : x ≠ G.edge b) (hb : x ≠ b) :
    (moveE G b).edge x = G.edge x := transpose_other _ ha hb

theorem moveE_face_a : (moveE G b).face (G.edge b) = G.face (G.edge (G.edge b)) :=
  transpose_b' _ _ _

theorem moveE_face_ea : (moveE G b).face (G.edge (G.edge b)) = G.face (G.edge b) :=
  transpose_a _ _ _

theorem moveE_face_other {x : Fin n} (h1 : x ≠ G.edge (G.edge b)) (h2 : x ≠ G.edge b) :
    (moveE G b).face x = G.face x := transpose_other _ h1 h2

theorem moveE_node : (moveE G b).node = G.node := rfl

/-- The edge cycle of `b` splits into the fixed point `edge b` and the rest. -/
theorem moveE_edge_cycles (hb : G.edge b ≠ b) :
    cycleCount (moveE G b).edge = cycleCount G.edge + 1 :=
  transpose_split_cycles (hm_edge_inj G) (G.edge b) b hb (cmin_step (hm_edge_inj G) b)

theorem edge_edge_ne (hb : G.edge b ≠ b) : G.edge (G.edge b) ≠ G.edge b :=
  fun h => hb (hm_edge_inj G _ _ h)

/-- When `edge b` and `edge (edge b)` lie on the same face, that face splits. -/
theorem moveE_face_split (hb : G.edge b ≠ b)
    (hc : cmin G.face (G.edge (G.edge b)) = cmin G.face (G.edge b)) :
    cycleCount (moveE G b).face = cycleCount G.face + 1 :=
  transpose_split_cycles (hm_face_inj G) _ _ (edge_edge_ne G b hb) hc

/-- When `edge b` and `edge (edge b)` lie on different faces, the two faces merge. -/
theorem moveE_face_merge (hc : cmin G.face (G.edge (G.edge b)) ≠ cmin G.face (G.edge b)) :
    cycleCount (moveE G b).face + 1 = cycleCount G.face :=
  transpose_merge_cycles (hm_face_inj G) _ _ hc

/-- The component label of `moveE G b` with the component of `edge b` merged into that of
`b` is invariant under the steps of `G`. -/
theorem moveE_mergedLabel_invariant (x y : Fin n) (hs : Linked.Step G x y) :
    mergedComponentLabel (moveE G b) (G.edge b) b y =
      mergedComponentLabel (moveE G b) (G.edge b) b x := by
  let K := moveE G b
  have hKa : mergedComponentLabel K (G.edge b) b (G.edge b) = componentRep K b :=
    mergedComponentLabel_a K _ b
  have hKb : mergedComponentLabel K (G.edge b) b b = componentRep K b :=
    mergedComponentLabel_b K _ b
  -- the dart `edge (edge b)` is one `K`-edge step from `b`
  have hKea : mergedComponentLabel K (G.edge b) b (G.edge (G.edge b)) = componentRep K b :=
    (mergedComponentLabel_step K _ b (Or.inl (moveE_edge_b G b))).trans hKb
  rcases hs with hs | hs | hs
  · subst y
    by_cases hxa : x = G.edge b
    · subst x; exact hKea.trans hKa.symm
    · by_cases hxb : x = b
      · subst x; exact hKa.trans hKb.symm
      · exact mergedComponentLabel_step K _ b (Or.inl (moveE_edge_other G b hxa hxb))
  · subst y
    exact mergedComponentLabel_step K _ b (Or.inr (Or.inl rfl))
  · subst y
    by_cases h1 : x = G.edge (G.edge b)
    · subst x
      have hs' : Linked.Step K (G.edge b) (G.face (G.edge (G.edge b))) :=
        Or.inr (Or.inr (moveE_face_a G b))
      exact (mergedComponentLabel_step K _ b hs').trans (hKa.trans hKea.symm)
    · by_cases h2 : x = G.edge b
      · subst x
        have hs' : Linked.Step K (G.edge (G.edge b)) (G.face (G.edge b)) :=
          Or.inr (Or.inr (moveE_face_ea G b))
        exact (mergedComponentLabel_step K _ b hs').trans (hKea.trans hKa.symm)
      · exact mergedComponentLabel_step K _ b
          (Or.inr (Or.inr (moveE_face_other G b h1 h2)))

/-- The edge transposition creates at most one more connected component. -/
theorem moveE_components_le_add_one :
    (moveE G b).componentCount ≤ G.componentCount + 1 := by
  let K := moveE G b
  let xs := (componentRoots K).erase (componentRep K (G.edge b))
  have hroots : (componentRoots K).Nodup := List.Pairwise.filter _ (List.nodup_finRange n)
  have hlen : xs.length + 1 = K.componentCount := by
    have hm : componentRep K (G.edge b) ∈ componentRoots K :=
      List.mem_filter.mpr ⟨List.mem_finRange _, componentRep_root K _⟩
    have hl := List.length_erase_of_mem hm
    have hpos : 0 < (componentRoots K).length :=
      List.length_pos_iff.mpr (fun he => by simp [he] at hm)
    have he := componentRoots_length K
    simp only [xs, hl]
    omega
  have hfixed : ∀ x ∈ xs, mergedComponentLabel K (G.edge b) b x = x := by
    intro x hx
    obtain ⟨hne, hm⟩ := (List.Nodup.mem_erase_iff hroots).mp hx
    have hr : componentRep K x = x :=
      Fin.ext ((componentRoot_iff K x).mp (List.mem_filter.mp hm).2)
    simp only [mergedComponentLabel, hr, ite_eq_right hne]
  have hnd : (xs.map (mergedComponentLabel K (G.edge b) b)).Nodup := by
    have he : xs.map (mergedComponentLabel K (G.edge b) b) = xs := by
      conv => rhs; rw [← List.map_id xs]
      exact List.map_congr_left hfixed
    rw [he]; exact hroots.erase _
  have hge := componentCount_ge G (mergedComponentLabel K (G.edge b) b)
    (moveE_mergedLabel_invariant G b) xs hnd
  change K.componentCount ≤ G.componentCount + 1
  omega

theorem moveE_step_transfer_of_faces_ne
    (hsep : cmin G.face (G.edge (G.edge b)) ≠ cmin G.face (G.edge b))
    {x y : Fin n} (hs : Linked.Step G x y) : LinkedPath (moveE G b) x y := by
  let K := moveE G b
  have hmarkers : LinkedPath K (G.edge (G.edge b)) (G.edge b) :=
    faceOrbit_linked K (transpose_merge_markers (hm_face_inj G) _ _ hsep)
  rcases hs with hs | hs | hs
  · subst y
    by_cases hxa : x = G.edge b
    · subst x; exact hmarkers.symm
    · by_cases hxb : x = b
      · subst x
        exact (LinkedPath.step K (Or.inl (moveE_edge_b G b))).trans hmarkers
      · exact LinkedPath.step K (Or.inl (moveE_edge_other G b hxa hxb))
  · subst y; exact LinkedPath.step K (Or.inr (Or.inl rfl))
  · subst y
    exact faceOrbit_linked K (transpose_merge_step (hm_face_inj G) _ _ hsep x)

theorem moveE_path_transfer_of_faces_ne
    (hsep : cmin G.face (G.edge (G.edge b)) ≠ cmin G.face (G.edge b))
    {x y : Fin n} (h : LinkedPath G x y) : LinkedPath (moveE G b) x y := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at hk; subst y; exact LinkedPath.refl _ _
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp hk with h | ⟨z, hz, hs⟩
    · exact ih h
    · exact (ih hz).trans (moveE_step_transfer_of_faces_ne G b hsep hs)

/-- No new component when `edge b` and `edge (edge b)` lie on different faces. -/
theorem moveE_components_le_of_faces_ne
    (hsep : cmin G.face (G.edge (G.edge b)) ≠ cmin G.face (G.edge b)) :
    (moveE G b).componentCount ≤ G.componentCount := by
  apply componentCount_le (moveE G b) (ComponentRoot G)
  intro x hx
  have hx' : compMin G x ≠ x.val := by
    intro he
    have hroot := (componentRoot_iff G x).mpr he
    rw [hroot] at hx
    contradiction
  have hle := (compMin_spec G x).2 x (Linked.linked_refl G n x)
  obtain ⟨k, hk⟩ := moveE_path_transfer_of_faces_ne G b hsep ⟨n, componentRep_linked G x⟩
  exact ⟨componentRep G x, by change compMin G x < x.val; omega, k, hk⟩

/-- The number of darts moved by a map. -/
def nonFixed (p : Fin n → Fin n) : Nat := (List.finRange n).countP fun x => p x != x

/-- The edge transposition fixes `edge b` and moves no new dart. -/
theorem moveE_nonFixed_lt (hb : G.edge b ≠ b) :
    nonFixed (moveE G b).edge < nonFixed G.edge := by
  unfold nonFixed
  apply Linked.countP_lt_of_mono (y := G.edge b)
  · intro x _ hx
    simp only [bne_iff_ne, ne_eq] at hx ⊢
    by_cases hxa : x = G.edge b
    · subst x; exact absurd (moveE_edge_a G b) hx
    · by_cases hxb : x = b
      · subst x; exact hb
      · rwa [moveE_edge_other G b hxa hxb] at hx
  · exact List.mem_finRange _
  · simpa using edge_edge_ne G b hb
  · simpa using moveE_edge_a G b

end

end STACS2027.HypEuler
