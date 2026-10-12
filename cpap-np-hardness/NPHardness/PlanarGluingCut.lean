module

public import NPHardness.PlanarGluingTransposition
public import NPHardness.PlanarGluingUnion
import Lean.Elab.Tactic.Omega

/-!
Cut one edge before deleting its two darts. The selected edge pair becomes
two fixed edge darts; the node permutation is unchanged and the face
permutation undergoes its actual successor transposition. We bound the
resulting components, including the improved bound for a nonseparating cut.
-/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

def cut {n : Nat} (G : Hypermap n) (a b : Fin n) (hab : a ≠ b)
    (ha : G.edge a = b) (hb : G.edge b = a) : Hypermap n where
  edge := transpose G.edge a b
  node := G.node
  face := transpose G.face a b
  edgeK x := by
    by_cases hxa : x = a
    · subst x
      rw [transpose_a, hb, transpose_a]
      have h := G.edgeK a
      simpa only [ha] using h
    · by_cases hxb : x = b
      · subst x
        rw [transpose_b _ hab, ha, transpose_b _ hab]
        have h := G.edgeK b
        simpa only [hb] using h
      · have heA : G.edge x ≠ a := by
          intro h; apply hxb; exact hm_edge_inj G _ _ (h.trans hb.symm)
        have heB : G.edge x ≠ b := by
          intro h; apply hxa; exact hm_edge_inj G _ _ (h.trans ha.symm)
        rw [transpose_other _ hxa hxb, transpose_other _ heA heB, G.edgeK]

theorem linked_label_invariant {n : Nat} {β : Type} (G : Hypermap n) (φ : Fin n → β)
    (hφ : ∀ x y, Linked.Step G x y → φ y = φ x) {k : Nat} {x y : Fin n}
    (h : G.linked k x y = true) : φ y = φ x := by
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at h; subst y; rfl
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp h with h | ⟨z, hz, hs⟩
    · exact ih h
    · exact (hφ z y hs).trans (ih hz)

/-- Distinct invariant labels provide a lower bound on connected components. -/
theorem componentCount_ge {n : Nat} {β : Type} (G : Hypermap n) (φ : Fin n → β)
    (hφ : ∀ x y, Linked.Step G x y → φ y = φ x)
    (xs : List (Fin n)) (hnd : (xs.map φ).Nodup) : xs.length ≤ G.componentCount := by
  let m : Fin n → Fin n := fun x => Classical.choose (exists_least_label φ x)
  have hmφ : ∀ x, φ (m x) = φ x := fun x => (Classical.choose_spec (exists_least_label φ x)).1
  have hmmin : ∀ x z, φ z = φ x → (m x).val ≤ z.val :=
    fun x => (Classical.choose_spec (exists_least_label φ x)).2
  have hroot : ∀ x, ComponentRoot G (m x) = true := by
    intro x
    simp only [ComponentRoot, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq]
    intro y
    by_cases hxy : G.linked n (m x) y = true
    · right
      exact hmmin x y ((linked_label_invariant G φ hφ hxy).trans (hmφ x))
    · left; exact Bool.eq_false_iff.mpr hxy
  have hlen := length_le_countP (ComponentRoot G) (xs.map m) (by
    have he : (xs.map m).map φ = xs.map φ := by
      rw [List.map_map]
      exact List.map_congr_left (fun x _ => hmφ x)
    rw [← he] at hnd
    exact nodup_of_map φ hnd) (by
      intro y hy
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
      exact hroot x)
  change xs.length ≤ (List.finRange n).countP (ComponentRoot G)
  simpa only [List.length_map] using hlen

theorem componentRep_step {n : Nat} (G : Hypermap n) {x y : Fin n}
    (h : Linked.Step G x y) : componentRep G y = componentRep G x :=
  Fin.ext (compMin_step G h)

noncomputable def mergedComponentLabel {n : Nat} (G : Hypermap n) (a b x : Fin n) : Fin n :=
  if componentRep G x = componentRep G a then componentRep G b else componentRep G x

theorem mergedComponentLabel_a {n : Nat} (G : Hypermap n) (a b : Fin n) :
    mergedComponentLabel G a b a = componentRep G b := by simp [mergedComponentLabel]

theorem mergedComponentLabel_b {n : Nat} (G : Hypermap n) (a b : Fin n) :
    mergedComponentLabel G a b b = componentRep G b := by simp [mergedComponentLabel]

theorem mergedComponentLabel_step {n : Nat} (G : Hypermap n) (a b : Fin n) {x y : Fin n}
    (h : Linked.Step G x y) : mergedComponentLabel G a b y = mergedComponentLabel G a b x := by
  unfold mergedComponentLabel
  rw [componentRep_step G h]

theorem cut_mergedLabel_invariant {n : Nat} (G : Hypermap n) (a b : Fin n) (hab : a ≠ b)
    (ha : G.edge a = b) (hb : G.edge b = a) (x y : Fin n) (hs : Linked.Step G x y) :
    mergedComponentLabel (cut G a b hab ha hb) a b y =
      mergedComponentLabel (cut G a b hab ha hb) a b x := by
  let K := cut G a b hab ha hb
  have hKa : mergedComponentLabel K a b a = componentRep K b := mergedComponentLabel_a K a b
  have hKb : mergedComponentLabel K a b b = componentRep K b := mergedComponentLabel_b K a b
  rcases hs with hs | hs | hs
  · subst y
    by_cases hxa : x = a
    · subst x; rw [ha]; exact hKb.trans hKa.symm
    · by_cases hxb : x = b
      · subst x; rw [hb]; exact hKa.trans hKb.symm
      · exact mergedComponentLabel_step K a b
          (Or.inl (transpose_other G.edge hxa hxb))
  · subst y
    exact mergedComponentLabel_step K a b (Or.inr (Or.inl rfl))
  · subst y
    by_cases hxa : x = a
    · subst x
      have hs' : Linked.Step K b (G.face a) := Or.inr (Or.inr (transpose_b G.face hab))
      exact (mergedComponentLabel_step K a b hs').trans (hKb.trans hKa.symm)
    · by_cases hxb : x = b
      · subst x
        have hs' : Linked.Step K a (G.face b) := Or.inr (Or.inr (transpose_a G.face a b))
        exact (mergedComponentLabel_step K a b hs').trans (hKa.trans hKb.symm)
      · exact mergedComponentLabel_step K a b
          (Or.inr (Or.inr (transpose_other G.face hxa hxb)))

/-- Cutting an edge creates at most one extra connected component. -/
theorem cut_components_le_add_one {n : Nat} (G : Hypermap n) (a b : Fin n) (hab : a ≠ b)
    (ha : G.edge a = b) (hb : G.edge b = a) :
    (cut G a b hab ha hb).componentCount ≤ G.componentCount + 1 := by
  let K := cut G a b hab ha hb
  let xs := (componentRoots K).erase (componentRep K a)
  have hroots : (componentRoots K).Nodup := List.Pairwise.filter _ (List.nodup_finRange n)
  have hlen : xs.length + 1 = K.componentCount := by
    have hm : componentRep K a ∈ componentRoots K :=
      List.mem_filter.mpr ⟨List.mem_finRange _, componentRep_root K a⟩
    have hl := List.length_erase_of_mem hm
    have hpos : 0 < (componentRoots K).length := List.length_pos_iff.mpr (fun he => by simp [he] at hm)
    have he := componentRoots_length K
    simp only [xs, hl]
    omega
  have hfixed : ∀ x ∈ xs, mergedComponentLabel K a b x = x := by
    intro x hx
    obtain ⟨hne, hm⟩ := (List.Nodup.mem_erase_iff hroots).mp hx
    have hr : componentRep K x = x :=
      Fin.ext ((componentRoot_iff K x).mp (List.mem_filter.mp hm).2)
    simp only [mergedComponentLabel, hr, ite_eq_right hne]
  have hnd : (xs.map (mergedComponentLabel K a b)).Nodup := by
    have he : xs.map (mergedComponentLabel K a b) = xs := by
      conv => rhs; rw [← List.map_id xs]
      exact List.map_congr_left hfixed
    rw [he]; exact hroots.erase _
  have hge := componentCount_ge G (mergedComponentLabel K a b)
    (cut_mergedLabel_invariant G a b hab ha hb) xs hnd
  change K.componentCount ≤ G.componentCount + 1
  omega

theorem cut_step_transfer_of_faces_ne {n : Nat} (G : Hypermap n) (a b : Fin n) (hab : a ≠ b)
    (ha : G.edge a = b) (hb : G.edge b = a) (hfaces : cmin G.face a ≠ cmin G.face b)
    {x y : Fin n} (hs : Linked.Step G x y) : LinkedPath (cut G a b hab ha hb) x y := by
  let K := cut G a b hab ha hb
  have hmarkers : LinkedPath K a b :=
    faceOrbit_linked K (transpose_merge_markers (hm_face_inj G) a b hfaces)
  rcases hs with hs | hs | hs
  · subst y
    by_cases hxa : x = a
    · subst x; rw [ha]; exact hmarkers
    · by_cases hxb : x = b
      · subst x; rw [hb]; exact hmarkers.symm
      · exact LinkedPath.step K (Or.inl (transpose_other G.edge hxa hxb))
  · subst y; exact LinkedPath.step K (Or.inr (Or.inl rfl))
  · subst y
    exact faceOrbit_linked K (transpose_merge_step (hm_face_inj G) a b hfaces x)

theorem cut_path_transfer_of_faces_ne {n : Nat} (G : Hypermap n) (a b : Fin n) (hab : a ≠ b)
    (ha : G.edge a = b) (hb : G.edge b = a) (hfaces : cmin G.face a ≠ cmin G.face b)
    {x y : Fin n} (h : LinkedPath G x y) : LinkedPath (cut G a b hab ha hb) x y := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at hk; subst y; exact LinkedPath.refl _ _
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp hk with h | ⟨z, hz, hs⟩
    · exact ih h
    · exact (ih hz).trans (cut_step_transfer_of_faces_ne G a b hab ha hb hfaces hs)

/-- The cut does not split a component when its two darts lie on different old faces. -/
theorem cut_components_le_of_faces_ne {n : Nat} (G : Hypermap n) (a b : Fin n) (hab : a ≠ b)
    (ha : G.edge a = b) (hb : G.edge b = a) (hfaces : cmin G.face a ≠ cmin G.face b) :
    (cut G a b hab ha hb).componentCount ≤ G.componentCount := by
  have h := componentCount_le (cut G a b hab ha hb) (ComponentRoot G) (by
    intro x hx
    have hx' : compMin G x ≠ x.val := by
      intro he
      have hroot := (componentRoot_iff G x).mpr he
      rw [hroot] at hx
      contradiction
    have hle := (compMin_spec G x).2 x (Linked.linked_refl G n x)
    obtain ⟨k, hk⟩ := cut_path_transfer_of_faces_ne G a b hab ha hb hfaces
      ⟨n, componentRep_linked G x⟩
    exact ⟨componentRep G x, by change compMin G x < x.val; omega, k, hk⟩)
  exact h

/-- Cutting a paired edge preserves the registered genus-zero condition.
The fixed darts are still present and can subsequently be excised. -/
theorem cut_planar {n : Nat} (G : Hypermap n) (a b : Fin n) (hab : a ≠ b)
    (ha : G.edge a = b) (hb : G.edge b = a) (hP : G.Planar) :
    (cut G a b hab ha hb).Planar := by
  have heSame : cmin G.edge a = cmin G.edge b :=
    (cmin_eq_iff_reaches (hm_edge_inj G) a b).mpr ⟨1, ha⟩
  have hE := transpose_split_cycles (hm_edge_inj G) a b hab heSame
  rw [planar_iff] at hP ⊢
  unfold Hypermap.eulerRhs at hP ⊢
  change 2 * (cut G a b hab ha hb).componentCount + n ≤
    cycleCount (transpose G.edge a b) + cycleCount G.node + cycleCount (transpose G.face a b) + 1
  by_cases hF : cmin G.face a = cmin G.face b
  · have hFc := transpose_split_cycles (hm_face_inj G) a b hab hF
    have hC := cut_components_le_add_one G a b hab ha hb
    omega
  · have hFc := transpose_merge_cycles (hm_face_inj G) a b hF
    have hC := cut_components_le_of_faces_ne G a b hab ha hb hF
    omega

end STACS2027.PlanarGluing
