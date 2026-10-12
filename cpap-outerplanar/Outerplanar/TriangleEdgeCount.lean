module

public import Outerplanar.TriangleFamily
import Mathlib.Tactic

/-! Exact finite edge loss under contraction of a proper canonical edge. -/

@[expose] public section
namespace STACS2027.TriangleMatching

theorem canonicalEdge_eq {e : Edge} (he : e.1 < e.2) : edge e.1 e.2 = e := by
  simp only [edge, min_eq_left he.le, max_eq_right he.le, Prod.mk.eta]

theorem identifyVertex_eq_iff {u v a b : Nat} (_huv : u ≠ v) :
    identifyVertex u v a = identifyVertex u v b ↔
      a = b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  unfold identifyVertex
  split_ifs <;> omega

theorem identifyEdge_collision {u v : Nat} (huv : u ≠ v) {x y : Edge}
    (hx : x.1 < x.2) (hy : y.1 < y.2)
    (hxuv : x ≠ edge u v) (hyuv : y ≠ edge u v)
    (himage : edge (identifyVertex u v x.1) (identifyVertex u v x.2) =
      edge (identifyVertex u v y.1) (identifyVertex u v y.2)) :
    x = y ∨ ∃ w, (x = edge u w ∧ y = edge v w) ∨
      (x = edge v w ∧ y = edge u w) := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  change a < b at hx
  change c < d at hy
  have hxn : edge a b = (a, b) := canonicalEdge_eq (e := (a, b)) hx
  have hyn : edge c d = (c, d) := canonicalEdge_eq (e := (c, d)) hy
  change edge (identifyVertex u v a) (identifyVertex u v b) =
    edge (identifyVertex u v c) (identifyVertex u v d) at himage
  rcases (edge_eq_iff ..).mp himage with ⟨ha, hb⟩ | ⟨ha, hb⟩
  all_goals
    rcases (identifyVertex_eq_iff huv).mp ha with ha | ⟨ha, ha'⟩ | ⟨ha, ha'⟩
    <;> rcases (identifyVertex_eq_iff huv).mp hb with hb | ⟨hb, hb'⟩ | ⟨hb, hb'⟩
  · exact Or.inl (Prod.ext ha hb)
  · exact Or.inr ⟨a, Or.inl ⟨by rw [← hxn, hb, edge_comm], by rw [← hyn, ← ha, hb', edge_comm]⟩⟩
  · exact Or.inr ⟨a, Or.inr ⟨by rw [← hxn, hb, edge_comm], by rw [← hyn, ← ha, hb', edge_comm]⟩⟩
  · exact Or.inr ⟨b, Or.inl ⟨by rw [← hxn, ha], by rw [← hyn, ← hb, ha']⟩⟩
  · exact False.elim (by omega)
  · exact False.elim (hxuv (by rw [← hxn, ha, hb]))
  · exact Or.inr ⟨b, Or.inr ⟨by rw [← hxn, ha], by rw [← hyn, ← hb, ha']⟩⟩
  · exact False.elim (hxuv (by rw [← hxn, ha, hb, edge_comm]))
  · exact False.elim (by omega)
  · exact False.elim (by omega)
  · exact Or.inr ⟨a, Or.inl ⟨by rw [← hxn, hb, edge_comm], by rw [← hyn, ← ha, hb']⟩⟩
  · exact Or.inr ⟨a, Or.inr ⟨by rw [← hxn, hb, edge_comm], by rw [← hyn, ← ha, hb']⟩⟩
  · exact Or.inr ⟨b, Or.inl ⟨by rw [← hxn, ha], by rw [← hyn, ← hb, ha', edge_comm]⟩⟩
  · exact False.elim (by omega)
  · exact False.elim (hxuv (by rw [← hxn, ha, hb]))
  · exact Or.inr ⟨b, Or.inr ⟨by rw [← hxn, ha], by rw [← hyn, ← hb, ha', edge_comm]⟩⟩
  · exact False.elim (hxuv (by rw [← hxn, ha, hb, edge_comm]))
  · exact False.elim (by omega)

theorem mem_commonVertices_iff {E : Finset Edge} {u v w : Nat} :
    w ∈ commonVertices E u v ↔ w ≠ u ∧ w ≠ v ∧ edge u w ∈ E ∧ edge v w ∈ E := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨edge w v, by simpa only [edge_comm w v] using h.2.2.2, ?_⟩
    rcases edge_left_endpoint w v with hleft | hright
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hleft
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr hright

theorem identifyEdge_map (u v a b : Nat) :
    edge (identifyVertex u v (edge a b).1) (identifyVertex u v (edge a b).2) =
      edge (identifyVertex u v a) (identifyVertex u v b) := by
  by_cases h : a ≤ b
  · simp only [edge, min_eq_left h, max_eq_right h]
  · have h' : b ≤ a := by omega
    simpa only [edge, min_eq_right h', max_eq_left h'] using
      edge_comm (identifyVertex u v b) (identifyVertex u v a)

theorem identifyEdges_card {E : Finset Edge} {u v : Nat}
    (hcanonical : ∀ e ∈ E, e.1 < e.2) (huv : u ≠ v) (hedge : edge u v ∈ E) :
    (identifyEdges u v E).card + (commonVertices E u v).card + 1 = E.card := by
  classical
  let S := E.erase (edge u v)
  let D := (commonVertices E u v).image (edge v)
  let φ : Edge → Edge := fun e =>
    edge (identifyVertex u v e.1) (identifyVertex u v e.2)
  have hD : D ⊆ S := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hwu, hwv, huw, hvw⟩ := mem_commonVertices_iff.mp hw
    apply Finset.mem_erase.mpr
    refine ⟨?_, hvw⟩
    intro h
    rcases (edge_eq_iff ..).mp h with h | h <;> omega
  have hDcard : D.card = (commonVertices E u v).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb h
    exact (edge_left_inj v a b).mp h
  have hinj : Set.InjOn φ (↑(S \ D) : Set Edge) := by
    intro x hx y hy hxy
    obtain ⟨hxS, hxD⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyS, hyD⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hxuv, hxE⟩ := Finset.mem_erase.mp hxS
    obtain ⟨hyuv, hyE⟩ := Finset.mem_erase.mp hyS
    rcases identifyEdge_collision huv (hcanonical x hxE) (hcanonical y hyE)
      hxuv hyuv hxy with h | ⟨w, h | h⟩
    · exact h
    · obtain ⟨rfl, rfl⟩ := h
      have hw : w ∈ commonVertices E u v := by
        apply mem_commonVertices_iff.mpr
        refine ⟨?_, ?_, hxE, hyE⟩
        · intro h; subst w; simpa [edge] using hcanonical (edge u u) hxE
        · intro h; subst w; simpa [edge] using hcanonical (edge v v) hyE
      exact False.elim (hyD (Finset.mem_image.mpr ⟨w, hw, rfl⟩))
    · obtain ⟨rfl, rfl⟩ := h
      have hw : w ∈ commonVertices E u v := by
        apply mem_commonVertices_iff.mpr
        refine ⟨?_, ?_, hyE, hxE⟩
        · intro h; subst w; simpa [edge] using hcanonical (edge u u) hyE
        · intro h; subst w; simpa [edge] using hcanonical (edge v v) hxE
      exact False.elim (hxD (Finset.mem_image.mpr ⟨w, hw, rfl⟩))
  have himage : (S \ D).image φ = S.image φ := by
    apply Finset.Subset.antisymm
    · exact Finset.image_subset_image Finset.sdiff_subset
    · intro e he
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
      by_cases hxD : x ∈ D
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxD
        obtain ⟨hwu, hwv, huw, hvw⟩ := mem_commonVertices_iff.mp hw
        have huS : edge u w ∈ S := by
          apply Finset.mem_erase.mpr
          refine ⟨?_, huw⟩
          intro h
          have h' := (edge_left_inj u w v).mp h
          exact hwv h'
        have huD : edge u w ∉ D := by
          intro h
          obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp h
          obtain ⟨hzu, hzv, huz, hvz⟩ := mem_commonVertices_iff.mp hz
          rcases (edge_eq_iff ..).mp heq with h | h <;> omega
        apply Finset.mem_image.mpr
        refine ⟨edge u w, Finset.mem_sdiff.mpr ⟨huS, huD⟩, ?_⟩
        dsimp [φ]
        simp only [identifyEdge_map]
        simp [identifyVertex, huv, hwv]
      · exact Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxD⟩, rfl⟩
  have hcard : (S.image φ).card = (S \ D).card := by
    rw [← himage]
    exact Finset.card_image_of_injOn hinj
  have hpartition := Finset.card_sdiff_add_card_eq_card hD
  have herase := Finset.card_erase_add_one hedge
  change (S.image φ).card + (commonVertices E u v).card + 1 = E.card
  rw [hcard, ← hDcard, hpartition]
  exact herase

end STACS2027.TriangleMatching
