module

public import ApproximationHardness.Embed.Forest
import Lean.Elab.Tactic.Omega

/-!
# Forests on a set of vertices

`TreeOn F P`: on the vertices satisfying `P`, the parent of a non-root lies in `P` one level up, and
roots have depth `0`. The ancestor relation is then a forest on `P` (`desc_depth'`, `desc_unique'`,
`desc_antisymm'`), as for a valid forest.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar

namespace ForestData

variable {F : ForestData}

/-- The forest structure on the vertices satisfying `P`. -/
def TreeOn (F : ForestData) (P : Nat → Prop) : Prop :=
  ∀ r, P r → (F.IsRoot r → F.depth r = 0) ∧ (¬ F.IsRoot r → P (F.up r) ∧ F.depth r = F.depth (F.up r) + 1)

section treeOn

variable {P : Nat → Prop} (hT : F.TreeOn P)
include hT

theorem treeOn_up {r : Nat} (hr : P r) : P (F.up r) := by
  by_cases h : F.IsRoot r
  · rw [up_root' h]; exact hr
  · exact ((hT r hr).2 h).1
where up_root' {r : Nat} (h : F.IsRoot r) : F.up r = r := by simp [up, h]

theorem treeOn_iter {r : Nat} (hr : P r) : ∀ k, P (iterate F.up k r) := by
  intro k
  induction k generalizing r with
  | zero => exact hr
  | succ k ih => exact ih (treeOn_up hT hr)

theorem depth_iterate' {r : Nat} (hr : P r) :
    ∀ k, k ≤ F.depth r → F.depth (iterate F.up k r) + k = F.depth r := by
  intro k
  induction k generalizing r with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    by_cases hroot : F.IsRoot r
    · rw [(hT r hr).1 hroot] at hk; omega
    · have h1 := ((hT r hr).2 hroot).2
      have := ih (treeOn_up hT hr) (by omega)
      show F.depth (iterate F.up k (F.up r)) + (k + 1) = F.depth r
      omega

theorem iterate_up_depth' {r : Nat} (hr : P r) : ∀ k, F.depth r ≤ k →
    iterate F.up k r = iterate F.up (F.depth r) r := by
  intro k hk
  have hroot : F.IsRoot (iterate F.up (F.depth r) r) := by
    have h := depth_iterate' hT hr (F.depth r) (Nat.le_refl _)
    apply Classical.byContradiction
    intro hn
    have := ((hT _ (treeOn_iter hT hr _)).2 hn).2
    omega
  obtain ⟨j, rfl⟩ : ∃ j, k = F.depth r + j := ⟨k - F.depth r, by omega⟩
  rw [iterate_add]
  induction j with
  | zero => rfl
  | succ j ih => rw [iterate_succ', ih (by omega), treeOn_up.up_root' hroot]

theorem desc_depth' {v u : Nat} (hu : P u) (h : F.Desc v u) : F.depth v ≤ F.depth u := by
  obtain ⟨k, rfl⟩ := h
  by_cases hk : k ≤ F.depth u
  · have := depth_iterate' hT hu k hk; omega
  · rw [iterate_up_depth' hT hu k (by omega)]
    have := depth_iterate' hT hu (F.depth u) (Nat.le_refl _); omega

theorem desc_eq_iterate' {v u : Nat} (hu : P u) (h : F.Desc v u) :
    v = iterate F.up (F.depth u - F.depth v) u := by
  obtain ⟨k, rfl⟩ := h
  by_cases hk : k ≤ F.depth u
  · have := depth_iterate' hT hu k hk
    rw [show F.depth u - F.depth (iterate F.up k u) = k by omega]
  · rw [iterate_up_depth' hT hu k (by omega)]
    have := depth_iterate' hT hu (F.depth u) (Nat.le_refl _)
    rw [show F.depth u - F.depth (iterate F.up (F.depth u) u) = F.depth u by omega]

theorem desc_unique' {v v' u : Nat} (hu : P u) (h : F.Desc v u) (h' : F.Desc v' u)
    (hd : F.depth v = F.depth v') : v = v' := by
  rw [desc_eq_iterate' hT hu h, desc_eq_iterate' hT hu h', hd]

theorem desc_P {v u : Nat} (hu : P u) (h : F.Desc v u) : P v := by
  obtain ⟨k, rfl⟩ := h; exact treeOn_iter hT hu k

theorem desc_antisymm' {a b : Nat} (hb : P b) (h1 : F.Desc a b) (h2 : F.Desc b a) : a = b := by
  have ha := desc_P hT hb h1
  have e1 := desc_depth' hT hb h1
  have e2 := desc_depth' hT ha h2
  exact desc_unique' hT hb h1 (desc_refl b) (by omega)

/-- A vertex has no ancestor strictly below it. -/
theorem desc_up_not {c : Nat} (hc : P c) (hroot : ¬ F.IsRoot c) : ¬ F.Desc c (F.up c) := by
  intro h
  have := desc_depth' hT (treeOn_up hT hc) h
  have := ((hT c hc).2 hroot).2
  omega

end treeOn

/-- The ancestors of a non-root are itself and the ancestors of its parent. -/
theorem desc_nonroot_iff {v c : Nat} (hroot : ¬ F.IsRoot c) : F.Desc v c ↔ v = c ∨ F.Desc v (F.up c) := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  · rintro (rfl | ⟨k, rfl⟩)
    · exact desc_refl _
    · exact ⟨k + 1, rfl⟩

theorem desc_root_iff {v c : Nat} (hroot : F.IsRoot c) : F.Desc v c ↔ v = c := by
  constructor
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => rfl
    | succ k ih => rw [iterate_succ', ih]; simp [up, hroot]
  · rintro rfl; exact desc_refl _


/-- Changing the parent pointers outside a set closed under parents keeps the ancestors there. -/
theorem iterate_up_congr {F' : ForestData} (hE : F'.E = F.E) (hrep : F'.rep = F.rep) {P : Nat → Prop}
    (hpar : ∀ u, P u → F'.par u = F.par u) (hcl : ∀ u, P u → P (F.up u)) :
    ∀ k u, P u → iterate F'.up k u = iterate F.up k u := by
  have hup : ∀ u, P u → F'.up u = F.up u := by
    intro u hu
    have hr : F'.IsRoot u ↔ F.IsRoot u := by unfold IsRoot; rw [hpar u hu, hE]
    unfold up
    by_cases h : F.IsRoot u
    · rw [ite_eq_left (hr.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hr.mp h')), ite_eq_right h, hpar u hu, hrep]
  intro k
  induction k with
  | zero => intro u _; rfl
  | succ k ih =>
    intro u hu
    show iterate F'.up k (F'.up u) = iterate F.up k (F.up u)
    rw [hup u hu]
    exact ih _ (hcl u hu)

theorem desc_congr {F' : ForestData} (hE : F'.E = F.E) (hrep : F'.rep = F.rep) {P : Nat → Prop}
    (hpar : ∀ u, P u → F'.par u = F.par u) (hcl : ∀ u, P u → P (F.up u)) {v u : Nat} (hu : P u) :
    F'.Desc v u ↔ F.Desc v u := by
  unfold Desc
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [← iterate_up_congr hE hrep hpar hcl k u hu]; exact hk⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [iterate_up_congr hE hrep hpar hcl k u hu]; exact hk⟩

end ForestData

end STACS2027.Embed
