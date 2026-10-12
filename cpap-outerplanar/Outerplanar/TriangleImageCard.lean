module

public import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-! Finite image bounds for triangle contraction. -/

@[expose] public section
namespace STACS2027.TriangleMatching

theorem card_le_image_add_exceptional {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S E : Finset α) (φ : α→β) (hinj : Set.InjOn φ (↑(S\E) : Set α)) :
    S.card≤(S.image φ).card+E.card := by
  have hi : (S\E).card≤(S.image φ).card := by
    rw [←Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card (Finset.image_subset_image Finset.sdiff_subset)
  have h := Finset.card_le_card_sdiff_add_card (s:=S) (t:=E)
  omega

theorem card_le_image_add_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (φ : α→β) (a : α)
    (hcollision : ∀x∈S,∀y∈S,φ x=φ y→x=y∨x=a∨y=a) :
    S.card≤(S.image φ).card+1 := by
  have hinj : Set.InjOn φ (↑(S\{a}) : Set α) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_sdiff.mp hx
    have hy' := Finset.mem_sdiff.mp hy
    rcases hcollision x hx'.1 y hy'.1 hxy with h | h | h
    · exact h
    · exact False.elim (hx'.2 (by simpa using h))
    · exact False.elim (hy'.2 (by simpa using h))
  simpa using card_le_image_add_exceptional S {a} φ hinj

end STACS2027.TriangleMatching
