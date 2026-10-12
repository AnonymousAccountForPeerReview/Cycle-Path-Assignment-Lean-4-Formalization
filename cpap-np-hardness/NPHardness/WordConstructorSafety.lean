module

public import NPHardness.WordConstructorBounds

/-! Payload bounds for the word constructor: ready clause buffers have at most
three literals, and placed vertex labels stay below the gadget-block bound. -/

@[expose] public section
namespace STACS2027.WordConstructor
open Complexity.SAT

theorem ready_spec {rev c : List PlacedLiteral} (h : ready rev = some c) :
    rev = c.reverse ∧ c.length ≤ 3 := by
  cases rev with
  | nil => simp [ready] at h; subst c; simp
  | cons a rev =>
    cases rev with
    | nil => simp [ready] at h; subst c; simp
    | cons b rev =>
      cases rev with
      | nil => simp [ready] at h; subst c; simp
      | cons d rev =>
        cases rev with
        | nil => simp [ready] at h; subst c; simp
        | cons e rev => simp [ready] at h

theorem block_payload {k n b v u : Nat} (hv : v ≤ n+b) (hu : u < gadgetWidth k) :
    blockVertex (gadgetWidth k) v u < (n+b+1)*gadgetWidth k := by
  have hm := Nat.mul_le_mul_right (gadgetWidth k) hv
  simp only [blockVertex, Nat.add_mul, Nat.one_mul] at *
  omega

theorem mapEdge_payload {es : Graph} {W B : Nat} {t : Nat → Nat}
    (hb : VerticesBelow es W) (ht : ∀ u, u < W → t u < B) {e : Edge} (he : e ∈ es) :
    (mapEdge t e).1 < B ∧ (mapEdge t e).2 < B :=
  (edge_below ..).mpr ⟨ht _ (hb e he).1,ht _ (hb e he).2⟩

end STACS2027.WordConstructor
