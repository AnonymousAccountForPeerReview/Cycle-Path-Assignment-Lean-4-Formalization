module

public import NPHardness.PlanarAssemblyRouting

/-! Two fixed-point-free cyclic orders of three ports either agree or are
opposite (`three_port_orders`). -/

@[expose] public section
namespace STACS2027.PlanarAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
open Complexity Complexity.Planar PlanarGluing

/-- Finite classification of the two fixed-point-free three-port cyclic orders. -/
theorem three_port_orders (p q : Fin 3 → Fin 3)
    (hp : ∀ i j, p i=p j → i=j) (hq : ∀ i j, q i=q j → i=j)
    (hpf : ∀ i, p i≠i) (hqf : ∀ i, q i≠i) :
    (∀ i, p i=q i) ∨ (∀ i, p i=q (q i)) := by
  have hf : ∀ a b c : Fin 3, a≠b → a≠c → b≠c → a≠0 → b≠1 → c≠2 →
      (a=1 ∧ b=2 ∧ c=0) ∨ (a=2 ∧ b=0 ∧ c=1) := by decide
  have pne : ∀ i j : Fin 3, i≠j → p i≠p j := fun _ _ hne he => hne (hp _ _ he)
  have qne : ∀ i j : Fin 3, i≠j → q i≠q j := fun _ _ hne he => hne (hq _ _ he)
  have hpclass := hf (p 0) (p 1) (p 2)
    (pne 0 1 (by decide)) (pne 0 2 (by decide)) (pne 1 2 (by decide)) (hpf 0) (hpf 1) (hpf 2)
  have hqclass := hf (q 0) (q 1) (q 2)
    (qne 0 1 (by decide)) (qne 0 2 (by decide)) (qne 1 2 (by decide)) (hqf 0) (hqf 1) (hqf 2)
  have all_three : ∀ {r s : Fin 3 → Fin 3}, r 0=s 0 → r 1=s 1 → r 2=s 2 → ∀ i, r i=s i := by
    intro r s h0 h1 h2 i
    have hi : i.val=0 ∨ i.val=1 ∨ i.val=2 := by have := i.isLt; omega
    rcases hi with hi | hi | hi
    · have he : i=0 := Fin.ext hi; subst i; exact h0
    · have he : i=1 := Fin.ext hi; subst i; exact h1
    · have he : i=2 := Fin.ext hi; subst i; exact h2
  rcases hpclass with ⟨p0,p1,p2⟩ | ⟨p0,p1,p2⟩ <;>
    rcases hqclass with ⟨q0,q1,q2⟩ | ⟨q0,q1,q2⟩
  · left; apply all_three <;> simp [p0,p1,p2,q0,q1,q2]
  · right; apply all_three <;> simp [p0,p1,p2,q0,q1,q2]
  · right; apply all_three <;> simp [p0,p1,p2,q0,q1,q2]
  · left; apply all_three <;> simp [p0,p1,p2,q0,q1,q2]

end STACS2027.PlanarAssembly
