module

public import NPHardness.PlanarAssemblyPortSelection
public import NPHardness.PlanarGluingReflection

/-! A fixed-point-free cyclic order of three ports returns after three steps
(`three_port_order_cube`). -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

def turn3 (i : Fin 3) : Fin 3 := if i=0 then 1 else if i=1 then 2 else 0

/-- A fixed-point-free permutation of three ports returns after three steps. -/
theorem three_port_order_cube (q : Fin 3 → Fin 3)
    (hq : ∀ i j, q i=q j → i=j) (hqf : ∀ i, q i≠i) :
    ∀ i, q (q (q i))=i := by
  have hi : ∀ i j, turn3 i=turn3 j → i=j := by decide
  have hf : ∀ i, turn3 i≠i := by decide
  have hc : ∀ i, turn3 (turn3 (turn3 i))=i := by decide
  rcases three_port_orders q turn3 hq hi hqf hf with h | h
  · intro i
    simp only [h,hc]
  · intro i
    simp only [h,hc]

end STACS2027.PlanarAssembly
