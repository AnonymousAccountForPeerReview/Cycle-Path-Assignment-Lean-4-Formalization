module

public import NPHardness.PlanarAssemblyPortOrder

/-! Ports on a common face reach one another along the face permutation, and two
ports have only one cyclic order. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

/-- A common actual face root implies mutual reachability of the port darts. -/
theorem common_face_reaches {n m : Nat} (G : Hypermap n)
    (root : Fin n) (port : Fin m → Fin n)
    (hroot : ∀ i, Reaches G.face root (port i)) :
    ∀ i j, Reaches G.face (port i) (port j) := by
  intro i j
  exact ((hroot i).symm (hm_face_inj G)).trans (hroot j)

/-- Two distinct ports on one face have only one possible first-hit order. -/
theorem two_port_orders (p q : Fin 2 → Fin 2)
    (hp : ∀ i, p i≠i) (hq : ∀ i, q i≠i) : ∀ i, p i=q i := by
  intro i
  have hi := i.isLt
  have hpi := (p i).isLt
  have hqi := (q i).isLt
  have hpv : (p i).val≠i.val := fun h => hp i (Fin.ext h)
  have hqv : (q i).val≠i.val := fun h => hq i (Fin.ext h)
  apply Fin.ext
  omega

end STACS2027.PlanarAssembly
