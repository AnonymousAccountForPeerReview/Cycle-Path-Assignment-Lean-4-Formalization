module

public import NPHardness.PlanarGluingTransport
import Lean.Elab.Tactic.Omega

/-! Paths of hypermap moves (`LinkedPath`) and the lemmas relating node and face
orbits to them, used for connectivity of assembled embeddings. -/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

theorem nodePredecessor_node {n : Nat} (G : Hypermap n) (a : Fin n) :
    G.face (G.edge (G.node a)) = a :=
  hm_node_inj G _ _ (G.edgeK (G.node a))

def LinkedPath {n : Nat} (G : Hypermap n) (x y : Fin n) : Prop :=
  ∃ k, G.linked k x y = true

theorem LinkedPath.refl {n : Nat} (G : Hypermap n) (x : Fin n) : LinkedPath G x x :=
  ⟨0, Linked.linked_refl G 0 x⟩

theorem LinkedPath.step {n : Nat} (G : Hypermap n) {x y : Fin n}
    (h : Linked.Step G x y) : LinkedPath G x y :=
  ⟨1, Linked.linked_step G (Linked.linked_refl G 0 x) h⟩

theorem LinkedPath.trans {n : Nat} {G : Hypermap n} {x y z : Fin n}
    (hxy : LinkedPath G x y) (hyz : LinkedPath G y z) : LinkedPath G x z := by
  obtain ⟨k, hk⟩ := hxy
  obtain ⟨l, hl⟩ := hyz
  exact ⟨k + l, Linked.linked_trans G hk hl⟩

theorem LinkedPath.symm {n : Nat} {G : Hypermap n} {x y : Fin n}
    (h : LinkedPath G x y) : LinkedPath G y x := by
  obtain ⟨k, hk⟩ := h
  exact hm_linked_symm G hk

theorem nodeOrbit_linked {n : Nat} (G : Hypermap n) {x y : Fin n}
    (h : Reaches G.node x y) : LinkedPath G x y := by
  obtain ⟨k, rfl⟩ := h
  induction k generalizing x with
  | zero => exact LinkedPath.refl _ _
  | succ k ih =>
    exact (LinkedPath.step G (Or.inr (Or.inl rfl))).trans (ih (x := G.node x))

theorem faceOrbit_linked {n : Nat} (G : Hypermap n) {x y : Fin n}
    (h : Reaches G.face x y) : LinkedPath G x y := by
  obtain ⟨k, rfl⟩ := h
  induction k generalizing x with
  | zero => exact LinkedPath.refl _ _
  | succ k ih =>
    exact (LinkedPath.step G (Or.inr (Or.inr rfl))).trans (ih (x := G.face x))

end STACS2027.PlanarGluing
