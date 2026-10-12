module

public import NPHardness.PlanarAssemblyDarts

/-!
Node-orbit correctness of simultaneous port assembly. Disjoint port endpoints
ensure at most one switched dart in each original node orbit. Under that
condition all original node paths survive, and each switch joins exactly the
endpoint fibers it is meant to identify.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

/-- Follow an old orbit until its uniquely modified endpoint is encountered. -/
theorem reaches_until_on_orbit {α : Type} (p q : α → α) (a : α)
    (hstep : ∀ x, Reaches p x a → x ≠ a → q x = p x)
    (k : Nat) (x : α) (hk : iterate p k x = a) : Reaches q x a := by
  induction k generalizing x with
  | zero => exact ⟨0,hk⟩
  | succ k ih =>
    by_cases hx : x=a
    · subst x; exact Reaches.refl _ _
    · have hs : Reaches q x (p x) := ⟨1,hstep x ⟨k+1,hk⟩ hx⟩
      exact hs.trans (ih (p x) hk)

namespace PortPairing
variable {n : Nat} {G : Hypermap n} (P : PortPairing G)

/-- No original gadget vertex is used as two different attachment endpoints. -/
def DisjointNodeSwitches : Prop :=
  ∀ a b, P.switch a ≠ a → P.switch b ≠ b → Reaches G.node a b → a=b

theorem switch_active {d : Fin n} (hd : P.switch d ≠ d) :
    P.switch (P.switch d) ≠ P.switch d := by
  rw [P.switch_involutive]
  exact Ne.symm hd

/-- Every original node edge survives as a finite path in the assembled node
permutation, even when its immediate successor is changed. -/
theorem node_step_transfer (hdisj : P.DisjointNodeSwitches) (d : Fin n) :
    Reaches P.assembled.node d (G.node d) := by
  by_cases hd : P.switch d = d
  · exact ⟨1,by change G.node (P.switch d) = _; rw [hd]⟩
  · let a := P.switch d
    have ha : P.switch a ≠ a := P.switch_active hd
    obtain ⟨k,hk⟩ := back (hm_node_inj G) 1 a
    have hu := reaches_until_on_orbit G.node P.assembled.node a
      (fun x hx hxa => by
        change G.node (P.switch x) = G.node x
        have he : P.switch x = x := by
          apply Classical.byContradiction
          intro hne
          exact hxa (hdisj x a hne ha hx)
        rw [he]) k (G.node a) hk
    have hfirst : Reaches P.assembled.node d (G.node a) := ⟨1,rfl⟩
    have hlast : Reaches P.assembled.node a (G.node d) :=
      ⟨1,by change G.node (P.switch (P.switch d)) = _; rw [P.switch_involutive]⟩
    exact hfirst.trans (hu.trans hlast)

theorem node_orbit_transfer (hdisj : P.DisjointNodeSwitches) {a b : Fin n}
    (h : Reaches G.node a b) : Reaches P.assembled.node a b := by
  obtain ⟨k,rfl⟩ := h
  induction k generalizing a with
  | zero => exact Reaches.refl _ _
  | succ k ih =>
    exact (P.node_step_transfer hdisj a).trans (ih (a := G.node a))

/-- Both old vertices paired by a switch belong to one new node orbit. -/
theorem switch_node_orbit (hdisj : P.DisjointNodeSwitches) (a : Fin n) :
    Reaches P.assembled.node a (P.switch a) := by
  have hfirst : Reaches P.assembled.node a (G.node (P.switch a)) := ⟨1,rfl⟩
  have hback : Reaches G.node (G.node (P.switch a)) (P.switch a) :=
    back (hm_node_inj G) 1 (P.switch a)
  exact hfirst.trans (P.node_orbit_transfer hdisj hback)

/-- A concrete description of endpoint fibers: either the original vertex is
unchanged, or precisely one matched endpoint identification joins the vertices. -/
def EndpointFibers {W : Type} (ends : Fin n → W) : Prop :=
  ∀ a b, ends a = ends b →
    Reaches G.node a b ∨ ∃ d, Reaches G.node a d ∧ Reaches G.node (P.switch d) b

/-- Full node-orbit correctness, not merely endpoint invariance. -/
theorem assembled_node_orbit_iff {W : Type} (ends : Fin n → W)
    (hdisj : P.DisjointNodeSwitches)
    (hE : ∀ d, G.edge (G.edge d) = d)
    (hN : ∀ d, ends (G.node d) = ends d)
    (hglue : ∀ d, P.marked d = true → ends d = ends (G.edge (P.pair d)))
    (hfibers : P.EndpointFibers ends) (a b : Fin n) :
    (∃ k, iterate P.assembled.node k a = b) ↔ ends a = ends b := by
  constructor
  · rintro ⟨k,rfl⟩
    exact (iterate_invariant P.assembled.node ends
      (P.assembled_node_end ends hE hN hglue) k a).symm
  · intro he
    rcases hfibers a b he with h | ⟨d,ha,hb⟩
    · exact P.node_orbit_transfer hdisj h
    · exact (P.node_orbit_transfer hdisj ha).trans
        ((P.switch_node_orbit hdisj d).trans (P.node_orbit_transfer hdisj hb))

end PortPairing
end STACS2027.PlanarAssembly
