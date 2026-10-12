module

public import NPHardness.PlanarOperationsPortsGadgets

/-!
Simultaneous port-edge assembly on actual hypermap darts. Both copies of each
matched port edge are retained. The marked outer-face darts form new digon
faces; the unmarked face walks are routed through their matched gadget ports.
This module constructs the rotation and proves its local consistency. Global
node-orbit completeness and the remaining face count are separate obligations.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar

/-- The inverse of the face permutation of a finite hypermap. -/
def faceInverse {n : Nat} (G : Hypermap n) (d : Fin n) : Fin n := G.edge (G.node d)

theorem face_faceInverse {n : Nat} (G : Hypermap n) (d : Fin n) :
    G.face (faceInverse G d) = d :=
  hm_node_inj G _ _ (G.edgeK (G.node d))

theorem faceInverse_face {n : Nat} (G : Hypermap n) (d : Fin n) :
    faceInverse G (G.face d) = d :=
  hm_face_inj G _ _ (face_faceInverse G (G.face d))

/-- Pair selected outer-face darts at opposite ends of each incidence. The
separation condition follows when the local port edges have disjoint endpoints. -/
structure PortPairing {n : Nat} (G : Hypermap n) where
  marked : Fin n → Bool
  pair : Fin n → Fin n
  pair_pair : ∀ d, pair (pair d) = d
  pair_marked : ∀ d, marked (pair d) = marked d
  pair_ne : ∀ d, marked d = true → pair d ≠ d
  face_separated : ∀ d, marked d = true → marked (G.face d) = false

namespace PortPairing
variable {n : Nat} {G : Hypermap n} (P : PortPairing G)

/-- Exchange a marked dart `d` with the old face-successor of its matched dart.
This splices both endpoints of every port edge simultaneously. -/
def switch (d : Fin n) : Fin n :=
  if P.marked d then G.face (P.pair d)
  else if P.marked (faceInverse G d) then P.pair (faceInverse G d) else d

theorem switch_marked {d : Fin n} (hd : P.marked d = true) :
    P.switch d = G.face (P.pair d) := by simp only [switch,hd,↓reduceIte]

theorem switch_face_marked {d : Fin n} (hd : P.marked d = true) :
    P.switch (G.face d) = P.pair d := by
  simp only [switch,P.face_separated d hd,Bool.false_eq_true,↓reduceIte,faceInverse_face,hd]

theorem switch_involutive (d : Fin n) : P.switch (P.switch d) = d := by
  cases hd : P.marked d
  · cases hi : P.marked (faceInverse G d)
    · simp only [switch,hd,hi,Bool.false_eq_true,↓reduceIte]
    · have hp : P.marked (P.pair (faceInverse G d)) = true := by rw [P.pair_marked,hi]
      rw [switch,switch]
      simp only [hd,hi,hp,Bool.false_eq_true,↓reduceIte,P.pair_pair,face_faceInverse]
  · rw [P.switch_marked hd,P.switch_face_marked (by rw [P.pair_marked,hd]),P.pair_pair]

/-- The assembled rotation retains every original dart and every edge copy. -/
def assembled : Hypermap n where
  edge := G.edge
  node d := G.node (P.switch d)
  face d := P.switch (G.face d)
  edgeK d := by
    change G.node (P.switch (P.switch (G.face (G.edge d)))) = d
    rw [P.switch_involutive,G.edgeK]

/-- Matched marked darts bound the face between the two retained port-edge copies. -/
theorem assembled_face_marked {d : Fin n} (hd : P.marked d = true) :
    P.assembled.face d = P.pair d := P.switch_face_marked hd

/-- Outside the new digons, face walks follow the original face until a port is
encountered, then continue after the matched port in its other gadget. -/
theorem assembled_face_unmarked {d : Fin n} (hd : P.marked d = false) :
    P.assembled.face d =
      if P.marked (G.face d) then G.face (P.pair (G.face d)) else G.face d := by
  change P.switch (G.face d) = _
  simp only [switch,faceInverse_face,hd,Bool.false_eq_true,↓reduceIte]

theorem assembled_face_preserves_marked (d : Fin n) :
    P.marked (P.assembled.face d) = P.marked d := by
  cases hd : P.marked d
  · rw [P.assembled_face_unmarked hd]
    cases hf : P.marked (G.face d)
    · exact hf
    · simp only [↓reduceIte]
      exact P.face_separated _ (by rw [P.pair_marked,hf])
  · rw [P.assembled_face_marked hd,P.pair_marked,hd]

/-- The source and target ends of a port are exchanged with the corresponding
ends of its matched port, as required for attachment across two disks. -/
theorem node_face_eq_edge (hE : ∀ d, G.edge (G.edge d) = d) (d : Fin n) :
    G.node (G.face d) = G.edge d := by
  have h := G.edgeK (G.edge d)
  rw [hE] at h
  exact h

theorem switch_end {W : Type} (ends : Fin n → W)
    (hE : ∀ d, G.edge (G.edge d) = d)
    (hN : ∀ d, ends (G.node d) = ends d)
    (hglue : ∀ d, P.marked d = true → ends d = ends (G.edge (P.pair d)))
    (d : Fin n) : ends (P.switch d) = ends d := by
  have hF : ∀ x, ends (G.face x) = ends (G.edge x) := by
    intro x
    rw [← hN (G.face x),node_face_eq_edge hE x]
  cases hd : P.marked d
  · cases hi : P.marked (faceInverse G d)
    · simp only [switch,hd,hi,Bool.false_eq_true,↓reduceIte]
    · simp only [switch,hd,hi,Bool.false_eq_true,↓reduceIte]
      rw [hglue _ (by rw [P.pair_marked,hi]),P.pair_pair,← hF,face_faceInverse]
  · rw [P.switch_marked hd,hF]
    exact (hglue d hd).symm

/-- Every new rotation step keeps the concrete identified endpoint unchanged. -/
theorem assembled_node_end {W : Type} (ends : Fin n → W)
    (hE : ∀ d, G.edge (G.edge d) = d)
    (hN : ∀ d, ends (G.node d) = ends d)
    (hglue : ∀ d, P.marked d = true → ends d = ends (G.edge (P.pair d)))
    (d : Fin n) : ends (P.assembled.node d) = ends d := by
  change ends (G.node (P.switch d)) = ends d
  rw [hN,P.switch_end ends hE hN hglue]

end PortPairing
end STACS2027.PlanarAssembly
