module

public import NPHardness.PlanarAssemblyBoundary

/-!
Constructing boundary routing from actual first-hit face walks. The one local
order requirement says which source incidence port is encountered next around
a gadget's selected outer face. All intermediate darts are explicitly required
to be unmarked. This isolates the finite cyclic-order/reflection step needed to
instantiate the assembly for the Figure 4 gadgets.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar

/-- Starting at an unmarked dart, this is the first marked port reached by the
old gadget face walk. The witness includes absence of earlier marked darts. -/
def NextPort {n m : Nat} {G : Hypermap n} (P : PortPairing G)
    (port : Fin m → Fin n) (d : Fin n) (i : Fin m) : Prop :=
  ∃ k, 0<k ∧ iterate G.face k d = port i ∧
    ∀ j, j<k → P.marked (iterate G.face j d) = false

namespace NextPort
variable {n m : Nat} {G : Hypermap n} {P : PortPairing G} {port : Fin m → Fin n}

theorem unique (hinj : ∀ i j, port i=port j → i=j)
    (hm : ∀ i, P.marked (port i)=true) {d : Fin n} {i j : Fin m}
    (hi : NextPort P port d i) (hj : NextPort P port d j) : i=j := by
  obtain ⟨a,_,ha,hna⟩ := hi
  obtain ⟨b,_,hb,hnb⟩ := hj
  have hab : a=b := by
    apply Classical.byContradiction
    intro hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hn := hnb a hlt
      rw [ha,hm] at hn
      contradiction
    · have hn := hna b hlt
      rw [hb,hm] at hn
      contradiction
  apply hinj
  rw [← ha,← hb,hab]

theorem unshift {d : Fin n} {i : Fin m} (hd : P.marked d=false)
    (h : NextPort P port (G.face d) i) : NextPort P port d i := by
  obtain ⟨k,hk,he,hn⟩ := h
  refine ⟨k+1,by omega,he,?_⟩
  intro j hj
  cases j with
  | zero => exact hd
  | succ j => exact hn j (by omega)

theorem shift (hm : ∀ i, P.marked (port i)=true)
    {d : Fin n} {i : Fin m} (hd : P.marked (G.face d)=false)
    (h : NextPort P port d i) : NextPort P port (G.face d) i := by
  obtain ⟨k,hk,he,hn⟩ := h
  have hk2 : 2≤k := by
    by_cases hk1 : k=1
    · rw [hk1] at he
      have hm' := hm i
      change G.face d = port i at he
      rw [← he,hd] at hm'
      contradiction
    · omega
  refine ⟨k-1,by omega,?_,?_⟩
  · have hke : k = (k-1)+1 := by omega
    rw [hke] at he
    exact he
  · intro j hj
    exact hn (j+1) (by omega)

theorem predecessor (hm : ∀ i, P.marked (port i)=true) (i : Fin m) :
    NextPort P port (faceInverse G (port i)) i := by
  have hu : P.marked (faceInverse G (port i))=false := by
    cases hx : P.marked (faceInverse G (port i))
    · rfl
    · have hh := P.face_separated _ hx
      rw [face_faceInverse,hm] at hh
      contradiction
  refine ⟨1,by decide,face_faceInverse G (port i),?_⟩
  intro j hj
  have hj0 : j=0 := by omega
  subst j
  exact hu

end NextPort

/-- Source incidence darts represented by selected local port darts, with the
required actual local cyclic order. Reversing a local embedding reverses this
order; selecting the correct reflection is a separate finite construction. -/
structure OrderedIncidencePorts {n m : Nat} {G : Hypermap n} (P : PortPairing G)
    (I : Hypermap m) where
  port : Fin m → Fin n
  injective : ∀ i j, port i=port j → i=j
  marked_port : ∀ i, P.marked (port i)=true
  every_marked : ∀ d, P.marked d=true → ∃ i, port i=d
  pair_port : ∀ i, P.pair (port i)=port (I.edge i)
  edge_involution : ∀ i, I.edge (I.edge i)=i
  order : ∀ i, NextPort P port (G.face (port i)) (I.face (I.edge i))

namespace OrderedIncidencePorts
variable {n m : Nat} {G : Hypermap n} {P : PortPairing G} {I : Hypermap m}
  (O : OrderedIncidencePorts P I)

noncomputable def boundary (d : Fin n) : Option (Fin m) := by
  classical
  exact if h : ∃ i, NextPort P O.port d i then some (faceInverse I (Classical.choose h)) else none

theorem boundary_of_next {d : Fin n} {i : Fin m} (h : NextPort P O.port d i) :
    O.boundary d = some (faceInverse I i) := by
  unfold boundary
  rw [dite_eq_left (show ∃ i, NextPort P O.port d i from ⟨i,h⟩)]
  have he := NextPort.unique O.injective O.marked_port (Classical.choose_spec
    (show ∃ i, NextPort P O.port d i from ⟨i,h⟩)) h
  rw [he]

theorem boundary_after (i : Fin m) : O.boundary (G.face (O.port i)) = some (I.edge i) := by
  rw [O.boundary_of_next (O.order i)]
  congr 1
  change I.edge (I.node (I.face (I.edge i))) = I.edge i
  rw [I.edgeK]

theorem boundary_before (i : Fin m) :
    O.boundary (faceInverse G (O.port i)) = some (faceInverse I i) :=
  O.boundary_of_next (NextPort.predecessor O.marked_port i)

theorem boundary_step {d : Fin n} (hd : P.marked d=false)
    (hf : P.marked (G.face d)=false) : O.boundary (G.face d)=O.boundary d := by
  by_cases h : ∃ i, NextPort P O.port d i
  · obtain ⟨i,hi⟩ := h
    rw [O.boundary_of_next hi,O.boundary_of_next (NextPort.shift O.marked_port hf hi)]
  · have hnext : ¬ ∃ i, NextPort P O.port (G.face d) i := by
      rintro ⟨i,hi⟩
      exact h ⟨i,NextPort.unshift hd hi⟩
    simp only [boundary,dite_eq_right h,dite_eq_right hnext]

/-- Boundary labels are constructed from face walks; no assembled face-orbit
or planarity conclusion occurs among the required inputs. -/
noncomputable def routing : BoundaryRouting P I where
  port := O.port
  marked_port := O.marked_port
  every_marked := O.every_marked
  pair_port := O.pair_port
  edge_involution := O.edge_involution
  boundary := O.boundary
  after_port := O.boundary_after
  before_port := O.boundary_before
  unmarked_step _ hd hf := O.boundary_step hd hf

/-- The face-count contribution of the source follows from actual cyclic order. -/
theorem face_count_lower_bound :
    P.digonCount + O.routing.interiorFaceCount + cycleCount I.face ≤ cycleCount P.assembled.face :=
  O.routing.face_count_lower_bound

end OrderedIncidencePorts
end STACS2027.PlanarAssembly
