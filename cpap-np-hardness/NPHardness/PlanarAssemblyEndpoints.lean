module

public import NPHardness.PlanarAssemblyEuler

/-!
Endpoint conditions for actual port-edge assembly. Pairwise disjoint local
port endpoints imply separation of marked face darts and of node switches.
A quotient identifying exactly the matched endpoint pairs gives full node-orbit
correctness. These lemmas connect the dart construction to ordinary graph
endpoint and vertex-identification statements.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

/-- One of the two graph endpoints of a selected port dart. -/
def portEndpoint {n : Nat} {W : Type} (G : Hypermap n) (ends : Fin n → W)
    (d : Fin n) (side : Bool) : W := if side then ends (G.edge d) else ends d

/-- All selected port edges have disjoint endpoints, including their own two
endpoints. The selection uses one dart per port edge. -/
def DisjointPortEndpoints {n : Nat} {W : Type} (G : Hypermap n)
    (ends : Fin n → W) (marked : Fin n → Bool) : Prop :=
  ∀a b,marked a=true→marked b=true→∀s t,
    portEndpoint G ends a s=portEndpoint G ends b t→a=b ∧ s=t

theorem face_endpoint {n : Nat} {W : Type} (G : Hypermap n) (ends : Fin n → W)
    (hE : ∀d,G.edge (G.edge d)=d) (hN : ∀d,ends (G.node d)=ends d) (d : Fin n) :
    ends (G.face d)=ends (G.edge d) := by
  rw [←hN (G.face d),PortPairing.node_face_eq_edge hE]

/-- Disjoint port endpoints force at least one unmarked dart between marked
outer-face darts. This proves the separation field used to construct a pairing. -/
theorem face_marked_false {n : Nat} {W : Type} (G : Hypermap n)
    (ends : Fin n → W) (marked : Fin n → Bool)
    (hE : ∀d,G.edge (G.edge d)=d) (hN : ∀d,ends (G.node d)=ends d)
    (hports : DisjointPortEndpoints G ends marked) {d : Fin n} (hd : marked d=true) :
    marked (G.face d)=false := by
  cases hm : marked (G.face d)
  · rfl
  · have he : portEndpoint G ends d true=portEndpoint G ends (G.face d) false :=
      (face_endpoint G ends hE hN d).symm
    have hh := (hports d (G.face d) hd hm true false he).2
    contradiction

namespace PortPairing
variable {n : Nat} {G : Hypermap n} (P : PortPairing G)

/-- Every switched dart is either a selected port dart or its old face successor. -/
theorem active_dart_rep {d : Fin n} (hd : P.switch d≠d) :
    ∃a,P.marked a=true ∧ ∃s:Bool,d=if s then G.face a else a := by
  cases hm : P.marked d
  · cases hi : P.marked (faceInverse G d)
    · have he : P.switch d=d := by simp only [switch,hm,hi,Bool.false_eq_true,↓reduceIte]
      exact False.elim (hd he)
    · exact ⟨faceInverse G d,hi,true,(face_faceInverse G d).symm⟩
  · exact ⟨d,hm,false,rfl⟩

/-- The separation of old node switches follows from concrete graph endpoints;
it need not be established by reasoning directly about permutation orbits. -/
theorem disjoint_node_switches {W : Type} (ends : Fin n → W)
    (hE : ∀d,G.edge (G.edge d)=d) (hN : ∀d,ends (G.node d)=ends d)
    (hports : DisjointPortEndpoints G ends P.marked) : P.DisjointNodeSwitches := by
  intro x y hx hy hxy
  obtain ⟨a,ha,s,hx⟩ := P.active_dart_rep hx
  obtain ⟨b,hb,t,hy⟩ := P.active_dart_rep hy
  have he : ends x=ends y := by
    obtain ⟨k,hk⟩ := hxy
    rw [←hk,iterate_invariant G.node ends hN]
  have hside : ∀d s,ends (if s then G.face d else d)=portEndpoint G ends d s := by
    intro d s
    cases s
    · rfl
    · exact face_endpoint G ends hE hN d
  rw [hx,hy,hside,hside] at he
  obtain ⟨hab,hst⟩ := hports a b ha hb s t he
  rw [hx,hy,hab,hst]

/-- Exact fiber condition on a quotient of the original vertex labels. Every
new equality either existed before assembly or is one selected matched pair. -/
def MatchedEndpointFibers {V W : Type} (ends : Fin n → V) (q : V → W) : Prop :=
  ∀a b,q (ends a)=q (ends b)→ends a=ends b ∨
    ∃d,P.marked d=true ∧
      ((ends a=ends d ∧ ends b=ends (G.edge (P.pair d))) ∨
       (ends b=ends d ∧ ends a=ends (G.edge (P.pair d))))

/-- Concrete quotient endpoint fibers imply the exact old-node/switch path
condition used by the assembled node-orbit theorem. -/
theorem endpoint_fibers {V W : Type} (ends : Fin n → V) (q : V → W)
    (hE : ∀d,G.edge (G.edge d)=d)
    (hN : ∀a b,Reaches G.node a b ↔ ends a=ends b)
    (hfib : P.MatchedEndpointFibers ends q) : P.EndpointFibers (fun d=>q (ends d)) := by
  have hn : ∀d,ends (G.node d)=ends d := by
    intro d
    exact ((hN d (G.node d)).mp (Reaches.step G.node d)).symm
  have hs : ∀d,P.marked d=true→ends (P.switch d)=ends (G.edge (P.pair d)) := by
    intro d hd
    rw [P.switch_marked hd,face_endpoint G ends hE hn]
  intro a b hab
  rcases hfib a b hab with he | ⟨d,hd,he | he⟩
  · exact Or.inl ((hN a b).mpr he)
  · exact Or.inr ⟨d,(hN a d).mpr he.1,(hN (P.switch d) b).mpr ((hs d hd).trans he.2.symm)⟩
  · refine Or.inr ⟨P.switch d,(hN a (P.switch d)).mpr (he.2.trans (hs d hd).symm),?_⟩
    rw [P.switch_involutive]
    exact (hN d b).mpr he.1.symm

end PortPairing
end STACS2027.PlanarAssembly
