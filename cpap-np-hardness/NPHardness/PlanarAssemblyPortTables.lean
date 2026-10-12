module

public import NPHardness.PlanarAssemblyPortEnds
public import NPHardness.PlanarAssemblyLocalOrder

/-! Exact finite boundary profiles of the three registered Figure 4 skeleton
embeddings. The profile records both first-hit order and endpoint direction;
all table checks are kernel-evaluated finite propositions. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def SphericalPortProfile (g : Graph) {m : Nat} (portEdges : Fin m → Edge)
    (next : Fin m → Fin m) (side : Fin m → Bool) : Prop :=
  ∃ G : Hypermap (2*g.length), IsGraphEmbedding g G ∧
    2*G.componentCount+2*g.length≤G.eulerRhs ∧
    ∃ port : Fin m → Fin (2*g.length),
      (∀ i j, port i=port j → i=j) ∧
      (∀ i, g[(port i).val/2]?=some (portEdges i)) ∧
      (∀ i, NextSelected G.face port i (next i)) ∧
      (∀ i, dartSide (port i)=side i)

theorem sphericalPortProfile_of_tables (g : Graph) (t : EmbedTables) (h : EmbedOK t)
    (hlen : g.length=t.n2)
    (hends : ∀ d, d<2*t.n2 → halfEdgeEnd g d=some (t.EN d))
    (hEuler : 2*t.cC (2*t.n2)+t.n2≤t.cR (2*t.n2)+t.cF (2*t.n2))
    {m : Nat} (portEdges : Fin m → Edge) (next : Fin m → Fin m) (side : Fin m → Bool)
    (port : Fin m → Fin (2*t.n2)) (steps : Fin m → Nat)
    (hinj : ∀ i j, port i=port j → i=j)
    (hlookup : ∀ i, g[(port i).val/2]?=some (portEdges i))
    (hsteps : ∀ i, 0<steps i)
    (hnext : ∀ i, iterate t.F (steps i) (port i).val=(port (next i)).val)
    (hfirst : ∀ i, ∀ r : Fin (steps i), 0<r.val → ∀ j,
      iterate t.F r.val (port i).val≠(port j).val)
    (hside : ∀ i, !(port i).val%2==0=side i) :
    SphericalPortProfile g portEdges next side := by
  unfold SphericalPortProfile IsGraphEmbedding
  rw [hlen]
  refine ⟨h.hypermap,⟨fun _ => rfl,?_,?_⟩,tables_spherical h hEuler,port,hinj,hlookup,?_,hside⟩
  · intro d d'
    rw [hends d.val d.isLt,hends d'.val d'.isLt]
    constructor
    · rintro ⟨k,hk⟩
      have hh := h.iterate_EN k d.isLt
      rw [← h.iterate_node k d,hk] at hh
      rw [hh]
    · intro he
      obtain ⟨k,hk⟩ := h.orbit d.isLt d'.isLt (Option.some.inj he)
      exact ⟨k,Fin.ext (by rw [h.iterate_node k d,hk])⟩
  · rw [planar_iff]
    have hh := tables_spherical h hEuler
    omega
  · intro i
    refine ⟨steps i,hsteps i,Fin.ext (by rw [h.iterate_face]; exact hnext i),?_⟩
    intro r hr hrk j he
    have hh := congrArg Fin.val he
    rw [h.iterate_face] at hh
    exact hfirst i ⟨r,hrk⟩ hr j hh

def variablePortNext (i : Fin 3) : Fin 3 := if i=0 then 2 else if i=1 then 0 else 1
/-- The inverse of `variablePortNext`, the port order of the mirrored embedding. -/
def variablePortPrev (i : Fin 3) : Fin 3 := if i=0 then 1 else if i=1 then 2 else 0
def clauseThreePortNext (i : Fin 3) : Fin 3 := if i=0 then 2 else if i=1 then 0 else 1
def clauseTwoPortNext (i : Fin 2) : Fin 2 := if i=0 then 1 else 0
def variablePortSide (i : Fin 3) : Bool := i==0

def variableTablePort (i : Fin 3) : Fin 16 := if i=0 then 15 else if i=1 then 12 else 8
def clauseThreeTablePort (i : Fin 3) : Fin 48 := if i=0 then 1 else if i=1 then 17 else 37
def clauseTwoTablePort (i : Fin 2) : Fin 68 := if i=0 then 1 else 17

def variablePortEdgeAt (i : Fin 3) : Edge := edge (variableEndpoint i.val false) (variableEndpoint i.val true)
def clauseThreePortEdgeAt (i : Fin 3) : Edge := edge (clauseEndpoint i.val false) (clauseEndpoint i.val true)
def clauseTwoPortEdgeAt (i : Fin 2) : Edge := edge (clauseEndpoint i.val false) (clauseEndpoint i.val true)

theorem variable_skeleton_port_profile :
    SphericalPortProfile variableSkeleton variablePortEdgeAt variablePortNext variablePortSide := by
  apply sphericalPortProfile_of_tables variableSkeleton variableEmbedding variableEmbedding_valid
    rfl variableEmbedding_ends (by decide) variablePortEdgeAt variablePortNext variablePortSide
    variableTablePort (fun i => if i=0 then 3 else 2)
  · exact (by decide : ∀ i j : Fin 3, variableTablePort i=variableTablePort j → i=j)
  all_goals decide

theorem clauseThree_skeleton_port_profile :
    SphericalPortProfile clauseThree5 clauseThreePortEdgeAt clauseThreePortNext (fun _ => true) := by
  apply sphericalPortProfile_of_tables clauseThree5 clauseThreeEmbedding clauseThreeEmbedding_valid
    rfl clauseThreeEmbedding_ends (by decide) clauseThreePortEdgeAt clauseThreePortNext (fun _ => true)
    clauseThreeTablePort (fun i => if i=0 then 3 else if i=1 then 4 else 6)
  · exact (by decide : ∀ i j : Fin 3, clauseThreeTablePort i=clauseThreeTablePort j → i=j)
  all_goals decide

theorem clauseTwo_skeleton_port_profile :
    SphericalPortProfile clauseTwoSkeleton clauseTwoPortEdgeAt clauseTwoPortNext (fun _ => true) := by
  apply sphericalPortProfile_of_tables clauseTwoSkeleton clauseTwoEmbedding clauseTwoEmbedding_valid
    rfl clauseTwoEmbedding_ends (by decide) clauseTwoPortEdgeAt clauseTwoPortNext (fun _ => true)
    clauseTwoTablePort (fun i => if i=0 then 9 else 4)
  · exact (by decide : ∀ i j : Fin 2, clauseTwoTablePort i=clauseTwoTablePort j → i=j)
  all_goals decide

end STACS2027.PlanarAssembly
