module

public import NPHardness.PlanarAssemblyPortProfilePrograms
public import NPHardness.PlanarAssemblySphericalPlaced

/-!
Reflection and monotone vertex-block placement preserve exact directed port
profiles. The variable profile is reflected precisely when the source sign is
false, yielding an explicit Boolean endpoint-direction table for every k.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

namespace SphericalPortProfile
variable {g : Graph} {m : Nat} {ports : Fin m→Edge} {next : Fin m→Fin m} {side : Fin m→Bool}

theorem mirror (hp:SphericalPortProfile g ports next side)
    (prev:Fin m→Fin m) (hinv:∀i,next (prev i)=i) :
    SphericalPortProfile g ports prev (fun i=>!(side i)) := by
  obtain ⟨G,hG,hs,p,hi,he,hnext,hside⟩:=hp
  have hE:∀d,G.edge d=graphEdge d:=fun d=>Fin.ext (hG.1 d)
  have he2:∀d,G.edge (G.edge d)=d:=Reflection.embedding_edge_twice hG
  refine ⟨Reflection.mirror G he2,Reflection.mirror_embedding hG he2,
    Reflection.mirror_spherical G he2 hs,fun i=>G.edge (p i),?_,?_,?_,?_⟩
  · intro i j hij
    exact hi i j (hm_edge_inj G _ _ hij)
  · intro i
    dsimp only
    rw [hE,graphEdge_index,he]
  · intro i
    have hn:=hnext (prev i)
    rw [hinv] at hn
    exact hn.mirror he2
  · intro i
    dsimp only
    rw [hE,dartSide_graphEdge,hside]

theorem relabel (hp:SphericalPortProfile g ports next side) (f:Nat→Nat)
    (hf:∀a b,f a=f b→a=b) :
    SphericalPortProfile (g.map (fun e=>(f e.1,f e.2)))
      (fun i=>(f (ports i).1,f (ports i).2)) next side := by
  unfold SphericalPortProfile IsGraphEmbedding
  rw [List.length_map]
  obtain ⟨G,hG,hs,p,hi,he,hnext,hside⟩:=hp
  refine ⟨G,⟨hG.1,?_,hG.2.2⟩,hs,p,hi,?_,hnext,hside⟩
  · intro d e
    rw [halfEdgeEnd_relabel,halfEdgeEnd_relabel,hG.2.1]
    constructor
    · exact congrArg (Option.map f)
    · intro h
      generalize hd:halfEdgeEnd g d.val=a at h ⊢
      generalize he:halfEdgeEnd g e.val=b at h ⊢
      cases a with
      | none => cases b <;> simp_all
      | some a =>
        cases b with
        | none => simp at h
        | some b => exact congrArg some (hf a b (Option.some.inj h))
  · intro i
    simp only [List.getElem?_map,he,Option.map_some]

theorem block (hp:SphericalPortProfile g ports next side) (hg:EdgesOrdered g)
    (hports:∀i,(ports i).1≤(ports i).2) (width tag:Nat) :
    SphericalPortProfile (mapGraph (blockVertex width tag) g)
      (fun i=>mapEdge (blockVertex width tag) (ports i)) next side := by
  rw [mapGraph_block_eq hg]
  have he:(fun i=>mapEdge (blockVertex width tag) (ports i))=
      (fun i=>(blockVertex width tag (ports i).1,blockVertex width tag (ports i).2)):=
    funext (fun i=>mapEdge_block_eq (hports i))
  rw [he]
  exact hp.relabel _ (fun _ _ h=>Nat.add_left_cancel h)

end SphericalPortProfile

def variableSignedNext (sign:Bool) (i:Fin 3) : Fin 3 :=
  if sign then variablePortPrev i else variablePortNext i

def variableSignedSide (sign:Bool) (i:Fin 3) : Bool := (i==0)==(!sign)

theorem variableGraph_signed_profile (k:Nat) (sign:Bool) :
    SphericalPortProfile (variableGraph k) variablePortEdgeAt
      (variableSignedNext sign) (variableSignedSide sign) := by
  cases sign
  · have he:variableSignedSide false=variablePortSide:=
      funext (by decide:∀i:Fin 3,variableSignedSide false i=variablePortSide i)
    change SphericalPortProfile (variableGraph k) variablePortEdgeAt variablePortNext (variableSignedSide false)
    rw [he]
    exact variableGraph_port_profile k
  · have h:=(variableGraph_port_profile k).mirror variablePortPrev
      (by decide:∀i:Fin 3,variablePortNext (variablePortPrev i)=i)
    have he:variableSignedSide true=(fun i=>!(variablePortSide i)):=
      funext (by decide:∀i:Fin 3,variableSignedSide true i= !(variablePortSide i))
    change SphericalPortProfile (variableGraph k) variablePortEdgeAt variablePortPrev (variableSignedSide true)
    rw [he]
    exact h

theorem placedVariableGraph_signed_profile (k v:Nat) (sign:Bool) :
    SphericalPortProfile (placedVariableGraph k v)
      (fun i=>mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdgeAt i))
      (variableSignedNext sign) (variableSignedSide sign) :=
  (variableGraph_signed_profile k sign).block (realizeLinks_ordered _ _)
    (fun i=>by unfold variablePortEdgeAt edge;omega) _ _

theorem placedClauseThreeGraph_port_profile (k tag:Nat) :
    SphericalPortProfile (mapGraph (blockVertex (gadgetWidth k) tag) (clauseThreeGraph k))
      (fun i=>mapEdge (blockVertex (gadgetWidth k) tag) (clauseThreePortEdgeAt i))
      clauseThreePortNext (fun _=>true) :=
  (clauseThreeGraph_port_profile k).block (realizeLinks_ordered _ _)
    (fun i=>by unfold clauseThreePortEdgeAt edge;omega) _ _

theorem placedClauseTwoGraph_port_profile (k tag:Nat) :
    SphericalPortProfile (mapGraph (blockVertex (gadgetWidth k) tag) (clauseTwoGraph k))
      (fun i=>mapEdge (blockVertex (gadgetWidth k) tag) (clauseTwoPortEdgeAt i))
      clauseTwoPortNext (fun _=>true) :=
  (clauseTwoGraph_port_profile k).block (realizeLinks_ordered _ _)
    (fun i=>by unfold clauseTwoPortEdgeAt edge;omega) _ _

end STACS2027.PlanarAssembly
