module

public import NPHardness.PlanarAssemblyPortTables
public import NPHardness.PlanarAssemblyPortSubdivision

/-! Exact spherical boundary profiles survive edge-list permutation and
subdivision away from their selected port edges. Both cyclic order and the
chosen endpoint direction are preserved. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

/-- Transport exact first-hit order along a genuine dart equivalence. -/
theorem NextSelected.conjugate {n r m : Nat} (e : DartEquiv n r)
    {f : Fin n→Fin n} {port : Fin m→Fin n} {i j : Fin m}
    (h:NextSelected f port i j) :
    NextSelected (e.conjugate f) (fun i=>e.toFun (port i)) i j := by
  obtain ⟨k,hk,hend,hinside⟩ := h
  refine ⟨k,hk,?_,?_⟩
  · rw [e.iterate_conjugate,e.left_inv,hend]
  · intro r hr hrk t he
    rw [e.iterate_conjugate,e.left_inv] at he
    exact hinside r hr hrk t (e.injective he)

namespace SphericalPortProfile
variable {g h : Graph} {m : Nat} {ports : Fin m→Edge} {next : Fin m→Fin m} {side : Fin m→Bool}

theorem mem (hp : SphericalPortProfile g ports next side) (i : Fin m) : ports i∈g := by
  obtain ⟨G,hG,hs,p,hi,he,hn,hside⟩ := hp
  exact List.mem_of_getElem? (he i)

theorem perm (hp:SphericalPortProfile g ports next side) (hperm:g.Perm h) :
    SphericalPortProfile h ports next side := by
  obtain ⟨e⟩ := IndexEquiv.of_perm hperm
  obtain ⟨G,hG,hs,p,hi,he,hn,hside⟩ := hp
  refine ⟨e.graphDarts.darts.hypermap G,PlanarOperations.Ports.embedding_transport e.graphDarts hG,
    e.graphDarts.darts.spherical G hs,fun i=>e.graphDarts.darts.toFun (p i),?_,?_,?_,?_⟩
  · intro i j hij
    exact hi i j (e.graphDarts.darts.injective hij)
  · intro i
    change h[(liftDart e.indices.toFun (p i)).val/2]?=some (ports i)
    have hd:=congrArg Fin.val (edgeIndex_liftDart e.indices.toFun (p i))
    change (liftDart e.indices.toFun (p i)).val/2=(e.indices.toFun (edgeIndex (p i))).val at hd
    rw [hd,e.values]
    exact he i
  · intro i
    exact (hn i).conjugate e.graphDarts.darts
  · intro i
    change (!(Nat.beq ((liftDart e.indices.toFun (p i)).val%2) 0))=side i
    rw [liftDart_mod]
    exact hside i

end SphericalPortProfile

namespace ProfileSubdivision
open PlanarOperations.Subdivision PlanarOperations.Ports

theorem subdivide (es ts : Graph) (c : Nat→Nat)
    (hc : ∀u,u<ts.length→∀v,v<ts.length→c u=c v→u=v)
    (hfresh : ∀e∈es++ts,∀u,u<ts.length→e.1≠c u ∧ e.2≠c u)
    {m : Nat} {ports : Fin m→Edge} {next : Fin m→Fin m} {side : Fin m→Bool}
    (hnop : ∀i,ports i∉ts) (hp:SphericalPortProfile (es++ts) ports next side) :
    SphericalPortProfile (es++splitEdges ts c) ports next side := by
  obtain ⟨G,hG,hs,p,hi,he,hnext,hside⟩ := hp
  have hn:2*(es++ts).length=2*es.length+2*ts.length:=by simp only [List.length_append];omega
  have hN:2*(es++splitEdges ts c).length=2*es.length+4*ts.length:=by
    simp only [List.length_append,splitEdges_length];omega
  have hA:(2*es.length)%2=0:=by omega
  have hlow : ∀i,(p i).val<2*es.length := by
    intro i
    apply Classical.byContradiction
    intro hge
    have hh:=he i
    rw [List.getElem?_append_right (by omega)] at hh
    exact hnop i (List.mem_of_getElem? hh)
  have hval : ∀i,(iotaF hn hN (p i)).val=(p i).val := by
    intro i
    change iota (2*es.length) (p i).val=(p i).val
    rw [iota,ite_eq_left (hlow i)]
  refine ⟨splitMap c G,embedding_subdivide es ts c hc hfresh hG,
    splitMap_spherical c G hG.1 hs,fun i=>iotaF hn hN (p i),?_,?_,?_,?_⟩
  · intro i j hij
    exact hi i j (iotaF_injective hn hN hij)
  · intro i
    rw [hval,List.getElem?_append_left (by have:=hlow i;omega)]
    have hh:=he i
    rw [List.getElem?_append_left (by have:=hlow i;omega)] at hh
    exact hh
  · intro i
    exact nextSelected_subdivide G hn hN hA hG.1 (hnext i)
  · intro i
    change (!(Nat.beq ((iotaF hn hN (p i)).val%2) 0))=side i
    rw [hval]
    exact hside i

end ProfileSubdivision
end STACS2027.PlanarAssembly
