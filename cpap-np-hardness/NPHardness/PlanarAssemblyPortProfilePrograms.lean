module

public import NPHardness.PlanarAssemblyPortProfileTransport

/-! Exact ordered and directed boundary profiles through the concrete
straight-chain subdivision programs used by all Figure 4 gadgets. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar
namespace SphericalPortProfile
variable {m : Nat} {ports : Fin m→Edge} {nextPort : Fin m→Fin m} {side : Fin m→Bool}

theorem subdivideOnce_bounded {g : Graph} {a b next : Nat}
    (hn:g.Nodup) (hb:VerticesBelow g next) (he:edge a b∈g)
    (hne:∀i,edge a b≠ports i) (hp:SphericalPortProfile g ports nextPort side) :
    SphericalPortProfile (subdivideOnce g a b next) ports nextPort side := by
  let es:=g.filter (·!=edge a b)
  have hperm:g.Perm (es++[edge a b]) := by
    have h:g.Perm (edge a b::es) := by simpa only [hn.erase_eq_filter] using List.perm_cons_erase he
    exact h.trans (List.perm_append_comm (l₁:=[edge a b]) (l₂:=es))
  have hsub:=ProfileSubdivision.subdivide es [edge a b] (fun _=>next)
    (by intro u hu v hv _;simp only [List.length_singleton] at hu hv;omega)
    (by
      intro e he' u _
      have hm:e∈g:=hperm.mem_iff.mpr he'
      exact ⟨Nat.ne_of_lt (hb e hm).1,Nat.ne_of_lt (hb e hm).2⟩)
    (by intro i hi;have he:ports i=edge a b:=by simpa using hi
        exact hne i he.symm) (hp.perm hperm)
  have hab:=(edge_below a b next).mp (hb _ he)
  have ht:=(splitEdges_singleton_perm a b next hab.1 hab.2).append_left es
  have hq:(es++[edge a next,edge next b]).Perm (subdivideOnce g a b next):=List.perm_append_comm
  exact hsub.perm (ht.trans hq)

theorem chainSteps {g : Graph} (a b next s : Nat)
    (hg:VerticesBelow g next) (hn:g.Nodup) (hab:a≠b) (he:edge a b∈g)
    (hs:s=0 ∨ ∀i,edge a b≠ports i) (hp:SphericalPortProfile g ports nextPort side) :
    SphericalPortProfile (subdivisionGraph g (chainSteps a b next s)) ports nextPort side := by
  induction s generalizing g a next with
  | zero => exact hp
  | succ s ih =>
    have hne:∀i,edge a b≠ports i:=hs.resolve_left (by omega)
    have hv:=(edge_below a b next).mp (hg _ he)
    have hnew:∀i,edge next b≠ports i:=by
      intro i hi
      exact hg.fresh.edge_right_absent b (hi.symm ▸ hp.mem i)
    exact ih next (next+1) (subdivideOnce_below hg hv.1 hv.2)
      (subdivideOnce_nodup hn hab he hg.fresh) (by omega)
      (mem_subdivideOnce.mpr (Or.inr (Or.inl rfl))) (Or.inr hnew)
      (subdivideOnce_bounded hn hg he hne hp)

theorem linkSteps {g : Graph} (next : Nat) (ls:List Link)
    (hg:VerticesBelow g next) (hgn:g.Nodup) (hn:(linkEdges ls).Nodup)
    (hl:∀l∈ls,l.source≠l.target ∧ edge l.source l.target∈g)
    (hz:∀l∈ls,∀i,edge l.source l.target=ports i→l.subdivisions=0)
    (hp:SphericalPortProfile g ports nextPort side) :
    SphericalPortProfile (subdivisionGraph g (STACS2027.linkSteps next ls)) ports nextPort side := by
  induction ls generalizing g next with
  | nil => exact hp
  | cons l ls ih =>
    obtain ⟨he,ht⟩:=List.nodup_cons.mp hn
    obtain ⟨hne,hmem⟩:=hl l (by simp)
    have hb:=(edge_below l.source l.target next).mp (hg _ hmem)
    have hzero:l.subdivisions=0 ∨ ∀i,edge l.source l.target≠ports i:=by
      by_cases hs:l.subdivisions=0
      · exact Or.inl hs
      · exact Or.inr (fun i hi=>hs (hz l (by simp) i hi))
    rw [STACS2027.linkSteps,subdivisionGraph_append]
    apply ih _ (chainSteps_below _ _ _ _ hg hb.1 hb.2)
      (subdivisionGraph_nodup _ _ hgn (chainSteps_valid _ _ _ _ hg hne hmem)) ht
    · intro r hr
      obtain ⟨hrne,hrmem⟩:=hl r (by simp [hr])
      refine ⟨hrne,chainSteps_retains _ _ _ _ hg hne hmem _ hrmem ?_⟩
      intro heq
      exact he (List.mem_map.mpr ⟨r,hr,heq⟩)
    · intro r hr;exact hz r (by simp [hr])
    · exact chainSteps _ _ _ _ hg hgn hne hmem hzero hp

theorem realizeLinks (next : Nat) (ls:List Link)
    (hb:VerticesBelow (linkEdges ls) next) (hn:(linkEdges ls).Nodup)
    (hp:∀l∈ls,l.source≠l.target)
    (hz:∀l∈ls,∀i,edge l.source l.target=ports i→l.subdivisions=0)
    (hports:SphericalPortProfile (linkEdges ls) ports nextPort side) :
    SphericalPortProfile (STACS2027.realizeLinks next ls) ports nextPort side := by
  have hs:=linkSteps next ls hb hn hn
    (fun l hl=>⟨hp l hl,List.mem_map.mpr ⟨l,hl,rfl⟩⟩) hz hports
  exact hs.perm (realizeLinks_perm_subdivisionGraph next ls hb hn hp).symm

end SphericalPortProfile

theorem variableGraph_port_profile (k:Nat) :
    SphericalPortProfile (variableGraph k) variablePortEdgeAt variablePortNext variablePortSide := by
  obtain ⟨hb,hn,hp⟩:=variable_links_wellformed k
  apply SphericalPortProfile.realizeLinks _ _ hb hn hp
  · intro l hl i hi
    apply variableLinks_ports_unsubdivided k l hl
    rw [hi]
    exact (by decide : ∀i:Fin 3,variablePortEdgeAt i∈variablePorts) i
  · exact variable_skeleton_port_profile

theorem clauseThreeGraph_port_profile (k:Nat) :
    SphericalPortProfile (clauseThreeGraph k) clauseThreePortEdgeAt clauseThreePortNext (fun _=>true) := by
  obtain ⟨hb,hn,hp⟩:=clauseThree_links_wellformed k
  apply SphericalPortProfile.realizeLinks _ _ hb hn hp
  · intro l hl i hi
    apply clauseThreeLinks_ports_unsubdivided k l hl
    rw [hi]
    exact (by decide : ∀i:Fin 3,clauseThreePortEdgeAt i∈clausePorts) i
  · exact clauseThree_skeleton_port_profile

theorem clauseTwoGraph_port_profile (k:Nat) :
    SphericalPortProfile (clauseTwoGraph k) clauseTwoPortEdgeAt clauseTwoPortNext (fun _=>true) := by
  obtain ⟨hb,hn,hp⟩:=clauseTwo_links_wellformed k
  apply SphericalPortProfile.realizeLinks _ _ hb hn hp
  · intro l hl i hi
    apply clauseTwoLinks_ports_unsubdivided k l hl
    rw [hi]
    exact (by decide : ∀i:Fin 2,clauseTwoPortEdgeAt i∈clausePorts.take 2) i
  · exact clauseTwo_skeleton_port_profile

end STACS2027.PlanarAssembly
