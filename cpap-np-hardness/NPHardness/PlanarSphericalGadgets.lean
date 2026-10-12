module

public import NPHardness.PlanarGluingSpherical
public import NPHardness.PlanarOperationsPortsGadgets
import Lean.Elab.Tactic.Omega

/-!
The Figure 4 embeddings retain both a genuine common face and the strict
spherical Euler inequality through every subdivision. The two properties
refer to the same explicit hypermap, so their witnesses can be used together
in a subsequent assembly proof.
-/

@[expose] public section
namespace STACS2027
open Complexity Complexity.Planar PlanarGluing

def HasSphericalCofacialPorts {V : Type} (es ports : List (V × V)) : Prop :=
  ∃ G : Hypermap (2 * es.length), IsGraphEmbedding es G ∧
    2 * G.componentCount + 2 * es.length ≤ G.eulerRhs ∧
    ∃ root : Fin (2 * es.length), ∀ e ∈ ports, ∃ d : Fin (2 * es.length), ∃ k,
      iterate G.face k root = d ∧ es[d.val / 2]? = some e

theorem HasSphericalCofacialPorts.cofacial {V : Type} {es ports : List (V × V)}
    (h : HasSphericalCofacialPorts es ports) : HasCofacialPorts es ports := by
  obtain ⟨G, hG, _, hports⟩ := h
  exact ⟨G, hG, hports⟩

theorem HasSphericalCofacialPorts.mem {V : Type} {es ports : List (V × V)}
    (h : HasSphericalCofacialPorts es ports) {e : V × V} (he : e ∈ ports) : e ∈ es :=
  h.cofacial.mem he

theorem HasSphericalCofacialPorts.perm {V : Type} {es ts ports : List (V × V)}
    (h : HasSphericalCofacialPorts es ports) (hp : es.Perm ts) :
    HasSphericalCofacialPorts ts ports := by
  obtain ⟨e⟩ := IndexEquiv.of_perm hp
  obtain ⟨G, hG, hEuler, r, hc⟩ := h
  refine ⟨e.graphDarts.darts.hypermap G, PlanarOperations.Ports.embedding_transport e.graphDarts hG,
    e.graphDarts.darts.spherical G hEuler, e.graphDarts.darts.toFun r, ?_⟩
  intro p hp
  obtain ⟨d, k, hk, hd⟩ := hc p hp
  refine ⟨e.graphDarts.darts.toFun d, k, ?_, ?_⟩
  · change iterate (e.graphDarts.darts.conjugate G.face) k (e.graphDarts.darts.toFun r) = _
    rw [e.graphDarts.darts.iterate_conjugate, e.graphDarts.darts.left_inv, hk]
  · change ts[(liftDart e.indices.toFun d).val / 2]? = some p
    have he := congrArg Fin.val (edgeIndex_liftDart e.indices.toFun d)
    change (liftDart e.indices.toFun d).val / 2 = (e.indices.toFun (edgeIndex d)).val at he
    rw [he, e.values (edgeIndex d)]
    exact hd

namespace PlanarOperations.Ports
open Subdivision

theorem splitMap_spherical {V : Type} {es ts : List (V × V)} (c : Nat → V)
    (G : Hypermap (2 * (es ++ ts).length))
    (hedge : IsGraphEdge G.edge)
    (hEuler : 2 * G.componentCount + 2 * (es ++ ts).length ≤ G.eulerRhs) :
    2 * (splitMap c G).componentCount + 2 * (es ++ splitEdges ts c).length ≤
      (splitMap c G).eulerRhs := by
  have hn : 2 * (es ++ ts).length = 2 * es.length + 2 * ts.length := by
    simp only [List.length_append]; omega
  have hN : 2 * (es ++ splitEdges ts c).length = 2 * es.length + 4 * ts.length := by
    simp only [List.length_append, splitEdges_length]; omega
  have hA : (2 * es.length) % 2 = 0 := by omega
  have hE := cycleCount_graphEdge_le hedge
  have hE' := cycleCount_graphEdge_ge (graphEdge_new G hn hN hA)
  have hV := nodes_ge G hn hN hA
  have hF := faces_ge G hn hN hA hedge
  have hC := components_le G hn hN hA hedge
  change 2 * (G' G hn hN hA).componentCount + 2 * (es ++ splitEdges ts c).length ≤
    (G' G hn hN hA).eulerRhs
  unfold Hypermap.eulerRhs at hEuler ⊢
  omega

theorem spherical_cofacial_subdivide {V : Type} (es ts ports : List (V × V)) (c : Nat → V)
    (hc : ∀ u, u < ts.length → ∀ u', u' < ts.length → c u = c u' → u = u')
    (hfresh : ∀ e ∈ es ++ ts, ∀ u, u < ts.length → e.1 ≠ c u ∧ e.2 ≠ c u)
    (hnop : ∀ e ∈ ports, e ∉ ts) (h : HasSphericalCofacialPorts (es ++ ts) ports) :
    HasSphericalCofacialPorts (es ++ splitEdges ts c) ports := by
  obtain ⟨G, hG, hEuler, r, hports⟩ := h
  have hn : 2 * (es ++ ts).length = 2 * es.length + 2 * ts.length := by
    simp only [List.length_append]; omega
  have hN : 2 * (es ++ splitEdges ts c).length = 2 * es.length + 4 * ts.length := by
    simp only [List.length_append, splitEdges_length]; omega
  have hA : (2 * es.length) % 2 = 0 := by omega
  refine ⟨splitMap c G, embedding_subdivide es ts c hc hfresh hG,
    splitMap_spherical c G hG.1 hEuler, iotaF hn hN r, ?_⟩
  intro e he
  obtain ⟨d, k, hk, hd⟩ := hports e he
  obtain ⟨k', _, _, hface⟩ := face_orbit_transfer G hn hN hA hG.1 k r
  refine ⟨iotaF hn hN d, k', ?_, ?_⟩
  · change iterate (G' G hn hN hA).face k' (iotaF hn hN r) = iotaF hn hN d
    rw [hface, hk]
  · have hlt : d.val < 2 * es.length := by
      apply Classical.byContradiction
      intro hge
      rw [List.getElem?_append_right (by omega)] at hd
      exact hnop e he (List.mem_of_getElem? hd)
    have hi : (iotaF hn hN d).val = d.val := by
      change iota (2 * es.length) d.val = d.val
      unfold iota; rw [ite_eq_left hlt]
    rw [hi, List.getElem?_append_left (by omega)]
    rw [List.getElem?_append_left (by omega)] at hd
    exact hd

end PlanarOperations.Ports

theorem sphericalCofacialPorts_of_tables (es ports : Graph) (t : EmbedTables) (h : EmbedOK t)
    (hlen : es.length = t.n2)
    (hends : ∀ d, d < 2 * t.n2 → halfEdgeEnd es d = some (t.EN d))
    (hEuler : 2 * t.cC (2 * t.n2) + t.n2 ≤ t.cR (2 * t.n2) + t.cF (2 * t.n2))
    (root : Fin (2 * t.n2))
    (hports : ∀ e ∈ ports, ∃ d : Fin (2 * t.n2), ∃ k,
      iterate t.F k root.val = d.val ∧ es[d.val / 2]? = some e) :
    HasSphericalCofacialPorts es ports := by
  unfold HasSphericalCofacialPorts IsGraphEmbedding
  rw [hlen]
  refine ⟨h.hypermap, ⟨fun _ => rfl, ?_, ?_⟩, tables_spherical h hEuler, root, ?_⟩
  · intro d d'
    rw [hends d.val d.isLt, hends d'.val d'.isLt]
    constructor
    · rintro ⟨k, hk⟩
      have := h.iterate_EN k d.isLt
      rw [← h.iterate_node k d, hk] at this
      rw [this]
    · intro hE
      obtain ⟨k, hk⟩ := h.orbit d.isLt d'.isLt (Option.some.inj hE)
      exact ⟨k, Fin.ext (by rw [h.iterate_node k d, hk])⟩
  · rw [planar_iff]
    have := tables_spherical h hEuler
    omega
  · intro e he
    obtain ⟨d, k, hk, hd⟩ := hports e he
    exact ⟨d, k, Fin.ext (by rw [h.iterate_face]; exact hk), hd⟩

/-- A nonport edge can be subdivided without changing the common-face property. -/
theorem spherical_subdivideOnce_bounded {g ports : Graph} {a b next : Nat}
    (hn : g.Nodup) (hb : VerticesBelow g next) (he : edge a b ∈ g)
    (hne : edge a b ∉ ports) (hp : HasSphericalCofacialPorts g ports) :
    HasSphericalCofacialPorts (subdivideOnce g a b next) ports := by
  let es := g.filter (· != edge a b)
  have hperm : g.Perm (es ++ [edge a b]) := by
    have h : g.Perm (edge a b :: es) := by
      simpa only [hn.erase_eq_filter] using List.perm_cons_erase he
    exact h.trans (List.perm_append_comm (l₁ := [edge a b]) (l₂ := es))
  have hsub := PlanarOperations.Ports.spherical_cofacial_subdivide es [edge a b] ports (fun _ => next)
    (by intro u hu v hv _; simp only [List.length_singleton] at hu hv; omega)
    (by
      intro e he' u _
      have hm : e ∈ g := hperm.mem_iff.mpr he'
      exact ⟨Nat.ne_of_lt (hb e hm).1,Nat.ne_of_lt (hb e hm).2⟩)
    (by intro e hep hem; have heq : e = edge a b := by simpa using hem
        subst e; exact hne hep) (hp.perm hperm)
  have hab := (edge_below a b next).mp (hb _ he)
  have ht := (splitEdges_singleton_perm a b next hab.1 hab.2).append_left es
  have hq : (es ++ [edge a next,edge next b]).Perm (subdivideOnce g a b next) :=
    List.perm_append_comm
  exact hsub.perm (ht.trans hq)

/-- Repeated subdivision of a nonport edge preserves the common face. -/
theorem spherical_chainSteps {g ports : Graph} (a b next s : Nat)
    (hg : VerticesBelow g next) (hn : g.Nodup) (hab : a ≠ b)
    (he : edge a b ∈ g) (hs : s=0 ∨ edge a b ∉ ports)
    (hp : HasSphericalCofacialPorts g ports) :
    HasSphericalCofacialPorts (subdivisionGraph g (chainSteps a b next s)) ports := by
  induction s generalizing g a next with
  | zero => exact hp
  | succ s ih =>
    have hne : edge a b ∉ ports := hs.resolve_left (by omega)
    have hv := (edge_below a b next).mp (hg _ he)
    have hnew : edge next b ∉ ports := fun hm => hg.fresh.edge_right_absent b (hp.mem hm)
    exact ih next (next+1) (subdivideOnce_below hg hv.1 hv.2)
      (subdivideOnce_nodup hn hab he hg.fresh) (by omega)
      (mem_subdivideOnce.mpr (Or.inr (Or.inl rfl))) (Or.inr hnew)
      (spherical_subdivideOnce_bounded hn hg he hne hp)

/-- Ports whose subdivision count is zero retain their common face through the
entire straight-chain program. -/
theorem spherical_linkSteps {g ports : Graph} (next : Nat) (ls : List Link)
    (hg : VerticesBelow g next) (hgn : g.Nodup) (hn : (linkEdges ls).Nodup)
    (hl : ∀ l ∈ ls, l.source ≠ l.target ∧ edge l.source l.target ∈ g)
    (hz : ∀ l ∈ ls, edge l.source l.target ∈ ports → l.subdivisions=0)
    (hp : HasSphericalCofacialPorts g ports) :
    HasSphericalCofacialPorts (subdivisionGraph g (linkSteps next ls)) ports := by
  induction ls generalizing g next with
  | nil => exact hp
  | cons l ls ih =>
    obtain ⟨he,ht⟩ := List.nodup_cons.mp hn
    obtain ⟨hne,hmem⟩ := hl l (by simp)
    have hb := (edge_below l.source l.target next).mp (hg _ hmem)
    have hzero : l.subdivisions=0 ∨ edge l.source l.target ∉ ports := by
      by_cases hm : edge l.source l.target ∈ ports
      · exact Or.inl (hz l (by simp) hm)
      · exact Or.inr hm
    rw [linkSteps,subdivisionGraph_append]
    apply ih _ (chainSteps_below _ _ _ _ hg hb.1 hb.2)
      (subdivisionGraph_nodup _ _ hgn (chainSteps_valid _ _ _ _ hg hne hmem)) ht
    · intro r hr
      obtain ⟨hrne,hrmem⟩ := hl r (by simp [hr])
      refine ⟨hrne,chainSteps_retains _ _ _ _ hg hne hmem _ hrmem ?_⟩
      intro heq
      apply he
      exact List.mem_map.mpr ⟨r,hr,heq⟩
    · intro r hr; exact hz r (by simp [hr])
    · exact spherical_chainSteps _ _ _ _ hg hgn hne hmem hzero hp

/-- The actual realized graph has a registered planar embedding with the same
untouched ports on one common face. -/
theorem spherical_realizeLinks (next : Nat) (ls : List Link) (ports : Graph)
    (hb : VerticesBelow (linkEdges ls) next) (hn : (linkEdges ls).Nodup)
    (hp : ∀ l ∈ ls, l.source ≠ l.target)
    (hz : ∀ l ∈ ls, edge l.source l.target ∈ ports → l.subdivisions=0)
    (hports : HasSphericalCofacialPorts (linkEdges ls) ports) : HasSphericalCofacialPorts (realizeLinks next ls) ports := by
  have hs := spherical_linkSteps next ls hb hn hn
    (fun l hl => ⟨hp l hl,List.mem_map.mpr ⟨l,hl,rfl⟩⟩) hz hports
  exact hs.perm (realizeLinks_perm_subdivisionGraph next ls hb hn hp).symm

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem variable_skeleton_sphericalPorts : HasSphericalCofacialPorts variableSkeleton variablePorts := by
  apply sphericalCofacialPorts_of_tables _ _ variableEmbedding variableEmbedding_valid rfl
    variableEmbedding_ends (by decide) ⟨1, by decide⟩
  intro e he
  obtain ⟨d, i, hi, hd⟩ := variable_skeleton_ports_cofacial e he
  exact ⟨d, i.val, hi, hd⟩

theorem clauseThree_skeleton_sphericalPorts : HasSphericalCofacialPorts clauseThree5 clausePorts := by
  apply sphericalCofacialPorts_of_tables _ _ clauseThreeEmbedding clauseThreeEmbedding_valid rfl
    clauseThreeEmbedding_ends (by decide) ⟨1, by decide⟩
  intro e he
  obtain ⟨d, i, hi, hd⟩ := clauseThree_skeleton_ports_cofacial e he
  exact ⟨d, i.val, hi, hd⟩

theorem clauseTwo_skeleton_sphericalPorts :
    HasSphericalCofacialPorts clauseTwoSkeleton (clausePorts.take 2) := by
  apply sphericalCofacialPorts_of_tables _ _ clauseTwoEmbedding clauseTwoEmbedding_valid rfl
    clauseTwoEmbedding_ends (by decide) ⟨1, by decide⟩
  intro e he
  obtain ⟨d, i, hi, hd⟩ := clauseTwo_skeleton_ports_cofacial e he
  exact ⟨d, i.val, hi, hd⟩

/-- The actual variable gadget has one witness for strict Euler and its common port face. -/
theorem variableGraph_sphericalPorts (k : Nat) :
    HasSphericalCofacialPorts (variableGraph k) variablePorts := by
  obtain ⟨hb, hn, hp⟩ := variable_links_wellformed k
  exact spherical_realizeLinks _ _ _ hb hn hp (variableLinks_ports_unsubdivided k)
    variable_skeleton_sphericalPorts

/-- The actual three-clause gadget has one spherical, cofacial witness. -/
theorem clauseThreeGraph_sphericalPorts (k : Nat) :
    HasSphericalCofacialPorts (clauseThreeGraph k) clausePorts := by
  obtain ⟨hb, hn, hp⟩ := clauseThree_links_wellformed k
  exact spherical_realizeLinks _ _ _ hb hn hp (clauseThreeLinks_ports_unsubdivided k)
    clauseThree_skeleton_sphericalPorts

/-- The actual two-clause gadget has one spherical, cofacial witness. -/
theorem clauseTwoGraph_sphericalPorts (k : Nat) :
    HasSphericalCofacialPorts (clauseTwoGraph k) (clausePorts.take 2) := by
  obtain ⟨hb, hn, hp⟩ := clauseTwo_links_wellformed k
  exact spherical_realizeLinks _ _ _ hb hn hp (clauseTwoLinks_ports_unsubdivided k)
    clauseTwo_skeleton_sphericalPorts

end STACS2027
