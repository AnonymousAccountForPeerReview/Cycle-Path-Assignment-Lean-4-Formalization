module

public import Outerplanar.OuterplanarMinor

/-! Ordinary planarity is preserved by the checked edge-list deletion and contraction surgery. -/

@[expose] public section
namespace Complexity.PlanarGraph
open Complexity.Planar STACS2027 STACS2027.PlanarGluing STACS2027.PlanarPreprocess
open STACS2027.PlanarPreprocess.Deletion STACS2027.OuterplanarMinor

theorem perm {V : Type} {es ts : List (V×V)} (hp : es.Perm ts)
    (h : PlanarGraph es) : PlanarGraph ts := by
  obtain ⟨e⟩ := IndexEquiv.of_perm hp
  exact e.graphDarts.planar h

theorem dropLast {V : Type} {es : List (V×V)} {e : V×V}
    (h : PlanarGraph (es++[e])) : PlanarGraph es := by
  unfold PlanarGraph at h ⊢
  rw [List.length_append] at h
  simp only [List.length_cons,List.length_nil] at h
  obtain ⟨G,he,hn,hp⟩ := h
  change (∀d,(G.edge d).val=ed d.val) at he
  exact ⟨cutThenShrink G (graphEdge_last_pair G he).1 (graphEdge_last_pair G he).2,
    cutThenShrink_graphEdge G he,cutThenShrink_graphNodes es e G he hn,
    shrinkLast_planar _ _ (shrinkLast_planar _ _ (cut_planar G _ _ (penultimate_ne_last _) _ _ hp))⟩

theorem sublist_prefix {V : Type} {es ts : List (V×V)} (h : es.Sublist ts) :
    ∀pre : List (V×V),PlanarGraph (pre++ts) → PlanarGraph (pre++es) := by
  induction h with
  | slnil => intro pre hp;exact hp
  | @cons es ts e h ih =>
    intro pre hp
    have he : (pre++e::ts).Perm ((pre++ts)++[e]) := by
      simpa only [List.append_assoc,List.singleton_append] using
        (List.perm_append_comm (l₁:=[e]) (l₂:=ts)).append_left pre
    exact ih pre (dropLast (perm he hp))
  | @cons_cons es ts e h ih =>
    intro pre hp
    have he : PlanarGraph ((pre++[e])++ts) := by
      simpa only [List.append_assoc,List.singleton_append] using hp
    have ht := ih (pre++[e]) he
    simpa only [List.append_assoc,List.singleton_append] using ht

theorem sublist {V : Type} {es ts : List (V×V)}
    (h : es.Sublist ts) (hp : PlanarGraph ts) : PlanarGraph es := by
  simpa only [List.nil_append] using sublist_prefix h [] hp

theorem subperm {V : Type} {es ts : List (V×V)}
    (h : es.Subperm ts) (hp : PlanarGraph ts) : PlanarGraph es := by
  obtain ⟨l,hp',hs⟩ := h
  exact perm hp' (sublist hs hp)

theorem canonical {es : List (Nat×Nat)} (h : PlanarGraph es) :
    PlanarGraph (es.map fun e=>edge e.1 e.2) := by
  have he : (es.map fun e=>edge e.1 e.2)=es.map canonicalEdge := rfl
  rw [he,canonicalEdges_eq_flipEdges]
  exact (flipGraphDartEquiv es _).planar h

theorem map_injOn {V W : Type} {es : List (V×V)} (f : V→W)
    (hf : ∀a b,(∃e∈es,a=e.1 ∨ a=e.2) → (∃e∈es,b=e.1 ∨ b=e.2) →
      f a=f b → a=b) (h : PlanarGraph es) :
    PlanarGraph (es.map fun e=>(f e.1,f e.2)) := by
  have hi : ∀d d' : Fin (2*es.length),
      (halfEdgeEnd es d.val).map f=(halfEdgeEnd es d'.val).map f ↔
      halfEdgeEnd es d.val=halfEdgeEnd es d'.val := by
    intro d d'
    obtain ⟨v,hv,hve⟩ := halfEdgeEnd_isEnd es d.isLt
    obtain ⟨v',hv',hve'⟩ := halfEdgeEnd_isEnd es d'.isLt
    rw [hv,hv']
    simp only [Option.map_some,Option.some.injEq]
    exact ⟨hf v v' hve hve',congrArg f⟩
  unfold PlanarGraph at h ⊢
  simp only [STACS2027.halfEdgeEnd_relabel]
  rw [List.length_map]
  obtain ⟨G,hE,hN,hP⟩ := h
  exact ⟨G,hE,fun d d'=>(hN d d').trans (hi d d').symm,hP⟩

theorem contractLast {V : Type} [DecidableEq V] {es : List (V × V)}
    {u v : V} (huv : u ≠ v) (h : PlanarGraph (es ++ [(u, v)])) :
    PlanarGraph (es.map fun e => (renameTo u v e.1, renameTo u v e.2)) := by
  obtain ⟨hu, hv⟩ := halfEdgeEnd_last_pair es u v
  unfold PlanarGraph at h ⊢
  rw [List.length_append] at h
  simp only [List.length_cons, List.length_nil] at h
  obtain ⟨G, he, hn, hp⟩ := h
  change (∀ d, (G.edge d).val = ed d.val) at he
  rw [List.length_map]
  have hpair := graphEdge_last_pair G he
  -- the two ends of the last edge are different vertices
  have hsep : ¬ Reaches G.node (penultimate (2 * es.length)) (last (2 * es.length + 1)) := by
    intro hr
    have h' := (hn _ _).mp hr
    change halfEdgeEnd (es ++ [(u, v)]) (2 * es.length) =
      halfEdgeEnd (es ++ [(u, v)]) (2 * es.length + 1) at h'
    rw [hu, hv] at h'
    exact huv (Option.some.inj h')
  let φ : Fin (2 * es.length + 2) → Option V := fun z =>
    (halfEdgeEnd (es ++ [(u, v)]) z.val).map (renameTo u v)
  have hφ : ∀ z, φ (G.node z) = φ z := by
    intro z
    have := (hn z (G.node z)).mp ⟨1, rfl⟩
    simp only [φ]
    rw [← this]
  have hφab : φ (penultimate (2 * es.length)) = φ (last (2 * es.length + 1)) := by
    change (halfEdgeEnd (es ++ [(u, v)]) (2 * es.length)).map (renameTo u v) =
      (halfEdgeEnd (es ++ [(u, v)]) (2 * es.length + 1)).map (renameTo u v)
    rw [hu, hv]
    simp [renameTo]
  refine ⟨contractThenShrink G hpair.1 hpair.2, ?_, ?_,
    contractThenShrink_planar G _ _ hsep hp⟩
  · intro d
    have h := congrArg Fin.val (contractThenShrink_edge_lift G hpair.1 hpair.2 d)
    rw [he] at h
    exact h
  · intro d d'
    change Reaches _ d d' ↔ _
    rw [contractThenShrink_node_orbit, halfEdgeEnd_relabel, halfEdgeEnd_relabel]
    have hd : halfEdgeEnd es d.val = halfEdgeEnd (es ++ [(u, v)]) (embedPair d).val :=
      (halfEdgeEnd_append_left es [(u, v)] d.val d.isLt).symm
    have hd' : halfEdgeEnd es d'.val = halfEdgeEnd (es ++ [(u, v)]) (embedPair d').val :=
      (halfEdgeEnd_append_left es [(u, v)] d'.val d'.isLt).symm
    rw [hd, hd']
    change _ ↔ φ (embedPair d) = φ (embedPair d')
    constructor
    · rintro ⟨k, hk⟩
      rw [← hk]
      exact (iterate_invariant _ φ
        (contract_node_invariant G _ _ (penultimate_ne_last _) hpair.1 hpair.2 φ hφ hφab) k
        (embedPair d)).symm
    · intro heq
      exact contract_node_of_label G _ _ _ hpair.1 hpair.2
        (fun z => halfEdgeEnd (es ++ [(u, v)]) z.val) hn huv hu hv heq

theorem contract {V : Type} [DecidableEq V] {es : List (V×V)} {s t : V}
    (hst : s≠t) (hmem : (s,t)∈es) (h : PlanarGraph es) :
    PlanarGraph ((es.erase (s,t)).map fun e=>(renameTo s t e.1,renameTo s t e.2)) := by
  have hp : es.Perm (es.erase (s,t)++[(s,t)]) :=
    (List.perm_cons_erase hmem).trans (List.perm_append_singleton _ _).symm
  exact contractLast hst (perm hp h)

theorem simpleEdges {g : Graph} (hp : PlanarGraph g) : PlanarGraph (STACS2027.simpleEdges g) :=
  hp.subperm ((simpleEdges_nodup g).subperm (fun e he=>by
    exact (List.mem_filter.mp (List.mem_eraseDups.mp he)).1))

end Complexity.PlanarGraph
