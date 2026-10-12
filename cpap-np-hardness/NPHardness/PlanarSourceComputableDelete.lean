module

public import NPHardness.PlanarSourceComputableFormula
public import NPHardness.PlanarPreprocessDeletionClosure

/-! Executable deletion of trailing edges from an actual registered graph
embedding. This retains the chosen rotation as data throughout; no existential
planarity certificate is eliminated by classical choice. -/

@[expose] public section
namespace STACS2027.PlanarSource.ComputableComb
open Complexity Complexity.SAT Complexity.Planar
open STACS2027.PlanarPreprocess STACS2027.PlanarPreprocess.Deletion STACS2027.PlanarGluing

/-- Reindexing preserves the numeric dart labels, making the computation of
successors explicit across the edge-list length identity. -/
def finalEdgeCast {V : Type} (es : List (V×V)) (e : V×V) :
    DartEquiv (2*(es++[e]).length) (2*es.length+2) :=
  DartEquiv.cast (by simp; omega)

theorem finalEdgeCast_nodes {V : Type} (es : List (V×V)) (e : V×V)
    (H : GraphEmbedding (es++[e])) (d d' : Fin (2*es.length+2)) :
    Reaches ((finalEdgeCast es e).hypermap H.map).node d d' ↔
      halfEdgeEnd (es++[e]) d.val=halfEdgeEnd (es++[e]) d'.val := by
  let E := finalEdgeCast es e
  have hc : Reaches (E.hypermap H.map).node d d' ↔
      Reaches H.map.node (E.invFun d) (E.invFun d') := by
    constructor
    · rintro ⟨k,hk⟩
      change iterate (E.conjugate H.map.node) k d=d' at hk
      rw [E.iterate_conjugate] at hk
      exact ⟨k,by
        have h := congrArg E.invFun hk
        simpa only [E.left_inv] using h⟩
    · rintro ⟨k,hk⟩
      exact ⟨k,by
        change iterate (E.conjugate H.map.node) k d=d'
        rw [E.iterate_conjugate,hk,E.right_inv]⟩
  rw [hc]
  exact H.node_orbit (E.invFun d) (E.invFun d')

/-- Remove the final stored edge using the checked cut-and-excise map. -/
def GraphEmbedding.dropLast {V : Type} (es : List (V×V)) (e : V×V)
    (H : GraphEmbedding (es++[e])) : GraphEmbedding es := by
  let G := (finalEdgeCast es e).hypermap H.map
  have he : ∀ d, (G.edge d).val=Complexity.Planar.ed d.val :=
    fun d => H.edge_pair ((finalEdgeCast es e).invFun d)
  refine ⟨cutThenShrink G (graphEdge_last_pair G he).1 (graphEdge_last_pair G he).2,
    cutThenShrink_graphEdge G he,?_,?_⟩
  · exact cutThenShrink_graphNodes es e G he (finalEdgeCast_nodes es e H)
  · exact cutThenShrink_planar G _ _ ((finalEdgeCast es e).planar H.map H.planar)

/-- Transport along an edge-list equality with explicit unchanged numeric
labels, avoiding an opaque cast of the entire embedding record. -/
def GraphEmbedding.reindex {V : Type} {es ts : List (V×V)}
    (H : GraphEmbedding es) (h : es=ts) : GraphEmbedding ts := by
  let E : DartEquiv (2*es.length) (2*ts.length) := DartEquiv.cast (congrArg (fun g => 2*g.length) h)
  refine ⟨E.hypermap H.map,fun d => H.edge_pair (E.invFun d),?_,E.planar H.map H.planar⟩
  intro d d'
  have hc : Reaches (E.hypermap H.map).node d d' ↔
      Reaches H.map.node (E.invFun d) (E.invFun d') := by
    constructor
    · rintro ⟨k,hk⟩
      change iterate (E.conjugate H.map.node) k d=d' at hk
      rw [E.iterate_conjugate] at hk
      exact ⟨k,by
        have he := congrArg E.invFun hk
        simpa only [E.left_inv] using he⟩
    · rintro ⟨k,hk⟩
      exact ⟨k,by
        change iterate (E.conjugate H.map.node) k d=d'
        rw [E.iterate_conjugate,hk,E.right_inv]⟩
  apply hc.trans
  change Reaches H.map.node (E.invFun d) (E.invFun d') ↔ _
  have ho := H.node_orbit (E.invFun d) (E.invFun d')
  change Reaches H.map.node (E.invFun d) (E.invFun d') ↔
    halfEdgeEnd es d.val=halfEdgeEnd es d'.val at ho
  simpa only [h] using ho

/-- Successively delete an explicitly listed suffix. -/
def GraphEmbedding.prefix {V : Type} (es ts : List (V×V))
    (G : GraphEmbedding (es++ts)) : GraphEmbedding es :=
  match ts with
  | [] => G.reindex (List.append_nil es)
  | e :: ts => GraphEmbedding.dropLast es e
      (GraphEmbedding.prefix (es++[e]) ts (G.reindex (by
        simp only [List.append_assoc,List.singleton_append])))
termination_by structural ts

/-- The incidence-only grid embedding is an executable restriction of the
registered comb embedding with its spine. -/
def gridIncidenceEmbedding (W m : Nat) (bits : Nat → Nat → Bool×Bool) (hm : 1 ≤ m) :
    GraphEmbedding (incidenceGraph (Grid.gridCNF W m bits)) :=
  (gridEmbedding W m bits hm).prefix _ _

/-- A concrete bounded planar formula from the registered grid. -/
def gridRingOutput (W m : Nat) (bits : Nat → Nat → Bool×Bool) (hm : 1 ≤ m) : CNF :=
  ComputableFormula.output (Grid.gridCNF W m bits) (gridIncidenceEmbedding W m bits hm)

theorem gridRingOutput_correct (W m : Nat) (bits : Nat → Nat → Bool×Bool) (hm : 1 ≤ m) :
    BoundedOccurrence (gridRingOutput W m bits hm) ∧
    PlanarGraph (incidenceGraph (gridRingOutput W m bits hm)) ∧
    (Satisfiable (gridRingOutput W m bits hm) ↔ Satisfiable (Grid.gridCNF W m bits)) := by
  apply ComputableFormula.output_correct
  intro c hc
  have h2 := (Grid.grid_clause_ok hc).1
  rw [Comb.svars_length] at h2
  have h3 := Grid.grid_threeCNF W m bits c hc
  omega

end STACS2027.PlanarSource.ComputableComb
