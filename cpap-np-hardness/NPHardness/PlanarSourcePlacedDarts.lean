module

public import NPHardness.PlanarSourcePlacedPorts
public import NPHardness.PlanarSourceRingEmbedding
public import NPHardness.PlanarAssemblySourcePorts

/-! The explicit ring-source rotation on the exact allocated occurrence darts
used by gadget assembly. Casts preserve arithmetic dart values. -/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar PlanarGluing PlanarAssembly
open Embedding Embedding.BipartiteRotation

def placedRingDarts (f : CNF) (next : Nat→Nat) (signs : Nat→Bool) :
    DartEquiv (6*f.flatten.length) (2*(placeFormula [] (ringFormula f next signs)).flatten.length) :=
  (ringFormulaDarts f next signs).trans (DartEquiv.cast (by rw [placed_occurrence_count]))

theorem placedRingDarts_val (f : CNF) (next : Nat→Nat) (signs : Nat→Bool)
    (d : Fin (6*f.flatten.length)) :
    ((placedRingDarts f next signs).toFun d).val=((ringDarts f.flatten.length).toFun d).val := rfl

def placedRingMap (f : CNF) (B : BipartiteRotation f.flatten.length) (signs : Nat→Bool) :
    Hypermap (2*(placeFormula [] (ringFormula f (nextIndex B) signs)).flatten.length) :=
  (placedRingDarts f (nextIndex B) signs).hypermap B.expanded

theorem placedRingMap_predecessor (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat→Bool) (d : Fin (6*f.flatten.length)) :
    (placedRingMap f B signs).face ((placedRingMap f B signs).edge
      ((placedRingDarts f (nextIndex B) signs).toFun d))=
      (placedRingDarts f (nextIndex B) signs).toFun (B.expanded.face (B.expanded.edge d)) := by
  change (placedRingDarts f (nextIndex B) signs).conjugate B.expanded.face
    ((placedRingDarts f (nextIndex B) signs).conjugate B.expanded.edge
      ((placedRingDarts f (nextIndex B) signs).toFun d))=_
  rw [DartEquiv.conjugate_toFun,DartEquiv.conjugate_toFun]

theorem placedRingMap_edge (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat→Bool) (d : Fin (2*(placeFormula [] (ringFormula f (nextIndex B) signs)).flatten.length)) :
    ((placedRingMap f B signs).edge d).val=ed d.val := by
  let e:=placedRingDarts f (nextIndex B) signs
  have h : ∀x,(e.toFun (B.expanded.edge x)).val=ed (e.toFun x).val:=fun x=>ringDarts_edge B x
  change (e.toFun (B.expanded.edge (e.invFun d))).val=ed d.val
  rw [h,e.right_inv]

theorem placedRingMap_nodes (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat→Bool) (clause : Fin f.flatten.length→Fin f.length)
    (hc : ∀i:Fin f.flatten.length,
      ((incidenceGraph f)[i.val]'(by rw [incidenceGraph_length_flatten];exact i.isLt)).2=Sum.inr (clause i).val)
    (horbit : ∀i j,Reaches B.clause.toFun i j ↔ clause i=clause j)
    (d d' : Fin (2*(placeFormula [] (ringFormula f (nextIndex B) signs)).flatten.length)) :
    Reaches (placedRingMap f B signs).node d d' ↔
      halfEdgeEnd (incidenceGraph (ringFormula f (nextIndex B) signs)) d.val=
      halfEdgeEnd (incidenceGraph (ringFormula f (nextIndex B) signs)) d'.val := by
  let e:=placedRingDarts f (nextIndex B) signs
  have hr : Reaches (placedRingMap f B signs).node d d' ↔
      Reaches B.expanded.node (e.invFun d) (e.invFun d') := by
    constructor
    · rintro ⟨k,hk⟩
      change iterate (e.conjugate B.expanded.node) k d=d' at hk
      rw [e.iterate_conjugate] at hk
      refine ⟨k,?_⟩
      have he:=congrArg e.invFun hk
      simpa only [e.left_inv] using he
    · rintro ⟨k,hk⟩
      refine ⟨k,?_⟩
      change iterate (e.conjugate B.expanded.node) k d=d'
      rw [e.iterate_conjugate,hk,e.right_inv]
  rw [hr,B.expanded_node_orbit clause horbit]
  have hd:=ringFormulaDarts_ends f B signs clause hc (e.invFun d)
  have hd':=ringFormulaDarts_ends f B signs clause hc (e.invFun d')
  change halfEdgeEnd (incidenceGraph (ringFormula f (nextIndex B) signs)) (e.toFun (e.invFun d)).val=_ at hd
  change halfEdgeEnd (incidenceGraph (ringFormula f (nextIndex B) signs)) (e.toFun (e.invFun d')).val=_ at hd'
  rw [e.right_inv] at hd hd'
  rw [hd,hd',Option.some.injEq]
  exact ⟨congrArg encodeExpanded,encodeExpanded_injective _ _⟩

theorem placedRingMap_planar (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat→Bool) (hp:B.original.Planar) : (placedRingMap f B signs).Planar :=
  (placedRingDarts f (nextIndex B) signs).planar B.expanded (B.expanded_planar hp)

end STACS2027.PlanarSource.Formula
