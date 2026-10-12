module

public import NPHardness.PlanarOperationsGadgets

/-!
A registered planar embedding with designated edges incident to one actual
face orbit. This records darts and iterates of the face permutation, rather
than equality of certificate face labels. The root dart makes the witness
appropriate for nonempty embedded graphs such as the Figure 4 gadgets.
-/

@[expose] public section
namespace STACS2027
open Complexity Complexity.Planar

/-- A full witness of the registered graph embedding conditions. -/
def IsGraphEmbedding {V : Type} (es : List (V × V)) (G : Hypermap (2*es.length)) : Prop :=
  (∀ d, (G.edge d).val = cond (Nat.beq (d.val%2) 0) (d.val+1) (d.val-1)) ∧
  (∀ d d', (∃ k, iterate G.node k d = d') ↔ halfEdgeEnd es d.val = halfEdgeEnd es d'.val) ∧
  G.Planar

/-- Each designated edge has a dart on one common face of one registered planar
embedding. All edge multiplicities and actual face orbits are retained. -/
def HasCofacialPorts {V : Type} (es ports : List (V × V)) : Prop :=
  ∃ G : Hypermap (2*es.length), IsGraphEmbedding es G ∧
    ∃ root : Fin (2*es.length), ∀ e ∈ ports, ∃ d : Fin (2*es.length), ∃ k,
      iterate G.face k root = d ∧ es[d.val/2]? = some e

theorem HasCofacialPorts.mem {V : Type} {es ports : List (V × V)}
    (h : HasCofacialPorts es ports) {e : V×V} (he : e ∈ ports) : e ∈ es := by
  obtain ⟨_,_,_,hc⟩ := h
  obtain ⟨_,_,_,hd⟩ := hc e he
  exact List.mem_of_getElem? hd

namespace PlanarOperations.Ports
open PlanarGluing

theorem embedding_transport {V : Type} {es ts : List (V × V)}
    (e : GraphDartEquiv es ts) {G : Hypermap (2*es.length)}
    (h : IsGraphEmbedding es G) : IsGraphEmbedding ts (e.darts.hypermap G) := by
  obtain ⟨hE,hN,hP⟩ := h
  have he : ∀ d, G.edge d = graphEdge d := fun d => Fin.ext (hE d)
  refine ⟨?_,?_,e.darts.planar G hP⟩
  · intro y
    change (e.darts.toFun (G.edge (e.darts.invFun y))).val = _
    rw [he,e.edge,e.darts.right_inv]
    rfl
  · intro y y'
    have hn : (∃ k, iterate (e.darts.conjugate G.node) k y = y') ↔
        ∃ k, iterate G.node k (e.darts.invFun y) = e.darts.invFun y' := by
      constructor
      · rintro ⟨k,hk⟩
        rw [e.darts.iterate_conjugate] at hk
        exact ⟨k,by have := congrArg e.darts.invFun hk; simpa only [e.darts.left_inv] using this⟩
      · rintro ⟨k,hk⟩
        exact ⟨k,by rw [e.darts.iterate_conjugate,hk,e.darts.right_inv]⟩
    change (∃ k, iterate (e.darts.conjugate G.node) k y = y') ↔ _
    rw [hn,hN]
    have hy := e.ends (e.darts.invFun y)
    have hy' := e.ends (e.darts.invFun y')
    rw [e.darts.right_inv] at hy hy'
    rw [← hy,← hy']

end PlanarOperations.Ports

end STACS2027
