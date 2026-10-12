module

public import NPHardness.SubdivisionProjection

/-!
Compositional cycle projection and lifting for arbitrary finite sequences of
edge subdivisions. The resulting exact edge-length formula is the bridge to
the parameterized gadgets: it is not restricted to a finite range of k.
-/

@[expose] public section
namespace STACS2027

structure SubdivisionStep where
  source : Nat
  target : Nat
  fresh : Nat
deriving DecidableEq, Repr

def subdivisionGraph (g : Graph) : List SubdivisionStep → Graph
  | [] => g
  | s :: ss => subdivisionGraph (subdivideOnce g s.source s.target s.fresh) ss

def validSubdivision (g : Graph) : List SubdivisionStep → Prop
  | [] => True
  | s :: ss => s.source ≠ s.target ∧ edge s.source s.target ∈ g ∧
      FreshVertex g s.fresh ∧
      validSubdivision (subdivideOnce g s.source s.target s.fresh) ss

def expandedEdge : List SubdivisionStep → Edge → List Edge
  | [], e => [e]
  | s :: ss, e => (splitEdge s.source s.target s.fresh e).flatMap (expandedEdge ss)

theorem subdivision_cycle_projection (g : Graph) (ss : List SubdivisionStep)
    (hv : validSubdivision g ss) {k : Nat} {c : Cycle}
    (hc : IsCycle (subdivisionGraph g ss) k c) :
    ∃ l d, IsCycle g l d ∧ (cycleEdges c).Perm ((cycleEdges d).flatMap (expandedEdge ss)) := by
  induction ss generalizing g k c with
  | nil => exact ⟨k, c, hc, by simp [expandedEdge]⟩
  | cons s ss ih =>
    obtain ⟨hne, he, hf, ht⟩ := hv
    obtain ⟨l, d, hd, hp⟩ := ih _ ht hc
    obtain ⟨m, e, hec, heq⟩ := subdivideOnce_cycle_projection hne he hf hd
    refine ⟨m, e, hec, ?_⟩
    have hx := hp.trans (heq.flatMap_right (expandedEdge ss))
    simpa only [liftEdges, List.flatMap_assoc, expandedEdge] using hx

theorem subdivision_cycle_lift (g : Graph) (ss : List SubdivisionStep)
    (hv : validSubdivision g ss) {k : Nat} {c : Cycle} (hc : IsCycle g k c) :
    ∃ l d, IsCycle (subdivisionGraph g ss) l d ∧
      (cycleEdges d).Perm ((cycleEdges c).flatMap (expandedEdge ss)) := by
  induction ss generalizing g k c with
  | nil => exact ⟨k, c, hc, by simp [expandedEdge]⟩
  | cons s ss ih =>
    obtain ⟨_, _, hf, ht⟩ := hv
    obtain ⟨l, d, hd, hp⟩ := subdivideOnce_cycle_lift hc hf
    obtain ⟨m, e, he, heq⟩ := ih _ ht hd
    refine ⟨m, e, he, ?_⟩
    have hx := heq.trans (hp.flatMap_right (expandedEdge ss))
    simpa only [liftEdges, List.flatMap_assoc, expandedEdge] using hx

def expandedLength (ss : List SubdivisionStep) (c : Cycle) : Nat :=
  ((cycleEdges c).map fun e => (expandedEdge ss e).length).sum

end STACS2027
