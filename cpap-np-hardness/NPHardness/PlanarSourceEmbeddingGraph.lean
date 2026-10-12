module

public import NPHardness.PlanarSourceEmbeddingPlanar

/-! The concrete edge list represented by the incidence-ring expansion. -/

@[expose] public section
namespace STACS2027.PlanarSource.Embedding.BipartiteRotation
open Complexity Complexity.Planar STACS2027.PlanarGluing

abbrev ExpandedVertex (E : Nat) (C : Type) := Sum (Fin E) (Sum C (Fin E))

def expandedVertex {E : Nat} {C : Type} (B : BipartiteRotation E)
    (clauseLabel : Fin E → C) (d : Fin (6 * E)) : ExpandedVertex E C :=
  let i := index 6 (by decide) d
  match d.val % 6 with
  | 0 => .inl i
  | 1 => .inr (.inl (clauseLabel i))
  | 2 => .inl i
  | 3 => .inr (.inr i)
  | 4 => .inr (.inr i)
  | _ => .inl (B.varRot.toFun i)

def expandedEdges {E : Nat} {C : Type} (B : BipartiteRotation E)
    (clauseLabel : Fin E → C) : List (ExpandedVertex E C × ExpandedVertex E C) :=
  (List.finRange (3 * E)).map fun j =>
    (expandedVertex B clauseLabel ⟨2 * j.val, by have := j.isLt; omega⟩,
      expandedVertex B clauseLabel ⟨2 * j.val + 1, by have := j.isLt; omega⟩)

@[simp] theorem expandedEdges_length {E : Nat} {C : Type} (B : BipartiteRotation E)
    (clauseLabel : Fin E → C) : (expandedEdges B clauseLabel).length = 3 * E := by
  simp [expandedEdges]

theorem expandedEdges_end {E : Nat} {C : Type} (B : BipartiteRotation E)
    (clauseLabel : Fin E → C) (d : Fin (6 * E)) :
    halfEdgeEnd (expandedEdges B clauseLabel) d.val = some (expandedVertex B clauseLabel d) := by
  have hi : d.val / 2 < (List.finRange (3 * E)).length := by
    simp only [List.length_finRange]
    have := d.isLt
    omega
  simp only [halfEdgeEnd, expandedEdges, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, List.getElem_finRange]
  by_cases he : d.val % 2 = 0
  · have hd : (⟨2 * (d.val / 2), by have := d.isLt; omega⟩ : Fin (6 * E)) = d := by
      apply Fin.ext
      change 2 * (d.val / 2) = d.val
      omega
    simp [he, hd]
  · have hd : (⟨2 * (d.val / 2) + 1, by have := d.isLt; omega⟩ : Fin (6 * E)) = d := by
      apply Fin.ext
      change 2 * (d.val / 2) + 1 = d.val
      omega
    have hb : Nat.beq (d.val % 2) 0 = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact he (Nat.eq_of_beq_eq_true h)
    simp [hb, hd]

abbrev Anchor (E : Nat) := Sum (Fin E) (Sum (Fin E) (Fin E))

def anchor {E : Nat} (B : BipartiteRotation E) (d : Fin (6 * E)) : Anchor E :=
  let i := index 6 (by decide) d
  match d.val % 6 with
  | 0 => .inl i
  | 1 => .inr (.inl i)
  | 2 => .inl i
  | 3 => .inr (.inr i)
  | 4 => .inr (.inr i)
  | _ => .inl (B.varRot.toFun i)

def anchorDart {E : Nat} : Anchor E → Fin (6 * E)
  | .inl i => d6 i 0
  | .inr (.inl i) => d6 i 1
  | .inr (.inr i) => d6 i 3

def anchorVertex {E : Nat} {C : Type} (clauseLabel : Fin E → C) : Anchor E → ExpandedVertex E C
  | .inl i => .inl i
  | .inr (.inl i) => .inr (.inl (clauseLabel i))
  | .inr (.inr i) => .inr (.inr i)

theorem expandedVertex_anchor {E : Nat} {C : Type} (B : BipartiteRotation E)
    (clauseLabel : Fin E → C) : ∀ d, expandedVertex B clauseLabel d = anchorVertex clauseLabel (B.anchor d) := by
  apply six_cases
  intro i
  simp [expandedVertex, anchor, anchorVertex, d6]

theorem newNode_reaches_anchor {E : Nat} (B : BipartiteRotation E) :
    ∀ d, STACS2027.PlanarGluing.Reaches B.newNode d (anchorDart (B.anchor d)) := by
  apply six_cases
  intro i
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨2, ?_⟩, ⟨0, ?_⟩, ⟨1, ?_⟩, ⟨1, ?_⟩⟩ <;>
    simp [iterate, anchor, anchorDart, newNode, d6, B.varRot.right_inv]

theorem expandedVertex_step {E : Nat} {C : Type} (B : BipartiteRotation E)
    (clauseLabel : Fin E → C)
    (horbit : ∀ i j, STACS2027.PlanarGluing.Reaches B.clause.toFun i j ↔ clauseLabel i = clauseLabel j) :
    ∀ d, expandedVertex B clauseLabel (B.newNode d) = expandedVertex B clauseLabel d := by
  apply six_cases
  intro i
  have hc : clauseLabel (B.clause.toFun i) = clauseLabel i :=
    ((horbit i _).mp (STACS2027.PlanarGluing.Reaches.step _ _)).symm
  simp [expandedVertex, newNode, d6, B.varRot.right_inv, hc]

theorem anchors_reach {E : Nat} {C : Type} (B : BipartiteRotation E)
    (clauseLabel : Fin E → C)
    (horbit : ∀ i j, STACS2027.PlanarGluing.Reaches B.clause.toFun i j ↔ clauseLabel i = clauseLabel j)
    (a b : Anchor E) (h : anchorVertex clauseLabel a = anchorVertex clauseLabel b) :
    STACS2027.PlanarGluing.Reaches B.newNode (anchorDart a) (anchorDart b) := by
  rcases a with i | (i | i) <;> rcases b with j | (j | j) <;>
    simp only [anchorVertex, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl] at h
  · subst j; exact STACS2027.PlanarGluing.Reaches.refl _ _
  · apply reaches_map B.clause.toFun B.newNode (fun i => d6 i 1) _ ((horbit i j).mpr h)
    intro i
    exact ⟨1, by simp [iterate, newNode, d6]⟩
  · subst j; exact STACS2027.PlanarGluing.Reaches.refl _ _

/-- Every node orbit is exactly one vertex of the explicit expanded graph. -/
theorem expanded_node_orbit {E : Nat} {C : Type} (B : BipartiteRotation E)
    (clauseLabel : Fin E → C)
    (horbit : ∀ i j, STACS2027.PlanarGluing.Reaches B.clause.toFun i j ↔ clauseLabel i = clauseLabel j)
    (d d' : Fin (6 * E)) :
    STACS2027.PlanarGluing.Reaches B.expanded.node d d' ↔ expandedVertex B clauseLabel d = expandedVertex B clauseLabel d' := by
  constructor
  · rintro ⟨k, rfl⟩
    exact (iterate_invariant B.newNode (expandedVertex B clauseLabel)
      (B.expandedVertex_step clauseLabel horbit) k d).symm
  · intro he
    rw [B.expandedVertex_anchor, B.expandedVertex_anchor] at he
    exact (B.newNode_reaches_anchor d).trans
      ((B.anchors_reach clauseLabel horbit _ _ he).trans
        ((B.newNode_reaches_anchor d').symm (hm_node_inj B.expanded)))

/-- Concrete edge-list planarity for the occurrence-copy ring expansion.
The sole orbit hypothesis identifies the source clause labels; the surgery
and the expanded graph's endpoint correspondence are proved above. -/
theorem expandedEdges_planar {E : Nat} {C : Type} (B : BipartiteRotation E)
    (clauseLabel : Fin E → C)
    (horbit : ∀ i j, STACS2027.PlanarGluing.Reaches B.clause.toFun i j ↔ clauseLabel i = clauseLabel j)
    (hp : B.original.Planar) : PlanarGraph (expandedEdges B clauseLabel) := by
  unfold PlanarGraph
  rw [expandedEdges_length]
  rw [show 2 * (3 * E) = 6 * E by omega]
  refine ⟨B.expanded, B.expanded_edge_pairing, ?_, B.expanded_planar hp⟩
  intro d d'
  rw [B.expandedEdges_end, B.expandedEdges_end, Option.some.injEq]
  exact B.expanded_node_orbit clauseLabel horbit d d'

end STACS2027.PlanarSource.Embedding.BipartiteRotation
