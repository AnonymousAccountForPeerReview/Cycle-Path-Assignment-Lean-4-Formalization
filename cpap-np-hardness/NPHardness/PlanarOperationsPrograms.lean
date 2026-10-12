module

public import NPHardness.PlanarOperations
public import NPHardness.SubdivisionPrograms

/-!
The existing subdivision programs are related by actual edge-list permutations,
not merely equality of simple edge sets. This preserves the multigraph semantics
of the registered planarity predicate.
-/

@[expose] public section
namespace STACS2027
open Complexity

theorem subdivideOnce_perm_liftEdges {g : Graph} {a b z : Nat}
    (hn : g.Nodup) (he : edge a b ∈ g) :
    (subdivideOnce g a b z).Perm (liftEdges a b z g) := by
  have h : g.Perm (edge a b :: g.filter (· != edge a b)) := by
    simpa only [hn.erase_eq_filter] using List.perm_cons_erase he
  have hf := h.flatMap_right (splitEdge a b z)
  have ha : edge a b ∉ g.filter (· != edge a b) := by simp
  have hl := liftEdges_of_absent a b z (g.filter (· != edge a b)) ha
  change (liftEdges a b z g).Perm _ at hf
  simp only [List.flatMap_cons,splitEdge,↓reduceIte,List.cons_append,List.nil_append] at hf
  change (liftEdges a b z g).Perm (edge a z :: edge z b :: liftEdges a b z (g.filter (· != edge a b))) at hf
  rw [hl] at hf
  exact hf.symm

theorem subdivideOnce_nodup {g : Graph} {a b z : Nat}
    (hn : g.Nodup) (hab : a ≠ b) (he : edge a b ∈ g) (hf : FreshVertex g z) :
    (subdivideOnce g a b z).Nodup :=
  (subdivideOnce_perm_liftEdges hn he).symm.nodup
    (liftEdges_nodup hab hf hn (fun _ h => h))

theorem subdivisionGraph_nodup (g : Graph) (ss : List SubdivisionStep)
    (hn : g.Nodup) (hv : validSubdivision g ss) : (subdivisionGraph g ss).Nodup := by
  induction ss generalizing g with
  | nil => exact hn
  | cons s ss ih =>
    exact ih _ (subdivideOnce_nodup hn hv.1 hv.2.1 hv.2.2.1) hv.2.2.2

theorem subdivisionGraph_perm_expanded (g : Graph) (ss : List SubdivisionStep)
    (hn : g.Nodup) (hv : validSubdivision g ss) :
    (subdivisionGraph g ss).Perm (g.flatMap (expandedEdge ss)) := by
  induction ss generalizing g with
  | nil => simp [subdivisionGraph,expandedEdge]
  | cons s ss ih =>
    have hp := ih _ (subdivideOnce_nodup hn hv.1 hv.2.1 hv.2.2.1) hv.2.2.2
    have hq := (subdivideOnce_perm_liftEdges (z := s.fresh) hn hv.2.1).flatMap_right (expandedEdge ss)
    have ht := hp.trans hq
    simpa only [subdivisionGraph,liftEdges,List.flatMap_assoc,expandedEdge] using ht

theorem realizeLinks_perm_subdivisionGraph (next : Nat) (ls : List Link)
    (hb : VerticesBelow (linkEdges ls) next) (hn : (linkEdges ls).Nodup)
    (hp : ∀ l ∈ ls, l.source ≠ l.target) :
    (realizeLinks next ls).Perm (subdivisionGraph (linkEdges ls) (linkSteps next ls)) := by
  rw [← realizeLinks_eq_expanded next ls hb hn hp]
  exact (subdivisionGraph_perm_expanded _ _ hn (linkSteps_from_base_valid next ls hb hn hp)).symm

/-- The bounded-label subdivision program agrees with the raw two-edge construction,
up to an edge-list permutation. Both new edge pairs are already normalized. -/
theorem splitEdges_singleton_perm (a b z : Nat) (ha : a<z) (hb : b<z) :
    (PlanarOperations.Subdivision.splitEdges [edge a b] (fun _ => z)).Perm
      [edge a z,edge z b] := by
  by_cases hab : a ≤ b
  · simp only [PlanarOperations.Subdivision.splitEdges,List.zipIdx_cons,List.zipIdx_nil,
      List.flatMap_cons,List.flatMap_nil,List.append_nil]
    simp [edge,Nat.min_eq_left hab,Nat.max_eq_right hab,
      Nat.min_eq_left (Nat.le_of_lt ha),Nat.max_eq_right (Nat.le_of_lt ha),
      Nat.min_eq_right (Nat.le_of_lt hb),Nat.max_eq_left (Nat.le_of_lt hb)]
  · have hba : b ≤ a := by omega
    simp only [PlanarOperations.Subdivision.splitEdges,List.zipIdx_cons,List.zipIdx_nil,
      List.flatMap_cons,List.flatMap_nil,List.append_nil]
    simp only [edge,Nat.min_eq_right hba,Nat.max_eq_left hba,
      Nat.min_eq_left (Nat.le_of_lt ha),Nat.max_eq_right (Nat.le_of_lt ha),
      Nat.min_eq_right (Nat.le_of_lt hb),Nat.max_eq_left (Nat.le_of_lt hb)]
    exact List.Perm.swap _ _ _

end STACS2027
