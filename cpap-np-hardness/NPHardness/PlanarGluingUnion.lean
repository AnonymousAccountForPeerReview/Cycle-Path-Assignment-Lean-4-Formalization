module

public import NPHardness.PlanarGluingJoin
public import Complexity.Planar.Incidence
import Lean.Elab.Tactic.Omega

/-!
Disjoint unions of embedded graphs. The added components carry the exact
spherical Euler inequality, which is directly available for explicitly
constructed cycles. This avoids assuming an unproved parity theorem for
arbitrary hypermaps when combining the registered natural-number genus.
-/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

theorem sumPerm_iterate_left {n m : Nat} (p : Fin n → Fin n) (q : Fin m → Fin m)
    (k : Nat) (x : Fin n) : iterate (sumPerm p q) k (left x) = left (iterate p k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simpa only [iterate, sumPerm_left] using ih (p x)

theorem sumPerm_iterate_right {n m : Nat} (p : Fin n → Fin n) (q : Fin m → Fin m)
    (k : Nat) (x : Fin m) : iterate (sumPerm p q) k (right x) = right (iterate q k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simpa only [iterate, sumPerm_right] using ih (q x)

def disjointSum {n m : Nat} (G : Hypermap n) (H : Hypermap m) : Hypermap (n + m) where
  edge := sumPerm G.edge H.edge
  node := sumPerm G.node H.node
  face := sumPerm G.face H.face
  edgeK x := by
    rcases cases_dart x with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> simp [G.edgeK, H.edgeK]

theorem disjointSum_left_path {n m : Nat} (G : Hypermap n) (H : Hypermap m)
    {x y : Fin n} (h : LinkedPath G x y) : LinkedPath (disjointSum G H) (left x) (left y) := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at hk; subst y; exact LinkedPath.refl _ _
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp hk with h | ⟨z, hz, hs⟩
    · exact ih h
    · apply (ih hz).trans
      apply LinkedPath.step
      rcases hs with hs | hs | hs
      · exact Or.inl (by change sumPerm G.edge H.edge (left z) = left y; rw [sumPerm_left, hs])
      · exact Or.inr (Or.inl (by change sumPerm G.node H.node (left z) = left y; rw [sumPerm_left, hs]))
      · exact Or.inr (Or.inr (by change sumPerm G.face H.face (left z) = left y; rw [sumPerm_left, hs]))

theorem disjointSum_right_path {n m : Nat} (G : Hypermap n) (H : Hypermap m)
    {x y : Fin m} (h : LinkedPath H x y) : LinkedPath (disjointSum G H) (right x) (right y) := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at hk; subst y; exact LinkedPath.refl _ _
  | succ k ih =>
    rcases (Linked.linked_succ H k x y).mp hk with h | ⟨z, hz, hs⟩
    · exact ih h
    · apply (ih hz).trans
      apply LinkedPath.step
      rcases hs with hs | hs | hs
      · exact Or.inl (by change sumPerm G.edge H.edge (right z) = right y; rw [sumPerm_right, hs])
      · exact Or.inr (Or.inl (by change sumPerm G.node H.node (right z) = right y; rw [sumPerm_right, hs]))
      · exact Or.inr (Or.inr (by change sumPerm G.face H.face (right z) = right y; rw [sumPerm_right, hs]))

def componentRoots {n : Nat} (G : Hypermap n) : List (Fin n) :=
  (List.finRange n).filter (ComponentRoot G)

theorem componentRoots_length {n : Nat} (G : Hypermap n) :
    (componentRoots G).length = G.componentCount := by
  change ((List.finRange n).filter (ComponentRoot G)).length =
    (List.finRange n).countP (ComponentRoot G)
  exact List.countP_eq_length_filter.symm

theorem disjointSum_components_le {n m : Nat} (G : Hypermap n) (H : Hypermap m) :
    (disjointSum G H).componentCount ≤ G.componentCount + H.componentCount := by
  let f : Fin (n + m) → Fin (n + m) :=
    split (fun x => left (componentRep G x)) (fun y => right (componentRep H y))
  let ys := (componentRoots G).map (left (m := m)) ++ (componentRoots H).map (right (n := n))
  have hp : ∀ x, LinkedPath (disjointSum G H) x (f x) := by
    intro x
    rcases cases_dart x with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · simpa only [f, split_left] using
        disjointSum_left_path G H ⟨n, componentRep_linked G x⟩
    · simpa only [f, split_right] using
        disjointSum_right_path G H ⟨m, componentRep_linked H x⟩
  have hm : ∀ x, f x ∈ ys := by
    intro x
    rcases cases_dart x with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · simp only [f, split_left]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨componentRep G x,
        List.mem_filter.mpr ⟨List.mem_finRange _, componentRep_root G x⟩, rfl⟩)
    · simp only [f, split_right]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨componentRep H x,
        List.mem_filter.mpr ⟨List.mem_finRange _, componentRep_root H x⟩, rfl⟩)
  have hnd : ((componentRoots (disjointSum G H)).map f).Nodup := by
    apply nodup_map_of_injOn' _ (List.Pairwise.filter _ (List.nodup_finRange _))
    intro x hx y hy he
    have hx' := hp x
    rw [he] at hx'
    obtain ⟨k, hk⟩ := hx'.trans (hp y).symm
    exact componentRoot_eq _ (List.mem_filter.mp hx).2 (List.mem_filter.mp hy).2 hk
  have hle := List.Nodup.length_le_of_subset hnd (l₂ := ys) (by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact hm y)
  simpa only [List.length_map, componentRoots_length, ys, List.length_append] using hle

theorem disjointSum_euler_ge {n m : Nat} (G : Hypermap n) (H : Hypermap m) :
    G.eulerRhs + H.eulerRhs ≤ (disjointSum G H).eulerRhs := by
  have he := sumPerm_cycles_ge (hm_edge_inj G) (hm_edge_inj H)
  have hn := sumPerm_cycles_ge (hm_node_inj G) (hm_node_inj H)
  have hf := sumPerm_cycles_ge (hm_face_inj G) (hm_face_inj H)
  unfold Hypermap.eulerRhs
  change _ ≤ cycleCount (sumPerm G.edge H.edge) + cycleCount (sumPerm G.node H.node) +
    cycleCount (sumPerm G.face H.face)
  omega

theorem disjointSum_planar {n m : Nat} (G : Hypermap n) (H : Hypermap m)
    (hG : G.Planar) (hH : 2 * H.componentCount + m ≤ H.eulerRhs) :
    (disjointSum G H).Planar := by
  rw [planar_iff] at hG ⊢
  have hc := disjointSum_components_le G H
  have hr := disjointSum_euler_ge G H
  omega

/-- The registered table checker supplies the strict inequality when its
final numeric check holds without the permitted one-unit slack. -/
theorem tables_spherical {t : EmbedTables} (h : EmbedOK t)
    (hfinal : 2 * t.cC (2 * t.n2) + t.n2 ≤ t.cR (2 * t.n2) + t.cF (2 * t.n2)) :
    2 * h.hypermap.componentCount + 2 * t.n2 ≤ h.hypermap.eulerRhs := by
  have he := cycleCount_graphEdge_ge h.isGraphEdge
  have hn := h.node_count
  have hf := h.face_count
  have hc := h.component_count
  unfold Hypermap.eulerRhs
  omega

/-- A registered graph embedding with the exact spherical Euler inequality. -/
structure SphericalEmbedding {V : Type} (es : List (V × V)) where
  map : Hypermap (2 * es.length)
  edge : ∀ d, map.edge d = graphEdge d
  nodes : ∀ d d', (∃ k, iterate map.node k d = d') ↔
    halfEdgeEnd es d.val = halfEdgeEnd es d'.val
  euler : 2 * map.componentCount + 2 * es.length ≤ map.eulerRhs

theorem disjointSum_graphEdge {E F : Nat} (G : Hypermap (2 * E)) (H : Hypermap (2 * F))
    (hG : ∀ d, G.edge d = graphEdge d) (hH : ∀ d, H.edge d = graphEdge d)
    (d : Fin (2 * E + 2 * F)) :
    ((disjointSum G H).edge d).val = ed d.val := by
  rcases cases_dart d with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · change (sumPerm G.edge H.edge (left d)).val = ed (left d).val
    rw [sumPerm_left, hG]
    rfl
  · change (sumPerm G.edge H.edge (right d)).val = ed (right d).val
    rw [sumPerm_right, hH]
    change 2 * E + ed d.val = ed (2 * E + d.val)
    rcases Nat.mod_two_eq_zero_or_one d.val with h | h <;>
      simp [ed, h, Nat.add_mod] <;> omega

theorem disjointSum_nodes {V : Type} (es ts : List (V × V))
    (G : Hypermap (2 * es.length)) (H : Hypermap (2 * ts.length))
    (hG : ∀ d d', (∃ k, iterate G.node k d = d') ↔ halfEdgeEnd es d.val = halfEdgeEnd es d'.val)
    (hH : ∀ d d', (∃ k, iterate H.node k d = d') ↔ halfEdgeEnd ts d.val = halfEdgeEnd ts d'.val)
    (hdisjoint : ∀ d : Fin (2 * es.length), ∀ d' : Fin (2 * ts.length),
      halfEdgeEnd es d.val ≠ halfEdgeEnd ts d'.val)
    (x y : Fin (2 * es.length + 2 * ts.length)) :
    (∃ k, iterate (disjointSum G H).node k x = y) ↔
      halfEdgeEnd (es ++ ts) x.val = halfEdgeEnd (es ++ ts) y.val := by
  have hleft : ∀ d : Fin (2 * es.length),
      halfEdgeEnd (es ++ ts) (left (m := 2 * ts.length) d).val = halfEdgeEnd es d.val :=
    fun d => halfEdgeEnd_append_left es ts d.val d.isLt
  have hright : ∀ d : Fin (2 * ts.length),
      halfEdgeEnd (es ++ ts) (right (n := 2 * es.length) d).val = halfEdgeEnd ts d.val := by
    intro d
    rw [halfEdgeEnd_append_right es ts _ (by simp [right])]
    simp [right]
  change (∃ k, iterate (sumPerm G.node H.node) k x = y) ↔ _
  rcases cases_dart x with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases cases_dart y with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · rw [hleft, hleft, ← hG]
    constructor
    · rintro ⟨k, hk⟩; rw [sumPerm_iterate_left] at hk; exact ⟨k, left_injective hk⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [sumPerm_iterate_left, hk]⟩
  · rw [hleft, hright]
    constructor
    · rintro ⟨k, hk⟩; rw [sumPerm_iterate_left] at hk; exact False.elim (left_ne_right _ _ hk)
    · intro h; exact False.elim (hdisjoint x y h)
  · rw [hright, hleft]
    constructor
    · rintro ⟨k, hk⟩; rw [sumPerm_iterate_right] at hk; exact False.elim (left_ne_right _ _ hk.symm)
    · intro h; exact False.elim (hdisjoint y x h.symm)
  · rw [hright, hright, ← hH]
    constructor
    · rintro ⟨k, hk⟩; rw [sumPerm_iterate_right] at hk; exact ⟨k, right_injective hk⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [sumPerm_iterate_right, hk]⟩

/-- Add disjoint components carrying an exact spherical embedding. -/
theorem planarGraph_append_spherical {V : Type} {es ts : List (V × V)}
    (hG : PlanarGraph es) (hH : SphericalEmbedding ts)
    (hdisjoint : ∀ d : Fin (2 * es.length), ∀ d' : Fin (2 * ts.length),
      halfEdgeEnd es d.val ≠ halfEdgeEnd ts d'.val) : PlanarGraph (es ++ ts) := by
  obtain ⟨G, he, hn, hp⟩ := hG
  unfold PlanarGraph
  rw [List.length_append, Nat.mul_add]
  refine ⟨disjointSum G hH.map, ?_, disjointSum_nodes es ts G hH.map hn hH.nodes hdisjoint,
    disjointSum_planar G hH.map hp hH.euler⟩
  exact disjointSum_graphEdge G hH.map (fun d => Fin.ext (he d)) hH.edge

end STACS2027.PlanarGluing
