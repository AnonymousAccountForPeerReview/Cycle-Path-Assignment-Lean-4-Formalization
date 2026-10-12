module

public import NPHardness.PlanarPreprocessDeletionShrink
public import NPHardness.PlanarGluingCut
import Lean.Elab.Tactic.Omega

/-! Exact connected-component accounting when an edge-fixed greatest dart
is excised. The surviving reachability relation is proved in both directions;
only an isolated removed dart contributes a lost component. -/

@[expose] public section
namespace STACS2027.PlanarPreprocess.Deletion
open Complexity Complexity.Planar STACS2027.PlanarGluing

theorem old_dart_cases {n : Nat} (d : Fin (n + 1)) : (∃ x : Fin n, embed x = d) ∨ d = last n := by
  by_cases h : d.val < n
  · exact Or.inl ⟨⟨d.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr (Fin.ext (by have := d.isLt; simp only [last]; omega))

def project {n : Nat} (base : Fin n) (d : Fin (n + 1)) : Fin n :=
  if h : d.val < n then ⟨d.val, h⟩ else base

@[simp] theorem project_embed {n : Nat} (base x : Fin n) : project base (embed x) = x := by
  simp [project, embed, x.isLt]

@[simp] theorem project_last {n : Nat} (base : Fin n) : project base (last n) = base := by
  simp [project, last]

theorem embed_project {n : Nat} (base : Fin n) {d : Fin (n + 1)} (h : d ≠ last n) :
    embed (project base d) = d := by
  rcases old_dart_cases d with ⟨x, rfl⟩ | hd
  · rw [project_embed]
  · exact False.elim (h hd)

theorem project_removeLast_of_ne {n : Nat} (base : Fin n) {p : Fin (n + 1) → Fin (n + 1)}
    (hp : ∀ x y, p x = p y → x = y) (x : Fin n) (h : p (embed x) ≠ last n) :
    project base (p (embed x)) = removeLast p hp x := by
  have he := embed_removeLast p hp x
  rw [skipLast, ite_eq_right h] at he
  rw [← he, project_embed]

theorem removeLast_of_hits {n : Nat} {p : Fin (n + 1) → Fin (n + 1)}
    (hp : ∀ x y, p x = p y → x = y) (x base : Fin n)
    (hx : p (embed x) = last n) (hb : p (last n) = embed base) : removeLast p hp x = base := by
  apply embed_injective
  rw [embed_removeLast, skipLast, ite_eq_left hx, hb]

theorem edgeOrbit_linked {n : Nat} (G : Hypermap n) {x y : Fin n}
    (h : Reaches G.edge x y) : LinkedPath G x y := by
  obtain ⟨k, rfl⟩ := h
  induction k generalizing x with
  | zero => exact LinkedPath.refl _ _
  | succ k ih => exact (LinkedPath.step G (Or.inl rfl)).trans (ih (x := G.edge x))

theorem shrink_step_lift {n : Nat} (G : Hypermap (n + 1)) (he : G.edge (last n) = last n)
    {x y : Fin n} (hs : Linked.Step (shrinkLast G he) x y) : LinkedPath G (embed x) (embed y) := by
  rcases hs with hs | hs | hs
  · exact edgeOrbit_linked G ((shrinkLast_edge_orbit G he x y).mp ⟨1, hs⟩)
  · exact nodeOrbit_linked G ((shrinkLast_node_orbit G he x y).mp ⟨1, hs⟩)
  · exact faceOrbit_linked G ((shrinkLast_face_orbit G he x y).mp ⟨1, hs⟩)

theorem shrink_path_lift {n : Nat} (G : Hypermap (n + 1)) (he : G.edge (last n) = last n)
    {x y : Fin n} (h : LinkedPath (shrinkLast G he) x y) : LinkedPath G (embed x) (embed y) := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at hk; subst y; exact LinkedPath.refl _ _
  | succ k ih =>
    rcases (Linked.linked_succ (shrinkLast G he) k x y).mp hk with h | ⟨z, hz, hs⟩
    · exact ih h
    · exact (ih hz).trans (shrink_step_lift G he hs)

theorem project_fixed_perm_step {n : Nat} (H : Hypermap n) (base : Fin n)
    {p : Fin (n + 1) → Fin (n + 1)} (hp : ∀ x y, p x = p y → x = y)
    (hfix : p (last n) = last n) (hstep : ∀ x, Linked.Step H x (removeLast p hp x))
    (d : Fin (n + 1)) : LinkedPath H (project base d) (project base (p d)) := by
  rcases old_dart_cases d with ⟨x, rfl⟩ | rfl
  · have hne : p (embed x) ≠ last n := fun h => embed_ne_last x (hp _ _ (h.trans hfix.symm))
    rw [project_embed, project_removeLast_of_ne base hp x hne]
    exact LinkedPath.step H (hstep x)
  · rw [hfix]
    exact LinkedPath.refl _ _

theorem project_shrink_step_fixed {n : Nat} (G : Hypermap (n + 1))
    (he : G.edge (last n) = last n) (hn : G.node (last n) = last n) (base : Fin n)
    {x y : Fin (n + 1)} (hs : Linked.Step G x y) :
    LinkedPath (shrinkLast G he) (project base x) (project base y) := by
  rcases hs with rfl | rfl | rfl
  · exact project_fixed_perm_step _ base (hm_edge_inj G) he (fun _ => Or.inl rfl) x
  · exact project_fixed_perm_step _ base (hm_node_inj G) hn (fun _ => Or.inr (Or.inl rfl)) x
  · exact project_fixed_perm_step _ base (hm_face_inj G)
      ((edge_fixed_face_node_fixed G he).mpr hn) (fun _ => Or.inr (Or.inr rfl)) x

theorem project_shrink_node_step {n : Nat} (G : Hypermap (n + 1))
    (he : G.edge (last n) = last n) (base : Fin n) (hb : G.node (last n) = embed base)
    (x : Fin (n + 1)) :
    LinkedPath (shrinkLast G he) (project base x) (project base (G.node x)) := by
  rcases old_dart_cases x with ⟨x, rfl⟩ | rfl
  · rw [project_embed]
    by_cases hx : G.node (embed x) = last n
    · rw [hx, project_last]
      have hs : (shrinkLast G he).node x = base := removeLast_of_hits (hm_node_inj G) x base hx hb
      exact LinkedPath.step _ (Or.inr (Or.inl hs))
    · rw [project_removeLast_of_ne base (hm_node_inj G) x hx]
      exact LinkedPath.step _ (Or.inr (Or.inl rfl))
  · rw [hb, project_last, project_embed]
    exact LinkedPath.refl _ _

theorem project_shrink_face_step {n : Nat} (G : Hypermap (n + 1))
    (he : G.edge (last n) = last n) (base : Fin n) (hb : G.node (last n) = embed base)
    (x : Fin (n + 1)) :
    LinkedPath (shrinkLast G he) (project base x) (project base (G.face x)) := by
  let H := shrinkLast G he
  rcases old_dart_cases x with ⟨x, rfl⟩ | rfl
  · rw [project_embed]
    by_cases hx : G.face (embed x) = last n
    · rw [hx, project_last]
      have hEb : G.edge (embed base) = embed x := by
        apply hm_face_inj G
        apply hm_node_inj G
        rw [G.edgeK, hx, hb]
      have hnew : H.edge base = x := by
        apply embed_injective
        rw [shrinkLast_edge_lift, hEb]
      exact (LinkedPath.step H (Or.inl hnew)).symm
    · rw [project_removeLast_of_ne base (hm_face_inj G) x hx]
      exact LinkedPath.step H (Or.inr (Or.inr rfl))
  · rw [project_last]
    have hnf : G.node (last n) ≠ last n := fun h => embed_ne_last base (hb.symm.trans h)
    have hff : G.face (last n) ≠ last n := fun h => hnf ((edge_fixed_face_node_fixed G he).mp h)
    let c := project base (G.face (last n))
    have hc : embed c = G.face (last n) := embed_project base hff
    have hNc : G.node (embed c) = last n := by
      rw [hc]
      have h := G.edgeK (last n)
      simpa only [he] using h
    have hnew : H.node c = base := removeLast_of_hits (hm_node_inj G) c base hNc hb
    exact (LinkedPath.step H (Or.inr (Or.inl hnew))).symm

theorem project_shrink_step {n : Nat} (G : Hypermap (n + 1))
    (he : G.edge (last n) = last n) (base : Fin n)
    (hb : G.node (last n) = last n ∨ G.node (last n) = embed base)
    {x y : Fin (n + 1)} (hs : Linked.Step G x y) :
    LinkedPath (shrinkLast G he) (project base x) (project base y) := by
  rcases hb with hn | hn
  · exact project_shrink_step_fixed G he hn base hs
  · rcases hs with rfl | rfl | rfl
    · exact project_fixed_perm_step _ base (hm_edge_inj G) he (fun _ => Or.inl rfl) x
    · exact project_shrink_node_step G he base hn x
    · exact project_shrink_face_step G he base hn x

theorem project_shrink_path {n : Nat} (G : Hypermap (n + 1))
    (he : G.edge (last n) = last n) (base : Fin n)
    (hb : G.node (last n) = last n ∨ G.node (last n) = embed base)
    {x y : Fin (n + 1)} (h : LinkedPath G x y) :
    LinkedPath (shrinkLast G he) (project base x) (project base y) := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at hk; subst y; exact LinkedPath.refl _ _
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp hk with h | ⟨z, hz, hs⟩
    · exact ih h
    · exact (ih hz).trans (project_shrink_step G he base hb hs)

theorem shrinkLast_linked {n : Nat} (G : Hypermap (n + 1)) (he : G.edge (last n) = last n)
    (x y : Fin n) : LinkedPath (shrinkLast G he) x y ↔ LinkedPath G (embed x) (embed y) := by
  constructor
  · exact shrink_path_lift G he
  · intro h
    by_cases hn : G.node (last n) = last n
    · have ht := project_shrink_path G he x (Or.inl hn) h
      simpa only [project_embed] using ht
    · obtain ⟨base, hb⟩ := (old_dart_cases (G.node (last n))).resolve_right hn
      have ht := project_shrink_path G he base (Or.inr hb.symm) h
      simpa only [project_embed] using ht

theorem shrinkLast_componentRoot {n : Nat} (G : Hypermap (n + 1))
    (he : G.edge (last n) = last n) (x : Fin n) :
    ComponentRoot G (embed x) = ComponentRoot (shrinkLast G he) x := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    simp only [ComponentRoot, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq]
    intro y
    by_cases hl : (shrinkLast G he).linked n x y = true
    · right
      obtain ⟨k, hk⟩ := (shrinkLast_linked G he x y).mp ⟨n, hl⟩
      exact componentRoot_le G hx hk
    · left; exact Bool.eq_false_iff.mpr hl
  · intro hx
    simp only [ComponentRoot, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq]
    intro y
    by_cases hl : G.linked (n + 1) (embed x) y = true
    · right
      rcases old_dart_cases y with ⟨y, rfl⟩ | rfl
      · obtain ⟨k, hk⟩ := (shrinkLast_linked G he x y).mpr ⟨n + 1, hl⟩
        change x.val ≤ y.val
        exact componentRoot_le (shrinkLast G he) hx hk
      · change x.val ≤ n
        have := x.isLt
        omega
    · left; exact Bool.eq_false_iff.mpr hl

theorem linked_from_fixed {n : Nat} (G : Hypermap n) (x : Fin n)
    (he : G.edge x = x) (hn : G.node x = x) (hf : G.face x = x)
    {y : Fin n} {k : Nat} (h : G.linked k x y = true) : y = x := by
  induction k generalizing y with
  | zero => exact ((Linked.linked_zero G x y).mp h).symm
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp h with h | ⟨z, hz, hs⟩
    · exact ih h
    · have hz' := ih hz
      subst z
      rcases hs with hs | hs | hs <;> simp_all

theorem componentRoot_last {n : Nat} (G : Hypermap (n + 1))
    (he : G.edge (last n) = last n) :
    ComponentRoot G (last n) = true ↔ G.node (last n) = last n := by
  constructor
  · intro hroot
    have hlink := Linked.linked_step G (Linked.linked_refl G 0 (last n)) (Or.inr (Or.inl rfl))
    have hle := componentRoot_le G hroot hlink
    apply Fin.ext
    have hlt := (G.node (last n)).isLt
    change n ≤ (G.node (last n)).val at hle
    change (G.node (last n)).val = n
    omega
  · intro hn
    have hf := (edge_fixed_face_node_fixed G he).mpr hn
    simp only [ComponentRoot, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq]
    intro y
    by_cases hl : G.linked (n + 1) (last n) y = true
    · right
      rw [linked_from_fixed G (last n) he hn hf hl]
      exact Nat.le_refl _
    · left; exact Bool.eq_false_iff.mpr hl

/-- Exactly one component is lost precisely when the removed dart was isolated. -/
theorem shrinkLast_components {n : Nat} (G : Hypermap (n + 1))
    (he : G.edge (last n) = last n) :
    G.componentCount = (shrinkLast G he).componentCount + singletonLoss G := by
  change (List.finRange (n + 1)).countP (ComponentRoot G) =
    (List.finRange n).countP (ComponentRoot (shrinkLast G he)) + singletonLoss G
  rw [List.finRange_succ_last, List.countP_append, List.countP_map]
  have hroots : (fun x : Fin n => ComponentRoot G (Fin.castSucc x)) =
      ComponentRoot (shrinkLast G he) := by
    funext x
    exact shrinkLast_componentRoot G he x
  simp only [Function.comp_def]
  rw [hroots]
  have hlast := componentRoot_last G he
  by_cases hn : G.node (last n) = last n
  · have ht := hlast.mpr hn
    simp only [singletonLoss, hn, ite_true]
    change _ + (if ComponentRoot G (last n) then 1 else 0) = _ + 1
    rw [ht]
    rfl
  · have ht : ComponentRoot G (last n) = false :=
      Bool.eq_false_iff.mpr (fun h => hn (hlast.mp h))
    simp only [singletonLoss, hn, ite_false]
    change _ + (if ComponentRoot G (last n) then 1 else 0) = _ + 0
    rw [ht]
    rfl

theorem shrinkLast_planar {n : Nat} (G : Hypermap (n + 1))
    (he : G.edge (last n) = last n) (hp : G.Planar) : (shrinkLast G he).Planar := by
  rw [planar_iff] at hp ⊢
  have hc := shrinkLast_components G he
  have hr := shrinkLast_eulerRhs G he
  omega

end STACS2027.PlanarPreprocess.Deletion
