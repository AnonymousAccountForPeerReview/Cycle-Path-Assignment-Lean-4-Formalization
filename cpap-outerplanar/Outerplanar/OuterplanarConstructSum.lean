module

public import Outerplanar.OuterplanarConstructSph
public import NPHardness.PlanarGluingUnion
public import NPHardness.PlanarGluingCut

/-!
# Disjoint unions of spherical outerplanar embeddings

The disjoint sum `disjointSum G H` of two hypermaps (Section 5) has the components of `G`
and of `H` side by side: a dart linked to a dart of `G` is a dart of `G`
(`disjointSum_linked_left`, `disjointSum_linked_right`). Hence the outer-face condition
holds on each side, and two spherical outerplanar embeddings of edge lists without common
vertex give one of their concatenation (`SphOuter.append_disjoint`).
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar PlanarGluing

section DisjointSum

variable {n m : Nat} (G : Hypermap n) (H : Hypermap m)

/-- The side and the component of a dart of the disjoint sum. -/
noncomputable def sumLabel : Fin (n + m) → Sum (Fin n) (Fin m) :=
  split (fun a => .inl (componentRep G a)) (fun b => .inr (componentRep H b))

theorem sumLabel_step {x y : Fin (n + m)} (hs : Linked.Step (disjointSum G H) x y) :
    sumLabel G H y = sumLabel G H x := by
  rcases cases_dart x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rcases hs with hs | hs | hs
    · change sumPerm G.edge H.edge (left a) = y at hs
      rw [sumPerm_left] at hs; subst hs
      simp only [sumLabel, split_left, componentRep_step G (Or.inl rfl)]
    · change sumPerm G.node H.node (left a) = y at hs
      rw [sumPerm_left] at hs; subst hs
      simp only [sumLabel, split_left, componentRep_step G (Or.inr (Or.inl rfl))]
    · change sumPerm G.face H.face (left a) = y at hs
      rw [sumPerm_left] at hs; subst hs
      simp only [sumLabel, split_left, componentRep_step G (Or.inr (Or.inr rfl))]
  · rcases hs with hs | hs | hs
    · change sumPerm G.edge H.edge (right b) = y at hs
      rw [sumPerm_right] at hs; subst hs
      simp only [sumLabel, split_right, componentRep_step H (Or.inl rfl)]
    · change sumPerm G.node H.node (right b) = y at hs
      rw [sumPerm_right] at hs; subst hs
      simp only [sumLabel, split_right, componentRep_step H (Or.inr (Or.inl rfl))]
    · change sumPerm G.face H.face (right b) = y at hs
      rw [sumPerm_right] at hs; subst hs
      simp only [sumLabel, split_right, componentRep_step H (Or.inr (Or.inr rfl))]

theorem sumLabel_path {x y : Fin (n + m)} (h : LinkedPath (disjointSum G H) x y) :
    sumLabel G H y = sumLabel G H x := by
  obtain ⟨k, hk⟩ := h
  exact linked_label_invariant _ (sumLabel G H) (fun _ _ hs => sumLabel_step G H hs) hk

/-- A dart linked in the disjoint sum to a dart of `G` is a dart of `G`, linked in `G`. -/
theorem disjointSum_linked_left {x : Fin n} {y : Fin (n + m)}
    (h : LinkedPath (disjointSum G H) (left x) y) : ∃ y', y = left y' ∧ LinkedPath G x y' := by
  have he := sumLabel_path G H h
  rcases cases_dart y with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · simp only [sumLabel, split_left, Sum.inl.injEq] at he
    exact ⟨a, rfl, linked_of_componentRep_eq G he.symm⟩
  · simp [sumLabel] at he

/-- A dart linked in the disjoint sum to a dart of `H` is a dart of `H`, linked in `H`. -/
theorem disjointSum_linked_right {x : Fin m} {y : Fin (n + m)}
    (h : LinkedPath (disjointSum G H) (right x) y) : ∃ y', y = right y' ∧ LinkedPath H x y' := by
  have he := sumLabel_path G H h
  rcases cases_dart y with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · simp [sumLabel] at he
  · simp only [sumLabel, split_right, Sum.inr.injEq] at he
    exact ⟨b, rfl, linked_of_componentRep_eq H he.symm⟩

theorem disjointSum_left_ne_right (x : Fin n) (y : Fin m) :
    ¬ LinkedPath (disjointSum G H) (left x) (right y) := by
  intro h
  obtain ⟨y', he, -⟩ := disjointSum_linked_left G H h
  exact left_ne_right y' y he.symm

theorem disjointSum_iterate_face_left (j : Nat) (x : Fin n) :
    iterate (disjointSum G H).face j (left x) = left (iterate G.face j x) :=
  sumPerm_iterate_left G.face H.face j x

theorem disjointSum_iterate_face_right (j : Nat) (x : Fin m) :
    iterate (disjointSum G H).face j (right x) = right (iterate H.face j x) :=
  sumPerm_iterate_right G.face H.face j x

theorem disjointSum_iterate_node_left (j : Nat) (x : Fin n) :
    iterate (disjointSum G H).node j (left x) = left (iterate G.node j x) :=
  sumPerm_iterate_left G.node H.node j x

theorem disjointSum_iterate_node_right (j : Nat) (x : Fin m) :
    iterate (disjointSum G H).node j (right x) = right (iterate H.node j x) :=
  sumPerm_iterate_right G.node H.node j x

/-- The outer-face condition of the two sides gives that of the disjoint sum. -/
theorem OuterFaceCond.disjointSum (hG : OuterFaceCond G) (hH : OuterFaceCond H) :
    OuterFaceCond (disjointSum G H) := by
  intro d
  rcases cases_dart d with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · obtain ⟨x, hx⟩ := hG a
    refine ⟨left x, fun d' hd' => ?_⟩
    obtain ⟨a', rfl, k0, hk0⟩ := disjointSum_linked_left G H ⟨_, hd'⟩
    obtain ⟨j, k, hjk⟩ := hx a' (Linked.linked_stable G hk0)
    exact ⟨j, k, by rw [disjointSum_iterate_face_left, disjointSum_iterate_node_left, hjk]⟩
  · obtain ⟨x, hx⟩ := hH b
    refine ⟨right x, fun d' hd' => ?_⟩
    obtain ⟨b', rfl, k0, hk0⟩ := disjointSum_linked_right G H ⟨_, hd'⟩
    obtain ⟨j, k, hjk⟩ := hx b' (Linked.linked_stable H hk0)
    exact ⟨j, k, by rw [disjointSum_iterate_face_right, disjointSum_iterate_node_right, hjk]⟩

end DisjointSum

/-- **Disjoint union.** Spherical outerplanar embeddings of two edge lists without common
vertex give one of their concatenation. -/
theorem SphOuter.append_disjoint {V : Type} {es ts : List (V × V)} (h1 : SphOuter es)
    (h2 : SphOuter ts)
    (hd : ∀ d : Fin (2 * es.length), ∀ d' : Fin (2 * ts.length),
      halfEdgeEnd es d.val ≠ halfEdgeEnd ts d'.val) : SphOuter (es ++ ts) := by
  obtain ⟨G, hE, hN, hS, hO⟩ := h1
  obtain ⟨H, hE', hN', hS', hO'⟩ := h2
  unfold SphOuter
  rw [List.length_append, Nat.mul_add]
  refine ⟨disjointSum G H, disjointSum_graphEdge G H (fun d => Fin.ext (hE d))
    (fun d => Fin.ext (hE' d)), disjointSum_nodes es ts G H hN hN' hd, ?_,
    OuterFaceCond.disjointSum G H hO hO'⟩
  have hc := disjointSum_components_le G H
  have hr := disjointSum_euler_ge G H
  omega

end STACS2027
