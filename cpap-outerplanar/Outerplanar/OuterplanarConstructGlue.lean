module

public import Outerplanar.OuterplanarConstructSum
public import NPHardness.PlanarGluingTransposition

/-!
# Gluing spherical outerplanar embeddings at a vertex

Two embedded graphs sharing exactly one vertex `c` are glued at `c` (`glueMap`): in the
disjoint sum, take a half-edge `α` at `c` on the outer face of the first graph and a
half-edge `β` at `c` on the outer face of the second; exchanging the successors of `α` and
`β` in the rotation (`transpose node α β`) inserts the rotation of the second graph at `c`
into a corner of the outer face of the first. Then the two node cycles at `c` merge into
one (`c` becomes one vertex), the two outer faces merge into one (`swap α β ∘ face`), and
the two components merge into one: the spherical inequality is preserved, and the merged
face passes through all the vertices of both outer faces (`SphOuter.append_glue`).

Together with the disjoint union this gives `SphOuter.append_cut`: spherical outerplanar
embeddings of two edge lists with at most one common vertex give one of their
concatenation.
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar PlanarGluing

/-! ### Permutation facts -/

section Perm

variable {n : Nat} {p : Fin n → Fin n} (hp : ∀ x y, p x = p y → x = y) {α β : Fin n}

theorem swap_left (α β : Fin n) : swap α β α = β := by simp [swap]

theorem swap_right (α β : Fin n) : swap α β β = α := by
  by_cases h : β = α
  · simp [swap, h]
  · simp [swap, h]

theorem swap_other {α β x : Fin n} (ha : x ≠ α) (hb : x ≠ β) : swap α β x = x := by
  simp [swap, ha, hb]

theorem iterate_swapComp (p : Fin n → Fin n) (α β : Fin n) (k : Nat) (x : Fin n) :
    iterate (fun y => swap α β (p y)) k x =
      swap α β (iterate (transpose p α β) k (swap α β x)) := by
  induction k generalizing x with
  | zero => simp [iterate]
  | succ k ih =>
    simp only [iterate]
    rw [ih]
    congr 2
    simp [transpose]

include hp in
/-- Composing with a transposition of two darts of different orbits merges the orbits. -/
theorem swapComp_reaches (hsep : cmin p α ≠ cmin p β) {y : Fin n}
    (hy : Reaches p α y ∨ Reaches p β y) : Reaches (fun y => swap α β (p y)) α y := by
  have hab : α ≠ β := fun h => hsep (congrArg (cmin p) h)
  have hba : Reaches (transpose p α β) β α :=
    (transpose_merge_markers hp α β hsep).symm (transpose_injective hp α β)
  suffices h : Reaches (transpose p α β) β (swap α β y) by
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    rw [iterate_swapComp, swap_left, hk, swap_swap]
  by_cases hya : y = α
  · subst hya; rw [swap_left]; exact Reaches.refl _ _
  by_cases hyb : y = β
  · subst hyb; rw [swap_right]; exact hba
  rw [swap_other hya hyb]
  rcases hy with hy | hy
  · exact hba.trans (transpose_merge_orbit hp α β hsep hy)
  · exact transpose_merge_orbit hp α β hsep hy

include hp in
theorem swapComp_cycles (hsep : cmin p α ≠ cmin p β) :
    cycleCount (fun y => swap α β (p y)) + 1 = cycleCount p := by
  let e : DartEquiv n n := ⟨swap α β, swap α β, swap_swap α β, swap_swap α β⟩
  have he : e.conjugate (transpose p α β) = fun y => swap α β (p y) := by
    funext y
    simp [DartEquiv.conjugate, e, transpose]
  rw [← he, e.cycles_eq (transpose_injective hp α β)]
  exact transpose_merge_cycles hp α β hsep

include hp in
/-- The orbits of `transpose p α β` when `α` and `β` lie in different orbits of `p`. -/
theorem transpose_reaches_iff (hsep : cmin p α ≠ cmin p β) (x y : Fin n) :
    Reaches (transpose p α β) x y ↔
      Reaches p x y ∨ ((Reaches p x α ∨ Reaches p x β) ∧ (Reaches p y α ∨ Reaches p y β)) := by
  constructor
  · rintro ⟨k, rfl⟩
    have hm := iterate_invariant (transpose p α β) (mergeRep p α β)
      (mergeRep_step hp α β hsep) k x
    unfold mergeRep at hm
    by_cases hx : cmin p x = cmin p α
    · right
      refine ⟨Or.inl ((cmin_eq_iff_reaches hp _ _).mp hx), ?_⟩
      by_cases hy : cmin p (iterate (transpose p α β) k x) = cmin p α
      · exact Or.inl ((cmin_eq_iff_reaches hp _ _).mp hy)
      · simp only [hx, hy, ↓reduceIte] at hm
        exact Or.inr ((cmin_eq_iff_reaches hp _ _).mp hm)
    · by_cases hy : cmin p (iterate (transpose p α β) k x) = cmin p α
      · simp only [hx, hy, ↓reduceIte] at hm
        right
        exact ⟨Or.inr ((cmin_eq_iff_reaches hp _ _).mp hm.symm),
          Or.inl ((cmin_eq_iff_reaches hp _ _).mp hy)⟩
      · simp only [hx, hy, ↓reduceIte] at hm
        exact Or.inl ((cmin_eq_iff_reaches hp _ _).mp hm.symm)
  · rintro (h | ⟨hx, hy⟩)
    · exact transpose_merge_orbit hp α β hsep h
    · have hab := transpose_merge_markers hp α β hsep
      have hba := hab.symm (transpose_injective hp α β)
      have hxα : Reaches (transpose p α β) x α := by
        rcases hx with hx | hx
        · exact transpose_merge_orbit hp α β hsep hx
        · exact (transpose_merge_orbit hp α β hsep hx).trans hba
      have hαy : Reaches (transpose p α β) α y := by
        rcases hy with hy | hy
        · exact transpose_merge_orbit hp α β hsep (hy.symm hp)
        · exact hab.trans (transpose_merge_orbit hp α β hsep (hy.symm hp))
      exact hxα.trans hαy

end Perm

/-! ### The glued hypermap -/

section Glue

variable {n : Nat} (D : Hypermap n) (α β : Fin n)

/-- Gluing at the darts `α`, `β`: exchange their successors in the rotation; the faces
follow (`face = swap α β ∘ face`). -/
def glueMap : Hypermap n where
  edge := D.edge
  node := transpose D.node α β
  face y := swap α β (D.face y)
  edgeK x := by
    change D.node (swap α β (swap α β (D.face (D.edge x)))) = x
    rw [swap_swap, D.edgeK]

theorem glueMap_node (y : Fin n) : (glueMap D α β).node y = D.node (swap α β y) := rfl

theorem glueMap_face (y : Fin n) : (glueMap D α β).face y = swap α β (D.face y) := rfl

/-- The component label `mergedComponentLabel` is invariant under the glued hypermap. -/
theorem glue_label_step {x y : Fin n} (hs : Linked.Step (glueMap D α β) x y) :
    mergedComponentLabel D α β y = mergedComponentLabel D α β x := by
  have hlab : ∀ z, componentRep D z = componentRep D β →
      mergedComponentLabel D α β z = componentRep D β := by
    intro z hz
    unfold mergedComponentLabel
    by_cases h : componentRep D z = componentRep D α
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]
      exact hz
  have hlabα : ∀ z, componentRep D z = componentRep D α →
      mergedComponentLabel D α β z = componentRep D β := by
    intro z hz
    unfold mergedComponentLabel
    simp only [hz, ↓reduceIte]
  rcases hs with hs | hs | hs
  · exact mergedComponentLabel_step D α β (Or.inl hs)
  · rw [glueMap_node] at hs
    have hstep : componentRep D y = componentRep D (swap α β x) :=
      componentRep_step D (Or.inr (Or.inl hs))
    by_cases hxa : x = α
    · rw [hxa, swap_left] at hstep
      rw [hlab y hstep, hxa, hlabα α rfl]
    · by_cases hxb : x = β
      · rw [hxb, swap_right] at hstep
        rw [hlabα y hstep, hxb, hlab β rfl]
      · rw [swap_other hxa hxb] at hstep
        unfold mergedComponentLabel
        rw [hstep]
  · rw [glueMap_face] at hs
    have hstep : componentRep D (D.face x) = componentRep D x :=
      componentRep_step D (Or.inr (Or.inr rfl))
    by_cases hya : y = α
    · have hf : D.face x = β := by
        have := congrArg (swap α β) hs
        rw [swap_swap, hya, swap_left] at this
        exact this
      rw [hf] at hstep
      rw [hya, hlabα α rfl, hlab x hstep.symm]
    · by_cases hyb : y = β
      · have hf : D.face x = α := by
          have := congrArg (swap α β) hs
          rw [swap_swap, hyb, swap_right] at this
          exact this
        rw [hf] at hstep
        rw [hyb, hlab β rfl, hlabα x hstep.symm]
      · have hf : D.face x = y := by
          have := congrArg (swap α β) hs
          rw [swap_swap, swap_other hya hyb] at this
          exact this
        rw [hf] at hstep
        unfold mergedComponentLabel
        rw [hstep]

theorem glue_label_path {x y : Fin n} (h : LinkedPath (glueMap D α β) x y) :
    mergedComponentLabel D α β y = mergedComponentLabel D α β x := by
  obtain ⟨k, hk⟩ := h
  exact linked_label_invariant _ _ (fun _ _ hs => glue_label_step D α β hs) hk

/-- Darts linked in the glued map are linked before gluing, or both linked to `α` or `β`. -/
theorem glue_linked_cases {x y : Fin n} (h : LinkedPath (glueMap D α β) x y) :
    LinkedPath D x y ∨ ((LinkedPath D x α ∨ LinkedPath D x β) ∧
      (LinkedPath D y α ∨ LinkedPath D y β)) := by
  have he := glue_label_path D α β h
  have hrep : ∀ u v, componentRep D u = componentRep D v → LinkedPath D u v :=
    fun u v huv => linked_of_componentRep_eq D huv
  unfold mergedComponentLabel at he
  by_cases hx : componentRep D x = componentRep D α
  · by_cases hy : componentRep D y = componentRep D α
    · exact Or.inr ⟨Or.inl (hrep _ _ hx), Or.inl (hrep _ _ hy)⟩
    · simp only [hx, hy, ↓reduceIte] at he
      exact Or.inr ⟨Or.inl (hrep _ _ hx), Or.inr (hrep _ _ he)⟩
  · by_cases hy : componentRep D y = componentRep D α
    · simp only [hx, hy, ↓reduceIte] at he
      exact Or.inr ⟨Or.inr (hrep _ _ he.symm), Or.inl (hrep _ _ hy)⟩
    · simp only [hx, hy, ↓reduceIte] at he
      exact Or.inl (hrep _ _ he.symm)

variable {D α β}

/-- Paths before gluing are paths after gluing, once `α` and `β` are linked. -/
theorem glue_path_of_path (hab : LinkedPath (glueMap D α β) α β) {x y : Fin n}
    (h : LinkedPath D x y) : LinkedPath (glueMap D α β) x y := by
  have hba := hab.symm
  obtain ⟨k, hk⟩ := h
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at hk; subst hk; exact LinkedPath.refl _ _
  | succ k ih =>
    rcases (Linked.linked_succ D k x y).mp hk with h' | ⟨z, hz, hs⟩
    · exact ih h'
    · refine (ih hz).trans ?_
      rcases hs with hs | hs | hs
      · exact LinkedPath.step _ (Or.inl hs)
      · by_cases hza : z = α
        · have h1 : (glueMap D α β).node β = y := by
            rw [glueMap_node, swap_right, ← hza, hs]
          rw [hza]
          exact hab.trans (LinkedPath.step _ (Or.inr (Or.inl h1)))
        · by_cases hzb : z = β
          · have h1 : (glueMap D α β).node α = y := by
              rw [glueMap_node, swap_left, ← hzb, hs]
            rw [hzb]
            exact hba.trans (LinkedPath.step _ (Or.inr (Or.inl h1)))
          · exact LinkedPath.step _ (Or.inr (Or.inl (by
              rw [glueMap_node, swap_other hza hzb, hs])))
      · by_cases hya : y = α
        · have h1 : (glueMap D α β).face z = β := by rw [glueMap_face, hs, hya, swap_left]
          rw [hya]
          exact (LinkedPath.step _ (Or.inr (Or.inr h1))).trans hba
        · by_cases hyb : y = β
          · have h1 : (glueMap D α β).face z = α := by rw [glueMap_face, hs, hyb, swap_right]
            rw [hyb]
            exact (LinkedPath.step _ (Or.inr (Or.inr h1))).trans hab
          · exact LinkedPath.step _ (Or.inr (Or.inr (by
              rw [glueMap_face, hs, swap_other hya hyb])))

/-- Gluing two different components merges them into one. -/
theorem glue_components (hab : LinkedPath (glueMap D α β) α β) (hsep : ¬ LinkedPath D α β) :
    (glueMap D α β).componentCount + 1 ≤ D.componentCount := by
  let f : Fin n → Fin n := mergedComponentLabel D α β
  let ys := (componentRoots D).erase (componentRep D α)
  have hroots : (componentRoots D).Nodup := List.Pairwise.filter _ (List.nodup_finRange n)
  have hmemα : componentRep D α ∈ componentRoots D :=
    List.mem_filter.mpr ⟨List.mem_finRange _, componentRep_root D α⟩
  have hlen : ys.length + 1 = D.componentCount := by
    have hl := List.length_erase_of_mem hmemα
    have hpos : 0 < (componentRoots D).length :=
      List.length_pos_iff.mpr (fun he => by simp [he] at hmemα)
    have he := componentRoots_length D
    simp only [ys, hl]
    omega
  have hrepα : componentRep D β ≠ componentRep D α := by
    intro he
    exact hsep (linked_of_componentRep_eq D he.symm)
  have hp : ∀ x, LinkedPath (glueMap D α β) x (f x) := by
    intro x
    have hx : LinkedPath D x (componentRep D x) := ⟨n, componentRep_linked D x⟩
    simp only [f, mergedComponentLabel]
    by_cases h : componentRep D x = componentRep D α
    · simp only [h, ↓reduceIte]
      have hxα : LinkedPath D x α := hx.trans (by
        rw [h]; exact (LinkedPath.symm ⟨n, componentRep_linked D α⟩))
      exact (glue_path_of_path hab hxα).trans
        (hab.trans (glue_path_of_path hab ⟨n, componentRep_linked D β⟩))
    · simp only [h, ↓reduceIte]
      exact glue_path_of_path hab hx
  have hm : ∀ x, f x ∈ ys := by
    intro x
    apply (List.Nodup.mem_erase_iff hroots).mpr
    simp only [f, mergedComponentLabel]
    by_cases h : componentRep D x = componentRep D α
    · simp only [h, ↓reduceIte]
      exact ⟨hrepα, List.mem_filter.mpr ⟨List.mem_finRange _, componentRep_root D β⟩⟩
    · simp only [h, ↓reduceIte]
      exact ⟨h, List.mem_filter.mpr ⟨List.mem_finRange _, componentRep_root D x⟩⟩
  have hnd : ((componentRoots (glueMap D α β)).map f).Nodup := by
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
  rw [List.length_map, componentRoots_length] at hle
  omega

/-- Iterates agree away from the glued darts. -/
theorem iterate_eq_of_closed {p q : Fin n → Fin n} {P : Fin n → Prop}
    (hP : ∀ z, P z → P (p z)) (hq : ∀ z, P z → q z = p z) :
    ∀ j z, P z → iterate q j z = iterate p j z := by
  intro j
  induction j with
  | zero => intro z _; rfl
  | succ j ih =>
    intro z hz
    simp only [iterate]
    rw [hq z hz]
    exact ih _ (hP z hz)

end Glue

end STACS2027
