module

public import MinorFree.Biclique
public import Complexity.Planarity
import Complexity.Planar.Hypermap

/-!
# `K_{2,r}` is planar

A planar embedding of `K_{2,r}` (`biclique r`) in the sense of the registered foundation's
`Complexity.PlanarGraph`, for every `r`. The edge `2j` of `biclique r` is `(0, j + 2)` and the
edge `2j + 1` is `(1, j + 2)`, so the half-edge `4j` lies at `0`, `4j + 2` at `1`, and `4j + 1`,
`4j + 3` at `j + 2`. The rotation at `0` lists `0, 4, …, 4(r − 1)` in this order, the rotation
at `1` lists `2, 6, …, 4(r − 1) + 2` in the reverse order, and each middle vertex swaps its two
half-edges. The face of `4j` is `4j, 4j + 3, 4j' + 2, 4j' + 1` with `j' = (j + 1) mod r`:
for `r ≥ 2` the `r` quadrilaterals `0, j + 2, 1, j' + 2`, for `r = 1` (the path `0, 2, 1`) the
one face around the path. With one component, Euler's formula `2 · 1 + 4r = 2r + (r + 2) + r`
holds for every `r ≥ 1`; `r = 0` is the empty graph. The proof uses only lower bounds on the
three cycle counts and an upper bound on the component count
(`Complexity.Planar.planar_of_bounds`).

`biclique_planar_family` states Lemma 23 in full: planarity together with the counts and cost bounds of
`MinorFree.Biclique`.
-/

@[expose] public section
namespace STACS2027

namespace BicliqueEmbedding
open Complexity Complexity.Planar

/-! ## The three permutations, on `Nat` -/

/-- The `edge` permutation: half-edges `2i` and `2i + 1` are swapped. -/
def ed (d : Nat) : Nat := cond (Nat.beq (d % 2) 0) (d + 1) (d - 1)

/-- The `node` permutation of the embedding of `K_{2,r}`: `4j ↦ 4(j + 1)` (cyclically) at
vertex `0`, `4j + 2 ↦ 4(j − 1) + 2` (cyclically) at vertex `1`, and `4j + 1 ↔ 4j + 3`. -/
def nd (r d : Nat) : Nat :=
  if d % 4 = 0 then (if d + 4 < 4 * r then d + 4 else 0)
  else if d % 4 = 1 then d + 2
  else if d % 4 = 2 then (if d < 4 then 4 * r - 2 else d - 4)
  else d - 2

/-- The `face` permutation, `node⁻¹ ∘ edge`: the face of `4j` is
`4j, 4j + 3, 4(j + 1) + 2, 4(j + 1) + 1` (indices modulo `r`). -/
def fc (r d : Nat) : Nat :=
  if d % 4 = 0 then d + 3
  else if d % 4 = 1 then (if d < 4 then 4 * r - 4 else d - 5)
  else if d % 4 = 2 then d - 1
  else (if d + 1 < 4 * r then d + 3 else 2)

theorem ed_eq (d : Nat) : ed d = if d % 2 = 0 then d + 1 else d - 1 := by
  unfold ed
  rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [h]

theorem ed_lt {r d : Nat} (hd : d < 4 * r) : ed d < 4 * r := by
  rw [ed_eq]; split <;> omega

theorem nd_lt {r d : Nat} (hd : d < 4 * r) : nd r d < 4 * r := by
  unfold nd; (repeat' split) <;> omega

theorem fc_lt {r d : Nat} (hd : d < 4 * r) : fc r d < 4 * r := by
  unfold fc; (repeat' split) <;> omega

theorem nd_fc_ed {r d : Nat} (hd : d < 4 * r) : nd r (fc r (ed d)) = d := by
  rw [ed_eq]; unfold fc nd; (repeat' split) <;> omega

/-- The embedding of `K_{2,r}` as a hypermap on `N = 4r` darts. -/
def bicliqueMap (r : Nat) {N : Nat} (hN : N = 4 * r) : Hypermap N where
  edge d := ⟨ed d.val, by have := ed_lt (r := r) (d := d.val) (by omega); omega⟩
  node d := ⟨nd r d.val, by have := nd_lt (r := r) (d := d.val) (by omega); omega⟩
  face d := ⟨fc r d.val, by have := fc_lt (r := r) (d := d.val) (by omega); omega⟩
  edgeK d := Fin.ext (nd_fc_ed (by omega))

/-! ## Half-edges and the node condition -/

theorem biclique_succ (r : Nat) : biclique (r + 1) = biclique r ++ [(0, r + 2), (1, r + 2)] := by
  simp [biclique, List.range_succ]

/-- Edge `i` of `K_{2,r}` is `(i mod 2, ⌊i/2⌋ + 2)`. -/
theorem biclique_getElem? {r i : Nat} (hi : i < 2 * r) :
    (biclique r)[i]? = some (i % 2, i / 2 + 2) := by
  induction r with
  | zero => omega
  | succ r ih =>
    rw [biclique_succ]
    by_cases h : i < 2 * r
    · rw [List.getElem?_append_left (by rw [biclique_length]; exact h), ih h]
    · rw [List.getElem?_append_right (by rw [biclique_length]; omega), biclique_length]
      obtain rfl | rfl : i = 2 * r ∨ i = 2 * r + 1 := by omega
      · simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq]; omega
      · simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq, Prod.mk.injEq]; omega

/-- The vertex of half-edge `d`: `0` for `4j`, `1` for `4j + 2`, `j + 2` for `4j + 1`, `4j + 3`. -/
def vert (d : Nat) : Nat := if d % 2 = 0 then d / 2 % 2 else d / 4 + 2

theorem halfEdgeEnd_biclique {r d : Nat} (hd : d < 4 * r) :
    halfEdgeEnd (biclique r) d = some (vert d) := by
  unfold halfEdgeEnd vert
  rw [biclique_getElem? (by omega)]
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · simp [h]
  · simp only [h, Option.map_some, Option.some.injEq]
    simp only [cond, Nat.one_ne_zero, ↓reduceIte]
    omega

theorem vert_nd {r d : Nat} (hd : d < 4 * r) : vert (nd r d) = vert d := by
  unfold vert nd; (repeat' split) <;> omega

theorem iterate_nd_zero {r : Nat} :
    ∀ k j, j + k < r → iterate (nd r) k (4 * j) = 4 * (j + k) := by
  intro k
  induction k with
  | zero => intro j _; rfl
  | succ k ih =>
    intro j hj
    have : nd r (4 * j) = 4 * (j + 1) := by unfold nd; (repeat' split) <;> omega
    show iterate (nd r) k (nd r (4 * j)) = _
    rw [this, ih (j + 1) (by omega)]
    congr 1; omega

theorem iterate_nd_one {r : Nat} :
    ∀ k j, k ≤ j → iterate (nd r) k (4 * j + 2) = 4 * (j - k) + 2 := by
  intro k
  induction k with
  | zero => intro j _; rfl
  | succ k ih =>
    intro j hj
    have : nd r (4 * j + 2) = 4 * (j - 1) + 2 := by unfold nd; (repeat' split) <;> omega
    show iterate (nd r) k (nd r (4 * j + 2)) = _
    rw [this, ih (j - 1) (by omega)]
    congr 1; omega

theorem reach_trans {f : Nat → Nat} {a b c : Nat} (h1 : ∃ k, iterate f k a = b)
    (h2 : ∃ k, iterate f k b = c) : ∃ k, iterate f k a = c := by
  obtain ⟨k1, h1⟩ := h1
  obtain ⟨k2, h2⟩ := h2
  exact ⟨k1 + k2, by rw [iterate_add, h1, h2]⟩

/-- The rotation at vertex `0` is one cycle. -/
theorem reach_zero {r j : Nat} (hj : j < r) :
    (∃ k, iterate (nd r) k (4 * j) = 0) ∧ ∃ k, iterate (nd r) k 0 = 4 * j := by
  refine ⟨⟨r - 1 - j + 1, ?_⟩, ⟨j, ?_⟩⟩
  · rw [iterate_add, iterate_nd_zero _ _ (by omega)]
    show nd r _ = 0
    unfold nd; (repeat' split) <;> omega
  · have := iterate_nd_zero (r := r) j 0 (by omega)
    simpa using this

/-- The rotation at vertex `1` is one cycle. -/
theorem reach_one {r j : Nat} (hj : j < r) :
    (∃ k, iterate (nd r) k (4 * j + 2) = 2) ∧ ∃ k, iterate (nd r) k 2 = 4 * j + 2 := by
  refine ⟨⟨j, by rw [iterate_nd_one _ _ (Nat.le_refl j), Nat.sub_self]⟩,
    ⟨1 + (r - 1 - j), ?_⟩⟩
  have h1 : iterate (nd r) 1 2 = 4 * (r - 1) + 2 := by
    show nd r 2 = _
    unfold nd; (repeat' split) <;> omega
  rw [iterate_add, h1, iterate_nd_one _ _ (by omega)]
  congr 1; omega

/-- Two half-edges at the same vertex lie in the same node cycle. -/
theorem nd_reach {r d d' : Nat} (hd : d < 4 * r) (hd' : d' < 4 * r) (h : vert d = vert d') :
    ∃ k, iterate (nd r) k d = d' := by
  unfold vert at h
  have hcases : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · have h0' : d' % 4 = 0 := by (repeat' split at h) <;> omega
    obtain ⟨k1, hk1⟩ := (reach_zero (r := r) (j := d / 4) (by omega)).1
    obtain ⟨k2, hk2⟩ := (reach_zero (r := r) (j := d' / 4) (by omega)).2
    refine reach_trans (b := 0) ⟨k1, ?_⟩ ⟨k2, ?_⟩
    · rw [show d = 4 * (d / 4) by omega]; exact hk1
    · rw [hk2]; omega
  · have : d' = d ∨ d' = d + 2 := by (repeat' split at h) <;> omega
    rcases this with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, show nd r d = d + 2 by unfold nd; (repeat' split) <;> omega⟩
  · have h2' : d' % 4 = 2 := by (repeat' split at h) <;> omega
    obtain ⟨k1, hk1⟩ := (reach_one (r := r) (j := d / 4) (by omega)).1
    obtain ⟨k2, hk2⟩ := (reach_one (r := r) (j := d' / 4) (by omega)).2
    refine reach_trans (b := 2) ⟨k1, ?_⟩ ⟨k2, ?_⟩
    · rw [show d = 4 * (d / 4) + 2 by omega]; exact hk1
    · rw [hk2]; omega
  · have : d' = d ∨ d' = d - 2 := by (repeat' split at h) <;> omega
    rcases this with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, show nd r d = d - 2 by unfold nd; (repeat' split) <;> omega⟩

theorem iterate_node_val (r : Nat) {N : Nat} (hN : N = 4 * r) (k : Nat) (d : Fin N) :
    (iterate (bicliqueMap r hN).node k d).val = iterate (nd r) k d.val := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => exact ih _

theorem iterate_nd_vert {r : Nat} :
    ∀ k x, x < 4 * r → iterate (nd r) k x < 4 * r ∧ vert (iterate (nd r) k x) = vert x := by
  intro k
  induction k with
  | zero => intro x hx; exact ⟨hx, rfl⟩
  | succ k ih =>
    intro x hx
    obtain ⟨h1, h2⟩ := ih (nd r x) (nd_lt hx)
    exact ⟨h1, h2.trans (vert_nd hx)⟩

/-! ## Euler's formula -/

/-- A half-edge at vertex `v`: `0` at `0`, `2` at `1`, `4(v − 2) + 1` at `v ≥ 2`. -/
def dartOf (v : Nat) : Nat := if v = 0 then 0 else if v = 1 then 2 else 4 * (v - 2) + 1

/-- The face of a half-edge: `j` for the face of `4j`. -/
def faceOf (r d : Nat) : Nat :=
  if d % 4 = 0 ∨ d % 4 = 3 then d / 4 else if d < 4 then r - 1 else d / 4 - 1

theorem faceOf_fc {r d : Nat} (hd : d < 4 * r) : faceOf r (fc r d) = faceOf r d := by
  unfold faceOf fc; (repeat' split) <;> omega

theorem countP_range_eq_zero (N : Nat) : (List.range N).countP (fun d => decide (d = 0)) ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.countP_append]
    rcases N with _ | N
    · simp
    · simpa using ih

/-- The embedding of `K_{2,r}` is planar. -/
theorem bicliqueMap_planar (r : Nat) (hN : 2 * (biclique r).length = 4 * r) :
    (bicliqueMap r hN).Planar := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · apply planar_of_bounds _ 0 0 0 0 (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) ?_ (by omega)
    unfold Hypermap.componentCount
    rw [Nat.le_zero, List.countP_eq_zero]
    intro x _
    exact absurd x.isLt (by omega)
  apply planar_of_bounds _ (2 * r) (r + 2) r 1 ?_ ?_ ?_ ?_ (by omega)
  · -- `2r` edges
    have := cycleCount_graphEdge_ge (E := (biclique r).length) (edge := (bicliqueMap r hN).edge)
      (fun _ => rfl)
    have hl := biclique_length r
    omega
  · -- `r + 2` nodes: the half-edges `dartOf v` at the vertices `v < r + 2`
    let xs : List (Fin (2 * (biclique r).length)) := (List.range (r + 2)).pmap
      (fun v hv => ⟨dartOf v, by unfold dartOf; (repeat' split) <;> omega⟩)
      (fun _ hv => List.mem_range.mp hv)
    have hmap : xs.map (fun x => vert x.val) = List.range (r + 2) := by
      simp only [xs, List.map_pmap]
      rw [List.pmap_eq_map]
      conv => rhs; rw [← List.map_id (List.range (r + 2))]
      apply List.map_inj_left.mpr
      intro v hv
      have := List.mem_range.mp hv
      unfold vert dartOf; (repeat' split) <;> simp_all <;> omega
    have := cycleCount_ge (bicliqueMap r hN).node (fun x => vert x.val)
      (fun x => vert_nd (by omega)) xs (by rw [hmap]; exact List.nodup_range)
    simpa [xs] using this
  · -- `r` faces: the face of `4j` for `j < r`
    let xs : List (Fin (2 * (biclique r).length)) := (List.range r).pmap
      (fun j hj => ⟨4 * j, by omega⟩) (fun _ hj => List.mem_range.mp hj)
    have hmap : xs.map (fun x => faceOf r x.val) = List.range r := by
      simp only [xs, List.map_pmap]
      rw [List.pmap_eq_map]
      conv => rhs; rw [← List.map_id (List.range r)]
      apply List.map_inj_left.mpr
      intro j _
      unfold faceOf; (repeat' split) <;> simp_all <;> omega
    have := cycleCount_ge (bicliqueMap r hN).face (fun x => faceOf r x.val)
      (fun x => faceOf_fc (by omega)) xs (by rw [hmap]; exact List.nodup_range)
    simpa [xs] using this
  · -- one component: every half-edge other than `0` reaches a smaller one
    have hc := componentCount_le (bicliqueMap r hN) (fun x => decide (x.val = 0)) ?_
    · have hR := countP_finRange_val (n := 2 * (biclique r).length) (fun d => decide (d = 0))
      have := countP_range_eq_zero (2 * (biclique r).length)
      omega
    intro x hx
    have hx0 : x.val ≠ 0 := by simpa using hx
    have hxl : x.val < 4 * r := by omega
    have hcases : x.val % 4 = 0 ∨ x.val % 4 = 2 ∨ x.val % 2 = 1 := by omega
    rcases hcases with h0 | h2 | h1
    · refine ⟨(bicliqueMap r hN).face ((bicliqueMap r hN).edge x), ?_, 2,
        Linked.linked_step _ (Linked.linked_step _ (Linked.linked_refl _ 0 x) (Or.inl rfl))
          (Or.inr (Or.inr rfl))⟩
      show fc r (ed x.val) < x.val
      rw [ed_eq]; unfold fc; (repeat' split) <;> omega
    · refine ⟨(bicliqueMap r hN).face x, ?_, 1,
        Linked.linked_step _ (Linked.linked_refl _ 0 x) (Or.inr (Or.inr rfl))⟩
      show fc r x.val < x.val
      unfold fc; (repeat' split) <;> omega
    · refine ⟨(bicliqueMap r hN).edge x, ?_, 1,
        Linked.linked_step _ (Linked.linked_refl _ 0 x) (Or.inl rfl)⟩
      show ed x.val < x.val
      rw [ed_eq]; split <;> omega

end BicliqueEmbedding

open BicliqueEmbedding in
/-- **`K_{2,r}` is planar**, in the sense of the registered foundation: a planar hypermap on its
`4r` half-edges whose `edge` permutation pairs the two ends of each edge and whose `node` cycles
are the sets of half-edges at each vertex. -/
theorem biclique_planar (r : Nat) : Complexity.PlanarGraph (biclique r) := by
  have hN : 2 * (biclique r).length = 4 * r := by rw [biclique_length]; omega
  refine ⟨bicliqueMap r hN, fun _ => rfl, ?_, bicliqueMap_planar r hN⟩
  intro d d'
  have hd : d.val < 4 * r := by omega
  have hd' : d'.val < 4 * r := by omega
  rw [halfEdgeEnd_biclique hd, halfEdgeEnd_biclique hd']
  constructor
  · rintro ⟨k, rfl⟩
    rw [iterate_node_val, (iterate_nd_vert k d.val hd).2]
  · intro h
    obtain ⟨k, hk⟩ := nd_reach hd hd' (Option.some.inj h)
    exact ⟨k, Fin.ext (by rw [iterate_node_val]; exact hk)⟩

/-- **Lemma 23.** `K_{2,r}` is planar (`Complexity.PlanarGraph`, the registered foundation's
hypermap definition), has `n = r + 2` vertices, `m = 2r` edges and `binom(r, 2)` four-cycles,
and every four-cycle assignment of it has cost between `(n − 2)(n − 3)(n − 5)/4` and
`(n − 2)(n − 3)(n − 4)`: a family of planar graphs whose optimal four-cycle assignment cost is
`Θ(n³)`. -/
theorem biclique_planar_family (r : Nat) :
    Complexity.PlanarGraph (biclique r) ∧
      (biclique r).length = 2 * r ∧ (cycles (biclique r) 4).length = pairCount r ∧
      ∀ ps, ValidChoices ((cycles (biclique r) 4).map selectedOptions) ps →
        r * (r - 1) * (r - 3) ≤ 4 * cost ps ∧ cost ps ≤ r * (r - 1) * (r - 2) :=
  ⟨biclique_planar r, biclique_length r, biclique_cycle_count r,
    fun _ hv => ⟨biclique_cost_lower hv, biclique_cost_upper hv⟩⟩

end STACS2027
