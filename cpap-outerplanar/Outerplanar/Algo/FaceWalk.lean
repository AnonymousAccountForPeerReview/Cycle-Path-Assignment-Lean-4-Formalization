module

public import Outerplanar.Algo.PolyEnum
import Mathlib.Tactic

/-!
# The polygon solver: walking along a face

The random-access machine computes the face vertices of a segment `s = (a, b)` of a polygon
`pg` by a walk along the face: from `a` to its largest neighbour below `b` (`predNb`), then
repeatedly to the largest neighbour (`lastNb`) until `b` (`walkTo`, `faceWalk`).

* `mem_nbP`, `nbP_pairwise`: `nbP pg n x` lists the neighbours of `x`, in increasing order;
* `predNb_eq`: the face vertex after `a` is the largest neighbour of `a` below `b` (a larger
  one `y < b` would give a segment `(a, y)` strictly inside `s` with that face vertex strictly
  inside);
* `lastNb_eq`: the face vertex after a face vertex `x ≠ a` is the largest neighbour of `x`
  (a larger neighbour `y ≤ b` would give a segment `(x, y)` strictly inside `s` with the next
  face vertex strictly inside; a neighbour `y > b` would cross `s`);
* `faceWalk_eq`: the walk lists the face vertices, `faceWalk pg n s = faceVerts pg n s`.
-/

@[expose] public section

namespace STACS2027.Poly

open IsPolygon

/-- The largest neighbour of `x` (or `x`). -/
def lastNb (pg : Graph) (n x : ℕ) : ℕ := (Poly.nbP pg n x).getLastD x

/-- The largest neighbour of `a` below `b` (or `a`). -/
def predNb (pg : Graph) (n a b : ℕ) : ℕ :=
  ((Poly.nbP pg n a).filter fun y => decide (y < b)).getLastD a

/-- Walking along the face from `x` to `b` by largest neighbours, with fuel. -/
def walkTo (pg : Graph) (n b : ℕ) : ℕ → ℕ → List ℕ
  | 0, x => [x]
  | f + 1, x => if x = b then [x] else x :: walkTo pg n b f (lastNb pg n x)

/-- The face vertices of the segment `s`, by the walk along its face. -/
def faceWalk (pg : Graph) (n : ℕ) (s : ℕ × ℕ) : List ℕ :=
  s.1 :: walkTo pg n s.2 n (predNb pg n s.1 s.2)

variable {pg : Graph} {n : ℕ}

/-! ### Neighbour lists -/

/-- `nbP pg n x` lists the neighbours of `x` below `n`. -/
theorem mem_nbP {x z : ℕ} : z ∈ nbP pg n x ↔ z < n ∧ Adj pg x z := by
  simp [nbP]

/-- On a polygon, `nbP pg n x` lists the neighbours of `x`. -/
theorem mem_nbP_iff (hP : IsPolygon pg n) {x z : ℕ} : z ∈ nbP pg n x ↔ Adj pg x z := by
  rw [mem_nbP]
  exact ⟨fun h => h.2, fun h => ⟨(hP.lt_of_adj h).2, h⟩⟩

/-- `nbP pg n x` is increasing. -/
theorem nbP_pairwise (x : ℕ) : (nbP pg n x).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

/-- The last entry of an increasing list: an entry at least every entry. -/
theorem getLastD_eq_of_le {l : List ℕ} (hs : l.Pairwise (· < ·)) {y : ℕ} (hy : y ∈ l)
    (hle : ∀ z ∈ l, z ≤ y) (d : ℕ) : l.getLastD d = y := by
  rw [List.getLastD_eq_getLast?, getLast?_eq_of_le hs hy hle, Option.getD_some]

/-! ### The next face vertex -/

/-- **The second face vertex** of a segment `s` is the largest neighbour of `s.1` below
`s.2`. -/
theorem predNb_eq (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ segs pg n) {y : ℕ}
    (hi : [s.1, y] <:+: faceVerts pg n s) : predNb pg n s.1 s.2 = y := by
  have hs' := hP.mem_segs.mp hs
  obtain ⟨hx, hy, hxy, hgap⟩ := (infix_pair_iff faceVerts_pairwise).mp hi
  have hy' := mem_faceVerts.mp hy
  have hadj := hP.adj_of_infix_faceVerts hs hi
  have hys : y < s.2 := by
    refine lt_of_le_of_ne hy'.2.1 fun he => ?_
    subst he
    have := (hP.child_iff (s := s) (t := s)).mpr ⟨hi, hs'.2⟩
    exact this.2.1 rfl
  apply getLastD_eq_of_le ((nbP_pairwise _).filter _)
  · rw [List.mem_filter, mem_nbP_iff hP, decide_eq_true_eq]
    exact ⟨hadj, hys⟩
  · intro z hz
    rw [List.mem_filter, mem_nbP_iff hP, decide_eq_true_eq] at hz
    by_contra hzy
    have hz2 : s.1 + 2 ≤ z := by omega
    have hseg : (s.1, z) ∈ segs pg n := hP.mem_segs.mpr ⟨hz.1, hz2⟩
    exact hy'.2.2 (s.1, z) hseg ⟨le_rfl, by simp only; omega⟩
      (fun he => by rw [← he] at hz; simp at hz) ⟨hxy, by simp only; omega⟩

/-- **The next face vertex**: after a face vertex `x ≠ s.1` of a segment `s`, the next face
vertex is the largest neighbour of `x`. -/
theorem lastNb_eq (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ segs pg n) {x y : ℕ}
    (hi : [x, y] <:+: faceVerts pg n s) (hxs : x ≠ s.1) : lastNb pg n x = y := by
  have hs' := hP.mem_segs.mp hs
  obtain ⟨hx, hy, hxy, hgap⟩ := (infix_pair_iff faceVerts_pairwise).mp hi
  have hx' := mem_faceVerts.mp hx
  have hy' := mem_faceVerts.mp hy
  have hadj := hP.adj_of_infix_faceVerts hs hi
  apply getLastD_eq_of_le (nbP_pairwise _) ((mem_nbP_iff hP).mpr hadj)
  intro z hz
  rw [mem_nbP_iff hP] at hz
  by_contra hzy
  by_cases hzb : s.2 < z
  · exact hP.noncross (show s.1 < x by omega) (show x < s.2 by omega) hzb hs'.1 hz
  · have hseg : (x, z) ∈ segs pg n := hP.mem_segs.mpr ⟨hz, by simp only; omega⟩
    exact hy'.2.2 (x, z) hseg ⟨hx'.1, by simp only; omega⟩
      (fun he => hxs (by rw [← he])) ⟨hxy, by simp only; omega⟩

/-! ### The walk -/

/-- The walk from a face vertex `x ≠ s.1` with enough fuel lists the face vertices from `x`
on. -/
theorem walkTo_eq (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ segs pg n) :
    ∀ (l pre : List ℕ) (x f : ℕ), faceVerts pg n s = pre ++ x :: l → pre ≠ [] →
      l.length ≤ f → walkTo pg n s.2 f x = x :: l
  | [], pre, x, f, h, _, _ => by
    have hs' := hP.mem_segs.mp hs
    have hl := faceVerts_getLast? (g := pg) (n := n) (s := s) (by omega)
    rw [h, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hl
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    cases f with
    | zero => rfl
    | succ f => simp [walkTo]
  | y :: l, pre, x, f, h, hpre, hf => by
    have hpw : (pre ++ x :: y :: l).Pairwise (· < ·) := h ▸ faceVerts_pairwise
    have hxy : x < y := by
      have := (List.pairwise_append.mp hpw).2.1
      exact (List.pairwise_cons.mp this).1 y (by simp)
    have hyb : y ≤ s.2 := (mem_faceVerts.mp (h ▸ (by simp : y ∈ pre ++ x :: y :: l))).2.1
    have hxs : x ≠ s.1 := by
      obtain ⟨p, pre', rfl⟩ : ∃ p pre', pre = p :: pre' := by
        cases pre with
        | nil => exact absurd rfl hpre
        | cons p pre' => exact ⟨p, pre', rfl⟩
      have hhead : p = s.1 := by
        have hs' := hP.mem_segs.mp hs
        have := faceVerts_head? (g := pg) (n := n) (s := s) (by omega)
        rw [h] at this
        simpa using this
      have := (List.pairwise_cons.mp hpw).1 x (by simp)
      omega
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hi : [x, y] <:+: faceVerts pg n s := ⟨pre, l, by rw [h]; simp⟩
    rw [walkTo, ite_eq_right (by omega), lastNb_eq hP hs hi hxs,
      walkTo_eq hP hs l (pre ++ [x]) y f (by rw [h]; simp) (by simp) (by simp at hf; omega)]

/-- **The face walk lists the face vertices** of a segment. -/
theorem faceWalk_eq (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ segs pg n) :
    faceWalk pg n s = faceVerts pg n s := by
  have hs' := hP.mem_segs.mp hs
  have h3 := hP.three_le_length_faceVerts hs
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp
    (faceVerts_head? (g := pg) (n := n) (s := s) (by omega))
  obtain ⟨y, rest', rfl⟩ : ∃ y rest', rest = y :: rest' := by
    cases rest with
    | nil => rw [hrest] at h3; simp at h3
    | cons y rest' => exact ⟨y, rest', rfl⟩
  have hi : [s.1, y] <:+: faceVerts pg n s := ⟨[], rest', by rw [hrest]; simp⟩
  have hlen : (faceVerts pg n s).length ≤ s.2 + 1 - s.1 := by
    unfold faceVerts
    exact (List.length_filter_le _ _).trans (by simp)
  have hn := (hP.lt_of_adj hs'.1).2
  rw [faceWalk, predNb_eq hP hs hi, hrest,
    walkTo_eq hP hs rest' [s.1] y n (by rw [hrest]; simp) (by simp)
      (by rw [hrest] at hlen; simp at hlen; omega)]

end STACS2027.Poly
