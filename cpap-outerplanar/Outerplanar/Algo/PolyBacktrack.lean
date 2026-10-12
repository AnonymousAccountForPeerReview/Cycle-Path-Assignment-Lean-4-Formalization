module

public import Outerplanar.Algo.PolyDP
public import Outerplanar.Algo.TreeDPArgmin
import Mathlib.Tactic

/-!
# The backtracking of the polygon solver chooses an optimal assignment

`backtrack` processes the segments top-down (a `foldr` over `segOrder`, which lists smaller
segments first, so every segment is processed before its children). With `(A, B) :=
backtrack`, every segment `s` gets `B s = argTab s (A s)`, and each child `w` of `s` gets
`A w = childIdx s w (A s, B s)` (`backtrack_inv`). The chosen values `chosen` give each
cycle its digit `valOf` in the `β` of its top segment; they are represented by `B s` on the
cycles with top `s` (`map_topIdx_chosen`) and, by induction down the segment tree, by `A s`
on the boundary cycles of `s` (`map_bnd_chosen`). By `tabArg_spec` they attain the minimum
of the dynamic program at every segment, so their total cost is the optimum
(`total_chosen`, `isMinCost_total_chosen`).
-/

@[expose] public section

namespace STACS2027.Poly

open IsPolygon TreeDP

variable {pg : Graph} {n k : ℕ}

/-! ### The backtracking steps -/

variable (pg n k) in
/-- One step of `backtrack`, at the segment `s`. -/
def btStep (s : ℕ × ℕ) (ab : (ℕ × ℕ → ℕ) × (ℕ × ℕ → ℕ)) : (ℕ × ℕ → ℕ) × (ℕ × ℕ → ℕ) :=
  let α := ab.1 s
  let β := argTab pg n k s α
  let nb := (bnd pg n k s).length
  let nc := (topIdx pg n k s).length
  ((childSegs pg n s).foldl (fun f w =>
    Function.update f w (childIdx pg n k s w (cfg k nb α ++ cfg k nc β))) ab.1,
   Function.update ab.2 s β)

variable (pg n k) in
theorem backtrack_eq :
    backtrack pg n k = (segOrder pg n).foldr (btStep pg n k) (fun _ => 0, fun _ => 0) := rfl

theorem foldl_update_apply {α β : Type*} [DecidableEq α] (g : α → β) :
    ∀ (l : List α) (f : α → β) (x : α),
      (l.foldl (fun f w => Function.update f w (g w)) f) x = if x ∈ l then g x else f x
  | [], f, x => by simp
  | w :: l, f, x => by
    rw [List.foldl_cons, foldl_update_apply g l]
    by_cases hx : x ∈ l
    · simp [hx]
    · by_cases hw : x = w
      · subst hw; simp
      · simp [hx, hw]

variable (pg n k) in
/-- The backtracking invariant at `s`: `B s` is the minimizing configuration of `A s`, and
the children of `s` get the restriction of `(A s, B s)`. -/
def BtInv (ab : (ℕ × ℕ → ℕ) × (ℕ × ℕ → ℕ)) (s : ℕ × ℕ) : Prop :=
  ab.2 s = argTab pg n k s (ab.1 s) ∧ ∀ w ∈ childSegs pg n s,
    ab.1 w = childIdx pg n k s w
      (cfg k (bnd pg n k s).length (ab.1 s) ++ cfg k (topIdx pg n k s).length (ab.2 s))

section Facts

variable {hP : IsPolygon pg n} {hk : 3 ≤ k}

theorem childSegs_size_lt (F : PolyFacts hP hk) {s w : ℕ × ℕ} (hs : s ∈ segs pg n)
    (hw : w ∈ childSegs pg n s) : w.2 - w.1 < s.2 - s.1 := by
  obtain ⟨hws, hch⟩ := (F.mem_childSegs s hs w).mp hw
  exact hP.child_size_lt hws hch

/-- A segment is a child of at most one segment. -/
theorem childSegs_unique (F : PolyFacts hP hk) {s t w : ℕ × ℕ} (hs : s ∈ segs pg n)
    (ht : t ∈ segs pg n) (hws : w ∈ childSegs pg n s) (hwt : w ∈ childSegs pg n t) : s = t := by
  obtain ⟨hw, hc1⟩ := (F.mem_childSegs s hs w).mp hws
  obtain ⟨-, hc2⟩ := (F.mem_childSegs t ht w).mp hwt
  have hlt : w.1 < w.2 := by have := (hP.mem_segs.mp hw).2; omega
  rcases hP.nested_of_within hs ht hlt hc1.2.1 hc2.2.1 with h | h
  · rcases hc2.2.2 s hs hc1.2.1 h with h' | h'
    · exact absurd h'.symm hc1.1
    · exact h'
  · rcases hc1.2.2 t ht hc2.2.1 h with h' | h'
    · exact absurd h'.symm hc2.1
    · exact h'.symm

/-- **The backtracking invariant** holds at every segment of a list processed by `foldr`,
when the list is duplicate-free and sorted by size. -/
theorem foldr_btInv (F : PolyFacts hP hk) :
    ∀ L : List (ℕ × ℕ), L.Nodup → L.Pairwise (fun s t => s.2 - s.1 ≤ t.2 - t.1) →
      (∀ s ∈ L, s ∈ segs pg n) →
      ∀ s ∈ L, BtInv pg n k (L.foldr (btStep pg n k) (fun _ => 0, fun _ => 0)) s
  | [], _, _, _ => by simp
  | s :: L, hnd, hsort, hsegs => by
    obtain ⟨hsL, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hsz, hsort'⟩ := List.pairwise_cons.mp hsort
    have hs := hsegs s (by simp)
    have ih := foldr_btInv F L hnd' hsort' (fun t ht => hsegs t (by simp [ht]))
    rw [List.foldr_cons]
    set ab := L.foldr (btStep pg n k) (fun _ => 0, fun _ => 0)
    set vals := cfg k (bnd pg n k s).length (ab.1 s) ++
      cfg k (topIdx pg n k s).length (argTab pg n k s (ab.1 s))
    have h1 : ∀ x, (btStep pg n k s ab).1 x =
        if x ∈ childSegs pg n s then childIdx pg n k s x vals else ab.1 x :=
      foldl_update_apply _ _ _
    have h2 : ∀ x, (btStep pg n k s ab).2 x = Function.update ab.2 s (argTab pg n k s (ab.1 s)) x :=
      fun _ => rfl
    have hss : s ∉ childSegs pg n s := fun h => by
      have := childSegs_size_lt F hs h; omega
    intro t ht
    rcases List.mem_cons.mp ht with rfl | htL
    · refine ⟨?_, fun w hw => ?_⟩
      · rw [h2, h1, Function.update_self, ite_eq_right_iff.mpr (fun h => absurd h hss)]
      · rw [h1, h1, h2, Function.update_self, ite_eq_left_iff.mpr (fun h => absurd hw h),
          ite_eq_right_iff.mpr (fun h => absurd h hss)]
    · have hts : t ≠ s := fun h => hsL (h ▸ htL)
      have htc : t ∉ childSegs pg n s := fun h => by
        have := childSegs_size_lt F hs h
        have := hsz t htL
        omega
      have hwc : ∀ w ∈ childSegs pg n t, w ∉ childSegs pg n s :=
        fun w hw h => hts (childSegs_unique F (hsegs t ht) hs hw h)
      obtain ⟨i1, i2⟩ := ih t htL
      refine ⟨?_, fun w hw => ?_⟩
      · rw [h2, h1, Function.update_of_ne hts, ite_eq_right_iff.mpr (fun h => absurd h htc)]
        exact i1
      · rw [h1, h1, h2, Function.update_of_ne hts, ite_eq_right_iff.mpr (fun h => absurd h htc),
          ite_eq_right_iff.mpr (fun h => absurd h (hwc w hw))]
        exact i2 w hw

/-- **The backtracking invariant** at every segment. -/
theorem backtrack_inv (F : PolyFacts hP hk) {s : ℕ × ℕ} (hs : s ∈ segs pg n) :
    BtInv pg n k (backtrack pg n k) s := by
  rw [backtrack_eq]
  exact foldr_btInv F _ F.segOrder_nodup F.segOrder_size
    (fun t ht => (F.mem_segOrder t).mp ht) s ((F.mem_segOrder s).mpr hs)

end Facts

/-! ### The chosen values -/

variable (pg n) in
/-- The values chosen by the backtracking: each convex cycle takes its omitted index
`valOf`. -/
def chosen (hk0 : 0 < k) (x : CycVar pg n k) : Fin k :=
  ⟨valOf pg n k (idx x), Nat.mod_lt _ hk0⟩

section Facts

variable {hP : IsPolygon pg n} {hk : 3 ≤ k}

theorem vOf_chosen (F : PolyFacts hP hk) (hk0 : 0 < k) {i : ℕ} (hi : i < (pool pg n k).length) :
    vOf (chosen pg n hk0) i = valOf pg n k i := by
  rw [vOf_eq _ (cyc_mem F hi)]
  simp only [chosen, idx_cyc F hi]

/-- On the cycles with top `s`, the chosen values are represented by `B s`. -/
theorem map_topIdx_chosen (F : PolyFacts hP hk) (hk0 : 0 < k) (s : ℕ × ℕ) :
    (topIdx pg n k s).map (vOf (chosen pg n hk0)) =
      cfg k (topIdx pg n k s).length ((backtrack pg n k).2 s) := by
  apply List.ext_getElem (by simp)
  intro q h1 h2
  have hq : q < (topIdx pg n k s).length := by simpa using h1
  have hi := mem_topIdx.mp (List.getElem_mem hq)
  simp only [List.getElem_map, getElem_cfg]
  rw [vOf_chosen F hk0 hi.1]
  simp only [valOf, hi.2, (nodup_topIdx s).idxOf_getElem]

/-- The root has no boundary cycles. -/
theorem bnd_root (F : PolyFacts hP hk) : bnd pg n k (hP.root).1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  have hlt := (mem_bnd.mp hi).1
  have hb : (⟨cyc pg n k i, cyc_mem F hlt⟩ : CycVar pg n k) ∈
      (polygonProblem hP hk).boundary hP.root := by
    rw [← idx_mem_bnd_iff F _ hP.root.2, idx_cyc F hlt]; exact hi
  simp only [Problem.boundary, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact hb.1 (hP.mem_sub_root _)

/-- On the boundary cycles of `s`, the chosen values are represented by `A s`. -/
theorem map_bnd_chosen (F : PolyFacts hP hk) (hk0 : 0 < k) {s : ℕ × ℕ} (hs : s ∈ segs pg n) :
    (bnd pg n k s).map (vOf (chosen pg n hk0)) =
      cfg k (bnd pg n k s).length ((backtrack pg n k).1 s) := by
  have key := (segTree hP).induction_sub
    (Q := fun v : Seg pg n => (bnd pg n k v.1).map (vOf (chosen pg n hk0)) =
      cfg k (bnd pg n k v.1).length ((backtrack pg n k).1 v.1)) ?_ hP.root ?_ ⟨s, hs⟩
    (hP.mem_sub_root _)
  · exact key
  · intro v w hw hv
    have hwc : w.1 ∈ childSegs pg n v.1 :=
      (F.mem_childSegs v.1 v.2 w.1).mpr ⟨w.2, (mem_children_iff hP v w).mp hw⟩
    rw [(backtrack_inv F v.2).2 w.1 hwc, ← hv, ← map_topIdx_chosen F hk0, ← List.map_append]
    change _ = cfg k _ (childIdx pg n k v.1 w.1 ((rel pg n k v.1).map (vOf (chosen pg n hk0))))
    rw [childIdx_eq F v.2 hwc, cfg_enc_map hk0]
  · show List.map _ (bnd pg n k hP.root.1) = cfg k (bnd pg n k hP.root.1).length _
    rw [bnd_root F]
    rfl

/-- The chosen values attain the minimum of the dynamic program at every segment. -/
theorem chosen_local [NeZero k] (F : PolyFacts hP hk) (hk0 : 0 < k) (v : Seg pg n) :
    (polygonProblem hP hk).loc v (chosen pg n hk0) +
      ∑ w ∈ (segTree hP).children v, (polygonProblem hP hk).dp w (chosen pg n hk0) =
        (polygonProblem hP hk).dp v (chosen pg n hk0) := by
  obtain ⟨s, hs⟩ := v
  have hsz : s.2 - s.1 ≤ n := by
    have := hP.lt_of_adj (hP.mem_segs.mp hs).1; omega
  have hA := (map_bnd_chosen F hk0 hs).symm
  obtain ⟨h1, h2⟩ := tabArg_spec F n s hs hsz ((backtrack pg n k).1 s) (chosen pg n hk0) hA
  rw [← h1]
  refine h2 (chosen pg n hk0) hA ?_
  have hB := (backtrack_inv F hs).1
  change cfg k _ (argTab pg n k s _) = _
  rw [← hB, map_topIdx_chosen F hk0]

/-- **The backtracking is optimal**: the total cost of the chosen values is `dp` at the
root, the least total cost. -/
theorem total_chosen [NeZero k] (F : PolyFacts hP hk) (hk0 : 0 < k) :
    (polygonProblem hP hk).total (chosen pg n hk0) = (polygonProblem hP hk).dp hP.root (chosen pg n hk0) ∧
    (polygonProblem hP hk).total (chosen pg n hk0) =
      (Finset.univ : Finset (CycVar pg n k → Fin k)).inf' Finset.univ_nonempty
        (polygonProblem hP hk).total :=
  (polygonProblem hP hk).total_eq_dp_of_local (fun _ => hP.mem_sub_root _)
    (fun _ _ => hP.mem_sub_root _) (fun v _ => chosen_local F hk0 v)

/-- The total cost of the chosen values is the optimum `C*` of `CPAP(pg, k)`. -/
theorem isMinCost_total_chosen (F : PolyFacts hP hk) (hk0 : 0 < k) :
    IsMinCost pg k ((polygonProblem hP hk).total (chosen pg n hk0)) := by
  have : NeZero k := ⟨by omega⟩
  rw [(total_chosen F hk0).1]
  exact dp_root_optimal hP hk _

end Facts

end STACS2027.Poly
