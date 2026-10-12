module

public import Outerplanar.Algo.PolyPool
import Mathlib.Tactic

/-!
# The polygon solver: the index lists of the pool

The pool (`Outerplanar.Algo.Poly`) is grouped by top segment, in the order `segOrder`. For the
running time of the dynamic program:

* `topIdx_eq`, `cyc_eq`: the cycles with top `s`, for `s` at index `j` of `segOrder`, are the
  consecutive pool entries starting after the cycles of the earlier segments, and they are
  the members of `rpF pg n k n s.1 s.2 k` in order;
* `length_topIdx_le`: there are at most `rpathBound k` of them;
* `length_bnd_le`: a segment has at most `(k - 2) * rpathBound k` boundary cycles: the tops
  of its boundary cycles are segments strictly containing it, nested, and a boundary cycle
  with the largest of these tops visits both ends of all of them
  (`ends_mem_of_inside_outside`), so there are at most `k - 2` of them.
-/

@[expose] public section

namespace STACS2027.Poly

open IsPolygon

variable {pg : Graph} {n k : ℕ}

/-! ### Indices of grouped lists -/

/-- `getD` in the left part of an append. -/
theorem getD_append_left' {β : Type*} {l₁ l₂ : List β} {i : ℕ} (d : β) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- `getD` in the right part of an append. -/
theorem getD_append_right' {β : Type*} {l₁ l₂ : List β} {i : ℕ} (d : β) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- `getD` below the length gives an entry. -/
theorem getD_mem {β : Type*} {l : List β} {i : ℕ} (d : β) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- The indices of `l₁ ++ l₂` satisfying `p`: those of `l₁`, then those of `l₂`, shifted. -/
theorem filter_range_append {β : Type*} (p : β → Bool) (d : β) (l₁ l₂ : List β) :
    (List.range (l₁ ++ l₂).length).filter (fun i => p ((l₁ ++ l₂).getD i d)) =
      (List.range l₁.length).filter (fun i => p (l₁.getD i d)) ++
        ((List.range l₂.length).filter (fun i => p (l₂.getD i d))).map (l₁.length + ·) := by
  rw [List.length_append, List.range_add, List.filter_append, List.filter_map]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [getD_append_left' d (List.mem_range.mp hi)]
  · congr 1
    apply List.filter_congr
    intro i _
    simp only [Function.comp_apply]
    rw [getD_append_right' d (by omega), Nat.add_sub_cancel_left]

/-- The number of indices of `l` whose entry satisfies `p`. -/
theorem length_filter_range_getD {β : Type*} (p : β → Bool) (d : β) :
    ∀ l : List β, ((List.range l.length).filter (fun i => p (l.getD i d))).length = l.countP p
  | [] => rfl
  | x :: l => by
    have h := filter_range_append p d [x] l
    simp only [List.singleton_append] at h
    rw [h, List.length_append, List.length_map, length_filter_range_getD p d l, List.countP_cons,
      List.length_singleton, List.range_one]
    by_cases hx : p x = true
    · simp [hx, Nat.add_comm]
    · simp [hx]

/-- **Grouped lists**: in `blocks.flatMap f`, where the entries of `f t` have key `t` and the
blocks are distinct, the indices with key `s`, for `s` at index `j` of `blocks`, are the
consecutive indices after the entries of the first `j` blocks. -/
theorem filter_range_flatMap {α β : Type*} [DecidableEq α] (key : β → α) (f : α → List β)
    (d : β) : ∀ (blocks : List α), blocks.Nodup → (∀ t ∈ blocks, ∀ u ∈ f t, key u = t) →
      ∀ (j : ℕ) (s : α), blocks[j]? = some s →
      (List.range (blocks.flatMap f).length).filter
          (fun i => decide (key ((blocks.flatMap f).getD i d) = s)) =
        List.range' ((blocks.take j).map fun t => (f t).length).sum (f s).length
  | [], _, _, j, s, hj => by simp at hj
  | b :: bs, hnd, hkey, j, s, hj => by
    have happ := filter_range_append (fun x => decide (key x = s)) d (f b) (bs.flatMap f)
    beta_reduce at happ
    rw [List.flatMap_cons, happ]
    have hb : b ∉ bs := (List.nodup_cons.mp hnd).1
    have hkb : ∀ i < (f b).length, key ((f b).getD i d) = b :=
      fun i hi => hkey b List.mem_cons_self _ (getD_mem d hi)
    have hkr : ∀ i < (bs.flatMap f).length, key ((bs.flatMap f).getD i d) ∈ bs := by
      intro i hi
      obtain ⟨t, ht, hu⟩ := List.mem_flatMap.mp (getD_mem d hi)
      rw [hkey t (List.mem_cons_of_mem _ ht) _ hu]
      exact ht
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [List.filter_eq_self.mpr (fun i hi => by simpa using hkb i (List.mem_range.mp hi)),
        List.filter_eq_nil_iff.mpr (fun i hi => by
          simp only [decide_eq_true_eq]
          intro he
          exact hb (he ▸ hkr i (List.mem_range.mp hi)))]
      simp [List.range_eq_range']
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have hs : s ∈ bs := List.mem_of_getElem? hj
      have hsb : s ≠ b := fun h => hb (h ▸ hs)
      rw [List.filter_eq_nil_iff.mpr (fun i hi => by
          simp only [decide_eq_true_eq]
          rw [hkb i (List.mem_range.mp hi)]
          exact hsb.symm),
        filter_range_flatMap key f d bs (List.nodup_cons.mp hnd).2
          (fun t ht => hkey t (List.mem_cons_of_mem _ ht)) j s hj]
      simp [List.map_add_range']

/-- The entries of the block `s` at index `j` of `blocks` in `blocks.flatMap f`. -/
theorem getD_flatMap {α β : Type*} (f : α → List β) (d : β) :
    ∀ (blocks : List α) (j : ℕ) (s : α), blocks[j]? = some s → ∀ i < (f s).length,
      (blocks.flatMap f).getD (((blocks.take j).map fun t => (f t).length).sum + i) d =
        (f s).getD i d
  | [], j, s, hj, _, _ => by simp at hj
  | b :: bs, 0, s, hj, i, hi => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    simp only [List.flatMap_cons, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add]
    exact getD_append_left' d hi
  | b :: bs, j + 1, s, hj, i, hi => by
    simp only [List.getElem?_cons_succ] at hj
    rw [List.flatMap_cons, List.take_succ_cons, List.map_cons, List.sum_cons, Nat.add_assoc,
      getD_append_right' d (by omega), Nat.add_sub_cancel_left]
    exact getD_flatMap f d bs j s hj i hi

/-! ### The cycles with a given top -/

/-- **The cycles with top `s`** are consecutive in the pool: for `s` at index `j` of
`segOrder`, they start after the cycles of the first `j` segments. -/
theorem topIdx_eq {s : ℕ × ℕ} {j : ℕ} (hj : (segOrder pg n)[j]? = some s) :
    topIdx pg n k s = List.range'
      (((segOrder pg n).take j).map fun t => (rpF pg n k n t.1 t.2 k).length).sum
      (rpF pg n k n s.1 s.2 k).length :=
  filter_range_flatMap topOf (fun t => rpF pg n k n t.1 t.2 k) [] (segOrder pg n)
    segOrder_nodup (fun _ _ _ hu => topOf_of_mem_rpF hu) j s hj

/-- **The pool entries with top `s`** are the members of `rpF pg n k n s.1 s.2 k`, in order. -/
theorem cyc_eq {s : ℕ × ℕ} {j i : ℕ} (hj : (segOrder pg n)[j]? = some s)
    (hi : i < (rpF pg n k n s.1 s.2 k).length) :
    cyc pg n k ((((segOrder pg n).take j).map fun t => (rpF pg n k n t.1 t.2 k).length).sum + i) =
      (rpF pg n k n s.1 s.2 k).getD i [] := by
  unfold cyc pool
  exact getD_flatMap (fun t => rpF pg n k n t.1 t.2 k) [] (segOrder pg n) j s hj i hi

/-- **At most `rpathBound k` cycles have top `s`.** -/
theorem length_topIdx_le (hP : IsPolygon pg n) (s : ℕ × ℕ) :
    (topIdx pg n k s).length ≤ rpathBound k := by
  by_cases hs : s ∈ segOrder pg n
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hs
    rw [topIdx_eq hj, List.length_range']
    exact length_rpF_le hP _ _ _ _
  · have : topIdx pg n k s = [] := by
      unfold topIdx
      rw [List.filter_eq_nil_iff]
      intro i hi
      simp only [decide_eq_true_eq]
      intro he
      have hm : cyc pg n k i ∈ pool pg n k := getD_mem [] (List.mem_range.mp hi)
      obtain ⟨t, ht, hu⟩ := List.mem_flatMap.mp hm
      rw [topOf_of_mem_rpF hu] at he
      exact hs (he ▸ ht)
    rw [this]
    exact Nat.zero_le _

/-! ### The boundary cycles -/

/-- A sum of terms at most `c` is at most `c` times the number of positive terms. -/
theorem sum_map_le_filter_mul {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, f x ≤ c) : (l.map f).sum ≤ (l.filter fun x => decide (0 < f x)).length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    by_cases h0 : 0 < f x
    · simp only [h0, decide_true, ↓reduceIte, List.length_cons, add_mul, one_mul]
      omega
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      omega

/-- Counting the entries of `u` in a larger interval: strictly more when the larger interval
has an end in `u` outside the smaller one. -/
theorem countP_interval_lt {u : List ℕ} {t t' : ℕ × ℕ} (ht : t.1 ≤ t.2) (hw : Within t t')
    (hne : t ≠ t') (h1 : t'.1 ∈ u) (h2 : t'.2 ∈ u) :
    u.countP (fun v => decide (t.1 ≤ v ∧ v ≤ t.2)) <
      u.countP (fun v => decide (t'.1 ≤ v ∧ v ≤ t'.2)) := by
  simp only [Within] at hw
  rw [List.countP_eq_countP_filter_add u (fun v => decide (t'.1 ≤ v ∧ v ≤ t'.2))
    (fun v => decide (t.1 ≤ v ∧ v ≤ t.2))]
  have e1 : (u.filter fun v => decide (t.1 ≤ v ∧ v ≤ t.2)).countP
      (fun v => decide (t'.1 ≤ v ∧ v ≤ t'.2)) = u.countP (fun v => decide (t.1 ≤ v ∧ v ≤ t.2)) := by
    rw [List.countP_eq_length_filter (l := u), List.countP_eq_length]
    intro v hv
    simp only [List.mem_filter, decide_eq_true_eq] at hv ⊢
    omega
  rw [e1]
  have : 0 < (u.filter fun v => !decide (t.1 ≤ v ∧ v ≤ t.2)).countP
      (fun v => decide (t'.1 ≤ v ∧ v ≤ t'.2)) := by
    rw [List.countP_pos_iff]
    by_cases h : t'.1 < t.1
    · exact ⟨t'.1, List.mem_filter.mpr ⟨h1, by simp; omega⟩, by simp; omega⟩
    · have : t.2 < t'.2 := by
        by_contra h'
        exact hne (Prod.ext (by omega) (by omega))
      exact ⟨t'.2, List.mem_filter.mpr ⟨h2, by simp; omega⟩, by simp; omega⟩
  omega

/-- **At most `k - 2` tops above a segment**: distinct segments `t ≠ s` each carrying a region
path with `k` entries through both ends of `s` are at most `k - 2`. -/
theorem length_tops_le (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s.1 < s.2) (T : List (ℕ × ℕ))
    (hT : T.Nodup) (hmem : ∀ t ∈ T, t ∈ segs pg n ∧ t ≠ s ∧
      ∃ u, IsRPath pg t.1 t.2 u ∧ u.length = k ∧ s.1 ∈ u ∧ s.2 ∈ u) :
    T.length ≤ k - 2 := by
  classical
  by_cases hne : T = []
  · rw [hne]
    exact Nat.zero_le _
  -- the largest top
  obtain ⟨tm, htm, hmax⟩ := T.toFinset.exists_max_image (fun t => t.2 - t.1)
    ((List.toFinset_nonempty_iff T).mpr hne)
  rw [List.mem_toFinset] at htm
  obtain ⟨hsegm, -, u, hu, hul, hs1, hs2⟩ := hmem tm htm
  have hsegm' := hP.mem_segs.mp hsegm
  -- every top contains `s`
  have hwithin_s : ∀ t ∈ T, Within s t := by
    intro t ht
    obtain ⟨-, -, u', hu', -, h1, h2⟩ := hmem t ht
    exact ⟨(hu'.bounds h1).1, (hu'.bounds h2).2⟩
  -- every top lies within the largest one
  have hwithin_m : ∀ t ∈ T, Within t tm := by
    intro t ht
    rcases hP.nested_of_within (hmem t ht).1 hsegm hs (hwithin_s t ht) (hwithin_s tm htm) with
      h | h
    · exact h
    · have h1 := hmax t (List.mem_toFinset.mpr ht)
      have h2 := (hP.mem_segs.mp (hmem t ht).1).2
      have : t = tm := Within.antisymm (by simp only [Within] at h ⊢; omega) h
      rw [this]
      exact Within.refl _
  -- the cycle of the largest top visits both ends of every top
  have hends : ∀ t ∈ T, t.1 ∈ u ∧ t.2 ∈ u := by
    intro t ht
    by_cases htt : t = tm
    · rw [htt]
      exact ⟨hu.head_mem, hu.last_mem⟩
    · have hst := hwithin_s t ht
      have htm' := hwithin_m t ht
      have hts : t ≠ s := (hmem t ht).2.1
      have hseg := hP.mem_segs.mp (hmem t ht).1
      simp only [Within] at hst htm'
      have hy : ∃ y ∈ u, t.1 < y ∧ y < t.2 := by
        by_cases h : t.1 < s.1
        · exact ⟨s.1, hs1, h, by omega⟩
        · have : s.2 < t.2 := by
            by_contra h'
            exact hts (Prod.ext (by omega) (by omega))
          exact ⟨s.2, hs2, by omega, this⟩
      have hz : ∃ z ∈ u, z < t.1 ∨ t.2 < z := by
        by_cases h : tm.1 < t.1
        · exact ⟨tm.1, hu.head_mem, Or.inl h⟩
        · have : t.2 < tm.2 := by
            by_contra h'
            exact htt (Prod.ext (by omega) (by omega))
          exact ⟨tm.2, hu.last_mem, Or.inr this⟩
      obtain ⟨y, hy, hy1, hy2⟩ := hy
      obtain ⟨z, hz, hz'⟩ := hz
      exact ends_mem_of_inside_outside hP hu hsegm'.1 hseg.1 hy hy1 hy2 hz hz'
  -- the number of entries of `u` within a top: between `3` and `k`, injective on the tops
  let φ : ℕ × ℕ → ℕ := fun t => u.countP (fun v => decide (t.1 ≤ v ∧ v ≤ t.2))
  have hφk : ∀ t, φ t ≤ k := fun t => hul ▸ List.countP_le_length
  have hφ3 : ∀ t ∈ T, 3 ≤ φ t := by
    intro t ht
    have hst := hwithin_s t ht
    have hts : t ≠ s := (hmem t ht).2.1
    obtain ⟨ht1, ht2⟩ := hends t ht
    simp only [Within] at hst
    have hw : ∃ w ∈ u, t.1 ≤ w ∧ w ≤ t.2 ∧ (w < s.1 ∨ s.2 < w) := by
      by_cases h : t.1 < s.1
      · exact ⟨t.1, ht1, le_rfl, by omega, Or.inl h⟩
      · have : s.2 < t.2 := by
          by_contra h'
          exact hts (Prod.ext (by omega) (by omega))
        exact ⟨t.2, ht2, by omega, le_rfl, Or.inr this⟩
    obtain ⟨w, hwu, hw1, hw2, hw3⟩ := hw
    show 3 ≤ u.countP _
    rw [List.countP_eq_length_filter]
    have hsub : [s.1, s.2, w] ⊆ u.filter (fun v => decide (t.1 ≤ v ∧ v ≤ t.2)) := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [List.mem_filter, decide_eq_true_eq]
      rcases hv with rfl | rfl | rfl
      · exact ⟨hs1, by omega, by omega⟩
      · exact ⟨hs2, by omega, by omega⟩
      · exact ⟨hwu, hw1, hw2⟩
    have hnd : [s.1, s.2, w].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true]
      omega
    simpa using hnd.length_le_of_subset hsub
  have hinj : ∀ t ∈ T, ∀ t' ∈ T, φ t = φ t' → t = t' := by
    intro t ht t' ht' he
    by_contra hne
    rcases hP.nested_of_within (hmem t ht).1 (hmem t' ht').1 hs (hwithin_s t ht)
      (hwithin_s t' ht') with h | h
    · have := countP_interval_lt (by have := (of_mem_segs (hmem t ht).1).2; omega) h hne
        (hends t' ht').1 (hends t' ht').2
      exact absurd he (Nat.ne_of_lt this)
    · have := countP_interval_lt (by have := (of_mem_segs (hmem t' ht').1).2; omega) h
        (Ne.symm hne) (hends t ht).1 (hends t ht).2
      exact absurd he (Nat.ne_of_gt this)
  have hsub : T.map φ ⊆ List.range' 3 (k - 2) := by
    intro m hm
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    have h1 := hφ3 t ht
    have h2 := hφk t
    rw [List.mem_range'_1]
    omega
  have := (hT.map_on hinj).length_le_of_subset hsub
  simpa using this

/-- **At most `(k - 2) * rpathBound k` boundary cycles.** -/
theorem length_bnd_le (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s.1 < s.2) :
    (bnd pg n k s).length ≤ (k - 2) * rpathBound k := by
  have h1 : (bnd pg n k s).length = (pool pg n k).countP
      (fun u => decide (s.1 ∈ u ∧ s.2 ∈ u ∧ topOf u ≠ s)) := by
    unfold bnd cyc
    exact length_filter_range_getD (fun u => decide (s.1 ∈ u ∧ s.2 ∈ u ∧ topOf u ≠ s)) []
      (pool pg n k)
  rw [h1, pool, List.countP_flatMap]
  refine le_trans (sum_map_le_filter_mul _ _ (rpathBound k) ?_) (Nat.mul_le_mul_right _ ?_)
  · intro t _
    exact List.countP_le_length.trans (length_rpF_le hP _ _ _ _)
  · refine length_tops_le hP hs _ (segOrder_nodup.filter _) ?_
    intro t ht
    simp only [List.mem_filter, Function.comp_apply, decide_eq_true_eq] at ht
    obtain ⟨ht, hpos⟩ := ht
    obtain ⟨u, hu, hP'⟩ := List.countP_pos_iff.mp hpos
    simp only [decide_eq_true_eq] at hP'
    obtain ⟨hr, hl⟩ := sound_rpF hu
    refine ⟨mem_segOrder.mp ht, fun he => hP'.2.2 ?_, u, hr, hl, hP'.1, hP'.2.1⟩
    rw [topOf_of_isRPath hr, ← he]

end STACS2027.Poly
