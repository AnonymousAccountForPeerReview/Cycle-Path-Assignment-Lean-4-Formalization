module

public import Outerplanar.RAM.Poly2Pool
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver: the pair scan of the pool, abstract side

The boundary lists `bnd s` are the stable sort, by segment index, of the records of the pairs
`(x, y)` of entries of every pool cycle `u` (index `i`) that are segments (`segId`) other than the
top of `u` (`bElem`, `bAll`): for each segment `s`, the pool indices `i` (increasing) of the
cycles through both ends of `s` with another top (`bnd_eq_scan`, `bndCat_eq`).

The machine finds the segments among the pairs without a table indexed by pairs of positions:

* it lists the triples `(x, y, i)` of all pairs of entries of the pool cycles but their tops
  (`trip`, in the order of the scan);
* it sorts them stably by `x` (`tripX`), and for each `x` marks the second ends of the segments
  `(x, b)`, so that it can write the key of every triple: the index of `(x, y)` in `segOrder`, or
  `|segOrder|` if `(x, y)` is not a segment (`keyOf`);
* a stable sort by key then gives the boundary lists: for every segment the triples with its
  key have the same pool indices as the records of the reference scan (`tripX_key_bnd`), so the
  sorts agree (`map_bucketIdx_congr`), and the boundary lists, concatenated, are the first part
  of the result (`bndCat_eq_trip`, `bndOffs_eq_trip`).
-/

@[expose] public section

namespace STACS2027.RAM.P2

open STACS2027.Poly P1

/-! ### Abstract side -/

section Abstract

variable (pg : Graph) (n k : ℕ)

/-- The record of the pair `(x, y)` of the cycle `u` (index `i`). -/
def bElem (u : List ℕ) (i x y : ℕ) : List (ℕ × ℕ) :=
  if segId pg n (x, y) = 0 then [] else
    if (x, y) = topOf u then [] else [(segId pg n (x, y) - 1, i)]

/-- The records of the cycle `u`. -/
def bCyc (u : List ℕ) (i : ℕ) : List (ℕ × ℕ) := u.flatMap fun x => u.flatMap (bElem pg n u i x)

/-- The records of the first `j` pool cycles. -/
def bAll (j : ℕ) : List (ℕ × ℕ) := (List.range j).flatMap fun i => bCyc pg n (cyc pg n k i) i

end Abstract

variable {pg : Graph} {n k : ℕ}

/-- In a list without repetition, the singletons at one value. -/
theorem flatMap_eq_single {u : List ℕ} (hu : u.Nodup) (b : ℕ) {β : Type*} (v : β) :
    (u.flatMap fun y => if y = b then [v] else []) = if b ∈ u then [v] else [] := by
  induction u with
  | nil => simp
  | cons y u ih =>
    obtain ⟨hy, hu⟩ := List.nodup_cons.mp hu
    rw [List.flatMap_cons, ih hu]
    by_cases hyb : y = b
    · subst hyb; simp [hy]
    · simp [hyb, Ne.symm hyb]

/-- In a list without repetition, the pairs at one value. -/
theorem flatMap_flatMap_eq_single {u : List ℕ} (hu : u.Nodup) (a b : ℕ) {β : Type*} (v : β) :
    (u.flatMap fun x => u.flatMap fun y => if x = a ∧ y = b then [v] else []) =
      if a ∈ u ∧ b ∈ u then [v] else [] := by
  have h : ∀ x, (u.flatMap fun y => if x = a ∧ y = b then [v] else []) =
      if x = a then (if b ∈ u then [v] else []) else [] := by
    intro x
    by_cases hx : x = a
    · simp only [hx, true_and, ite_true]; exact flatMap_eq_single hu b v
    · simp [hx]
  rw [List.flatMap_congr (fun x _ => h x)]
  by_cases hb : b ∈ u
  · simp only [hb, ite_true, and_true]
    exact flatMap_eq_single hu a v
  · simp [hb]

/-- The index of an entry of a list without repetition. -/
theorem idxOf_eq_iff {l : List (ℕ × ℕ)} (hl : l.Nodup) {p : ℕ × ℕ} (hp : p ∈ l) {t : ℕ}
    (ht : t < l.length) : l.idxOf p = t ↔ p = l[t] := by
  constructor
  · intro h; subst h; exact (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hp)).symm
  · intro h; subst h; exact hl.idxOf_getElem t ht

/-- The record of a pair for the segment `t`. -/
theorem bElem_filter {u : List ℕ} {t : ℕ} (ht : t < (segOrder pg n).length) (i x y : ℕ) :
    ((bElem pg n u i x y).filter fun p => decide (p.1 = t)).map Prod.snd =
      if (x, y) = (segOrder pg n)[t] ∧ topOf u ≠ (segOrder pg n)[t] then [i] else [] := by
  unfold bElem segId
  by_cases hm : (x, y) ∈ segOrder pg n
  · rw [ite_eq_left hm]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    by_cases htop : (x, y) = topOf u
    · rw [ite_eq_left htop, ite_eq_right]
      · rfl
      · rintro ⟨h1, h2⟩; exact h2 (htop ▸ h1)
    · rw [ite_eq_right htop]
      by_cases hxs : (x, y) = (segOrder pg n)[t]
      · have hidx := (idxOf_eq_iff segOrder_nodup hm ht).mpr hxs
        rw [ite_eq_left ⟨hxs, fun h => htop (hxs.trans h.symm)⟩]
        simp [hidx]
      · have hidx : (segOrder pg n).idxOf (x, y) ≠ t := fun h =>
          hxs ((idxOf_eq_iff segOrder_nodup hm ht).mp h)
        rw [ite_eq_right (fun h => hxs h.1)]
        simp [hidx]
  · rw [ite_eq_right hm]
    have hn : ¬ ((x, y) = (segOrder pg n)[t] ∧ topOf u ≠ (segOrder pg n)[t]) := by
      rintro ⟨h1, -⟩; exact hm (h1 ▸ List.getElem_mem ht)
    rw [ite_eq_right hn]
    simp

/-- The records of a cycle `u` (entries below `n`, without repetition) for the segment `t`. -/
theorem bCyc_filter {u : List ℕ} (hu : u.Nodup) {t : ℕ}
    (ht : t < (segOrder pg n).length) (i : ℕ) :
    ((bCyc pg n u i).filter fun p => decide (p.1 = t)).map Prod.snd =
      if (segOrder pg n)[t].1 ∈ u ∧ (segOrder pg n)[t].2 ∈ u ∧ topOf u ≠ (segOrder pg n)[t]
      then [i] else [] := by
  unfold bCyc
  rw [List.filter_flatMap, List.map_flatMap]
  rw [List.flatMap_congr (fun x _ => by
    rw [List.filter_flatMap, List.map_flatMap,
      List.flatMap_congr (fun y _ => bElem_filter ht i x y)])]
  by_cases htop : topOf u = (segOrder pg n)[t]
  · simp [htop]
  · have hc : ∀ x y, ((x, y) = (segOrder pg n)[t] ∧ topOf u ≠ (segOrder pg n)[t]) ↔
        (x = (segOrder pg n)[t].1 ∧ y = (segOrder pg n)[t].2) := by
      intro x y
      simp only [htop, ne_eq, not_false_eq_true, and_true, Prod.ext_iff]
    simp only [hc]
    rw [flatMap_flatMap_eq_single hu]
    simp [htop]

/-- A list read through its indices. -/
theorem flatMap_range_getD {α β : Type*} (l : List α) (d : α) (f : α → List β) :
    (List.range l.length).flatMap (fun t => f (l.getD t d)) = l.flatMap f := by
  have h : (List.range l.length).map (fun t => l.getD t d) = l := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact getD_of_lt h2 d
  conv_rhs => rw [← h]
  rw [List.flatMap_map]

/-- The pool cycles: increasing, entries below `n`, `k` entries. -/
theorem cyc_facts {i : ℕ} (hi : i < (pool pg n k).length) :
    (cyc pg n k i).Pairwise (· < ·) ∧ (∀ x ∈ cyc pg n k i, x < n) ∧ (cyc pg n k i).length = k := by
  have hm : cyc pg n k i ∈ pool pg n k := Poly.getD_mem [] hi
  obtain ⟨s, hs, hu⟩ := List.mem_flatMap.mp hm
  obtain ⟨hr, hl⟩ := sound_rpF hu
  have hsn := (lt_of_mem_segOrder hs).2
  exact ⟨hr.pairwise, fun x hx => by have := hr.bounds hx; omega, hl⟩

/-- **The boundary cycles from the scan.** -/
theorem bnd_eq_scan {t : ℕ} (ht : t < (segOrder pg n).length) :
    ((bAll pg n k (pool pg n k).length).filter fun p => decide (p.1 = t)).map Prod.snd =
      bnd pg n k (segOrder pg n)[t] := by
  unfold bAll bnd
  rw [List.filter_flatMap, List.map_flatMap]
  rw [← List.map_id ((List.range (pool pg n k).length).filter _),
    ← flatMap_ite_single (fun i => (segOrder pg n)[t].1 ∈ cyc pg n k i ∧
      (segOrder pg n)[t].2 ∈ cyc pg n k i ∧ topOf (cyc pg n k i) ≠ (segOrder pg n)[t]) id]
  apply List.flatMap_congr
  intro i hi
  obtain ⟨hpw, -, -⟩ := cyc_facts (k := k) (List.mem_range.mp hi)
  rw [bCyc_filter (hpw.imp Nat.ne_of_lt) ht]
  rfl

/-- The segment index of a record is below `|segOrder|`. -/
theorem fst_lt_of_mem_bElem {u : List ℕ} {i x y : ℕ} {p : ℕ × ℕ}
    (h : p ∈ bElem pg n u i x y) : p.1 < (segOrder pg n).length := by
  unfold bElem segId at h
  by_cases h1 : (x, y) ∈ segOrder pg n
  · rw [ite_eq_left h1] at h
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at h
    split_ifs at h with h3
    · simp at h
    · simp only [List.mem_singleton] at h
      rw [h]
      exact List.idxOf_lt_length_iff.mpr h1
  · rw [ite_eq_right h1] at h
    simp at h

theorem length_bCyc_le (u : List ℕ) (i : ℕ) : (bCyc pg n u i).length ≤ u.length * u.length := by
  unfold bCyc
  rw [List.length_flatMap]
  refine sum_map_le_mul _ _ _ fun x _ => ?_
  rw [List.length_flatMap]
  refine (sum_map_le_mul _ _ 1 fun y _ => ?_).trans (by simp)
  unfold bElem; split_ifs <;> simp

theorem length_bAll_le {j : ℕ} (hj : j ≤ (pool pg n k).length) :
    (bAll pg n k j).length ≤ j * (k * k) := by
  unfold bAll
  rw [List.length_flatMap]
  refine (sum_map_le_mul _ _ (k * k) fun i hi => ?_).trans (by simp)
  have := (cyc_facts (k := k) (show i < (pool pg n k).length by
    simp only [List.mem_range] at hi; omega)).2.2
  have h := length_bCyc_le (pg := pg) (n := n) (cyc pg n k i) i
  rw [this] at h
  exact h

/-- **The boundary lists, concatenated**, read through the stably sorted records. -/
theorem bndCat_eq :
    (bucketIdx ((bAll pg n k (pool pg n k).length).map Prod.fst) (segOrder pg n).length).map
        (fun i => ((bAll pg n k (pool pg n k).length).map Prod.snd).getD i 0) = bndCat pg n k := by
  rw [map_bucketIdx (bAll pg n k (pool pg n k).length) (0, 0) Prod.fst Prod.snd, List.map_flatMap,
    bndCat, ← flatMap_range_getD (segOrder pg n) (0, 0)]
  apply List.flatMap_congr
  intro t ht
  rw [List.mem_range] at ht
  rw [getD_of_lt ht, ← bnd_eq_scan ht]

theorem sum_range_take {α : Type*} (l : List α) (d : α) (f : α → ℕ) :
    ∀ t, t ≤ l.length → ((List.range t).map fun t' => f (l.getD t' d)).sum = ((l.map f).take t).sum
  | 0, _ => by simp
  | t + 1, ht => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_take l d f t (by omega),
      take_succ_eq (by simp; omega), List.sum_append]
    simp [List.getElem?_eq_getElem (show t < l.length by omega)]

/-- **The boundary-list offsets** are the bucket starts of the sort. -/
theorem bndOffs_eq :
    (List.range ((segOrder pg n).length + 1)).map
        (offOf ((bAll pg n k (pool pg n k).length).map Prod.fst)) = bndOffs pg n k := by
  rw [bndOffs, prefixSums, List.length_map]
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  rw [offOf, ← sum_range_take (segOrder pg n) (0, 0) (fun s => (bnd pg n k s).length) t (by omega)]
  congr 1
  apply List.map_congr_left
  intro t' ht'
  rw [List.mem_range] at ht'
  rw [List.length_map, length_bkt_map (bAll pg n k (pool pg n k).length) (0, 0) Prod.fst t',
    getD_of_lt (show t' < (segOrder pg n).length by omega), ← bnd_eq_scan (by omega),
    List.length_map]

/-! ### The triples of the machine -/

section TripDefs

variable (pg : Graph) (n k : ℕ)

/-- The triple of the entries `x`, `y` of the cycle `u` (index `i`), unless `(x, y)` is the top
of `u`. -/
def tElem (u : List ℕ) (i x y : ℕ) : List (ℕ × ℕ × ℕ) :=
  if (x, y) = topOf u then [] else [(x, y, i)]

/-- The triples of the cycle `u`. -/
def tCyc (u : List ℕ) (i : ℕ) : List (ℕ × ℕ × ℕ) := u.flatMap fun x => u.flatMap (tElem u i x)

/-- The triples of the first `j` pool cycles. -/
def trip (j : ℕ) : List (ℕ × ℕ × ℕ) := (List.range j).flatMap fun i => tCyc (cyc pg n k i) i

/-- All triples, grouped stably by their first entry. -/
def tripX : List (ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun x => (trip pg n k (pool pg n k).length).filter fun p => p.1 = x

/-- The key of a triple `(x, y, i)`: the index of `(x, y)` in `segOrder`, or `|segOrder|` if
`(x, y)` is not a segment. -/
def keyOf (p : ℕ × ℕ × ℕ) : ℕ :=
  if (p.1, p.2.1) ∈ segOrder pg n then (segOrder pg n).idxOf (p.1, p.2.1) else (segOrder pg n).length

end TripDefs

/-- A list without repetitions, containing `b`, mapped to `L` at `b` and to `[]` elsewhere. -/
theorem flatMap_ite_eq {β : Type*} {l : List ℕ} (hl : l.Nodup) {b : ℕ} (hb : b ∈ l)
    (L : List β) : (l.flatMap fun y => if y = b then L else []) = L := by
  induction l with
  | nil => simp at hb
  | cons y l ih =>
    obtain ⟨hy, hl⟩ := List.nodup_cons.mp hl
    rw [List.flatMap_cons]
    by_cases hyb : y = b
    · subst hyb
      have : (l.flatMap fun y' => if y' = y then L else []) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro z hz
        rw [ite_eq_right (fun h : z = y => hy (h ▸ hz))]
      rw [this]; simp
    · rw [ite_eq_right hyb, List.nil_append]
      exact ih hl ((List.mem_cons.mp hb).resolve_left (Ne.symm hyb))

/-- The triples of a cycle `u` without repetition for the segment `t`. -/
theorem tCyc_filter {u : List ℕ} (hu : u.Nodup) {t : ℕ} (ht : t < (segOrder pg n).length)
    (i : ℕ) :
    ((tCyc u i).filter fun p => decide ((p.1, p.2.1) = (segOrder pg n)[t])).map (·.2.2) =
      if (segOrder pg n)[t].1 ∈ u ∧ (segOrder pg n)[t].2 ∈ u ∧ topOf u ≠ (segOrder pg n)[t]
      then [i] else [] := by
  have he : ∀ x y, ((tElem u i x y).filter fun p => decide ((p.1, p.2.1) = (segOrder pg n)[t])).map
      (·.2.2) = if (x, y) = (segOrder pg n)[t] ∧ topOf u ≠ (segOrder pg n)[t] then [i] else [] := by
    intro x y
    unfold tElem
    by_cases htop : (x, y) = topOf u
    · rw [ite_eq_left htop, ite_eq_right]
      · rfl
      · rintro ⟨h1, h2⟩; exact h2 (htop ▸ h1)
    · rw [ite_eq_right htop]
      by_cases hxs : (x, y) = (segOrder pg n)[t]
      · rw [ite_eq_left ⟨hxs, fun h => htop (hxs.trans h.symm)⟩]
        simp [hxs]
      · rw [ite_eq_right (fun h => hxs h.1)]
        simp [hxs]
  unfold tCyc
  rw [List.filter_flatMap, List.map_flatMap]
  rw [List.flatMap_congr (fun x _ => by
    rw [List.filter_flatMap, List.map_flatMap, List.flatMap_congr (fun y _ => he x y)])]
  by_cases htop : topOf u = (segOrder pg n)[t]
  · simp [htop]
  · have hc : ∀ x y, ((x, y) = (segOrder pg n)[t] ∧ topOf u ≠ (segOrder pg n)[t]) ↔
        (x = (segOrder pg n)[t].1 ∧ y = (segOrder pg n)[t].2) := by
      intro x y
      simp only [htop, ne_eq, not_false_eq_true, and_true, Prod.ext_iff]
    simp only [hc]
    rw [flatMap_flatMap_eq_single hu]
    simp [htop]

/-- **The boundary cycles from the triples.** -/
theorem trip_filter_seg {t : ℕ} (ht : t < (segOrder pg n).length) :
    ((trip pg n k (pool pg n k).length).filter
        fun p => decide ((p.1, p.2.1) = (segOrder pg n)[t])).map (·.2.2) =
      bnd pg n k (segOrder pg n)[t] := by
  unfold trip bnd
  rw [List.filter_flatMap, List.map_flatMap]
  rw [← List.map_id ((List.range (pool pg n k).length).filter _),
    ← flatMap_ite_single (fun i => (segOrder pg n)[t].1 ∈ cyc pg n k i ∧
      (segOrder pg n)[t].2 ∈ cyc pg n k i ∧ topOf (cyc pg n k i) ≠ (segOrder pg n)[t]) id]
  apply List.flatMap_congr
  intro i hi
  obtain ⟨hpw, -, -⟩ := cyc_facts (k := k) (List.mem_range.mp hi)
  rw [tCyc_filter (hpw.imp Nat.ne_of_lt) ht]
  rfl

/-- The key of a triple is `t` exactly for the triples of the segment `t`. -/
theorem keyOf_eq_iff {t : ℕ} (ht : t < (segOrder pg n).length) (p : ℕ × ℕ × ℕ) :
    keyOf pg n p = t ↔ (p.1, p.2.1) = (segOrder pg n)[t] := by
  unfold keyOf
  split_ifs with h
  · exact idxOf_eq_iff segOrder_nodup h ht
  · constructor
    · intro h'; omega
    · intro h'; exact absurd (h' ▸ List.getElem_mem ht) h

/-- The triples with key `t`, in the grouped order, are those of the segment `t`, in the order
of the scan. -/
theorem tripX_filter_key {t : ℕ} (ht : t < (segOrder pg n).length) :
    (tripX pg n k).filter (fun p => decide (keyOf pg n p = t)) =
      (trip pg n k (pool pg n k).length).filter
        fun p => decide ((p.1, p.2.1) = (segOrder pg n)[t]) := by
  have hx := (lt_of_mem_segOrder (List.getElem_mem ht)).2
  have hx0 : (segOrder pg n)[t].1 < n := by have := lt_of_mem_segOrder (List.getElem_mem ht); omega
  set T := trip pg n k (pool pg n k).length
  rw [List.filter_congr (fun p _ => by rw [decide_eq_decide.mpr (keyOf_eq_iff ht p)])]
  unfold tripX
  rw [List.filter_flatMap]
  have hg : ∀ x, (T.filter fun p => decide (p.1 = x)).filter
      (fun p => decide ((p.1, p.2.1) = (segOrder pg n)[t])) =
      if x = (segOrder pg n)[t].1 then T.filter fun p => decide ((p.1, p.2.1) = (segOrder pg n)[t])
      else [] := by
    intro x
    rw [List.filter_filter]
    split_ifs with h
    · apply List.filter_congr
      intro p _
      by_cases hp : (p.1, p.2.1) = (segOrder pg n)[t]
      · have : p.1 = x := by rw [h, ← hp]
        simp [this]
      · simp [hp]
    · rw [List.filter_eq_nil_iff]
      intro p _ hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      have e1 := congrArg Prod.fst hp.1
      have e2 := hp.2
      simp only at e1
      exact h (by omega)
  rw [List.flatMap_congr (fun x _ => hg x)]
  exact flatMap_ite_eq List.nodup_range (List.mem_range.mpr hx0) _

/-- **The pool indices of the triples with key `t`** are the boundary cycles of the segment
`t`, which are also those of the records of the reference scan. -/
theorem tripX_key_bnd {t : ℕ} (ht : t < (segOrder pg n).length) :
    ((tripX pg n k).filter fun p => decide (keyOf pg n p = t)).map (·.2.2) =
      ((bAll pg n k (pool pg n k).length).filter fun p => decide (p.1 = t)).map Prod.snd := by
  rw [tripX_filter_key ht, trip_filter_seg ht, bnd_eq_scan ht]

/-- **The boundary lists from the triples**: sorting the pool indices of the grouped triples
stably by key gives the boundary lists, concatenated (the per-key subsequences agree with
those of the reference scan). -/
theorem bndCat_eq_trip :
    (bucketIdx ((tripX pg n k).map (keyOf pg n)) (segOrder pg n).length).map
        (fun i => ((tripX pg n k).map (·.2.2)).getD i 0) = bndCat pg n k := by
  rw [map_bucketIdx_congr (tripX pg n k) (bAll pg n k (pool pg n k).length) (0, 0, 0) (0, 0)
    (keyOf pg n) (·.2.2) Prod.fst Prod.snd _ fun t ht => tripX_key_bnd ht, bndCat_eq]

/-- **The boundary-list offsets from the triples.** -/
theorem bndOffs_eq_trip :
    (List.range ((segOrder pg n).length + 1)).map (offOf ((tripX pg n k).map (keyOf pg n))) =
      bndOffs pg n k := by
  rw [← bndOffs_eq]
  apply List.map_congr_left
  intro s hs
  refine offOf_congr (tripX pg n k) (bAll pg n k (pool pg n k).length) (0, 0, 0) (0, 0)
    (keyOf pg n) Prod.fst (segOrder pg n).length (fun t ht => ?_) (by simp at hs; omega)
  have := congrArg List.length (tripX_key_bnd (k := k) ht)
  simpa using this

/-- The keys are below `|segOrder| + 1`. -/
theorem keyOf_lt (p : ℕ × ℕ × ℕ) : keyOf pg n p < (segOrder pg n).length + 1 := by
  unfold keyOf
  split_ifs with h
  · have := List.idxOf_lt_length_iff.mpr h; omega
  · omega

/-- The entries of the triples are pool entries, below `n`. -/
theorem trip_lt {j : ℕ} (hj : j ≤ (pool pg n k).length) {p : ℕ × ℕ × ℕ}
    (hp : p ∈ trip pg n k j) : p.1 < n ∧ p.2.1 < n ∧ p.2.2 < j := by
  simp only [trip, tCyc, tElem, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨i, hi, x, hx, y, hy, hp⟩ := hp
  split_ifs at hp
  · simp at hp
  · simp only [List.mem_singleton] at hp
    subst hp
    have h := (cyc_facts (k := k) (show i < (pool pg n k).length by omega)).2.1
    exact ⟨h x hx, h y hy, hi⟩

theorem length_tCyc_le (u : List ℕ) (i : ℕ) : (tCyc u i).length ≤ u.length * u.length := by
  unfold tCyc
  rw [List.length_flatMap]
  refine sum_map_le_mul _ _ _ fun x _ => ?_
  rw [List.length_flatMap]
  refine (sum_map_le_mul _ _ 1 fun y _ => ?_).trans (by simp)
  unfold tElem; split_ifs <;> simp

/-- There are at most `k²` triples per pool cycle. -/
theorem length_trip_le {j : ℕ} (hj : j ≤ (pool pg n k).length) :
    (trip pg n k j).length ≤ j * (k * k) := by
  unfold trip
  rw [List.length_flatMap]
  refine (sum_map_le_mul _ _ (k * k) fun i hi => ?_).trans (by simp)
  have := (cyc_facts (k := k) (show i < (pool pg n k).length by
    simp only [List.mem_range] at hi; omega)).2.2
  have h := length_tCyc_le (cyc pg n k i) i
  rw [this] at h
  exact h

theorem length_tripX (hn : ∀ p ∈ trip pg n k (pool pg n k).length, p.1 < n) :
    (tripX pg n k).length = (trip pg n k (pool pg n k).length).length := by
  have h := congrArg List.length (map_bucketIdx (trip pg n k (pool pg n k).length) (0, 0, 0)
    Prod.fst (·.2.2) n)
  rw [List.length_map, List.length_map, length_bucketIdx _ _ (by
    intro x hx; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hn p hp), List.length_map] at h
  exact h.symm

end STACS2027.RAM.P2
