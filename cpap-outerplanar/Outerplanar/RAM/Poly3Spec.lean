module

public import Outerplanar.RAM.Poly1Spec
public import Outerplanar.Algo.PolyDP
public import Outerplanar.Algo.PolyBounds
public import Outerplanar.Algo.PolyPool
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver, abstract side

The facts about the tables of `Outerplanar/Algo/Poly.lean` in the form the machine of phase P3
computes them:

* `tabArg_fuel`: the tables do not depend on the fuel once it exceeds the size of the segment
  (children are strictly smaller); hence `table s α = (best s α).2` and
  `argTab s α = (best s α).1` (`table_eq`, `argTab_eq`), where `best` is the machine's
  minimization: a fold over all `β < k ^ |topIdx s|` keeping the first strict minimum
  (`stepB`, `foldl_stepB`) of the total `totAB s α β`;
* `totV_eq`: the total of a configuration is the load cost of `s` plus, slot by slot of the
  face, the load cost of a side or the table entry of a child (`slotCost`);
* `loadAt_eq`: the load as a count over the relevant cycles (`selQ`); `mem_cycleEdges_iff`,
  `eq_edge_iff`: the edges of a cycle `c` of length `k` are `edge c[j] c[j + 1 mod k]`;
* the pool: every cycle has `k` entries, so cycle `i` is at `i * k` of the flattened pool
  (`getD_pool`);
* offsets: `getD_prefixSums_seg`, `getD_flatMap_seg`; the children come before their parent
  in `segOrder` (`idxOf_child_lt`); the tables of the first `j` segments, concatenated (`tabDone`), give the
  entries of the earlier segments (`getD_tabDone`); the entry `a` of the segment `j` is at
  `toffAt j + a` of `tabCat`, `argCat` (`getD_tabCat`, `getD_argCat`, for the next phase);
* `childIdx`: `enc` of the digits, accumulated digit by digit (`enc_append_singleton`), each
  digit found by a scan (`scan_step`);
* the odometer `odoL` on base-`k` digits (`odoL_cfg`, `cfg_pow`);
* bounds `length_rel_le`, `length_bnd_le'` by `Rb k`.
-/

@[expose] public section

namespace STACS2027.RAM.P3

open STACS2027.Poly STACS2027.RAM.P1

/-! ### Fuel independence of the tables -/

section Fuel

variable {pg : Graph} {n k : ℕ}

/-- **The tables do not depend on the fuel** once it exceeds the size of the segment. -/
theorem tabArg_fuel (hP : IsPolygon pg n) : ∀ (d : ℕ) (s : ℕ × ℕ), s ∈ IsPolygon.segs pg n →
    s.2 - s.1 ≤ d → ∀ f f', d < f → d < f' → tabArg pg n k f s = tabArg pg n k f' s := by
  intro d
  induction d with
  | zero => intro s hs hd; have := (of_mem_segs hs).2; omega
  | succ d ih =>
    intro s hs hd f f' hf hf'
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    funext α
    rw [tabArg_succ, tabArg_succ]
    have h : stepTotal pg n k f s α = stepTotal pg n k f' s α := by
      funext β
      unfold stepTotal
      congr 2
      apply List.map_congr_left
      intro w hw
      have hc := (mem_childSegs hP s w).mp hw
      have hlt := hP.child_size_lt hc.1 hc.2
      simp only [IsPolygon.segSize] at hlt
      rw [ih w hc.1 (by omega) f f' (by omega) (by omega)]
    rw [h]

end Fuel

/-! ### The machine's minimization -/

section Best

variable (pg : Graph) (n k : ℕ)

/-- The total of a configuration with values `vals` of the relevant cycles of `s`: the local
cost plus the table entries of the children. -/
def totV (s : ℕ × ℕ) (vals : List ℕ) : ℕ :=
  localCost pg n k s vals +
    ((childSegs pg n s).map fun w => table pg n k w (childIdx pg n k s w vals)).sum

/-- The total of the configuration `(α, β)` of `s`. -/
def totAB (s : ℕ × ℕ) (α β : ℕ) : ℕ :=
  totV pg n k s (cfg k (bnd pg n k s).length α ++ cfg k (topIdx pg n k s).length β)

/-- One step of the machine's minimization: take `β = 0`, then every strictly better `β`. -/
def stepB (f : ℕ → ℕ) (bv : ℕ × ℕ) (β : ℕ) : ℕ × ℕ :=
  if β = 0 ∨ f β < bv.2 then (β, f β) else bv

/-- The machine's minimization over `β`, for `α`. -/
def best (s : ℕ × ℕ) (α : ℕ) : ℕ × ℕ :=
  (List.range (k ^ (topIdx pg n k s).length)).foldl (stepB (totAB pg n k s α)) (0, 0)

variable {pg n k}

theorem foldl_stepB_tail (f : ℕ → ℕ) : ∀ (l : List ℕ), (∀ β ∈ l, β ≠ 0) → ∀ bv,
    l.foldl (stepB f) bv = l.foldl (fun bv β => if f β < bv.2 then (β, f β) else bv) bv
  | [], _, _ => rfl
  | β :: l, h, bv => by
    simp only [List.foldl_cons]
    have hβ := h β List.mem_cons_self
    have e : stepB f bv β = if f β < bv.2 then (β, f β) else bv := by simp [stepB, hβ]
    rw [e]
    exact foldl_stepB_tail f l (fun x hx => h x (List.mem_cons_of_mem _ hx)) _

/-- The machine's minimization is the fold of `tabArg`. -/
theorem foldl_stepB (f : ℕ → ℕ) {m : ℕ} (hm : 0 < m) :
    (List.range m).foldl (stepB f) (0, 0) =
      (List.range' 1 (m - 1)).foldl (fun bv β => if f β < bv.2 then (β, f β) else bv) (0, f 0) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.range_eq_range', List.range'_succ, List.foldl_cons, Nat.add_sub_cancel, Nat.zero_add]
  have h0 : stepB f (0, 0) 0 = (0, f 0) := by simp [stepB]
  rw [h0]
  exact foldl_stepB_tail f _ (fun β hβ => by rw [List.mem_range'_1] at hβ; omega) _

/-- **The tables are the machine's minimization.** -/
theorem tabArg_eq_best (hP : IsPolygon pg n) (hk : 0 < k) {s : ℕ × ℕ}
    (hs : s ∈ IsPolygon.segs pg n) (α : ℕ) : tabArg pg n k n s α = best pg n k s α := by
  have hsn := (hP.lt_of_adj (of_mem_segs hs).1).2
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : tabArg pg n k n s α = tabArg pg n k (m + 1) s α := by rw [← hm]
  rw [e, tabArg_succ]
  have hst : stepTotal pg n k m s α = totAB pg n k s α := by
    funext β
    unfold stepTotal totAB totV
    congr 2
    apply List.map_congr_left
    intro w hw
    have hc := (mem_childSegs hP s w).mp hw
    have hlt := hP.child_size_lt hc.1 hc.2
    simp only [IsPolygon.segSize] at hlt
    unfold table
    rw [tabArg_fuel hP (w.2 - w.1) w hc.1 le_rfl m n (by omega) (by omega)]
  rw [hst, best, foldl_stepB _ (pow_pos hk _)]

theorem table_eq (hP : IsPolygon pg n) (hk : 0 < k) {s : ℕ × ℕ}
    (hs : s ∈ IsPolygon.segs pg n) (α : ℕ) : table pg n k s α = (best pg n k s α).2 := by
  unfold table; rw [tabArg_eq_best hP hk hs]

theorem argTab_eq (hP : IsPolygon pg n) (hk : 0 < k) {s : ℕ × ℕ}
    (hs : s ∈ IsPolygon.segs pg n) (α : ℕ) : argTab pg n k s α = (best pg n k s α).1 := by
  unfold argTab; rw [tabArg_eq_best hP hk hs]

/-- One more `β` in the machine's minimization. -/
theorem foldl_stepB_succ (f : ℕ → ℕ) (b : ℕ) :
    (List.range (b + 1)).foldl (stepB f) (0, 0) = stepB f ((List.range b).foldl (stepB f) (0, 0)) b := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end Best

/-! ### The slots of a face -/

section Slots

variable (pg : Graph) (n k : ℕ)

/-- The contribution of a slot `t` of the face of `s`: the load cost of a side, the table entry
of a child. -/
def slotCost (s : ℕ × ℕ) (vals : List ℕ) (t : ℕ × ℕ) : ℕ :=
  if t.2 = t.1 + 1 then pairCount (loadAt pg n k s vals t) else table pg n k t (childIdx pg n k s t vals)

variable {pg n k}

/-- The consecutive pairs of an increasing list are increasing. -/
theorem pairs_lt : ∀ {l : List ℕ}, l.Pairwise (· < ·) → ∀ t ∈ pairs l, t.1 < t.2
  | [], _, t, ht => by simp [pairs] at ht
  | [_], _, t, ht => by simp [pairs] at ht
  | x :: y :: rest, h, t, ht => by
    rw [pairs, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact List.rel_of_pairwise_cons h List.mem_cons_self
    · exact pairs_lt h.of_cons t ht

/-- The consecutive pairs by index. -/
theorem pairs_eq_map : ∀ l : List ℕ,
    pairs l = (List.range (l.length - 1)).map fun q => (l.getD q 0, l.getD (q + 1) 0)
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    rw [pairs, pairs_eq_map (y :: rest)]
    simp only [List.length_cons, Nat.add_sub_cancel, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.getD_cons_zero, List.getD_cons_succ]
    rfl

theorem sum_map_ite {α : Type*} (p : α → Prop) [DecidablePred p] (f g : α → ℕ) :
    ∀ l : List α, (l.map fun x => if p x then f x else g x).sum =
      ((l.filter fun x => decide (p x)).map f).sum + ((l.filter fun x => !decide (p x)).map g).sum
  | [] => rfl
  | x :: l => by
    have ih := sum_map_ite p f g l
    by_cases h : p x
    · simp only [List.map_cons, List.sum_cons, h, ↓reduceIte, List.filter_cons, decide_true,
        Bool.not_true, Bool.false_eq_true, ih]
      omega
    · simp only [List.map_cons, List.sum_cons, h, ↓reduceIte, List.filter_cons, decide_false,
        Bool.not_false, Bool.false_eq_true, ih]
      omega

/-- **The total, slot by slot**: the load cost of `s`, then the slots of the face. -/
theorem totV_eq (s : ℕ × ℕ) (vals : List ℕ) :
    totV pg n k s vals = pairCount (loadAt pg n k s vals s) +
      ((slots pg n s).map (slotCost pg n k s vals)).sum := by
  have hlt : ∀ t ∈ slots pg n s, t.1 < t.2 := pairs_lt faceVerts_pairwise
  unfold totV localCost owned childSegs slotCost
  rw [List.map_cons, List.sum_cons, sum_map_ite]
  have hf : (slots pg n s).filter (fun t => !decide (t.2 = t.1 + 1)) =
      (slots pg n s).filter (fun t => decide (t.1 + 2 ≤ t.2)) := by
    apply List.filter_congr
    intro t ht
    have := hlt t ht
    by_cases h : t.2 = t.1 + 1
    · simp only [h, decide_true, Bool.not_true, false_eq_decide_iff]; omega
    · simp only [h, decide_false, Bool.not_false, true_eq_decide_iff]; omega
  rw [hf, Nat.add_assoc]

end Slots

/-! ### Loads and the edges of the cycles -/

section Loads

variable (pg : Graph) (n k : ℕ)

/-- Is the edge `e` selected in the relevant cycle `q` of `s` (with its value in `vals`)? -/
def selQ (s : ℕ × ℕ) (vals : List ℕ) (e : Edge) (q : ℕ) : Bool :=
  decide (e ∈ selectedAt (cyc pg n k ((rel pg n k s).getD q 0))
    ((cyc pg n k ((rel pg n k s).getD q 0)).getD (vals.getD q 0) 0))

variable {pg n k}

theorem zip_eq_map_range {l v : List ℕ} (h : v.length = l.length) :
    l.zip v = (List.range l.length).map fun q => (l.getD q 0, v.getD q 0) := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
  have hi : i < l.length := by simpa using h2
  rw [getD_of_lt hi, getD_of_lt (by omega)]

/-- **The load as a count** over the relevant cycles. -/
theorem loadAt_eq (s : ℕ × ℕ) (vals : List ℕ) (e : Edge) (h : vals.length = (rel pg n k s).length) :
    loadAt pg n k s vals e = (List.range (rel pg n k s).length).countP (selQ pg n k s vals e) := by
  unfold loadAt
  rw [zip_eq_map_range h, List.countP_map]
  rfl

/-- The edges of a walk. -/
theorem mem_pathEdges_iff : ∀ (l : List ℕ) (e : Edge),
    e ∈ pathEdges l ↔ ∃ j, j + 1 < l.length ∧ e = edge (l.getD j 0) (l.getD (j + 1) 0)
  | [], e => by simp [pathEdges]
  | [x], e => by simp [pathEdges]
  | x :: y :: rest, e => by
    rw [pathEdges, List.mem_cons, mem_pathEdges_iff (y :: rest)]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨j + 1, by simp only [List.length_cons] at hj ⊢; omega, by simp⟩
    · rintro ⟨j, hj, rfl⟩
      cases j with
      | zero => left; simp
      | succ j => right; exact ⟨j, by simp only [List.length_cons] at hj ⊢; omega, by simp⟩

/-- The index after `j` on a cycle of length `k`. -/
def nxt (k j : ℕ) : ℕ := if j + 1 = k then 0 else j + 1

/-- **The edges of a cycle** of length `k`: `edge c[j] c[j + 1 mod k]`. -/
theorem mem_cycleEdges_iff {c : List ℕ} (hc : c.length = k) (hk : 0 < k) (e : Edge) :
    e ∈ cycleEdges c ↔ ∃ j < k, e = edge (c.getD j 0) (c.getD (nxt k j) 0) := by
  unfold cycleEdges
  rw [mem_pathEdges_iff]
  have hl : (c ++ c.take 1).length = k + 1 := by
    simp only [List.length_append, List.length_take, hc]; omega
  rw [hl]
  have h1 : ∀ j < k, (c ++ c.take 1).getD j 0 = c.getD j 0 := fun j hj =>
    getD_append_left' 0 (by omega)
  have h2 : ∀ j < k, (c ++ c.take 1).getD (j + 1) 0 = c.getD (nxt k j) 0 := by
    intro j hj
    unfold nxt
    split
    · rw [getD_append_right' 0 (by omega), show j + 1 - c.length = 0 by omega]
      obtain ⟨x, l, rfl⟩ : ∃ x l, c = x :: l := by
        cases c with
        | nil => simp at hc; omega
        | cons x l => exact ⟨x, l, rfl⟩
      simp
    · exact getD_append_left' 0 (by omega)
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega, by rw [h1 j (by omega), h2 j (by omega)]⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega, by rw [h1 j hj, h2 j hj]⟩

/-- An edge with smaller end `ex` is `edge a b` when `{a, b} = {ex, ey}`. -/
theorem eq_edge_iff {ex ey a b : ℕ} (h : ex < ey) :
    (ex, ey) = edge a b ↔ (a = ex ∧ b = ey) ∨ (a = ey ∧ b = ex) := by
  unfold edge
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab, Prod.mk.injEq]; omega
  · rw [min_eq_right hab, max_eq_left hab, Prod.mk.injEq]; omega

/-- Every cycle of the pool has `k` entries. -/
theorem length_of_mem_pool {u : List ℕ} (hu : u ∈ pool pg n k) : u.length = k := by
  obtain ⟨s, -, hu⟩ := List.mem_flatMap.mp hu
  exact (sound_rpF hu).2

theorem length_cyc {i : ℕ} (hi : i < (pool pg n k).length) : (cyc pg n k i).length = k := by
  rw [cyc_eq_getElem hi]; exact length_of_mem_pool (List.getElem_mem hi)

theorem getD_flatten_const (k : ℕ) : ∀ (L : List (List ℕ)), (∀ u ∈ L, u.length = k) →
    ∀ i v, i < L.length → v < k → L.flatten.getD (i * k + v) 0 = (L.getD i []).getD v 0
  | [], _, i, _, hi, _ => by simp at hi
  | u :: L, hL, i, v, hi, hv => by
    have hu := hL u List.mem_cons_self
    rw [List.flatten_cons]
    cases i with
    | zero => simp only [Nat.zero_mul, Nat.zero_add, List.getD_cons_zero]; exact getD_append_left' 0 (by omega)
    | succ i =>
      rw [getD_append_right' 0 (by rw [hu, Nat.succ_mul]; omega), List.getD_cons_succ,
        show (i + 1) * k + v - u.length = i * k + v by rw [hu, Nat.succ_mul]; omega]
      exact getD_flatten_const k L (fun u hu => hL u (List.mem_cons_of_mem _ hu)) i v
        (by simp only [List.length_cons] at hi; omega) hv

theorem length_flatten_const (k : ℕ) : ∀ (L : List (List ℕ)), (∀ u ∈ L, u.length = k) →
    L.flatten.length = L.length * k
  | [], _ => by simp
  | u :: L, hL => by
    rw [List.flatten_cons, List.length_append, hL u List.mem_cons_self,
      length_flatten_const k L (fun u hu => hL u (List.mem_cons_of_mem _ hu)), List.length_cons,
      Nat.succ_mul]
    omega

/-- **The pool cycle `i` is at `i * k`** of the flattened pool. -/
theorem getD_pool {i v : ℕ} (hi : i < (pool pg n k).length) (hv : v < k) :
    (pool pg n k).flatten.getD (i * k + v) 0 = (cyc pg n k i).getD v 0 :=
  getD_flatten_const k _ (fun _ hu => length_of_mem_pool hu) i v hi hv

theorem length_flatten_pool : (pool pg n k).flatten.length = (pool pg n k).length * k :=
  length_flatten_const k _ (fun _ hu => length_of_mem_pool hu)

end Loads

/-! ### Offsets, children, tables -/

section Offsets

variable (pg : Graph) (n k : ℕ)

/-- The tables of a segment. -/
def blk (s : ℕ × ℕ) : List ℕ := (List.range (k ^ (bnd pg n k s).length)).map (table pg n k s)

/-- The minimizing configurations of a segment. -/
def ablk (s : ℕ × ℕ) : List ℕ := (List.range (k ^ (bnd pg n k s).length)).map (argTab pg n k s)

/-- The tables of the first `j` segments, concatenated. -/
def tabDone (j : ℕ) : List ℕ := ((segOrder pg n).take j).flatMap (blk pg n k)

/-- The minimizing configurations of the first `j` segments, concatenated. -/
def argDone (j : ℕ) : List ℕ := ((segOrder pg n).take j).flatMap (ablk pg n k)

/-- The table offset of the segment `j`. -/
def toffAt (j : ℕ) : ℕ := (((segOrder pg n).take j).map fun t => k ^ (bnd pg n k t).length).sum

variable {pg n k}

theorem getD_prefixSums (l : List ℕ) {j : ℕ} (hj : j ≤ l.length) :
    (prefixSums l).getD j 0 = (l.take j).sum := by
  simp [prefixSums, List.getD_eq_getElem?_getD, show j < l.length + 1 by omega]

theorem length_prefixSums (l : List ℕ) : (prefixSums l).length = l.length + 1 := by
  simp [prefixSums]

/-- The prefix sums over the segments. -/
theorem getD_prefixSums_seg (g : ℕ × ℕ → ℕ) {j : ℕ} (hj : j ≤ (segOrder pg n).length) :
    (prefixSums ((segOrder pg n).map g)).getD j 0 = (((segOrder pg n).take j).map g).sum := by
  rw [getD_prefixSums _ (by simpa using hj), List.map_take]

/-- A concatenation over the segments, read at the offset of the segment `j`. -/
theorem getD_flatMap_seg (f : ℕ × ℕ → List ℕ) {j : ℕ} (hj : j < (segOrder pg n).length) {i : ℕ}
    (hi : i < (f (segOrder pg n)[j]).length) :
    ((segOrder pg n).flatMap f).getD ((((segOrder pg n).take j).map fun t => (f t).length).sum + i) 0 =
      (f (segOrder pg n)[j]).getD i 0 :=
  getD_flatMap f 0 _ j _ (List.getElem?_eq_getElem hj) i hi

theorem lt_length_flatMap_seg (f : ℕ × ℕ → List ℕ) {j : ℕ} (hj : j < (segOrder pg n).length)
    {i : ℕ} (hi : i < (f (segOrder pg n)[j]).length) :
    (((segOrder pg n).take j).map fun t => (f t).length).sum + i < ((segOrder pg n).flatMap f).length := by
  have h1 : ((segOrder pg n).flatMap f).length =
      (((segOrder pg n).take (j + 1)).map fun t => (f t).length).sum +
        (((segOrder pg n).drop (j + 1)).map fun t => (f t).length).sum := by
    rw [List.length_flatMap, ← List.sum_append, ← List.map_append, List.take_append_drop]
  rw [h1, take_succ_segOrder hj, List.map_append, List.sum_append]
  simp only [List.map_singleton, List.sum_singleton]
  omega

/-- Reading a concatenation over the segments stored as an array. -/
theorem arr_flatMap_seg_read {m : ℕ → ℕ} {b : ℕ} (f : ℕ × ℕ → List ℕ)
    (h : Arr m b ((segOrder pg n).flatMap f)) {j : ℕ} (hj : j < (segOrder pg n).length) {i : ℕ}
    (hi : i < (f (segOrder pg n)[j]).length) :
    m (b + ((((segOrder pg n).take j).map fun t => (f t).length).sum + i)) = (f (segOrder pg n)[j]).getD i 0 := by
  rw [h.getD (lt_length_flatMap_seg f hj hi), getD_flatMap_seg f hj hi]

/-- Reading prefix sums over the segments stored as an array. -/
theorem arr_prefixSums_seg_read {m : ℕ → ℕ} {b : ℕ} (g : ℕ × ℕ → ℕ)
    (h : Arr m b (prefixSums ((segOrder pg n).map g))) {j : ℕ} (hj : j ≤ (segOrder pg n).length) :
    m (b + j) = (((segOrder pg n).take j).map g).sum := by
  rw [h.getD (by rw [length_prefixSums, List.length_map]; omega), getD_prefixSums_seg g hj]

/-- **Children come first**: a child of the segment `j` has a smaller index in `segOrder`. -/
theorem idxOf_child_lt (hP : IsPolygon pg n) {j : ℕ} (hj : j < (segOrder pg n).length) {w : ℕ × ℕ}
    (hw : w ∈ childSegs pg n (segOrder pg n)[j]) : (segOrder pg n).idxOf w < j := by
  have hc := (mem_childSegs hP _ w).mp hw
  have hwS : w ∈ segOrder pg n := mem_segOrder.mpr hc.1
  have hlt := hP.child_size_lt hc.1 hc.2
  simp only [IsPolygon.segSize] at hlt
  have hi := List.idxOf_lt_length_iff.mpr hwS
  have he : (segOrder pg n)[(segOrder pg n).idxOf w] = w := List.getElem_idxOf hi
  by_contra hge
  rcases Nat.lt_or_eq_of_le (not_lt.mp hge) with h | h
  · have := List.pairwise_iff_getElem.mp segOrder_size j _ hj hi h
    rw [he] at this; omega
  · have e : w = (segOrder pg n)[j] := by
      rw [← he]; congr 1; exact h.symm
    exact hc.2.1 e

theorem length_blk (s : ℕ × ℕ) : (blk pg n k s).length = k ^ (bnd pg n k s).length := by
  simp [blk]

theorem length_ablk (s : ℕ × ℕ) : (ablk pg n k s).length = k ^ (bnd pg n k s).length := by
  simp [ablk]

theorem length_tabDone (j : ℕ) : (tabDone pg n k j).length = toffAt pg n k j := by
  simp only [tabDone, toffAt, List.length_flatMap, length_blk]

theorem length_argDone (j : ℕ) : (argDone pg n k j).length = toffAt pg n k j := by
  simp only [argDone, toffAt, List.length_flatMap, length_ablk]

theorem tabDone_succ {j : ℕ} (hj : j < (segOrder pg n).length) :
    tabDone pg n k (j + 1) = tabDone pg n k j ++ blk pg n k (segOrder pg n)[j] := by
  rw [tabDone, tabDone, take_succ_segOrder hj, List.flatMap_append, List.flatMap_singleton]

theorem argDone_succ {j : ℕ} (hj : j < (segOrder pg n).length) :
    argDone pg n k (j + 1) = argDone pg n k j ++ ablk pg n k (segOrder pg n)[j] := by
  rw [argDone, argDone, take_succ_segOrder hj, List.flatMap_append, List.flatMap_singleton]

theorem tabDone_full : tabDone pg n k (segOrder pg n).length = tabCat pg n k := by
  rw [tabDone, List.take_length]; rfl

theorem argDone_full : argDone pg n k (segOrder pg n).length = argCat pg n k := by
  rw [argDone, List.take_length]; rfl

theorem toffAt_succ {j : ℕ} (hj : j < (segOrder pg n).length) :
    toffAt pg n k (j + 1) = toffAt pg n k j + k ^ (bnd pg n k (segOrder pg n)[j]).length := by
  rw [toffAt, toffAt, take_succ_segOrder hj, List.map_append, List.sum_append]
  simp

theorem sum_take_mono (l : List ℕ) {j j' : ℕ} (h : j ≤ j') : (l.take j).sum ≤ (l.take j').sum := by
  have e : l.take j = (l.take j').take j := by rw [List.take_take, min_eq_left h]
  rw [e]
  conv_rhs => rw [← List.take_append_drop j (l.take j')]
  rw [List.sum_append]
  omega

theorem toffAt_mono {j j' : ℕ} (h : j ≤ j') : toffAt pg n k j ≤ toffAt pg n k j' := by
  unfold toffAt
  rw [List.map_take, List.map_take]
  exact sum_take_mono _ h

/-- The entries of the segment `j'` lie before the offset of a later segment. -/
theorem toffAt_add_lt {j j' a : ℕ} (hj : j' < j) (hj' : j' < (segOrder pg n).length)
    (ha : a < k ^ (bnd pg n k (segOrder pg n)[j']).length) : toffAt pg n k j' + a < toffAt pg n k j := by
  have h1 := toffAt_succ (pg := pg) (n := n) (k := k) hj'
  have h2 := toffAt_mono (pg := pg) (n := n) (k := k) (show j' + 1 ≤ j by omega)
  omega

theorem getD_tabOffs {j : ℕ} (hj : j ≤ (segOrder pg n).length) :
    (tabOffs pg n k).getD j 0 = toffAt pg n k j := getD_prefixSums_seg _ hj

theorem length_tabOffs : (tabOffs pg n k).length = (segOrder pg n).length + 1 := by
  rw [tabOffs, length_prefixSums, List.length_map]

/-- **The entries of an earlier segment** in the tables of the first `j` segments. -/
theorem getD_tabDone {j j' a : ℕ} (hj : j ≤ (segOrder pg n).length) (hj' : j' < j)
    (ha : a < k ^ (bnd pg n k (segOrder pg n)[j']).length) :
    (tabDone pg n k j).getD (toffAt pg n k j' + a) 0 = table pg n k (segOrder pg n)[j'] a := by
  have h1 : ((segOrder pg n).take j)[j']? = some (segOrder pg n)[j'] := by
    rw [List.getElem?_take]
    simp only [hj', ↓reduceIte, List.getElem?_eq_getElem (show j' < (segOrder pg n).length by omega)]
  have h := getD_flatMap (blk pg n k) 0 _ j' _ h1 a (by rw [length_blk]; exact ha)
  have h2 : (((segOrder pg n).take j).take j').map (fun t => (blk pg n k t).length) =
      ((segOrder pg n).take j').map fun t => k ^ (bnd pg n k t).length := by
    rw [List.take_take, min_eq_left hj'.le]
    simp only [length_blk]
  rw [h2] at h
  rw [tabDone, toffAt, h, blk, getD_map_lt (by simpa using ha) 0]
  simp [List.getD_eq_getElem?_getD, ha]

/-- The minimizing configurations of an earlier segment in those of the first `j` segments. -/
theorem getD_argDone {j j' a : ℕ} (hj : j ≤ (segOrder pg n).length) (hj' : j' < j)
    (ha : a < k ^ (bnd pg n k (segOrder pg n)[j']).length) :
    (argDone pg n k j).getD (toffAt pg n k j' + a) 0 = argTab pg n k (segOrder pg n)[j'] a := by
  have h1 : ((segOrder pg n).take j)[j']? = some (segOrder pg n)[j'] := by
    rw [List.getElem?_take]
    simp only [hj', ↓reduceIte, List.getElem?_eq_getElem (show j' < (segOrder pg n).length by omega)]
  have h := getD_flatMap (ablk pg n k) 0 _ j' _ h1 a (by rw [length_ablk]; exact ha)
  have h2 : (((segOrder pg n).take j).take j').map (fun t => (ablk pg n k t).length) =
      ((segOrder pg n).take j').map fun t => k ^ (bnd pg n k t).length := by
    rw [List.take_take, min_eq_left hj'.le]
    simp only [length_ablk]
  rw [h2] at h
  rw [argDone, toffAt, h, ablk, getD_map_lt (by simpa using ha) 0]
  simp [List.getD_eq_getElem?_getD, ha]

/-- **Reading the tables** (for the next phase): the entry `a` of the segment `j` of `segOrder`
is at the offset `toffAt j + a` of `tabCat`. -/
theorem getD_tabCat {j a : ℕ} (hj : j < (segOrder pg n).length)
    (ha : a < k ^ (bnd pg n k (segOrder pg n)[j]).length) :
    (tabCat pg n k).getD (toffAt pg n k j + a) 0 = table pg n k (segOrder pg n)[j] a := by
  rw [← tabDone_full]; exact getD_tabDone le_rfl hj ha

/-- **Reading the minimizing configurations** (for the next phase): the entry `a` of the
segment `j` of `segOrder` is at the offset `toffAt j + a` of `argCat`. -/
theorem getD_argCat {j a : ℕ} (hj : j < (segOrder pg n).length)
    (ha : a < k ^ (bnd pg n k (segOrder pg n)[j]).length) :
    (argCat pg n k).getD (toffAt pg n k j + a) 0 = argTab pg n k (segOrder pg n)[j] a := by
  rw [← argDone_full]; exact getD_argDone le_rfl hj ha

end Offsets

/-! ### The configurations of the children -/

section Child

variable (pg : Graph) (n k : ℕ)

/-- The digit of the cycle `i` in the configuration `vals` of the relevant cycles of `s`. -/
def digit (s : ℕ × ℕ) (vals : List ℕ) (i : ℕ) : ℕ := vals.getD ((rel pg n k s).idxOf i) 0

variable {pg n k}

theorem enc_append_singleton (l : List ℕ) (d : ℕ) : enc k (l ++ [d]) = enc k l + k ^ l.length * d := by
  induction l with
  | nil => simp [enc]
  | cons x l ih =>
    simp only [List.cons_append, enc, ih, List.length_cons, pow_succ]
    ring

theorem map_range_getD {α β : Type*} (f : α → β) (d : α) (l : List α) :
    (List.range l.length).map (fun i => f (l.getD i d)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [getD_of_lt (by simpa using h2)]

/-- The code of the child configuration, digit by digit. -/
theorem childIdx_eq (s w : ℕ × ℕ) (vals : List ℕ) :
    childIdx pg n k s w vals = enc k ((List.range (bnd pg n k w).length).map fun t =>
      digit pg n k s vals ((bnd pg n k w).getD t 0)) := by
  rw [map_range_getD]; rfl

theorem enc_range_succ (f : ℕ → ℕ) (t : ℕ) :
    enc k ((List.range (t + 1)).map f) = enc k ((List.range t).map f) + k ^ t * f t := by
  rw [List.range_succ, List.map_append, List.map_singleton, enc_append_singleton, List.length_map,
    List.length_range]

theorem digit_lt (hk : 0 < k) {s : ℕ × ℕ} {vals : List ℕ} (hv : ∀ x ∈ vals, x < k) (i : ℕ) :
    digit pg n k s vals i < k := by
  unfold digit
  rw [List.getD_eq_getElem?_getD]
  cases h : vals[(rel pg n k s).idxOf i]? with
  | none => simpa using hk
  | some x => exact hv x (List.mem_of_getElem? h)

theorem childIdx_lt (hk : 0 < k) {s w : ℕ × ℕ} {vals : List ℕ} (hv : ∀ x ∈ vals, x < k) :
    childIdx pg n k s w vals < k ^ (bnd pg n k w).length := by
  have := enc_lt hk ((bnd pg n k w).map (digit pg n k s vals)) (by
    intro d hd
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hd
    exact digit_lt hk hv i)
  rw [List.length_map] at this
  exact this

/-- One step of the scan for the digit of `i`. -/
theorem scan_step {l vals : List ℕ} (hl : l.Nodup) (i : ℕ) {r : ℕ} (hr : r < l.length) (x : ℕ)
    (hx : x = if i ∈ l.take r then vals.getD (l.idxOf i) 0 else 0) :
    (if l.getD r 0 = i then vals.getD r 0 else x) =
      if i ∈ l.take (r + 1) then vals.getD (l.idxOf i) 0 else 0 := by
  rw [List.take_succ_eq_append_getElem hr, getD_of_lt hr]
  by_cases h : l[r] = i
  · have hidx : l.idxOf i = r := by rw [← h]; exact hl.idxOf_getElem r hr
    simp [h, hidx]
  · have : i ∈ l.take r ++ [l[r]] ↔ i ∈ l.take r := by
      simp only [List.mem_append, List.mem_singleton]
      exact ⟨fun h' => h'.resolve_right (Ne.symm h), Or.inl⟩
    simp only [h, ↓reduceIte, this, hx]

/-- The scan gives the digit. -/
theorem scan_done {l vals : List ℕ} (hlen : vals.length = l.length) (i : ℕ) :
    (if i ∈ l.take l.length then vals.getD (l.idxOf i) 0 else 0) = vals.getD (l.idxOf i) 0 := by
  rw [List.take_length]
  split
  · rfl
  · next h =>
    rw [List.idxOf_eq_length h, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega)]
    rfl

end Child

/-! ### The odometer -/

section Odo

/-- The odometer on base-`k` digits (lowest first). -/
def odoL (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: ds => if d + 1 = k then 0 :: odoL k ds else (d + 1) :: ds

/-- The odometer with a carry `cy` (`0` or `1`). -/
def odoc (k cy : ℕ) (l : List ℕ) : List ℕ := if cy = 0 then l else odoL k l

/-- **The odometer adds one.** -/
theorem odoL_cfg {k : ℕ} (hk : 0 < k) : ∀ L x, odoL k (cfg k L x) = cfg k L (x + 1)
  | 0, _ => rfl
  | L + 1, x => by
    rw [cfg_succ, cfg_succ, odoL]
    have hx := Nat.div_add_mod x k
    have hr := Nat.mod_lt x hk
    split
    · next h =>
      have e : x + 1 = k * (x / k + 1) := by rw [Nat.mul_add, Nat.mul_one]; linarith
      have h1 : (x + 1) % k = 0 := by rw [e, Nat.mul_mod_right]
      have h2 : (x + 1) / k = x / k + 1 := by rw [e, Nat.mul_div_cancel_left _ hk]
      rw [h1, h2, odoL_cfg hk L]
    · next h =>
      have e : x + 1 = (x % k + 1) + k * (x / k) := by linarith
      have h1 : (x + 1) % k = x % k + 1 := by
        rw [e, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
      have h2 : (x + 1) / k = x / k := by
        rw [e, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega), Nat.zero_add]
      rw [h1, h2]

/-- After `k ^ L` steps the digits are zero again. -/
theorem cfg_pow {k : ℕ} (hk : 0 < k) (L : ℕ) : cfg k L (k ^ L) = cfg k L 0 := by
  unfold cfg
  apply List.map_congr_left
  intro t ht
  have ht' := List.mem_range.mp ht
  rw [Nat.pow_div ht'.le hk, Nat.zero_div, Nat.zero_mod,
    show L - t = (L - t - 1) + 1 by omega, pow_succ, Nat.mul_mod_left]

theorem odoc_zero (k : ℕ) (l : List ℕ) : odoc k 0 l = l := rfl

theorem odoc_nil (k cy : ℕ) : odoc k cy [] = [] := by unfold odoc; split <;> rfl

theorem set_middle (pre rest : List ℕ) (d v : ℕ) :
    (pre ++ d :: rest).set pre.length v = (pre ++ [v]) ++ rest := by
  rw [List.set_append_right _ _ le_rfl, Nat.sub_self, List.set_cons_zero, List.append_assoc]
  rfl

end Odo

/-! ### Bounds -/

section Bounds

variable {pg : Graph} {n k : ℕ}

/-- The bound on the numbers of relevant cycles. -/
def Rb (k : ℕ) : ℕ := (k - 2) * rpathBound k + rpathBound k

theorem length_bnd_le' (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ IsPolygon.segs pg n) :
    (bnd pg n k s).length ≤ Rb k := by
  have := length_bnd_le (k := k) hP (show s.1 < s.2 by have := (of_mem_segs hs).2; omega)
  unfold Rb; omega

theorem length_topIdx_le' (hP : IsPolygon pg n) (s : ℕ × ℕ) : (topIdx pg n k s).length ≤ Rb k := by
  have := length_topIdx_le (k := k) hP s
  unfold Rb; omega

theorem length_rel_le (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ IsPolygon.segs pg n) :
    (rel pg n k s).length ≤ 2 * Rb k := by
  have h1 := length_bnd_le' (k := k) hP hs
  have h2 := length_topIdx_le' (k := k) hP s
  rw [rel, List.length_append]; omega

end Bounds

end STACS2027.RAM.P3
