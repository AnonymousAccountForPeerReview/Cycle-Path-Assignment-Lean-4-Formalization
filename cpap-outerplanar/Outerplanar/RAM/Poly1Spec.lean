module

public import Outerplanar.RAM.PolyIface
public import Outerplanar.RAM.SortSpec
public import Outerplanar.Algo.FaceWalk
import Mathlib.Tactic

/-!
# Phase P1 of the polygon solver, abstract side: neighbour lists

The structure phase P1 (`Outerplanar/RAM/Poly1.lean`) computes its lists by stable counting
sorts (`bucketIdx`, `SortSpec.lean`: the indices of a key list, grouped by key, increasing
within a group). This file proves the facts about the neighbour lists of the polygon:

* the arcs of the polygon (`arcs`: each edge in both directions) grouped by target
  (`arcs1`) and then by source: the group of `p` lists the neighbours `nbP pg n p` in
  increasing order (`map_snd_filter_arcs1`), so a second stable sort by source yields the
  sorted neighbour lists `nbCat pg n` with offsets `nbOff pg n` (`length_nbCat`).
-/

@[expose] public section

namespace STACS2027.RAM.P1

open STACS2027.Poly

/-! ### The arcs of the polygon and the sorted neighbour lists -/

section Arcs

variable (pg : Graph) (n : ℕ)

/-- The arcs of the polygon: each edge in both directions. -/
def arcs : List (ℕ × ℕ) := pg ++ pg.map Prod.swap

/-- The arcs grouped by target, stably. -/
def arcs1 : List (ℕ × ℕ) := (List.range n).flatMap fun q => (arcs pg).filter fun x => x.2 = q

/-- The sorted neighbour lists of the positions `0, …, n - 1`, concatenated. -/
def nbCat : List ℕ := (List.range n).flatMap (nbP pg n)

/-- The start of the neighbour list of `p` in `nbCat`. -/
def nbOff (p : ℕ) : ℕ := ((List.range p).map fun q => (nbP pg n q).length).sum

variable {pg n}

theorem length_arcs : (arcs pg).length = 2 * pg.length := by
  simp [arcs]; omega

theorem mem_arcs {x : ℕ × ℕ} : x ∈ arcs pg ↔ x ∈ pg ∨ x.swap ∈ pg := by
  simp only [arcs, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using hy)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨x.swap, h, by simp⟩

/-- An arc is an adjacency (edges written smaller end first). -/
theorem mem_arcs_iff (hlt : ∀ e ∈ pg, e.1 < e.2) {p q : ℕ} : (p, q) ∈ arcs pg ↔ Adj pg p q := by
  rw [mem_arcs]
  simp only [Prod.swap_prod_mk, Adj, edge]
  constructor
  · rintro (h | h)
    · have := hlt _ h
      simp only at this
      refine ⟨by omega, ?_⟩
      rwa [min_eq_left (by omega), max_eq_right (by omega)]
    · have := hlt _ h
      simp only at this
      refine ⟨by omega, ?_⟩
      rwa [min_eq_right (by omega), max_eq_left (by omega)]
  · rintro ⟨hne, h⟩
    rcases lt_or_gt_of_ne hne with hpq | hpq
    · left; rwa [min_eq_left (by omega), max_eq_right (by omega)] at h
    · right; rwa [min_eq_right (by omega), max_eq_left (by omega)] at h

theorem arcs_nodup (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) : (arcs pg).Nodup := by
  rw [arcs, List.nodup_append]
  refine ⟨hnd, hnd.map Prod.swap_injective, ?_⟩
  intro x hx y hy hxy
  subst hxy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
  have h1 := hlt _ hx
  have h2 := hlt _ hz
  simp at h1
  omega

/-- The ends of an arc are positions. -/
theorem lt_of_mem_arcs (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) {x : ℕ × ℕ}
    (hx : x ∈ arcs pg) : x.1 < n ∧ x.2 < n := by
  have : (x.1, x.2) ∈ arcs pg := hx
  exact hP.lt_of_adj ((mem_arcs_iff hlt).mp this)

/-- Filtering the singletons of the members satisfying `P`. -/
theorem flatMap_ite_singleton (P : ℕ → Prop) [DecidablePred P] :
    ∀ l : List ℕ, (l.flatMap fun q => if P q then [q] else []) = l.filter fun q => P q
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, flatMap_ite_singleton P l, List.filter_cons]
    split <;> simp_all

/-- **The arcs from `p`, grouped by target**, list the neighbours of `p` in increasing
order. -/
theorem map_snd_filter_arcs1 (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) (p : ℕ) :
    ((arcs1 pg n).filter fun x => x.1 = p).map Prod.snd = nbP pg n p := by
  have key : ∀ q, (((arcs pg).filter fun x => x.2 = q).filter fun x => x.1 = p) =
      if Adj pg p q then [(p, q)] else [] := by
    intro q
    rw [List.filter_filter]
    have : ((arcs pg).filter fun x => (decide (x.1 = p) && decide (x.2 = q))) =
        (arcs pg).filter fun x => decide (x = (p, q)) := by
      apply List.filter_congr
      intro x _
      simp only [Bool.decide_and, Prod.ext_iff]
    rw [this, List.filter_eq]
    split
    · next h =>
      rw [List.count_eq_one_of_mem (arcs_nodup hlt hnd) ((mem_arcs_iff hlt).mpr h)]
      rfl
    · next h =>
      rw [List.count_eq_zero_of_not_mem (fun h' => h ((mem_arcs_iff hlt).mp h'))]
      rfl
  rw [arcs1, List.filter_flatMap, List.flatMap_congr (fun q _ => key q), List.map_flatMap, nbP,
    ← flatMap_ite_singleton]
  apply List.flatMap_congr
  intro q _
  split <;> rfl

/-- The arcs grouped by target are read off the arcs through the sorted indices. -/
theorem map_bucketIdx_arcs (g : ℕ × ℕ → ℕ) :
    (bucketIdx ((arcs pg).map Prod.snd) n).map (fun i => ((arcs pg).map g).getD i 0) =
      (arcs1 pg n).map g :=
  map_bucketIdx (arcs pg) (0, 0) Prod.snd g n

theorem length_arcs1 (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) :
    (arcs1 pg n).length = 2 * pg.length := by
  have h := congrArg List.length (map_bucketIdx_arcs (pg := pg) (n := n) Prod.fst)
  rw [List.length_map, List.length_map, length_bucketIdx] at h
  · rw [← h, List.length_map, length_arcs]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (lt_of_mem_arcs hP hlt hy).2

theorem mem_arcs_of_mem_arcs1 {x : ℕ × ℕ} (hx : x ∈ arcs1 pg n) : x ∈ arcs pg := by
  simp only [arcs1, List.mem_flatMap, List.mem_filter] at hx
  obtain ⟨_, _, h, _⟩ := hx
  exact h

/-- **The sorted neighbour lists** are the arcs grouped by target, then by source. -/
theorem map_bucketIdx_arcs1 (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) :
    (bucketIdx ((arcs1 pg n).map Prod.fst) n).map (fun i => ((arcs1 pg n).map Prod.snd).getD i 0) =
      nbCat pg n := by
  rw [map_bucketIdx (arcs1 pg n) (0, 0) Prod.fst Prod.snd n, List.map_flatMap, nbCat]
  apply List.flatMap_congr
  intro p _
  exact map_snd_filter_arcs1 hlt hnd p

/-- The bucket sizes of the second sort are the degrees. -/
theorem length_bkt_arcs1 (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) (p : ℕ) :
    (bkt ((arcs1 pg n).map Prod.fst) ((arcs1 pg n).map Prod.fst).length p).length =
      (nbP pg n p).length := by
  rw [List.length_map, length_bkt_map (arcs1 pg n) (0, 0) Prod.fst p,
    ← map_snd_filter_arcs1 hlt hnd p, List.length_map]

/-- The offsets of the second sort are the starts of the neighbour lists. -/
theorem offOf_arcs1 (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) (p : ℕ) :
    offOf ((arcs1 pg n).map Prod.fst) p = nbOff pg n p := by
  unfold offOf nbOff
  congr 1
  apply List.map_congr_left
  intro q _
  exact length_bkt_arcs1 hlt hnd q

theorem length_nbCat (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) :
    (nbCat pg n).length = 2 * pg.length := by
  rw [← map_bucketIdx_arcs1 hlt hnd, List.length_map, length_bucketIdx, List.length_map,
    length_arcs1 hP hlt]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact (lt_of_mem_arcs hP hlt (mem_arcs_of_mem_arcs1 hy)).1

theorem nbOff_succ (p : ℕ) : nbOff pg n (p + 1) = nbOff pg n p + (nbP pg n p).length := by
  simp only [nbOff, List.sum_range_succ]

theorem nbOff_eq (n : ℕ) : nbOff pg n n = (nbCat pg n).length := by
  simp only [nbOff, nbCat, List.length_flatMap]

end Arcs

/-! ### The enumeration of the segments -/

section Segs

variable (pg : Graph) (n : ℕ)

/-- The segments `(a, b)` for the entries `b` of `l` (a part of the neighbour list of `a`). -/
def segsOf (a : ℕ) (l : List ℕ) : List (ℕ × ℕ) :=
  (l.filter fun b => decide (a + 2 ≤ b)).map fun b => (a, b)

/-- The segments enumerated before the rest of the neighbour list of `a`, `l` being the part
of it already scanned. -/
def enumPre (a : ℕ) (l : List ℕ) : List (ℕ × ℕ) :=
  (List.range a).flatMap (fun a' => segsOf a' (nbP pg n a')) ++ segsOf a l

/-- The face vertex after the first end of a segment. -/
def predOf (s : ℕ × ℕ) : ℕ := predNb pg n s.1 s.2

/-- The cell of a segment in the `n × n` matrix. -/
def cellOf (s : ℕ × ℕ) : ℕ := s.1 * n + s.2

/-- The size of a segment. -/
def sizeOf (s : ℕ × ℕ) : ℕ := s.2 - s.1

variable {pg n}

theorem segEnum_eq : segEnum pg n = (List.range n).flatMap fun a => segsOf a (nbP pg n a) := rfl

theorem segsOf_nil (a : ℕ) : segsOf a [] = [] := rfl

theorem segsOf_snoc (a b : ℕ) (l : List ℕ) :
    segsOf a (l ++ [b]) = segsOf a l ++ if a + 2 ≤ b then [(a, b)] else [] := by
  simp only [segsOf, List.filter_append, List.filter_singleton, List.map_append]
  split <;> simp_all

theorem enumPre_snoc (a b : ℕ) (l : List ℕ) :
    enumPre pg n a (l ++ [b]) = enumPre pg n a l ++ if a + 2 ≤ b then [(a, b)] else [] := by
  rw [enumPre, enumPre, segsOf_snoc, List.append_assoc]

theorem enumPre_zero : enumPre pg n 0 [] = [] := rfl

theorem enumPre_succ (a : ℕ) : enumPre pg n (a + 1) [] = enumPre pg n a (nbP pg n a) := by
  rw [enumPre, enumPre, segsOf_nil, List.append_nil, List.range_succ, List.flatMap_append,
    List.flatMap_singleton]

theorem enumPre_full : enumPre pg n n [] = segEnum pg n := by
  rw [enumPre, segsOf_nil, List.append_nil, segEnum_eq]

/-- The enumeration so far is a prefix of the full enumeration. -/
theorem enumPre_prefix {a : ℕ} (ha : a < n) {l : List ℕ} (hl : l <+: nbP pg n a) :
    enumPre pg n a l <+: segEnum pg n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = a + 1 + k := ⟨n - (a + 1), by omega⟩
  rw [segEnum_eq, List.range_add, List.flatMap_append, List.range_succ, List.flatMap_append,
    List.flatMap_singleton, List.append_assoc, enumPre]
  exact (List.prefix_append_right_inj _).mpr (((hl.filter _).map _).trans (List.prefix_append _ _))

/-- The segments are edges of the polygon (smaller end first). -/
theorem mem_pg_of_mem_segEnum {s : ℕ × ℕ} (hs : s ∈ segEnum pg n) : s ∈ pg := by
  have h := of_mem_segs (mem_segEnum.mp hs)
  have := h.1.2
  simpa [edge, min_eq_left (show s.1 ≤ s.2 by omega), max_eq_right (show s.1 ≤ s.2 by omega)]
    using this

/-- There are at most as many segments as edges. -/
theorem length_segEnum_le : (segEnum pg n).length ≤ pg.length :=
  segEnum_nodup.length_le_of_subset fun _ hs => mem_pg_of_mem_segEnum hs

theorem lt_of_mem_segEnum {s : ℕ × ℕ} (hs : s ∈ segEnum pg n) : s.1 + 2 ≤ s.2 ∧ s.2 < n := by
  have h := mem_segEnum.mp hs
  simp only [IsPolygon.segs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
  exact ⟨h.2.2, h.1.2⟩

/-- Reading a field of the segments through the indices sorted by size gives `segOrder`. -/
theorem map_bucketIdx_segEnum (g : ℕ × ℕ → ℕ) :
    (bucketIdx ((segEnum pg n).map sizeOf) n).map (fun i => ((segEnum pg n).map g).getD i 0) =
      (segOrder pg n).map g :=
  map_bucketIdx (segEnum pg n) (0, 0) sizeOf g n

theorem sizeOf_lt {s : ℕ × ℕ} (hs : s ∈ segEnum pg n) : sizeOf s < n := by
  have := lt_of_mem_segEnum hs
  simp only [sizeOf]; omega

theorem length_segOrder : (segOrder pg n).length = (segEnum pg n).length := by
  have h := congrArg List.length (map_bucketIdx_segEnum (pg := pg) (n := n) Prod.fst)
  rw [List.length_map, List.length_map, length_bucketIdx] at h
  · rw [← h, List.length_map]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact sizeOf_lt hy

/-! ### The face vertex after the first end -/

/-- In an increasing list, the entries below the entry `i` are the first `i` entries. -/
theorem filter_lt_getElem {l : List ℕ} (hs : l.Pairwise (· < ·)) {i : ℕ} (hi : i < l.length) :
    l.filter (fun x => decide (x < l[i])) = l.take i := by
  rw [List.pairwise_iff_getElem] at hs
  obtain ⟨b, hb⟩ : ∃ b, l[i] = b := ⟨_, rfl⟩
  rw [hb]
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.append_nil]
  · intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [List.getElem_drop, decide_eq_true_eq, not_lt, ← hb]
    rcases Nat.eq_or_lt_of_le (Nat.le_add_right i j) with h | h
    · simp only [← h, le_refl]
    · exact (hs _ _ _ _ h).le
  · intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [List.length_take] at hj
    simp only [List.getElem_take, decide_eq_true_eq, ← hb]
    exact hs _ _ _ _ (by omega)

/-- The face vertex after `a` for the neighbour `b = (nbP a)[i]`: the last of the first `i`
neighbours (or `a`). -/
theorem predNb_getElem (a : ℕ) {i : ℕ} (hi : i < (nbP pg n a).length) :
    predNb pg n a (nbP pg n a)[i] = ((nbP pg n a).take i).getLastD a := by
  rw [predNb, filter_lt_getElem (nbP_pairwise a) hi]

theorem getLastD_take_succ {l : List ℕ} {i : ℕ} (hi : i < l.length) (d : ℕ) :
    (l.take (i + 1)).getLastD d = l[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.getLastD_eq_getLast?,
    List.getLast?_append, List.getLast?_singleton]
  simp

end Segs

/-! ### The segment order -/

section Order

variable {pg : Graph} {n : ℕ}

theorem idxOf_append_singleton {α : Type*} [BEq α] [LawfulBEq α] {a : α} :
    ∀ {l : List α}, a ∉ l → (l ++ [a]).idxOf a = l.length
  | [], _ => by simp
  | x :: l, h => by
    rw [List.mem_cons, not_or] at h
    rw [List.cons_append, List.idxOf_cons_ne _ (Ne.symm h.1), idxOf_append_singleton h.2,
      List.length_cons]

theorem lt_of_mem_segOrder {s : ℕ × ℕ} (hs : s ∈ segOrder pg n) : s.1 + 2 ≤ s.2 ∧ s.2 < n :=
  lt_of_mem_segEnum (mem_segEnum.mpr (mem_segOrder.mp hs))

theorem take_succ_segOrder {t : ℕ} (ht : t < (segOrder pg n).length) :
    (segOrder pg n).take (t + 1) = (segOrder pg n).take t ++ [(segOrder pg n)[t]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht]; rfl

theorem getElem_segOrder_not_mem_take {t : ℕ} (ht : t < (segOrder pg n).length) :
    (segOrder pg n)[t] ∉ (segOrder pg n).take t := by
  intro h
  rw [List.mem_iff_getElem] at h
  obtain ⟨j, hj, he⟩ := h
  simp only [List.length_take] at hj
  rw [List.getElem_take] at he
  have := (segOrder_nodup.getElem_inj_iff).mp he
  omega

theorem mem_segOrder_iff_segEnum {p : ℕ × ℕ} : p ∈ segOrder pg n ↔ p ∈ segEnum pg n := by
  rw [mem_segOrder, mem_segEnum]

end Order

/-! ### Enumeration ids and segment ids

The machine finds the id of a slot without a table indexed by pairs of positions: the first
slot `(a, predNb a b)` of the face of `s = (a, b)` is, if it is a segment, the segment before `s`
in `segEnum` (the neighbours `y ≥ a + 2` of `a` are a suffix of its sorted neighbour list,
`enumId_pred`); every other slot `(x, lastNb x)` is the last segment of `x` (`enumId_last`).
Enumeration ids become segment ids through `posId` (`posId_enumId`). -/

section Ids

variable (pg : Graph) (n : ℕ)

/-- The enumeration id of a pair: `1 +` its index in `segEnum`, or `0`. -/
def enumId (p : ℕ × ℕ) : ℕ := if p ∈ segEnum pg n then (segEnum pg n).idxOf p + 1 else 0

/-- Enumeration ids to segment ids (`0 ↦ 0`). -/
def posId (i : ℕ) : ℕ := if i = 0 then 0 else segId pg n ((segEnum pg n).getD (i - 1) (0, 0))

variable {pg n}

theorem segId_of_not_mem {p : ℕ × ℕ} (h : p ∉ segOrder pg n) : segId pg n p = 0 := by
  simp [segId, h]

theorem segId_of_mem {p : ℕ × ℕ} (h : p ∈ segOrder pg n) :
    segId pg n p = (segOrder pg n).idxOf p + 1 := by
  simp [segId, h]

/-- A pair `(x, y)` with `y < x + 2` is not a segment. -/
theorem segId_of_lt {x y : ℕ} (h : y < x + 2) : segId pg n (x, y) = 0 :=
  segId_of_not_mem fun hm => by have := lt_of_mem_segOrder hm; simp only at this; omega

theorem segId_getElem {t : ℕ} (ht : t < (segOrder pg n).length) :
    segId pg n (segOrder pg n)[t] = t + 1 := by
  rw [segId_of_mem (List.getElem_mem ht), segOrder_nodup.idxOf_getElem t ht]

theorem posId_zero : posId pg n 0 = 0 := rfl

theorem posId_enumId (p : ℕ × ℕ) : posId pg n (enumId pg n p) = segId pg n p := by
  unfold enumId
  split_ifs with h
  · simp only [posId, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [getD_of_lt (List.idxOf_lt_length_iff.mpr h), List.getElem_idxOf]
  · simp only [posId, ↓reduceIte]
    rw [segId_of_not_mem]
    rwa [mem_segOrder_iff_segEnum]

/-- The index of the last entry of a prefix of `segEnum`. -/
theorem idxOf_segEnum_of_prefix {A : List (ℕ × ℕ)} {p : ℕ × ℕ} (h : A ++ [p] <+: segEnum pg n) :
    (segEnum pg n).idxOf p = A.length := by
  obtain ⟨rest, hr⟩ := h
  have hnd : (A ++ [p]).Nodup := segEnum_nodup.sublist (by rw [← hr]; exact List.sublist_append_left _ _)
  have hp : p ∉ A := by
    have := List.nodup_append_comm.mp hnd
    exact (List.nodup_cons.mp this).1
  rw [← hr, List.idxOf_append_of_mem (by simp), idxOf_append_singleton hp]

/-- **The last segment of a position**: the enumeration id of `(a, lastNb a)` is the number of
segments enumerated up to the end of the neighbour list of `a` (if it is a segment). -/
theorem enumId_last {a : ℕ} (ha : a < n) :
    enumId pg n (a, lastNb pg n a) =
      if a + 2 ≤ lastNb pg n a then (enumPre pg n a (nbP pg n a)).length else 0 := by
  split_ifs with h
  · obtain ⟨l', z, hl⟩ : ∃ l' z, nbP pg n a = l' ++ [z] := by
      rcases List.eq_nil_or_concat (nbP pg n a) with h0 | ⟨l', z, hz⟩
      · exfalso; simp [lastNb, h0] at h
      · exact ⟨l', z, by simpa using hz⟩
    have hz : lastNb pg n a = z := by simp [lastNb, hl]
    rw [hz] at h ⊢
    have hpre := enumPre_prefix (pg := pg) ha (List.prefix_refl (nbP pg n a))
    rw [hl, enumPre_snoc] at hpre ⊢
    simp only [h, ↓reduceIte] at hpre ⊢
    have hm : (a, z) ∈ segEnum pg n := hpre.subset (by simp)
    rw [enumId, ite_eq_left hm, idxOf_segEnum_of_prefix hpre, List.length_append, List.length_singleton]
  · rw [enumId, ite_eq_right]
    intro hm
    have := lt_of_mem_segEnum hm
    simp only at this
    omega

/-- **The segment before a segment**: if the face vertex `predNb a b` after `a` makes a segment
`(a, predNb a b)`, it is enumerated just before `(a, b)`, so its enumeration id is the index of
`(a, b)`. -/
theorem enumId_pred {s : ℕ × ℕ} (hs : s ∈ segEnum pg n) :
    enumId pg n (s.1, predNb pg n s.1 s.2) =
      if s.1 + 2 ≤ predNb pg n s.1 s.2 then (segEnum pg n).idxOf s else 0 := by
  obtain ⟨a, b⟩ := s
  simp only
  have hab := lt_of_mem_segEnum hs
  simp only at hab
  have hadj : Adj pg a b := (of_mem_segs (mem_segEnum.mp hs)).1
  have hb : b ∈ nbP pg n a := mem_nbP.mpr ⟨hab.2, hadj⟩
  have ha : a < n := by omega
  obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
  have hpred := predNb_getElem (pg := pg) (n := n) a hi
  rw [hbi] at hpred
  have hpi := enumPre_prefix (pg := pg) ha (List.take_prefix (i + 1) (nbP pg n a))
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, enumPre_snoc, hbi] at hpi
  simp only [hab.1, ↓reduceIte] at hpi
  have hsidx := idxOf_segEnum_of_prefix hpi
  split_ifs with h
  · rw [hpred] at h ⊢
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := by
      cases i with
      | zero => simp at h
      | succ i' => exact ⟨i', rfl⟩
    rw [getLastD_take_succ (by omega)] at h ⊢
    have hpj := enumPre_prefix (pg := pg) ha (List.take_prefix (i' + 1) (nbP pg n a))
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      enumPre_snoc] at hpj
    simp only [h, ↓reduceIte] at hpj
    have hm : (a, (nbP pg n a)[i']) ∈ segEnum pg n := hpj.subset (by simp)
    rw [enumId, ite_eq_left hm, idxOf_segEnum_of_prefix hpj, hsidx, List.take_add_one,
      List.getElem?_eq_getElem (by omega), Option.toList_some, enumPre_snoc]
    simp [h]
  · rw [enumId, ite_eq_right]
    intro hm
    have := lt_of_mem_segEnum hm
    simp only at this
    omega

end Ids

/-! ### Faces and slots -/

section FaceSlots

variable {pg : Graph} {n : ℕ}

/-- Two consecutive entries of a list. -/
theorem infix_getElem_pair {l : List ℕ} {r : ℕ} (h : r + 1 < l.length) :
    [l[r], l[r + 1]] <:+: l := by
  refine ⟨l.take r, l.drop (r + 2), ?_⟩
  conv_rhs => rw [← List.take_append_drop r l]
  rw [List.drop_eq_getElem_cons (show r < l.length by omega),
    List.drop_eq_getElem_cons (show r + 1 < l.length by omega)]
  simp

/-- The first two face vertices of a segment: its first end and `predNb`. -/
theorem faceVerts_start (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ IsPolygon.segs pg n) :
    (faceVerts pg n s).getD 0 0 = s.1 ∧ (faceVerts pg n s).getD 1 0 = predNb pg n s.1 s.2 := by
  have h : s.1 :: walkTo pg n s.2 n (predNb pg n s.1 s.2) = faceVerts pg n s := faceWalk_eq hP hs
  have hn : 0 < n := by have := (hP.mem_segs.mp hs); have := (hP.lt_of_adj this.1).2; omega
  obtain ⟨f, rfl⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega⟩
  rw [← h]
  refine ⟨by simp, ?_⟩
  simp only [walkTo]
  split <;> simp

/-- A face vertex after the first: the next one is its largest neighbour. -/
theorem faceVerts_next (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ IsPolygon.segs pg n) {r : ℕ}
    (hr : 1 ≤ r) (hr' : r + 1 < (faceVerts pg n s).length) :
    (faceVerts pg n s).getD (r + 1) 0 = lastNb pg n ((faceVerts pg n s).getD r 0) := by
  have hi := infix_getElem_pair hr'
  have h0 : (faceVerts pg n s)[0]'(by omega) = s.1 := by
    have := (faceVerts_start hP hs).1
    rwa [getD_of_lt (by omega)] at this
  have hlt : (faceVerts pg n s)[0]'(by omega) < (faceVerts pg n s)[r]'(by omega) :=
    List.pairwise_iff_getElem.mp faceVerts_pairwise 0 r (by omega) (by omega) (by omega)
  rw [getD_of_lt hr', getD_of_lt (by omega), lastNb_eq hP hs hi (by omega)]

/-- The slot id of the last face vertex is `0`. -/
theorem segId_last_slot {s : ℕ × ℕ} :
    segId pg n ((faceVerts pg n s).getD ((faceVerts pg n s).length - 1) 0,
      (faceVerts pg n s).getD ((faceVerts pg n s).length - 1 + 1) 0) = 0 := by
  have : (faceVerts pg n s).getD ((faceVerts pg n s).length - 1 + 1) 0 = 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
  rw [this]
  exact segId_of_lt (by omega)

theorem length_faceSids (s : ℕ × ℕ) : (faceSids pg n s).length = (faceVerts pg n s).length := by
  simp [faceSids]

theorem length_fsidCat : (fsidCat pg n).length = (faceCat pg n).length := by
  rw [fsidCat, faceCat, List.length_flatMap, List.length_flatMap]
  congr 1
  exact List.map_congr_left fun s _ => length_faceSids s

end FaceSlots

/-! ### The faces -/

section Faces

variable (pg : Graph) (n : ℕ)

/-- The number of face vertices of the first `j` segments of `segOrder`. -/
def fOff (j : ℕ) : ℕ := (((segOrder pg n).take j).flatMap (faceVerts pg n)).length

variable {pg n}

theorem fOff_zero : fOff pg n 0 = 0 := rfl

theorem fOff_succ {t : ℕ} (ht : t < (segOrder pg n).length) :
    fOff pg n (t + 1) = fOff pg n t + (faceVerts pg n (segOrder pg n)[t]).length := by
  rw [fOff, fOff, take_succ_segOrder ht, List.flatMap_append, List.length_append,
    List.flatMap_singleton]

theorem fOff_full : fOff pg n (segOrder pg n).length = (faceCat pg n).length := by
  rw [fOff, List.take_length]; rfl

theorem fOff_le_faceCat (t : ℕ) : fOff pg n t ≤ (faceCat pg n).length := by
  rw [fOff, faceCat]
  conv_rhs => rw [← List.take_append_drop t (segOrder pg n)]
  rw [List.flatMap_append, List.length_append]
  omega

theorem map_fOff : (List.range ((segOrder pg n).length + 1)).map (fOff pg n) = faceOffs pg n := by
  rw [faceOffs, prefixSums, List.length_map]
  apply List.map_congr_left
  intro j _
  rw [fOff, List.length_flatMap, List.map_take]

theorem length_pairs (l : List ℕ) : (pairs l).length = l.length - 1 := by
  rw [← List.length_map (f := Prod.fst), map_fst_pairs, List.length_dropLast]

/-- A slot belongs to one face only. -/
theorem slot_unique (hP : IsPolygon pg n) {s s' t : ℕ × ℕ} (hs' : s' ∈ IsPolygon.segs pg n) (hne : s' ≠ s) (hw : Within s' s)
    (h : t ∈ slots pg n s) (h' : t ∈ slots pg n s') : False := by
  rw [mem_slots] at h h'
  obtain ⟨hx, hy, hxy, -⟩ := (infix_pair_iff faceVerts_pairwise).mp h
  have hx' := (mem_faceVerts.mp hx).2.2 s' hs' hw hne
  have hy' := (mem_faceVerts.mp hy).2.2 s' hs' hw hne
  have h1 := hP.infix_faceVerts_lt hs' h'
  omega

/-- The slots of all faces, listed once each. -/
theorem slotsCat_nodup (hP : IsPolygon pg n) : ((segOrder pg n).flatMap (slots pg n)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun s _ => slots_nodup s, ?_⟩
  refine List.Pairwise.imp_of_mem (fun {s s'} hs hs' hne => ?_) segOrder_nodup
  have hs1 := mem_segOrder.mp hs
  have hs1' := mem_segOrder.mp hs'
  intro t ht ht'
  have hi := mem_slots.mp ht
  have h1 := hP.infix_faceVerts_lt hs1 hi
  have h1' := hP.infix_faceVerts_lt hs1' (mem_slots.mp ht')
  rcases hP.nested_of_within hs1 hs1' (e := t) h1.2.1 ⟨h1.1, h1.2.2.1⟩ ⟨h1'.1, h1'.2.2.1⟩ with
    hw | hw
  · exact slot_unique hP hs1 hne hw ht' ht
  · exact slot_unique hP hs1' (Ne.symm hne) hw ht ht'

/-- **The total length of the faces** is at most twice the number of edges. -/
theorem length_faceCat_le (hP : IsPolygon pg n) :
    (faceCat pg n).length ≤ 2 * pg.length := by
  have hsub : (segOrder pg n).flatMap (slots pg n) ⊆ pg := by
    intro t ht
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
    have hs1 := mem_segOrder.mp hs
    have hi := mem_slots.mp ht
    have hadj := hP.adj_of_infix_faceVerts hs1 hi
    have h1 := hP.infix_faceVerts_lt hs1 hi
    have := hadj.2
    simpa [edge, min_eq_left (show t.1 ≤ t.2 by omega), max_eq_right (show t.1 ≤ t.2 by omega)]
      using this
  have h1 := (slotsCat_nodup hP).length_le_of_subset hsub
  have h2 : (faceCat pg n).length =
      ((segOrder pg n).flatMap (slots pg n)).length + (segOrder pg n).length := by
    rw [faceCat, List.length_flatMap, List.length_flatMap]
    have : ∀ s ∈ segOrder pg n, (faceVerts pg n s).length = (slots pg n s).length + 1 := by
      intro s hs
      have := hP.three_le_length_faceVerts (mem_segOrder.mp hs)
      rw [slots, length_pairs]
      omega
    rw [List.map_congr_left this, List.sum_map_add]
    simp
  have h3 := length_segOrder (pg := pg) (n := n)
  have h4 := length_segEnum_le (pg := pg) (n := n)
  omega

/-- The slot ids of the first `t` segments. -/
abbrev doneS (pg : Graph) (n t : ℕ) : List ℕ := ((segOrder pg n).take t).flatMap (faceSids pg n)

theorem length_doneS (t : ℕ) : (doneS pg n t).length = fOff pg n t := by
  rw [doneS, fOff, List.length_flatMap, List.length_flatMap]
  congr 1
  exact List.map_congr_left fun s _ => length_faceSids s

theorem doneS_succ {t : ℕ} (ht : t < (segOrder pg n).length) :
    doneS pg n (t + 1) = doneS pg n t ++ faceSids pg n (segOrder pg n)[t] := by
  rw [doneS, take_succ_segOrder ht, List.flatMap_append, List.flatMap_singleton]

theorem doneS_full : doneS pg n (segOrder pg n).length = fsidCat pg n := by
  rw [doneS, List.take_length]; rfl

/-- The slot id of the face vertex `j` of the segment `t`, read off `fsidCat`. -/
theorem fsidCat_getD {t j : ℕ} (ht : t < (segOrder pg n).length)
    (hj : j < (faceVerts pg n (segOrder pg n)[t]).length) :
    (fsidCat pg n).getD (fOff pg n t + j) 0 =
      segId pg n ((faceVerts pg n (segOrder pg n)[t]).getD j 0,
        (faceVerts pg n (segOrder pg n)[t]).getD (j + 1) 0) := by
  have hS : segOrder pg n = (segOrder pg n).take t ++ (segOrder pg n)[t] ::
      (segOrder pg n).drop (t + 1) := by
    rw [← List.drop_eq_getElem_cons ht, List.take_append_drop]
  have e : fsidCat pg n = doneS pg n t ++ (faceSids pg n (segOrder pg n)[t] ++
      ((segOrder pg n).drop (t + 1)).flatMap (faceSids pg n)) := by
    rw [fsidCat]
    conv_lhs => rw [hS]
    rw [List.flatMap_append, List.flatMap_cons]
  have hj' : j < (faceSids pg n (segOrder pg n)[t]).length := by rw [length_faceSids]; exact hj
  rw [e, ← length_doneS, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left hj', List.getElem?_eq_getElem hj',
    Option.getD_some]
  simp [faceSids]

end Faces

end STACS2027.RAM.P1
