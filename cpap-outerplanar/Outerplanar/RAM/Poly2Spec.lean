module

public import Outerplanar.RAM.Poly1
public import Outerplanar.Algo.PolyBounds
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver, abstract side: the region paths as the machine folds them

The region paths `rpF pg n k n a b L` are computed by the machine (`Outerplanar/RAM/Poly2.lean`)
once per segment, in the order `segOrder`, as the final list of partial paths of the fold over
the slots of the face (`fin`), with fuel `n` throughout. This file proves the facts used to
verify it:

* `rpF_eq_cfin`: for an edge `(x, y)` and `L ≠ 2`, `rpF … x y L` is read off the final partial
  paths `cfin x y` of `(x, y)` (empty for a side), by the number of edges;
* `extendParts_eq`: one step of the fold is the machine's step `extPe` on every partial path:
  the path through the slot itself (`emit2`), then for `l = 0, 1, …` the child's partial paths
  with `l + 2` edges (`emitL`), each appended;
* `finPre_succ`: the fold after `j + 1` slots, the slot `j` being read off the face vertices
  (`getElem_pairs`); `finPre_bound`: at most `partsBound k` partial paths, well formed;
* `enc`: partial paths stored as records `[edges, entries…]`; `arr_enc_get` reads the record
  `j` at the running offset `encOff`;
* `rpF_seg`: the cycles with top `s` are the final partial paths of `s` with `k` entries;
* `child_idx_lt`: a child segment is processed earlier.
-/

@[expose] public section

namespace STACS2027.RAM.P2

open STACS2027.Poly STACS2027.RAM.P1 IsPolygon

section Defs

variable (pg : Graph) (n k : ℕ)

/-- The partial paths of the fold of `rpF` (fuel `n`) over the first `j` slots of `s`. -/
def finPre (s : ℕ × ℕ) (j : ℕ) : List (List ℕ × ℕ) :=
  ((slots pg n s).take j).foldl (fun parts t => extendParts k (rpF pg n k n) parts t.1 t.2)
    [([s.1], 0)]

/-- The final partial paths of the segment `s` (fuel `n`). -/
def fin (s : ℕ × ℕ) : List (List ℕ × ℕ) :=
  (slots pg n s).foldl (fun parts t => extendParts k (rpF pg n k n) parts t.1 t.2) [([s.1], 0)]

/-- The final partial paths of the slot `(x, y)`: those of the segment `(x, y)`, or none for a
side. -/
def cfin (x y : ℕ) : List (List ℕ × ℕ) := if (x, y) ∈ segEnum pg n then fin pg n k (x, y) else []

end Defs

/-- The partial paths stored as records: the number of edges, then the entries. -/
def enc (parts : List (List ℕ × ℕ)) : List ℕ := parts.flatMap fun pe => pe.2 :: pe.1

/-- Well-formed partial paths: one entry more than edges. -/
def WF (parts : List (List ℕ × ℕ)) : Prop := ∀ pe ∈ parts, pe.1.length = pe.2 + 1

/-- The extension of `pe` by the slot path `[x, y]` (if the budget allows). -/
def emit2 (k : ℕ) (pe : List ℕ × ℕ) (y : ℕ) : List (List ℕ × ℕ) :=
  if pe.2 < k then [(pe.1 ++ [y], pe.2 + 1)] else []

/-- The extension of `pe` by the child's partial path `r` if it has `l + 2` edges. -/
def emitR (pe : List ℕ × ℕ) (l : ℕ) (r : List ℕ × ℕ) : List (List ℕ × ℕ) :=
  if r.2 = l + 2 then [(pe.1 ++ r.1.tail, pe.2 + r.2)] else []

/-- The extensions of `pe` by the child's partial paths with `l + 2` edges. -/
def emitL (pe : List ℕ × ℕ) (cf : List (List ℕ × ℕ)) (l : ℕ) : List (List ℕ × ℕ) :=
  cf.flatMap (emitR pe l)

/-- The machine's extension of `pe` through a slot ending at `y` with child paths `cf`. -/
def extPe (k : ℕ) (pe : List ℕ × ℕ) (y : ℕ) (cf : List (List ℕ × ℕ)) : List (List ℕ × ℕ) :=
  emit2 k pe y ++ (List.range (k - pe.2 - 1)).flatMap (emitL pe cf)

variable {pg : Graph} {n k : ℕ}

/-! ### Lists -/

theorem flatMap_ite_single {α β : Type*} (p : α → Prop) [DecidablePred p] (f : α → β) :
    ∀ l : List α, l.flatMap (fun a => if p a then [f a] else []) = (l.filter fun a => decide (p a)).map f
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, flatMap_ite_single p f l, List.filter_cons]
    by_cases h : p a <;> simp [h]

/-- The consecutive pairs of a list, by index. -/
theorem getElem_pairs : ∀ (l : List ℕ) (j : ℕ) (h : j < (pairs l).length),
    (pairs l)[j] = (l[j]'(by rw [length_pairs] at h; omega), l[j + 1]'(by rw [length_pairs] at h; omega))
  | [], j, h => by simp [pairs] at h
  | [_], j, h => by simp [pairs] at h
  | x :: y :: rest, 0, _ => by simp [pairs]
  | x :: y :: rest, j + 1, h => by
    simp only [pairs, List.getElem_cons_succ]
    exact getElem_pairs (y :: rest) j (by simp only [pairs, List.length_cons] at h; omega)

/-! ### Records -/

@[simp] theorem enc_nil : enc [] = [] := rfl

theorem enc_append (l₁ l₂ : List (List ℕ × ℕ)) : enc (l₁ ++ l₂) = enc l₁ ++ enc l₂ := by
  simp [enc]

theorem enc_cons (pe : List ℕ × ℕ) (l : List (List ℕ × ℕ)) : enc (pe :: l) = (pe.2 :: pe.1) ++ enc l := by
  simp [enc]

theorem enc_singleton (pe : List ℕ × ℕ) : enc [pe] = pe.2 :: pe.1 := by simp [enc]

theorem enc_flatMap {α : Type*} (f : α → List (List ℕ × ℕ)) (l : List α) :
    enc (l.flatMap f) = l.flatMap fun a => enc (f a) := by
  simp [enc, List.flatMap_assoc]

/-- The start of the record `j`. -/
def encOff (l : List (List ℕ × ℕ)) (j : ℕ) : ℕ := (enc (l.take j)).length

theorem encOff_succ {l : List (List ℕ × ℕ)} {j : ℕ} (hj : j < l.length) :
    encOff l (j + 1) = encOff l j + l[j].1.length + 1 := by
  simp only [encOff, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, enc_append,
    enc_singleton, List.length_append, List.length_cons]
  omega

theorem encOff_length (l : List (List ℕ × ℕ)) : encOff l l.length = (enc l).length := by
  simp [encOff]

theorem enc_take_succ {l : List (List ℕ × ℕ)} {j : ℕ} (hj : j < l.length) :
    enc (l.take (j + 1)) = enc (l.take j) ++ (l[j].2 :: l[j].1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, enc_append, enc_singleton]

/-- Reading the record `j`. -/
theorem arr_enc_get {m : ℕ → ℕ} {b : ℕ} {l : List (List ℕ × ℕ)} (h : Arr m b (enc l)) {j : ℕ}
    (hj : j < l.length) : m (b + encOff l j) = l[j].2 ∧ Arr m (b + encOff l j + 1) l[j].1 := by
  have he : enc l = enc (l.take j) ++ (l[j].2 :: l[j].1) ++ enc (l.drop (j + 1)) := by
    rw [← enc_take_succ hj, ← enc_append, List.take_append_drop]
  rw [he, arr_append, arr_append, arr_cons] at h
  exact ⟨h.1.2.1, h.1.2.2⟩

theorem encOff_le {l : List (List ℕ × ℕ)} {j : ℕ} (hj : j < l.length) :
    encOff l j + l[j].1.length + 1 ≤ (enc l).length := by
  rw [← encOff_succ hj, encOff]
  have h := congrArg (fun l' => (enc l').length) (List.take_append_drop (j + 1) l)
  simp only [enc_append, List.length_append] at h
  omega

/-! ### Region paths read off the final partial paths -/

theorem finPre_zero (s : ℕ × ℕ) : finPre pg n k s 0 = [([s.1], 0)] := rfl

theorem finPre_succ {s : ℕ × ℕ} {j : ℕ} (hj : j < (slots pg n s).length) :
    finPre pg n k s (j + 1) =
      extendParts k (rpF pg n k n) (finPre pg n k s j) (slots pg n s)[j].1 (slots pg n s)[j].2 := by
  rw [finPre, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.foldl_append]
  rfl

theorem finPre_full (s : ℕ × ℕ) : finPre pg n k s (slots pg n s).length = fin pg n k s := by
  rw [finPre, List.take_length]; rfl

/-- The partial paths during the fold: at most `partsBound k`, well formed. -/
theorem finPre_bound (hP : IsPolygon pg n) (s : ℕ × ℕ) (j : ℕ) :
    (finPre pg n k s j).length ≤ partsBound k ∧
      ∀ pe ∈ finPre pg n k s j, pe.2 ≤ k ∧ pe.1.length = pe.2 + 1 :=
  foldl_rpF_bound hP n s.1 ((slots pg n s).take j)

theorem fin_bound (hP : IsPolygon pg n) (s : ℕ × ℕ) :
    (fin pg n k s).length ≤ partsBound k ∧ ∀ pe ∈ fin pg n k s, pe.2 ≤ k ∧ pe.1.length = pe.2 + 1 :=
  foldl_rpF_bound hP n s.1 (slots pg n s)

theorem cfin_bound (hP : IsPolygon pg n) (x y : ℕ) :
    (cfin pg n k x y).length ≤ partsBound k ∧ ∀ pe ∈ cfin pg n k x y, pe.2 ≤ k ∧ pe.1.length = pe.2 + 1 := by
  unfold cfin
  split_ifs
  · exact fin_bound hP _
  · simp

/-- **`rpF` from the final partial paths**: for an edge `(x, y)` and `L ≠ 2`. -/
theorem rpF_eq_cfin (hP : IsPolygon pg n) {x y L : ℕ} (hxy : x < y) (hy : y < n) (hL : L ≠ 2) :
    rpF pg n k n x y L = ((cfin pg n k x y).filter fun pe => decide (pe.2 + 1 = L)).map Prod.fst := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [rpF_succ hL, cfin]
  split_ifs with hs
  · rw [fin, foldl_extendParts_congr]
    intro t ht L'
    have hlt := hP.infix_faceVerts_lt (mem_segEnum.mp hs) (mem_slots.mp ht)
    simp only at hlt
    exact rpF_fuel hP (by omega) (by omega)
  · rfl

/-- **One step of the fold** as the machine runs it. -/
theorem extendParts_eq (hP : IsPolygon pg n) {x y : ℕ} (hxy : x < y) (hy : y < n)
    (hadj : Adj pg x y) (parts : List (List ℕ × ℕ)) :
    extendParts k (rpF pg n k n) parts x y = parts.flatMap fun pe => extPe k pe y (cfin pg n k x y) := by
  unfold extendParts
  apply List.flatMap_congr
  intro pe _
  rcases Nat.eq_zero_or_pos (k - pe.2) with h | h
  · rw [h]
    simp [extPe, emit2, show ¬ pe.2 < k by omega, show k - pe.2 - 1 = 0 by omega]
  · obtain ⟨m, hm⟩ : ∃ m, k - pe.2 = m + 1 := ⟨k - pe.2 - 1, by omega⟩
    rw [hm, List.range'_succ, List.flatMap_cons, rpF_two, ite_eq_left ⟨hxy, hadj⟩, extPe, emit2,
      ite_eq_left (show pe.2 < k by omega), show k - pe.2 - 1 = m by omega,
      List.range'_eq_map_range, List.flatMap_map]
    simp only [List.map_cons, List.map_nil, List.tail_cons, List.singleton_append, List.cons.injEq]
    refine ⟨by simp, ?_⟩
    apply List.flatMap_congr
    intro l _
    rw [rpF_eq_cfin (L := 2 + 1 + l) hP hxy hy (by omega), emitL, List.map_map,
      show emitR pe l = fun r => if r.2 = l + 2 then [(pe.1 ++ r.1.tail, pe.2 + r.2)] else [] from rfl,
      flatMap_ite_single (fun r : List ℕ × ℕ => r.2 = l + 2) (fun r => (pe.1 ++ r.1.tail, pe.2 + r.2))]
    have hf : ((cfin pg n k x y).filter fun pe => decide (pe.2 + 1 = 2 + 1 + l)) =
        (cfin pg n k x y).filter fun r => decide (r.2 = l + 2) := by
      apply List.filter_congr; intro r _; simp only [decide_eq_decide]; omega
    rw [hf]
    apply List.map_congr_left
    intro r hr
    simp only [List.mem_filter, decide_eq_true_eq] at hr
    simp only [Function.comp_apply, hr.2, show 2 + 1 + l - 1 = l + 2 by omega]

/-- Filtering by the number of edges. -/
theorem filter_map_fst_eq (hk : 1 ≤ k) (l : List (List ℕ × ℕ)) :
    (l.filter fun pe => decide (pe.2 + 1 = k)).map Prod.fst =
      l.flatMap fun pe => if pe.2 = k - 1 then [pe.1] else [] := by
  rw [flatMap_ite_single (fun pe : List ℕ × ℕ => pe.2 = k - 1) Prod.fst]
  congr 1
  apply List.filter_congr
  intro pe _
  simp only [decide_eq_decide]
  omega

/-- **The cycles with top `s`**: the final partial paths of `s` with `k` entries. -/
theorem rpF_seg (hP : IsPolygon pg n) (hk : 3 ≤ k) {s : ℕ × ℕ} (hs : s ∈ segOrder pg n) :
    rpF pg n k n s.1 s.2 k = (fin pg n k s).flatMap fun pe => if pe.2 = k - 1 then [pe.1] else [] := by
  have h := lt_of_mem_segOrder hs
  rw [rpF_eq_cfin hP (by omega) h.2 (by omega), cfin,
    ite_eq_left (mem_segEnum.mpr (mem_segOrder.mp hs)), filter_map_fst_eq (by omega)]

/-! ### The children -/

/-- A slot `(x, y)` of the segment `t` that is a segment comes earlier in `segOrder`. -/
theorem child_idx_lt (hP : IsPolygon pg n) {t : ℕ} (ht : t < (segOrder pg n).length) {x y : ℕ}
    (hslot : (x, y) ∈ slots pg n (segOrder pg n)[t]) (hxy : (x, y) ∈ segOrder pg n) :
    (segOrder pg n).idxOf (x, y) < t := by
  have hs := mem_segOrder.mp (List.getElem_mem ht)
  have hlt := hP.infix_faceVerts_lt hs (mem_slots.mp hslot)
  simp only at hlt
  have hi := List.idxOf_lt_length_iff.mpr hxy
  have hget : (segOrder pg n)[(segOrder pg n).idxOf (x, y)] = (x, y) := List.getElem_idxOf hi
  by_contra hge
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hge) with h | h
  · have := List.pairwise_iff_getElem.mp segOrder_size t _ ht hi h
    rw [hget] at this
    simp only at this
    omega
  · have : (segOrder pg n)[t] = (x, y) := by simp only [h] at hget ⊢; exact hget
    rw [this] at hlt
    simp only at hlt
    omega

end STACS2027.RAM.P2
