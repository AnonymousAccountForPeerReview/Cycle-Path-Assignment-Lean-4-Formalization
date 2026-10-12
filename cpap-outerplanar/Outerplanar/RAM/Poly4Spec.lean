module

public import Outerplanar.RAM.Poly1Spec
public import Outerplanar.Algo.PolyBacktrack
public import Outerplanar.Algo.PolyBounds
import Mathlib.Tactic

/-!
# Phase P4 of the polygon solver (backtracking and output): the abstract side

Facts used by the machine of phase P4 (`Outerplanar/RAM/Poly4.lean`), without the machine:

* `wr m b l`: the memory `m` with the list `l` written at `b, b + 1, …` (`wr_snoc`, `arr_wr`,
  `wr_of_lt`, `wr_of_ge`, `sameOn_wr`, `zeroFrom_wr`);
* base-`k` numbers: `enc_take_succ` (accumulating the digits with powers of `k`),
  `cfg_take_succ`, `div_pow_succ`;
* `pairs_eq` (the slots by index), `map_rotateTo` (a rotated cycle by index),
  `lkp` and `getD_idxOf_rel` (the digit of a pool index in the configuration of a segment);
* the backtracking by suffixes of `segOrder`: `abAt m` (`abAt_zero`, `abAt_length`,
  `abAt_succ`, `abAt_fst_lt`), the children of the slots processed so far (`chPart`,
  `chPart_succ`, `chPart_full`), the value of a cycle under the second component
  (`valAt`, `valAt_update_self`, `valAt_update_ne`);
* the starts `tst j` of the cycles with top `segOrder[j]` (`topIdx_tst`, `mem_tst`,
  `tst_length`) and the polygon facts (`length_cyc`, `lt_of_mem_cyc`, `mem_childSegs'`,
  `argTab_lt`, the bounds `length_bnd_le'`, `length_topIdx_le'`, `length_pool_le`);
* reading the interface arrays: `arr_prefixSums_get`, `arr_flatMap_part`, `arr_pool`.
-/

@[expose] public section

namespace STACS2027.RAM.P4

open STACS2027.Poly

/-! ### Conditionals -/

theorem iteT {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : p) : (if p then a else b) = a := by
  simp [h]

theorem iteF {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) : (if p then a else b) = b := by
  simp [h]

/-- `getD` of a list of digits is a digit. -/
theorem getD_lt {k : ℕ} (hk : 0 < k) {l : List ℕ} (h : ∀ d ∈ l, d < k) (j : ℕ) : l.getD j 0 < k := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : l[j]? with
  | none => exact hk
  | some d => exact h d (List.mem_of_getElem? hj)

/-! ### Writing a block of memory -/

/-- The memory `m` with the list `l` written at `b, b + 1, …`. -/
def wr (m : ℕ → ℕ) (b : ℕ) (l : List ℕ) : ℕ → ℕ :=
  fun a => if b ≤ a ∧ a < b + l.length then l.getD (a - b) 0 else m a

theorem wr_nil (m : ℕ → ℕ) (b : ℕ) : wr m b [] = m := by
  funext a; simp only [wr, List.length_nil, Nat.add_zero]; split <;> [omega; rfl]

theorem wr_of_lt {m : ℕ → ℕ} {b a : ℕ} (l : List ℕ) (h : a < b) : wr m b l a = m a := by
  simp only [wr]; split <;> [omega; rfl]

theorem wr_of_ge {m : ℕ → ℕ} {b a : ℕ} {l : List ℕ} (h : b + l.length ≤ a) : wr m b l a = m a := by
  simp only [wr]; split <;> [omega; rfl]

theorem wr_snoc (m : ℕ → ℕ) (b : ℕ) (l : List ℕ) (v : ℕ) :
    wr m b (l ++ [v]) = upd (wr m b l) (b + l.length) v := by
  funext a
  simp only [wr, upd_apply, List.length_append, List.length_singleton]
  by_cases ha : a = b + l.length
  · subst ha
    simp only [Nat.le_add_right, true_and, show b + l.length < b + (l.length + 1) by omega,
      ↓reduceIte, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
  · simp only [ha, ↓reduceIte]
    by_cases h : b ≤ a ∧ a < b + l.length
    · rw [iteT ⟨h.1, by omega⟩, iteT h, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    · rw [iteF (by omega), iteF h]

theorem arr_wr (m : ℕ → ℕ) (b : ℕ) (l : List ℕ) : Arr (wr m b l) b l := by
  intro i hi
  simp only [wr, Nat.le_add_right, true_and, Nat.add_lt_add_iff_left, hi, ↓reduceIte,
    Nat.add_sub_cancel_left]
  exact getD_eq_getElem' hi

theorem sameOn_wr {F b : ℕ} {m₀ m : ℕ → ℕ} (h : SameOn (· < F) m₀ m) (hb : F ≤ b) (l : List ℕ) :
    SameOn (· < F) m₀ (wr m b l) := fun a (ha : a < F) => by
  rw [wr_of_lt l (by omega)]; exact h a ha

theorem zeroFrom_wr {F b : ℕ} {m : ℕ → ℕ} {l : List ℕ} (h : ZeroFrom m F) (hb : b + l.length ≤ F) :
    ZeroFrom (wr m b l) F := fun a ha => by
  rw [wr_of_ge (by omega)]; exact h a ha

/-! ### Base-`k` numbers -/

theorem enc_append (k : ℕ) : ∀ l m : List ℕ, enc k (l ++ m) = enc k l + k ^ l.length * enc k m
  | [], m => by simp [enc]
  | d :: l, m => by
    simp only [List.cons_append, enc, enc_append k l m, List.length_cons, pow_succ]
    ring

/-- Accumulating the digits with powers of `k`. -/
theorem enc_take_succ (k : ℕ) (l : List ℕ) {q : ℕ} (hq : q < l.length) :
    enc k (l.take (q + 1)) = enc k (l.take q) + l[q] * k ^ q := by
  rw [List.take_add_one, List.getElem?_eq_getElem hq, Option.toList_some, enc_append,
    List.length_take, min_eq_left hq.le]
  simp [enc]; ring

theorem cfg_take_succ (k L x : ℕ) {t : ℕ} (ht : t < L) :
    (cfg k L x).take (t + 1) = (cfg k L x).take t ++ [x / k ^ t % k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using ht), Option.toList_some,
    getElem_cfg]

theorem div_pow_succ (x k t : ℕ) : x / k ^ t / k = x / k ^ (t + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-! ### Slots, rotations, digits -/

/-- The consecutive pairs of a list, by index. -/
theorem pairs_eq : ∀ l : List ℕ,
    pairs l = (List.range (l.length - 1)).map fun q => (l.getD q 0, l.getD (q + 1) 0)
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    rw [pairs, pairs_eq (y :: rest)]
    simp only [List.length_cons, Nat.add_sub_cancel, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    congr 1

/-- A rotated `k`-cycle, by index. -/
theorem map_rotateTo (g : ℕ → ℕ) {u : List ℕ} {v k : ℕ} (hu : u.length = k) (hv : v < k) :
    (rotateTo u v).map g = (List.range k).map fun t => g (u.getD ((v + t) % k) 0) := by
  apply List.ext_getElem
  · simp [rotateTo, hu]; omega
  intro t h1 h2
  have ht : t < k := by simpa using h2
  simp only [List.getElem_map, List.getElem_range, rotateTo]
  congr 1
  by_cases hlt : v + t < k
  · rw [List.getElem_append_left (by simp; omega), List.getElem_drop, Nat.mod_eq_of_lt hlt,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  · have hmod : (v + t) % k = v + t - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [List.getElem_append_right (by simp; omega), List.getElem_take, hmod,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    simp only [List.length_drop]
    omega

/-- The digit found by the machine for the pool index `i`: its digit in `ds` if it is in
`l`, else the value `vv i` if `ts ≤ i < te`, else `0`. -/
def lkp (l ds : List ℕ) (ts te : ℕ) (vv : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ∈ l then ds.getD (l.idxOf i) 0 else if ts ≤ i ∧ i < te then vv i else 0

theorem idxOf_range' {s c i : ℕ} (h : s ≤ i ∧ i < s + c) : (List.range' s c).idxOf i = i - s := by
  have hlt : i - s < (List.range' s c).length := by simp; omega
  have he : (List.range' s c)[i - s] = i := by simp; omega
  conv_lhs => rw [← he]
  exact (List.nodup_range' (s := s) (n := c)).idxOf_getElem _ hlt

/-- **The digit of a pool index** in the configuration `cfg α ++ cfg β` of a segment whose
relevant cycles are `l ++ range' ts nc`. -/
theorem getD_idxOf_rel (k α β : ℕ) (l : List ℕ) (ts nc i : ℕ) :
    (cfg k l.length α ++ cfg k nc β).getD ((l ++ List.range' ts nc).idxOf i) 0 =
      lkp l (cfg k l.length α) ts (ts + nc) (fun x => β / k ^ (x - ts) % k) i := by
  unfold lkp
  by_cases hl : i ∈ l
  · have hlt := List.idxOf_lt_length_iff.mpr hl
    rw [List.idxOf_append_of_mem hl, iteT hl, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simpa using hlt), ← List.getD_eq_getElem?_getD]
  · rw [iteF hl]
    have hidx : (l ++ List.range' ts nc).idxOf i = l.length + (List.range' ts nc).idxOf i := by
      induction l with
      | nil => simp
      | cons x l ih =>
        rw [List.mem_cons, not_or] at hl
        rw [List.cons_append, List.idxOf_cons_ne _ (Ne.symm hl.1), ih hl.2, List.length_cons]
        omega
    rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
      length_cfg, Nat.add_sub_cancel_left]
    by_cases hr : ts ≤ i ∧ i < ts + nc
    · rw [iteT hr, idxOf_range' hr, List.getElem?_eq_getElem (by simp; omega),
        Option.getD_some, getElem_cfg]
    · rw [iteF hr, List.idxOf_eq_length (by rw [List.mem_range'_1]; exact hr),
        List.getElem?_eq_none (by simp)]
      rfl

/-! ### The backtracking by suffixes -/

section Back

variable (pg : Graph) (n k : ℕ)

/-- The backtracking state after the segments `segOrder[m], …` (processed last first). -/
def abAt (m : ℕ) : (ℕ × ℕ → ℕ) × (ℕ × ℕ → ℕ) :=
  ((segOrder pg n).drop m).foldr (btStep pg n k) (fun _ => 0, fun _ => 0)

/-- The value of the pool cycle `i` under the configurations `B` of the segments. -/
def valAt (B : ℕ × ℕ → ℕ) (i : ℕ) : ℕ :=
  B (topOf (cyc pg n k i)) / k ^ ((topIdx pg n k (topOf (cyc pg n k i))).idxOf i) % k

/-- The number of cycles with top `t`. -/
def rpLen (t : ℕ × ℕ) : ℕ := (rpF pg n k n t.1 t.2 k).length

/-- The start of the cycles with top `segOrder[j]` in the pool. -/
def tst (j : ℕ) : ℕ := (((segOrder pg n).take j).map (rpLen pg n k)).sum

/-- The children among the first `q` slots of `s`. -/
def chPart (s : ℕ × ℕ) (q : ℕ) : List (ℕ × ℕ) :=
  ((slots pg n s).take q).filter fun t => decide (t.1 + 2 ≤ t.2)

/-- The configuration of the relevant cycles of `s`: `α` on the boundary cycles, `β` on the
cycles with top `s`. -/
def valsOf (s : ℕ × ℕ) (α β : ℕ) : List ℕ :=
  cfg k (bnd pg n k s).length α ++ cfg k (topIdx pg n k s).length β

/-- The first component after the first `q` slots of `s` (from `f`, with `α`, `β`). -/
def fPart (s : ℕ × ℕ) (α β : ℕ) (f : ℕ × ℕ → ℕ) (q : ℕ) : ℕ × ℕ → ℕ :=
  (chPart pg n s q).foldl (fun f w => Function.update f w (childIdx pg n k s w (valsOf pg n k s α β))) f

variable {pg n k}

theorem abAt_zero : abAt pg n k 0 = backtrack pg n k := by
  rw [abAt, List.drop_zero, backtrack_eq]

theorem abAt_length : abAt pg n k (segOrder pg n).length = (fun _ => 0, fun _ => 0) := by
  rw [abAt, List.drop_length]; rfl

theorem abAt_succ {m : ℕ} (hm : m < (segOrder pg n).length) :
    abAt pg n k m = btStep pg n k (segOrder pg n)[m] (abAt pg n k (m + 1)) := by
  rw [abAt, List.drop_eq_getElem_cons hm, List.foldr_cons]; rfl

theorem abAt_succ_fst {m : ℕ} (hm : m < (segOrder pg n).length) :
    (abAt pg n k m).1 = fPart pg n k (segOrder pg n)[m] ((abAt pg n k (m + 1)).1 (segOrder pg n)[m])
      (argTab pg n k (segOrder pg n)[m] ((abAt pg n k (m + 1)).1 (segOrder pg n)[m]))
      (abAt pg n k (m + 1)).1 (slots pg n (segOrder pg n)[m]).length := by
  rw [abAt_succ hm, fPart, chPart, List.take_length]; rfl

theorem abAt_succ_snd {m : ℕ} (hm : m < (segOrder pg n).length) :
    (abAt pg n k m).2 = Function.update (abAt pg n k (m + 1)).2 (segOrder pg n)[m]
      (argTab pg n k (segOrder pg n)[m] ((abAt pg n k (m + 1)).1 (segOrder pg n)[m])) := by
  rw [abAt_succ hm]; rfl

/-- The configurations passed to the segments are below `k ^ |bnd|`. -/
theorem abAt_fst_lt (hk : 0 < k) (m : ℕ) (s : ℕ × ℕ) :
    (abAt pg n k m).1 s < k ^ (bnd pg n k s).length := by
  unfold abAt
  generalize (segOrder pg n).drop m = L
  induction L with
  | nil => exact Nat.pow_pos hk
  | cons t L ih =>
    rw [List.foldr_cons]
    simp only [btStep]
    rw [foldl_update_apply]
    split
    · refine lt_of_lt_of_eq (enc_lt hk _ ?_) (by simp)
      intro d hd
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hd
      refine getD_lt hk (fun d hd => ?_) _
      rcases List.mem_append.mp hd with h' | h'
      · exact cfg_lt hk _ _ d h'
      · exact cfg_lt hk _ _ d h'
    · exact ih

theorem chPart_zero (s : ℕ × ℕ) : chPart pg n s 0 = [] := by simp [chPart]

theorem chPart_full (s : ℕ × ℕ) : chPart pg n s (slots pg n s).length = childSegs pg n s := by
  rw [chPart, List.take_length]; rfl

theorem chPart_succ (s : ℕ × ℕ) {q : ℕ} (hq : q < (slots pg n s).length) :
    chPart pg n s (q + 1) = chPart pg n s q ++
      (if (slots pg n s)[q].1 + 2 ≤ (slots pg n s)[q].2 then [(slots pg n s)[q]] else []) := by
  rw [chPart, chPart, List.take_add_one, List.getElem?_eq_getElem hq, Option.toList_some,
    List.filter_append]
  congr 1
  by_cases h : (slots pg n s)[q].1 + 2 ≤ (slots pg n s)[q].2 <;> simp [h]

theorem fPart_zero (s : ℕ × ℕ) (α β : ℕ) (f : ℕ × ℕ → ℕ) : fPart pg n k s α β f 0 = f := by
  rw [fPart, chPart_zero]; rfl

theorem fPart_succ_child (s : ℕ × ℕ) (α β : ℕ) (f : ℕ × ℕ → ℕ) {q : ℕ}
    (hq : q < (slots pg n s).length) (h : (slots pg n s)[q].1 + 2 ≤ (slots pg n s)[q].2) :
    fPart pg n k s α β f (q + 1) = Function.update (fPart pg n k s α β f q) (slots pg n s)[q]
      (childIdx pg n k s (slots pg n s)[q] (valsOf pg n k s α β)) := by
  rw [fPart, chPart_succ s hq, iteT h, List.foldl_append]; rfl

theorem fPart_succ_side (s : ℕ × ℕ) (α β : ℕ) (f : ℕ × ℕ → ℕ) {q : ℕ}
    (hq : q < (slots pg n s).length) (h : ¬ (slots pg n s)[q].1 + 2 ≤ (slots pg n s)[q].2) :
    fPart pg n k s α β f (q + 1) = fPart pg n k s α β f q := by
  rw [fPart, chPart_succ s hq, iteF h, List.append_nil]; rfl

/-! ### The cycles with a given top -/

theorem tst_zero : tst pg n k 0 = 0 := by simp [tst]

theorem tst_succ {j : ℕ} (hj : j < (segOrder pg n).length) :
    tst pg n k (j + 1) = tst pg n k j + rpLen pg n k (segOrder pg n)[j] := by
  rw [tst, tst, P1.take_succ_segOrder hj, List.map_append, List.sum_append]; simp

theorem tst_length : tst pg n k (segOrder pg n).length = (pool pg n k).length := by
  rw [tst, List.take_length, pool, List.length_flatMap]; rfl

theorem tst_mono {i j : ℕ} (h : i ≤ j) : tst pg n k i ≤ tst pg n k j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [tst, List.take_add, List.map_append, List.sum_append]
  omega

/-- The cycles with top `segOrder[j]`. -/
theorem topIdx_tst {j : ℕ} (hj : j < (segOrder pg n).length) :
    topIdx pg n k (segOrder pg n)[j] =
      List.range' (tst pg n k j) (rpLen pg n k (segOrder pg n)[j]) :=
  topIdx_eq (List.getElem?_eq_getElem hj)

theorem length_topIdx {j : ℕ} (hj : j < (segOrder pg n).length) :
    (topIdx pg n k (segOrder pg n)[j]).length = rpLen pg n k (segOrder pg n)[j] := by
  rw [topIdx_tst hj, List.length_range']

/-- **The cycles with top `segOrder[j]`** are the pool indices in `[tst j, tst (j + 1))`. -/
theorem mem_tst {j i : ℕ} (hj : j < (segOrder pg n).length) :
    tst pg n k j ≤ i ∧ i < tst pg n k (j + 1) ↔
      i < (pool pg n k).length ∧ topOf (cyc pg n k i) = (segOrder pg n)[j] := by
  rw [← mem_topIdx, topIdx_tst hj, List.mem_range'_1, tst_succ hj]

theorem valAt_update_self {B : ℕ × ℕ → ℕ} {j i : ℕ} (hj : j < (segOrder pg n).length) (β : ℕ)
    (hi : tst pg n k j ≤ i ∧ i < tst pg n k (j + 1)) :
    valAt pg n k (Function.update B (segOrder pg n)[j] β) i = β / k ^ (i - tst pg n k j) % k := by
  have h := ((mem_tst hj).mp hi).2
  rw [valAt, h, Function.update_self, topIdx_tst hj, idxOf_range' (by rw [← tst_succ hj]; exact hi)]

theorem valAt_update_ne {B : ℕ × ℕ → ℕ} {j i : ℕ} (hj : j < (segOrder pg n).length) (β : ℕ)
    (hi : tst pg n k (j + 1) ≤ i) (hp : i < (pool pg n k).length) :
    valAt pg n k (Function.update B (segOrder pg n)[j] β) i = valAt pg n k B i := by
  have hne : topOf (cyc pg n k i) ≠ (segOrder pg n)[j] := fun h => by
    have := (mem_tst hj).mpr ⟨hp, h⟩; omega
  rw [valAt, valAt, Function.update_of_ne hne]

end Back

/-! ### Polygon facts -/

section Poly

variable {pg : Graph} {n k : ℕ}

theorem cyc_mem_pool {i : ℕ} (hi : i < (pool pg n k).length) : cyc pg n k i ∈ pool pg n k := by
  rw [cyc_eq_getElem hi]; exact List.getElem_mem hi

theorem length_of_mem_pool (hP : IsPolygon pg n) (hk : 3 ≤ k) {u : List ℕ}
    (hu : u ∈ pool pg n k) : u.length = k := by
  rw [mem_pool hP hk, hP.mem_convexList] at hu
  exact hu.2

/-- The pool cycles have `k` entries. -/
theorem length_cyc (hP : IsPolygon pg n) (hk : 3 ≤ k) {i : ℕ} (hi : i < (pool pg n k).length) :
    (cyc pg n k i).length = k :=
  length_of_mem_pool hP hk (cyc_mem_pool hi)

/-- The entries of the pool cycles are positions. -/
theorem lt_of_mem_cyc (hP : IsPolygon pg n) (hk : 3 ≤ k) {i : ℕ} (hi : i < (pool pg n k).length)
    {x : ℕ} (hx : x ∈ cyc pg n k i) : x < n := by
  have h := cyc_mem_pool hi
  rw [mem_pool hP hk] at h
  simp only [convexList, List.mem_filter, List.mem_sublistsLen] at h
  exact List.mem_range.mp (h.1.1.subset hx)

/-- The children of a segment are segments. -/
theorem mem_childSegs' (hP : IsPolygon pg n) {s w : ℕ × ℕ} (hw : w ∈ childSegs pg n s) :
    w ∈ segOrder pg n ∧ w.1 + 2 ≤ w.2 ∧ w.2 < n := by
  have h := mem_segOrder.mpr ((mem_childSegs hP s w).mp hw).1
  exact ⟨h, P1.lt_of_mem_segOrder h⟩

/-- The minimizing configuration has `|topIdx s|` digits. -/
theorem argTab_lt (hk : 0 < k) (s : ℕ × ℕ) (α : ℕ) :
    argTab pg n k s α < k ^ (topIdx pg n k s).length := by
  unfold argTab
  generalize n = fuel
  cases fuel with
  | zero => exact Nat.pow_pos hk
  | succ f =>
    rw [tabArg_succ]
    exact (argmin_fold _ (Nat.pow_pos hk)).1

/-- The bound on the numbers of relevant cycles of a segment. -/
def Lk (k : ℕ) : ℕ := k * rpathBound k

theorem length_bnd_le' (hP : IsPolygon pg n) {s : ℕ × ℕ} (hs : s ∈ segOrder pg n) :
    (bnd pg n k s).length ≤ Lk k :=
  (length_bnd_le hP (by have := P1.lt_of_mem_segOrder hs; omega)).trans
    (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

theorem length_topIdx_le' (hP : IsPolygon pg n) (hk : 0 < k) (s : ℕ × ℕ) :
    (topIdx pg n k s).length ≤ Lk k :=
  (length_topIdx_le hP s).trans (Nat.le_mul_of_pos_left _ hk)

theorem length_pool_le (hP : IsPolygon pg n) :
    (pool pg n k).length ≤ pg.length * rpathBound k := by
  rw [← tst_length, tst, List.take_length]
  refine (List.sum_le_length_nsmul _ (rpathBound k) ?_).trans ?_
  · intro x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact length_rpF_le hP _ _ _ _
  · rw [List.length_map, smul_eq_mul, P1.length_segOrder]
    exact Nat.mul_le_mul_right _ P1.length_segEnum_le

end Poly

/-! ### Reading the interface arrays -/

theorem getD_prefixSums (l : List ℕ) {j : ℕ} (hj : j ≤ l.length) :
    (prefixSums l).getD j 0 = (l.take j).sum := by
  rw [prefixSums, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega)]
  rfl

theorem arr_prefixSums_get {α : Type*} {m : ℕ → ℕ} {b : ℕ} {S : List α} {f : α → ℕ}
    (h : Arr m b (prefixSums (S.map f))) {j : ℕ} (hj : j ≤ S.length) :
    m (b + j) = ((S.take j).map f).sum := by
  rw [h.getD (by simp [prefixSums]; omega), getD_prefixSums _ (by simpa using hj), List.map_take]

theorem arr_flatMap_part {α : Type*} {m : ℕ → ℕ} {b : ℕ} {S : List α} (g : α → List ℕ)
    (h : Arr m b (S.flatMap g)) {j : ℕ} (hj : j < S.length) :
    Arr m (b + ((S.take j).map fun t => (g t).length).sum) (g S[j]) := by
  have hS : S = S.take j ++ S[j] :: S.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  rw [hS, List.flatMap_append, List.flatMap_cons, arr_append] at h
  have := h.2.prefix
  rwa [List.length_flatMap] at this

/-- The pool cycle `i`, flattened at `b`, starts at `b + k * i`. -/
theorem arr_pool {pg : Graph} {n k : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k) {m : ℕ → ℕ} {b : ℕ}
    (h : Arr m b (pool pg n k).flatten) {i : ℕ} (hi : i < (pool pg n k).length) :
    Arr m (b + k * i) (cyc pg n k i) := by
  have h' : Arr m b ((pool pg n k).flatMap id) := by rw [List.flatMap_id]; exact h
  have hp := arr_flatMap_part id h' hi
  have hsum : (((pool pg n k).take i).map fun t => (id t).length).sum = k * i := by
    have hc : ∀ t ∈ (pool pg n k).take i, (id t).length = k := fun t ht =>
      length_of_mem_pool hP hk (List.mem_of_mem_take ht)
    rw [List.map_congr_left hc, List.map_const', List.sum_replicate, List.length_take,
      min_eq_left hi.le, smul_eq_mul, mul_comm]
  rw [hsum, ← cyc_eq_getElem hi] at hp
  exact hp

end STACS2027.RAM.P4
