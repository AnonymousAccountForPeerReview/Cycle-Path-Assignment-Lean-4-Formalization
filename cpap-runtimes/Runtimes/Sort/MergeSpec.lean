module

public import Outerplanar.RAM.PairIdsSpec
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# A stable bottom-up merge sort: the abstract side

The indices `0, …, L − 1` of a key list `keys` (`L = |keys|`, keys arbitrary naturals) are
sorted stably by key, i.e. by `(key, index)`, by a bottom-up merge sort that only **compares**
keys (no memory indexed by a key):

* `mergeK keys xs ys`: the merge of two runs, the left run first on equal keys (the machine
  compares `key y < key x` by truncated subtraction);
* `sl a lo hi`: the slice `[lo, hi)` of the array `a`; `bk w a b = sl a (w b) (w b + w)`: block
  `b` of width `w`;
* `pass keys w a`: one pass, merging the blocks `2b` and `2b + 1` of width `w` into block `b` of
  width `2w` (`blk`); `sortP keys p`: `p` passes from `range L`.

**Invariant** (`Good w a`): every block of width `w` is sorted by `(key, index)` and holds
exactly the indices of its range. It holds for `w = 1` (`good_range`), passes preserve it
(`Good.pass`), and for `w ≥ L` the whole array is the stable sort (`Good.eq_sortKey`):
**`sortKey keys`**, the indices sorted by `List.mergeSort` on `(key, index)`, the unique
permutation of `range L` that is `Pairwise (KeyLt keys)` (`eq_sortKey`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Sort

open STACS2027.RAM STACS2027.RAM.PairIds
open scoped List

/-! ### The stable sort by `(key, index)` -/

section spec

variable (keys : List ℕ)

/-- The order `(key, index) ≤ (key', index')`. -/
def KeyLe (a b : ℕ) : Prop :=
  keys.getD a 0 < keys.getD b 0 ∨ (keys.getD a 0 = keys.getD b 0 ∧ a ≤ b)

instance (a b : ℕ) : Decidable (KeyLe keys a b) := by unfold KeyLe; infer_instance

/-- **The stable sort** of the indices `0, …, |keys| − 1` by key: `List.mergeSort` on
`(key, index)`. -/
def sortKey : List ℕ := (List.range keys.length).mergeSort fun a b => decide (KeyLe keys a b)

variable {keys}

theorem sortKey_perm : sortKey keys ~ List.range keys.length := List.mergeSort_perm _ _

theorem pairwise_sortKey : (sortKey keys).Pairwise (KeyLt keys) := by
  have h := List.pairwise_mergeSort (le := fun a b => decide (KeyLe keys a b))
    (fun a b c hab hbc => by simp only [KeyLe, decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [KeyLe, Bool.or_eq_true, decide_eq_true_eq]; omega)
    (List.range keys.length)
  have hnd : (sortKey keys).Nodup := sortKey_perm.symm.nodup List.nodup_range
  refine (h.and hnd).imp fun {a b} ⟨hab, hne⟩ => ?_
  simp only [KeyLe, decide_eq_true_eq] at hab
  unfold KeyLt; omega

/-- **Uniqueness**: a permutation of `range L` sorted by `(key, index)` is the stable sort. -/
theorem eq_sortKey {ord : List ℕ} (hp : ord ~ List.range keys.length)
    (hs : ord.Pairwise (KeyLt keys)) : ord = sortKey keys :=
  List.Perm.eq_of_pairwise (le := KeyLt keys)
    (fun a b _ _ h1 h2 => absurd (show KeyLt keys a a by unfold KeyLt at *; omega)
      (keyLt_irrefl keys a)) hs pairwise_sortKey (hp.trans sortKey_perm.symm)

theorem length_sortKey : (sortKey keys).length = keys.length := by
  rw [sortKey_perm.length_eq, List.length_range]

theorem lt_of_mem_sortKey {q : ℕ} (h : q ∈ sortKey keys) : q < keys.length :=
  List.mem_range.mp (sortKey_perm.mem_iff.mp h)

theorem mem_sortKey {q : ℕ} (h : q < keys.length) : q ∈ sortKey keys :=
  sortKey_perm.mem_iff.mpr (List.mem_range.mpr h)

end spec

/-! ### Merging two runs -/

section merge

variable (keys : List ℕ)

/-- **The merge** of two runs by key, the left run first on equal keys. -/
def mergeK : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    if keys.getD y 0 < keys.getD x 0 then y :: mergeK (x :: xs) ys else x :: mergeK xs (y :: ys)
termination_by xs ys => xs.length + ys.length

@[simp] theorem mergeK_nil_left (ys : List ℕ) : mergeK keys [] ys = ys := by
  rw [mergeK]

@[simp] theorem mergeK_nil_right (xs : List ℕ) : mergeK keys xs [] = xs := by
  cases xs <;> rw [mergeK]

theorem mergeK_cons_cons (x y : ℕ) (xs ys : List ℕ) :
    mergeK keys (x :: xs) (y :: ys) =
      if keys.getD y 0 < keys.getD x 0 then y :: mergeK keys (x :: xs) ys
      else x :: mergeK keys xs (y :: ys) := by
  rw [mergeK]

variable {keys}

theorem mergeK_perm : ∀ xs ys : List ℕ, mergeK keys xs ys ~ xs ++ ys
  | [], ys => by simp
  | x :: xs, [] => by simp
  | x :: xs, y :: ys => by
    rw [mergeK_cons_cons]
    split
    · exact ((mergeK_perm (x :: xs) ys).cons y).trans List.perm_middle.symm
    · exact (mergeK_perm xs (y :: ys)).cons x
termination_by xs ys => xs.length + ys.length

theorem mem_mergeK {xs ys : List ℕ} {z : ℕ} : z ∈ mergeK keys xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  rw [(mergeK_perm xs ys).mem_iff, List.mem_append]

theorem length_mergeK (xs ys : List ℕ) : (mergeK keys xs ys).length = xs.length + ys.length := by
  rw [(mergeK_perm xs ys).length_eq, List.length_append]

theorem key_le_of_keyLt {a b : ℕ} (h : KeyLt keys a b) : keys.getD a 0 ≤ keys.getD b 0 := by
  unfold KeyLt at h; omega

/-- **The merge of two sorted runs, every index of the first below every index of the second,
is sorted by `(key, index)`.** -/
theorem mergeK_pairwise : ∀ xs ys : List ℕ, xs.Pairwise (KeyLt keys) → ys.Pairwise (KeyLt keys) →
    (∀ x ∈ xs, ∀ y ∈ ys, x < y) → (mergeK keys xs ys).Pairwise (KeyLt keys)
  | [], ys, _, hy, _ => by simpa using hy
  | x :: xs, [], hx, _, _ => by simpa using hx
  | x :: xs, y :: ys, hx, hy, hsep => by
    rw [mergeK_cons_cons]
    split
    · rename_i hlt
      refine List.pairwise_cons.mpr ⟨fun z hz => ?_, mergeK_pairwise (x :: xs) ys hx
        (List.pairwise_cons.mp hy).2 fun a ha b hb => hsep a ha b (List.mem_cons_of_mem _ hb)⟩
      rcases mem_mergeK.mp hz with hz | hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl hlt
        · exact Or.inl (lt_of_lt_of_le hlt (key_le_of_keyLt ((List.pairwise_cons.mp hx).1 z hz)))
      · exact (List.pairwise_cons.mp hy).1 z hz
    · rename_i hle
      refine List.pairwise_cons.mpr ⟨fun z hz => ?_, mergeK_pairwise xs (y :: ys)
        (List.pairwise_cons.mp hx).2 hy fun a ha b hb => hsep a (List.mem_cons_of_mem _ ha) b hb⟩
      rcases mem_mergeK.mp hz with hz | hz
      · exact (List.pairwise_cons.mp hx).1 z hz
      · have hyz : keys.getD y 0 ≤ keys.getD z 0 := by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact le_rfl
          · exact key_le_of_keyLt ((List.pairwise_cons.mp hy).1 z hz)
        have hxz := hsep x List.mem_cons_self z hz
        unfold KeyLt; omega
termination_by xs ys => xs.length + ys.length

/-! #### One step of the merge, read off the runs -/

theorem mergeK_drop_left {xs ys : List ℕ} {p q : ℕ} (hp : p < xs.length)
    (h : ∀ hq : q < ys.length, keys.getD xs[p] 0 ≤ keys.getD ys[q] 0) :
    mergeK keys (xs.drop p) (ys.drop q) = xs[p] :: mergeK keys (xs.drop (p + 1)) (ys.drop q) := by
  rw [List.drop_eq_getElem_cons hp]
  by_cases hq : q < ys.length
  · rw [List.drop_eq_getElem_cons hq, mergeK_cons_cons]
    simp only [show ¬ keys.getD ys[q] 0 < keys.getD xs[p] 0 by have := h hq; omega, ↓reduceIte]
  · rw [List.drop_eq_nil_of_le (as := ys) (by omega), mergeK_nil_right, mergeK_nil_right]

theorem mergeK_drop_right {xs ys : List ℕ} {p q : ℕ} (hq : q < ys.length)
    (h : ∀ hp : p < xs.length, keys.getD ys[q] 0 < keys.getD xs[p] 0) :
    mergeK keys (xs.drop p) (ys.drop q) = ys[q] :: mergeK keys (xs.drop p) (ys.drop (q + 1)) := by
  rw [List.drop_eq_getElem_cons hq]
  by_cases hp : p < xs.length
  · rw [List.drop_eq_getElem_cons hp, mergeK_cons_cons]
    simp only [h hp, ↓reduceIte]
  · rw [List.drop_eq_nil_of_le (as := xs) (by omega), mergeK_nil_left, mergeK_nil_left]

/-- The merge so far: after `p` entries of `xs` and `q` of `ys`, the rest of the merge is the
merge of the rests. -/
def MState (xs ys : List ℕ) (p q : ℕ) : Prop :=
  p ≤ xs.length ∧ q ≤ ys.length ∧
    (mergeK keys xs ys).drop (p + q) = mergeK keys (xs.drop p) (ys.drop q)

theorem mState_zero (xs ys : List ℕ) : MState (keys := keys) xs ys 0 0 :=
  ⟨Nat.zero_le _, Nat.zero_le _, by simp⟩

/-- A step taking the left entry. -/
theorem MState.left {xs ys : List ℕ} {p q : ℕ} (h : MState (keys := keys) xs ys p q)
    (hp : p < xs.length) (hle : ∀ hq : q < ys.length, keys.getD xs[p] 0 ≤ keys.getD ys[q] 0) :
    (mergeK keys xs ys).getD (p + q) 0 = xs[p] ∧ MState (keys := keys) xs ys (p + 1) q := by
  obtain ⟨-, hq, he⟩ := h
  have e := mergeK_drop_left hp hle
  rw [← he] at e
  have hl : p + q < (mergeK keys xs ys).length := by
    rw [length_mergeK]; omega
  rw [List.drop_eq_getElem_cons hl] at e
  obtain ⟨e1, e2⟩ := List.cons.inj e
  refine ⟨by rw [getD_eq_getElem' hl, e1], by omega, hq, ?_⟩
  rw [show p + 1 + q = p + q + 1 by omega, e2]

/-- A step taking the right entry. -/
theorem MState.right {xs ys : List ℕ} {p q : ℕ} (h : MState (keys := keys) xs ys p q)
    (hq : q < ys.length) (hlt : ∀ hp : p < xs.length, keys.getD ys[q] 0 < keys.getD xs[p] 0) :
    (mergeK keys xs ys).getD (p + q) 0 = ys[q] ∧ MState (keys := keys) xs ys p (q + 1) := by
  obtain ⟨hp, -, he⟩ := h
  have e := mergeK_drop_right hq hlt
  rw [← he] at e
  have hl : p + q < (mergeK keys xs ys).length := by
    rw [length_mergeK]; omega
  rw [List.drop_eq_getElem_cons hl] at e
  obtain ⟨e1, e2⟩ := List.cons.inj e
  refine ⟨by rw [getD_eq_getElem' hl, e1], hp, by omega, ?_⟩
  rw [show p + (q + 1) = p + q + 1 by omega, e2]

end merge

/-! ### Slices and blocks -/

section slices

/-- The slice `[lo, hi)` of `a` (truncated at the end of `a`). -/
def sl (a : List ℕ) (lo hi : ℕ) : List ℕ := (a.drop lo).take (hi - lo)

theorem length_sl (a : List ℕ) (lo hi : ℕ) : (sl a lo hi).length = min hi a.length - lo := by
  simp only [sl, List.length_take, List.length_drop]; omega

theorem getElem_sl {a : List ℕ} {lo hi p : ℕ} (hp : p < (sl a lo hi).length) :
    (sl a lo hi)[p] = a[lo + p]'(by rw [length_sl] at hp; omega) := by
  simp [sl]

/-- Block `b` of width `w`. -/
def bk (w : ℕ) (a : List ℕ) (b : ℕ) : List ℕ := sl a (w * b) (w * b + w)

theorem length_flatMap_range {f : ℕ → List ℕ} {c L : ℕ}
    (hf : ∀ b, (f b).length = min (c * b + c) L - min (c * b) L) :
    ∀ n, ((List.range n).flatMap f).length = min (c * n) L
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range hf n]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hf]
    rw [show c * (n + 1) = c * n + c by ring]
    omega

theorem flatMap_range_eq_nil {f : ℕ → List ℕ} {m : ℕ} (h : ∀ i, m ≤ i → f i = []) (n : ℕ) :
    ((List.range n).map (fun x => m + x)).flatMap f = [] :=
  List.flatMap_eq_nil_iff.mpr fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    exact h _ (by omega)

/-- Blocks beyond the data are empty, so the number of blocks does not matter. -/
theorem flatMap_range_congr {f : ℕ → List ℕ} {m n : ℕ} (h : ∀ i, min m n ≤ i → f i = []) :
    (List.range m).flatMap f = (List.range n).flatMap f := by
  rcases Nat.le_total m n with hmn | hmn
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [List.range_add, List.flatMap_append, flatMap_range_eq_nil (fun i hi => h i (by omega)),
      List.append_nil]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [List.range_add, List.flatMap_append, flatMap_range_eq_nil (fun i hi => h i (by omega)),
      List.append_nil]

/-- **A slice of a concatenation of blocks** of width `c`, at a block boundary, is the block. -/
theorem sl_flatMap {f : ℕ → List ℕ} {c L n : ℕ} (hc : 0 < c) (hn : L ≤ c * n)
    (hf : ∀ b, (f b).length = min (c * b + c) L - min (c * b) L) (b : ℕ) :
    sl ((List.range n).flatMap f) (c * b) (c * b + c) = f b := by
  have hlen := length_flatMap_range hf n
  rw [Nat.min_eq_right hn] at hlen
  by_cases hb : L ≤ c * b
  · have h1 : f b = [] := List.eq_nil_of_length_eq_zero (by rw [hf]; omega)
    rw [h1, sl, List.drop_eq_nil_of_le (by omega), List.take_nil]
  · have hbn : b < n := by
      by_contra h'
      have : c * n ≤ c * b := Nat.mul_le_mul_left _ (by omega)
      omega
    have hsplit : (List.range n).flatMap f =
        (List.range b).flatMap f ++ (f b ++ ((List.range (n - b - 1)).map
          (fun x => (b + 1) + x)).flatMap f) := by
      conv_lhs => rw [show n = b + (1 + (n - b - 1)) by omega, List.range_add, List.range_add]
      simp only [List.flatMap_append, List.map_append, List.range_one, List.map_cons,
        List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero,
        List.map_map]
      congr 3
      refine List.map_congr_left fun x _ => ?_
      simp only [Function.comp_apply]
      omega
    have hpre := length_flatMap_range hf b
    rw [Nat.min_eq_left (by omega)] at hpre
    rw [hsplit, sl, List.drop_left' hpre, Nat.add_sub_cancel_left, List.take_append]
    by_cases hfull : c * b + c ≤ L
    · have hlb : (f b).length = c := by rw [hf]; omega
      rw [List.take_of_length_le (by omega), hlb, Nat.sub_self, List.take_zero, List.append_nil]
    · rw [flatMap_range_eq_nil (fun i hi => List.eq_nil_of_length_eq_zero (by
        rw [hf]
        have : c * (b + 1) ≤ c * i := Nat.mul_le_mul_left _ hi
        rw [show c * (b + 1) = c * b + c by ring] at this
        omega)), List.take_nil, List.append_nil, List.take_of_length_le (by rw [hf]; omega)]

end slices

/-! ### Passes -/

section passes

variable (keys : List ℕ)

/-- The merge of the blocks `2b` and `2b + 1` of width `w`. -/
def blk (w : ℕ) (a : List ℕ) (b : ℕ) : List ℕ := mergeK keys (bk w a (2 * b)) (bk w a (2 * b + 1))

/-- **One pass** of width `w`: the merges of the pairs of blocks. -/
def pass (w : ℕ) (a : List ℕ) : List ℕ := (List.range a.length).flatMap (blk keys w a)

/-- **`p` passes** from `range L` (widths `1, 2, …, 2^{p−1}`). -/
def sortP : ℕ → List ℕ
  | 0 => List.range keys.length
  | p + 1 => pass keys (2 ^ p) (sortP p)

/-- **The invariant of the passes**: every block of width `w` is sorted by `(key, index)` and
holds exactly the indices of its range. -/
structure Good (w : ℕ) (a : List ℕ) : Prop where
  len : a.length = keys.length
  sorted : ∀ b, (bk w a b).Pairwise (KeyLt keys)
  perm : ∀ b, bk w a b ~ List.range' (w * b) (min (w * b + w) keys.length - w * b)

variable {keys}

theorem bk_one_range {L b : ℕ} (hb : b < L) : bk 1 (List.range L) b = [b] :=
  List.ext_getElem (by rw [bk, length_sl]; simp; omega) fun i h1 h2 => by
    simp only [List.length_singleton, Nat.lt_one_iff] at h2
    subst h2
    simp [bk, sl]

theorem bk_one_range_nil {L b : ℕ} (hb : L ≤ b) : bk 1 (List.range L) b = [] :=
  List.eq_nil_of_length_eq_zero (by rw [bk, length_sl]; simp; omega)

theorem good_range : Good keys 1 (List.range keys.length) := by
  refine ⟨List.length_range, fun b => ?_, fun b => ?_⟩
  · by_cases hb : b < keys.length
    · rw [bk_one_range hb]; exact List.pairwise_singleton _ _
    · rw [bk_one_range_nil (by omega)]; exact List.Pairwise.nil
  · by_cases hb : b < keys.length
    · rw [bk_one_range hb, one_mul, show min (b + 1) keys.length - b = 1 by omega]
      simp
    · rw [bk_one_range_nil (by omega), one_mul, show min (b + 1) keys.length - b = 0 by omega]
      simp

theorem Good.length_bk {w : ℕ} {a : List ℕ} (h : Good keys w a) (b : ℕ) :
    (bk w a b).length = min (w * b + w) keys.length - w * b := by
  rw [(h.perm b).length_eq, List.length_range']

theorem Good.mem_bk {w : ℕ} {a : List ℕ} (h : Good keys w a) {b x : ℕ} (hx : x ∈ bk w a b) :
    w * b ≤ x ∧ x < min (w * b + w) keys.length := by
  have := List.mem_range'_1.mp ((h.perm b).mem_iff.mp hx)
  omega

theorem Good.length_blk {w : ℕ} {a : List ℕ} (h : Good keys w a) (b : ℕ) :
    (blk keys w a b).length =
      min (2 * w * b + 2 * w) keys.length - min (2 * w * b) keys.length := by
  rw [blk, length_mergeK, h.length_bk, h.length_bk]
  rw [show w * (2 * b) = 2 * w * b by ring, show w * (2 * b + 1) = 2 * w * b + w by ring]
  omega

theorem Good.blk_sorted {w : ℕ} {a : List ℕ} (h : Good keys w a) (b : ℕ) :
    (blk keys w a b).Pairwise (KeyLt keys) :=
  mergeK_pairwise _ _ (h.sorted _) (h.sorted _) fun x hx y hy => by
    have h1 := h.mem_bk hx
    have h2 := h.mem_bk hy
    rw [show w * (2 * b + 1) = w * (2 * b) + w by ring] at h2
    omega

theorem Good.blk_perm {w : ℕ} {a : List ℕ} (h : Good keys w a) (b : ℕ) :
    blk keys w a b ~ List.range' (2 * w * b) (min (2 * w * b + 2 * w) keys.length - 2 * w * b) := by
  refine (mergeK_perm _ _).trans ((List.Perm.append (h.perm _) (h.perm _)).trans ?_)
  rw [show w * (2 * b) = 2 * w * b by ring, show w * (2 * b + 1) = 2 * w * b + w by ring]
  set L := keys.length
  by_cases hw : 2 * w * b + w ≤ L
  · rw [show min (2 * w * b + w) L - 2 * w * b = w by omega]
    have := List.range'_append (s := 2 * w * b) (m := w)
      (n := min (2 * w * b + w + w) L - (2 * w * b + w)) (step := 1)
    rw [one_mul] at this
    rw [this, show w + (min (2 * w * b + w + w) L - (2 * w * b + w)) =
      min (2 * w * b + 2 * w) L - 2 * w * b by omega]
  · rw [show min (2 * w * b + w + w) L - (2 * w * b + w) = 0 by omega, List.range'_zero,
      List.append_nil, show min (2 * w * b + w) L - 2 * w * b =
        min (2 * w * b + 2 * w) L - 2 * w * b by omega]

theorem Good.length_pass {w : ℕ} {a : List ℕ} (h : Good keys w a) (hw : 0 < w) :
    (pass keys w a).length = keys.length := by
  rw [pass, length_flatMap_range (c := 2 * w) (L := keys.length) h.length_blk, h.len]
  exact Nat.min_eq_right (by nlinarith)

/-- Block `b` of width `2w` after the pass is the merge of the blocks `2b`, `2b + 1`. -/
theorem Good.bk_pass {w : ℕ} {a : List ℕ} (h : Good keys w a) (hw : 0 < w) (b : ℕ) :
    bk (2 * w) (pass keys w a) b = blk keys w a b := by
  rw [bk, pass]
  exact sl_flatMap (by omega) (by rw [h.len]; nlinarith) h.length_blk b

/-- **A pass preserves the invariant**, doubling the width. -/
theorem Good.next {w : ℕ} {a : List ℕ} (h : Good keys w a) (hw : 0 < w) :
    Good keys (2 * w) (pass keys w a) :=
  ⟨h.length_pass hw, fun b => by rw [h.bk_pass hw]; exact h.blk_sorted b,
    fun b => by rw [h.bk_pass hw]; exact h.blk_perm b⟩

/-- The invariant after `p` passes. -/
theorem good_sortP : ∀ p, Good keys (2 ^ p) (sortP keys p)
  | 0 => good_range
  | p + 1 => by
    rw [sortP, pow_succ, Nat.mul_comm]
    exact (good_sortP p).next (by positivity)

/-- **With one block, the array is the stable sort.** -/
theorem Good.eq_sortKey {w : ℕ} {a : List ℕ} (h : Good keys w a) (hw : keys.length ≤ w) :
    a = sortKey keys := by
  have hb : bk w a 0 = a := by
    rw [bk, sl, Nat.mul_zero, List.drop_zero, Nat.zero_add, Nat.sub_zero,
      List.take_of_length_le (by rw [h.len]; exact hw)]
  have hp := h.perm 0
  have hs := h.sorted 0
  rw [hb, Nat.mul_zero, Nat.zero_add, Nat.sub_zero, Nat.min_eq_right hw] at hp
  rw [hb] at hs
  exact Sort.eq_sortKey (by rwa [List.range_eq_range']) hs

/-- **`clog₂ L` passes sort.** -/
theorem sortP_clog : sortP keys (Nat.clog 2 keys.length) = sortKey keys :=
  (good_sortP _).eq_sortKey (Nat.le_pow_clog (by norm_num) _)

/-- The prefix of a pass after the merges of the first `b` blocks. -/
theorem Good.length_passPre {w : ℕ} {a : List ℕ} (h : Good keys w a) (b : ℕ) :
    ((List.range b).flatMap (blk keys w a)).length = min (2 * w * b) keys.length :=
  length_flatMap_range h.length_blk b

/-- The prefix after the last block is the whole pass. -/
theorem Good.passPre_full {w : ℕ} {a : List ℕ} (h : Good keys w a) (hw : 0 < w) {b : ℕ}
    (hb : keys.length ≤ 2 * w * b) :
    (List.range b).flatMap (blk keys w a) = Sort.pass keys w a := by
  rw [Sort.pass, h.len]
  refine flatMap_range_congr fun i hi => List.eq_nil_of_length_eq_zero ?_
  rw [h.length_blk]
  have : keys.length ≤ 2 * w * i := by
    rcases Nat.le_total b keys.length with hbL | hbL
    · exact le_trans hb (Nat.mul_le_mul_left _ (by omega))
    · have : keys.length ≤ 2 * w * keys.length := by nlinarith
      exact le_trans this (Nat.mul_le_mul_left _ (by omega))
  omega

end passes

end STACS2027.Runtimes.Sort
