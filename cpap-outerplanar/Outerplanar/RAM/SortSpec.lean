module

public import Outerplanar.RAM.Lib
import Mathlib.Tactic

/-!
# Stable counting sort, abstract side: buckets of indices by key

The stable counting sort `P1.csort` (`Poly1Sort.lean`) stores the indices of a key list,
grouped by key, increasing within a group (`bucketIdx`). This file proves the facts about
these lists (it was the first part of `Poly1Spec.lean`; it depends on no polygon, so that the
graph-level phases can sort too):

* `bkt keys i k`: the indices below `i` with key `k` (`bkt_succ`, `length_bkt_succ`,
  `length_bkt_mono`); `offOf keys k`: the number of keys below `k` (`offOf_succ`, `offOf_mono`,
  `offOf_eq_length`);
  `bucketIdx keys K`: the buckets concatenated (`length_bucketIdx`, `lt_of_mem_bucketIdx`);
* `map_bucketIdx`: reading a list of pairs `A` through `bucketIdx (A.map f) K` gives the
  pairs grouped by `f`, stably (`map_getD_filter_range`);
* `sum_range_eq`: finite sums over `Finset.range` as list sums.
-/

@[expose] public section

namespace STACS2027.RAM.P1


/-! ### Lists -/

/-- `getD` below the length. -/
theorem getD_of_lt {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) (d : α) :
    l.getD i d = l[i] := (List.getElem_eq_getD d).symm

/-- `getD` in the left part of an append. -/
theorem getD_append_of_lt {α : Type*} {l₁ l₂ : List α} {i : ℕ} (h : i < l₁.length) (d : α) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [getD_of_lt (by simp; omega), getD_of_lt h, List.getElem_append_left h]

/-! ### Sums -/

/-- A sum over `Finset.range` as a list sum. -/
theorem sum_range_eq (f : ℕ → ℕ) : ∀ N, ∑ j ∈ Finset.range N, f j = ((List.range N).map f).sum
  | 0 => rfl
  | N + 1 => by rw [Finset.sum_range_succ, List.sum_range_succ, sum_range_eq f N]

/-- A sum over the indices of a list. -/
theorem sum_range_getD {α : Type*} (f : α → ℕ) (d : α) (l : List α) :
    ∑ j ∈ Finset.range l.length, f (l.getD j d) = (l.map f).sum := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ, List.map_append,
      List.sum_append, ← ih]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [getD_append_of_lt (Finset.mem_range.mp hj)]
    · simp

/-! ### Bucketing by keys -/

/-- The indices below `i` whose key is `k`, in increasing order. -/
def bkt (keys : List ℕ) (i k : ℕ) : List ℕ := (List.range i).filter fun j => keys.getD j 0 = k

/-- The number of keys below `k` (the start of the bucket `k`). -/
def offOf (keys : List ℕ) (k : ℕ) : ℕ :=
  ((List.range k).map fun k' => (bkt keys keys.length k').length).sum

/-- The buckets `0, …, K - 1`, concatenated: a stable sort of the indices by key. -/
def bucketIdx (keys : List ℕ) (K : ℕ) : List ℕ := (List.range K).flatMap (bkt keys keys.length)

/-- The bucket counts, shifted by one (the counting pass of the sort). -/
def cntS (keys : List ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (bkt keys i k).length

theorem bkt_zero (keys : List ℕ) (k : ℕ) : bkt keys 0 k = [] := rfl

theorem bkt_succ (keys : List ℕ) (i k : ℕ) :
    bkt keys (i + 1) k = bkt keys i k ++ if keys.getD i 0 = k then [i] else [] := by
  simp only [bkt, List.range_succ, List.filter_append, List.filter_singleton]
  split <;> simp_all

theorem length_bkt_succ (keys : List ℕ) (i k : ℕ) :
    (bkt keys (i + 1) k).length = (bkt keys i k).length + if keys.getD i 0 = k then 1 else 0 := by
  rw [bkt_succ]; split <;> simp

theorem length_bkt_mono (keys : List ℕ) (k : ℕ) {i j : ℕ} (h : i ≤ j) :
    (bkt keys i k).length ≤ (bkt keys j k).length := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => rw [length_bkt_succ]; omega

theorem mem_bkt {keys : List ℕ} {i k j : ℕ} : j ∈ bkt keys i k ↔ j < i ∧ keys.getD j 0 = k := by
  simp [bkt]

theorem offOf_zero (keys : List ℕ) : offOf keys 0 = 0 := rfl

theorem offOf_succ (keys : List ℕ) (k : ℕ) :
    offOf keys (k + 1) = offOf keys k + (bkt keys keys.length k).length := by
  simp only [offOf, List.sum_range_succ]

theorem offOf_mono (keys : List ℕ) {k k' : ℕ} (h : k ≤ k') : offOf keys k ≤ offOf keys k' := by
  induction k', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k' _ ih => rw [offOf_succ]; omega

/-- The total size of the buckets `0, …, K - 1` among the first `i` indices. -/
theorem sum_bkt (keys : List ℕ) (K : ℕ) (hK : ∀ x ∈ keys, x < K) :
    ∀ i, i ≤ keys.length → ((List.range K).map fun k => (bkt keys i k).length).sum = i
  | 0, _ => by simp [bkt_zero]
  | i + 1, hi => by
    have ih := sum_bkt keys K hK i (by omega)
    have hk : keys.getD i 0 < K := by
      rw [getD_of_lt (by omega)]
      exact hK _ (List.getElem_mem _)
    rw [← sum_range_eq] at ih ⊢
    simp only [length_bkt_succ, Finset.sum_add_distrib, ih, Finset.sum_ite_eq,
      Finset.mem_range, hk, ↓reduceIte]

/-- `offOf keys K` is the number of keys when all keys are below `K`. -/
theorem offOf_eq_length (keys : List ℕ) (K : ℕ) (hK : ∀ x ∈ keys, x < K) :
    offOf keys K = keys.length := sum_bkt keys K hK _ le_rfl

/-- The sorted indices are as many as the keys. -/
theorem length_bucketIdx (keys : List ℕ) (K : ℕ) (hK : ∀ x ∈ keys, x < K) :
    (bucketIdx keys K).length = keys.length := by
  rw [bucketIdx, List.length_flatMap]
  exact sum_bkt keys K hK _ le_rfl

theorem lt_of_mem_bucketIdx {keys : List ℕ} {K x : ℕ} (h : x ∈ bucketIdx keys K) :
    x < keys.length := by
  simp only [bucketIdx, List.mem_flatMap, mem_bkt] at h
  obtain ⟨_, _, h, _⟩ := h
  exact h

/-- A bucket ends before the next starts. -/
theorem offOf_add_le (keys : List ℕ) {i k k' : ℕ} (hi : i ≤ keys.length) (hk : k < k') :
    offOf keys k + (bkt keys i k).length ≤ offOf keys k' := by
  have := length_bkt_mono keys k hi
  have := offOf_mono keys (show k + 1 ≤ k' by omega)
  rw [offOf_succ] at this
  omega

/-! ### Reading through the sorted indices -/

/-- The entries of `l` at the indices satisfying `p`, in order: `l.filter p`. -/
theorem map_getD_filter_range {β : Type*} (p : β → Bool) (d : β) :
    ∀ l : List β, ((List.range l.length).filter (fun i => p (l.getD i d))).map (l.getD · d) =
      l.filter p
  | [] => rfl
  | x :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map,
      List.filter_cons]
    have ih := map_getD_filter_range p d l
    have h1 : (List.filter ((fun i => p ((x :: l).getD i d)) ∘ Nat.succ) (List.range l.length)) =
        (List.range l.length).filter (fun i => p (l.getD i d)) := by
      apply List.filter_congr; intro i _; simp
    rw [h1]
    by_cases hx : p x = true
    · simp only [List.getD_cons_zero, hx, ↓reduceIte, List.map_cons, List.map_map]
      rw [← ih]
      congr 1
    · simp only [List.getD_cons_zero, hx, Bool.false_eq_true, ↓reduceIte, List.map_map]
      rw [← ih]
      apply List.map_congr_left; intro i _; simp

/-- A `getD` of a mapped list below its length. -/
theorem getD_map_lt {α : Type*} {l : List α} {f : α → ℕ} {i : ℕ} (h : i < l.length) (d : α) :
    (l.map f).getD i 0 = f (l.getD i d) := by
  rw [getD_of_lt (by simpa using h), getD_of_lt h, List.getElem_map]

/-- The bucket `k` of the keys `A.map f`, read off `A.map g`. -/
theorem map_bkt {α : Type*} (A : List α) (d : α) (f g : α → ℕ) (k : ℕ) :
    (bkt (A.map f) A.length k).map (fun i => (A.map g).getD i 0) =
      (A.filter fun x => f x = k).map g := by
  have h := map_getD_filter_range (fun x => decide (f x = k)) d A
  rw [← h, List.map_map]
  unfold bkt
  have hf : (List.range A.length).filter (fun j => decide ((A.map f).getD j 0 = k)) =
      (List.range A.length).filter (fun i => decide (f (A.getD i d) = k)) := by
    apply List.filter_congr
    intro i hi
    rw [getD_map_lt (List.mem_range.mp hi) d]
  rw [hf]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_filter, List.mem_range] at hi
  simp only [Function.comp_apply]
  exact getD_map_lt hi.1 d

/-- The size of the bucket `k` of the keys `A.map f`. -/
theorem length_bkt_map {α : Type*} (A : List α) (d : α) (f : α → ℕ) (k : ℕ) :
    (bkt (A.map f) A.length k).length = (A.filter fun x => f x = k).length := by
  have := congrArg List.length (map_bkt A d f f k)
  simpa using this

/-- **Stable sorting by keys**: reading `A.map g` through the sorted indices of the keys
`A.map f` gives `A` grouped by `f`, stably. -/
theorem map_bucketIdx {α : Type*} (A : List α) (d : α) (f g : α → ℕ) (K : ℕ) :
    (bucketIdx (A.map f) K).map (fun i => (A.map g).getD i 0) =
      ((List.range K).flatMap fun k => A.filter fun x => f x = k).map g := by
  unfold bucketIdx
  rw [List.length_map, List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro k _
  exact map_bkt A d f g k

/-- The buckets `0, …, K` are the buckets `0, …, K - 1` and the bucket `K`. -/
theorem bucketIdx_succ (keys : List ℕ) (K : ℕ) :
    bucketIdx keys (K + 1) = bucketIdx keys K ++ bkt keys keys.length K := by
  rw [bucketIdx, bucketIdx, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- **Stable sorts of two streams with equal per-key subsequences are equal**: reading `A.map g`
through the stable sort of the keys `A.map f`, and `B.map g'` through the stable sort of the keys
`B.map f'`, give the same list when, for every key `k < K`, the values of the entries of `A` with
key `k` and those of the entries of `B` with key `k` are the same, in order. -/
theorem map_bucketIdx_congr {α β : Type*} (A : List α) (B : List β) (dA : α) (dB : β)
    (f g : α → ℕ) (f' g' : β → ℕ) (K : ℕ)
    (h : ∀ k < K, (A.filter fun x => f x = k).map g = (B.filter fun y => f' y = k).map g') :
    (bucketIdx (A.map f) K).map (fun i => (A.map g).getD i 0) =
      (bucketIdx (B.map f') K).map (fun i => (B.map g').getD i 0) := by
  rw [map_bucketIdx A dA f g K, map_bucketIdx B dB f' g' K, List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro k hk
  exact h k (List.mem_range.mp hk)

/-- The bucket starts of two key lists with per-key parts of equal sizes agree. -/
theorem offOf_congr {α β : Type*} (A : List α) (B : List β) (dA : α) (dB : β) (f : α → ℕ)
    (f' : β → ℕ) (K : ℕ)
    (h : ∀ k < K, (A.filter fun x => f x = k).length = (B.filter fun y => f' y = k).length)
    {k : ℕ} (hk : k ≤ K) : offOf (A.map f) k = offOf (B.map f') k := by
  unfold offOf
  congr 1
  apply List.map_congr_left
  intro k' hk'
  rw [List.length_map, List.length_map, length_bkt_map A dA f k', length_bkt_map B dB f' k']
  exact h k' (by simp at hk'; omega)

end STACS2027.RAM.P1
