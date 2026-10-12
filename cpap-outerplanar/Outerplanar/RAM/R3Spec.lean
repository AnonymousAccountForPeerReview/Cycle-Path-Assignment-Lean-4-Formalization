module

public import Outerplanar.RAM.R2
import Mathlib.Tactic

/-!
# Phase R3 (blocks), abstract side

The blocks `blocksOf g` are the id edges bucketed by the key `key g e` (the head of the lower
end of `e`), in the order of the edges. The machine computes them by a stable counting sort;
this file supplies the abstract facts:

* the buckets of the first `j` edges `bk g j h` (`bk_succ`, `length_bk_succ`, `length_bk_le`):
  `blocksOf g = (range N).map (bk g |E|)` (`blocksOf_eq`);
* the bucket starts `bs g h` (`bs_succ`, `bs_mono`, `bs_total`: `bs g N = |E|`, since every key
  is a vertex, `key_lt`), `blockStarts g = (range (N + 1)).map (bs g)` (`blockStarts_eq`);
* the concatenation of the blocks (`flatten_fst`, `flatten_snd`, `length_flatten`) and its
  storage by parts (`arr_flatMap_parts`).
-/

@[expose] public section

namespace STACS2027.RAM.R3

open STACS2027.Algo

/-! ### Keys and buckets -/

/-- The bucket of an edge: the head of its lower end. -/
def key (g : Graph) (e : Edge) : ℕ := headsOf g (lowerOf (dfsOf g) e)

/-- The edges among the first `j` id edges whose key is `h`, in order. -/
def bk (g : Graph) (j h : ℕ) : List Edge := ((idEdges g).take j).filter fun e => key g e = h

/-- The start of the bucket `h` in the concatenation of the buckets. -/
def bs (g : Graph) (h : ℕ) : ℕ :=
  ((List.range h).map fun h' => (bk g (idEdges g).length h').length).sum

theorem bk_zero (g : Graph) : bk g 0 = fun _ => [] := by
  funext h; simp [bk]

theorem bk_succ (g : Graph) {j : ℕ} (hj : j < (idEdges g).length) (h : ℕ) :
    bk g (j + 1) h = bk g j h ++ if key g (idEdges g)[j] = h then [(idEdges g)[j]] else [] := by
  unfold bk
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.filter_append]
  by_cases hk : key g (idEdges g)[j] = h <;> simp [hk]

/-- The buckets after one more edge `e`, of key `k`: `e` appended to the bucket `k`. -/
theorem bk_succ_eq (g : Graph) {j : ℕ} (hj : j < (idEdges g).length) :
    bk g (j + 1) = Function.update (bk g j) (key g (idEdges g)[j])
      (bk g j (key g (idEdges g)[j]) ++ [(idEdges g)[j]]) := by
  funext h
  rw [bk_succ g hj]
  by_cases hk : h = key g (idEdges g)[j]
  · subst hk; simp
  · rw [Function.update_of_ne hk]; simp [Ne.symm hk]

theorem length_bk_succ (g : Graph) {j : ℕ} (hj : j < (idEdges g).length) (h : ℕ) :
    (bk g (j + 1) h).length = (bk g j h).length + if key g (idEdges g)[j] = h then 1 else 0 := by
  rw [bk_succ g hj]; split <;> simp

theorem length_bk_le (g : Graph) (j h : ℕ) : (bk g j h).length ≤ (bk g (idEdges g).length h).length := by
  unfold bk
  rw [List.take_length]
  exact (List.take_sublist j _).filter _ |>.length_le

theorem bs_succ (g : Graph) (h : ℕ) : bs g (h + 1) = bs g h + (bk g (idEdges g).length h).length := by
  simp [bs, List.range_succ]

theorem bs_mono (g : Graph) {h h' : ℕ} (hh : h ≤ h') : bs g h ≤ bs g h' := by
  induction h', hh using Nat.le_induction with
  | base => exact le_rfl
  | succ h' _ ih => rw [bs_succ]; omega

/-- A bucket ends before the next starts. -/
theorem bs_add_le (g : Graph) {h h' : ℕ} (hh : h < h') :
    bs g h + (bk g (idEdges g).length h).length ≤ bs g h' := by
  rw [← bs_succ]; exact bs_mono g hh

/-! ### Every key is a vertex -/

theorem foldl_head_lt {N : ℕ} (s : DFS.State) (low : ℕ → ℕ) :
    ∀ (l : List ℕ) (hf : ℕ → ℕ), (∀ v ∈ l, v < N) → (∀ x, hf x < N) → ∀ x,
      (l.foldl (fun hf v => Function.update hf v
        (if s.par v = v then v else if s.pre (s.par v) ≤ low v then v else hf (s.par v))) hf) x < N
  | [], _, _, hhf, x => hhf x
  | v :: l, hf, hl, hhf, x => by
    rw [List.foldl_cons]
    refine foldl_head_lt s low l _ (fun w hw => hl w (List.mem_cons_of_mem _ hw)) (fun y => ?_) x
    have hv := hl v (by simp)
    by_cases hy : y = v
    · subst hy
      simp only [Function.update_self]
      split_ifs
      · exact hv
      · exact hv
      · exact hhf _
    · rw [Function.update_of_ne hy]; exact hhf y

/-- The heads are vertices (when there is a vertex). -/
theorem headsOf_lt {g : Graph} (hN : 0 < numV g) (x : ℕ) : headsOf g x < numV g :=
  foldl_head_lt _ _ _ _ (fun _ hv => R2.mem_ord_iff.mp hv) (fun _ => hN) x

theorem key_lt {g : Graph} {e : Edge} (he : e ∈ idEdges g) : key g e < numV g :=
  headsOf_lt (by have := idEdges_lt he; omega) _

theorem key_get_lt {g : Graph} {j : ℕ} (hj : j < (idEdges g).length) :
    key g (idEdges g)[j] < numV g := key_lt (List.getElem_mem hj)

/-! ### The total size of the buckets -/

theorem sum_length_filter {α : Type*} (f : α → ℕ) (N : ℕ) :
    ∀ (E : List α), (∀ e ∈ E, f e < N) →
      ((List.range N).map fun h => (E.filter fun e => f e = h).length).sum = E.length
  | [], _ => by simp
  | e :: E, hE => by
    have ih := sum_length_filter f N E (fun e' he' => hE e' (by simp [he']))
    have hsplit : ∀ x, ((e :: E).filter fun e' => f e' = x).length =
        (if f e = x then 1 else 0) + (E.filter fun e' => f e' = x).length := by
      intro x
      by_cases hx : f e = x
      · simp [hx]; omega
      · simp [hx]
    simp only [hsplit, List.sum_map_add, R1.sum_indicator, ih, hE e (by simp), ↓reduceIte,
      List.length_cons]
    omega

/-- The buckets hold all edges. -/
theorem bs_total (g : Graph) : bs g (numV g) = (idEdges g).length := by
  unfold bs bk
  rw [List.take_length]
  exact sum_length_filter (key g) (numV g) _ fun e he => key_lt he

/-- Every bucket lies within the edges. -/
theorem bs_add_le_total (g : Graph) {h : ℕ} (hh : h < numV g) :
    bs g h + (bk g (idEdges g).length h).length ≤ (idEdges g).length := by
  rw [← bs_succ, ← bs_total g]; exact bs_mono g hh

/-! ### The blocks -/

theorem blocksOf_eq (g : Graph) : blocksOf g = (List.range (numV g)).map (bk g (idEdges g).length) := by
  unfold blocksOf bk
  rw [List.take_length]
  rfl

theorem blockStarts_eq (g : Graph) : blockStarts g = (List.range (numV g + 1)).map (bs g) := by
  unfold blockStarts
  apply List.map_congr_left
  intro h hh
  have hh' : h ≤ numV g := by simp at hh; omega
  rw [blocksOf_eq, ← List.map_take, List.take_range, min_eq_left hh', List.map_map]
  rfl

theorem flatten_blocksOf (g : Graph) :
    (blocksOf g).flatten = (List.range (numV g)).flatMap (bk g (idEdges g).length) := by
  rw [blocksOf_eq, List.flatMap_def]

theorem flatten_fst (g : Graph) : (blocksOf g).flatten.map Prod.fst =
    (List.range (numV g)).flatMap fun h => (bk g (idEdges g).length h).map Prod.fst := by
  rw [flatten_blocksOf, List.map_flatMap]

theorem flatten_snd (g : Graph) : (blocksOf g).flatten.map Prod.snd =
    (List.range (numV g)).flatMap fun h => (bk g (idEdges g).length h).map Prod.snd := by
  rw [flatten_blocksOf, List.map_flatMap]

theorem length_flatten (g : Graph) : (blocksOf g).flatten.length = (idEdges g).length := by
  rw [flatten_blocksOf, List.length_flatMap]
  exact bs_total g

/-- A concatenation `(range K).flatMap f` stored by parts at the running offsets. -/
theorem arr_flatMap_parts {m : ℕ → ℕ} {b : ℕ} (f : ℕ → List ℕ) :
    ∀ K, (∀ k, k < K → Arr m (b + ((List.range k).map fun j => (f j).length).sum) (f k)) →
      Arr m b ((List.range K).flatMap f)
  | 0, _ => by simp
  | K + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, arr_append,
      List.length_flatMap]
    exact ⟨arr_flatMap_parts f K fun k hk => h k (by omega), h K (by omega)⟩

end STACS2027.RAM.R3
