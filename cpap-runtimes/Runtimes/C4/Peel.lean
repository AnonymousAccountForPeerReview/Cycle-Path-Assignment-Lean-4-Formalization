module

public import Runtimes.C4.Spec
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Outerplanar.RAM.R1Spec
import Mathlib.Tactic

/-!
# Four-cycle listing: the peeling (smallest-last order with a lazy bucket queue)

Generic part, for neighbour lists `nb` on the vertices `0, …, N - 1` that are duplicate-free,
symmetric, loop-free and below `N` (`NbOk N nb`; the id graph: `nbOk g`).

* **Invariant** `PInv N nb s`: the order is duplicate-free, below `N`,
  and is the set of removed vertices; the current degree of a remaining vertex is its number
  of remaining neighbours (`deg`); every remaining vertex has an entry in the bucket of its
  current degree; the pointer is at most every current degree; stack entries are below `N`
  and buckets `≥ N` are empty; and the *history* `hist`: the number of neighbours of the
  vertex `ord[i]` removed at step `i` that are removed after it is at most the number of
  neighbours of any vertex `w` still present before step `i` that are still present then
  (`ord[i]` had minimum degree in the graph it was removed from).
  `pinv_pinit`, `pinv_pstep`, `pinv_iterate`.
* **Potential** (`pot`, `acost`): `pot (pstep s) + acost s ≤ pot s` while `|ord| < N`
  (`pot_pstep`), where `acost s` is `1` for an advance or a stale pop and `1 + |nb v|` for
  the removal of `v`; `pot (pinit) ≤ 9 N + 4 Σ_{w<N} |nb w|` (`pot_pinit_le`). Hence after
  `pot (pinit) + 1` rounds the order is complete (`iterate_complete`), and the iteration is
  stationary afterwards (`iterate_eq_of_complete`).
* **The id graph.** `nbOk g`, `sum_length_nb` (`Σ_{w<N} |nb g w| = 2 |E|`),
  `pot_pinit_graph` (`≤ peelFuel g - 1`), `length_peelOrd`, `peelOrd_perm` (a permutation
  of `range N`), `iterate_eq_peelState` (a state reached from `pinit` with a complete order
  is `peelState g`), `peelPos_lt`, `peelPos_inj`, and the **minimum-degree property**
  `peel_minDeg`: if `peelPos v ≤ peelPos w`, the out-degree of `v` is at most the
  number of neighbours `u` of `w` with `peelPos v ≤ peelPos u`.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo Finset

/-! ### Hypotheses on the neighbour lists -/

/-- The neighbour lists are duplicate-free, below `N`, symmetric and loop-free. -/
structure NbOk (N : ℕ) (nb : ℕ → List ℕ) : Prop where
  nodup : ∀ v, (nb v).Nodup
  lt : ∀ v, ∀ w ∈ nb v, w < N
  symm : ∀ v w, w ∈ nb v → v ∈ nb w
  noloop : ∀ v, v ∉ nb v

section Generic

variable {N : ℕ} {nb : ℕ → List ℕ}

theorem NbOk.length_lt (h : NbOk N nb) {v : ℕ} (hv : v < N) : (nb v).length < N := by
  have h1 : (nb v).toFinset ⊆ (range N).erase v := by
    intro w hw
    rw [List.mem_toFinset] at hw
    simp only [mem_erase, mem_range]
    exact ⟨fun e => h.noloop v (e ▸ hw), h.lt v w hw⟩
  have h2 := card_le_card h1
  rw [List.toFinset_card_of_nodup (h.nodup v), card_erase_of_mem (by simpa using hv),
    card_range] at h2
  omega

/-! ### The basic operations -/

@[simp] theorem push_del (s : PState) (w d : ℕ) : (push s w d).del = s.del := rfl
@[simp] theorem push_cur (s : PState) (w d : ℕ) : (push s w d).cur = s.cur := rfl
@[simp] theorem push_p (s : PState) (w d : ℕ) : (push s w d).p = s.p := rfl
@[simp] theorem push_ord (s : PState) (w d : ℕ) : (push s w d).ord = s.ord := rfl

theorem push_stk (s : PState) (w d d' : ℕ) :
    (push s w d).stk d' = if d' = d then w :: s.stk d else s.stk d' := by
  simp only [push, Function.update_apply]

@[simp] theorem relax_del (s : PState) (w : ℕ) : (relax s w).del = s.del := by
  unfold relax; split <;> rfl
@[simp] theorem relax_p (s : PState) (w : ℕ) : (relax s w).p = s.p := by
  unfold relax; split <;> rfl
@[simp] theorem relax_ord (s : PState) (w : ℕ) : (relax s w).ord = s.ord := by
  unfold relax; split <;> rfl

theorem relax_cur (s : PState) (w u : ℕ) :
    (relax s w).cur u = if u = w ∧ s.del w = false then s.cur w - 1 else s.cur u := by
  unfold relax
  by_cases hd : s.del w = true
  · simp [hd]
  · have hd' : s.del w = false := by simpa using hd
    by_cases hu : u = w
    · subst hu; simp [hd']
    · simp [hd', hu]

theorem relax_stk (s : PState) (w d : ℕ) :
    (relax s w).stk d = if s.del w = false ∧ d = s.cur w - 1 then w :: s.stk d else s.stk d := by
  unfold relax
  by_cases hd : s.del w = true
  · simp [hd]
  · have hd' : s.del w = false := by simpa using hd
    by_cases hu : d = s.cur w - 1
    · subst hu; simp [hd', push]
    · simp [hd', hu, push]

/-! ### Relaxing a list of neighbours -/

theorem foldl_relax_del (l : List ℕ) (s : PState) : (l.foldl relax s).del = s.del := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, relax_del]

theorem foldl_relax_p (l : List ℕ) (s : PState) : (l.foldl relax s).p = s.p := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, relax_p]

theorem foldl_relax_ord (l : List ℕ) (s : PState) : (l.foldl relax s).ord = s.ord := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, relax_ord]

theorem foldl_relax_cur {l : List ℕ} (hl : l.Nodup) (s : PState) (w : ℕ) :
    (l.foldl relax s).cur w = if w ∈ l ∧ s.del w = false then s.cur w - 1 else s.cur w := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons, ih hl.2, relax_del, relax_cur]
    by_cases hw : w = a
    · subst hw; simp [hl.1]
    · simp [hw]

theorem foldl_relax_stk_sub (l : List ℕ) (s : PState) {d x : ℕ} (hx : x ∈ s.stk d) :
    x ∈ (l.foldl relax s).stk d := by
  induction l generalizing s with
  | nil => exact hx
  | cons a l ih =>
    rw [List.foldl_cons]
    refine ih _ ?_
    rw [relax_stk]
    split_ifs <;> simp [hx]

theorem foldl_relax_stk_mem {l : List ℕ} (hl : l.Nodup) (s : PState) {w : ℕ} (hw : w ∈ l)
    (hd : s.del w = false) : w ∈ (l.foldl relax s).stk (s.cur w - 1) := by
  induction l generalizing s with
  | nil => simp at hw
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons]
    by_cases hwa : w = a
    · subst hwa
      refine foldl_relax_stk_sub l _ ?_
      rw [relax_stk]
      simp [hd]
    · have hw' : w ∈ l := by simpa [hwa] using hw
      have h1 := ih hl.2 (relax s a) hw' (by rwa [relax_del])
      have hc : (relax s a).cur w = s.cur w := by rw [relax_cur]; simp [hwa]
      rwa [hc] at h1

theorem foldl_relax_stk_cases {l : List ℕ} (hl : l.Nodup) (s : PState) {d x : ℕ}
    (hx : x ∈ (l.foldl relax s).stk d) :
    x ∈ s.stk d ∨ (x ∈ l ∧ s.del x = false ∧ d = s.cur x - 1) := by
  induction l generalizing s with
  | nil => exact Or.inl hx
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons] at hx
    rcases ih hl.2 _ hx with h | ⟨hxl, hd, hc⟩
    · rw [relax_stk] at h
      split_ifs at h with hh
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨List.mem_cons_self .., hh.1, hh.2⟩
        · exact Or.inl h
      · exact Or.inl h
    · have hxa : x ≠ a := fun e => hl.1 (e ▸ hxl)
      rw [relax_del] at hd
      have hc' : (relax s a).cur x = s.cur x := by rw [relax_cur]; simp [hxa]
      rw [hc'] at hc
      exact Or.inr ⟨List.mem_cons_of_mem _ hxl, hd, hc⟩

/-! ### Sizes -/

/-- The total number of entries in the buckets `0, …, N - 1`. -/
def stkSize (N : ℕ) (s : PState) : ℕ := ∑ d ∈ range N, (s.stk d).length

theorem stkSize_push_le (s : PState) (w d : ℕ) : stkSize N (push s w d) ≤ stkSize N s + 1 := by
  unfold stkSize
  calc ∑ d' ∈ range N, ((push s w d).stk d').length
      ≤ ∑ d' ∈ range N, ((s.stk d').length + if d' = d then 1 else 0) := by
        refine sum_le_sum fun d' _ => ?_
        rw [push_stk]
        split_ifs with h
        · subst h; simp
        · simp
    _ ≤ ∑ d' ∈ range N, (s.stk d').length + 1 := by
        rw [sum_add_distrib, sum_ite_eq']
        split_ifs <;> omega

theorem stkSize_relax_le (s : PState) (w : ℕ) : stkSize N (relax s w) ≤ stkSize N s + 1 := by
  unfold relax
  split
  · omega
  · exact stkSize_push_le _ _ _

theorem stkSize_foldl_relax_le (l : List ℕ) (s : PState) :
    stkSize N (l.foldl relax s) ≤ stkSize N s + l.length := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, List.length_cons]
    have := ih (relax s a)
    have := stkSize_relax_le (N := N) s a
    omega

theorem stkSize_pop {s : PState} {v : ℕ} {rest : List ℕ} (he : s.stk s.p = v :: rest)
    (hp : s.p < N) :
    stkSize N { s with stk := Function.update s.stk s.p rest } + 1 = stkSize N s := by
  unfold stkSize
  have h1 : ∀ d ∈ range N, (Function.update s.stk s.p rest d).length +
      (if d = s.p then 1 else 0) = (s.stk d).length := by
    intro d _
    by_cases h : d = s.p
    · subst h; simp [he]
    · simp [h]
  dsimp only
  rw [← sum_congr rfl h1, sum_add_distrib, sum_ite_eq']
  simp [hp]

/-- The total degree of the remaining vertices below `N`. -/
def remSum (N : ℕ) (nb : ℕ → List ℕ) (s : PState) : ℕ :=
  ∑ w ∈ (range N).filter (fun w => s.del w = false), (nb w).length

/-- The potential of the peeling loop. -/
def pot (N : ℕ) (nb : ℕ → List ℕ) (s : PState) : ℕ :=
  3 * stkSize N s + 2 * (N - s.p) + 4 * (N - s.ord.length) + 4 * remSum N nb s

/-- The cost of one round, in units: `1` for an advance or a stale pop, `1 + |nb v|` for the
removal of `v`. -/
def acost (nb : ℕ → List ℕ) (s : PState) : ℕ :=
  match s.stk s.p with
  | [] => 1
  | v :: _ => if s.del v = false ∧ s.cur v = s.p then (nb v).length + 1 else 1

/-! ### Removal -/

theorem remove_del (s : PState) (v : ℕ) :
    (remove nb s v).del = Function.update s.del v true := by
  simp [remove, foldl_relax_del]

theorem remove_ord (s : PState) (v : ℕ) : (remove nb s v).ord = s.ord ++ [v] := by
  simp [remove, foldl_relax_ord]

theorem remove_p (s : PState) (v : ℕ) : (remove nb s v).p = s.p - 1 := by
  simp [remove, foldl_relax_p]

theorem remove_cur (hnd : (nb v).Nodup) (s : PState) (w : ℕ) :
    (remove nb s v).cur w =
      if w ∈ nb v ∧ w ≠ v ∧ s.del w = false then s.cur w - 1 else s.cur w := by
  simp only [remove]
  rw [foldl_relax_cur hnd]
  by_cases hw : w = v
  · subst hw; simp
  · simp [hw]

theorem remove_stk_sub (s : PState) (v : ℕ) {d x : ℕ} (hx : x ∈ s.stk d) :
    x ∈ (remove nb s v).stk d := by
  simp only [remove]
  exact foldl_relax_stk_sub _ _ hx

theorem remove_stk_mem (hnd : (nb v).Nodup) (s : PState) {w : ℕ} (hw : w ∈ nb v) (hwv : w ≠ v)
    (hd : s.del w = false) : w ∈ (remove nb s v).stk (s.cur w - 1) := by
  simp only [remove]
  exact foldl_relax_stk_mem hnd _ hw (by simp [hwv, hd])

theorem remove_stk_cases (hnd : (nb v).Nodup) (s : PState) {d x : ℕ}
    (hx : x ∈ (remove nb s v).stk d) :
    x ∈ s.stk d ∨ (x ∈ nb v ∧ x ≠ v ∧ s.del x = false ∧ d = s.cur x - 1) := by
  simp only [remove] at hx
  rcases foldl_relax_stk_cases hnd _ hx with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · have hxv : x ≠ v := by rintro rfl; simp at h2
    simp only [Function.update_apply, hxv, ↓reduceIte] at h2
    exact Or.inr ⟨h1, hxv, h2, h3⟩

theorem stkSize_remove_le (s : PState) (v : ℕ) :
    stkSize N (remove nb s v) ≤ stkSize N s + (nb v).length := by
  simp only [remove]
  exact stkSize_foldl_relax_le _ _

/-! ### Degrees -/

/-- The number of remaining neighbours of `w`. -/
def deg (nb : ℕ → List ℕ) (s : PState) (w : ℕ) : ℕ := ((nb w).filter fun u => !s.del u).length

theorem length_filter_update (L : List ℕ) (hL : L.Nodup) (f : ℕ → Bool) (v : ℕ)
    (hv : f v = false) :
    (L.filter fun u => !Function.update f v true u).length + (if v ∈ L then 1 else 0) =
      (L.filter fun u => !f u).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.nodup_cons] at hL
    have ih := ih hL.2
    by_cases hav : a = v
    · subst hav
      have h1 : (L.filter fun u => !Function.update f a true u) = L.filter fun u => !f u :=
        List.filter_congr fun x hx => by
          have hxa : x ≠ a := by rintro rfl; exact hL.1 hx
          rw [Function.update_of_ne hxa]
      simp [hL.1, hv, h1]
    · have hva : v ≠ a := Ne.symm hav
      have hu : Function.update f v true a = f a := Function.update_of_ne hav _ _
      have hm : v ∈ a :: L ↔ v ∈ L := by simp [hva]
      by_cases hvL : v ∈ L
      · have hm' : v ∈ a :: L := hm.mpr hvL
        simp only [hvL, hm', ↓reduceIte] at ih ⊢
        cases hfa : f a <;> simp [hu, hfa] <;> omega
      · have hm' : v ∉ a :: L := fun h => hvL (hm.mp h)
        simp only [hvL, hm', ↓reduceIte] at ih ⊢
        cases hfa : f a <;> simp [hu, hfa] <;> omega

/-! ### The invariant -/

/-- The invariant of the peeling loop. -/
structure PInv (N : ℕ) (nb : ℕ → List ℕ) (s : PState) : Prop where
  ord_nodup : s.ord.Nodup
  ord_lt : ∀ v ∈ s.ord, v < N
  del_iff : ∀ w, s.del w = true ↔ w ∈ s.ord
  cur_eq : ∀ w < N, s.del w = false → s.cur w = deg nb s w
  mem_stk : ∀ w < N, s.del w = false → w ∈ s.stk (s.cur w)
  p_le : ∀ w < N, s.del w = false → s.p ≤ s.cur w
  stk_lt : ∀ d, ∀ x ∈ s.stk d, x < N
  stk_nil : ∀ d, N ≤ d → s.stk d = []
  hist : ∀ i < s.ord.length, ∀ w < N, w ∉ s.ord.take i →
    ((nb (s.ord.getD i 0)).filter fun u => u ∉ s.ord.take (i + 1)).length ≤
      ((nb w).filter fun u => u ∉ s.ord.take i).length

theorem PInv.length_ord_le {s : PState} (hI : PInv N nb s) : s.ord.length ≤ N := by
  have h := (List.subperm_of_subset hI.ord_nodup (l₂ := List.range N)
    fun v hv => List.mem_range.mpr (hI.ord_lt v hv)).length_le
  simpa using h

/-- While the order is incomplete, some vertex below `N` remains. -/
theorem PInv.exists_rem {s : PState} (hI : PInv N nb s) (hlt : s.ord.length < N) :
    ∃ w < N, s.del w = false := by
  by_contra h
  simp only [not_exists, not_and, Bool.not_eq_false] at h
  have hsub : List.range N ⊆ s.ord := fun w hw => (hI.del_iff w).mp (h w (List.mem_range.mp hw))
  have := (List.subperm_of_subset List.nodup_range hsub).length_le
  simp at this
  omega

theorem PInv.del_eq_false_iff {s : PState} (hI : PInv N nb s) (w : ℕ) :
    s.del w = false ↔ w ∉ s.ord := by
  rw [← hI.del_iff]; simp

theorem deg_le (s : PState) (w : ℕ) : deg nb s w ≤ (nb w).length :=
  List.length_filter_le _ _

theorem PInv.cur_lt (hok : NbOk N nb) {s : PState} (hI : PInv N nb s) {w : ℕ} (hw : w < N)
    (hd : s.del w = false) : s.cur w < N := by
  rw [hI.cur_eq w hw hd]
  exact lt_of_le_of_lt (List.length_filter_le _ _) (hok.length_lt hw)

/-- While the order is incomplete, the pointer is below `N`. -/
theorem PInv.p_lt (hok : NbOk N nb) {s : PState} (hI : PInv N nb s) (hlt : s.ord.length < N) :
    s.p < N := by
  obtain ⟨w, hw, hd⟩ := hI.exists_rem hlt
  exact lt_of_le_of_lt (hI.p_le w hw hd) (hI.cur_lt hok hw hd)

/-- The removed vertices are the entries of the order: a filter by "not in the order" is a
filter by "not removed". -/
theorem PInv.filter_not_mem {s : PState} (hI : PInv N nb s) (L : List ℕ) :
    (L.filter fun u => u ∉ s.ord) = L.filter fun u => !s.del u := by
  refine List.filter_congr fun u _ => ?_
  have := hI.del_iff u
  cases h : s.del u <;> simp_all

/-! ### The initial state -/

theorem pinitPre_fields (nb : ℕ → List ℕ) (j : ℕ) :
    (pinitPre nb j).del = (fun _ => false) ∧ (pinitPre nb j).cur = (fun v => (nb v).length) ∧
      (pinitPre nb j).p = 0 ∧ (pinitPre nb j).ord = [] ∧
      ∀ d, (pinitPre nb j).stk d = ((List.range j).filter fun v => (nb v).length = d).reverse := by
  induction j with
  | zero => exact ⟨rfl, rfl, rfl, rfl, fun d => rfl⟩
  | succ j ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    refine ⟨by rw [pinitPre_succ]; exact h1, by rw [pinitPre_succ]; exact h2,
      by rw [pinitPre_succ]; exact h3, by rw [pinitPre_succ]; exact h4, fun d => ?_⟩
    rw [pinitPre_succ, push_stk, List.range_succ, List.filter_append]
    by_cases hd : d = (nb j).length
    · subst hd; simp [h5]
    · simp [hd, h5, Ne.symm hd]

theorem stkSize_pinitPre_le (j : ℕ) : stkSize N (pinitPre nb j) ≤ j := by
  induction j with
  | zero => simp [stkSize, pinitPre_zero]
  | succ j ih =>
    rw [pinitPre_succ]
    have := stkSize_push_le (N := N) (pinitPre nb j) j (nb j).length
    omega

theorem pinv_pinit (hok : NbOk N nb) : PInv N nb (pinit N nb) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pinitPre_fields nb N
  rw [pinit_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h4]
  · simp [h4]
  · simp [h1, h4]
  · intro w _ _
    simp [h1, h2, deg]
  · intro w hw _
    simp [h2, h5, hw]
  · simp [h3]
  · intro d x hx
    rw [h5] at hx
    simpa using (List.mem_filter.mp (List.mem_reverse.mp hx)).1
  · intro d hd
    rw [h5, List.reverse_eq_nil_iff, List.filter_eq_nil_iff]
    intro v hv
    have := hok.length_lt (List.mem_range.mp hv)
    simp only [decide_eq_true_eq]
    omega
  · simp [h4]

theorem pot_pinit_le (hok : NbOk N nb) :
    pot N nb (pinit N nb) ≤ 9 * N + 4 * ∑ w ∈ range N, (nb w).length := by
  have _ := hok
  obtain ⟨h1, -, h3, h4, -⟩ := pinitPre_fields nb N
  have hs := stkSize_pinitPre_le (N := N) (nb := nb) N
  have hf : ((range N).filter fun w => (pinitPre nb N).del w = false) = range N := by
    rw [h1]; exact Finset.filter_true_of_mem fun _ _ => rfl
  rw [pinit_eq]
  unfold pot remSum
  rw [hf, h3, h4, List.length_nil, Nat.sub_zero]
  omega

/-! ### One round preserves the invariant -/

theorem pinv_advance {s : PState} (hI : PInv N nb s) (he : s.stk s.p = []) :
    PInv N nb { s with p := s.p + 1 } := by
  refine ⟨hI.ord_nodup, hI.ord_lt, hI.del_iff, hI.cur_eq, hI.mem_stk, ?_, hI.stk_lt,
    hI.stk_nil, hI.hist⟩
  intro w hw hd
  have h1 := hI.p_le w hw hd
  have h2 := hI.mem_stk w hw hd
  have h3 : s.cur w ≠ s.p := by
    intro h; rw [h, he] at h2; simp at h2
  show s.p + 1 ≤ s.cur w
  omega

theorem pinv_stale {s : PState} (hI : PInv N nb s) {v : ℕ} {rest : List ℕ}
    (he : s.stk s.p = v :: rest) (hv : ¬ (s.del v = false ∧ s.cur v = s.p)) :
    PInv N nb { s with stk := Function.update s.stk s.p rest } := by
  refine ⟨hI.ord_nodup, hI.ord_lt, hI.del_iff, hI.cur_eq, ?_, hI.p_le, ?_, ?_, hI.hist⟩
  · intro w hw hd
    have h2 := hI.mem_stk w hw hd
    show w ∈ Function.update s.stk s.p rest (s.cur w)
    by_cases hc : s.cur w = s.p
    · rw [hc, Function.update_self]
      rw [hc, he] at h2
      rcases List.mem_cons.mp h2 with rfl | h
      · exact absurd ⟨hd, hc⟩ hv
      · exact h
    · rwa [Function.update_of_ne hc]
  · intro d x hx
    simp only [Function.update_apply] at hx
    split_ifs at hx with h
    · subst h; exact hI.stk_lt _ x (by rw [he]; exact List.mem_cons_of_mem _ hx)
    · exact hI.stk_lt d x hx
  · intro d hd
    simp only [Function.update_apply]
    split_ifs with h
    · subst h; have := hI.stk_nil _ hd; rw [he] at this; simp at this
    · exact hI.stk_nil d hd

theorem pinv_valid (hok : NbOk N nb) {s : PState} (hI : PInv N nb s) {v : ℕ} {rest : List ℕ}
    (he : s.stk s.p = v :: rest) (hd : s.del v = false) (hc : s.cur v = s.p) :
    PInv N nb (remove nb { s with stk := Function.update s.stk s.p rest } v) := by
  set s₁ : PState := { s with stk := Function.update s.stk s.p rest } with hs₁
  have hvN : v < N := hI.stk_lt _ v (by rw [he]; exact List.mem_cons_self ..)
  have hvo : v ∉ s.ord := (hI.del_eq_false_iff v).mp hd
  have hnd := hok.nodup v
  have hdel : (remove nb s₁ v).del = Function.update s.del v true := remove_del _ _
  have hord : (remove nb s₁ v).ord = s.ord ++ [v] := remove_ord _ _
  have hp : (remove nb s₁ v).p = s.p - 1 := remove_p _ _
  have hdel' : ∀ w, (remove nb s₁ v).del w = false ↔ w ≠ v ∧ s.del w = false := by
    intro w; rw [hdel]; by_cases h : w = v <;> simp [h]
  have hcur : ∀ w, w ≠ v → s.del w = false →
      (remove nb s₁ v).cur w = if w ∈ nb v then s.cur w - 1 else s.cur w := by
    intro w hw hdw
    rw [remove_cur hnd]
    by_cases h : w ∈ nb v <;> simp [h, hw, hdw, s₁]
  -- the new degree
  have hdeg : ∀ w, deg nb (remove nb s₁ v) w + (if w ∈ nb v then 1 else 0) = deg nb s w := by
    intro w
    unfold deg
    rw [hdel]
    have := length_filter_update (nb w) (hok.nodup w) s.del v hd
    have hiff : v ∈ nb w ↔ w ∈ nb v := ⟨hok.symm w v, hok.symm v w⟩
    simpa [hiff] using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hord]
    refine List.nodup_append.mpr ⟨hI.ord_nodup, List.nodup_singleton v, ?_⟩
    intro a ha b hb e
    rw [List.mem_singleton] at hb
    subst hb; subst e
    exact hvo ha
  · intro x hx
    rw [hord, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hI.ord_lt x hx
    · simp at hx; rw [hx]; exact hvN
  · intro w
    rw [hdel, hord]
    by_cases h : w = v
    · subst h; simp
    · simp [h, hI.del_iff w]
  · intro w hw hdw
    obtain ⟨hwv, hdw⟩ := (hdel' w).mp hdw
    have h1 := hdeg w
    have h2 := hI.cur_eq w hw hdw
    rw [hcur w hwv hdw]
    split_ifs at h1 ⊢ <;> omega
  · intro w hw hdw
    obtain ⟨hwv, hdw⟩ := (hdel' w).mp hdw
    rw [hcur w hwv hdw]
    split_ifs with hwn
    · exact remove_stk_mem hnd _ hwn hwv hdw
    · apply remove_stk_sub
      have h2 := hI.mem_stk w hw hdw
      show w ∈ Function.update s.stk s.p rest (s.cur w)
      by_cases hcw : s.cur w = s.p
      · rw [hcw, Function.update_self]
        rw [hcw, he] at h2
        rcases List.mem_cons.mp h2 with h | h
        · exact absurd h hwv
        · exact h
      · rwa [Function.update_of_ne hcw]
  · intro w hw hdw
    obtain ⟨hwv, hdw⟩ := (hdel' w).mp hdw
    rw [hp, hcur w hwv hdw]
    have := hI.p_le w hw hdw
    split_ifs <;> omega
  · intro d x hx
    rcases remove_stk_cases hnd _ hx with h | ⟨h1, -, -, -⟩
    · simp only [s₁, Function.update_apply] at h
      split_ifs at h with h'
      · subst h'; exact hI.stk_lt _ x (by rw [he]; exact List.mem_cons_of_mem _ h)
      · exact hI.stk_lt d x h
    · exact hok.lt v x h1
  · intro d hdN
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    rcases remove_stk_cases hnd _ hx with h | ⟨h1, -, h3, h4⟩
    · simp only [s₁, Function.update_apply] at h
      split_ifs at h with h'
      · subst h'; have := hI.stk_nil _ hdN; rw [he] at this; simp at this
      · rw [hI.stk_nil d hdN] at h; simp at h
    · have := hI.cur_lt hok (hok.lt v x h1) h3
      have h4' : d = s.cur x - 1 := h4
      omega
  · intro i hi w hw hwi
    rw [hord, List.length_append, List.length_singleton] at hi
    rw [hord] at hwi ⊢
    rcases Nat.lt_or_ge i s.ord.length with hi' | hi'
    · rw [List.take_append_of_le_length hi'.le] at hwi ⊢
      rw [List.take_append_of_le_length hi']
      have hg : (s.ord ++ [v]).getD i 0 = s.ord.getD i 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
      rw [hg]
      exact hI.hist i hi' w hw hwi
    · have hie : i = s.ord.length := by omega
      subst hie
      have ht0 : (s.ord ++ [v]).take s.ord.length = s.ord := by simp
      have hg : (s.ord ++ [v]).getD s.ord.length 0 = v := by simp [List.getD_eq_getElem?_getD]
      have ht : (s.ord ++ [v]).take (s.ord.length + 1) = s.ord ++ [v] := by simp
      rw [ht0] at hwi
      rw [ht0, hg, ht]
      have hl : ((nb v).filter fun u => u ∉ s.ord ++ [v]) = (nb v).filter fun u => u ∉ s.ord := by
        refine List.filter_congr fun u hu => ?_
        have : u ≠ v := fun e => hok.noloop v (e ▸ hu)
        simp [this]
      rw [hl, hI.filter_not_mem, hI.filter_not_mem]
      have hdw : s.del w = false := (hI.del_eq_false_iff w).mpr hwi
      have h1 := hI.cur_eq v hvN hd
      have h2 := hI.cur_eq w hw hdw
      have h3 := hI.p_le w hw hdw
      unfold deg at h1 h2
      omega

/-- One round preserves the invariant. -/
theorem pinv_pstep (hok : NbOk N nb) {s : PState} (hI : PInv N nb s) :
    PInv N nb (pstep N nb s) := by
  by_cases hlt : s.ord.length < N
  · rcases he : s.stk s.p with _ | ⟨v, rest⟩
    · rw [pstep_advance hlt he]; exact pinv_advance hI he
    · by_cases hv : s.del v = false ∧ s.cur v = s.p
      · rw [pstep_valid hlt he hv.1 hv.2]; exact pinv_valid hok hI he hv.1 hv.2
      · rw [pstep_stale hlt he hv]; exact pinv_stale hI he hv
  · rw [pstep_of_not_lt hlt]; exact hI

/-- Every state reached from `pinit` satisfies the invariant. -/
theorem pinv_iterate (hok : NbOk N nb) (k : ℕ) : PInv N nb ((pstep N nb)^[k] (pinit N nb)) := by
  induction k with
  | zero => exact pinv_pinit hok
  | succ k ih => rw [Function.iterate_succ_apply']; exact pinv_pstep hok ih

/-! ### The potential decreases -/

/-- **Potential**: while the order is incomplete, one round costs at most the
decrease of the potential. -/
theorem pot_pstep (hok : NbOk N nb) {s : PState} (hI : PInv N nb s) (hlt : s.ord.length < N) :
    pot N nb (pstep N nb s) + acost nb s ≤ pot N nb s := by
  have hpN := hI.p_lt hok hlt
  rcases he : s.stk s.p with _ | ⟨v, rest⟩
  · -- advance
    rw [pstep_advance hlt he]
    obtain ⟨w, hw, hd⟩ := hI.exists_rem hlt
    have h1 := hI.p_le w hw hd
    have h2 := hI.mem_stk w hw hd
    have h3 : s.cur w ≠ s.p := by intro h; rw [h, he] at h2; simp at h2
    have h4 := hI.cur_lt hok hw hd
    simp only [acost, he, pot, stkSize, remSum]
    omega
  · have hpop := stkSize_pop (N := N) he hpN
    by_cases hv : s.del v = false ∧ s.cur v = s.p
    · -- valid pop
      rw [pstep_valid hlt he hv.1 hv.2]
      have hvN : v < N := hI.stk_lt _ v (by rw [he]; exact List.mem_cons_self ..)
      set s₁ : PState := { s with stk := Function.update s.stk s.p rest } with hs₁
      have hS := stkSize_remove_le (N := N) (nb := nb) s₁ v
      have hrem : remSum N nb (remove nb s₁ v) + (nb v).length = remSum N nb s := by
        unfold remSum
        rw [remove_del]
        have hset : ((range N).filter fun w => Function.update s₁.del v true w = false) =
            ((range N).filter fun w => s.del w = false).erase v := by
          ext w
          by_cases h : w = v <;> simp [h, Function.update_apply, s₁]
        rw [hset]
        exact sum_erase_add _ _ (by simp [hvN, hv.1])
      have hord := remove_ord (nb := nb) s₁ v
      have hp := remove_p (nb := nb) s₁ v
      simp only [acost, he, hv, and_self, ↓reduceIte]
      unfold pot
      rw [hord, hp]
      simp only [s₁, List.length_append, List.length_singleton] at hS hpop hrem ⊢
      omega
    · -- stale pop
      rw [pstep_stale hlt he hv]
      simp only [acost, he, hv, ↓reduceIte, pot, remSum]
      omega

theorem pstep_iterate_of_not_lt {s : PState} (h : ¬ s.ord.length < N) (k : ℕ) :
    (pstep N nb)^[k] s = s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, pstep_of_not_lt h, ih]

theorem length_ord_pstep_ge (s : PState) : s.ord.length ≤ (pstep N nb s).ord.length := by
  by_cases hlt : s.ord.length < N
  · rcases he : s.stk s.p with _ | ⟨v, rest⟩
    · rw [pstep_advance hlt he]
    · by_cases hv : s.del v = false ∧ s.cur v = s.p
      · rw [pstep_valid hlt he hv.1 hv.2, remove_ord]; simp
      · rw [pstep_stale hlt he hv]
  · rw [pstep_of_not_lt hlt]

/-- Termination: from a state satisfying the invariant, more rounds than the potential
complete the order. -/
theorem iterate_complete (hok : NbOk N nb) :
    ∀ (k : ℕ) (s : PState), PInv N nb s → pot N nb s < k →
      ((pstep N nb)^[k] s).ord.length = N
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, s, hI, h => by
    by_cases hlt : s.ord.length < N
    · have h1 := pot_pstep hok hI hlt
      have h2 : 1 ≤ acost nb s := by
        unfold acost; split
        · exact le_refl _
        · split_ifs <;> omega
      rw [Function.iterate_succ_apply]
      exact iterate_complete hok k _ (pinv_pstep hok hI) (by omega)
    · rw [pstep_iterate_of_not_lt hlt]
      exact le_antisymm hI.length_ord_le (by omega)

/-- Stationarity: two iterates from `pinit` that both have a complete order are equal. -/
theorem iterate_eq_of_complete (hok : NbOk N nb) {k k' : ℕ}
    (hk : ((pstep N nb)^[k] (pinit N nb)).ord.length = N)
    (hk' : ((pstep N nb)^[k'] (pinit N nb)).ord.length = N) :
    (pstep N nb)^[k] (pinit N nb) = (pstep N nb)^[k'] (pinit N nb) := by
  have _ := hok
  rcases Nat.le_total k k' with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show k + j = j + k from Nat.add_comm _ _, Function.iterate_add_apply,
      pstep_iterate_of_not_lt (s := (pstep N nb)^[k] (pinit N nb)) (by omega) j]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show k' + j = j + k' from Nat.add_comm _ _, Function.iterate_add_apply,
      pstep_iterate_of_not_lt (s := (pstep N nb)^[k'] (pinit N nb)) (by omega) j]

end Generic

/-! ### The id graph -/

theorem nodup_nb (g : Graph) (v : ℕ) : (nb g v).Nodup := by
  unfold nb nbOf
  rw [List.nodup_flatMap]
  refine ⟨fun e _ => by split_ifs <;> simp, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ (idEdges_nodup g)
  intro a b ha hb hab
  have ha' := idEdges_lt ha
  have hb' := idEdges_lt hb
  simp only [Function.onFun]
  intro x hxa hxb
  apply hab
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  dsimp only at ha' hb' hxa hxb ⊢
  split_ifs at hxa hxb <;> simp at hxa hxb <;> simp only [Prod.mk.injEq] <;> omega

/-- The neighbour lists of the id graph satisfy the hypotheses of the peeling. -/
theorem nbOk (g : Graph) : NbOk (numV g) (nb g) where
  nodup := nodup_nb g
  lt _ _ h := RAM.R1.lt_of_mem_nbOf h
  symm := (ok_idEdges g).symm
  noloop := (ok_idEdges g).noloop

/-- The degrees of the id graph sum to twice its number of edges. -/
theorem sum_length_nb (g : Graph) :
    ∑ w ∈ range (numV g), (nb g w).length = 2 * (idEdges g).length := by
  rw [← RAM.R1.idEdges_ps g]
  have : ∀ n, ∑ w ∈ range n, (nb g w).length = RAM.R1.ps (idEdges g) n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, RAM.R1.ps_succ]
  exact this _

theorem pot_pinit_graph (g : Graph) :
    pot (numV g) (nb g) (pinit (numV g) (nb g)) < peelFuel g := by
  have h := pot_pinit_le (nbOk g)
  rw [sum_length_nb] at h
  unfold peelFuel
  omega

theorem pinv_peelState (g : Graph) : PInv (numV g) (nb g) (peelState g) :=
  pinv_iterate (nbOk g) _

theorem length_peelOrd (g : Graph) : (peelOrd g).length = numV g :=
  iterate_complete (nbOk g) _ _ (pinv_pinit (nbOk g)) (pot_pinit_graph g)

/-- A state reached from `pinit` with a complete order is the final state `peelState g`. -/
theorem iterate_eq_peelState (g : Graph) {k : ℕ}
    (hk : ((pstep (numV g) (nb g))^[k] (pinit (numV g) (nb g))).ord.length = numV g) :
    (pstep (numV g) (nb g))^[k] (pinit (numV g) (nb g)) = peelState g :=
  iterate_eq_of_complete (nbOk g) hk (length_peelOrd g)

theorem peelOrd_nodup (g : Graph) : (peelOrd g).Nodup := (pinv_peelState g).ord_nodup

theorem mem_peelOrd {g : Graph} {v : ℕ} : v ∈ peelOrd g ↔ v < numV g := by
  constructor
  · exact (pinv_peelState g).ord_lt v
  · intro hv
    have hp : (peelOrd g).Perm (List.range (numV g)) :=
      (List.subperm_of_subset (peelOrd_nodup g)
        fun v hv => List.mem_range.mpr ((pinv_peelState g).ord_lt v hv)).perm_of_length_le
        (by simp [length_peelOrd])
    exact hp.mem_iff.mpr (List.mem_range.mpr hv)

/-- The peeling order is a permutation of the vertices. -/
theorem peelOrd_perm (g : Graph) : (peelOrd g).Perm (List.range (numV g)) :=
  (List.perm_ext_iff_of_nodup (peelOrd_nodup g) List.nodup_range).mpr fun v => by
    rw [mem_peelOrd, List.mem_range]

theorem peelPos_lt {g : Graph} {v : ℕ} (hv : v < numV g) : peelPos g v < numV g := by
  have := List.idxOf_lt_length_iff.mpr (mem_peelOrd.mpr hv)
  rwa [length_peelOrd] at this

theorem getD_peelPos {g : Graph} {v : ℕ} (hv : v < numV g) :
    (peelOrd g).getD (peelPos g v) 0 = v := by
  have h := List.idxOf_lt_length_iff.mpr (mem_peelOrd.mpr hv)
  simp only [peelPos, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_idxOf h

theorem peelPos_inj {g : Graph} {v w : ℕ} (hv : v < numV g) (hw : w < numV g)
    (h : peelPos g v = peelPos g w) : v = w := by
  rw [← getD_peelPos hv, ← getD_peelPos hw, h]

/-- `peelPos` is injective on the vertices. -/
theorem peelPos_injOn (g : Graph) : Set.InjOn (peelPos g) (Set.Iio (numV g)) :=
  fun _ hv _ hw h => peelPos_inj hv hw h

theorem mem_take_peelOrd {g : Graph} {u : ℕ} (hu : u < numV g) (i : ℕ) :
    u ∈ (peelOrd g).take i ↔ peelPos g u < i := by
  have hm := mem_peelOrd.mpr hu
  have hlt := List.idxOf_lt_length_iff.mpr hm
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, hju⟩
    have := (peelOrd_nodup g).idxOf_getElem j (by omega)
    rw [hju] at this
    change (peelOrd g).idxOf u < i
    omega
  · intro h
    change (peelOrd g).idxOf u < i at h
    exact ⟨(peelOrd g).idxOf u, by omega, List.getElem_idxOf hlt⟩

/-- **Minimum-degree property**: if `v` is removed no later than `w`, the
out-degree of `v` is at most the number of neighbours `u` of `w` removed no earlier than `v`. -/
theorem peel_minDeg (g : Graph) {v w : ℕ} (hv : v < numV g) (hw : w < numV g)
    (h : peelPos g v ≤ peelPos g w) :
    (outL g (peelPos g) v).length ≤
      ((nb g w).filter fun u => peelPos g v ≤ peelPos g u).length := by
  have hI := pinv_peelState g
  have hi : peelPos g v < (peelState g).ord.length := by
    have := peelPos_lt hv; rwa [← length_peelOrd] at this
  have hwi : w ∉ (peelState g).ord.take (peelPos g v) := by
    change w ∉ (peelOrd g).take _
    rw [mem_take_peelOrd hw]; omega
  have hh := hI.hist _ hi w hw hwi
  change ((nb g ((peelOrd g).getD (peelPos g v) 0)).filter fun u =>
      u ∉ (peelOrd g).take (peelPos g v + 1)).length ≤
    ((nb g w).filter fun u => u ∉ (peelOrd g).take (peelPos g v)).length at hh
  rw [getD_peelPos hv] at hh
  have e1 : ((nb g v).filter fun u => u ∉ (peelOrd g).take (peelPos g v + 1)) =
      outL g (peelPos g) v := by
    unfold outL
    refine List.filter_congr fun u hu => ?_
    rw [decide_eq_decide, mem_take_peelOrd ((nbOk g).lt v u hu)]
    omega
  have e2 : ((nb g w).filter fun u => u ∉ (peelOrd g).take (peelPos g v)) =
      (nb g w).filter fun u => peelPos g v ≤ peelPos g u := by
    refine List.filter_congr fun u hu => ?_
    rw [decide_eq_decide, mem_take_peelOrd ((nbOk g).lt w u hu)]
    omega
  rwa [e1, e2] at hh

end STACS2027.Runtimes.C4
