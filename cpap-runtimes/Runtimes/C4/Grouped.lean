module

public import Runtimes.C4.Output
import Mathlib.Tactic

/-!
# Four-cycle listing: the reports grouped by the first key component

Phase ENUM does not keep a bucket table indexed by the key pairs
(`N²` cells). It writes the inserted 2-paths `ins g pos` as triples, sorts them stably by the
first component `x` of their key (`P1.csort`, keys `< N`), and walks the sorted list `sortX N l`
with one list head per second component `y`, valid within the current `x` (a time stamp per
`y`). It therefore reports `reports (sortX N l)`: the reports of the insertions in the sorted
order. This file proves that this is a permutation of the reports in insertion order:

* `sortX N l`: the entries grouped by `x`, stably (the order read off the sorted indices,
  `P1.map_bucketIdx`); `filter_sortX`: for every key `k` the entries with key `k` are in the
  same order as in `l`; `pairwise_sortX`: the first components are monotone;
* `reports_filter`: the reports with key `k` are the reports of the entries with key `k`;
  hence **`reports_perm_of_filter`**: two insertion lists with the same per-key subsequences
  have permuted reports;
* `enumOutS g`: the machine's output (`reports (sortX N (ins g (peelPos g)))`, as cycles);
  `enumOutS_perm`: it is a permutation of `cycles g 4`.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo

/-- The insertions grouped by the first component of their key, stably. -/
def sortX (N : ℕ) (l : Ins) : Ins :=
  (List.range N).flatMap fun x => l.filter fun e => e.1.1 = x

theorem sortX_succ (N : ℕ) (l : Ins) :
    sortX (N + 1) l = sortX N l ++ l.filter fun e => e.1.1 = N := by
  simp [sortX, List.range_succ, List.flatMap_append]

theorem filter_sortX_aux (l : Ins) (k : ℕ × ℕ) :
    ∀ N, (sortX N l).filter (fun e => e.1 = k) = if k.1 < N then l.filter (fun e => e.1 = k) else []
  | 0 => by simp [sortX]
  | N + 1 => by
    rw [sortX_succ, List.filter_append, filter_sortX_aux l k N, List.filter_filter]
    have h2 : (l.filter fun e => decide (e.1 = k) && decide (e.1.1 = N)) =
        if k.1 = N then l.filter (fun e => e.1 = k) else [] := by
      split_ifs with h
      · refine List.filter_congr fun e _ => ?_
        by_cases he : e.1 = k
        · simp [he, h]
        · simp [he]
      · rw [List.filter_eq_nil_iff]
        intro e _ hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact h (hc.1 ▸ hc.2)
    rw [h2]
    by_cases h1 : k.1 < N
    · simp [h1, show k.1 ≠ N by omega, show k.1 < N + 1 by omega]
    · by_cases h3 : k.1 = N
      · simp [h3]
      · simp [h1, h3, show ¬ k.1 < N + 1 by omega]

/-- Sorting by `x` keeps the order of the entries of every key. -/
theorem filter_sortX {N : ℕ} {l : Ins} (hl : ∀ e ∈ l, e.1.1 < N) (k : ℕ × ℕ) :
    (sortX N l).filter (fun e => e.1 = k) = l.filter (fun e => e.1 = k) := by
  rw [filter_sortX_aux]
  split_ifs with h
  · rfl
  · symm
    rw [List.filter_eq_nil_iff]
    intro e he hk
    have := hl e he
    simp only [decide_eq_true_eq] at hk
    rw [hk] at this
    exact h this

/-- The first components along `sortX N l` are monotone. -/
theorem pairwise_sortX (N : ℕ) (l : Ins) : (sortX N l).Pairwise fun a b => a.1.1 ≤ b.1.1 := by
  unfold sortX
  rw [List.pairwise_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True) fun _ _ => trivial)
    intro a b ha hb _
    simp only [List.mem_filter, decide_eq_true_eq] at ha hb
    omega
  · refine (List.pairwise_lt_range (n := N)).imp_of_mem ?_
    intro x y _ _ hxy a ha b hb
    simp only [List.mem_filter, decide_eq_true_eq] at ha hb
    omega

/-- Adjacent entries of `sortX N l` have monotone first components. -/
theorem sortX_mono {N : ℕ} {l : Ins} {t : ℕ} (ht : t + 1 < (sortX N l).length) :
    ((sortX N l)[t]'(by omega)).1.1 ≤ ((sortX N l)[t + 1]'ht).1.1 :=
  List.pairwise_iff_getElem.mp (pairwise_sortX N l) t (t + 1) (by omega) ht (by omega)

/-! ### Reports per key -/

/-- The reports with key `k` are the reports of the insertions with key `k`. -/
theorem reports_filter (l : Ins) (k : ℕ × ℕ) :
    (reports l).filter (fun r => r.1 = k) = reports (l.filter fun e => e.1 = k) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    obtain ⟨k₀, z⟩ := e
    rw [reports_snoc, List.filter_append, ih, List.filter_append]
    by_cases hk : k₀ = k
    · subst hk
      have hb : bucket l k₀ = bucket (l.filter fun e => e.1 = k₀) k₀ := by
        simp [bucket, List.filter_filter]
      rw [show (List.filter (fun e => decide (e.1 = k₀)) [(k₀, z)]) = [(k₀, z)] by simp,
        reports_snoc, ← hb]
      congr 1
      rw [List.filter_eq_self]
      intro r hr
      simp only [List.mem_map] at hr
      obtain ⟨_, _, rfl⟩ := hr
      simp
    · have e1 : (List.filter (fun e => decide (e.1 = k)) [(k₀, z)]) = [] := by simp [hk]
      have e2 : ((bucket l k₀).map fun z' => (k₀, z, z')).filter (fun r => decide (r.1 = k)) =
          [] := by
        rw [List.filter_eq_nil_iff]
        intro r hr
        simp only [List.mem_map] at hr
        obtain ⟨_, _, rfl⟩ := hr
        simp [hk]
      rw [e1, e2, List.append_nil, List.append_nil]

/-- **Per-key subsequences determine the reports up to order.** -/
theorem reports_perm_of_filter {l l' : Ins}
    (h : ∀ k, l.filter (fun e => e.1 = k) = l'.filter (fun e => e.1 = k)) :
    (reports l).Perm (reports l') := by
  rw [List.perm_iff_count]
  intro r
  have h1 : (reports l).count r = ((reports l).filter fun r' => r'.1 = r.1).count r := by
    rw [List.count_filter]; simp
  have h2 : (reports l').count r = ((reports l').filter fun r' => r'.1 = r.1).count r := by
    rw [List.count_filter]; simp
  rw [h1, h2, reports_filter, reports_filter, h r.1]

/-- Sorting by `x` permutes the entries. -/
theorem sortX_perm {N : ℕ} {l : Ins} (hl : ∀ e ∈ l, e.1.1 < N) : (sortX N l).Perm l := by
  rw [List.perm_iff_count]
  intro e
  have h1 : (sortX N l).count e = ((sortX N l).filter fun e' => e'.1 = e.1).count e := by
    rw [List.count_filter]; simp
  have h2 : l.count e = (l.filter fun e' => e'.1 = e.1).count e := by
    rw [List.count_filter]; simp
  rw [h1, h2, filter_sortX hl]

/-! ### The machine's output -/

/-- The insertions of the peeling order, sorted by `x` (the order of the report walk). -/
def insS (g : Graph) : Ins := sortX (numV g) (ins g (peelPos g))

/-- The cycles reported by the machine: the reports of `insS g`, in labels. -/
def enumOutS (g : Graph) : List Cycle := (reports (insS g)).map (phi g)

theorem lt_of_mem_ins' {g : Graph} {e : (ℕ × ℕ) × ℕ} (h : e ∈ ins g (peelPos g)) :
    e.1.1 < numV g := by
  have := lt_of_mem_ins h; omega

theorem insS_perm (g : Graph) : (insS g).Perm (ins g (peelPos g)) :=
  sortX_perm fun _ he => lt_of_mem_ins' he

theorem length_insS (g : Graph) : (insS g).length = numPaths g (peelPos g) :=
  (insS_perm g).length_eq

theorem lt_of_mem_insS {g : Graph} {e : (ℕ × ℕ) × ℕ} (h : e ∈ insS g) :
    e.1.1 < e.1.2 ∧ e.1.2 < numV g ∧ e.2 < numV g :=
  lt_of_mem_ins ((insS_perm g).subset h)

theorem reports_insS_perm (g : Graph) : (reports (insS g)).Perm (reports (ins g (peelPos g))) :=
  reports_perm_of_filter (filter_sortX fun _ he => lt_of_mem_ins' he)

/-- **The machine's output is a permutation of the four-cycles.** -/
theorem enumOutS_perm (g : Graph) : (enumOutS g).Perm (cycles g 4) :=
  ((reports_insS_perm g).map (phi g)).trans (enumOut_perm g)

theorem length_enumOutS (g : Graph) : (enumOutS g).length = (cycles g 4).length :=
  (enumOutS_perm g).length_eq

theorem length_reports_insS (g : Graph) : (reports (insS g)).length = (cycles g 4).length := by
  rw [← length_enumOutS, enumOutS, List.length_map]

theorem length_flatten_enumOutS (g : Graph) :
    (enumOutS g).flatten.length = 4 * (cycles g 4).length := by
  have h : (enumOutS g).flatten.length = 4 * (enumOutS g).length := by
    unfold enumOutS
    induction reports (insS g) with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, length_phi,
        List.length_cons] at ih ⊢
      omega
  rw [h, length_enumOutS]

end STACS2027.Runtimes.C4
