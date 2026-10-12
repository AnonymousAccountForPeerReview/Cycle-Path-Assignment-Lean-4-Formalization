module

public import Runtimes.ZeroCostSpec
public import Approximation.Theorems
import Mathlib.Tactic

/-!
# Lemma 15 on the RAM: the abstract side of the greedy algorithm

Algorithm 1 (`greedy`, Section 7) gives the cycles `C_0, …, C_{t-1}` of `cycles g k`, in order,
a path of minimum current load-sum, the first one among the options `selected C_i j`, `j < k`
(`chooseMin`). This file describes what the machine of `Runtimes/Greedy/Prog.lean` computes,
cycle by cycle, as functions of the paths `acc g k i` chosen for the first `i` cycles:

* the load table `ldF g k i e = l(e)` over the edge identifiers `e` of Corollary 5 (the index of
  the edge in `edgesOnCycles g k`); the machine reads the identifier of occurrence `ik + p` (the
  edge at position `p` of `C_i`) in `EID`, so the load of that edge is `ldF g k i (eidOf (ik + p))`
  (`ldF_eidOf`);
* the total `tot g k i = Σ_{p < k} l(e_p)` of the loads of the `k` edges of `C_i`, and the
  load-sum of option `j`, which omits the edges at the positions `j` and `prv k j`:
  `val g k i j = tot − l(e_j) − l(e_{prv j})` (`val_eq`; `O(1)` per option after the total);
* the scan `scanMin` for the first minimum, giving the chosen position `pos g k i`; the first
  minimizer is the option `chooseMin` picks (`chooseMin_eq_of_first`), so
  `selected C_i (pos i)` is Algorithm 1's path (`greedy_getD_pos`), and
  `zipWith selected (cycles g k) (pos 0, …, pos (t − 1)) = greedy …` (`zipWith_pos`);
* the update of the table along the positions `p < k` of `C_i` that lie on the chosen path
  (`uF`, `uF_succ`), ending in the table of `i + 1` cycles (`uF_final`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Greedy

open STACS2027 STACS2027.Runtimes.ZeroCost

/-! ### Algorithm 1, cycle by cycle -/

theorem length_greedyFrom (acc : List (List Edge)) (os : List (List (List Edge))) :
    (greedyFrom acc os).length = os.length := by
  induction os generalizing acc with
  | nil => rfl
  | cons o rest ih => simp only [greedyFrom, List.length_cons, ih]

theorem greedyFrom_getD (acc : List (List Edge)) (os : List (List (List Edge))) (i : ℕ)
    (hi : i < os.length) :
    (greedyFrom acc os).getD i [] =
      chooseMin (pathLoad (acc ++ (greedyFrom acc os).take i)) (os.getD i []) := by
  induction os generalizing acc i with
  | nil => simp at hi
  | cons o rest ih =>
    cases i with
    | zero => simp [greedyFrom]
    | succ i =>
      simp only [greedyFrom, List.getD_cons_succ, List.take_succ_cons]
      rw [ih _ i (by simpa using hi), List.append_assoc, List.singleton_append]

/-- The first option minimizing `f` is the one `chooseMin` picks. -/
theorem chooseMin_eq_of_first (f : List Edge → ℕ) : ∀ (l : List (List Edge)) (i : ℕ)
    (hi : i < l.length), (∀ j (hj : j < l.length), f l[i] ≤ f l[j]) →
      (∀ j (hj : j < i), f l[i] < f (l[j]'(by omega))) → chooseMin f l = l[i]
  | [], i, hi, _, _ => by simp at hi
  | [p], i, hi, _, _ => by
    obtain rfl : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
    rfl
  | p :: q :: rest, 0, _, hmin, _ => by
    have hm := chooseMin_mem f (opts := q :: rest) (by simp)
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hm
    have h := hmin (j + 1) (by simp only [List.length_cons] at hj ⊢; omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [hjeq] at h
    simp only [chooseMin, h, ↓reduceIte, List.getElem_cons_zero]
  | p :: q :: rest, i + 1, hi, hmin, hfirst => by
    have ih := chooseMin_eq_of_first f (q :: rest) i (by simpa using hi)
      (fun j hj => by
        have h := hmin (j + 1) (by simp only [List.length_cons] at hj ⊢; omega)
        simp only [List.getElem_cons_succ] at h
        exact h)
      (fun j hj => by
        have h := hfirst (j + 1) (by omega)
        simp only [List.getElem_cons_succ] at h
        exact h)
    have h0 := hfirst 0 (by omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h0
    have hi' : i < (q :: rest).length := by simpa using hi
    have hn : ¬ f p ≤ f ((q :: rest)[i]'hi') := by omega
    simp only [chooseMin, ih, List.getElem_cons_succ, hn, ↓reduceIte]

/-! ### The first minimum -/

/-- The scan for the first minimum of `v 0, …, v (n − 1)`: the best value and its position,
starting from the value `B` at position `0`; a value replaces the best one only if it is
smaller. -/
def scanMin (v : ℕ → ℕ) (B : ℕ) : ℕ → ℕ × ℕ
  | 0 => (B, 0)
  | j + 1 => if v j < (scanMin v B j).1 then (v j, j) else scanMin v B j

theorem scanMin_succ (v : ℕ → ℕ) (B j : ℕ) :
    scanMin v B (j + 1) = if v j < (scanMin v B j).1 then (v j, j) else scanMin v B j := rfl

theorem scanMin_inv (v : ℕ → ℕ) (B : ℕ) (n : ℕ) :
    (scanMin v B n).1 ≤ B ∧ (∀ j < n, (scanMin v B n).1 ≤ v j) ∧
      (∀ j < (scanMin v B n).2, (scanMin v B n).1 < v j) ∧
      (((scanMin v B n).2 = 0 ∧ (scanMin v B n).1 = B) ∨
        ((scanMin v B n).2 < n ∧ (scanMin v B n).1 = v (scanMin v B n).2)) := by
  induction n with
  | zero => simp [scanMin]
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [scanMin_succ]
    split_ifs with h
    · refine ⟨by omega, fun j hj => ?_, fun j hj => lt_of_lt_of_le h (h2 j hj),
        Or.inr ⟨by omega, rfl⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact le_trans (le_of_lt h) (h2 j hj)
      · exact le_refl _
    · refine ⟨h1, fun j hj => ?_, h3, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h2 j hj
        · omega
      · rcases h4 with h4 | h4
        · exact Or.inl h4
        · exact Or.inr ⟨by omega, h4.2⟩

/-- With all values below `B`, the scan ends at the first minimizer. -/
theorem scanMin_first (v : ℕ → ℕ) (B : ℕ) {n : ℕ} (hn : 0 < n) (hB : ∀ j < n, v j < B) :
    (scanMin v B n).2 < n ∧ (∀ j < n, v (scanMin v B n).2 ≤ v j) ∧
      ∀ j < (scanMin v B n).2, v (scanMin v B n).2 < v j := by
  obtain ⟨_, h2, h3, h4⟩ := scanMin_inv v B n
  rcases h4 with ⟨h40, h41⟩ | ⟨h40, h41⟩
  · have := h2 0 hn
    have := hB 0 hn
    omega
  · rw [← h41]; exact ⟨h40, h2, h3⟩

/-! ### The quantities of one cycle -/

section defs

variable (g : Graph) (k : ℕ)

/-- The option lists of the cycles. -/
def opts : List (List (List Edge)) := (cycles g k).map selectedOptions

/-- The paths chosen by Algorithm 1 for the first `i` cycles. -/
def acc (i : ℕ) : List (List Edge) := (greedy (opts g k)).take i

/-- The load table after `i` cycles, over the edge identifiers. -/
def ldF (i e : ℕ) : ℕ := load (acc g k i) ((edgesOnCycles g k).getD e (0, 0))

/-- The load of the edge at position `p` of `C_i` before `C_i` is processed. -/
def lp (i p : ℕ) : ℕ := load (acc g k i) (cycleEdgeAt g k i p)

/-- The sum of the loads of the edges at the positions `p' < p` of `C_i`. -/
def tsum (i p : ℕ) : ℕ := ∑ p' ∈ Finset.range p, lp g k i p'

/-- The total load of the `k` edges of `C_i`. -/
def tot (i : ℕ) : ℕ := tsum g k i k

/-- The load-sum of option `j` of `C_i` (the path omitting the vertex at position `j`). -/
def val (i j : ℕ) : ℕ := pathLoad (acc g k i) (selected (kCycle g k i) j)

/-- The option chosen for `C_i`: the first minimizer of the load-sums. -/
def pos (i : ℕ) : ℕ := (scanMin (val g k i) (tot g k i + 1) k).2

/-- The number of the positions `p' < p` of `C_i` on option `J` whose edge has identifier `e`. -/
def ucnt (i J p e : ℕ) : ℕ :=
  ∑ p' ∈ Finset.range p, if ¬ (J = p' ∨ J = next k p') ∧ eidOf g k (i * k + p') = e then 1 else 0

/-- The load table after the update of the positions `p' < p` of `C_i` on option `J`. -/
def uF (i J p e : ℕ) : ℕ := ldF g k i e + ucnt g k i J p e

end defs

/-- The position before `j` on a cycle of length `k`. -/
def prv (k j : ℕ) : ℕ := if j = 0 then k - 1 else j - 1

theorem prv_lt {k j : ℕ} (hj : j < k) : prv k j < k := by unfold prv; split <;> omega

variable {g : Graph} {k : ℕ}

theorem t_le_kt : (cycles g k).length ≤ k * (cycles g k).length := by
  by_cases h : cycles g k = []
  · simp [h]
  · exact Nat.le_mul_of_pos_left _ (by have := cycles_k_ge h; omega)

theorem k_ge_of_lt {i : ℕ} (hi : i < (cycles g k).length) : 3 ≤ k :=
  cycles_k_ge (g := g) (k := k) fun h => by rw [h] at hi; simp at hi

/-- Occurrence `ik + j` of Corollary 5's numbering is below `kt`. -/
theorem occIdx_lt {k i j t : ℕ} (hi : i < t) (hj : j < k) : i * k + j < k * t := by
  have : (i + 1) * k ≤ t * k := Nat.mul_le_mul_right k hi
  rw [Nat.add_mul, one_mul] at this; rw [Nat.mul_comm k]; omega

theorem length_greedy : (greedy (opts g k)).length = (cycles g k).length := by
  simp [greedy, length_greedyFrom, opts]

theorem opts_getD {i : ℕ} (hi : i < (cycles g k).length) :
    (opts g k).getD i [] = selectedOptions (kCycle g k i) := by
  rw [opts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  simp [kCycle, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem greedy_getD {i : ℕ} (hi : i < (cycles g k).length) :
    (greedy (opts g k)).getD i [] =
      chooseMin (pathLoad (acc g k i)) (selectedOptions (kCycle g k i)) := by
  rw [greedy, greedyFrom_getD [] _ i (by simpa [opts] using hi), opts_getD hi]
  rfl

theorem acc_succ {i : ℕ} (hi : i < (cycles g k).length) :
    acc g k (i + 1) = acc g k i ++ [(greedy (opts g k)).getD i []] := by
  have hl : i < (greedy (opts g k)).length := by rw [length_greedy]; exact hi
  rw [acc, acc, List.take_add_one, List.getElem?_eq_getElem hl, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hl]
  rfl

theorem acc_zero : acc g k 0 = [] := by simp [acc]

/-! ### The load-sum of an option -/

theorem tsum_succ (i p : ℕ) : tsum g k i (p + 1) = tsum g k i p + lp g k i p := by
  simp [tsum, Finset.sum_range_succ]

theorem tsum_zero (i : ℕ) : tsum g k i 0 = 0 := by simp [tsum]

/-- The positions not on option `j`: `j` and `prv k j`. -/
theorem off_option_iff {k j p : ℕ} (hk : 2 ≤ k) (hj : j < k) (hp : p < k) :
    (j = p ∨ j = next k p) ↔ (p = j ∨ p = prv k j) := by
  unfold next prv
  split_ifs <;> omega

/-- **The load-sum of option `j`**: the total minus the loads at the two positions not on it. -/
theorem val_eq {i j : ℕ} (hi : i < (cycles g k).length) (hj : j < k) :
    val g k i j = tot g k i - lp g k i j - lp g k i (prv k j) := by
  have hc := kCycle_isCycle g hi
  have hk : 3 ≤ k := hc.1
  set c := kCycle g k i
  set f := load (acc g k i)
  set ed : ℕ → Edge := fun p => (cycleEdges c).getD p (0, 0) with hed
  have hsel : (selected c j).toFinset = ((Finset.range k).filter
      (fun p => ¬ (j = p ∨ j = next k p))).image ed := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := exists_position hc (selected_mem_cycleEdges hx)
      exact ⟨p, ⟨hp, (mem_selected_iff_position hc hj hp).mp hx⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hn⟩, rfl⟩
      exact (mem_selected_iff_position hc hj hp).mpr hn
  have hinj : Set.InjOn ed ((Finset.range k).filter (fun p => ¬ (j = p ∨ j = next k p)) : Set ℕ) :=
    fun p hp p' hp' h => by
      have hp1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).1
      have hp2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp')).1
      exact edgeAt_inj hc (Finset.mem_range.mp hp1) (Finset.mem_range.mp hp2) h
  have hval : val g k i j = ∑ p ∈ (Finset.range k).filter (fun p => ¬ (j = p ∨ j = next k p)),
      f (ed p) := by
    rw [val, pathLoad, ← List.sum_toFinset _ (selected_nodup hc.2.2.1 j), hsel,
      Finset.sum_image hinj]
  have hoff : (Finset.range k).filter (fun p => ¬ ¬ (j = p ∨ j = next k p)) = {j, prv k j} := by
    ext p
    simp only [not_not, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hp, h⟩; exact (off_option_iff (by omega) hj hp).mp h
    · intro h
      have hp : p < k := by rcases h with rfl | rfl; exacts [hj, prv_lt hj]
      exact ⟨hp, (off_option_iff (by omega) hj hp).mpr h⟩
  have hne : j ≠ prv k j := by unfold prv; split <;> omega
  have htot : tot g k i = val g k i j + (lp g k i j + lp g k i (prv k j)) := by
    rw [hval, tot, tsum, ← Finset.sum_filter_add_sum_filter_not (Finset.range k)
      (fun p => ¬ (j = p ∨ j = next k p)), hoff, Finset.sum_pair hne]
    rfl
  omega

theorem val_le {i j : ℕ} (hi : i < (cycles g k).length) (hj : j < k) :
    val g k i j ≤ tot g k i := by
  rw [val_eq hi hj]; omega

/-! ### The chosen option -/

theorem pos_spec {i : ℕ} (hi : i < (cycles g k).length) :
    pos g k i < k ∧ (∀ j < k, val g k i (pos g k i) ≤ val g k i j) ∧
      ∀ j < pos g k i, val g k i (pos g k i) < val g k i j :=
  scanMin_first _ _ (by have := k_ge_of_lt hi; omega) fun j hj => by
    have := val_le hi hj; omega

theorem pos_lt {i : ℕ} (hi : i < (cycles g k).length) : pos g k i < k := (pos_spec hi).1

theorem length_kCycle {i : ℕ} (hi : i < (cycles g k).length) : (kCycle g k i).length = k :=
  (kCycle_isCycle g hi).2.1

/-- **The path chosen for `C_i`** is option `pos g k i`. -/
theorem greedy_getD_pos {i : ℕ} (hi : i < (cycles g k).length) :
    (greedy (opts g k)).getD i [] = selected (kCycle g k i) (pos g k i) := by
  obtain ⟨hlt, hmin, hfirst⟩ := pos_spec hi
  have hlen := length_kCycle hi
  rw [greedy_getD hi, selectedOptions]
  rw [chooseMin_eq_of_first _ _ (pos g k i) (by simpa [hlen] using hlt)
    (fun j hj => by
      simp only [List.getElem_map, List.getElem_range]
      exact hmin j (by simpa [hlen] using hj))
    (fun j hj => by
      simp only [List.getElem_map, List.getElem_range]
      exact hfirst j hj)]
  simp

/-- **The output of the machine is Algorithm 1**: the chosen options, as paths. -/
theorem zipWith_pos :
    List.zipWith selected (cycles g k) ((List.range (cycles g k).length).map (pos g k)) =
      greedy (opts g k) := by
  apply List.ext_getElem
  · simp [length_greedy]
  · intro i h1 h2
    have hi : i < (cycles g k).length := by simpa using h1
    rw [List.getElem_zipWith, List.getElem_map, List.getElem_range,
      List.getElem_eq_getD [], List.getElem_eq_getD [], greedy_getD_pos hi]
    rfl

/-! ### The load table -/

theorem eoc_getD_eidOf {q : ℕ} (hq : q < k * (cycles g k).length) :
    (edgesOnCycles g k).getD (eidOf g k q) (0, 0) = (occs g k).getD q (0, 0) := by
  have hm := occs_getD_mem_eoc hq
  have hl := List.idxOf_lt_length_of_mem hm
  unfold eidOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    List.getElem_idxOf hl]

/-- The machine reads the load of the edge at position `p` of `C_i` at its identifier. -/
theorem ldF_eidOf (i' : ℕ) {i p : ℕ} (hi : i < (cycles g k).length) (hp : p < k) :
    ldF g k i' (eidOf g k (i * k + p)) = load (acc g k i') (cycleEdgeAt g k i p) := by
  rw [ldF, eoc_getD_eidOf (occIdx_lt hi hp), occs_getD_cycleEdgeAt hi hp]

theorem eidOf_eq_iff_edge {i p e : ℕ} (hi : i < (cycles g k).length) (hp : p < k)
    (he : e < (edgesOnCycles g k).length) :
    eidOf g k (i * k + p) = e ↔ cycleEdgeAt g k i p = (edgesOnCycles g k).getD e (0, 0) := by
  have hq := occIdx_lt hi hp
  constructor
  · rintro rfl
    rw [eoc_getD_eidOf hq, occs_getD_cycleEdgeAt hi hp]
  · intro h
    rw [eidOf, occs_getD_cycleEdgeAt hi hp, h, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem he, Option.getD_some]
    exact (edgesOnCycles_nodup g k).idxOf_getElem e he

theorem uF_zero (i J : ℕ) : uF g k i J 0 = ldF g k i := by
  funext e; simp [uF, ucnt]

theorem uF_succ_apply (i J p e : ℕ) : uF g k i J (p + 1) e = uF g k i J p e +
    if ¬ (J = p ∨ J = next k p) ∧ eidOf g k (i * k + p) = e then 1 else 0 := by
  simp only [uF, ucnt, Finset.sum_range_succ]; omega

theorem uF_succ (i J p : ℕ) : uF g k i J (p + 1) =
    if ¬ (J = p ∨ J = next k p) then Function.update (uF g k i J p) (eidOf g k (i * k + p))
      (uF g k i J p (eidOf g k (i * k + p)) + 1) else uF g k i J p := by
  funext e
  rw [uF_succ_apply]
  by_cases h : ¬ (J = p ∨ J = next k p)
  · by_cases he : eidOf g k (i * k + p) = e
    · subst he; simp only [h, not_false_eq_true, and_self, ↓reduceIte, Function.update_self]
    · simp only [h, he, not_false_eq_true, and_false, ↓reduceIte, Nat.add_zero,
        Function.update_of_ne (Ne.symm he)]
  · simp only [h, false_and, ↓reduceIte, Nat.add_zero]

theorem ldF_succ {i e : ℕ} (hi : i < (cycles g k).length) :
    ldF g k (i + 1) e = ldF g k i e +
      (selected (kCycle g k i) (pos g k i)).count ((edgesOnCycles g k).getD e (0, 0)) := by
  rw [ldF, ldF, acc_succ hi, load_append, greedy_getD_pos hi]
  simp [load]

/-- **The update ends in the table of `i + 1` cycles.** -/
theorem uF_final {i e : ℕ} (hi : i < (cycles g k).length) (he : e < (edgesOnCycles g k).length) :
    uF g k i (pos g k i) k e = ldF g k (i + 1) e := by
  have hc := kCycle_isCycle g hi
  set J := pos g k i
  have hJ : J < k := pos_lt hi
  set x := (edgesOnCycles g k).getD e (0, 0)
  set P := selected (kCycle g k i) J
  rw [ldF_succ hi, uF]
  congr 1
  have hcongr : ucnt g k i J k e = ∑ p ∈ Finset.range k,
      if ¬ (J = p ∨ J = next k p) ∧ cycleEdgeAt g k i p = x then 1 else 0 :=
    Finset.sum_congr rfl fun p hp => by
      simp only [eidOf_eq_iff_edge hi (Finset.mem_range.mp hp) he]
      rfl
  rw [hcongr]
  by_cases hx : x ∈ P
  · obtain ⟨p0, hp0, hpx⟩ := exists_position hc (selected_mem_cycleEdges hx)
    have hcnd : ¬ (J = p0 ∨ J = next k p0) := (mem_selected_iff_position hc hJ hp0).mp (hpx ▸ hx)
    rw [List.count_eq_one_of_mem (selected_nodup hc.2.2.1 J) hx,
      Finset.sum_eq_single_of_mem p0 (Finset.mem_range.mpr hp0)]
    · simp only [cycleEdgeAt, hpx, hcnd, not_false_eq_true, and_self, ↓reduceIte]
    · intro p hp hne
      have hp' := Finset.mem_range.mp hp
      have hn : ¬ (¬ (J = p ∨ J = next k p) ∧ cycleEdgeAt g k i p = x) := fun ⟨_, h⟩ =>
        hne (edgeAt_inj hc hp' hp0 (h.trans hpx.symm))
      simp only [hn, ↓reduceIte]
  · rw [List.count_eq_zero_of_not_mem hx]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hn : ¬ (¬ (J = p ∨ J = next k p) ∧ cycleEdgeAt g k i p = x) := fun ⟨h1, h2⟩ =>
      hx (h2 ▸ (mem_selected_iff_position hc hJ (Finset.mem_range.mp hp)).mpr h1)
    simp only [hn, ↓reduceIte]

end STACS2027.Runtimes.Greedy
