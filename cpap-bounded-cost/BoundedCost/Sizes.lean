module

public import BoundedCost.ZeroCost

/-!
# Sizes of the encodings

Every clause has two literals. `Γ₁` has exactly `k(k−3)t/2` clauses on the `kt` path
variables, `𝒰` has at most `kt(t−1)/2` candidate overlaps, and the zero-cost formula
has at most `|Γ₁| + 3kt` clauses on fewer than `2kt` variables.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-! ## Two literals per clause, variables below `kt` -/

theorem pathConstraints_two_literals (g : Graph) (k : Nat) :
    ∀ cl ∈ pathConstraints g k, cl.length = 2 ∧ ∀ l ∈ cl, l.var < k * (cycles g k).length := by
  intro cl hcl
  obtain ⟨i, a, b, hi, hab, hb, _, rfl⟩ := (mem_pathConstraints g k cl).mp hcl
  refine ⟨rfl, ?_⟩
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact pathVariable_lt hi (by omega)
  · exact pathVariable_lt hi hb

theorem overlapClause_two_literals (g : Graph) (k : Nat) {u : Nat × Nat × Edge}
    (hu : u ∈ candidateOverlaps g k) :
    (overlapClause g k u).length = 2 ∧ ∀ l ∈ overlapClause g k u, l.var < k * (cycles g k).length := by
  obtain ⟨i, i', e, hlt, hi', he, he', rfl⟩ := (mem_candidateOverlaps g k u).mp hu
  have hi : i < (cycles g k).length := by omega
  refine ⟨rfl, ?_⟩
  intro l hl
  simp only [overlapClause, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact edgeVariable_lt g hi he
  · exact edgeVariable_lt g hi' he'

theorem almostFormula_two_cnf (g : Graph) (k Ψ : Nat) :
    ∀ cl ∈ almostFormula g k Ψ, cl.length = 2 ∧ ∀ l ∈ cl, l.var < k * (cycles g k).length := by
  intro cl hcl
  rcases (mem_almostFormula g k Ψ cl).mp hcl with hcl | ⟨u, hu, rfl⟩
  · exact pathConstraints_two_literals g k cl hcl
  · exact overlapClause_two_literals g k hu

/-! ## Counting the path constraints -/

theorem countP_gt_range (n a : Nat) : (List.range n).countP (fun b => decide (a < b)) = n - (a + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add]
    by_cases h : a < n
    · simp [h]; omega
    · simp [h]; omega

theorem countP_point (n x : Nat) : (List.range n).countP (fun b => decide (b = x)) = if x < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add]
    by_cases h : x < n
    · have : x ≠ n := by omega
      have : n ≠ x := by omega
      simp [*]
      omega
    · by_cases h' : x = n
      · subst h'; simp
      · have : ¬ x < n + 1 := by omega
        have : n ≠ x := fun e => h' e.symm
        simp [*]

theorem countP_and_or {α : Type} (l : List α) (P Q : α → Bool) :
    l.countP (fun b => P b && Q b) + l.countP (fun b => P b && !Q b) = l.countP P := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons]
    cases P x <;> cases Q x <;> simp <;> omega

/-- The number of vertex-disjoint pairs `(a, b)`, `a < b`, of edges of a simple `k`-cycle, with
`a` fixed, plus the number of its non-disjoint pairs, is the number of `b > a`. -/
theorem disjoint_pairs_count {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) {a : Nat} (ha : a < k) :
    (List.range k).countP (fun b => decide (a < b) && disjointEdges ((cycleEdges c).getD a (0, 0)) ((cycleEdges c).getD b (0, 0))) +
      ((if a + 1 < k then 1 else 0) + (if a = 0 then 1 else 0)) = k - (a + 1) := by
  have hk := hc.1
  -- rewrite disjointness by positions
  have hcongr : (List.range k).countP (fun b => decide (a < b) &&
      disjointEdges ((cycleEdges c).getD a (0, 0)) ((cycleEdges c).getD b (0, 0))) =
      (List.range k).countP (fun b => decide (a < b) && !(decide (b = a + 1) || decide (a = 0 && b = k - 1))) := by
    apply List.countP_congr
    intro b hb
    have hbk := List.mem_range.mp hb
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    constructor
    · rintro ⟨hab, hd⟩
      rw [disjointEdges_edgeAt hc ha hbk] at hd
      have na := next_spec ha
      have nb := next_spec hbk
      refine ⟨hab, ?_, ?_⟩
      · intro h; apply hd; omega
      · simp only [not_and]
        intro h0 hb'; apply hd; omega
    · rintro ⟨hab, h1, h2⟩
      refine ⟨hab, ?_⟩
      rw [disjointEdges_edgeAt hc ha hbk]
      have na := next_spec ha
      have nb := next_spec hbk
      simp only [not_and] at h2
      omega
  rw [hcongr]
  have hsplit := countP_and_or (List.range k) (fun b => decide (a < b))
    (fun b => decide (b = a + 1) || decide (a = 0 && b = k - 1))
  rw [countP_gt_range] at hsplit
  -- the non-disjoint pairs: `b = a + 1`, and `b = k - 1` when `a = 0`
  have hnd : (List.range k).countP (fun b => decide (a < b) && (decide (b = a + 1) || decide (a = 0 && b = k - 1))) =
      (if a + 1 < k then 1 else 0) + (if a = 0 then 1 else 0) := by
    have h := countP_and_or (List.range k)
      (fun b => decide (a < b) && (decide (b = a + 1) || decide (a = 0 && b = k - 1)))
      (fun b => decide (b = a + 1))
    have h1 : (List.range k).countP (fun b => (decide (a < b) && (decide (b = a + 1) || decide (a = 0 && b = k - 1))) &&
        decide (b = a + 1)) = (List.range k).countP (fun b => decide (b = a + 1)) := by
      apply List.countP_congr
      intro b _
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      omega
    have h2 : (List.range k).countP (fun b => (decide (a < b) && (decide (b = a + 1) || decide (a = 0 && b = k - 1))) &&
        !decide (b = a + 1)) = (List.range k).countP (fun b => decide (a = 0) && decide (b = k - 1)) := by
      apply List.countP_congr
      intro b hb
      have hbk := List.mem_range.mp hb
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not]
      omega
    rw [h1, h2, countP_point] at h
    have h3 : (List.range k).countP (fun b => decide (a = 0) && decide (b = k - 1)) = if a = 0 then 1 else 0 := by
      by_cases h0 : a = 0
      · subst h0
        simp only [decide_true, Bool.true_and, ↓reduceIte]
        rw [countP_point]
        have : k - 1 < k := by omega
        simp [this]
      · simp [h0]
    rw [h3] at h
    rw [← h]
  rw [hnd] at hsplit
  omega

theorem per_cycle_pathConstraints {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) :
    2 * (((List.range k).map fun a => (List.range k).countP fun b =>
      decide (a < b) && disjointEdges ((cycleEdges c).getD a (0, 0)) ((cycleEdges c).getD b (0, 0))).sum) =
      k * (k - 3) := by
  have hk := hc.1
  -- sum the identity of `disjoint_pairs_count` over `a`
  have hsum : ((List.range k).map fun a => (List.range k).countP fun b =>
      decide (a < b) && disjointEdges ((cycleEdges c).getD a (0, 0)) ((cycleEdges c).getD b (0, 0))).sum +
      ((List.range k).map fun a => (if a + 1 < k then 1 else 0) + (if a = 0 then 1 else 0)).sum =
      ((List.range k).map fun a => k - (a + 1)).sum := by
    rw [← sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    exact disjoint_pairs_count hc (List.mem_range.mp ha)
  have hnd : ((List.range k).map fun a => (if a + 1 < k then 1 else 0) + (if a = 0 then 1 else 0)).sum = k := by
    rw [sum_map_add]
    have h1 : ((List.range k).map fun a => if a + 1 < k then 1 else 0).sum = k - 1 := by
      have := countP_gt_range k 0
      -- countP (0 < b) = k - 1; reindex: a + 1 < k ↔ a < k - 1
      have hc' : ((List.range k).map fun a => if a + 1 < k then 1 else 0).sum =
          (List.range k).countP fun a => decide (a + 1 < k) := by
        rw [countP_eq_sum_range _ 0]
        simp only [List.length_range]
        apply congrArg List.sum
        apply List.map_congr_left
        intro a ha
        simp [List.getD_eq_getElem?_getD, List.getElem?_range (List.mem_range.mp ha)]
      rw [hc']
      have : (List.range k).countP (fun a => decide (a + 1 < k)) = (List.range k).countP (fun a => decide (a < k - 1)) := by
        apply List.countP_congr; intro a _; simp; omega
      rw [this, countP_lt_range]
      omega
    have h2 : ((List.range k).map fun a => if a = 0 then 1 else 0).sum = 1 := by
      rw [sum_map_range_single k 0 _ (fun a ha => by simp [ha])]
      simp; omega
    omega
  have htri : ((List.range k).map fun a => k - (a + 1)).sum = pairCount k := by
    clear hsum hnd hc hk
    induction k with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.sub_self]
      have : ((List.range n).map fun a => n + 1 - (a + 1)).sum =
          ((List.range n).map fun a => (n - (a + 1)) + 1).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro a ha
        have := List.mem_range.mp ha
        omega
      rw [this, sum_map_add, ih, sum_map_const, List.length_range]
      rw [show pairCount (n + 1) = pairCount n + n from rfl]
      omega
  have h2p := two_mul_pairCount k
  have hk3 : k * (k - 1) = k * (k - 3) + 2 * k := by
    rw [show k - 1 = (k - 3) + 2 by omega, Nat.mul_add, Nat.mul_comm k 2]
  omega

/-- `Γ₁` has exactly `k(k−3)t/2` clauses. -/
theorem two_mul_pathConstraints_length (g : Graph) (k : Nat) :
    2 * (pathConstraints g k).length = k * (k - 3) * (cycles g k).length := by
  rw [pathConstraints, List.length_flatMap]
  have : ((List.range (cycles g k).length).map fun i =>
      ((List.range k).flatMap fun a => (List.range k).filterMap fun b =>
        if decide (a < b) && disjointEdges (cycleEdgeAt g k i a) (cycleEdgeAt g k i b) then
          some [(⟨pathVariable k i a, false⟩ : Literal), ⟨pathVariable k i b, false⟩] else none).length) =
      (List.range (cycles g k).length).map fun _ => k * (k - 3) / 2 := by
    apply List.map_congr_left
    intro i hi
    have hc := kCycle_isCycle g (List.mem_range.mp hi)
    have hper := per_cycle_pathConstraints hc
    rw [List.length_flatMap]
    have hlen : ((List.range k).map fun a => ((List.range k).filterMap fun b =>
        if decide (a < b) && disjointEdges (cycleEdgeAt g k i a) (cycleEdgeAt g k i b) then
          some [(⟨pathVariable k i a, false⟩ : Literal), ⟨pathVariable k i b, false⟩] else none).length) =
        (List.range k).map fun a => (List.range k).countP fun b =>
          decide (a < b) && disjointEdges ((cycleEdges (kCycle g k i)).getD a (0, 0)) ((cycleEdges (kCycle g k i)).getD b (0, 0)) := by
      apply List.map_congr_left
      intro a _
      rw [List.length_filterMap_eq_countP]
      apply List.countP_congr
      intro b _
      simp only [cycleEdgeAt]
      simp
    rw [hlen]
    omega
  rw [this, sum_map_const, List.length_range]
  -- `k(k-3)` is even
  have heven : k * (k - 3) / 2 * 2 = k * (k - 3) := by
    by_cases hk : 3 ≤ k
    · have h := two_mul_pairCount k
      have : k * (k - 3) = 2 * pairCount k - 2 * k := by
        rw [h]
        have : k * (k - 1) = k * (k - 3) + 2 * k := by
          have : k - 1 = (k - 3) + 2 := by omega
          rw [this, Nat.mul_add, Nat.mul_comm k 2]
        omega
      rw [this]
      have : (2 * pairCount k - 2 * k) / 2 = pairCount k - k := by omega
      rw [this]
      omega
    · have : k - 3 = 0 := by omega
      simp [this]
  calc 2 * ((cycles g k).length * (k * (k - 3) / 2)) = (cycles g k).length * (k * (k - 3) / 2 * 2) := by
        rw [Nat.mul_comm 2, Nat.mul_assoc]
    _ = k * (k - 3) * (cycles g k).length := by rw [heven, Nat.mul_comm]

/-! ## Counting the candidate overlaps -/

/-- `|𝒰| ≤ kt(t−1)/2`: cycle `i` shares each of its `k` edges with at most `t − 1 − i` later cycles. -/
theorem two_mul_candidateOverlaps_length_le (g : Graph) (k : Nat) :
    2 * (candidateOverlaps g k).length ≤ k * (cycles g k).length * ((cycles g k).length - 1) := by
  have hrow : ∀ i, i < (cycles g k).length →
      ((List.range (cycles g k).length).map fun i' =>
        (if i < i' then ((cycleEdges (kCycle g k i)).filter fun e =>
          (cycleEdges (kCycle g k i')).contains e).map (fun e => (i, i', e)) else []).length).sum ≤
      k * ((cycles g k).length - (i + 1)) := by
    intro i hi
    have hc := kCycle_isCycle g hi
    have hle : ∀ i', ((if i < i' then ((cycleEdges (kCycle g k i)).filter fun e =>
        (cycleEdges (kCycle g k i')).contains e).map (fun e => (i, i', e)) else []).length) ≤
        if i < i' then k else 0 := by
      intro i'
      split
      · rw [List.length_map]
        have := List.length_filter_le (fun e => (cycleEdges (kCycle g k i')).contains e) (cycleEdges (kCycle g k i))
        rw [hc.edge_length] at this
        exact this
      · exact Nat.le_refl _
    have h1 := sum_map_le_sum_map (List.range (cycles g k).length) _ _ (fun i' _ => hle i')
    have h2 : ((List.range (cycles g k).length).map fun i' => if i < i' then k else 0).sum =
        k * ((cycles g k).length - (i + 1)) := by
      have : ((List.range (cycles g k).length).map fun i' => if i < i' then k else 0) =
          (List.range (cycles g k).length).map fun i' => (if decide (i < i') then 1 else 0) * k := by
        apply List.map_congr_left; intro i' _; split <;> rename_i h <;> simp [h]
      rw [this]
      have hm : ∀ (l : List Nat) (q : Nat → Bool), (l.map fun x => (if q x then 1 else 0) * k).sum = l.countP q * k := by
        intro l q
        induction l with
        | nil => simp
        | cons x l ih =>
          simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
          split <;> simp [Nat.add_mul] <;> omega
      rw [hm, countP_gt_range, Nat.mul_comm]
    rw [h2] at h1
    exact h1
  have htri : ∀ t, ((List.range t).map fun i => k * (t - (i + 1))).sum = k * pairCount t := by
    intro t
    induction t with
    | zero => simp [pairCount]
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.sub_self,
        Nat.mul_zero]
      have : ((List.range n).map fun i => k * (n + 1 - (i + 1))).sum =
          ((List.range n).map fun i => k * (n - (i + 1)) + k).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro i hi
        have := List.mem_range.mp hi
        rw [show n + 1 - (i + 1) = (n - (i + 1)) + 1 by omega, Nat.mul_succ]
      rw [this, sum_map_add, ih, sum_map_const, List.length_range]
      rw [show pairCount (n + 1) = pairCount n + n from rfl, Nat.mul_add, Nat.mul_comm n k]
  have key : (candidateOverlaps g k).length ≤ k * pairCount (cycles g k).length := by
    rw [candidateOverlaps, List.length_flatMap]
    simp only [List.length_flatMap]
    have hsum := sum_map_le_sum_map (List.range (cycles g k).length) _ _
      (fun i hi => hrow i (List.mem_range.mp hi))
    rw [htri] at hsum
    exact hsum
  have h2p := two_mul_pairCount (cycles g k).length
  calc 2 * (candidateOverlaps g k).length
      ≤ 2 * (k * pairCount (cycles g k).length) := Nat.mul_le_mul_left 2 key
    _ = k * (2 * pairCount (cycles g k).length) := by rw [Nat.mul_left_comm]
    _ = k * ((cycles g k).length * ((cycles g k).length - 1)) := by rw [h2p]
    _ = k * (cycles g k).length * ((cycles g k).length - 1) := by rw [Nat.mul_assoc]

/-! ## The zero-cost formula -/

theorem prefixClauses_two_literals (g : Graph) (k : Nat) {e : Edge} (he : e ∈ edgesOnCycles g k) :
    ∀ cl ∈ prefixClauses g k e, cl.length = 2 ∧ ∀ l ∈ cl, l.var < 2 * (k * (cycles g k).length) := by
  intro cl hcl
  have hb : ∀ x, x < (cyclesThrough g k e).length →
      edgeVariable g k ((cyclesThrough g k e).getD x 0) e < 2 * (k * (cycles g k).length) := by
    intro x hx
    have := edgeVariable_lt g (cyclesThrough_getD_lt g k e hx) (cyclesThrough_getD_mem g k e hx)
    omega
  rcases (mem_prefixClauses g k e cl).mp hcl with ⟨x, hx, rfl⟩ | ⟨x, hx0, hx, rfl⟩ | ⟨x, hx0, hx, rfl⟩ <;>
    refine ⟨rfl, ?_⟩ <;> intro l hl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl
  · exact hb x (by omega)
  · exact prefixVariable_lt he hx
  · exact prefixVariable_lt he (by omega)
  · exact prefixVariable_lt he hx
  · exact hb x hx
  · exact prefixVariable_lt he (by omega)

theorem zeroCostFormula_two_cnf (g : Graph) (k : Nat) :
    ∀ cl ∈ zeroCostFormula g k, cl.length = 2 ∧ ∀ l ∈ cl, l.var < 2 * (k * (cycles g k).length) := by
  intro cl hcl
  rcases (mem_zeroCostFormula g k cl).mp hcl with hcl | ⟨e, he, hcl⟩
  · obtain ⟨h1, h2⟩ := pathConstraints_two_literals g k cl hcl
    exact ⟨h1, fun l hl => by have := h2 l hl; omega⟩
  · exact prefixClauses_two_literals g k he cl hcl

theorem prefixClauses_length_le (g : Graph) (k : Nat) (e : Edge) :
    (prefixClauses g k e).length ≤ 3 * (cyclesThrough g k e).length := by
  unfold prefixClauses
  simp only [List.length_append, List.length_map, List.length_range]
  refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) (List.length_filterMap_le _ _))
    (List.length_filterMap_le _ _)) ?_
  simp only [List.length_range]
  omega

/-- The positive positions of `range n`, mapped to arbitrary values, number `n − 1`.
This counts clause occurrences, so repeated clauses are retained. -/
theorem filterMap_positive_range_length {α : Type} (f : Nat → α) (n : Nat) :
    ((List.range n).filterMap fun x => if 0 < x then some (f x) else none).length = n - 1 := by
  cases n with
  | zero => simp
  | succ n => simp [List.range_succ_eq_map, List.filterMap_map, Function.comp_def]

/-- For an edge in `p ≥ 2` cycles the three prefix families have, in order,
`p − 1`, `p − 2`, and `p − 1` clause occurrences, for a total of `3p − 4`. -/
theorem prefixClauses_length (g : Graph) (k : Nat) (e : Edge)
    (hp : 2 ≤ (cyclesThrough g k e).length) :
    (prefixClauses g k e).length = 3 * (cyclesThrough g k e).length - 4 := by
  simp only [prefixClauses, List.length_append, List.length_map, List.length_range,
    filterMap_positive_range_length]
  omega

/-- The listed auxiliary variables for an edge in `p` cycles are distinct and number
exactly `p − 1` (zero when `p ≤ 1`). -/
theorem prefixAuxiliaryVariables_count (g : Graph) (k : Nat) (e : Edge) :
    let vars := (List.range ((cyclesThrough g k e).length - 1)).map (prefixVariable g k e)
    vars.length = (cyclesThrough g k e).length - 1 ∧ vars.Nodup := by
  refine ⟨by simp, ?_⟩
  exact List.Pairwise.map (prefixVariable g k e)
    (by intro x y hne heq; unfold prefixVariable at heq; omega) List.nodup_range

/-- The zero-cost formula has at most `|Γ₁| + 3kt` clauses. -/
theorem zeroCostFormula_length_le (g : Graph) (k : Nat) :
    (zeroCostFormula g k).length ≤ (pathConstraints g k).length + 3 * (k * (cycles g k).length) := by
  rw [zeroCostFormula, List.length_append, List.length_flatMap]
  have := sum_map_le_sum_map (edgesOnCycles g k) (fun e => (prefixClauses g k e).length)
    (fun e => 3 * (cyclesThrough g k e).length) (fun e _ => prefixClauses_length_le g k e)
  have h3 : ((edgesOnCycles g k).map fun e => 3 * (cyclesThrough g k e).length).sum =
      3 * ((edgesOnCycles g k).map fun e => (cyclesThrough g k e).length).sum := by
    induction (edgesOnCycles g k) with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]
  rw [h3, sum_cyclesThrough_length] at this
  omega

/-! ## The compared size theorems -/

/-- The size of `Γ'`: a 2-CNF on the `kt` variables `b_{C,e}`, with `k(k−3)t/2` path
constraints, at most `kt(t−1)/2` candidate overlaps and `(Ψ+1)|Γ₁| + |𝒰|` clause occurrences,
`t` being the number of simple `k`-cycles. -/
theorem almostFormula_size (g : Graph) (k Ψ : Nat) :
    (∀ cl ∈ almostFormula g k Ψ, cl.length = 2 ∧ ∀ l ∈ cl, l.var < k * (cycles g k).length) ∧
    2 * (pathConstraints g k).length = k * (k - 3) * (cycles g k).length ∧
    2 * (candidateOverlaps g k).length ≤ k * (cycles g k).length * ((cycles g k).length - 1) ∧
    (almostFormula g k Ψ).length =
      (Ψ + 1) * (pathConstraints g k).length + (candidateOverlaps g k).length :=
  ⟨almostFormula_two_cnf g k Ψ, two_mul_pathConstraints_length g k,
   two_mul_candidateOverlaps_length_le g k, almostFormula_length g k Ψ⟩

/-- The size of the zero-cost formula: a 2-CNF on fewer than `2kt` variables with at most
`|Γ₁| + 3kt` clauses, where `2|Γ₁| = k(k−3)t`. -/
theorem zeroCostFormula_size (g : Graph) (k : Nat) :
    (∀ cl ∈ zeroCostFormula g k, cl.length = 2 ∧ ∀ l ∈ cl, l.var < 2 * (k * (cycles g k).length)) ∧
    (zeroCostFormula g k).length ≤ (pathConstraints g k).length + 3 * (k * (cycles g k).length) ∧
    2 * (pathConstraints g k).length = k * (k - 3) * (cycles g k).length :=
  ⟨zeroCostFormula_two_cnf g k, zeroCostFormula_length_le g k, two_mul_pathConstraints_length g k⟩

end STACS2027
