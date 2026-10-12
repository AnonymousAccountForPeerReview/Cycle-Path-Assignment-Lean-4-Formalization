module

public import Runtimes.ZeroCostSpec
public import Runtimes.TwoSatSpec
import Mathlib.Tactic

/-!
# Corollary 5 on the RAM: the formula the machine builds, and the recovery test

* `pcList k t` is the path-constraint part `Γ₁` as the RAM generates it: for every cycle `i`
  and positions `a, b < k`, the clause `¬b_{ik+a} ∨ ¬b_{ik+b}` when `a + 1 < b` and not
  `a = 0, b = k − 1` (the positions of vertex-disjoint edges, `pcList_eq`);
* `occClOf q x p o` are the clauses generated at occurrence `q` of an edge with `p` occurrences,
  of rank `x` and offset `o`, and `zcf g k = Γ₁ ++ ⋃_q occCl q`. It has exactly the clauses of
  `zeroCostFormula g k` (`mem_zcf`), so the same models (`evalCNF_zcf`); it is a 2-CNF over
  `2kt` variables (`zcf_two`) with at most `k²t + 3kt` clauses (`length_zcf_le`);
* `posOk g k σ i i₀` is the test of the recovery loop and `omittedPosition_eq` identifies
  Algorithm 3's `omittedPosition g k σ i` with the first position passing it;
  `zipWith_recover`: the paths `selected C_i pos_i` of the output positions are
  `recoverAssignment g k σ`.
-/

@[expose] public section

namespace STACS2027.Runtimes.ZeroCost

open STACS2027 Complexity.SAT STACS2027.RAM STACS2027.RAM.R0

/-! ### The path constraints as the RAM generates them -/

/-- The path constraint of positions `a, b` of cycle `i` (none unless `a + 1 < b` and not
`a = 0, b = k − 1`). -/
def pcCl (k i a b : ℕ) : CNF :=
  if a + 1 < b ∧ ¬ (a = 0 ∧ b + 1 = k) then [[⟨i * k + a, false⟩, ⟨i * k + b, false⟩]] else []

/-- The path constraints, cycle by cycle, pair by pair. -/
def pcList (k t : ℕ) : CNF :=
  (List.range t).flatMap fun i => (List.range k).flatMap fun a => (List.range k).flatMap (pcCl k i a)

theorem pcList_eq (g : Graph) (k : ℕ) : pcList k (cycles g k).length = pathConstraints g k := by
  unfold pcList pathConstraints
  apply List.flatMap_congr
  intro i hi
  have hc := kCycle_isCycle g (List.mem_range.mp hi)
  apply List.flatMap_congr
  intro a ha
  have ha' := List.mem_range.mp ha
  rw [List.filterMap_eq_flatMap_toList]
  apply List.flatMap_congr
  intro b hb
  have hb' := List.mem_range.mp hb
  have hd := disjointEdges_edgeAt hc ha' hb'
  have hiff : (decide (a < b) && disjointEdges (cycleEdgeAt g k i a) (cycleEdgeAt g k i b)) = true ↔
      (a + 1 < b ∧ ¬ (a = 0 ∧ b + 1 = k)) := by
    rw [Bool.and_eq_true, decide_eq_true_iff]
    unfold cycleEdgeAt
    rw [hd]
    unfold next
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · by_contra h
        apply h2
        right; right
        split <;> omega
      · rintro ⟨rfl, hbk⟩
        apply h2
        right; left
        split <;> omega
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      rintro (h | h | h)
      · omega
      · split at h <;> omega
      · split at h <;> omega
  unfold pcCl pathVariable
  by_cases hcnd : a + 1 < b ∧ ¬ (a = 0 ∧ b + 1 = k)
  · rw [ite_eq_left (hiff.mpr hcnd), ite_eq_left hcnd]; rfl
  · rw [ite_eq_right (fun h => hcnd (hiff.mp h)), ite_eq_right hcnd]; rfl

theorem length_pcCl_le (k i a b : ℕ) : (pcCl k i a b).length ≤ 1 := by
  unfold pcCl; split <;> simp

/-! ### The prefix clauses, occurrence by occurrence -/

/-- The clauses generated at an occurrence `q` of an edge with `p` occurrences, of rank `x`, whose
prefix variables start at `o`: `b_q ∨ s_x` (if `x + 1 < p`), `¬s_{x-1} ∨ s_x` (if
`0 < x`, `x + 1 < p`), `b_q ∨ ¬s_{x-1}` (if `0 < x`). -/
def occClOf (q x p o : ℕ) : CNF :=
  (if x + 1 < p then [[⟨q, true⟩, ⟨o + x, true⟩]] else []) ++
    ((if 0 < x ∧ x + 1 < p then [[⟨o + (x - 1), false⟩, ⟨o + x, true⟩]] else []) ++
      (if 0 < x then [[⟨q, true⟩, ⟨o + (x - 1), false⟩]] else []))

theorem length_occClOf_le (q x p o : ℕ) : (occClOf q x p o).length ≤ 3 := by
  unfold occClOf; split <;> split <;> split <;> simp

section formula

variable (g : Graph) (k : ℕ)

/-- The clauses generated at occurrence `q`. -/
def occCl (q : ℕ) : CNF :=
  occClOf q (rank g k q) (cntF g k (k * (cycles g k).length) (eidOf g k q)) (offF g k (eidOf g k q))

/-- The formula built by the machine: the path constraints, then the clauses of every
occurrence. -/
def zcf : CNF := pathConstraints g k ++ (List.range (k * (cycles g k).length)).flatMap (occCl g k)

variable {g k}

/-- The facts about an occurrence used for the membership equivalence. -/
theorem occ_facts {q : ℕ} (hq : q < k * (cycles g k).length) :
    let e := (occs g k).getD q (0, 0)
    e ∈ edgesOnCycles g k ∧
      cntF g k (k * (cycles g k).length) (eidOf g k q) = (cyclesThrough g k e).length ∧
      offF g k (eidOf g k q) = prefixOffset g k e ∧
      rank g k q < (cyclesThrough g k e).length ∧
      edgeVariable g k ((cyclesThrough g k e).getD (rank g k q) 0) e = q := by
  intro e
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hq
    · exact h
  obtain ⟨hi, hj, hqe⟩ := occ_decomp hk hq
  obtain ⟨hr1, hr2⟩ := rank_spec hq hk
  refine ⟨occs_getD_mem_eoc hq, cntF_final hq, offF_eidOf hq, hr2, ?_⟩
  rw [hr1]
  have he : e = cycleEdgeAt g k (q / k) (q % k) := by
    simp only [e]; conv_lhs => rw [hqe]
    exact occs_getD_cycleEdgeAt hi hj
  rw [he, edgeVariable_eq hi hj, pathVariable]
  exact hqe.symm

theorem mem_occCl_iff {q : ℕ} (hq : q < k * (cycles g k).length) (cl : Clause) :
    cl ∈ occCl g k q ↔ cl ∈ prefixClauses g k ((occs g k).getD q (0, 0)) ∧
      ((∃ x, x < (cyclesThrough g k ((occs g k).getD q (0, 0))).length - 1 ∧ x = rank g k q ∧
          cl = [⟨edgeVariable g k ((cyclesThrough g k ((occs g k).getD q (0, 0))).getD x 0)
            ((occs g k).getD q (0, 0)), true⟩, ⟨prefixVariable g k ((occs g k).getD q (0, 0)) x, true⟩]) ∨
        (∃ x, 0 < x ∧ x < (cyclesThrough g k ((occs g k).getD q (0, 0))).length - 1 ∧ x = rank g k q ∧
          cl = [⟨prefixVariable g k ((occs g k).getD q (0, 0)) (x - 1), false⟩,
            ⟨prefixVariable g k ((occs g k).getD q (0, 0)) x, true⟩]) ∨
        (∃ x, 0 < x ∧ x < (cyclesThrough g k ((occs g k).getD q (0, 0))).length ∧ x = rank g k q ∧
          cl = [⟨edgeVariable g k ((cyclesThrough g k ((occs g k).getD q (0, 0))).getD x 0)
            ((occs g k).getD q (0, 0)), true⟩, ⟨prefixVariable g k ((occs g k).getD q (0, 0)) (x - 1), false⟩])) := by
  obtain ⟨_, hp, ho, hx, hv⟩ := occ_facts hq
  unfold occCl occClOf
  rw [hp, ho]
  simp only [prefixVariable, List.mem_append]
  constructor
  · intro h
    have hcases : ((rank g k q + 1 < (cyclesThrough g k ((occs g k).getD q (0, 0))).length ∧
          cl = [⟨q, true⟩, ⟨prefixOffset g k ((occs g k).getD q (0, 0)) + rank g k q, true⟩]) ∨
        (0 < rank g k q ∧ rank g k q + 1 < (cyclesThrough g k ((occs g k).getD q (0, 0))).length ∧
          cl = [⟨prefixOffset g k ((occs g k).getD q (0, 0)) + (rank g k q - 1), false⟩,
            ⟨prefixOffset g k ((occs g k).getD q (0, 0)) + rank g k q, true⟩]) ∨
        (0 < rank g k q ∧
          cl = [⟨q, true⟩, ⟨prefixOffset g k ((occs g k).getD q (0, 0)) + (rank g k q - 1), false⟩])) := by
      rcases h with h | h | h
      · split at h
        · exact Or.inl ⟨by assumption, by simpa using h⟩
        · simp at h
      · split at h
        · rename_i hc; exact Or.inr (Or.inl ⟨hc.1, hc.2, by simpa using h⟩)
        · simp at h
      · split at h
        · exact Or.inr (Or.inr ⟨by assumption, by simpa using h⟩)
        · simp at h
    have hmem : cl ∈ prefixClauses g k ((occs g k).getD q (0, 0)) := by
      rw [mem_prefixClauses]
      rcases hcases with ⟨h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h2⟩
      · exact Or.inl ⟨rank g k q, by omega, by rw [h2, hv]; rfl⟩
      · exact Or.inr (Or.inl ⟨rank g k q, h0, by omega, by rw [h2]; rfl⟩)
      · exact Or.inr (Or.inr ⟨rank g k q, h0, hx, by rw [h2, hv]; rfl⟩)
    refine ⟨hmem, ?_⟩
    rcases hcases with ⟨h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h2⟩
    · exact Or.inl ⟨rank g k q, by omega, rfl, by rw [h2, hv]⟩
    · exact Or.inr (Or.inl ⟨rank g k q, h0, by omega, rfl, h2⟩)
    · exact Or.inr (Or.inr ⟨rank g k q, h0, hx, rfl, by rw [h2, hv]⟩)
  · rintro ⟨_, h⟩
    rcases h with ⟨x, hx1, rfl, rfl⟩ | ⟨x, hx0, hx1, rfl, rfl⟩ | ⟨x, hx0, hx1, rfl, rfl⟩
    · left; rw [ite_eq_left (by omega), hv]; simp
    · right; left; rw [ite_eq_left ⟨hx0, by omega⟩]; simp
    · right; right; rw [ite_eq_left hx0, hv]; simp

/-- **The machine's formula has the clauses of the zero-cost formula.** -/
theorem mem_zcf (cl : Clause) : cl ∈ zcf g k ↔ cl ∈ zeroCostFormula g k := by
  rw [mem_zeroCostFormula, zcf, List.mem_append, List.mem_flatMap]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨q, hq, hcl⟩
    have hq' := List.mem_range.mp hq
    exact ⟨_, (occ_facts hq').1, ((mem_occCl_iff hq' cl).mp hcl).1⟩
  · rintro ⟨e, he, hcl⟩
    -- the occurrence of `e` of the right rank
    have hrank : ∀ x, x < (cyclesThrough g k e).length →
        ∃ q, q < k * (cycles g k).length ∧ (occs g k).getD q (0, 0) = e ∧ rank g k q = x ∧
          edgeVariable g k ((cyclesThrough g k e).getD x 0) e = q := by
      intro x hx
      set i := (cyclesThrough g k e).getD x 0
      have hi : i < (cycles g k).length := cyclesThrough_getD_lt g k e hx
      have hei : e ∈ cycleEdges (kCycle g k i) := cyclesThrough_getD_mem g k e hx
      have hj := edgePosition_lt hi hei
      have hk : 0 < k := by omega
      have hq : i * k + edgePosition g k i e < k * (cycles g k).length := by
        have : (i + 1) * k ≤ (cycles g k).length * k := Nat.mul_le_mul_right k hi
        rw [Nat.add_mul, one_mul] at this
        rw [Nat.mul_comm k]; omega
      have hocc : (occs g k).getD (i * k + edgePosition g k i e) (0, 0) = e := by
        rw [occs_getD_cycleEdgeAt hi hj, cycleEdgeAt_edgePosition hi hei]
      refine ⟨i * k + edgePosition g k i e, hq, hocc, ?_, rfl⟩
      obtain ⟨hr1, hr2⟩ := rank_spec hq hk
      rw [hocc] at hr1 hr2
      have hdiv : (i * k + edgePosition g k i e) / k = i := by
        rw [Nat.mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt hj, Nat.add_zero]
      rw [hdiv] at hr1
      exact cyclesThrough_getD_inj g k e hr2 hx hr1
    have hcl' := (mem_prefixClauses g k e cl).mp hcl
    have hx : ∃ x, x < (cyclesThrough g k e).length ∧
        ((x < (cyclesThrough g k e).length - 1 ∧
          cl = [⟨edgeVariable g k ((cyclesThrough g k e).getD x 0) e, true⟩, ⟨prefixVariable g k e x, true⟩]) ∨
         (0 < x ∧ x < (cyclesThrough g k e).length - 1 ∧
          cl = [⟨prefixVariable g k e (x - 1), false⟩, ⟨prefixVariable g k e x, true⟩]) ∨
         (0 < x ∧ x < (cyclesThrough g k e).length ∧
          cl = [⟨edgeVariable g k ((cyclesThrough g k e).getD x 0) e, true⟩,
            ⟨prefixVariable g k e (x - 1), false⟩])) := by
      rcases hcl' with ⟨x, h1, h2⟩ | ⟨x, h0, h1, h2⟩ | ⟨x, h0, h1, h2⟩
      · exact ⟨x, by omega, Or.inl ⟨h1, h2⟩⟩
      · exact ⟨x, by omega, Or.inr (Or.inl ⟨h0, h1, h2⟩)⟩
      · exact ⟨x, h1, Or.inr (Or.inr ⟨h0, h1, h2⟩)⟩
    obtain ⟨x, hxl, hcase⟩ := hx
    obtain ⟨q, hq, hqe, hqr, _⟩ := hrank x hxl
    refine ⟨q, List.mem_range.mpr hq, (mem_occCl_iff hq cl).mpr ⟨by rw [hqe]; exact hcl, ?_⟩⟩
    rw [hqe]
    rcases hcase with ⟨h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · exact Or.inl ⟨x, h1, hqr.symm, h2⟩
    · exact Or.inr (Or.inl ⟨x, h0, h1, hqr.symm, h2⟩)
    · exact Or.inr (Or.inr ⟨x, h0, h1, hqr.symm, h2⟩)

/-- The machine's formula has the models of the zero-cost formula. -/
theorem evalCNF_zcf (σ : Assignment) : evalCNF σ (zcf g k) = evalCNF σ (zeroCostFormula g k) := by
  rw [Bool.eq_iff_iff, evalCNF_iff, evalCNF_iff]
  exact forall_congr' fun cl => imp_congr (mem_zcf cl) Iff.rfl

/-- The machine's formula is a 2-CNF over the `2kt` variables. -/
theorem zcf_two : TwoSat.IsTwoCNF (2 * (k * (cycles g k).length)) (zcf g k) := fun cl hcl =>
  zeroCostFormula_two_cnf g k cl ((mem_zcf cl).mp hcl)

theorem length_pathConstraints_le : (pathConstraints g k).length ≤ k * k * (cycles g k).length := by
  have h := two_mul_pathConstraints_length g k
  have h2 : k * (k - 3) * (cycles g k).length ≤ k * k * (cycles g k).length :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le k 3))
  omega

/-- The number of clauses of the machine's formula. -/
theorem length_zcf_le :
    (zcf g k).length ≤ k * k * (cycles g k).length + 3 * (k * (cycles g k).length) := by
  have h1 := length_pathConstraints_le (g := g) (k := k)
  have h2 : ((List.range (k * (cycles g k).length)).flatMap (occCl g k)).length ≤
      3 * (k * (cycles g k).length) := by
    rw [List.length_flatMap]
    have := sum_map_le_sum_map (List.range (k * (cycles g k).length)) (fun q => (occCl g k q).length)
      (fun _ => 3) (fun q _ => length_occClOf_le _ _ _ _)
    simp only [sum_map_const, List.length_range] at this
    linarith
  rw [zcf, List.length_append]; omega

end formula

/-! ### The recovery test -/

section recovery

variable (g : Graph) (k : ℕ)

/-- The test of position `i₀` of `C_i` under `σ`: every edge of `C_i` whose variable is true is
incident to the vertex at position `i₀`. -/
def posOk (σ : Assignment) (i i₀ : ℕ) : Bool :=
  (List.range k).all fun j => !σ (i * k + j) ||
    ((verts g k).getD (i * k + j) 0 == (verts g k).getD (i * k + i₀) 0 ||
      (verts g k).getD (i * k + next k j) 0 == (verts g k).getD (i * k + i₀) 0)

variable {g k}

theorem incident_edge (v x y : ℕ) : incident v (edge x y) = (x == v || y == v) := by
  unfold incident edge
  rcases Nat.le_total x y with h | h
  · simp [Nat.min_eq_left h, Nat.max_eq_right h]
  · simp [Nat.min_eq_right h, Nat.max_eq_left h, Bool.or_comm]

theorem all_congr_mem {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.all_cons, List.all_cons, h a (by simp),
      all_congr_mem (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- **Algorithm 3's omitted position** is the first position passing the test `posOk`. -/
theorem omittedPosition_eq (σ : Assignment) {i : ℕ} (hi : i < (cycles g k).length) :
    omittedPosition g k σ i = ((List.range k).find? (posOk g k σ i)).getD 0 := by
  have hc := kCycle_isCycle g hi
  unfold omittedPosition
  congr 1
  apply List.find?_congr
  intro i₀ hi₀
  have hi₀' := List.mem_range.mp hi₀
  unfold markedEdges posOk
  rw [List.all_filter]
  have hce : cycleEdges (kCycle g k i) = (List.range k).map (cycleEdgeAt g k i) := by
    have := map_getD_range (cycleEdges (kCycle g k i)) (0, 0)
    rw [hc.edge_length] at this
    exact this.symm
  rw [hce, List.all_map]
  apply all_congr_mem
  intro j hj
  have hj' := List.mem_range.mp hj
  simp only [Function.comp_apply]
  rw [edgeVariable_eq hi hj', pathVariable, ← occs_getD_cycleEdgeAt hi hj', occs_getD hi hj',
    incident_edge, verts_getD hi hi₀']

theorem find?_range_succ (p : ℕ → Bool) (n : ℕ) :
    (List.range (n + 1)).find? p = ((List.range n).find? p).or (if p n then some n else none) := by
  rw [List.range_succ, List.find?_append]
  congr 1
  by_cases h : p n <;> simp [h]

theorem all_range_succ (p : ℕ → Bool) (n : ℕ) :
    (List.range (n + 1)).all p = ((List.range n).all p && p n) := by
  rw [List.range_succ, List.all_append]; simp

/-- The paths of the output positions are the recovered assignment. -/
theorem zipWith_recover (σ : Assignment) :
    List.zipWith selected (cycles g k) ((List.range (cycles g k).length).map (omittedPosition g k σ)) =
      recoverAssignment g k σ := by
  unfold recoverAssignment recoveredPath
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, kCycle]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h1; omega)]
    rfl

end recovery

end STACS2027.Runtimes.ZeroCost
