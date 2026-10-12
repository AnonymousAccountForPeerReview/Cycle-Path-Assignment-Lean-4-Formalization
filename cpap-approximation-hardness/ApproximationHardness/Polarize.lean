module

public import ApproximationHardness.Optimization
public import ApproximationHardness.Sums

/-!
# Lemma 10: from 3-OCCURRENCE MAX-3-SAT to MAX-(≤1,≤2)-SAT

"We give an L-reduction from 3-OCCURRENCE MAX-3-SAT with `α = β = 1`. Repeatedly set any
variable that occurs with only one polarity to the value satisfying all its occurrences,
and delete the clauses thereby satisfied. Let `r` be the number of deleted clauses and let
`ψ` be the remaining formula. [...] Every remaining variable occurs with both polarities.
Complementing variables that occur twice positively and once negatively therefore gives a
formula `ψ'` satisfying the required occurrence bounds, without changing its objective
values. To preserve the optimum, form the target formula `φ'` by adding `r` clauses
`(a_j ∨ b_j)` to `ψ'`, each using two fresh variables." (Appendix D of the paper.)

The formalization also deletes every clause containing a variable and its negation, because without this step `ψ'` can contain a clause with a repeated variable, which Definition 7
excludes (for `(x ∨ ¬x ∨ y) ∧ (¬y ∨ w) ∧ (¬w ∨ y)` nothing is eliminated, `y` is complemented,
and `(x ∨ ¬x ∨ ¬y)` remains; `docs/paper-map.md`). Such a clause is satisfied by every
assignment, so deleting it and padding one clause keeps both L-reduction conditions.
It eliminates only the variables that must go: those with three
occurrences of a single polarity. A variable occurring with one polarity at most twice
already meets the bounds, after complementation if it occurs twice positively; and a
variable that loses occurrences when clauses are deleted keeps at most two, so one round
of deletion suffices (`polarize_leOneLeTwo`). This module defines the transformation and
proves that its output satisfies Definition 7; `ApproximationHardness/PolarizeLReduction.lean` proves the
L-reduction inequalities.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-! ## The source problem -/

/-- 3-OCCURRENCE MAX-3-SAT: clauses of two or three distinct literals, each variable at most three times. -/
def ThreeOccurrence (f : CNF) : Prop :=
  (∀ c ∈ f, c.length = 2 ∨ c.length = 3) ∧ (∀ c ∈ f, c.Nodup) ∧
    ∀ v, occurrences f v true + occurrences f v false ≤ 3

/-! ## The transformation -/

/-- The variable `v` occurs in `f` exactly three times, all with the same polarity. -/
def pureThree (f : CNF) (v : Nat) : Bool :=
  (occurrences f v true == 3 && occurrences f v false == 0) ||
    (occurrences f v false == 3 && occurrences f v true == 0)

/-- The value satisfying all occurrences of a variable of one polarity. -/
def pureValue (f : CNF) (v : Nat) : Bool := occurrences f v true == 3

/-- The clauses Lemma 10 deletes: the tautological ones and those satisfied by an eliminated variable. -/
def deleted (f : CNF) (c : Clause) : Bool := tautological c || c.any fun l => pureThree f l.var

/-- `ψ`, the remaining formula. -/
def kept (f : CNF) : CNF := f.filter fun c => !deleted f c

/-- `r`, the number of deleted clauses. -/
def deletedCount (f : CNF) : Nat := f.countP (deleted f)

/-- The variables to complement: those occurring twice positively in `ψ`. -/
def complemented (f : CNF) (v : Nat) : Bool := 2 ≤ occurrences (kept f) v true

/-- Complementing the variables selected by `F` in a literal. -/
def flipLiteral (F : Nat → Bool) (l : Literal) : Literal :=
  if F l.var then ⟨l.var, !l.positive⟩ else l

/-- Complementing the variables selected by `F` in a formula. -/
def flipFormula (F : Nat → Bool) (g : CNF) : CNF := g.map (List.map (flipLiteral F))

/-- The `r` clauses `(a_j ∨ b_j)` on the fresh variables `base, base + 1, …`. -/
def padding (base r : Nat) : CNF :=
  (List.range r).map fun j => [⟨base + 2 * j, true⟩, ⟨base + 2 * j + 1, true⟩]

/-- `φ'`, the MAX-(≤1,≤2)-SAT instance of Lemma 10: `ψ'` followed by the padding. -/
def polarize (f : CNF) : CNF :=
  flipFormula (complemented f) (kept f) ++ padding (variableBound f) (deletedCount f)

/-! ## Occurrence counts -/

theorem sublist_flatten_of_sublist {α : Type} {l₁ l₂ : List (List α)} (h : l₁.Sublist l₂) :
    l₁.flatten.Sublist l₂.flatten := by
  induction h with
  | slnil => exact List.Sublist.refl _
  | cons a _ ih => simp only [List.flatten_cons]; exact ih.trans (List.sublist_append_right _ _)
  | cons_cons a _ ih => simp only [List.flatten_cons]; exact ih.append_left a

theorem occurrences_kept_le (f : CNF) (v : Nat) (p : Bool) :
    occurrences (kept f) v p ≤ occurrences f v p := by
  rw [occurrences_eq_count, occurrences_eq_count]
  exact (sublist_flatten_of_sublist List.filter_sublist).count_le _

theorem occurrences_flipFormula (F : Nat → Bool) (g : CNF) (v : Nat) (p : Bool) :
    occurrences (flipFormula F g) v p = occurrences g v (if F v then !p else p) := by
  rw [occurrences_eq_count, occurrences_eq_count, flipFormula, ← List.map_flatten,
    List.count_eq_countP, List.count_eq_countP, List.countP_map]
  apply List.countP_congr
  intro l _
  cases l with
  | mk x q =>
    simp only [Function.comp_def, beq_iff_eq, flipLiteral]
    by_cases hv : x = v
    · subst hv
      cases hF : F x <;> cases q <;> cases p <;> simp
    · cases hF : F x <;> simp [hv]

theorem occurrences_eq_zero_of_forall {g : CNF} {v : Nat} {p : Bool}
    (h : ∀ c ∈ g, ∀ l ∈ c, ¬ (l.var = v ∧ l.positive = p)) : occurrences g v p = 0 := by
  rw [occurrences_eq_count]
  apply List.count_eq_zero_of_not_mem
  intro hm
  obtain ⟨c, hc, hl⟩ := List.mem_flatten.mp hm
  exact h c hc _ hl ⟨rfl, rfl⟩

theorem occurrences_padding_lt {base r v : Nat} (hv : v < base) (p : Bool) :
    occurrences (padding base r) v p = 0 := by
  apply occurrences_eq_zero_of_forall
  intro c hc l hl
  simp only [padding, List.mem_map, List.mem_range] at hc
  obtain ⟨j, _, rfl⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> simp <;> omega

theorem occurrences_padding_false (base r v : Nat) : occurrences (padding base r) v false = 0 := by
  apply occurrences_eq_zero_of_forall
  intro c hc l hl
  simp only [padding, List.mem_map, List.mem_range] at hc
  obtain ⟨j, _, rfl⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> simp

theorem occurrences_padding_true_le (base r v : Nat) : occurrences (padding base r) v true ≤ 1 := by
  induction r with
  | zero => simp [padding, occurrences]
  | succ r ih =>
    have : padding base (r + 1) = padding base r ++ [[⟨base + 2 * r, true⟩, ⟨base + 2 * r + 1, true⟩]] := by
      simp [padding, List.range_succ]
    rw [this, occurrences_append]
    by_cases hv : v < base + 2 * r
    · have : occurrences [[⟨base + 2 * r, true⟩, ⟨base + 2 * r + 1, true⟩]] v true = 0 := by
        apply occurrences_eq_zero_of_forall
        intro c hc l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> simp <;> omega
      omega
    · have hz : occurrences (padding base r) v true = 0 := by
        apply occurrences_eq_zero_of_forall
        intro c hc l hl
        simp only [padding, List.mem_map, List.mem_range] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> simp <;> omega
      rw [hz]
      simp only [occurrences, List.flatten_cons, List.flatten_nil, List.append_nil, Nat.zero_add]
      by_cases h1 : base + 2 * r = v
      · subst h1
        simp
      · by_cases h2 : base + 2 * r + 1 = v
        · simp [h1, h2]
        · simp [h1, h2]

theorem occurrences_kept_pure {f : CNF} {v : Nat} (hv : pureThree f v = true) (p : Bool) :
    occurrences (kept f) v p = 0 := by
  apply occurrences_eq_zero_of_forall
  intro c hc l hl hlv
  have hkept := (List.mem_filter.mp hc).2
  simp only [Bool.not_eq_true', deleted, Bool.or_eq_false_iff, List.any_eq_false] at hkept
  exact absurd hv (by simpa [hlv.1] using hkept.2 l hl)

/-! ## The output satisfies Definition 7 -/

theorem variable_lt_of_mem_flipFormula_kept {f : CNF} {c : Clause}
    (hc : c ∈ flipFormula (complemented f) (kept f)) {l : Literal} (hl : l ∈ c) :
    l.var < variableBound f := by
  simp only [flipFormula, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  have hcf : c' ∈ f := (List.mem_filter.mp hc').1
  have := literal_lt_variableBound hcf hl'
  simp only [flipLiteral]
  split <;> simpa

theorem polarize_boundedOccurrence {f : CNF} (hf : ThreeOccurrence f) : BoundedOccurrence (polarize f) := by
  obtain ⟨hsize, _, hocc⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · simp only [flipFormula, List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      rw [List.length_map]
      exact hsize c' (List.mem_filter.mp hc').1
    · simp only [padding, List.mem_map] at hc
      obtain ⟨j, _, rfl⟩ := hc
      exact Or.inl rfl
  · intro v
    rw [polarize, occurrences_append, occurrences_flipFormula]
    by_cases hv : v < variableBound f
    · rw [occurrences_padding_lt hv, Nat.add_zero]
      have h3 := hocc v
      have hkt := occurrences_kept_le f v true
      have hkf := occurrences_kept_le f v false
      by_cases hc : complemented f v = true
      · simp only [hc, ↓reduceIte, Bool.not_true]
        simp only [complemented, decide_eq_true_eq] at hc
        omega
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        simp only [complemented, decide_eq_true_eq] at hc
        omega
    · have hz : ∀ p, occurrences (kept f) v p = 0 := by
        intro p
        apply occurrences_eq_zero_of_forall
        intro c hc l hl hlv
        have hcf : c ∈ f := (List.mem_filter.mp hc).1
        have := literal_lt_variableBound hcf hl
        omega
      rw [hz, Nat.zero_add]
      exact occurrences_padding_true_le _ _ v
  · intro v
    rw [polarize, occurrences_append, occurrences_flipFormula, occurrences_padding_false, Nat.add_zero]
    have h3 := hocc v
    have hkt := occurrences_kept_le f v true
    have hkf := occurrences_kept_le f v false
    by_cases hc : complemented f v = true
    · simp only [hc, ↓reduceIte, Bool.not_false]
      simp only [complemented, decide_eq_true_eq] at hc
      -- `v` occurs at most twice positively in `ψ`: three times would make it pure in `f`
      by_cases h3' : occurrences (kept f) v true = 3
      · have hpure : pureThree f v = true := by
          simp only [pureThree, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
          left
          omega
        have := occurrences_kept_pure hpure true
        omega
      · omega
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      simp only [complemented, decide_eq_true_eq] at hc
      by_cases h3' : occurrences (kept f) v false = 3
      · have hpure : pureThree f v = true := by
          simp only [pureThree, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
          right
          omega
        have := occurrences_kept_pure hpure false
        omega
      · omega

theorem polarize_clauseVariablesDistinct {f : CNF} (hf : ThreeOccurrence f) :
    ClauseVariablesDistinct (polarize f) := by
  obtain ⟨_, hnodup, _⟩ := hf
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [flipFormula, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    have hcf : c' ∈ f := (List.mem_filter.mp hc').1
    have hkept := (List.mem_filter.mp hc').2
    simp only [Bool.not_eq_true', deleted, Bool.or_eq_false_iff] at hkept
    have htaut := hkept.1
    have hvars : (c'.map Literal.var).Nodup := by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      have hn := hnodup c' hcf
      rw [List.nodup_iff_pairwise_ne] at hn
      refine hn.imp_of_mem ?_
      intro l l' hl hl' hne heq
      -- two distinct literals on one variable form a tautology
      have hpos : l'.positive = !l.positive := by
        cases l with
        | mk x p =>
          cases l' with
          | mk y q =>
            simp only at heq hne ⊢
            subst heq
            cases p <;> cases q <;> simp_all
      have : tautological c' = true := by
        simp only [tautological, List.any_eq_true]
        refine ⟨l, hl, l', hl', ?_⟩
        simp [heq, hpos]
      rw [htaut] at this
      cases this
    have : (c'.map (flipLiteral (complemented f))).map Literal.var = c'.map Literal.var := by
      rw [List.map_map]
      apply List.map_congr_left
      intro l _
      simp only [Function.comp_def, flipLiteral]
      split <;> rfl
    rw [this]
    exact hvars
  · simp only [padding, List.mem_map] at hc
    obtain ⟨j, _, rfl⟩ := hc
    simp

/-- The output of Lemma 10 is an instance of MAX-(≤1,≤2)-SAT with distinct variables in each
clause (Definition 7). -/
theorem polarize_leOneLeTwo {f : CNF} (hf : ThreeOccurrence f) :
    BoundedOccurrence (polarize f) ∧ ClauseVariablesDistinct (polarize f) :=
  ⟨polarize_boundedOccurrence hf, polarize_clauseVariablesDistinct hf⟩

end STACS2027
