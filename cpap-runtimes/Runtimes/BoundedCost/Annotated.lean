module

public import Runtimes.BoundedCost.Solver
import Mathlib.Tactic

/-!
# Clause-occurrence semantics and the compression branches of Almost 2-SAT

The compression step of ANONYMIZED and ANONYMIZED [RO09] assigns each clause of a
known deletion set one of three choices: delete it, require its first literal,
or require its second literal.  The definitions here count occurrences, so
repeated clauses remain distinct.  The resulting annotated subproblem keeps
the required literals fixed while deleting clauses from the other formula.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

/-- The number of clause occurrences falsified by an assignment. -/
def unsatisfiedCount (σ : Assignment) (f : CNF) : ℕ :=
  f.countP fun c => !(evalClause σ c)

@[simp] theorem unsatisfiedCount_nil (σ : Assignment) : unsatisfiedCount σ [] = 0 := rfl

@[simp] theorem unsatisfiedCount_cons (σ : Assignment) (c : Clause) (f : CNF) :
    unsatisfiedCount σ (c :: f) =
      (if evalClause σ c = true then 0 else 1) + unsatisfiedCount σ f := by
  simp only [unsatisfiedCount, List.countP_cons]
  cases evalClause σ c <;> simp [Nat.add_comm]

@[simp] theorem unsatisfiedCount_append (σ : Assignment) (f g : CNF) :
    unsatisfiedCount σ (f ++ g) = unsatisfiedCount σ f + unsatisfiedCount σ g := by
  simp [unsatisfiedCount]

/-- Deleting at most `k` occurrences is equivalent to falsifying at most `k`
occurrences under one assignment. -/
theorem almostSatisfiable_iff_unsatisfiedCount (f : CNF) (k : ℕ) :
    AlmostSatisfiable f k ↔ ∃ σ, unsatisfiedCount σ f ≤ k := by
  constructor
  · rintro ⟨sub, hsub, hlen, σ, hσ⟩
    refine ⟨σ, ?_⟩
    have hzero : unsatisfiedCount σ sub = 0 := by
      apply List.countP_eq_zero.mpr
      intro c hc
      simpa [(evalCNF_iff σ sub).mp hσ c hc]
    have hc := hsub.le_countP (fun c => !(evalClause σ c))
    change unsatisfiedCount σ f - (f.length - sub.length) ≤ unsatisfiedCount σ sub at hc
    have := hsub.length_le
    omega
  · rintro ⟨σ, hσ⟩
    refine ⟨f.filter (evalClause σ), List.filter_sublist, ?_, σ, ?_⟩
    · have hlen := List.length_eq_countP_add_countP (evalClause σ) (l := f)
      have hfilter : (f.filter (evalClause σ)).length = f.countP (evalClause σ) :=
        List.countP_eq_length_filter.symm
      have hneg : f.countP (fun c => ¬evalClause σ c) = unsatisfiedCount σ f := rfl
      omega
    · apply (evalCNF_iff σ _).mpr
      intro c hc
      exact (List.mem_filter.mp hc).2

/-- Clause deletion with a prescribed list of literals required to be true. -/
def AnnotatedAlmostSatisfiable (f : CNF) (L : List Literal) (k : ℕ) : Prop :=
  ∃ σ : Assignment, unsatisfiedCount σ f ≤ k ∧ ∀ l ∈ L, evalLiteral σ l = true

/-- Unit requirements encoded as two-literal clauses, as used by ordinary 2-SAT. -/
def forcedUnits (L : List Literal) : CNF := L.map fun l => [l, l]

theorem evalCNF_forcedUnits (σ : Assignment) (L : List Literal) :
    evalCNF σ (forcedUnits L) = true ↔ ∀ l ∈ L, evalLiteral σ l = true := by
  simp [forcedUnits, evalCNF, evalClause, List.all_map, List.all_eq_true]

theorem forcedUnits_twoCNF {n : ℕ} {L : List Literal}
    (hL : ∀ l ∈ L, l.var < n) : TwoSat.IsTwoCNF n (forcedUnits L) := by
  intro c hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨by simp, by simpa using hL l hl⟩

theorem annotated_zero_iff_satisfiable (f : CNF) (L : List Literal) :
    AnnotatedAlmostSatisfiable f L 0 ↔ Satisfiable (f ++ forcedUnits L) := by
  constructor
  · rintro ⟨σ, hcount, hL⟩
    refine ⟨σ, ?_⟩
    rw [evalCNF_append, Bool.and_eq_true]
    refine ⟨?_, (evalCNF_forcedUnits σ L).mpr hL⟩
    apply (evalCNF_iff σ f).mpr
    intro c hc
    have hn := List.countP_eq_zero.mp (Nat.eq_zero_of_le_zero hcount) c hc
    simpa using hn
  · rintro ⟨σ, hσ⟩
    rw [evalCNF_append, Bool.and_eq_true] at hσ
    refine ⟨σ, ?_, (evalCNF_forcedUnits σ L).mp hσ.2⟩
    have hz : unsatisfiedCount σ f = 0 := by
      apply List.countP_eq_zero.mpr
      intro c hc
      simpa [(evalCNF_iff σ f).mp hσ.1 c hc]
    omega

/-- A branch records the number of deleted special clauses and the literals
required by the special clauses retained in that branch. -/
abbrev CompressionBranch := ℕ × List Literal

/-- The three choices for a two-literal special clause. -/
def compressionBranches : CNF → List CompressionBranch
  | [] => [(0, [])]
  | [a, b] :: f =>
      (compressionBranches f).map (fun r => (r.1 + 1, r.2)) ++
      (compressionBranches f).map (fun r => (r.1, a :: r.2)) ++
      (compressionBranches f).map (fun r => (r.1, b :: r.2))
  | _ :: _ => []

/-- The branch list has exactly one entry for every ternary choice sequence. -/
theorem compressionBranches_length {f : CNF} (hf : Clauses2 f) :
    (compressionBranches f).length = 3 ^ f.length := by
  induction f with
  | nil => simp [compressionBranches]
  | cons c f ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf c (by simp))
    have htail : Clauses2 f := fun c hc => hf c (by simp [hc])
    simp [compressionBranches, ih htail, pow_succ]
    ring

/-- Every branch is sound: an assignment satisfying its required literals
falsifies at most the recorded number of special clauses. -/
theorem compressionBranches_sound {f : CNF} (hf : Clauses2 f) {r : CompressionBranch}
    (hr : r ∈ compressionBranches f) {σ : Assignment}
    (hL : ∀ l ∈ r.2, evalLiteral σ l = true) : unsatisfiedCount σ f ≤ r.1 := by
  induction f generalizing r with
  | nil => simp [compressionBranches] at hr; subst r; simp
  | cons c f ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf c (by simp))
    have htail : Clauses2 f := fun c hc => hf c (by simp [hc])
    simp only [compressionBranches, List.mem_append, List.mem_map] at hr
    rcases hr with (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩
    · have ht := ih htail hs hL
      rw [unsatisfiedCount_cons]
      split <;> omega
    · have ht := ih htail hs (fun l hl => hL l (by simp [hl]))
      have ha := hL a (by simp)
      simp [unsatisfiedCount_cons, evalClause, ha]
      exact ht
    · have ht := ih htail hs (fun l hl => hL l (by simp [hl]))
      have hb := hL b (by simp)
      simp [unsatisfiedCount_cons, evalClause, hb]
      exact ht

/-- Any assignment chooses a branch that deletes exactly its false special
clauses and requires only literals that it makes true. -/
theorem compressionBranches_complete {f : CNF} (hf : Clauses2 f) (σ : Assignment) :
    ∃ r ∈ compressionBranches f, r.1 = unsatisfiedCount σ f ∧
      ∀ l ∈ r.2, evalLiteral σ l = true := by
  induction f with
  | nil => exact ⟨(0, []), by simp [compressionBranches], rfl, by simp⟩
  | cons c f ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf c (by simp))
    have htail : Clauses2 f := fun c hc => hf c (by simp [hc])
    obtain ⟨r, hr, hcount, hL⟩ := ih htail
    by_cases ha : evalLiteral σ a = true
    · refine ⟨(r.1, a :: r.2), ?_, ?_, ?_⟩
      · simp only [compressionBranches, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨r, hr, rfl⟩)
      · simp [unsatisfiedCount_cons, evalClause, ha, hcount]
      · simpa using And.intro ha hL
    · by_cases hb : evalLiteral σ b = true
      · refine ⟨(r.1, b :: r.2), ?_, ?_, ?_⟩
        · simp only [compressionBranches, List.mem_append, List.mem_map]
          exact Or.inr ⟨r, hr, rfl⟩
        · simp [unsatisfiedCount_cons, evalClause, hb, hcount]
        · simpa using And.intro hb hL
      · refine ⟨(r.1 + 1, r.2), ?_, ?_, hL⟩
        · simp only [compressionBranches, List.mem_append, List.mem_map]
          exact Or.inl (Or.inl ⟨r, hr, rfl⟩)
        · have ha' : evalLiteral σ a = false := by simpa using ha
          have hb' : evalLiteral σ b = false := by simpa using hb
          simp [unsatisfiedCount_cons, evalClause, ha', hb', hcount, Nat.add_comm]

/-- Exact correctness of the finite compression branch reduction.  The
annotated solver still has to solve the base formula for each branch. -/
theorem almostSatisfiable_compression {base special : CNF} (hs : Clauses2 special) (k : ℕ) :
    AlmostSatisfiable (base ++ special) k ↔
      ∃ r ∈ compressionBranches special, r.1 ≤ k ∧
        AnnotatedAlmostSatisfiable base r.2 (k - r.1) := by
  rw [almostSatisfiable_iff_unsatisfiedCount]
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨r, hr, hcount, hL⟩ := compressionBranches_complete hs σ
    rw [unsatisfiedCount_append] at hσ
    refine ⟨r, hr, by omega, σ, by omega, hL⟩
  · rintro ⟨r, hr, hbudget, σ, hbase, hL⟩
    have hs' := compressionBranches_sound hs hr hL
    exact ⟨σ, by rw [unsatisfiedCount_append]; omega⟩

end STACS2027.Runtimes.BoundedCost
