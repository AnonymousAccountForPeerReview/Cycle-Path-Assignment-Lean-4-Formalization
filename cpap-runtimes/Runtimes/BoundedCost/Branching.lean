module

public import Runtimes.BoundedCost.Exchange
import Mathlib.Tactic

/-!
# Branching on a conflict in a least minimum cut

The least set of deviations among all minimum cuts is obtained from a maximum
flow by reverse residual reachability.  A conflict in that set is handled by
deleting its clause, or by requiring either reference-true literal.  Deletion
reduces the budget and leaves the cut optimum unchanged.  Either requirement
strictly increases the cut optimum.  Thus all three branches reduce the
remaining budget above the cut lower bound.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

/-- The required literal list is satisfied by the assignment. -/
def Requires (σ : Assignment) (L : List Literal) : Prop :=
  ∀ l ∈ L, evalLiteral σ l = true

/-- A minimum cut whose deviation set is contained in every other minimum
cut deviation set.  The executable cut construction provides this certificate. -/
structure IsLeastCut (τ : Assignment) (f : CNF) (L : List Literal) (δ : Assignment) : Prop where
  required : Requires δ L
  optimal : ∀ σ, Requires σ L → cutCost τ δ f ≤ cutCost τ σ f
  least : ∀ σ, Requires σ L → cutCost τ σ f = cutCost τ δ f →
    ∀ x, δ x ≠ τ x → σ x ≠ τ x

/-- Cut cost is a lower bound on the number of deleted occurrences. -/
theorem cutCost_le_unsatisfiedCount (τ σ : Assignment) (f : CNF) :
    cutCost τ σ f ≤ unsatisfiedCount σ f := by
  rw [unsatisfiedCount_eq_cut_add_conflict τ]
  omega

theorem leastCut_lower_bound {τ δ : Assignment} {f : CNF} {L : List Literal}
    (hδ : IsLeastCut τ f L δ) {k : ℕ} (h : AnnotatedAlmostSatisfiable f L k) :
    cutCost τ δ f ≤ k := by
  obtain ⟨σ, hσ, hL⟩ := h
  exact (hδ.optimal σ hL).trans ((cutCost_le_unsatisfiedCount τ σ f).trans hσ)

/-- A reference-true literal false in the least cut is false in every minimum
cut; requiring it therefore raises the cut optimum by at least one. -/
theorem leastCut_requirement_increases {τ δ : Assignment} {f : CNF} {L : List Literal}
    (hδ : IsLeastCut τ f L δ) {a : Literal} (hτa : evalLiteral τ a = true)
    (hδa : evalLiteral δ a = false) {σ : Assignment} (hσ : Requires σ (a :: L)) :
    cutCost τ δ f + 1 ≤ cutCost τ σ f := by
  have hL : Requires σ L := fun x hx => hσ x (by simp [hx])
  have ho := hδ.optimal σ hL
  have hne : δ a.var ≠ τ a.var := by
    intro he
    have hev : evalLiteral δ a = evalLiteral τ a := by simp [evalLiteral, he]
    rw [hδa, hτa] at hev
    cases hev
  have hn : cutCost τ σ f ≠ cutCost τ δ f := by
    intro he
    have hv := hδ.least σ hL he a.var hne
    have ha := hσ a (by simp)
    have heq : σ a.var = τ a.var := by
      rcases a with ⟨x, p⟩
      cases p <;> simp_all [evalLiteral]
    exact hv heq
  omega

/-- A reference-true conflict contributes no directed-cut edge. -/
theorem cutClause_eq_zero_of_all {τ σ : Assignment} {c : Clause}
    (hc : c.all (evalLiteral τ) = true) : cutClause τ σ c = 0 := by
  simp [cutClause, hc]

theorem cutCost_cons_conflict {τ σ : Assignment} {c : Clause} {f : CNF}
    (hc : c.all (evalLiteral τ) = true) : cutCost τ σ (c :: f) = cutCost τ σ f := by
  simp [cutCost, cutClause_eq_zero_of_all hc]

/-- Removing a conflict clause preserves the minimum cut and its leastness. -/
theorem leastCut_remove_conflict {τ δ : Assignment} {c : Clause} {f : CNF}
    {L : List Literal} (hδ : IsLeastCut τ (c :: f) L δ)
    (hc : c.all (evalLiteral τ) = true) : IsLeastCut τ f L δ := by
  refine ⟨hδ.required, ?_, ?_⟩
  · intro σ hσ
    simpa only [cutCost_cons_conflict hc] using hδ.optimal σ hσ
  · intro σ hσ he x hx
    apply hδ.least σ hσ ?_ x hx
    simpa only [cutCost_cons_conflict hc] using he

/-- The three branches are an exact reduction, with no solver hypothesis. -/
theorem annotated_cons_branches (a b : Literal) (f : CNF) (L : List Literal) (k : ℕ) :
    AnnotatedAlmostSatisfiable ([a, b] :: f) L k ↔
      (0 < k ∧ AnnotatedAlmostSatisfiable f L (k - 1)) ∨
      AnnotatedAlmostSatisfiable ([a, b] :: f) (a :: L) k ∨
      AnnotatedAlmostSatisfiable ([a, b] :: f) (b :: L) k := by
  constructor
  · rintro ⟨σ, hσ, hL⟩
    by_cases ha : evalLiteral σ a = true
    · exact Or.inr (Or.inl ⟨σ, hσ, by simpa using And.intro ha hL⟩)
    · by_cases hb : evalLiteral σ b = true
      · exact Or.inr (Or.inr ⟨σ, hσ, by simpa using And.intro hb hL⟩)
      · have ha' : evalLiteral σ a = false := by simpa using ha
        have hb' : evalLiteral σ b = false := by simpa using hb
        simp only [unsatisfiedCount_cons, evalClause, List.any_cons, List.any_nil,
          ha', hb', Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hσ
        exact Or.inl ⟨by omega, σ, by omega, hL⟩
  · rintro (⟨hk, σ, hσ, hL⟩ | ⟨σ, hσ, hL⟩ | ⟨σ, hσ, hL⟩)
    · refine ⟨σ, ?_, hL⟩
      rw [unsatisfiedCount_cons]
      split <;> omega
    · exact ⟨σ, hσ, fun x hx => hL x (by simp [hx])⟩
    · exact ⟨σ, hσ, fun x hx => hL x (by simp [hx])⟩

/-- At a violated reference-true clause, both requirement branches raise the
cut lower bound, and the deletion branch leaves it unchanged. -/
theorem leastCut_conflict_branches {τ δ : Assignment} {a b : Literal} {f : CNF}
    {L : List Literal} (hδ : IsLeastCut τ ([a, b] :: f) L δ)
    (hτa : evalLiteral τ a = true) (hτb : evalLiteral τ b = true)
    (hδc : evalClause δ [a, b] = false) :
    IsLeastCut τ f L δ ∧
      (∀ σ, Requires σ (a :: L) →
        cutCost τ δ ([a, b] :: f) + 1 ≤ cutCost τ σ ([a, b] :: f)) ∧
      (∀ σ, Requires σ (b :: L) →
        cutCost τ δ ([a, b] :: f) + 1 ≤ cutCost τ σ ([a, b] :: f)) := by
  have hc : evalLiteral δ a = false ∧ evalLiteral δ b = false := by
    simpa [evalClause] using hδc
  refine ⟨leastCut_remove_conflict hδ (by simp [hτa, hτb]), ?_, ?_⟩
  · exact fun σ hσ => leastCut_requirement_increases hδ hτa hc.1 hσ
  · exact fun σ hσ => leastCut_requirement_increases hδ hτb hc.2 hσ

end STACS2027.Runtimes.BoundedCost
