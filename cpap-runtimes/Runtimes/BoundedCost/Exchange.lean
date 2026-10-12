module

public import Runtimes.BoundedCost.Annotated
import Mathlib.Tactic

/-!
# Neutral-literal exchange by cut submodularity

Relative to an assignment satisfying a two-literal formula, every clause has
one or two true literals.  A clause with one true literal gives a directed-cut
cost.  A clause with two true literals gives a cost that can only decrease
when the set of variables changed from that assignment shrinks.  This proves
the neutral-literal exchange used by the cited [RO09] search algorithm.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

/-- Intersection of the variables changed from the reference assignment. -/
def meetAssignment (τ σ δ : Assignment) : Assignment :=
  fun x => if σ x = τ x then τ x else δ x

/-- Union of the variables changed from the reference assignment. -/
def joinAssignment (τ σ δ : Assignment) : Assignment :=
  fun x => if σ x = τ x then δ x else σ x

theorem evalLiteral_meetAssignment (τ σ δ : Assignment) (l : Literal) :
    evalLiteral (meetAssignment τ σ δ) l =
      if evalLiteral σ l = evalLiteral τ l then evalLiteral τ l else evalLiteral δ l := by
  rcases l with ⟨x, p⟩
  cases p <;> cases ht : τ x <;> cases hs : σ x <;> cases hd : δ x <;>
    simp [evalLiteral, meetAssignment, ht, hs, hd]

theorem evalLiteral_joinAssignment (τ σ δ : Assignment) (l : Literal) :
    evalLiteral (joinAssignment τ σ δ) l =
      if evalLiteral σ l = evalLiteral τ l then evalLiteral δ l else evalLiteral σ l := by
  rcases l with ⟨x, p⟩
  cases p <;> cases ht : τ x <;> cases hs : σ x <;> cases hd : δ x <;>
    simp [evalLiteral, joinAssignment, ht, hs, hd]

/-- Required literals shared by both assignments remain true in their meet
and join, regardless of the reference assignment. -/
theorem meet_join_preserve_required {τ σ δ : Assignment} {l : Literal}
    (hσ : evalLiteral σ l = true) (hδ : evalLiteral δ l = true) :
    evalLiteral (meetAssignment τ σ δ) l = true ∧
      evalLiteral (joinAssignment τ σ δ) l = true := by
  rw [evalLiteral_meetAssignment, evalLiteral_joinAssignment]
  cases ht : evalLiteral τ l <;> simp [ht, hσ, hδ]

/-- If the reference and second assignment agree on a required literal, the
meet obeys that requirement even when the first assignment does not. -/
theorem meet_preserve_reference {τ σ δ : Assignment} {l : Literal}
    (hτ : evalLiteral τ l = true) (hδ : evalLiteral δ l = true) :
    evalLiteral (meetAssignment τ σ δ) l = true := by
  rw [evalLiteral_meetAssignment]
  simp only [hτ, hδ]
  split <;> rfl

/-- The directed-cut contribution of a clause relative to the reference. -/
def cutClause (τ σ : Assignment) (c : Clause) : ℕ :=
  if !(evalClause σ c) && !(c.all (evalLiteral τ)) then 1 else 0

/-- The contribution of a clause whose two reference literals are true. -/
def conflictClause (τ σ : Assignment) (c : Clause) : ℕ :=
  if !(evalClause σ c) && c.all (evalLiteral τ) then 1 else 0

/-- Sum of the directed-cut contributions, with clause multiplicities. -/
def cutCost (τ σ : Assignment) (f : CNF) : ℕ := (f.map (cutClause τ σ)).sum

/-- Sum of the reference-true conflict contributions. -/
def conflictCost (τ σ : Assignment) (f : CNF) : ℕ :=
  (f.map (conflictClause τ σ)).sum

theorem unsatisfiedCount_eq_cut_add_conflict (τ σ : Assignment) (f : CNF) :
    unsatisfiedCount σ f = cutCost τ σ f + conflictCost τ σ f := by
  induction f with
  | nil => simp [cutCost, conflictCost]
  | cons c f ih =>
    rw [unsatisfiedCount_cons]
    simp only [cutCost, conflictCost, List.map_cons, List.sum_cons] at ih ⊢
    cases he : evalClause σ c <;> cases ha : c.all (evalLiteral τ) <;>
      simp [cutClause, conflictClause, he, ha] <;> omega

/-- A satisfied two-literal clause gives a submodular directed-cut cost. -/
theorem cutClause_submodular (τ σ δ : Assignment) (a b : Literal)
    (hτ : evalClause τ [a, b] = true) :
    cutClause τ (meetAssignment τ σ δ) [a, b] +
        cutClause τ (joinAssignment τ σ δ) [a, b] ≤
      cutClause τ σ [a, b] + cutClause τ δ [a, b] := by
  simp only [cutClause, evalClause, List.any_cons, List.any_nil, Bool.or_false,
    List.all_cons, List.all_nil, Bool.and_true, evalLiteral_meetAssignment,
    evalLiteral_joinAssignment] at hτ ⊢
  cases hta : evalLiteral τ a <;> cases htb : evalLiteral τ b <;>
    cases hsa : evalLiteral σ a <;> cases hsb : evalLiteral σ b <;>
    cases hda : evalLiteral δ a <;> cases hdb : evalLiteral δ b <;>
    simp_all

/-- Reference-true conflicts cannot increase when deviations are intersected. -/
theorem conflictClause_meet_le (τ σ δ : Assignment) (a b : Literal) :
    conflictClause τ (meetAssignment τ σ δ) [a, b] ≤ conflictClause τ σ [a, b] := by
  simp only [conflictClause, evalClause, List.any_cons, List.any_nil, Bool.or_false,
    List.all_cons, List.all_nil, Bool.and_true, evalLiteral_meetAssignment]
  cases hta : evalLiteral τ a <;> cases htb : evalLiteral τ b <;>
    cases hsa : evalLiteral σ a <;> cases hsb : evalLiteral σ b <;>
    cases hda : evalLiteral δ a <;> cases hdb : evalLiteral δ b <;>
    simp_all

theorem cutCost_submodular {f : CNF} (hf : Clauses2 f) {τ σ δ : Assignment}
    (hτ : evalCNF τ f = true) :
    cutCost τ (meetAssignment τ σ δ) f + cutCost τ (joinAssignment τ σ δ) f ≤
      cutCost τ σ f + cutCost τ δ f := by
  induction f with
  | nil => simp [cutCost]
  | cons c f ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf c (by simp))
    rw [evalCNF_cons, Bool.and_eq_true] at hτ
    have hc := cutClause_submodular τ σ δ a b hτ.1
    have ht := ih (fun c hc => hf c (by simp [hc])) hτ.2
    simp only [cutCost, List.map_cons, List.sum_cons] at ht ⊢
    omega

theorem conflictCost_meet_le {f : CNF} (hf : Clauses2 f) (τ σ δ : Assignment) :
    conflictCost τ (meetAssignment τ σ δ) f ≤ conflictCost τ σ f := by
  induction f with
  | nil => simp [conflictCost]
  | cons c f ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf c (by simp))
    have hc := conflictClause_meet_le τ σ δ a b
    have ht := ih (fun c hc => hf c (by simp [hc]))
    simp only [conflictCost, List.map_cons, List.sum_cons] at ht ⊢
    omega

/-- Neutral-literal exchange: `δ` satisfies the extended requirements and is
a minimum cut even among assignments satisfying only the original ones.
Intersecting deviations therefore preserves every deletion budget. -/
theorem annotated_neutral_exchange {f : CNF} (hf : Clauses2 f)
    {L : List Literal} {l : Literal} {τ δ : Assignment}
    (hτ : evalCNF τ f = true) (hτl : evalLiteral τ l = true)
    (hδ : ∀ x ∈ l :: L, evalLiteral δ x = true)
    (hmin : ∀ σ : Assignment, (∀ x ∈ L, evalLiteral σ x = true) →
      cutCost τ δ f ≤ cutCost τ σ f) {k : ℕ}
    (hsol : AnnotatedAlmostSatisfiable f L k) :
    AnnotatedAlmostSatisfiable f (l :: L) k := by
  obtain ⟨σ, hσ, hL⟩ := hsol
  have hjoin : ∀ x ∈ L, evalLiteral (joinAssignment τ σ δ) x = true := by
    intro x hx
    exact (meet_join_preserve_required (hL x hx) (hδ x (by simp [hx]))).2
  have hcut := cutCost_submodular hf hτ (σ := σ) (δ := δ)
  have hminimum := hmin (joinAssignment τ σ δ) hjoin
  have hpenalty := conflictCost_meet_le hf τ σ δ
  refine ⟨meetAssignment τ σ δ, ?_, ?_⟩
  · rw [unsatisfiedCount_eq_cut_add_conflict τ] at hσ ⊢
    omega
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact meet_preserve_reference hτl (hδ x (by simp))
    · exact (meet_join_preserve_required (hL x hx) (hδ x (by simp [hx]))).1

end STACS2027.Runtimes.BoundedCost
