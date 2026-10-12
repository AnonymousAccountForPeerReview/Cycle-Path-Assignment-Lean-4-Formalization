module

public import Runtimes.BoundedCost.Branching
import Mathlib.Tactic

/-!
# The variable cut graph of a satisfiable two-literal formula

Each clause with exactly one reference-true literal contributes one directed
arc occurrence.  Clauses with two reference-true literals contribute none.
The source side of a cut records variables kept at their reference values.
The cut cardinality is exactly the directed-cut part of the deletion cost.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

/-- Source side of the cut: agreement with the reference assignment. -/
def agreementRegion (τ σ : Assignment) (x : ℕ) : Bool := decide (σ x = τ x)

theorem agreementRegion_literal (τ σ : Assignment) (l : Literal) :
    agreementRegion τ σ l.var = decide (evalLiteral σ l = evalLiteral τ l) := by
  rcases l with ⟨x, p⟩
  cases p <;> cases ht : τ x <;> cases hs : σ x <;>
    simp [agreementRegion, evalLiteral, ht, hs]

/-- Decode a variable cut: keep reference values inside, complement outside. -/
def assignmentOfRegion (τ : Assignment) (region : ℕ → Bool) : Assignment :=
  fun x => if region x then τ x else !(τ x)

@[simp] theorem agreementRegion_assignmentOfRegion (τ : Assignment) (region : ℕ → Bool) :
    agreementRegion τ (assignmentOfRegion τ region) = region := by
  funext x
  cases hr : region x <;> cases ht : τ x <;>
    simp [agreementRegion, assignmentOfRegion, hr, ht]

@[simp] theorem assignmentOfRegion_agreementRegion (τ σ : Assignment) :
    assignmentOfRegion τ (agreementRegion τ σ) = σ := by
  funext x
  cases ht : τ x <;> cases hs : σ x <;>
    simp [agreementRegion, assignmentOfRegion, ht, hs]

/-- The possible single arc occurrence contributed by a clause. -/
def clauseCutArcs (τ : Assignment) : Clause → List (ℕ × ℕ)
  | [a, b] =>
      if evalLiteral τ a = false then [(a.var, b.var)]
      else if evalLiteral τ b = false then [(b.var, a.var)] else []
  | _ => []

/-- Arc occurrences in formula order, preserving repeated clauses. -/
def variableCutArcs (τ : Assignment) (f : CNF) : List (ℕ × ℕ) :=
  f.flatMap (clauseCutArcs τ)

/-- A unit arc crosses the cut precisely from reference agreement to deviation. -/
def variableArcCut (region : ℕ → Bool) (e : ℕ × ℕ) : ℕ :=
  if region e.1 && !(region e.2) then 1 else 0

/-- Cardinality of a directed cut, counting each arc occurrence. -/
def variableCutSize (arcs : List (ℕ × ℕ)) (region : ℕ → Bool) : ℕ :=
  (arcs.map (variableArcCut region)).sum

theorem cutClause_eq_variableArcCut (τ σ : Assignment) (a b : Literal)
    (hτ : evalClause τ [a, b] = true) :
    cutClause τ σ [a, b] =
      variableCutSize (clauseCutArcs τ [a, b]) (agreementRegion τ σ) := by
  simp only [cutClause, evalClause, List.any_cons, List.any_nil, Bool.or_false,
    List.all_cons, List.all_nil, Bool.and_true, clauseCutArcs,
    variableCutSize, variableArcCut, agreementRegion_literal] at hτ ⊢
  cases hta : evalLiteral τ a <;> cases htb : evalLiteral τ b <;>
    cases hsa : evalLiteral σ a <;> cases hsb : evalLiteral σ b <;>
    simp_all [variableArcCut, agreementRegion_literal]

/-- Exact correspondence between formula cut cost and directed graph cut size. -/
theorem cutCost_eq_variableCutSize {f : CNF} (hf : Clauses2 f) {τ : Assignment}
    (hτ : evalCNF τ f = true) (σ : Assignment) :
    cutCost τ σ f = variableCutSize (variableCutArcs τ f) (agreementRegion τ σ) := by
  induction f with
  | nil => simp [cutCost, variableCutSize, variableCutArcs]
  | cons c f ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf c (by simp))
    rw [evalCNF_cons, Bool.and_eq_true] at hτ
    have hc := cutClause_eq_variableArcCut τ σ a b hτ.1
    have ht := ih (fun c hc => hf c (by simp [hc])) hτ.2
    simp only [cutCost, variableCutArcs, variableCutSize, List.map_cons,
      List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append] at hc ht ⊢
    omega

theorem variableCutArcs_length_le (τ : Assignment) (f : CNF) :
    (variableCutArcs τ f).length ≤ f.length := by
  induction f with
  | nil => simp [variableCutArcs]
  | cons c f ih =>
    have hc : (clauseCutArcs τ c).length ≤ 1 := by
      cases c with
      | nil => simp [clauseCutArcs]
      | cons a c =>
        cases c with
        | nil => simp [clauseCutArcs]
        | cons b c =>
          cases c with
          | nil =>
            simp only [clauseCutArcs]
            split
            · simp
            · split <;> simp
          | cons d c => simp [clauseCutArcs]
    simp only [variableCutArcs, List.flatMap_cons, List.length_append,
      List.length_cons] at ih ⊢
    omega

theorem variableCutArcs_endpoints {n : ℕ} {f : CNF} (hf : TwoSat.IsTwoCNF n f)
    (τ : Assignment) : ∀ e ∈ variableCutArcs τ f, e.1 < n ∧ e.2 < n := by
  intro e he
  obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp he
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf c hc).1
  have ha := (hf [a, b] hc).2 a (by simp)
  have hb := (hf [a, b] hc).2 b (by simp)
  simp only [clauseCutArcs] at he
  split at he
  · simp only [List.mem_singleton] at he
    subst e
    exact ⟨ha, hb⟩
  · split at he
    · simp only [List.mem_singleton] at he
      subst e
      exact ⟨hb, ha⟩
    · simp at he

/-- Literal requirements become source or sink membership constraints on variables. -/
theorem requires_iff_agreementRegion (τ σ : Assignment) (L : List Literal) :
    Requires σ L ↔
      ∀ l ∈ L, agreementRegion τ σ l.var = evalLiteral τ l := by
  unfold Requires
  constructor <;> intro h l hl
  · rw [agreementRegion_literal]
    cases ht : evalLiteral τ l <;> simp [h l hl, ht]
  · have hs := h l hl
    rw [agreementRegion_literal] at hs
    cases ht : evalLiteral τ l <;> cases hv : evalLiteral σ l <;> simp_all

end STACS2027.Runtimes.BoundedCost
