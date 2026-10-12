module

public import Runtimes.BoundedCost.NodeSemantics
import Mathlib.Tactic

/-! Dense table updates preserve literal domains and the semantic requirements
of the annotated path state. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

theorem requires_dense_force_equiv {nodes : ℕ} {forced : ℕ → Bool} {required : List Literal}
    {literal : Literal} (hl : literal.var < nodes)
    (he : ∀ σ, Requires σ (denseRequirements nodes forced) ↔ Requires σ required) :
    ∀ σ, Requires σ (denseRequirements nodes (Function.update forced (TwoSat.code literal) true)) ↔
      Requires σ (literal :: required) := by
  intro σ
  rw [requires_denseRequirements_force_literal σ nodes forced literal hl]
  simp only [Requires, List.mem_cons, forall_eq_or_imp]
  change (evalLiteral σ literal = true ∧ Requires σ (denseRequirements nodes forced)) ↔
    (evalLiteral σ literal = true ∧ Requires σ required)
  exact and_congr_right (fun _ => he σ)

theorem decodedBits_upd (memory : ℕ → ℕ) (base code value : ℕ) :
    (fun u => upd memory (base + code) value (base + u) == 1) =
      Function.update (fun u => memory (base + u) == 1) code (value == 1) := by
  funext u
  by_cases he : u = code
  · subst u
    simp [upd_apply]
  · have haddr : base + u ≠ base + code := by omega
    simp [upd_apply, he, haddr, Function.update]

theorem disableOccurrence_clause_mem {rows : List (Bool × Clause)} (i : ℕ)
    {active : Bool} {clause : Clause} (hc : (active, clause) ∈ disableOccurrence rows i) :
    ∃ old, (old, clause) ∈ rows := by
  induction rows generalizing i with
  | nil => simp [disableOccurrence] at hc
  | cons row rows ih =>
    rcases row with ⟨bit, head⟩
    cases i with
    | zero =>
      rcases List.mem_cons.mp hc with he | ht
      · have hclause : clause = head := (Prod.mk.inj he).2
        subst clause
        exact ⟨bit, by simp⟩
      · exact ⟨active, by simp [ht]⟩
    | succ i =>
      rcases List.mem_cons.mp hc with he | ht
      · have hclause : clause = head := (Prod.mk.inj he).2
        subst clause
        exact ⟨bit, by simp⟩
      · obtain ⟨old, ho⟩ := ih i ht
        exact ⟨old, by simp [ho]⟩

theorem disableOccurrence_domain {nodes : ℕ} {rows : List (Bool × Clause)}
    (hrows : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < nodes) (i : ℕ) :
    ∀ row ∈ disableOccurrence rows i, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < nodes := by
  rintro ⟨active, clause⟩ hc
  obtain ⟨old, ho⟩ := disableOccurrence_clause_mem i hc
  exact hrows (old, clause) ho

end STACS2027.Runtimes.BoundedCost
