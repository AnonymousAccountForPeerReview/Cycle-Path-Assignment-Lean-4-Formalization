module

public import Runtimes.BoundedCost.SearchSemantics
public import Runtimes.BoundedCost.ContractionRAM
public import Runtimes.BoundedCost.DenseTables
import Mathlib.Tactic

/-! The same concrete occurrence and dual-literal tables supply both the cut
builder and the annotated node scanner. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

def ForcedTable (memory : ℕ → ℕ) (base n : ℕ) (forced : ℕ → Bool) : Prop :=
  ∀ u, u < 2 * n → memory (base + u) = (if forced u then 1 else 0)

theorem terminalRowsMem_of_tables {n forcedBase reference : ℕ} {memory : ℕ → ℕ}
    {τ : Assignment} {forced : ℕ → Bool}
    (hf : ForcedTable memory forcedBase n forced)
    (hr : TruthTable memory reference n τ) :
    TerminalRowsMem forcedBase reference (terminalRowsOf n τ forced) memory := by
  intro x hx
  rw [terminalRowsOf_length] at hx
  rw [terminalRowsOf_getD n τ forced x hx]
  exact ⟨hf (2 * x) (by omega), by simpa only [Nat.add_assoc] using hf (2 * x + 1) (by omega),
    truthTable_positive hr x hx⟩

theorem searchRowsMem_of_contraction {n formula active candidate reference : ℕ}
    {memory : ℕ → ℕ} {τ δ : Assignment} {rows : List (Bool × Clause)}
    (hrows : ∀ row ∈ rows, row.2.length = 2)
    (hc : ContractionRowsMem formula active reference n (contractionRowsOf τ rows) memory)
    (ht : TruthTable memory candidate n δ) :
    SearchRowsMem formula active candidate reference (2 * n) (searchRowsOf τ δ rows) memory := by
  intro i hi
  rw [searchRowsOf_length] at hi
  have hm := hc i (by simpa [contractionRowsOf] using hi)
  rcases he : rows[i] with ⟨selected, clause⟩
  have hclause := hrows rows[i] (List.getElem_mem hi)
  rw [he] at hclause
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hclause
  change clause = [a, b] at hab
  subst clause
  have hget : rows.getD i default = (selected, [a, b]) := by
    rw [← List.getElem_eq_getD (h := hi) default, he]
  have hcontract : (contractionRowsOf τ rows).getD i default =
      contractionRowOf τ (selected, [a, b]) := by
    simp [contractionRowsOf, List.getD_eq_getElem?_getD, hi, he]
  rw [hcontract] at hm
  change TwoSat.code a < 2 * n ∧ TwoSat.code b < 2 * n ∧
    memory (formula + 2 * i) = TwoSat.code a ∧ memory (formula + 2 * i + 1) = TwoSat.code b ∧
    memory (active + i) = (if selected then 1 else 0) ∧
    memory (reference + TwoSat.code a) = (if evalLiteral τ a then 1 else 0) ∧
    memory (reference + TwoSat.code b) = (if evalLiteral τ b then 1 else 0) at hm
  rw [searchRowsOf_getD τ δ rows i hi, hget]
  dsimp [searchRowOf]
  refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, ?_, ?_,
    hm.2.2.2.2.2.1, hm.2.2.2.2.2.2⟩
  · simpa only [TwoSat.nodeVal_code] using ht (TwoSat.code a) hm.1
  · simpa only [TwoSat.nodeVal_code] using ht (TwoSat.code b) hm.2.1

end STACS2027.Runtimes.BoundedCost
