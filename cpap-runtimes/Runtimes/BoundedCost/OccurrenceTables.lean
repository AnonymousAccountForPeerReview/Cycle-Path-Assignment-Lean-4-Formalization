module

public import Runtimes.BoundedCost.SearchMemory
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

def MaskTable (memory : ℕ → ℕ) (active : ℕ) (rows : List (Bool × Clause)) : Prop :=
  ∀ i, (hi : i < rows.length) → memory (active + i) = if rows[i].1 then 1 else 0

theorem contractionRowsMem_of_tables {n formula active reference : ℕ}
    {memory : ℕ → ℕ} {rows : List (Bool × Clause)} {τ : Assignment}
    (hrows : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < n)
    (hcodes : Arr memory formula (TwoSat.codes (rows.map Prod.snd)))
    (hmask : MaskTable memory active rows) (htruth : TruthTable memory reference n τ) :
    ContractionRowsMem formula active reference n (contractionRowsOf τ rows) memory := by
  have hf : TwoSat.IsTwoCNF n (rows.map Prod.snd) := by
    intro c hc
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hc
    exact hrows row hr
  intro i hi
  have hi' : i < rows.length := by simpa [contractionRowsOf] using hi
  obtain ⟨a, b, hpair, ha, hb, hx, hy⟩ := codes_clause_pair hf i (by simpa using hi')
  have hrowPair : rows[i].2 = [a, b] := by simpa using hpair
  have hrow : rows[i] = (rows[i].1, [a, b]) := Prod.ext rfl hrowPair
  have hget : (contractionRowsOf τ rows).getD i default =
      contractionRowOf τ (rows[i].1, [a, b]) := by
    have hget' : (contractionRowsOf τ rows).getD i default = contractionRowOf τ rows[i] := by
      simp [contractionRowsOf, List.getD_eq_getElem?_getD, hi']
    exact hget'.trans (congrArg (contractionRowOf τ) hrow)
  rw [hget]
  dsimp [contractionRowOf]
  have hlength := TwoSat.length_codes hf
  refine ⟨TwoSat.code_lt ha, TwoSat.code_lt hb, ?_, ?_, hmask i hi', ?_, ?_⟩
  · exact (hcodes.getD (i := 2 * i) (by rw [hlength]; simp; omega)).trans hx
  · have h := (hcodes.getD (i := 2 * i + 1) (by rw [hlength]; simp; omega)).trans hy
    simpa only [Nat.add_assoc] using h
  · simpa only [TwoSat.nodeVal_code] using htruth (TwoSat.code a) (TwoSat.code_lt ha)
  · simpa only [TwoSat.nodeVal_code] using htruth (TwoSat.code b) (TwoSat.code_lt hb)

theorem disableOccurrence_getElem {α : Type*} (rows : List (Bool × α)) (j i : ℕ)
    (hi : i < rows.length) :
    (disableOccurrence rows j)[i]'(by rw [disableOccurrence_length]; exact hi) =
      if i = j then (false, rows[i].2) else rows[i] := by
  induction rows generalizing i j with
  | nil => simp at hi
  | cons row rows ih =>
    cases i with
    | zero => cases j <;> simp [disableOccurrence]
    | succ i =>
      have hi' : i < rows.length := by simpa using hi
      cases j with
      | zero => simp [disableOccurrence]
      | succ j => simpa [disableOccurrence] using ih j i hi'

theorem disableOccurrence_clauses {α : Type*} (rows : List (Bool × α)) (j : ℕ) :
    (disableOccurrence rows j).map Prod.snd = rows.map Prod.snd := by
  induction rows generalizing j with
  | nil => rfl
  | cons row rows ih => cases j <;> simp [disableOccurrence, ih]

theorem MaskTable.disable {memory : ℕ → ℕ} {active : ℕ} {rows : List (Bool × Clause)}
    (h : MaskTable memory active rows) (j : ℕ) :
    MaskTable (upd memory (active + j) 0) active (disableOccurrence rows j) := by
  intro i hi
  have hi' : i < rows.length := by rwa [disableOccurrence_length] at hi
  rw [disableOccurrence_getElem rows j i hi']
  by_cases hij : i = j
  · simp [hij]
  · have hne : active + i ≠ active + j := by omega
    simpa only [hij, ite_false, upd_apply, hne] using h i hi'

theorem ForcedTable.force {memory : ℕ → ℕ} {base n : ℕ} {forced : ℕ → Bool}
    (h : ForcedTable memory base n forced) (u : ℕ) :
    ForcedTable (upd memory (base + u) 1) base n (Function.update forced u true) := by
  intro v hv
  by_cases hvu : v = u
  · simp [hvu]
  · have hne : base + v ≠ base + u := by omega
    simpa only [Function.update_of_ne hvu, upd_apply, hne, ite_false] using h v hv

theorem requires_dense_force_congr {n : ℕ} {forced : ℕ → Bool} {L : List Literal}
    (hL : ∀ σ, Requires σ (denseRequirements n forced) ↔ Requires σ L)
    (l : Literal) (hl : l.var < n) (σ : Assignment) :
    Requires σ (denseRequirements n (Function.update forced (TwoSat.code l) true)) ↔
      Requires σ (l :: L) := by
  rw [requires_denseRequirements_force_literal σ n forced l hl]
  simp only [Requires, List.mem_cons, forall_eq_or_imp] at ⊢
  exact and_congr Iff.rfl (hL σ)

theorem MaskTable.upd_outside {memory : ℕ → ℕ} {active a value : ℕ}
    {rows : List (Bool × Clause)} (h : MaskTable memory active rows)
    (ha : a < active ∨ active + rows.length ≤ a) : MaskTable (upd memory a value) active rows := by
  intro i hi
  have hne : active + i ≠ a := by omega
  simpa only [upd_apply, hne, ite_false] using h i hi

theorem ForcedTable.upd_outside {memory : ℕ → ℕ} {base n a value : ℕ} {forced : ℕ → Bool}
    (h : ForcedTable memory base n forced) (ha : a < base ∨ base + 2 * n ≤ a) :
    ForcedTable (upd memory a value) base n forced := by
  intro u hu
  have hne : base + u ≠ a := by omega
  simpa only [upd_apply, hne, ite_false] using h u hu

theorem TruthTable.upd_outside {memory : ℕ → ℕ} {base n a value : ℕ} {σ : Assignment}
    (h : TruthTable memory base n σ) (ha : a < base ∨ base + 2 * n ≤ a) :
    TruthTable (upd memory a value) base n σ := by
  intro u hu
  have hne : base + u ≠ a := by omega
  simpa only [upd_apply, hne, ite_false] using h u hu

end STACS2027.Runtimes.BoundedCost
