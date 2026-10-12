module

public import Runtimes.BoundedCost.LeastCutRAM
public import Runtimes.BoundedCost.OccurrenceTables
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

def SearchNodeMemoryFrame (span active candidate forced labels output n m a : ℕ) : Prop :=
  LeastCutFrame span candidate labels output n m a ∧
    OutsideCells active m a ∧ OutsideCells forced (2 * n) a

theorem nodeActionMemory_outside {active forced n m a : ℕ} {memory : ℕ → ℕ}
    {summary : SearchSummary} {budget choice : ℕ}
    (hc : summary.conflict ≤ m) (hf : summary.firstLiteral < 2 * n)
    (hs : summary.secondLiteral < 2 * n)
    (ha : OutsideCells active m a) (hforced : OutsideCells forced (2 * n) a) :
    nodeActionMemory (nodeAction summary budget choice) active forced memory a = memory a := by
  by_cases hsat : summary.unsatisfied ≤ budget
  · simp [nodeAction, nodeActionMemory, hsat]
  by_cases hbudget : budget < summary.cut
  · simp [nodeAction, nodeActionMemory, hsat, hbudget]
  by_cases hconflict : summary.conflict = 0
  · simp [nodeAction, nodeActionMemory, hsat, hbudget, hconflict]
  by_cases hzero : choice = 0
  · by_cases hk : budget = 0
    · have hunsat : summary.unsatisfied ≠ 0 := by omega
      simp [nodeAction, nodeActionMemory, hsat, hbudget, hconflict, hzero, hk, hunsat]
    · have hne : a ≠ active + (summary.conflict - 1) := by unfold OutsideCells at ha; omega
      simp [nodeAction, nodeActionMemory, hsat, hbudget, hconflict, hzero, hk, hne]
  by_cases hone : choice = 1
  · have hne : a ≠ forced + summary.firstLiteral := by unfold OutsideCells at hforced; omega
    simp [nodeAction, nodeActionMemory, hsat, hbudget, hconflict, hzero, hone, hne]
  by_cases htwo : choice = 2
  · have hne : a ≠ forced + summary.secondLiteral := by unfold OutsideCells at hforced; omega
    simp [nodeAction, nodeActionMemory, hsat, hbudget, hconflict, hzero, hone, htwo, hne]
  · simp [nodeAction, nodeActionMemory, hsat, hbudget, hconflict, hzero, hone, htwo]

theorem LeastCutGeometry.frame_input {S span formula active candidate reference forced labels output n m a : ℕ}
    (h : LeastCutGeometry S span formula active candidate reference forced labels output n m)
    (ha : (formula ≤ a ∧ a < formula + 2 * m) ∨ (active ≤ a ∧ a < active + m) ∨
      (reference ≤ a ∧ a < reference + 2 * n) ∨ (forced ≤ a ∧ a < forced + 2 * n)) :
    LeastCutFrame span candidate labels output n m a := by
  obtain ⟨hh, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := h
  unfold LeastCutFrame OutsideCells
  rcases ha with ha | ha | ha | ha <;> omega

theorem Arr.leastCutFrame {S span formula active candidate reference forced labels output n m : ℕ}
    {memory next : ℕ → ℕ} {values : List ℕ}
    (hgeo : LeastCutGeometry S span formula active candidate reference forced labels output n m)
    (hframe : SameOn (LeastCutFrame span candidate labels output n m) memory next)
    (hlen : values.length ≤ 2 * m) (h : Arr memory formula values) : Arr next formula values := by
  intro i hi
  exact (hframe _ (hgeo.frame_input (Or.inl (by omega)))).trans (h i hi)

theorem MaskTable.leastCutFrame {S span formula active candidate reference forced labels output n : ℕ}
    {memory next : ℕ → ℕ} {rows : List (Bool × Clause)}
    (hgeo : LeastCutGeometry S span formula active candidate reference forced labels output n rows.length)
    (hframe : SameOn (LeastCutFrame span candidate labels output n rows.length) memory next)
    (h : MaskTable memory active rows) : MaskTable next active rows := by
  intro i hi
  exact (hframe _ (hgeo.frame_input (Or.inr (Or.inl (by omega))))).trans (h i hi)

theorem ForcedTable.leastCutFrame {S span formula active candidate reference forced labels output n m : ℕ}
    {memory next : ℕ → ℕ} {bits : ℕ → Bool}
    (hgeo : LeastCutGeometry S span formula active candidate reference forced labels output n m)
    (hframe : SameOn (LeastCutFrame span candidate labels output n m) memory next)
    (h : ForcedTable memory forced n bits) : ForcedTable next forced n bits := by
  intro i hi
  exact (hframe _ (hgeo.frame_input (Or.inr (Or.inr (Or.inr (by omega)))))).trans (h i hi)

theorem TruthTable.leastCutFrame {S span formula active candidate reference forced labels output n m : ℕ}
    {memory next : ℕ → ℕ} {σ : Assignment}
    (hgeo : LeastCutGeometry S span formula active candidate reference forced labels output n m)
    (hframe : SameOn (LeastCutFrame span candidate labels output n m) memory next)
    (h : TruthTable memory reference n σ) : TruthTable next reference n σ := by
  intro i hi
  exact (hframe _ (hgeo.frame_input (Or.inr (Or.inr (Or.inl (by omega)))))).trans (h i hi)

end STACS2027.Runtimes.BoundedCost
