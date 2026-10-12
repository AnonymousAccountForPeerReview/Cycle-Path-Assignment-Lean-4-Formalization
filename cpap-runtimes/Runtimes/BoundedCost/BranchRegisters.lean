module

public import Runtimes.BoundedCost.TernaryControl
import Mathlib.Tactic

/-! Disjoint physical controls for the nested ternary enumerations. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027.RAM STACS2027.RAM.P3

def innerRegisterSwap (r : ℕ) : ℕ :=
  if 132 ≤ r ∧ r < 182 then r + 400
  else if 532 ≤ r ∧ r < 582 then r - 400 else r

theorem innerRegisterSwap_involutive : Function.Involutive innerRegisterSwap := by
  intro r
  by_cases hlo : 132 ≤ r ∧ r < 182
  · have hhi : 532 ≤ r + 400 ∧ r + 400 < 582 := by omega
    have hn : ¬(132 ≤ r + 400 ∧ r + 400 < 182) := by omega
    simp [innerRegisterSwap, hlo, hhi, hn]
  · by_cases hhi : 532 ≤ r ∧ r < 582
    · have hl : 132 ≤ r - 400 ∧ r - 400 < 182 := by omega
      simp [innerRegisterSwap, hlo, hhi, hl]; omega
    · simp [innerRegisterSwap, hlo, hhi]

theorem innerRegisterSwap_injective : Function.Injective innerRegisterSwap :=
  innerRegisterSwap_involutive.injective

def innerCallerRegister (r : ℕ) : ℕ := callerRegister (innerRegisterSwap r)

theorem innerCallerRegister_injective : Function.Injective innerCallerRegister :=
  callerRegister_injective.comp innerRegisterSwap_injective

theorem innerCallerRegister_outside {r : ℕ}
    (hlo : r < 132 ∨ 182 ≤ r) (hhi : r < 532 ∨ 582 ≤ r) :
    innerCallerRegister r = callerRegister r := by
  have hl : ¬(132 ≤ r ∧ r < 182) := by omega
  have hh : ¬(532 ≤ r ∧ r < 582) := by omega
  simp [innerCallerRegister, innerRegisterSwap, hl, hh]

@[simp] theorem innerCallerRegister_base : innerCallerRegister rOB = callerRegister 532 := rfl
@[simp] theorem innerCallerRegister_depth : innerCallerRegister rOL = callerRegister 533 := rfl
@[simp] theorem innerCallerRegister_index : innerCallerRegister wordIndex = callerRegister 580 := rfl
@[simp] theorem innerCallerRegister_count : innerCallerRegister wordCount = callerRegister 581 := rfl
@[simp] theorem innerCallerRegister_radix : innerCallerRegister rK = callerRegister rK := rfl

theorem innerCallerRegister_ne_temporary {r : ℕ} (hr : r ≠ 0) :
    innerCallerRegister r ≠ rT := by
  intro he
  change 4 * innerRegisterSwap r + 3 = 3 at he
  have hz' : innerRegisterSwap r = 0 := by omega
  have hz : innerRegisterSwap r = innerRegisterSwap 0 := by
    exact hz'.trans (by decide)
  exact hr (innerRegisterSwap_injective hz)

end STACS2027.Runtimes.BoundedCost
