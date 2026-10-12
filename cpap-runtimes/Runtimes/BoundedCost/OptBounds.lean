module

public import Runtimes.BoundedCost.OptStep
public import Runtimes.BoundedCost.OptGeometric
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptBounds

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost

set_option maxHeartbeats 1000000

def uniformConstant (C w : ℕ) : ℕ := 50000 * (C + 1) * (1151 + w)

def totalTime (component : Stmt) (C : ℕ) (g : Graph) (k P : ℕ) : ℕ :=
  100 * (k * (cycles g k).length + 1) + 7 +
    (∑ p ∈ Finset.range (P + 1), (OptStep.cost component C g k p + 1)) +
    12 * (OptCall.bound C g k P + 1) + 1

theorem paper_positive (g : Graph) (k P : ℕ) : 1 ≤ paper5 g k P := by unfold paper5; omega

theorem incidence_le_paper (g : Graph) {k : ℕ} (hk : 3 ≤ k) (P : ℕ) :
    k * (cycles g k).length + 1 ≤ paper5 g k P := by
  have hkk : k ≤ k * k := by nlinarith
  have hmul := Nat.mul_le_mul_right (cycles g k).length hkk
  unfold paper5
  omega

theorem bound_succ_le_paper (g : Graph) {k : ℕ} (hk : 3 ≤ k) (C P : ℕ) :
    OptCall.bound C g k P + 1 ≤ 17 * (C + 1) * paper5 g k P := by
  have hspan := OptSpanRAM.span_le_paper g hk C P
  have hpaper := paper_positive g k P
  change OptSpanRAM.span C k (cycles g k).length P + 1 ≤ _
  nlinarith

theorem totalTime_le {component : Stmt} {C : ℕ} (g : Graph) {k : ℕ} (hk : 3 ≤ k)
    (ht : 1 ≤ (cycles g k).length) (P : ℕ) :
    totalTime component C g k P ≤ uniformConstant C (wregs component).length * paper5 g k P := by
  have hsum : (∑ p ∈ Finset.range (P + 1), (OptStep.cost component C g k p + 1)) ≤
      (1151 + (wregs component).length) *
        (∑ p ∈ Finset.range (P + 1), (OptCall.bound C g k p + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    unfold OptStep.cost
    nlinarith
  have hgeom := OptSpanRAM.span_sum_le hk ht C P
  change (∑ p ∈ Finset.range (P + 1), (OptCall.bound C g k p + 1)) ≤
    6 * (OptCall.bound C g k P + 1) at hgeom
  have hsum' := hsum.trans (Nat.mul_le_mul_left (1151 + (wregs component).length) hgeom)
  have hb := bound_succ_le_paper g hk C P
  have hi := incidence_le_paper g hk P
  have hp := paper_positive g k P
  have hcoef : 6 * (1151 + (wregs component).length) + 12 ≤
      7 * (1151 + (wregs component).length) := by omega
  have htotal : totalTime component C g k P ≤
      100 * paper5 g k P + 8 +
        (6 * (1151 + (wregs component).length) + 12) * (OptCall.bound C g k P + 1) := by
    unfold totalTime
    nlinarith only [hsum', hi]
  calc
    _ ≤ 100 * paper5 g k P + 8 +
        (6 * (1151 + (wregs component).length) + 12) * (OptCall.bound C g k P + 1) := htotal
    _ ≤ 100 * paper5 g k P + 8 +
        7 * (1151 + (wregs component).length) * (17 * (C + 1) * paper5 g k P) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul hcoef hb) _
    _ ≤ uniformConstant C (wregs component).length * paper5 g k P := by
      unfold uniformConstant
      nlinarith

theorem callSpace_le {C w : ℕ} (g : Graph) {k : ℕ} (hk : 3 ≤ k) (P : ℕ) :
    OptCall.callSpace C g k P ≤ uniformConstant C w * paper5 g k P := by
  have hb := bound_succ_le_paper g hk C P
  have hi := incidence_le_paper g hk P
  have hm : g.length + 1 ≤ paper5 g k P := by unfold paper5; omega
  have hp := paper_positive g k P
  unfold OptCall.callSpace bD bV uniformConstant
  nlinarith

theorem constant_lower (C w : ℕ) : 50000 ≤ uniformConstant C w := by
  unfold uniformConstant
  exact (Nat.le_mul_of_pos_right _ (by omega : 0 < C + 1)).trans
    (Nat.le_mul_of_pos_right _ (by omega : 0 < 1151 + w))

theorem coreSpace_le {C w : ℕ} (g : Graph) {k : ℕ} (hk : 3 ≤ k) (P : ℕ) :
    CoreRAM.coreSpace g k ≤ uniformConstant C w * paper5 g k P := by
  have hi := incidence_le_paper g hk P
  have hm : g.length + 1 ≤ paper5 g k P := by unfold paper5; omega
  have hp := paper_positive g k P
  have hlow := Nat.mul_le_mul_right (paper5 g k P) (constant_lower C w)
  have hc : CoreRAM.coreSpace g k ≤ 50 * paper5 g k P := by
    unfold CoreRAM.coreSpace bD bV
    nlinarith
  exact hc.trans (by omega)

theorem emptyTime_le {C w : ℕ} (g : Graph) (k P : ℕ) :
    111 ≤ uniformConstant C w * paper5 g k P := by
  have hp := paper_positive g k P
  have hlow := Nat.mul_le_mul_right (paper5 g k P) (constant_lower C w)
  omega

end STACS2027.Runtimes.BoundedCost.OptBounds
