module

import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

theorem leastCutIncompatibleTime {n m span width t : ℕ}
    (hn : n + 2 ≤ span) (hm : m ≤ n) (ht : t ≤ 84 * n + 204 * m + 51) :
    t + 2 ≤ (500 + width) * (span + 1) := by
  calc
    t + 2 ≤ 500 * (span + 1) := by omega
    _ ≤ (500 + width) * (span + 1) := Nat.mul_le_mul_right _ (by omega)

theorem leastCutTotalTime {n m span width tb tm tc td : ℕ}
    (hn : n + 2 ≤ span) (hm : m ≤ n)
    (hb : tb ≤ 84 * n + 204 * m + 51) (hmeta : tm ≤ 7)
    (hcall : tc ≤ (40 + width) * (span + 1)) (hdecode : td ≤ 44 * n + 3) :
    tb + (tm + (tc + td) + 1) ≤ (500 + width) * (span + 1) := by
  have hlinear : 84 * n + 204 * m + 51 + 7 + (44 * n + 3) + 1 ≤ 460 * (span + 1) := by omega
  calc
    tb + (tm + (tc + td) + 1) ≤ 460 * (span + 1) + (40 + width) * (span + 1) := by omega
    _ = _ := by ring

end STACS2027.Runtimes.BoundedCost
