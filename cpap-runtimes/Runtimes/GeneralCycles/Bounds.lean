module

public import Runtimes.GeneralCycles.TupleLoop
import Mathlib.Tactic

/-! Polynomial bounds independent of vertex labels. Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

theorem tupleTime_double_bound (N k B D : ℕ) (hB : B ≤ D * (N + 1)) :
    tupleTime N (B + tupleTime N B k + k + 3) k + 6 ≤
      (2 * D + k + 29) * (N + 1) ^ (2 * k + 4) := by
  have hA : 1 ≤ N + 1 := by omega
  have hpow : 1 ≤ (N + 1) ^ (k + 2) := Nat.one_le_pow _ _ hA
  have hlinear : N + 1 ≤ (N + 1) ^ (k + 2) := Nat.le_self_pow (by omega) _
  have hinner : tupleTime N B k ≤ (D + 10) * (N + 1) ^ (k + 2) := by
    calc
      tupleTime N B k ≤ (B + 10) * (N + 1) ^ (k + 1) := tupleTime_bound _ _ _
      _ ≤ ((D + 10) * (N + 1)) * (N + 1) ^ (k + 1) := by
        apply Nat.mul_le_mul_right
        nlinarith
      _ = (D + 10) * (N + 1) ^ (k + 2) := by rw [pow_succ]; ring
  have hbase : B + tupleTime N B k + k + 3 + 10 ≤
      (2 * D + k + 23) * (N + 1) ^ (k + 2) := by
    have hb' := hB.trans (Nat.mul_le_mul_left D hlinear)
    nlinarith
  have houter : tupleTime N (B + tupleTime N B k + k + 3) k ≤
      (2 * D + k + 23) * (N + 1) ^ (2 * k + 3) := by
    calc
      _ ≤ (B + tupleTime N B k + k + 3 + 10) * (N + 1) ^ (k + 1) :=
        tupleTime_bound _ _ _
      _ ≤ ((2 * D + k + 23) * (N + 1) ^ (k + 2)) * (N + 1) ^ (k + 1) :=
        Nat.mul_le_mul_right _ hbase
      _ = (2 * D + k + 23) * (N + 1) ^ (2 * k + 3) := by
        rw [Nat.mul_assoc, ← pow_add]
        congr 2
        omega
  have hpow' : 1 ≤ (N + 1) ^ (2 * k + 3) := Nat.one_le_pow _ _ hA
  have hmono : (N + 1) ^ (2 * k + 3) ≤ (N + 1) ^ (2 * k + 4) :=
    Nat.pow_le_pow_right hA (by omega)
  calc
    _ ≤ (2 * D + k + 29) * (N + 1) ^ (2 * k + 3) := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_left _ hmono

theorem graph_polynomial_bound (m k B D : ℕ) (hB : B ≤ D * (2 * m + 1)) :
    tupleTime (2 * m) (B + tupleTime (2 * m) B k + k + 3) k + 6 ≤
      ((2 * D + k + 29) * 2 ^ (2 * k + 4)) * (m + 1) ^ (2 * k + 4) := by
  calc
    _ ≤ (2 * D + k + 29) * (2 * m + 1) ^ (2 * k + 4) :=
      tupleTime_double_bound _ _ _ _ hB
    _ ≤ (2 * D + k + 29) * (2 * (m + 1)) ^ (2 * k + 4) := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [mul_pow]; ring

end STACS2027.Runtimes.GeneralCycles
