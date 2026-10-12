module

public import Runtimes.GeneralCycles.Assembly
import Mathlib.Tactic

/-! Uniform label-independent polynomial time and bounded memory.
Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

def programConstant (k B : ℕ) : ℕ :=
  (2 * (B + size (clearCounter k)) + k + 29) * 2 ^ (2 * k + 4)

theorem programConstant_lower (k B : ℕ) : 2 ≤ programConstant k B := by
  have h : 1 ≤ 2 ^ (2 * k + 4) := Nat.one_le_pow _ _ (by decide)
  dsimp [programConstant]
  nlinarith

theorem program_space_bound (k B m : ℕ) :
    2 * m + 1 ≤ programConstant k B * (m + 1) ^ (2 * k + 4) := by
  have hC := programConstant_lower k B
  have hm : m + 1 ≤ (m + 1) ^ (2 * k + 4) := Nat.le_self_pow (by omega) _
  nlinarith

theorem enumerateProgram_polynomial {outerValidity innerValidity : Stmt} {k B : ℕ}
    (houterValid : ValiditySpec outerValidity outerIndices (outerValues k) k acceptanceFlag B)
    (hinnerValid : ValiditySpec innerValidity (innerIndices k) (innerValues k) k innerValidFlag B)
    (g : Graph) :
    ∃ (cs : List Cycle) (steps : ℕ), cs.Perm (cycles g k) ∧
      ComputesIn (enumerateProgram outerValidity innerValidity k) (graphInput g) cs.flatten steps
        (programConstant k B * (g.length + 1) ^ (2 * k + 4)) ∧
      steps ≤ programConstant k B * (g.length + 1) ^ (2 * k + 4) := by
  obtain ⟨t, ht, hc⟩ := enumerateProgram_computes houterValid hinnerValid g
  have hb : callbackCost k B g ≤ (B + size (clearCounter k)) * (2 * g.length + 1) := le_rfl
  have hpoly := graph_polynomial_bound g.length k (callbackCost k B g)
    (B + size (clearCounter k)) hb
  refine ⟨outputCycles g k, t, outputCycles_perm g k,
    hc.mono (program_space_bound k B g.length), ?_⟩
  apply ht.trans
  exact (by omega : tupleTime (2 * g.length)
    (callbackCost k B g + tupleTime (2 * g.length) (callbackCost k B g) k + k + 3) k + 3 ≤
      tupleTime (2 * g.length)
        (callbackCost k B g + tupleTime (2 * g.length) (callbackCost k B g) k + k + 3) k + 6).trans hpoly

end STACS2027.Runtimes.GeneralCycles
