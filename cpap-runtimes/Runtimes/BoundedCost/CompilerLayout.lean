module

public import Runtimes.BoundedCost.ArrayBlocks
import Mathlib.Tactic

/-! The reserved workspace and disjoint caller tables of the Almost 2-SAT RAM
compiler. The original input is copied above the reusable separator workspace. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

structure CompilerLayout where
  span : ℕ
  region : ℕ
  formula : ℕ
  active : ℕ
  candidate : ℕ
  reference : ℕ
  forced : ℕ
  labels : ℕ
  baseActive : ℕ
  seedForced : ℕ
  special : ℕ
  outerDigits : ℕ
  innerDigits : ℕ
  saved : ℕ
  edgeInput : ℕ
  space : ℕ

def compilerLayout (constant clauses budget : ℕ) : CompilerLayout :=
  let n := 2 * clauses + 1
  let depth := min budget clauses + 1
  let span := (constant + 1) * (n + 1) ^ 2
  let formula := 8 * span + 4
  let active := formula + 2 * clauses
  let candidate := active + clauses
  let reference := candidate + 2 * n
  let forced := reference + 2 * n
  let labels := forced + 2 * n
  let baseActive := labels + 2 * n
  let seedForced := baseActive + clauses
  let special := seedForced + 2 * n
  let outerDigits := special + 2 * depth
  let innerDigits := outerDigits + depth
  let saved := innerDigits + depth
  let edgeInput := saved + 4
  ⟨span, 4 * span + 1, formula, active, candidate, reference, forced, labels,
    baseActive, seedForced, special, outerDigits, innerDigits, saved, edgeInput,
    edgeInput + 2 * clauses + 5⟩

theorem compilerLayout_regions (constant clauses budget : ℕ) :
    let layout := compilerLayout constant clauses budget
    let n := 2 * clauses + 1
    let depth := min budget clauses + 1
    4 * layout.span ≤ layout.formula ∧
      8 * layout.span + 1 < layout.formula ∧
      layout.formula + 2 * clauses = layout.active ∧
      layout.active + clauses = layout.candidate ∧
      layout.candidate + 2 * n = layout.reference ∧
      layout.reference + 2 * n = layout.forced ∧
      layout.forced + 2 * n = layout.labels ∧
      layout.labels + 2 * n = layout.baseActive ∧
      layout.baseActive + clauses = layout.seedForced ∧
      layout.seedForced + 2 * n = layout.special ∧
      layout.special + 2 * depth = layout.outerDigits ∧
      layout.outerDigits + depth = layout.innerDigits ∧
      layout.innerDigits + depth = layout.saved ∧
      layout.saved + 4 = layout.edgeInput ∧
      layout.edgeInput + 2 * clauses + 5 = layout.space := by
  dsimp [compilerLayout]
  omega

theorem compilerLayout_input_copy (constant clauses budget : ℕ) :
    2 + 2 * clauses ≤ (compilerLayout constant clauses budget).formula := by
  dsimp [compilerLayout]
  have hq : 2 * clauses + 2 ≤ (2 * clauses + 1 + 1) ^ 2 := by nlinarith
  nlinarith

theorem compilerLayout_space_bound (constant clauses budget : ℕ) :
    (compilerLayout constant clauses budget).space ≤
      128 * (constant + 1) * (clauses + 1) ^ 2 := by
  dsimp [compilerLayout]
  have hk : min budget clauses ≤ clauses := min_le_right _ _
  have hq : clauses + 1 ≤ (clauses + 1) ^ 2 := by nlinarith
  have hspan : (constant + 1) * (2 * clauses + 1 + 1) ^ 2 =
      4 * (constant + 1) * (clauses + 1) ^ 2 := by ring
  rw [hspan]
  nlinarith

end STACS2027.Runtimes.BoundedCost
