module

public import ApproximationHardness.Embed.SolverStepRAM
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! The actual pop branch of the linked embedding RAM solver. -/

@[expose] public section
set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Operational effect of the two class appends in a pop. -/
theorem popClasses_raw (c : Config) (positive : Bool) (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let uh := if positive then c.reg 21 else c.reg 23
    let ut := if positive then c.reg 22 else c.reg 24
    let wh := if positive then c.reg 23 else c.reg 21
    let wt := if positive then c.reg 24 else c.reg 22
    let a := appL (fun i => c.mem (c.reg 50 + i)) (c.reg 14) (c.reg 15) uh ut
    let b := appL a.2.2 (c.reg 16) (c.reg 17) wh wt
    let out := run (popClasses positive) c
    (∀ i, (i < 30 ∧ i ≠ 14 ∧ i ≠ 15 ∧ i ≠ 16 ∧ i ≠ 17) ∨ 50 ≤ i → out.reg i = c.reg i) ∧
    out.reg 14 = a.1 ∧ out.reg 15 = a.2.1 ∧ out.reg 16 = b.1 ∧ out.reg 17 = b.2.1 ∧
    out.reg 30 = (if positive then 0 else 1) ∧
    out.mem = appendMem (appendMem c.mem (c.reg 50) (c.reg 14) (c.reg 15) uh)
      (c.reg 50) (c.reg 16) (c.reg 17) wh ∧ out.out = c.out := by
  cases positive <;> dsimp only
  all_goals
    by_cases hp : c.reg 21 = 0 <;> by_cases hm : c.reg 23 = 0 <;>
      by_cases ha : c.reg 14 = 0 <;> by_cases hb : c.reg 16 = 0
    all_goals
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        have hn : i ≠ 14 ∧ i ≠ 15 ∧ i ≠ 16 ∧ i ≠ 17 ∧ i ≠ 30 ∧ i ≠ 32 ∧
          i ≠ 33 ∧ i ≠ 34 ∧ i ≠ 35 ∧ i ≠ 40 := by rcases hi with hi | hi <;> omega
        rcases hn with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
        simp [popClasses, appendInto, run, seqs, hz, ho, hp, hm, ha, hb, *]
      · simp [popClasses, appendInto, appL, run, seqs, hz, ho, hp, hm, ha, hb]
      · simp [popClasses, appendInto, appL, run, seqs, hz, ho, hp, hm, ha, hb]
      · simp [popClasses, appendInto, appL, run, seqs, hz, ho, hp, hm, ha, hb]
      · simp [popClasses, appendInto, appL, run, seqs, hz, ho, hp, hm, ha, hb]
      · simp [popClasses, appendInto, run, seqs, hz, ho, hp, hm, ha, hb]
      · funext i
        simp [popClasses, appendInto, appL, appendMem, upd, run, seqs, hz, ho, hp, hm, ha, hb]
      · simp [popClasses, appendInto, run, seqs, hz, ho, hp, hm, ha, hb]

/-- The read-only probe used before testing whether an upper group must be popped. -/
def popProbe : Stmt := seqs [.sub 20 12 1, groupRead,
  headKey 25 21, headKey 26 23, .sub 25 25 10, .sub 26 26 10]

/-- Exact read-only effect of the pop probe. -/
theorem popProbe_raw (c : Config) (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let g := c.reg 12 - 1
    let p := run popProbe c
    (∀ i, i < 20 ∨ 50 ≤ i → p.reg i = c.reg i) ∧
    p.reg 20 = g ∧ p.reg 21 = c.mem (c.reg 51 + g) ∧
    p.reg 22 = c.mem (c.reg 52 + g) ∧ p.reg 23 = c.mem (c.reg 53 + g) ∧
    p.reg 24 = c.mem (c.reg 54 + g) ∧ p.reg 28 = c.mem (c.reg 55 + g) ∧
    p.reg 25 = rawHeadKey c (c.mem (c.reg 51 + g)) - c.reg 10 ∧
    p.reg 26 = rawHeadKey c (c.mem (c.reg 53 + g)) - c.reg 10 ∧
    p.mem = c.mem ∧ p.out = c.out := by
  dsimp only
  by_cases hp : c.mem (c.reg 51 + (c.reg 12 - 1)) = 0 <;>
    by_cases hm : c.mem (c.reg 53 + (c.reg 12 - 1)) = 0
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hn : i ≠ 20 ∧ i ≠ 21 ∧ i ≠ 22 ∧ i ≠ 23 ∧ i ≠ 24 ∧ i ≠ 25 ∧
        i ≠ 26 ∧ i ≠ 28 ∧ i ≠ 40 ∧ i ≠ 41 := by rcases hi with hi | hi <;> omega
      rcases hn with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
      simp [popProbe, groupRead, headKey, loadCell, run, seqs, hz, ho, hp, hm, *]
    all_goals simp [popProbe, groupRead, headKey, loadCell, rawHeadKey,
      run, seqs, hz, ho, hp, hm]

/-- Exact footprint of recording a consumed group. -/
theorem consumeRecord_raw (c : Config) (pointer : Nat) (hp : pointer < 20)
    (hzero : pointer ≠ 0) (hone : pointer ≠ 1) (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let out := run (consumeRecord pointer) c
    (∀ i, i < 20 → out.reg i = if i = pointer then c.reg 28 else c.reg i) ∧
    out.mem = upd (upd c.mem (c.reg 58 + c.reg 20) (c.reg 9 + 1))
      (c.reg 59 + c.reg 20) (c.reg 30) ∧
    (∀ i, 50 ≤ i → out.reg i = c.reg i) ∧ out.out = c.out := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi₁ : i ≠ 29 := by omega
    have hi₂ : i ≠ 40 := by omega
    simp [consumeRecord, storeCell, seqs, run, hz, ho, hi₁, hi₂]
  · funext i
    have hp₁ : pointer ≠ 29 := by omega
    have hp₂ : pointer ≠ 40 := by omega
    simp [consumeRecord, storeCell, seqs, run, upd, hz, ho, hp₁, hp₂]
  · intro i hi
    have hi₁ : i ≠ pointer := by omega
    have hi₂ : i ≠ 29 := by omega
    have hi₃ : i ≠ 40 := by omega
    simp [consumeRecord, storeCell, seqs, run, hz, ho, hi₁, hi₂, hi₃]
  · simp [consumeRecord, storeCell, seqs, run]

/-- The full operational effect of appending and recording one popped group. -/
theorem popExecute_raw (p : Config) (positive : Bool) (hz : p.reg 0 = 0) (ho : p.reg 1 = 1) :
    let uh := if positive then p.reg 21 else p.reg 23
    let ut := if positive then p.reg 22 else p.reg 24
    let wh := if positive then p.reg 23 else p.reg 21
    let wt := if positive then p.reg 24 else p.reg 22
    let a := appL (fun i => p.mem (p.reg 50 + i)) (p.reg 14) (p.reg 15) uh ut
    let b := appL a.2.2 (p.reg 16) (p.reg 17) wh wt
    let m₁ := appendMem p.mem (p.reg 50) (p.reg 14) (p.reg 15) uh
    let m₂ := appendMem m₁ (p.reg 50) (p.reg 16) (p.reg 17) wh
    let out := run (consumeRecord 12) (run (popClasses positive) p)
    (∀ i, i < 20 → out.reg i = if i = 12 then p.reg 28
      else if i = 14 then a.1 else if i = 15 then a.2.1
      else if i = 16 then b.1 else if i = 17 then b.2.1 else p.reg i) ∧
    out.mem = upd (upd m₂ (p.reg 58 + p.reg 20) (p.reg 9 + 1))
      (p.reg 59 + p.reg 20) (if positive then 0 else 1) ∧
    (∀ i, 50 ≤ i → out.reg i = p.reg i) ∧ out.out = p.out := by
  dsimp only
  obtain ⟨hf, ha, hat, hb, hbt, hflip, hm, hout⟩ := popClasses_raw p positive hz ho
  let q := run (popClasses positive) p
  have hzero : q.reg 0 = 0 := (hf 0 (Or.inl (by decide))).trans hz
  have hone : q.reg 1 = 1 := (hf 1 (Or.inl (by decide))).trans ho
  obtain ⟨hs, hm', hf', hout'⟩ := consumeRecord_raw q 12 (by decide) (by decide) (by decide) hzero hone
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hs i hi]
    have hkeep : i ≠ 14 → i ≠ 15 → i ≠ 16 → i ≠ 17 → q.reg i = p.reg i := by
      intro ha hb hc hd
      exact hf i (Or.inl ⟨by omega, ha, hb, hc, hd⟩)
    by_cases h₁ : i = 12 <;> by_cases h₂ : i = 14 <;> by_cases h₃ : i = 15 <;>
      by_cases h₄ : i = 16 <;> by_cases h₅ : i = 17
    all_goals simp_all only [q, ↓reduceIte]
    all_goals first
      | exact hf 28 (Or.inl (by decide))
      | exact ha
      | exact hat
      | exact hb
      | exact hbt
      | exact hkeep h₂ h₃ h₄ h₅
  · rw [hm']
    simp only [q, hf 58 (Or.inr (by decide)), hf 59 (Or.inr (by decide)),
      hf 20 (Or.inl (by decide)), hf 9 (Or.inl (by decide)), hflip, hm]
  · intro i hi
    exact (hf' i hi).trans (hf i (Or.inr hi))
  · exact hout'.trans hout

end STACS2027.Embed.RAMSolver
