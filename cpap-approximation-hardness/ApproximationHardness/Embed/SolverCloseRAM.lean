module

public import ApproximationHardness.Embed.SolverNodeRAM
import Lean.Elab.Tactic.Omega

/-! Direct linked-array closing of the deepest target end. -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

@[simp] theorem difference_pair_zero (a b : Nat) : (a - b = 0 ∧ b - a = 0) ↔ a = b := by omega

@[simp] theorem symmetric_difference_zero (a b : Nat) : a - b + (b - a) = 0 ↔ a = b := by omega

/-- The exact operational effect of closing an end; group tables are reread after the update. -/
theorem closeResultProgram_raw (c : Config) (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let e := c.reg 23
    let h := c.reg 24
    let l := c.reg 25
    let g := h - 1
    let ph := c.mem (c.reg 51 + g)
    let pt := c.mem (c.reg 52 + g)
    let mh := c.mem (c.reg 53 + g)
    let mt := c.mem (c.reg 54 + g)
    let m := if ph = e + 1 then
        upd c.mem (c.reg 51 + g) (if ph = pt then 0 else c.mem (c.reg 50 + e))
      else upd c.mem (c.reg 53 + g) (if mh = mt then 0 else c.mem (c.reg 50 + e))
    let out := run closeResultProgram c
    out.reg 24 = (if h = 0 then 0 else
      if m (c.reg 51 + g) = 0 ∧ m (c.reg 53 + g) = 0 then m (c.reg 55 + g) else h) ∧
    out.reg 25 = (if h = 0 then c.reg 5 else
      if l = m (c.reg 62 + e) + 1 then c.reg 5 else l) ∧
    out.mem = (if h = 0 then c.mem else m) ∧
    (∀ i, i < 20 ∨ i = 20 ∨ i = 23 ∨ i = 34 ∨ 50 ≤ i → out.reg i = c.reg i) ∧ out.out = c.out := by
  dsimp only
  by_cases hh : c.reg 24 = 0
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [closeResultProgram, run, hh]
    · simp [closeResultProgram, run, hh, hz]
    · simp [closeResultProgram, run, hh]
    · intro i hi
      have hn : i ≠ 25 := by rcases hi with hi | hi | hi | hi | hi <;> omega
      simp [closeResultProgram, run, hh, hn]
    · simp [closeResultProgram, run, hh]
  · by_cases hp : c.mem (c.reg 51 + (c.reg 24 - 1)) = c.reg 23 + 1 <;>
      by_cases hpt : c.mem (c.reg 51 + (c.reg 24 - 1)) = c.mem (c.reg 52 + (c.reg 24 - 1)) <;>
      by_cases hmt : c.mem (c.reg 53 + (c.reg 24 - 1)) = c.mem (c.reg 54 + (c.reg 24 - 1))
    all_goals
      try simp only [hp] at hpt
      try simp only [hpt] at hp
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [closeResultProgram, closePositiveProgram, closeNegativeProgram,
          loadCell, storeCell, run, seqs, upd, Nat.add_eq_zero, hh, hp, hpt, hmt, hz, ho]
      · simp [closeResultProgram, closePositiveProgram, closeNegativeProgram,
          loadCell, storeCell, run, seqs, upd, Nat.add_eq_zero, hh, hp, hpt, hmt, hz, ho]
      · funext i
        simp [closeResultProgram, closePositiveProgram, closeNegativeProgram,
          loadCell, storeCell, run, seqs, upd, Nat.add_eq_zero, hh, hp, hpt, hmt, hz, ho]
      · intro i hi
        have hn : i ≠ 21 ∧ i ≠ 22 ∧ i ≠ 24 ∧ i ≠ 25 ∧ i ≠ 26 ∧ i ≠ 27 ∧
          i ≠ 30 ∧ i ≠ 31 ∧ i ≠ 32 ∧ i ≠ 33 ∧ i ≠ 40 := by
          rcases hi with hi | hi | hi | hi | hi <;> omega
        rcases hn with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩
        simp [closeResultProgram, closePositiveProgram, closeNegativeProgram,
          loadCell, storeCell, run, seqs, upd, Nat.add_eq_zero, hh, hp, hpt, hmt, hz, ho, *]
      · simp [closeResultProgram, closePositiveProgram, closeNegativeProgram,
          loadCell, storeCell, run, seqs, upd, Nat.add_eq_zero, hh, hp, hpt, hmt, hz, ho]

end STACS2027.Embed.RAMSolver
