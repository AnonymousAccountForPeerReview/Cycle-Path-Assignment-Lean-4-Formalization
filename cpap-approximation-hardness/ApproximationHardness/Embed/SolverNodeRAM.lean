module

public import ApproximationHardness.Embed.SolverPopRefine
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! Executable constant-time node operations of the linked embedding solver. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Read a child's result, or initialize the singleton group of a dart. -/
def itemResultInto (typ value head low : Nat) : Stmt :=
  .ifz typ (seqs [loadCell head 6 value, loadCell low 7 value])
    (seqs [.add head value 1, storeCell 1 value head, storeCell 2 value head,
      storeCell 3 value 0, storeCell 5 value 0, loadCell low 12 value, .add low low 1])

/-- Store an ordinary node result and advance the post-order index. -/
def storeNodeResult (head low : Nat) : Stmt := seqs [storeCell 6 20 head,
  storeCell 7 20 low, storeCell 10 20 0, .add 6 6 1]

/-- The empty-parts branch of the node dispatcher. -/
def leafNodeProgram : Stmt := seqs [.const 24 0, .add 25 5 0, storeNodeResult 24 25]

/-- The one-part branch of the node dispatcher. -/
def singleNodeProgram : Stmt := seqs [loadCell 22 17 20, loadCell 23 18 20,
  itemResultInto 22 23 24 25, storeNodeResult 24 25]

/-- Save the scalar fields of a nontrivial fork after its two part results are ordered. -/
def beginForkProgram : Stmt := seqs [storeCell 10 20 31, .add 6 6 1,
  .const 7 1, .add 8 20 0, loadCell 9 15 20,
  .add 10 29 0, .add 11 25 0, .add 12 24 0, .add 13 28 0,
  .const 14 0, .const 15 0, .const 16 0, .const 17 0, .const 18 0, .const 19 0]

/-- Either store the sole nonempty result or enter the linked merge phases. -/
def forkResultProgram : Stmt := .ifz 28 (storeNodeResult 24 25) beginForkProgram

/-- Order the two result triples by their low keys before starting a fork. -/
def forkNodeProgram : Stmt := seqs [itemResultInto 22 23 24 25,
  itemResultInto 26 27 28 29, .sub 30 29 25,
  .ifz 30 (seqs [.add 21 24 0, .add 24 28 0, .add 28 21 0,
    .add 21 25 0, .add 25 29 0, .add 29 21 0, .const 31 4]) (.const 31 3),
  forkResultProgram]

/-- Remove the positive head of an open-end group. -/
def closePositiveProgram : Stmt := seqs [.sub 32 21 22, .sub 33 22 21, .add 32 32 33,
  .ifz 32 (storeCell 1 30 0) (seqs [loadCell 32 0 23, storeCell 1 30 32])]

/-- Remove the negative head of an open-end group. -/
def closeNegativeProgram : Stmt := seqs [.sub 32 26 27, .sub 33 27 26, .add 32 32 33,
  .ifz 32 (storeCell 3 30 0) (seqs [loadCell 32 0 23, storeCell 3 30 32])]

/-- Close dart register 23 in result registers 24/25, using direct bounded array accesses. -/
def closeResultProgram : Stmt :=
  .ifz 24 (.add 25 5 0) (seqs [.sub 30 24 1,
    loadCell 21 1 30, loadCell 22 2 30, loadCell 26 3 30, loadCell 27 4 30,
    .add 31 23 1, .sub 32 21 31, .sub 33 31 21, .add 32 32 33,
    .ifz 32 closePositiveProgram closeNegativeProgram,
    loadCell 21 1 30, loadCell 26 3 30, .add 32 21 26,
    .ifz 32 (loadCell 24 5 30) .skip,
    loadCell 31 12 23, .add 31 31 1, .sub 32 25 31, .sub 33 31 25,
    .add 32 32 33, .ifz 32 (.add 25 5 0) .skip])

/-- Close a target node: child register 21, input dart register 23, and code register 34. -/
def targetNodeProgram : Stmt := seqs [loadCell 23 13 23,
  loadCell 24 6 21, loadCell 25 7 21, closeResultProgram,
  storeCell 6 20 24, storeCell 7 20 25, storeCell 10 20 34,
  storeCell 11 20 23, .add 6 6 1]

/-- Detect a target among two parts, otherwise start a fork. -/
def twoNodeProgram : Stmt := seqs [loadCell 22 17 20, loadCell 23 18 20,
  loadCell 26 19 20, loadCell 27 20 20,
  .ifz 22
    (.ifz 26 forkNodeProgram
      (seqs [loadCell 28 14 27, .ifz 28 forkNodeProgram
        (seqs [.add 21 23 0, .add 23 27 0, .const 34 1, targetNodeProgram])]))
    (.ifz 26
      (seqs [loadCell 28 14 23, .ifz 28 forkNodeProgram
        (seqs [.add 21 27 0, .const 34 2, targetNodeProgram])])
      forkNodeProgram)]

/-- Process the node in temporary register 20 using its at-most-two parts table. -/
def nodeStepProgram : Stmt := seqs [loadCell 21 16 20,
  .ifz 21 leafNodeProgram
    (seqs [.sub 21 21 1, .ifz 21 singleNodeProgram twoNodeProgram])]

/-- The actual solver dispatcher, with its post-order bounds test. -/
def mstepProgram : Stmt := .ifz 7
  (seqs [.sub 21 4 6, .ifz 21 .skip (seqs [loadCell 20 21 6, nodeStepProgram])])
  (seqs [.sub 21 7 1, .ifz 21 popStepProgram consStepProgram])

theorem itemResultInto_loopFree (typ value head low : Nat) : LoopFree (itemResultInto typ value head low) := by
  simp [itemResultInto, storeCell, loadCell, LoopFree, seqs]

theorem nodeStepProgram_loopFree : LoopFree nodeStepProgram := by
  simp [nodeStepProgram, leafNodeProgram, singleNodeProgram, twoNodeProgram,
    itemResultInto, storeNodeResult, targetNodeProgram, closeResultProgram,
    closePositiveProgram, closeNegativeProgram, forkNodeProgram, forkResultProgram,
    beginForkProgram, loadCell, storeCell, LoopFree, seqs]

theorem nodeStepProgram_size : size nodeStepProgram ≤ 1000 := by decide

theorem mstepProgram_loopFree : LoopFree mstepProgram := by
  simp [mstepProgram, nodeStepProgram_loopFree, popStepProgram_loopFree,
    consStepProgram_loopFree, loadCell, LoopFree, seqs]

theorem mstepProgram_size : size mstepProgram ≤ 2000 := by decide

/-- Exact full-memory effect of reading a part result. -/
theorem itemResultInto_raw (c : Config) {typ value head low : Nat}
    (hh : 20 ≤ head ∧ head < 30) (hl : 20 ≤ low ∧ low < 30)
    (hv : value < 30) (hvh : value ≠ head) (hvl : value ≠ low) (hhl : head ≠ low)
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let d := c.reg value
    let m₁ := upd c.mem (c.reg 51 + d) (d + 1)
    let m₂ := upd m₁ (c.reg 52 + d) (d + 1)
    let m₃ := upd m₂ (c.reg 53 + d) 0
    let m₄ := upd m₃ (c.reg 55 + d) 0
    let out := run (itemResultInto typ value head low) c
    out.reg head = (if c.reg typ = 0 then c.mem (c.reg 56 + d) else d + 1) ∧
    out.reg low = (if c.reg typ = 0 then c.mem (c.reg 57 + d) else m₄ (c.reg 62 + d) + 1) ∧
    out.mem = (if c.reg typ = 0 then c.mem else m₄) ∧
    (∀ i, i < 20 ∨ 50 ≤ i → out.reg i = c.reg i) ∧ out.out = c.out := by
  dsimp only
  have ha : head ≠ 0 ∧ head ≠ 1 ∧ head ≠ 40 ∧ head ≠ 51 ∧ head ≠ 52 ∧
    head ≠ 53 ∧ head ≠ 55 ∧ head ≠ 56 ∧ head ≠ 57 ∧ head ≠ 62 ∧
    low ≠ 0 ∧ low ≠ 1 ∧ low ≠ 40 ∧ low ≠ 51 ∧ low ≠ 52 ∧
    low ≠ 53 ∧ low ≠ 55 ∧ low ≠ 56 ∧ low ≠ 57 ∧ low ≠ 62 ∧ value ≠ 40 := by omega
  rcases ha with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    l₁, l₂, l₃, l₄, l₅, l₆, l₇, l₈, l₉, l₁₀, v₁⟩
  have har : 0 ≠ head ∧ 1 ≠ head ∧ 40 ≠ head ∧ 51 ≠ head ∧ 52 ≠ head ∧
    53 ≠ head ∧ 55 ≠ head ∧ 56 ≠ head ∧ 57 ≠ head ∧ 62 ≠ head ∧
    0 ≠ low ∧ 1 ≠ low ∧ 40 ≠ low ∧ 51 ≠ low ∧ 52 ≠ low ∧
    53 ≠ low ∧ 55 ≠ low ∧ 56 ≠ low ∧ 57 ≠ low ∧ 62 ≠ low ∧ 40 ≠ value := by omega
  rcases har with ⟨rh₁, rh₂, rh₃, rh₄, rh₅, rh₆, rh₇, rh₈, rh₉, rh₁₀,
    rl₁, rl₂, rl₃, rl₄, rl₅, rl₆, rl₇, rl₈, rl₉, rl₁₀, rv₁⟩
  by_cases ht : c.reg typ = 0
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [itemResultInto, loadCell, storeCell, run, seqs, upd, ht, Ne.symm hhl, Ne.symm hvh, *]
    · simp [itemResultInto, loadCell, storeCell, run, seqs, upd, ht, Ne.symm hhl, Ne.symm hvh, *]
    · funext i
      simp [itemResultInto, loadCell, storeCell, run, seqs, upd, ht, Ne.symm hhl, Ne.symm hvh, *]
    · intro i hi
      have hin : i ≠ head ∧ i ≠ low ∧ i ≠ 40 := by rcases hi with hi | hi <;> omega
      rcases hin with ⟨ih, il, ia⟩
      simp [itemResultInto, loadCell, storeCell, run, seqs, upd, ht, Ne.symm hhl, Ne.symm hvh, *]
    · simp [itemResultInto, loadCell, storeCell, run, seqs, ht]

/-- Full operational effect of storing a finished ordinary node. -/
theorem storeNodeResult_raw (c : Config) (head low : Nat)
    (hh : head < 30 ∧ head ≠ 40) (hl : low < 30 ∧ low ≠ 40)
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let out := run (storeNodeResult head low) c
    (∀ i, i < 20 → out.reg i = if i = 6 then c.reg 6 + 1 else c.reg i) ∧
    out.mem = upd (upd (upd c.mem (c.reg 56 + c.reg 20) (c.reg head))
      (c.reg 57 + c.reg 20) (c.reg low)) (c.reg 60 + c.reg 20) 0 ∧
    (∀ i, 50 ≤ i → out.reg i = c.reg i) ∧ out.out = c.out := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hin : i ≠ 40 := by omega
    simp [storeNodeResult, storeCell, run, seqs, hin, hz, ho]
  · funext i
    simp [storeNodeResult, storeCell, run, seqs, upd, hh.2, hl.2, hz, ho]
  · intro i hi
    have hin : i ≠ 6 ∧ i ≠ 40 := by omega
    simp [storeNodeResult, storeCell, run, seqs, hin.1, hin.2]
  · simp [storeNodeResult, storeCell, run, seqs]

/-- Full operational effect of entering the linked merge phases. -/
theorem beginForkProgram_raw (c : Config) (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let m := upd c.mem (c.reg 60 + c.reg 20) (c.reg 31)
    let out := run beginForkProgram c
    (∀ i, i < 20 → out.reg i = if i = 6 then c.reg 6 + 1
      else if i = 7 then 1 else if i = 8 then c.reg 20
      else if i = 9 then m (c.reg 65 + c.reg 20)
      else if i = 10 then c.reg 29 else if i = 11 then c.reg 25
      else if i = 12 then c.reg 24 else if i = 13 then c.reg 28
      else if 14 ≤ i then 0 else c.reg i) ∧
    out.mem = m ∧ (∀ i, 50 ≤ i → out.reg i = c.reg i) ∧ out.out = c.out := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> simp [beginForkProgram, loadCell, storeCell, run, seqs, upd, hz, ho]
  · funext i
    simp [beginForkProgram, loadCell, storeCell, run, seqs, upd]
  · intro i hi
    have hn : i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 9 ∧ i ≠ 10 ∧ i ≠ 11 ∧ i ≠ 12 ∧
      i ≠ 13 ∧ i ≠ 14 ∧ i ≠ 15 ∧ i ≠ 16 ∧ i ≠ 17 ∧ i ≠ 18 ∧ i ≠ 19 ∧ i ≠ 40 := by omega
    rcases hn with ⟨h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₄₀⟩
    simp [beginForkProgram, loadCell, storeCell, run, seqs, hz, ho, *]
  · simp [beginForkProgram, loadCell, storeCell, run, seqs]

end STACS2027.Embed.RAMSolver
