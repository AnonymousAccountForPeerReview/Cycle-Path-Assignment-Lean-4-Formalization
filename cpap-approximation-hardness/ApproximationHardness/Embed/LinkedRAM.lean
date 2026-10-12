module

public import ApproximationHardness.Embed.Linked
public import ApproximationHardness.RAM.SpecB
import Lean.Elab.Tactic.Omega

/-!
# Constant-time linked-class concatenation on the RAM

Registers 2--6 hold the successor-array base, the first head and tail, and the
second head and tail. Registers 7 and 8 receive the resulting head and tail;
register 9 is temporary. The program initializes its zero and one registers.
-/

@[expose] public section

namespace STACS2027.Embed

open RAM

/-- The RAM implementation of `appL`; it modifies at most one successor cell. -/
def appendClassProgram : Stmt := seqs [
  .const 0 0, .const 1 1,
  .ifz 3 (seqs [.add 7 5 0, .add 8 6 0])
    (.ifz 5 (seqs [.add 7 3 0, .add 8 4 0])
      (seqs [.add 7 3 0, .add 8 6 0, .sub 9 4 1, .add 9 2 9, .store 9 5]))]

theorem appendClassProgram_loopFree : LoopFree appendClassProgram := by
  simp [appendClassProgram, LoopFree, seqs]

theorem appendClassProgram_size : size appendClassProgram = 17 := by decide

/-- The only possible store address is below the supplied space bound. -/
def AppendAddressOK (S : Nat) (c : Config) : Prop :=
  c.reg 3 ≠ 0 → c.reg 5 ≠ 0 → c.reg 2 + (c.reg 4 - 1) < S

theorem appendClassProgram_addrOK {S : Nat} {c : Config} (h : AppendAddressOK S c) :
    AddrOK S appendClassProgram c := by
  simpa [appendClassProgram, AddrOK, seqs, run, AppendAddressOK] using h

/-- Every safe concatenation halts in at most seventeen actual RAM steps. -/
theorem appendClassProgram_exec {S : Nat} {c : Config} (h : AppendAddressOK S c) :
    ∃ t, ExecB S appendClassProgram c t (run appendClassProgram c) ∧ t ≤ 17 :=
  ⟨cost appendClassProgram c, execB_run appendClassProgram appendClassProgram_loopFree c
    (appendClassProgram_addrOK h), by
      simpa [appendClassProgram_size] using cost_le_size appendClassProgram c⟩

/-- The output registers and successor-array slice are exactly the abstract concatenation. -/
theorem appendClassProgram_spec (c : Config) :
    let nx := fun i => c.mem (c.reg 2 + i)
    let r := appL nx (c.reg 3) (c.reg 4) (c.reg 5) (c.reg 6)
    let c' := run appendClassProgram c
    c'.reg 7 = r.1 ∧ c'.reg 8 = r.2.1 ∧
      (∀ i, c'.mem (c.reg 2 + i) = r.2.2 i) ∧ c'.out = c.out := by
  dsimp only
  by_cases h₁ : c.reg 3 = 0
  · simp [appendClassProgram, seqs, run, appL, h₁]
  · by_cases h₂ : c.reg 5 = 0
    · simp [appendClassProgram, seqs, run, appL, h₁, h₂]
    · simp [appendClassProgram, seqs, run, appL, h₁, h₂, upd]

/-- Combining the semantic and machine proofs: safe concatenation maintains the linked
representation and performs the operation in a constant number of bounded-address steps. -/
theorem appendClassProgram_linked {S : Nat} {c : Config} {A B : List Nat}
    (HA : Linked (fun i => c.mem (c.reg 2 + i)) (c.reg 3) (c.reg 4) A)
    (HB : Linked (fun i => c.mem (c.reg 2 + i)) (c.reg 5) (c.reg 6) B)
    (hd : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) (hS : AppendAddressOK S c) :
    ∃ t c', ExecB S appendClassProgram c t c' ∧ t ≤ 17 ∧
      Linked (fun i => c'.mem (c.reg 2 + i)) (c'.reg 7) (c'.reg 8) (A ++ B) := by
  obtain ⟨t, ht, hb⟩ := appendClassProgram_exec hS
  obtain ⟨hh, htail, hmem, _⟩ := appendClassProgram_spec c
  refine ⟨t, run appendClassProgram c, ht, hb, ?_⟩
  rw [hh, htail]
  exact (Linked.append HA HB hd).frame (fun i _ => hmem i)

end STACS2027.Embed
