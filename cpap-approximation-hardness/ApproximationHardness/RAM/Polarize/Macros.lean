module

public import ApproximationHardness.RAM.Polarize.Read
import Lean.Elab.Tactic.Omega

/-!
# The blocks of the Lemma 10 program
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-! ### Counting a literal -/

theorem cntLit_mem (c : Config) (vr sr : Nat) (h1 : vr ≠ PR.addr) (h2 : sr ≠ PR.addr) (hone : c.reg Reg.one = 1) (a : Nat) :
    (run (cntLit vr sr) c).mem a =
      if a = c.reg Reg.N + c.reg vr + c.reg vr + c.reg sr then c.mem a + 1 else c.mem a := by
  simp only [cntLit, run_seqs_cons, run_seqs_nil, run]
  simp +decide [h1, h2, hone]
  split <;> simp_all

theorem cntLit_out (c : Config) (vr sr : Nat) : (run (cntLit vr sr) c).out = c.out :=
  run_out_frame _ _ (by simp [cntLit, hasWrite])

theorem cntLit_frame (c : Config) (vr sr r : Nat) (h1 : r ≠ PR.addr) (h2 : r ≠ PR.x) :
    (run (cntLit vr sr) c).reg r = c.reg r :=
  run_reg_frame _ _ _ (by simp [cntLit, regsW, h1, h2])

/-! ### Tautological pairs -/

theorem tautPair_del (c : Config) (va sa vb sb : Nat)
    (ha : va ≠ PR.x ∧ va ≠ PR.y ∧ va ≠ PR.z ∧ va ≠ PR.del) (hsa : sa ≠ PR.x ∧ sa ≠ PR.y ∧ sa ≠ PR.z ∧ sa ≠ PR.del)
    (hb : vb ≠ PR.x ∧ vb ≠ PR.y ∧ vb ≠ PR.z ∧ vb ≠ PR.del) (hsb : sb ≠ PR.x ∧ sb ≠ PR.y ∧ sb ≠ PR.z ∧ sb ≠ PR.del) :
    (run (tautPair va sa vb sb) c).reg PR.del =
      if c.reg va = c.reg vb ∧ c.reg sa ≠ c.reg sb then 1 else c.reg PR.del := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  obtain ⟨c1, c2, c3, c4⟩ := hsa
  obtain ⟨d1, d2, d3, d4⟩ := hsb
  simp only [tautPair, run_seqs_cons, run_seqs_nil, run]
  simp +decide [a1, b1, c1, c2, d1, d2]
  by_cases e1 : c.reg va = c.reg vb <;> by_cases e2 : c.reg sa = c.reg sb <;> simp +decide [e1, e2] <;> omega

theorem tautPair_mem (c : Config) (va sa vb sb : Nat) : (run (tautPair va sa vb sb) c).mem = c.mem :=
  run_mem_frame _ _ (by simp [tautPair, hasStore])

theorem tautPair_out (c : Config) (va sa vb sb : Nat) : (run (tautPair va sa vb sb) c).out = c.out :=
  run_out_frame _ _ (by simp [tautPair, hasWrite])

theorem tautPair_frame (c : Config) (va sa vb sb r : Nat) (h1 : r ≠ PR.x) (h2 : r ≠ PR.y) (h3 : r ≠ PR.z)
    (h4 : r ≠ PR.del) : (run (tautPair va sa vb sb) c).reg r = c.reg r :=
  run_reg_frame _ _ _ (by simp [tautPair, regsW, h1, h2, h3, h4])

/-! ### Pure variables -/

/-- The counts `x` (negative) and `y` (positive) of a variable are `0, 3` or `3, 0`. -/
def pureCounts (x y : Nat) : Bool := (x == 0 && y == 3) || (y == 0 && x == 3)

theorem pureLit_del (c : Config) (vr : Nat) (h : vr ≠ PR.addr ∧ vr ≠ PR.x ∧ vr ≠ PR.y ∧ vr ≠ PR.z ∧ vr ≠ PR.u ∧
    vr ≠ PR.del) (hone : c.reg Reg.one = 1) (hthree : c.reg PR.three = 3) :
    (run (pureLit vr) c).reg PR.del =
      if pureCounts (c.mem (c.reg Reg.N + c.reg vr + c.reg vr)) (c.mem (c.reg Reg.N + c.reg vr + c.reg vr + 1))
      = true then 1 else c.reg PR.del := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  simp only [pureLit, run_seqs_cons, run_seqs_nil, run]
  simp +decide [a1, hone, hthree]
  generalize c.mem (c.reg Reg.N + c.reg vr + c.reg vr) = X
  generalize c.mem (c.reg Reg.N + c.reg vr + c.reg vr + 1) = Y
  simp only [pureCounts]
  by_cases hx : X = 0 <;> by_cases hy : Y = 0 <;> by_cases hx3 : X = 3 <;> by_cases hy3 : Y = 3 <;>
    simp +decide [hx, hy, hx3, hy3] <;> omega

theorem pureLit_mem (c : Config) (vr : Nat) : (run (pureLit vr) c).mem = c.mem :=
  run_mem_frame _ _ (by simp [pureLit, hasStore])

theorem pureLit_out (c : Config) (vr : Nat) : (run (pureLit vr) c).out = c.out :=
  run_out_frame _ _ (by simp [pureLit, hasWrite])

theorem pureLit_frame (c : Config) (vr r : Nat) (h1 : r ≠ PR.addr) (h2 : r ≠ PR.x) (h3 : r ≠ PR.y)
    (h4 : r ≠ PR.z) (h5 : r ≠ PR.u) (h6 : r ≠ PR.del) : (run (pureLit vr) c).reg r = c.reg r :=
  run_reg_frame _ _ _ (by simp [pureLit, regsW, h1, h2, h3, h4, h5, h6])

end STACS2027.RAM
