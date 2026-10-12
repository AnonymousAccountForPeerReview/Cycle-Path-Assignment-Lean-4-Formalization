module

public import ApproximationHardness.RAM.Polarize.Program
import Lean.Elab.Tactic.Omega

/-!
# Reading a clause into the slots
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-- The slot `(vr, sr)` holds the literal `l`. -/
def LitIn (c : Config) (vr sr : Nat) (l : Literal) : Prop := c.reg vr = l.var ∧ c.reg sr = signCode l

/-- The registers holding the constants of the program. -/
structure Consts (c : Config) : Prop where
  one : c.reg Reg.one = 1
  zero : c.reg Reg.zero = 0
  two : c.reg PR.two = 2
  three : c.reg PR.three = 3

theorem Consts.frame {c c' : Config} (h : Consts c) (h1 : c'.reg Reg.one = c.reg Reg.one)
    (h2 : c'.reg Reg.zero = c.reg Reg.zero) (h3 : c'.reg PR.two = c.reg PR.two)
    (h4 : c'.reg PR.three = c.reg PR.three) : Consts c' :=
  ⟨h1.trans h.one, h2.trans h.zero, h3.trans h.two, h4.trans h.three⟩

theorem At.getD {c : Config} {w : List Nat} (h : At c w) {i : Nat} (hi : i < w.length) :
    c.mem (c.reg Reg.p + i) = w.getD i 0 := h i hi

/-- Reading a clause of two literals. -/
theorem readClause_two (c : Config) (l0 l1 : Literal) (w : List Nat) (hAt : At c (clauseCode [l0, l1] ++ w))
    (hk : Consts c) :
    let c' := run readClause c
    c'.reg Reg.len = 2 ∧ LitIn c' PR.v0 PR.s0 l0 ∧ LitIn c' PR.v1 PR.s1 l1 ∧
      c'.reg Reg.m = c.reg Reg.m - 1 ∧ c'.reg Reg.p = c.reg Reg.p + 5 ∧ At c' w ∧
      c'.mem = c.mem ∧ c'.out = c.out := by
  have g0 := hAt.getD (i := 0) (by simp [clauseCode, litCode])
  have g1 := hAt.getD (i := 1) (by simp [clauseCode, litCode])
  have g2 := hAt.getD (i := 2) (by simp [clauseCode, litCode])
  have g3 := hAt.getD (i := 3) (by simp [clauseCode, litCode])
  have g4 := hAt.getD (i := 4) (by simp [clauseCode, litCode])
  simp only [clauseCode, litCode, List.flatMap_cons, List.flatMap_nil, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, List.append_nil, List.getD_cons_succ, List.getD_cons_zero,
    Nat.add_zero] at g0 g1 g2 g3 g4
  have hone := hk.one
  have htwo := hk.two
  have hmem : (run readClause c).mem = c.mem := run_mem_frame _ _ (by decide)
  have hp : (run readClause c).reg Reg.p = c.reg Reg.p + 5 := by
    simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0]
    try omega
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, hp, ?_, hmem, run_out_frame _ _ (by decide)⟩
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0, Nat.add_assoc] at g1 ⊢; simp [g1]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0, Nat.add_assoc] at g2 ⊢; simp [g2]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0, Nat.add_assoc] at g3 ⊢; simp [g3]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0, Nat.add_assoc] at g4 ⊢; simp [g4]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0]
  · exact hAt.drop hmem (by rw [hp]; simp [clauseCode, litCode])

/-- Reading a clause of three literals. -/
theorem readClause_three (c : Config) (l0 l1 l2 : Literal) (w : List Nat)
    (hAt : At c (clauseCode [l0, l1, l2] ++ w)) (hk : Consts c) :
    let c' := run readClause c
    c'.reg Reg.len = 3 ∧ LitIn c' PR.v0 PR.s0 l0 ∧ LitIn c' PR.v1 PR.s1 l1 ∧ LitIn c' PR.v2 PR.s2 l2 ∧
      c'.reg Reg.m = c.reg Reg.m - 1 ∧ c'.reg Reg.p = c.reg Reg.p + 7 ∧ At c' w ∧
      c'.mem = c.mem ∧ c'.out = c.out := by
  have g0 := hAt.getD (i := 0) (by simp [clauseCode, litCode])
  have g1 := hAt.getD (i := 1) (by simp [clauseCode, litCode])
  have g2 := hAt.getD (i := 2) (by simp [clauseCode, litCode])
  have g3 := hAt.getD (i := 3) (by simp [clauseCode, litCode])
  have g4 := hAt.getD (i := 4) (by simp [clauseCode, litCode])
  have g5 := hAt.getD (i := 5) (by simp [clauseCode, litCode])
  have g6 := hAt.getD (i := 6) (by simp [clauseCode, litCode])
  simp only [clauseCode, litCode, List.flatMap_cons, List.flatMap_nil, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, List.append_nil, List.getD_cons_succ, List.getD_cons_zero,
    Nat.add_zero] at g0 g1 g2 g3 g4 g5 g6
  have hone := hk.one
  have htwo := hk.two
  have hmem : (run readClause c).mem = c.mem := run_mem_frame _ _ (by decide)
  have hp : (run readClause c).reg Reg.p = c.reg Reg.p + 7 := by
    simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0]
    try omega
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, hp, ?_, hmem, run_out_frame _ _ (by decide)⟩
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0, Nat.add_assoc] at g1 ⊢; simp [g1]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0, Nat.add_assoc] at g2 ⊢; simp [g2]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0, Nat.add_assoc] at g3 ⊢; simp [g3]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0, Nat.add_assoc] at g4 ⊢; simp [g4]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0, Nat.add_assoc] at g5 ⊢; simp [g5]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0, Nat.add_assoc] at g6 ⊢; simp [g6]
  · simp only [readClause, rdLit, run_seqs_cons, run_seqs_nil, run]
    simp +decide [hone, htwo, g0]
  · exact hAt.drop hmem (by rw [hp]; simp [clauseCode, litCode])

/-- The registers `readClause` writes. -/
theorem readClause_frame (c : Config) (r : Nat) (h : r ∉ regsW readClause) :
    (run readClause c).reg r = c.reg r := run_reg_frame _ _ _ h

end STACS2027.RAM
