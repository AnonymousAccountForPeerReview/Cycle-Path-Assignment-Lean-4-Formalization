module

public import ApproximationHardness.Embed.FirstOccurrences
public import ApproximationHardness.RAM.SpecB
import Lean.Elab.Tactic.Omega

/-! # Constant-time lookup and insertion in the first-occurrence dictionary -/

@[expose] public section

namespace STACS2027.Embed

open RAM Complexity.SAT

/-- Base205, variable211, currenteven-dart209; result214 is its representative. -/
def firstLookup : Stmt := seqs [
  .add 213 205 211, .load 212 213,
  .ifz 212 (seqs [.add 212 209 1, .store 213 212]) .skip,
  .sub 214 212 1]

theorem firstLookup_loopFree : LoopFree firstLookup := by
  simp [firstLookup, LoopFree, seqs]

theorem firstLookup_size : size firstLookup ≤ 10 := by decide

theorem firstLookup_mem (c : Config) (hone : c.reg 1 = 1) :
    ∀ a, (run firstLookup c).mem a =
      if a = c.reg 205+c.reg 211 ∧ c.mem (c.reg 205+c.reg 211) = 0
      then c.reg 209+1 else c.mem a := by
  intro a
  by_cases h : c.mem (c.reg 205+c.reg 211) = 0 <;>
    simp [firstLookup, seqs, run, hone, h]

theorem firstLookup_value (c : Config) (hone : c.reg 1 = 1) :
    (run firstLookup c).reg 214 =
      if c.mem (c.reg 205+c.reg 211) = 0 then c.reg 209
      else c.mem (c.reg 205+c.reg 211)-1 := by
  by_cases h : c.mem (c.reg 205+c.reg 211) = 0 <;>
    simp [firstLookup, seqs, run, hone, h]

theorem firstLookup_out (c : Config) : (run firstLookup c).out = c.out := by
  simp [firstLookup, seqs, run]

theorem firstLookup_reg (c : Config) (r : Nat) (hr : r ≠ 212 ∧ r ≠ 213 ∧ r ≠ 214) :
    (run firstLookup c).reg r = c.reg r := by
  simp [firstLookup, seqs, run, hr.1,hr.2.1,hr.2.2]

theorem firstLookup_addrOK {S : Nat} (c : Config) (ha : c.reg 205+c.reg 211 < S) :
    AddrOK S firstLookup c := by
  simp [firstLookup, seqs, AddrOK, run, ha]

theorem firstLookup_exec {S : Nat} (c : Config) (ha : c.reg 205+c.reg 211 < S) :
    ∃ t, ExecB S firstLookup c t (run firstLookup c) ∧ t ≤ 10 :=
  ⟨_,execB_run firstLookup firstLookup_loopFree c (firstLookup_addrOK c ha),
    Nat.le_trans (cost_le_size firstLookup c) firstLookup_size⟩

theorem firstLookup_dictionary (c : Config) (past : List Literal) (l : Literal)
    (hone : c.reg 1 = 1) (hv : c.reg 211 = l.var) (hd : c.reg 209 = 2*past.length)
    (hm : ∀ v, c.mem (c.reg 205+v) = firstCode past v) :
    (∀ v, (run firstLookup c).mem (c.reg 205+v) = firstCode (past++[l]) v) ∧
      (run firstLookup c).reg 214 = firstCode (past++[l]) l.var-1 := by
  constructor
  · intro v
    rw [firstLookup_mem c hone,firstCode_snoc]
    rw [hv,hd,hm]
    by_cases he : v = l.var
    · subst v
      simp [hm]
    · have he' : l.var ≠ v := Ne.symm he
      simp [he,he',hm]
  · rw [firstLookup_value c hone,hv,hd,hm,firstCode_snoc]
    by_cases h : firstCode past l.var = 0 <;> simp [h]


theorem firstLookup_dictionary_bounded (c : Config) (past : List Literal) (l : Literal)
    (n : Nat) (hl : l.var < n) (hone : c.reg 1 = 1) (hv : c.reg 211 = l.var)
    (hd : c.reg 209 = 2*past.length)
    (hm : ∀ v, v < n → c.mem (c.reg 205+v) = firstCode past v) :
    (∀ v, v < n → (run firstLookup c).mem (c.reg 205+v) = firstCode (past++[l]) v) ∧
      (run firstLookup c).reg 214 = firstCode (past++[l]) l.var-1 := by
  constructor
  · intro v hvn
    rw [firstLookup_mem c hone,firstCode_snoc,hv,hd,hm _ hl]
    by_cases he : v = l.var
    · subst v; simp [hm _ hl]
    · have he' : l.var ≠ v := Ne.symm he
      simp [he,he',hm _ hvn]
  · rw [firstLookup_value c hone,hv,hd,hm _ hl,firstCode_snoc]
    by_cases h : firstCode past l.var = 0 <;> simp [h]

end STACS2027.Embed
