module

public import ApproximationHardness.Embed.OrientationSequence
public import ApproximationHardness.Embed.RotationChoice
import Lean.Elab.Tactic.Omega

/-! # RAM extraction of a rotation from the solver's bit codes -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Branch on the solver's information code in register 117. -/
def codeCase (code : Nat) (yes no : Stmt) : Stmt := seqs [
  .const 134 code, .sub 132 117 134, .sub 133 134 117,
  .add 132 132 133, .ifz 132 yes no]

@[simp] theorem difference_zero (a b : Nat) : a - b + (b - a) = 0 ↔ a = b := by omega

@[simp] theorem both_differences_zero (a b : Nat) :
    (a - b = 0 ∧ b - a = 0) ↔ a = b := by omega

/-- Load the orientation at the identifier in the indicated per-vertex table. -/
def loadOrientation (source : Nat) : Stmt := seqs [
  .add 121 source 120, .load 118 121, .add 121 130 118, .load 119 121]

def negateOrientation : Stmt := .ifz 119 (.const 119 1) (.const 119 0)

/-- The exact five-code interpretation stored by the solver. -/
def encodedBit (code index group : Nat) (o : Nat → Bool) : Bool :=
  if code = 1 then !(o index) else
  if code = 2 then o index else
  if code = 3 then o group else
  if code = 4 then !(o group) else false

def codeBit : Stmt := .seq (seqs [.add 121 60 120, .load 117 121])
  (codeCase 1 (.seq (loadOrientation 61) negateOrientation)
    (codeCase 2 (loadOrientation 61)
      (codeCase 3 (loadOrientation 65)
        (codeCase 4 (.seq (loadOrientation 65) negateOrientation) (.const 119 0)))))

theorem codeBit_loopFree : LoopFree codeBit := by
  simp [codeBit, codeCase, loadOrientation, negateOrientation, LoopFree, seqs]

theorem codeBit_value (c : Config) (o : Nat → Bool)
    (hi : c.mem (c.reg 130 + c.mem (c.reg 61 + c.reg 120)) =
      boolWord (o (c.mem (c.reg 61 + c.reg 120))))
    (hg : c.mem (c.reg 130 + c.mem (c.reg 65 + c.reg 120)) =
      boolWord (o (c.mem (c.reg 65 + c.reg 120)))) :
    (run codeBit c).reg 119 = boolWord (encodedBit
      (c.mem (c.reg 60 + c.reg 120)) (c.mem (c.reg 61 + c.reg 120))
      (c.mem (c.reg 65 + c.reg 120)) o) := by
  cases hoi : o (c.mem (c.reg 61 + c.reg 120)) <;>
    cases hog : o (c.mem (c.reg 65 + c.reg 120)) <;>
    simp [codeBit, codeCase, loadOrientation, negateOrientation, seqs, run,
      hi, hg, boolWord, encodedBit, hoi, hog] <;> split_ifs <;> simp_all

theorem codeBit_mem (c : Config) : (run codeBit c).mem = c.mem := by
  simp [codeBit, codeCase, loadOrientation, negateOrientation, seqs, run]

theorem codeBit_out (c : Config) : (run codeBit c).out = c.out := by
  simp [codeBit, codeCase, loadOrientation, negateOrientation, seqs, run]

theorem codeBit_reg (c : Config) (r : Nat)
    (hr : r ≠ 117 ∧ r ≠ 118 ∧ r ≠ 119 ∧ r ≠ 121 ∧
      r ≠ 132 ∧ r ≠ 133 ∧ r ≠ 134) :
    (run codeBit c).reg r = c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩
  simp [codeBit, codeCase, loadOrientation, negateOrientation, seqs, run,
    h₁,h₂,h₃,h₄,h₅,h₆,h₇]

theorem codeBit_addrOK {S : Nat} (c : Config)
    (hinfo : c.reg 60 + c.reg 120 < S)
    (hindex : c.reg 61 + c.reg 120 < S)
    (hgroup : c.reg 65 + c.reg 120 < S)
    (hio : c.reg 130 + c.mem (c.reg 61 + c.reg 120) < S)
    (hgo : c.reg 130 + c.mem (c.reg 65 + c.reg 120) < S) :
    AddrOK S codeBit c := by
  simp [codeBit, codeCase, loadOrientation, negateOrientation, seqs, AddrOK,
    run, hinfo, hindex, hgroup, hio, hgo]

def readVertex : Stmt := seqs [.add 121 127 126, .load 120 121]

def writeRotation : Stmt := seqs [
  .ifz 119 (.add 121 129 126) (.add 121 128 126),
  .load 131 121, .write 131, .add 126 126 1, .sub 125 125 1]

/-- Output one dart's chosen predecessor and advance the bounded scan. -/
def rotationStep : Stmt := .seq readVertex (.seq codeBit writeRotation)
def rotationLoop : Stmt := .loop 125 rotationStep

theorem readVertex_value (c : Config) :
    (run readVertex c).reg 120 = c.mem (c.reg 127 + c.reg 126) := by
  simp [readVertex, seqs, run]

theorem readVertex_mem (c : Config) : (run readVertex c).mem = c.mem := by
  simp [readVertex, seqs, run]

theorem readVertex_out (c : Config) : (run readVertex c).out = c.out := by
  simp [readVertex, seqs, run]

theorem readVertex_reg (c : Config) (r : Nat) (hr : r ≠ 121 ∧ r ≠ 120) :
    (run readVertex c).reg r = c.reg r := by
  simp [readVertex, seqs, run, hr.1, hr.2]

theorem writeRotation_out (c : Config) :
    (run writeRotation c).out = c.out ++ [if c.reg 119 = 0 then
      c.mem (c.reg 129 + c.reg 126) else c.mem (c.reg 128 + c.reg 126)] := by
  by_cases h : c.reg 119 = 0 <;> simp [writeRotation, seqs, run, h]

theorem writeRotation_mem (c : Config) : (run writeRotation c).mem = c.mem := by
  simp [writeRotation, seqs, run]

theorem writeRotation_reg (c : Config) (r : Nat)
    (hr : r ≠ 121 ∧ r ≠ 131 ∧ r ≠ 126 ∧ r ≠ 125) :
    (run writeRotation c).reg r = c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄⟩
  simp [writeRotation, seqs, run, h₁,h₂,h₃,h₄]

theorem writeRotation_advance (c : Config) (hone : c.reg 1 = 1) :
    (run writeRotation c).reg 126 = c.reg 126 + 1 ∧
    (run writeRotation c).reg 125 = c.reg 125 - 1 := by
  simp [writeRotation, seqs, run, hone]

theorem rotationStep_mem (c : Config) : (run rotationStep c).mem = c.mem := by
  simp only [rotationStep, run, writeRotation_mem, codeBit_mem, readVertex_mem]

theorem rotationStep_reg (c : Config) (r : Nat)
    (hr : r ≠ 117 ∧ r ≠ 118 ∧ r ≠ 119 ∧ r ≠ 120 ∧ r ≠ 121 ∧
      r ≠ 125 ∧ r ≠ 126 ∧ r ≠ 131 ∧ r ≠ 132 ∧ r ≠ 133 ∧ r ≠ 134) :
    (run rotationStep c).reg r = c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁⟩
  simp only [rotationStep, run, writeRotation_reg _ _ ⟨h₅,h₈,h₇,h₆⟩,
    codeBit_reg _ _ ⟨h₁,h₂,h₃,h₅,h₉,h₁₀,h₁₁⟩, readVertex_reg _ _ ⟨h₅,h₄⟩]

theorem rotationStep_loopFree : LoopFree rotationStep := by
  simp [rotationStep, readVertex, writeRotation, codeBit_loopFree, LoopFree, seqs]

def rotationValue (c : Config) (o : Nat → Bool) (d : Nat) : Nat :=
  let v := c.mem (c.reg 127 + d)
  if encodedBit (c.mem (c.reg 60 + v)) (c.mem (c.reg 61 + v))
      (c.mem (c.reg 65 + v)) o then
    c.mem (c.reg 128 + d) else c.mem (c.reg 129 + d)

theorem rotationStep_out (c : Config) (o : Nat → Bool)
    (hi : c.mem (c.reg 130 + c.mem (c.reg 61 + c.mem (c.reg 127 + c.reg 126))) =
      boolWord (o (c.mem (c.reg 61 + c.mem (c.reg 127 + c.reg 126)))))
    (hg : c.mem (c.reg 130 + c.mem (c.reg 65 + c.mem (c.reg 127 + c.reg 126))) =
      boolWord (o (c.mem (c.reg 65 + c.mem (c.reg 127 + c.reg 126))))) :
    (run rotationStep c).out = c.out ++ [rotationValue c o (c.reg 126)] := by
  have hb := codeBit_value (run readVertex c) o
    (by simpa [readVertex, seqs, run] using hi)
    (by simpa [readVertex, seqs, run] using hg)
  simp only [readVertex_value, readVertex_mem,
    readVertex_reg _ 60 (by decide), readVertex_reg _ 61 (by decide),
    readVertex_reg _ 65 (by decide)] at hb
  simp only [rotationStep, run, writeRotation_out, codeBit_out, readVertex_out,
    codeBit_mem, readVertex_mem, codeBit_reg _ 129 (by decide),
    codeBit_reg _ 128 (by decide), codeBit_reg _ 126 (by decide),
    readVertex_reg _ 129 (by decide), readVertex_reg _ 128 (by decide),
    readVertex_reg _ 126 (by decide), hb]
  cases h : encodedBit (c.mem (c.reg 60 + c.mem (c.reg 127 + c.reg 126)))
      (c.mem (c.reg 61 + c.mem (c.reg 127 + c.reg 126)))
      (c.mem (c.reg 65 + c.mem (c.reg 127 + c.reg 126))) o <;>
    simp [rotationValue, boolWord, h]

theorem rotationStep_advance (c : Config) (hone : c.reg 1 = 1) :
    (run rotationStep c).reg 126 = c.reg 126 + 1 ∧
    (run rotationStep c).reg 125 = c.reg 125 - 1 := by
  have ho : (run codeBit (run readVertex c)).reg 1 = 1 := by
    rw [codeBit_reg _ _ (by decide), readVertex_reg _ _ (by decide)]
    exact hone
  have h := writeRotation_advance (run codeBit (run readVertex c)) ho
  simpa only [rotationStep, run, codeBit_reg _ 125 (by decide),
    codeBit_reg _ 126 (by decide), readVertex_reg _ 125 (by decide),
    readVertex_reg _ 126 (by decide)] using h

theorem rotationStep_addrOK {S : Nat} (c : Config)
    (hrep : c.reg 127 + c.reg 126 < S)
    (hinfo : c.reg 60 + c.mem (c.reg 127 + c.reg 126) < S)
    (hindex : c.reg 61 + c.mem (c.reg 127 + c.reg 126) < S)
    (hgroup : c.reg 65 + c.mem (c.reg 127 + c.reg 126) < S)
    (hio : c.reg 130 + c.mem (c.reg 61 + c.mem (c.reg 127 + c.reg 126)) < S)
    (hgo : c.reg 130 + c.mem (c.reg 65 + c.mem (c.reg 127 + c.reg 126)) < S)
    (hn : c.reg 128 + c.reg 126 < S) (hp : c.reg 129 + c.reg 126 < S) :
    AddrOK S rotationStep c := by
  have hA : AddrOK S readVertex c := by simp [readVertex, seqs, AddrOK, run, hrep]
  have hB : AddrOK S codeBit (run readVertex c) := by
    apply codeBit_addrOK <;> simpa [readVertex, seqs, run] using
      (by first | exact hinfo | exact hindex | exact hgroup | exact hio | exact hgo)
  have hC : AddrOK S writeRotation (run codeBit (run readVertex c)) := by
    have hn' : (run codeBit (run readVertex c)).reg 128 +
        (run codeBit (run readVertex c)).reg 126 < S := by
      simpa only [codeBit_reg _ 128 (by decide), codeBit_reg _ 126 (by decide),
        readVertex_reg _ 128 (by decide), readVertex_reg _ 126 (by decide)] using hn
    have hp' : (run codeBit (run readVertex c)).reg 129 +
        (run codeBit (run readVertex c)).reg 126 < S := by
      simpa only [codeBit_reg _ 129 (by decide), codeBit_reg _ 126 (by decide),
        readVertex_reg _ 129 (by decide), readVertex_reg _ 126 (by decide)] using hp
    by_cases h : (run codeBit (run readVertex c)).reg 119 = 0 <;>
      simp [writeRotation, seqs, AddrOK, run, h, hn', hp']
  exact .seq hA (.seq hB hC)

end STACS2027.Embed.RAMSolver
