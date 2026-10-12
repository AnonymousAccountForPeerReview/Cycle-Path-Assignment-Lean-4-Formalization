module

public import Runtimes.BoundedCost.CompressionSetupBridge
public import Runtimes.BoundedCost.ActualInnerRAM
public import Runtimes.BoundedCost.CompilerRegisterFrame
import Mathlib.Tactic

/-! The outer ternary scan keeps the original code array, reference assignment,
base snapshot and packed special clauses while testing each concrete seed. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

@[mk_iff] structure OuterGeometry (S : ℕ) (layout : CompilerLayout) (nodes clauses depth special : ℕ) : Prop where
  inner : InnerGeometry S layout nodes clauses depth
  seedSpecial : layout.seedForced + 2 * nodes ≤ layout.special
  specialDigits : layout.special + 2 * special ≤ layout.outerDigits
  outerInner : layout.outerDigits + special ≤ layout.innerDigits

def OuterBasic (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (rows : List (Bool × Clause)) (special : CNF)
    (budget depth processed : ℕ) (oldOutput digits : List ℕ) (c : Config) : Prop :=
  Compiler.Globals layout nodes original.length budget depth (registerView callerRegister c) ∧
  Arr c.mem layout.formula (TwoSat.codes original) ∧ TruthTable c.mem layout.reference nodes τ ∧
  Compiler.StageZero (Flow.hornSeparator F) c ∧ c.out = oldOutput ∧
  Arr c.mem layout.baseActive (maskWords rows) ∧ Arr c.mem layout.special (TwoSat.codes special) ∧
  c.reg (callerRegister rOB) = layout.outerDigits ∧ c.reg (callerRegister rOL) = digits.length ∧
  c.reg (callerRegister rK) = 3 ∧ Arr c.mem layout.outerDigits digits ∧
  digits.length = special.length ∧ c.reg (callerRegister seedSpecialCount) = special.length ∧
  c.reg (callerRegister Compiler.processed) = processed ∧ c.reg (callerRegister Compiler.alive) = 1

def OuterRep (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (rows : List (Bool × Clause)) (special : CNF)
    (budget depth processed : ℕ) (oldOutput : List ℕ) (answer : Option Assignment)
    (digits : List ℕ) (c : Config) : Prop :=
  OuterBasic F layout nodes original τ rows special budget depth processed oldOutput digits c ∧
    InnerAnswerRep layout nodes answer c

def outerAnswerStep (cut : LeastCutOperation) (τ : Assignment) (depth : ℕ)
    (base special : CNF) (budget : ℕ) (found : Option Assignment) (digits : List ℕ) : Option Assignment :=
  found.orElse fun _ =>
    match compressionVector digits special with
    | none => none
    | some branch => if branch.1 ≤ budget then
        encodedPathSearch cut τ depth base branch.2 (budget - branch.1) else none

theorem outerAnswerStep_fold (cut : LeastCutOperation) (τ : Assignment) (depth : ℕ)
    (base special : CNF) (budget : ℕ) :
    ternaryFold (outerAnswerStep cut τ depth base special budget)
      special.length (3 ^ special.length) none =
      encodedCompressionSearch cut τ depth base special budget := by
  unfold ternaryFold outerAnswerStep encodedCompressionSearch
  rw [firstSuccess_foldl]
  rfl

theorem outerRep_setDigit {F : Stmt} {layout : CompilerLayout} {nodes S budget depth processed : ℕ}
    {original : CNF} {τ : Assignment} {rows : List (Bool × Clause)} {special : CNF}
    {oldOutput digits : List ℕ} {answer : Option Assignment} {c : Config} {i v : ℕ}
    (hgeo : OuterGeometry S layout nodes original.length depth special.length)
    (hrows : rows.length = original.length)
    (hcodes : (TwoSat.codes original).length ≤ 2 * original.length)
    (hspecial : (TwoSat.codes special).length ≤ 2 * special.length)
    (h : OuterRep F layout nodes original τ rows special budget depth processed oldOutput answer digits c)
    (hi : i < digits.length) :
    OuterRep F layout nodes original τ rows special budget depth processed oldOutput answer
      (digits.set i v) (c.setMem (layout.outerDigits + i) v) := by
  obtain ⟨⟨hg, hc, hr, hz, ho, hbase, hspecialArray, hob, hol, hk, hdigits, hlen, hcount, hp, halive⟩,
    hans⟩ := h
  obtain ⟨hinner, hseedSpecial, hspecialDigits, houterInner⟩ := hgeo
  obtain ⟨hcut, hlabels, hbaseSeed, hseedInner, hinnerOutput⟩ := hinner
  obtain ⟨hhigh, hformula, hactive, hcandidate, href, hforced, hlabelsOutput, houtput⟩ := hcut
  refine ⟨⟨by simpa only [Compiler.globals_iff, registerView, setMem_reg] using hg,
    hc.upd_of_disjoint (by omega), hr.upd_outside (by omega), hz, ho,
    hbase.upd_of_disjoint (by simp [maskWords_length, hrows]; omega),
    hspecialArray.upd_of_disjoint (by omega), hob, ?_, hk, hdigits.upd_set rfl,
    by simpa using hlen, hcount, hp, halive⟩, ?_⟩
  · simpa only [List.length_set, setMem_reg] using hol
  · cases answer with
    | none => exact hans
    | some σ => exact ⟨hans.1, hans.2.upd_outside (by omega)⟩

end STACS2027.Runtimes.BoundedCost
