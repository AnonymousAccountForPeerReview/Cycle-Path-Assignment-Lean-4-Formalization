module

public import Runtimes.BoundedCost.CompilerLayout
public import Runtimes.BoundedCost.SearchScan
import Mathlib.Tactic

/-! Input metadata, arithmetic and caller-table allocation are performed by one
finite RAM program. The reserved separator span is computed from the formula
size; no size or exponential counter is supplied by the caller. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.LayoutRAM

open STACS2027 STACS2027.RAM

abbrev span : ℕ := 400
abbrev nodesPlus : ℕ := 401
abbrev square : ℕ := 402
abbrev multiplyIndex : ℕ := 403
abbrev factor : ℕ := 404
abbrev codeLength : ℕ := 405
abbrev truthLength : ℕ := 406
abbrev depth : ℕ := 407
abbrev originalBase : ℕ := 408
abbrev inputAddress : ℕ := 409
abbrev savedBase : ℕ := 416
abbrev savedLength : ℕ := 417
abbrev edgeLength : ℕ := 418

def prepare (constant : ℕ) : Stmt :=
  .seq (.const inputAddress 0) (.seq (.load 225 inputAddress)
  (.seq (.const inputAddress 1) (.seq (.load scanClauseCount inputAddress)
  (.seq (mov 226 scanClauseCount)
  (.seq (.add 220 scanClauseCount scanClauseCount) (.seq (inc 220)
  (.seq (addc nodesPlus 220 1) (.seq (.const factor (constant + 1))
  (.seq (.add codeLength scanClauseCount scanClauseCount)
  (.seq (.add truthLength 220 220)
  (.seq (ifLe 225 scanClauseCount (mov depth 225) (mov depth scanClauseCount))
  (.seq (inc depth) (.seq (.const originalBase 2) (.const 224 0))))))))))))))

def allocateTables : Stmt :=
  .seq (.add scanFormulaBase span span)
  (.seq (.add scanFormulaBase scanFormulaBase scanFormulaBase)
  (.seq (.add scanFormulaBase scanFormulaBase scanFormulaBase)
  (.seq (addc scanFormulaBase scanFormulaBase 4) (.seq (mov rFREE scanFormulaBase)
  (.seq (alloc scanFormulaBase codeLength) (.seq (alloc scanActiveBase scanClauseCount)
  (.seq (alloc scanCandidateBase truthLength) (.seq (alloc scanReferenceBase truthLength)
  (.seq (alloc 222 truthLength) (.seq (alloc 223 truthLength)
  (.seq (alloc 434 scanClauseCount) (.seq (alloc 435 truthLength)
  (.seq (.add inputAddress depth depth) (.seq (alloc 430 inputAddress)
  (.seq (alloc 433 depth) (.seq (alloc 344 depth)
  (.seq (.const savedLength 4) (.seq (alloc savedBase savedLength)
  (.seq (addc edgeLength codeLength 5) (.seq (alloc 300 edgeLength)
  (.seq (.add 350 span span) (.seq (.add 350 350 350)
  (.seq (inc 350) (mov 345 depth))))))))))))))))))))))))

def program (constant : ℕ) : Stmt :=
  .seq (prepare constant)
    (.seq (mul square nodesPlus nodesPlus multiplyIndex)
      (.seq (mul span square factor multiplyIndex) allocateTables))

def ArithmeticGlobals (constant clauses budget : ℕ) (c : Config) : Prop :=
  c.reg scanClauseCount = clauses ∧ c.reg 226 = clauses ∧ c.reg 225 = budget ∧
    c.reg 220 = 2 * clauses + 1 ∧ c.reg nodesPlus = 2 * clauses + 2 ∧
    c.reg factor = constant + 1 ∧ c.reg codeLength = 2 * clauses ∧
    c.reg truthLength = 2 * (2 * clauses + 1) ∧
    c.reg depth = min budget clauses + 1 ∧ c.reg originalBase = 2 ∧ c.reg 224 = 0

def LayoutRep (layout : CompilerLayout) (c : Config) : Prop :=
  c.reg span = layout.span ∧ c.reg 350 = layout.region ∧
    c.reg scanFormulaBase = layout.formula ∧ c.reg scanActiveBase = layout.active ∧
    c.reg scanCandidateBase = layout.candidate ∧ c.reg scanReferenceBase = layout.reference ∧
    c.reg 222 = layout.forced ∧ c.reg 223 = layout.labels ∧ c.reg 434 = layout.baseActive ∧
    c.reg 435 = layout.seedForced ∧ c.reg 430 = layout.special ∧
    c.reg 433 = layout.outerDigits ∧ c.reg 344 = layout.innerDigits ∧
    c.reg savedBase = layout.saved ∧ c.reg 300 = layout.edgeInput ∧ c.reg rFREE = layout.space

theorem prepare_spec {S constant clauses budget : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hS : 2 ≤ S) (hk : memory 0 = budget) (hm : memory 1 = clauses) :
    HTB S (prepare constant) (fun c => c.mem = memory ∧ c.out = out)
      (fun c => ArithmeticGlobals constant clauses budget c ∧ c.mem = memory ∧ c.out = out) 100 := by
  refine HTB.run_le (by simp [prepare, LoopFree, ifLe, ifLt, mov, inc, addc])
    (by simp [prepare, size, ifLe, ifLt, mov, inc, addc]) ?_
  rintro c ⟨hmem, ho⟩
  refine ⟨?_, ?_⟩
  · addr_ok [prepare, hmem]
  · simp +decide only [ArithmeticGlobals, prepare, ifLe, ifLt, run_seq', run_load,
      run_const, run_add, run_inc, run_addc, run_mov, run_sub, run_ifz',
      setReg_reg, setReg_mem, setReg_out, hmem, ho, hk, hm, ↓reduceIte]
    split_ifs <;> simp_all [Nat.min_def] <;> omega

theorem allocateTables_spec {S constant clauses budget : ℕ} {memory : ℕ → ℕ} {out : List ℕ} :
    HTB S allocateTables
      (fun c => ArithmeticGlobals constant clauses budget c ∧
        c.reg span = (compilerLayout constant clauses budget).span ∧ c.mem = memory ∧ c.out = out)
      (fun c => LayoutRep (compilerLayout constant clauses budget) c ∧
        ArithmeticGlobals constant clauses budget c ∧
        c.reg 345 = min budget clauses + 1 ∧ c.mem = memory ∧ c.out = out) 150 := by
  refine HTB.run_le (by simp [allocateTables, LoopFree, alloc, mov, addc, inc])
    (by simp [allocateTables, size, alloc, mov, addc, inc]) ?_
  rintro c ⟨⟨hm, hm', hk, hn, hnp, hc, hcl, htl, hd, hb, hp⟩, hs, hmem, ho⟩
  refine ⟨AddrOK.of_memFree (by simp [allocateTables, memFree, alloc, mov, addc, inc]), ?_⟩
  simp +decide only [LayoutRep, ArithmeticGlobals, compilerLayout, allocateTables,
    run_seq', run_add, run_addc, run_mov, run_alloc, run_const, run_inc,
    setReg_reg, setReg_mem, setReg_out, hm, hm', hk, hn, hnp, hc, hcl, htl, hd, hb, hp,
    hs, hmem, ho, ↓reduceIte]
  ring_nf
  trivial

theorem program_spec {S constant clauses budget : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hS : 2 ≤ S) (hk : memory 0 = budget) (hm : memory 1 = clauses) :
    HTB S (program constant) (fun c => c.mem = memory ∧ c.out = out)
      (fun c => LayoutRep (compilerLayout constant clauses budget) c ∧
        ArithmeticGlobals constant clauses budget c ∧
        c.reg 345 = min budget clauses + 1 ∧ c.mem = memory ∧ c.out = out)
      (260 + 5 * (2 * clauses + 2) + 5 * (constant + 1)) := by
  let P := fun c => ArithmeticGlobals constant clauses budget c ∧ c.mem = memory ∧ c.out = out
  have hsq := HTB.mul (S := S) (d := square) (a := nodesPlus) (b := nodesPlus)
    (k := multiplyIndex) (x := 2 * clauses + 2) (y := 2 * clauses + 2)
    (P := P) (by decide) (by indep [P, ArithmeticGlobals])
    (fun c hc => hc.1.2.2.2.2.1) (fun c hc => hc.1.2.2.2.2.1)
  let Q := fun c => P c ∧ c.reg square = (2 * clauses + 2) * (2 * clauses + 2)
  have hspan := HTB.mul (S := S) (d := span) (a := square) (b := factor)
    (k := multiplyIndex) (x := (2 * clauses + 2) * (2 * clauses + 2)) (y := constant + 1)
    (P := Q) (by decide) (by indep [Q, P, ArithmeticGlobals])
    (fun c hc => hc.2) (fun c hc => hc.1.1.2.2.2.2.2.1)
  have hsuffix : HTB S allocateTables
      (fun c => Q c ∧ c.reg span = ((2 * clauses + 2) * (2 * clauses + 2)) * (constant + 1))
      (fun c => LayoutRep (compilerLayout constant clauses budget) c ∧
        ArithmeticGlobals constant clauses budget c ∧
        c.reg 345 = min budget clauses + 1 ∧ c.mem = memory ∧ c.out = out) 150 := by
    refine allocateTables_spec.pre ?_
    rintro c ⟨⟨⟨hg, hmem, ho⟩, _⟩, hs⟩
    refine ⟨hg, ?_, hmem, ho⟩
    rw [hs]
    dsimp [compilerLayout]
    ring
  exact ((prepare_spec hS hk hm).seq (hsq.seq (hspan.seq hsuffix))).weaken (by omega)

end STACS2027.Runtimes.BoundedCost.LayoutRAM
