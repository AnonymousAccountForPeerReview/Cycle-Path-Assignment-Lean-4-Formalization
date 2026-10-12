module

public import Runtimes.BoundedCost.LayoutRAM
public import Runtimes.BoundedCost.TruthInit
import Mathlib.Tactic

/-! The original encoded formula is copied into preserved caller storage and its
initial all-false assignment table is constructed by actual RAM execution. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.CompilerInit

open STACS2027 STACS2027.RAM Complexity.SAT

def copyReady : Stmt :=
  .seq (mov ArrayBlocks.sourceBase LayoutRAM.originalBase)
    (.seq (mov ArrayBlocks.targetBase scanFormulaBase)
      (mov ArrayBlocks.arrayLength LayoutRAM.codeLength))

def program (constant : ℕ) : Stmt :=
  .seq (LayoutRAM.program constant)
    (.seq copyReady (.seq ArrayBlocks.copyArray TruthInit.program))

def Globals (constant clauses budget : ℕ) (c : Config) : Prop :=
  LayoutRAM.LayoutRep (compilerLayout constant clauses budget) c ∧
    LayoutRAM.ArithmeticGlobals constant clauses budget c ∧
    c.reg 345 = min budget clauses + 1

def initializedMemory (constant clauses budget : ℕ) (memory : ℕ → ℕ)
    (codes : List ℕ) : ℕ → ℕ :=
  let layout := compilerLayout constant clauses budget
  CandidateDecode.prefixMemory
    (ArrayBlocks.prefixMemory memory layout.formula codes codes.length)
    layout.candidate (fun _ => false) (2 * clauses + 1)

theorem program_spec {S constant clauses budget : ℕ} {memory : ℕ → ℕ}
    {codes out : List ℕ} (hlen : codes.length = 2 * clauses)
    (hS : (compilerLayout constant clauses budget).space ≤ S)
    (hk : memory 0 = budget) (hm : memory 1 = clauses) (hcodes : Arr memory 2 codes) :
    HTB S (program constant) (fun c => c.mem = memory ∧ c.out = out)
      (fun c => Globals constant clauses budget c ∧
        c.mem = initializedMemory constant clauses budget memory codes ∧ c.out = out)
      (400 + 5 * (constant + 1) + 80 * (clauses + 1)) := by
  let layout := compilerLayout constant clauses budget
  let Fr := Globals constant clauses budget
  have hSmall : 2 ≤ S := by dsimp [compilerLayout] at hS; omega
  have hFormS : layout.formula + codes.length ≤ S := by
    dsimp [layout, compilerLayout] at hS ⊢; rw [hlen]; omega
  have hSourceS : 2 + codes.length ≤ S := by
    rw [hlen]
    apply (compilerLayout_input_copy constant clauses budget).trans
    change layout.formula ≤ S
    omega
  have hTruthS : layout.candidate + 2 * (2 * clauses + 1) ≤ S := by
    dsimp [layout, compilerLayout] at hS ⊢; omega
  have hSep : 2 + codes.length ≤ layout.formula := by
    simpa [hlen, layout] using compilerLayout_input_copy constant clauses budget
  have hReady : HTB S copyReady
      (fun c => Fr c ∧ c.mem = memory ∧ c.out = out)
      (fun c => ArrayBlocks.CopyGlobals 2 layout.formula codes.length c ∧
        c.mem = memory ∧ c.out = out ∧ Fr c) 6 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨⟨hLayout, hArithmetic, hDepth⟩, hmem, ho⟩
    have hglobal : Fr (run copyReady c) := by
      have hindep : RegIndep (wregs copyReady) Fr := by
        indep [Fr, Globals, LayoutRAM.LayoutRep, LayoutRAM.ArithmeticGlobals, copyReady]
      exact hindep.run (by decide) ⟨hLayout, hArithmetic, hDepth⟩
    have hf := hLayout.2.2.1
    have hb := hArithmetic.2.2.2.2.2.2.2.2.2.1
    have hl := hArithmetic.2.2.2.2.2.2.1
    refine ⟨AddrOK.of_memFree (by decide), ?_, ?_, ?_, hglobal⟩
    all_goals simp +decide only [ArrayBlocks.CopyGlobals, copyReady, run_seq', run_mov,
      setReg_reg, setReg_mem, setReg_out, hf, hb, hl, hlen, hmem, ho, layout, ↓reduceIte,
      true_and, and_true]
  have hcopy := (ArrayBlocks.copyArray_spec (out := out) hcodes (Or.inr hSep) ⟨hSourceS, hFormS⟩).frameReg
    (F := Fr) (by indep [Fr, Globals, LayoutRAM.LayoutRep, LayoutRAM.ArithmeticGlobals,
      ArrayBlocks.copyArray, ArrayBlocks.copyBody, forUp, upLoop, wregs, ld, st, inc, addc])
  let copied := ArrayBlocks.prefixMemory memory layout.formula codes codes.length
  have hTruth := (TruthInit.program_spec (memory := copied) (out := out) hTruthS).frameReg
    (F := Fr) (by indep [Fr, Globals, LayoutRAM.LayoutRep, LayoutRAM.ArithmeticGlobals,
      TruthInit.program, TruthInit.body, forUp, upLoop, wregs, ld, st, inc, addc])
  have hcopy' : HTB S ArrayBlocks.copyArray
      (fun c => ArrayBlocks.CopyGlobals 2 layout.formula codes.length c ∧
        c.mem = memory ∧ c.out = out ∧ Fr c)
      (fun c => Fr c ∧ c.reg TruthInit.candidateBase = layout.candidate ∧
        c.reg TruthInit.variableCount = 2 * clauses + 1 ∧ c.mem = copied ∧ c.out = out)
      (codes.length * 8 + 3) := by
    refine hcopy.mono (fun c hc => ⟨⟨hc.1, hc.2.1, hc.2.2.1⟩, hc.2.2.2⟩) ?_ (by omega)
    rintro c ⟨⟨_, hmem, ho⟩, hg⟩
    exact ⟨hg, hg.1.2.2.2.2.1, hg.2.1.2.2.2.1, hmem, ho⟩
  have hTruth' : HTB S TruthInit.program
      (fun c => Fr c ∧ c.reg TruthInit.candidateBase = layout.candidate ∧
        c.reg TruthInit.variableCount = 2 * clauses + 1 ∧ c.mem = copied ∧ c.out = out)
      (fun c => Fr c ∧ c.mem = initializedMemory constant clauses budget memory codes ∧ c.out = out)
      (16 * (2 * clauses + 1) + 3) := by
    refine hTruth.mono (fun c hc => ⟨⟨hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩, hc.1⟩)
      ?_ (by omega)
    rintro c ⟨⟨_, _, hmem, ho⟩, hg⟩
    exact ⟨hg, hmem, ho⟩
  have hLayout : HTB S (LayoutRAM.program constant)
      (fun c => c.mem = memory ∧ c.out = out)
      (fun c => Fr c ∧ c.mem = memory ∧ c.out = out)
      (260 + 5 * (2 * clauses + 2) + 5 * (constant + 1)) := by
    refine (LayoutRAM.program_spec hSmall hk hm).mono (fun c hc => hc) ?_ (by omega)
    rintro c ⟨hl, hg, hd, hmem, ho⟩
    exact ⟨⟨hl, hg, hd⟩, hmem, ho⟩
  exact (hLayout.seq (hReady.seq (hcopy'.seq hTruth'))).weaken
    (by rw [hlen]; omega)

end STACS2027.Runtimes.BoundedCost.CompilerInit
