module

public import Runtimes.BoundedCost.ArrayBlocks
public import Runtimes.BoundedCost.AnnotatedNode
import Mathlib.Tactic

/-! Each enumerated search path restores the compression state before evaluating
its concrete node programs. The restoration copies both occurrence and literal tables. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.PathRestore

open STACS2027 STACS2027.RAM

abbrev activeSnapshot : ℕ := 434
abbrev forcedSnapshot : ℕ := 435
abbrev globalBudget : ℕ := 225
abbrev specialDeleted : ℕ := 432
abbrev truthLength : ℕ := 406

def activeReady : Stmt :=
  .seq (mov ArrayBlocks.sourceBase activeSnapshot)
    (.seq (mov ArrayBlocks.targetBase scanActiveBase)
      (mov ArrayBlocks.arrayLength scanClauseCount))

def forcedReady : Stmt :=
  .seq (mov ArrayBlocks.sourceBase forcedSnapshot)
    (.seq (mov ArrayBlocks.targetBase nodeForcedBase)
      (mov ArrayBlocks.arrayLength truthLength))

def finish : Stmt := .seq (.sub nodeBudget globalBudget specialDeleted) (.const nodeLive 1)

def program : Stmt := .seq activeReady
  (.seq ArrayBlocks.copyArray (.seq forcedReady (.seq ArrayBlocks.copyArray finish)))

def Globals (active forced activeCopy forcedCopy count bound budget deleted : ℕ)
    (c : Config) : Prop :=
  c.reg scanActiveBase = active ∧ c.reg nodeForcedBase = forced ∧
  c.reg activeSnapshot = activeCopy ∧ c.reg forcedSnapshot = forcedCopy ∧
  c.reg scanClauseCount = count ∧ c.reg truthLength = bound ∧
  c.reg globalBudget = budget ∧ c.reg specialDeleted = deleted

def restoredMemory (memory : ℕ → ℕ) (active forced : ℕ)
    (activeBits forcedBits : List ℕ) : ℕ → ℕ :=
  ArrayBlocks.prefixMemory
    (ArrayBlocks.prefixMemory memory active activeBits activeBits.length)
    forced forcedBits forcedBits.length

theorem program_spec {S active forced activeCopy forcedCopy budget deleted : ℕ}
    {activeBits forcedBits out : List ℕ} {memory : ℕ → ℕ}
    (ha : Arr memory activeCopy activeBits) (hf : Arr memory forcedCopy forcedBits)
    (hasep : active + activeBits.length ≤ activeCopy ∨ activeCopy + activeBits.length ≤ active)
    (hfsep : forced + forcedBits.length ≤ forcedCopy ∨ forcedCopy + forcedBits.length ≤ forced)
    (hcross : active + activeBits.length ≤ forcedCopy ∨ forcedCopy + forcedBits.length ≤ active)
    (hS : active + activeBits.length ≤ S ∧ forced + forcedBits.length ≤ S ∧
      activeCopy + activeBits.length ≤ S ∧ forcedCopy + forcedBits.length ≤ S) :
    HTB S program
      (fun c => Globals active forced activeCopy forcedCopy activeBits.length forcedBits.length
        budget deleted c ∧ c.mem = memory ∧ c.out = out)
      (fun c => Globals active forced activeCopy forcedCopy activeBits.length forcedBits.length
        budget deleted c ∧ c.mem = restoredMemory memory active forced activeBits forcedBits ∧
        c.out = out ∧ c.reg nodeBudget = budget - deleted ∧ c.reg nodeLive = 1)
      (8 * (activeBits.length + forcedBits.length) + 20) := by
  let G := Globals active forced activeCopy forcedCopy activeBits.length forcedBits.length budget deleted
  have hga : RegIndep (wregs activeReady) G := by indep [G, Globals, activeReady]
  have hgf : RegIndep (wregs forcedReady) G := by indep [G, Globals, forcedReady]
  have hgc : RegIndep (wregs ArrayBlocks.copyArray) G := by
    indep [G, Globals, ArrayBlocks.copyArray, ArrayBlocks.copyBody, forUp, upLoop, ld, st, inc, addc]
  have hActiveReady : HTB S activeReady
      (fun c => G c ∧ c.mem = memory ∧ c.out = out)
      (fun c => ArrayBlocks.CopyGlobals activeCopy active activeBits.length c ∧
        c.mem = memory ∧ c.out = out ∧ G c) 6 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨hg, hm, ho⟩
    have hgp := hg
    obtain ⟨hactive, hforced, hac, hfc, hcount, hbound, hk, hd⟩ := hg
    refine ⟨AddrOK.of_memFree (by decide), ?_, ?_, ?_, hga.run (by decide) hgp⟩
    all_goals simp +decide only [activeReady, ArrayBlocks.CopyGlobals, run_seq', run_mov,
      setReg_reg, setReg_mem, setReg_out, hactive, hac, hcount, hm, ho, ↓reduceIte]
  have hActiveCopy := (ArrayBlocks.copyArray_spec (out := out) ha hasep
    ⟨hS.2.2.1, hS.1⟩).frameReg hgc
  let copied := ArrayBlocks.prefixMemory memory active activeBits activeBits.length
  have hf' : Arr copied forcedCopy forcedBits := by
    intro i hi
    dsimp only [copied]
    rw [ArrayBlocks.prefixMemory_outside (by rcases hcross with h | h <;> omega)]
    exact hf i hi
  have hForcedReady : HTB S forcedReady
      (fun c => G c ∧ c.mem = copied ∧ c.out = out)
      (fun c => ArrayBlocks.CopyGlobals forcedCopy forced forcedBits.length c ∧
        c.mem = copied ∧ c.out = out ∧ G c) 6 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨hg, hm, ho⟩
    have hgp := hg
    obtain ⟨hactive, hforced, hac, hfc, hcount, hbound, hk, hd⟩ := hg
    refine ⟨AddrOK.of_memFree (by decide), ?_, ?_, ?_, hgf.run (by decide) hgp⟩
    all_goals simp +decide only [forcedReady, ArrayBlocks.CopyGlobals, run_seq', run_mov,
      setReg_reg, setReg_mem, setReg_out, hforced, hfc, hbound, hm, ho, ↓reduceIte]
  have hForcedCopy := (ArrayBlocks.copyArray_spec (out := out) hf' hfsep
    ⟨hS.2.2.2, hS.2.1⟩).frameReg hgc
  have hFinish : HTB S finish
      (fun c => G c ∧ c.mem = restoredMemory memory active forced activeBits forcedBits ∧ c.out = out)
      (fun c => G c ∧ c.mem = restoredMemory memory active forced activeBits forcedBits ∧
        c.out = out ∧ c.reg nodeBudget = budget - deleted ∧ c.reg nodeLive = 1) 2 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨hg, hm, ho⟩
    have hgg : RegIndep (wregs finish) G := by indep [G, Globals, finish]
    have hgp := hg
    obtain ⟨_, _, _, _, _, _, hk, hd⟩ := hg
    refine ⟨AddrOK.of_memFree (by decide), hgg.run (by decide) hgp, ?_, ?_, ?_, ?_⟩
    all_goals simp +decide only [finish, run_seq', run_sub, run_const,
      setReg_mem, setReg_out, setReg_reg, hk, hd, hm, ho, ↓reduceIte]
  have hca : HTB S ArrayBlocks.copyArray
      (fun c => ArrayBlocks.CopyGlobals activeCopy active activeBits.length c ∧
        c.mem = memory ∧ c.out = out ∧ G c)
      (fun c => G c ∧ c.mem = copied ∧ c.out = out) (activeBits.length * 8 + 3) :=
    hActiveCopy.mono (fun c hc => ⟨⟨hc.1, hc.2.1, hc.2.2.1⟩, hc.2.2.2⟩)
      (fun c hc => ⟨hc.2, hc.1.2.1, hc.1.2.2⟩) (by omega)
  have hcf : HTB S ArrayBlocks.copyArray
      (fun c => ArrayBlocks.CopyGlobals forcedCopy forced forcedBits.length c ∧
        c.mem = copied ∧ c.out = out ∧ G c)
      (fun c => G c ∧ c.mem = restoredMemory memory active forced activeBits forcedBits ∧ c.out = out)
      (forcedBits.length * 8 + 3) :=
    hForcedCopy.mono (fun c hc => ⟨⟨hc.1, hc.2.1, hc.2.2.1⟩, hc.2.2.2⟩)
      (fun c hc => ⟨hc.2, hc.1.2.1, hc.1.2.2⟩) (by omega)
  exact (hActiveReady.seq (hca.seq (hForcedReady.seq (hcf.seq hFinish)))).weaken (by omega)

end STACS2027.Runtimes.BoundedCost.PathRestore
