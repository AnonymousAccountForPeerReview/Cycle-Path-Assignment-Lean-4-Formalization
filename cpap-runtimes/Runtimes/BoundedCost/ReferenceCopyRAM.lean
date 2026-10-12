module

public import Runtimes.BoundedCost.ArrayBlocks
public import Runtimes.BoundedCost.DenseTables
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

abbrev referenceCopyCandidate : ℕ := 203
abbrev referenceCopyReference : ℕ := 204
abbrev referenceCopyLength : ℕ := 406

def referenceCopyReady : Stmt :=
  .seq (mov ArrayBlocks.sourceBase referenceCopyCandidate)
    (.seq (mov ArrayBlocks.targetBase referenceCopyReference)
      (mov ArrayBlocks.arrayLength referenceCopyLength))

def copyReference : Stmt := .seq referenceCopyReady ArrayBlocks.copyArray

def ReferenceCopyGlobals (candidate reference length : ℕ) (c : Config) : Prop :=
  c.reg referenceCopyCandidate = candidate ∧ c.reg referenceCopyReference = reference ∧
    c.reg referenceCopyLength = length

theorem copyReference_spec {S candidate reference : ℕ} {values : List ℕ}
    {memory : ℕ → ℕ} {out : List ℕ}
    (hvalues : Arr memory candidate values)
    (hsep : reference + values.length ≤ candidate ∨ candidate + values.length ≤ reference)
    (hS : candidate + values.length ≤ S ∧ reference + values.length ≤ S) :
    HTB S copyReference
      (fun c => ReferenceCopyGlobals candidate reference values.length c ∧ c.mem = memory ∧ c.out = out)
      (fun c => ReferenceCopyGlobals candidate reference values.length c ∧
        c.mem = ArrayBlocks.prefixMemory memory reference values values.length ∧ c.out = out)
      (8 * values.length + 9) := by
  have hready : HTB S referenceCopyReady
      (fun c => ReferenceCopyGlobals candidate reference values.length c ∧ c.mem = memory ∧ c.out = out)
      (fun c => ArrayBlocks.CopyGlobals candidate reference values.length c ∧
        ReferenceCopyGlobals candidate reference values.length c ∧ c.mem = memory ∧ c.out = out) 6 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨⟨hc, hr, hl⟩, hm, ho⟩
    refine ⟨AddrOK.of_memFree rfl, ?_⟩
    simp +decide [referenceCopyReady, mov, ArrayBlocks.CopyGlobals, ReferenceCopyGlobals, hc, hr, hl, hm, ho]
  have hcopy := (ArrayBlocks.copyArray_spec (out := out) hvalues hsep hS).frameReg
    (show RegIndep (wregs ArrayBlocks.copyArray) (ReferenceCopyGlobals candidate reference values.length) by
      indep [ReferenceCopyGlobals, ArrayBlocks.copyArray, ArrayBlocks.copyBody])
  have hcopy' : HTB S ArrayBlocks.copyArray
      (fun c => ArrayBlocks.CopyGlobals candidate reference values.length c ∧
        ReferenceCopyGlobals candidate reference values.length c ∧ c.mem = memory ∧ c.out = out)
      (fun c => ReferenceCopyGlobals candidate reference values.length c ∧
        c.mem = ArrayBlocks.prefixMemory memory reference values values.length ∧ c.out = out)
      (values.length * 8 + 3) := by
    refine hcopy.mono (fun c hc => ⟨⟨hc.1, hc.2.2⟩, hc.2.1⟩)
      (fun c hc => ⟨hc.2, hc.1.2.1, hc.1.2.2⟩) (by omega)
  exact (hready.seq hcopy').mono (fun c hc => hc) (fun c hc => hc) (by omega)

def dualTruthValues (n : ℕ) (σ : Assignment) : List ℕ :=
  (List.range (2 * n)).map fun u => if TwoSat.nodeVal σ u then 1 else 0

@[simp] theorem dualTruthValues_length (n : ℕ) (σ : Assignment) :
    (dualTruthValues n σ).length = 2 * n := by simp [dualTruthValues]

theorem TruthTable.array {memory : ℕ → ℕ} {base n : ℕ} {σ : Assignment}
    (h : TruthTable memory base n σ) : Arr memory base (dualTruthValues n σ) :=
  (show Tab memory base (2 * n) (fun u => if TwoSat.nodeVal σ u then 1 else 0) from h).toArr

theorem referenceCopy_truth {candidate reference n : ℕ} {memory : ℕ → ℕ} {σ : Assignment}
    (h : TruthTable memory candidate n σ)
    (hsep : reference + 2 * n ≤ candidate ∨ candidate + 2 * n ≤ reference) :
    let next := ArrayBlocks.prefixMemory memory reference (dualTruthValues n σ) (2 * n)
    TruthTable next reference n σ ∧ TruthTable next candidate n σ ∧
      SameOn (fun a => a < reference ∨ reference + 2 * n ≤ a) memory next := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    have ha := ArrayBlocks.prefixMemory_array memory reference (dualTruthValues n σ)
    have hget := ha.getD (i := u) (by simpa using hu)
    simpa [dualTruthValues, List.getD_eq_getElem?_getD, hu] using hget
  · intro u hu
    rw [ArrayBlocks.prefixMemory_outside (by rcases hsep with h | h <;> omega)]
    exact h u hu
  · intro a ha
    exact ArrayBlocks.prefixMemory_outside ha

end STACS2027.Runtimes.BoundedCost
