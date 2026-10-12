module

public import Runtimes.BoundedCost.ArrayBlocks
public import Runtimes.BoundedCost.BranchRegisters
import Mathlib.Tactic

/-! Concrete initialization of the digit arrays and separate controls used by
the inner path scan and outer compression scan. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.LoopHeaders

open STACS2027 STACS2027.RAM STACS2027.RAM.P3

def inputBase (inner : Bool) : ℕ := if inner then 344 else 433
def inputDepth (inner : Bool) : ℕ := if inner then 345 else 431
def controlBase (inner : Bool) : ℕ := if inner then 532 else rOB
def controlDepth (inner : Bool) : ℕ := if inner then 533 else rOL

def ready (inner : Bool) : Stmt :=
  .seq (mov (controlBase inner) (inputBase inner))
    (.seq (mov (controlDepth inner) (inputDepth inner))
      (.seq (.const rK 3)
        (.seq (mov ArrayBlocks.targetBase (inputBase inner))
          (.seq (mov ArrayBlocks.arrayLength (inputDepth inner)) (.const ArrayBlocks.fillValue 0)))))

def program (inner : Bool) : Stmt := .seq (ready inner) ArrayBlocks.fillArray

def Globals (inner : Bool) (base depth : ℕ) (c : Config) : Prop :=
  c.reg (inputBase inner) = base ∧ c.reg (inputDepth inner) = depth ∧
    c.reg (controlBase inner) = base ∧ c.reg (controlDepth inner) = depth ∧ c.reg rK = 3

theorem program_spec (inner : Bool) {S base depth : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hS : base + depth ≤ S) :
    HTB S (program inner)
      (fun c => c.reg (inputBase inner) = base ∧ c.reg (inputDepth inner) = depth ∧
        c.mem = memory ∧ c.out = out)
      (fun c => Globals inner base depth c ∧
        c.mem = ArrayBlocks.prefixMemory memory base (List.replicate depth 0) depth ∧
        Arr c.mem base (List.replicate depth 0) ∧ c.out = out)
      (6 * depth + 13) := by
  have hready : HTB S (ready inner)
      (fun c => c.reg (inputBase inner) = base ∧ c.reg (inputDepth inner) = depth ∧
        c.mem = memory ∧ c.out = out)
      (fun c => ArrayBlocks.FillGlobals base depth 0 c ∧ c.mem = memory ∧ c.out = out ∧
        Globals inner base depth c) 10 := by
    refine HTB.run_le (by cases inner <;> decide) (by cases inner <;> decide) ?_
    rintro c ⟨hb, hd, hm, ho⟩
    refine ⟨AddrOK.of_memFree (by cases inner <;> decide), ?_⟩
    cases inner <;> simp +decide only [ready, Globals, inputBase, inputDepth, controlBase, controlDepth,
      ArrayBlocks.FillGlobals, Bool.false_eq_true, ite_true, ite_false,
      run_seq', run_mov, run_const, setReg_reg, setReg_mem, setReg_out, hb, hd, hm, ho, ↓reduceIte]
    all_goals simp only [inputBase, inputDepth, ite_true, ite_false, Bool.false_eq_true] at hb hd
    all_goals simp_all
  have hgi : RegIndep (wregs ArrayBlocks.fillArray) (Globals inner base depth) := by
    cases inner <;> indep [Globals, inputBase, inputDepth, controlBase, controlDepth,
      ArrayBlocks.fillArray, ArrayBlocks.fillBody, forUp, upLoop, st, inc, addc]
  have hf := (ArrayBlocks.fillArray_spec (fill := 0) (memory := memory) (out := out) hS).frameReg hgi
  have hf' : HTB S ArrayBlocks.fillArray
      (fun c => ArrayBlocks.FillGlobals base depth 0 c ∧ c.mem = memory ∧ c.out = out ∧
        Globals inner base depth c)
      (fun c => Globals inner base depth c ∧
        c.mem = ArrayBlocks.prefixMemory memory base (List.replicate depth 0) depth ∧
        Arr c.mem base (List.replicate depth 0) ∧ c.out = out) (depth * 6 + 3) := by
    refine hf.mono (fun c hc => ⟨⟨hc.1, hc.2.1, hc.2.2.1⟩, hc.2.2.2⟩) ?_ (by omega)
    rintro c ⟨⟨_, hm, ho⟩, hg⟩
    refine ⟨hg, hm, ?_, ho⟩
    rw [hm]
    simpa only [List.length_replicate] using ArrayBlocks.prefixMemory_array memory base (List.replicate depth 0)
  exact (hready.seq hf').weaken (by omega)

end STACS2027.Runtimes.BoundedCost.LoopHeaders
