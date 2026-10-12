module

public import Outerplanar.RAM.BoundedLib
public import Outerplanar.RAM.Layout
import Mathlib.Tactic

/-! Linear bounded RAM array initialization and restoration blocks. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.ArrayBlocks

open STACS2027 STACS2027.RAM

abbrev sourceBase : ℕ := 410
abbrev targetBase : ℕ := 411
abbrev arrayLength : ℕ := 412
abbrev index : ℕ := 413
abbrev value : ℕ := 414
abbrev fillValue : ℕ := 415

def prefixMemory (memory : ℕ → ℕ) (target : ℕ) (values : List ℕ) (j : ℕ) : ℕ → ℕ :=
  fun a => if target ≤ a ∧ a < target + j then values.getD (a - target) 0 else memory a

theorem prefixMemory_zero (memory : ℕ → ℕ) (target : ℕ) (values : List ℕ) :
    prefixMemory memory target values 0 = memory := by
  funext a; simp [prefixMemory]

theorem prefixMemory_outside {memory : ℕ → ℕ} {target j a : ℕ} {values : List ℕ}
    (ha : a < target ∨ target + j ≤ a) : prefixMemory memory target values j a = memory a := by
  simp [prefixMemory]; omega

theorem prefixMemory_succ (memory : ℕ → ℕ) (target : ℕ) (values : List ℕ) (j : ℕ) :
    upd (prefixMemory memory target values j) (target + j) (values.getD j 0) =
      prefixMemory memory target values (j + 1) := by
  funext a
  by_cases he : a = target + j
  · subst a; simp [prefixMemory]
  · have hiff : (target ≤ a ∧ a < target + (j + 1)) ↔ (target ≤ a ∧ a < target + j) := by omega
    simp [upd_apply, he, prefixMemory, hiff]

theorem prefixMemory_array (memory : ℕ → ℕ) (target : ℕ) (values : List ℕ) :
    Arr (prefixMemory memory target values values.length) target values := by
  intro i hi
  rw [prefixMemory, if_pos (by omega), Nat.add_sub_cancel_left]
  exact RAM.getD_eq_getElem' hi

def copyBody : Stmt := .seq (ld value sourceBase index) (st targetBase index value)
def copyArray : Stmt := forUp index arrayLength copyBody
def fillBody : Stmt := st targetBase index fillValue
def fillArray : Stmt := forUp index arrayLength fillBody

def CopyGlobals (source target length : ℕ) (c : Config) : Prop :=
  c.reg sourceBase = source ∧ c.reg targetBase = target ∧ c.reg arrayLength = length

def CopyInv (source target : ℕ) (values : List ℕ) (memory : ℕ → ℕ) (out : List ℕ)
    (j : ℕ) (c : Config) : Prop :=
  CopyGlobals source target values.length c ∧
    c.mem = prefixMemory memory target values j ∧ c.out = out

theorem copyBody_spec {S source target : ℕ} {values : List ℕ} {memory : ℕ → ℕ}
    {out : List ℕ} (hvalues : Arr memory source values)
    (hsep : target + values.length ≤ source ∨ source + values.length ≤ target)
    (hS : source + values.length ≤ S ∧ target + values.length ≤ S)
    (j : ℕ) (hj : j < values.length) :
    HTB S copyBody
      (fun c => CopyInv source target values memory out j c ∧
        c.reg index = j ∧ c.reg arrayLength = values.length)
      (fun c => CopyInv source target values memory out (j + 1) c ∧
        c.reg index = j ∧ c.reg arrayLength = values.length) 4 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨⟨hs, ht, hn⟩, hm, ho⟩, hi, _⟩
  have hread : c.mem (source + j) = values.getD j 0 := by
    rw [hm, prefixMemory_outside (by rcases hsep with h | h <;> omega)]
    exact hvalues.getD hj
  refine ⟨?_, ?_⟩
  · addr_ok [copyBody, hs, ht, hi]
  · refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide only [copyBody, CopyInv, CopyGlobals, run_seq', run_ld, run_st,
      setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, setReg_out, setMem_out, hs, ht, hi, hn, hm, ho,
      hread, prefixMemory_succ, ↓reduceIte]

theorem copyArray_spec {S source target : ℕ} {values : List ℕ} {memory : ℕ → ℕ}
    {out : List ℕ} (hvalues : Arr memory source values)
    (hsep : target + values.length ≤ source ∨ source + values.length ≤ target)
    (hS : source + values.length ≤ S ∧ target + values.length ≤ S) :
    HTB S copyArray
      (fun c => CopyGlobals source target values.length c ∧ c.mem = memory ∧ c.out = out)
      (fun c => CopyGlobals source target values.length c ∧
        c.mem = prefixMemory memory target values values.length ∧ c.out = out)
      (values.length * 8 + 3) := by
  have hloop := HTB.forUpC (S := S) (i := index) (n := arrayLength)
    (N := values.length) (body := copyBody) (CopyInv source target values memory out) 4
    (by decide) (by decide) (by decide) (fun _ => by indep [CopyInv, CopyGlobals])
    (fun j hj => copyBody_spec hvalues hsep hS j hj)
  refine hloop.mono ?_ (fun c hc => hc.1) (by omega)
  intro c ⟨hg, hm, ho⟩
  exact ⟨⟨hg, by simpa [prefixMemory_zero] using hm, ho⟩, hg.2.2⟩

def FillGlobals (target length fill : ℕ) (c : Config) : Prop :=
  c.reg targetBase = target ∧ c.reg arrayLength = length ∧ c.reg fillValue = fill

def FillInv (target length fill : ℕ) (memory : ℕ → ℕ) (out : List ℕ)
    (j : ℕ) (c : Config) : Prop :=
  FillGlobals target length fill c ∧
    c.mem = prefixMemory memory target (List.replicate length fill) j ∧ c.out = out

theorem fillBody_spec {S target length fill : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hS : target + length ≤ S) (j : ℕ) (hj : j < length) :
    HTB S fillBody
      (fun c => FillInv target length fill memory out j c ∧
        c.reg index = j ∧ c.reg arrayLength = length)
      (fun c => FillInv target length fill memory out (j + 1) c ∧
        c.reg index = j ∧ c.reg arrayLength = length) 2 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨⟨ht, hn, hv⟩, hm, ho⟩, hi, _⟩
  have hfill : (List.replicate length fill).getD j 0 = fill := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hj, Option.getD_some]
  have hstep : upd (prefixMemory memory target (List.replicate length fill) j)
      (target + j) fill = prefixMemory memory target (List.replicate length fill) (j + 1) := by
    simpa only [hfill] using prefixMemory_succ memory target (List.replicate length fill) j
  refine ⟨?_, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · addr_ok [fillBody, ht, hi]
  all_goals simp +decide only [fillBody, FillGlobals, FillInv, run_st, setReg_reg,
    setReg_mem, setMem_reg, setMem_mem_upd, setReg_out, setMem_out,
    ht, hn, hi, hv, hm, ho, ↓reduceIte, hstep]

theorem fillArray_spec {S target length fill : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hS : target + length ≤ S) :
    HTB S fillArray
      (fun c => FillGlobals target length fill c ∧ c.mem = memory ∧ c.out = out)
      (fun c => FillGlobals target length fill c ∧
        c.mem = prefixMemory memory target (List.replicate length fill) length ∧ c.out = out)
      (length * 6 + 3) := by
  have hloop := HTB.forUpC (S := S) (i := index) (n := arrayLength)
    (N := length) (body := fillBody) (FillInv target length fill memory out) 2
    (by decide) (by decide) (by decide) (fun _ => by indep [FillInv, FillGlobals])
    (fun j hj => fillBody_spec hS j hj)
  refine hloop.mono ?_ (fun c hc => hc.1) (by omega)
  intro c ⟨hg, hm, ho⟩
  exact ⟨⟨hg, by simpa [prefixMemory_zero] using hm, ho⟩, hg.2.1⟩

end STACS2027.Runtimes.BoundedCost.ArrayBlocks
