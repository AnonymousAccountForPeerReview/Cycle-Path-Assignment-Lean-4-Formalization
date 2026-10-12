module

public import Runtimes.BoundedCost.OccurrenceTables
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

abbrev prefixMaskIndex : ℕ := 480
abbrev prefixMaskTemporary : ℕ := 481
abbrev prefixMaskValue : ℕ := 482
abbrev prefixMaskActiveBase : ℕ := 202
abbrev prefixMaskClauseCount : ℕ := 201
abbrev prefixMaskProcessed : ℕ := 224

def prefixMaskBody : Stmt :=
  .seq (.sub prefixMaskTemporary prefixMaskProcessed prefixMaskIndex)
    (.seq (.ifz prefixMaskTemporary (.const prefixMaskValue 0) (.const prefixMaskValue 1))
      (st prefixMaskActiveBase prefixMaskIndex prefixMaskValue))

def prefixMaskProgram : Stmt := forUp prefixMaskIndex prefixMaskClauseCount prefixMaskBody

def PrefixMaskGlobals (active count processed : ℕ) (c : Config) : Prop :=
  c.reg prefixMaskActiveBase = active ∧ c.reg prefixMaskClauseCount = count ∧
    c.reg prefixMaskProcessed = processed

def PrefixMaskInv (active count processed : ℕ) (memory : ℕ → ℕ) (out : List ℕ)
    (j : ℕ) (c : Config) : Prop :=
  PrefixMaskGlobals active count processed c ∧
  Tab c.mem active j (fun i => if i < processed then 1 else 0) ∧
  SameOn (OutsideCells active j) memory c.mem ∧ c.out = out

theorem prefixMaskBody_spec {S active count processed : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hS : active + count ≤ S) (j : ℕ) (hj : j < count) :
    HTB S prefixMaskBody
      (fun c => PrefixMaskInv active count processed memory out j c ∧
        c.reg prefixMaskIndex = j ∧ c.reg prefixMaskClauseCount = count)
      (fun c => PrefixMaskInv active count processed memory out (j + 1) c ∧
        c.reg prefixMaskIndex = j ∧ c.reg prefixMaskClauseCount = count) 8 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hg, ht, hf, ho⟩, hi, hn⟩
  obtain ⟨ha, hc, hp⟩ := hg
  have hmem : (run prefixMaskBody c).mem = upd c.mem (active + j) (if j < processed then 1 else 0) := by
    by_cases hlt : j < processed
    · have hsub : processed - j ≠ 0 := by omega
      simp +decide [prefixMaskBody, st, ha, hp, hi, hlt, hsub]
    · have hsub : processed - j = 0 := by omega
      simp +decide [prefixMaskBody, st, ha, hp, hi, hlt, hsub]
  have hg' : PrefixMaskGlobals active count processed (run prefixMaskBody c) := by
    have h : RegIndep (wregs prefixMaskBody) (PrefixMaskGlobals active count processed) := by
      indep [PrefixMaskGlobals, prefixMaskBody]
    exact h.run (by decide) ⟨ha, hc, hp⟩
  have hi' : (run prefixMaskBody c).reg prefixMaskIndex = j :=
    (run_reg_of_not_mem (by decide) (by decide) c).trans hi
  refine ⟨?_, ⟨hg', ?_, ?_, ?_⟩, hi', hg'.2.1⟩
  · by_cases hlt : j < processed
    · have hsub : processed - j ≠ 0 := by omega
      addr_ok [prefixMaskBody, st, ha, hp, hi, hsub]
    · have hsub : processed - j = 0 := by omega
      addr_ok [prefixMaskBody, st, ha, hp, hi, hsub]
  · rw [hmem]
    exact (ht.upd_of_disjoint (by omega)).snoc (by simp)
  · intro a ha'
    rw [hmem]
    have hne : a ≠ active + j := by unfold OutsideCells at ha'; omega
    simp only [upd_apply, hne, ite_false]
    exact hf a (by unfold OutsideCells at *; omega)
  · exact (run_out_of_writes (by decide) (by decide) c).trans ho

/-- The actual bounded scan resets all occurrence bits to the selected prefix. -/
theorem prefixMaskProgram_spec {S active count processed : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hS : active + count ≤ S) :
    HTB S prefixMaskProgram
      (fun c => PrefixMaskGlobals active count processed c ∧ c.mem = memory ∧ c.out = out)
      (PrefixMaskInv active count processed memory out count) (12 * count + 3) := by
  have h := HTB.forUpC (S := S) (i := prefixMaskIndex) (n := prefixMaskClauseCount)
    (N := count) (body := prefixMaskBody) (PrefixMaskInv active count processed memory out) 8
    (by decide) (by decide) (by decide) (fun _ => by indep [PrefixMaskInv, PrefixMaskGlobals])
    (fun j hj => prefixMaskBody_spec hS j hj)
  refine h.mono ?_ (fun c hc => hc.1) (by omega)
  rintro c ⟨hg, hm, ho⟩
  refine ⟨⟨hg, by simp, ?_, ho⟩, hg.2.1⟩
  intro a ha
  exact congrFun hm a

def prefixOccurrences (f : CNF) (processed : ℕ) : List (Bool × Clause) :=
  List.ofFn fun i : Fin f.length => (decide (i.val < processed), f[i.val])

@[simp] theorem prefixOccurrences_length (f : CNF) (processed : ℕ) :
    (prefixOccurrences f processed).length = f.length := by simp [prefixOccurrences]

theorem prefixMask_table {memory : ℕ → ℕ} {active processed : ℕ} {f : CNF}
    (h : Tab memory active f.length (fun i => if i < processed then 1 else 0)) :
    MaskTable memory active (prefixOccurrences f processed) := by
  intro i hi
  have hi' : i < f.length := by simpa using hi
  simpa [prefixOccurrences] using h i hi'

@[simp] theorem prefixOccurrences_clauses (f : CNF) (processed : ℕ) :
    (prefixOccurrences f processed).map Prod.snd = f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [prefixOccurrences]

theorem activeOccurrences_prefixOccurrences (f : CNF) (processed : ℕ) :
    activeOccurrences (prefixOccurrences f processed) = f.take processed := by
  induction f generalizing processed with
  | nil => simp [prefixOccurrences, activeOccurrences]
  | cons c f ih =>
    cases processed with
    | zero =>
      simp [prefixOccurrences, List.ofFn_succ, activeOccurrences]
      simpa [prefixOccurrences] using ih 0
    | succ processed =>
      simp [prefixOccurrences, List.ofFn_succ, activeOccurrences]
      exact ih processed

end STACS2027.Runtimes.BoundedCost
