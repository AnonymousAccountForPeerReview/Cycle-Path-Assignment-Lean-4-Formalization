module

public import Runtimes.BoundedCost.CompressionSeedVectors
public import Runtimes.BoundedCost.CompressionSetupSemantics
public import Runtimes.BoundedCost.CompilerState
import Mathlib.Tactic

/-! Packed special occurrences and ternary digits provide the actual seed
program's complete input, including its precise deletion count and requirements. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

theorem compressionVector_total (special : CNF) (hf : Clauses2 special)
    (digits : List ℕ) (hlen : digits.length = special.length)
    (hdigits : ∀ d ∈ digits, d < 3) : ∃ branch, compressionVector digits special = some branch := by
  induction special generalizing digits with
  | nil =>
    have hz : digits = [] := by simpa using hlen
    subst digits
    exact ⟨(0, []), rfl⟩
  | cons clause special ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf clause (by simp))
    have ht : Clauses2 special := fun c hc => hf c (by simp [hc])
    cases digits with
    | nil => simp at hlen
    | cons d ds =>
      obtain ⟨branch, hb⟩ := ih ht ds (by simpa using hlen)
        (fun x hx => hdigits x (by simp [hx]))
      have hd : d = 0 ∨ d = 1 ∨ d = 2 := by have := hdigits d (by simp); omega
      rcases hd with rfl | rfl | rfl
      · exact ⟨(branch.1 + 1, branch.2), by simp [compressionVector, hb]⟩
      · exact ⟨(branch.1, a :: branch.2), by simp [compressionVector, hb]⟩
      · exact ⟨(branch.1, b :: branch.2), by simp [compressionVector, hb]⟩

theorem clauseCodePairs_codes (special : CNF) (hf : Clauses2 special) :
    contractionArcCodes (special.map clauseCodePair) = TwoSat.codes special := by
  induction special with
  | nil => rfl
  | cons clause special ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf clause (by simp))
    have ht : Clauses2 special := fun c hc => hf c (by simp [hc])
    simpa [contractionArcCodes, clauseCodePair, TwoSat.codes] using ih ht

theorem seedRowsOf_getD (special : CNF) (hf : Clauses2 special) (digits : List ℕ)
    (hlen : digits.length = special.length) (i : ℕ) (hi : i < special.length) :
    let row := (seedRowsOf digits special).getD i default
    row.first = (TwoSat.codes special).getD (2 * i) 0 ∧
      row.second = (TwoSat.codes special).getD (2 * i + 1) 0 ∧
      row.choice = digits.getD i 0 := by
  induction special generalizing digits i with
  | nil => simp at hi
  | cons clause special ih =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hf clause (by simp))
    have ht : Clauses2 special := fun c hc => hf c (by simp [hc])
    cases digits with
    | nil => simp at hlen
    | cons d ds =>
      cases i with
      | zero => simp [seedRowsOf, TwoSat.codes]
      | succ i =>
        have h := ih ht ds (by simpa using hlen) i (by simpa using hi)
        simpa [seedRowsOf, TwoSat.codes, show 2 * (i + 1) = (2 * i + 1) + 1 by omega] using h

theorem seedRowsOf_tables {nodes specialBase digitBase : ℕ} {memory : ℕ → ℕ}
    (special : CNF) (hf : TwoSat.IsTwoCNF nodes special) (digits : List ℕ)
    (hlen : digits.length = special.length) (hdigits : ∀ d ∈ digits, d < 3)
    (hcodes : Arr memory specialBase (TwoSat.codes special))
    (harray : Arr memory digitBase digits) :
    CompressionSeedRowsMem specialBase digitBase nodes (seedRowsOf digits special) memory := by
  have hc : Clauses2 special := fun c hc => (hf c hc).1
  obtain ⟨branch, hb⟩ := compressionVector_total special hc digits hlen hdigits
  have hv := seedRowsOf_vector special hc digits branch hb
  intro i hi
  have his : i < special.length := by simpa [hv.1] using hi
  have hrow := seedRowsOf_getD special hc digits hlen i his
  have hbound := seedRowsOf_bounded special hf digits
    ((seedRowsOf digits special).getD i default)
    (by rw [← List.getElem_eq_getD (h := hi) default]; exact List.getElem_mem hi)
  have hid : i < digits.length := by omega
  refine ⟨hbound.1, hbound.2, ?_, ?_, ?_, ?_⟩
  · rw [hrow.2.2]
    have hm : digits.getD i 0 ∈ digits := by
      rw [← List.getElem_eq_getD (h := hid) 0]
      exact List.getElem_mem hid
    exact Nat.le_of_lt_succ (hdigits _ hm)
  · rw [hrow.1]
    exact hcodes.getD (by rw [TwoSat.length_codes hf]; omega)
  · rw [hrow.2.1]
    simpa only [Nat.add_assoc] using hcodes.getD (i := 2 * i + 1)
      (by rw [TwoSat.length_codes hf]; omega)
  · rw [hrow.2.2]
    exact harray.getD hid

theorem compressionSeedCaller_spec {S specialBase digitBase forcedBase nodes budget : ℕ}
    (special : CNF) (hf : TwoSat.IsTwoCNF nodes special) (digits : List ℕ)
    (hlen : digits.length = special.length) (hdigits : ∀ d ∈ digits, d < 3)
    (hsep : DisjointCells forcedBase (2 * nodes) specialBase (2 * special.length) ∧
      DisjointCells forcedBase (2 * nodes) digitBase special.length)
    (hspace : specialBase + 2 * special.length ≤ S ∧ digitBase + special.length ≤ S ∧
      forcedBase + 2 * nodes ≤ S)
    (c₀ : Config)
    (hg : CompressionSeedGlobals specialBase digitBase forcedBase nodes budget special.length
      (registerView callerRegister c₀))
    (hcodes : Arr c₀.mem specialBase (TwoSat.codes special))
    (harray : Arr c₀.mem digitBase digits) :
    HTB S (onCallerRegisters compressionSeedSetup) (· = c₀)
      (fun c => SeedScanInv specialBase digitBase forcedBase nodes budget
        (seedRowsOf digits special) c₀.mem c₀.out special.length (registerView callerRegister c) ∧
        Frame (onCallerRegisters compressionSeedSetup) c₀ c ∧
        ∀ r, c.reg (Flow.rl 0 r) = c₀.reg (Flow.rl 0 r))
      (12 * nodes + 44 * special.length + 11) := by
  have hc : Clauses2 special := fun c hc => (hf c hc).1
  obtain ⟨branch, hb⟩ := compressionVector_total special hc digits hlen hdigits
  have hlength := (seedRowsOf_vector special hc digits branch hb).1
  have hs := compressionSeedSetup_spec (budget := budget) (oldOutput := c₀.out)
    (seedRowsOf_tables special hf digits hlen hdigits hcodes harray)
    (by simpa [hlength] using hsep.1) (by simpa [hlength] using hsep.2)
    (by simpa [hlength] using hspace)
  have hp := onCallerRegisters_htb hs
  intro c hc
  subst c
  obtain ⟨d, time, he, hd, ht⟩ := hp c₀ ⟨by simpa [hlength] using hg, rfl, rfl⟩
  exact ⟨d, time, he, ⟨by simpa [hlength] using hd, he.frame,
    callerRegister_exec_zero he⟩, by simpa [hlength] using ht⟩

end STACS2027.Runtimes.BoundedCost
