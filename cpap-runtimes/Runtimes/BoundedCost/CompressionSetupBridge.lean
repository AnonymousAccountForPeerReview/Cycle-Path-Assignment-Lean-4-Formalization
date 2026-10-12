module

public import Runtimes.BoundedCost.CompressionInputs
public import Runtimes.BoundedCost.PathRestoreTables
import Mathlib.Tactic

/-! The actual setup scan supplies the exact base occurrence snapshot and
packed special clauses used by the nested compression scans. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

theorem setupRowsOf_tables {n formula candidate : ℕ} {memory : ℕ → ℕ}
    (f : CNF) (hf : TwoSat.IsTwoCNF n f) (τ : Assignment)
    (hcodes : Arr memory formula (TwoSat.codes f))
    (htruth : TruthTable memory candidate n τ) :
    CompressionSetupRowsMem formula candidate n (setupRowsOf τ f) memory := by
  intro i hi
  have hi' : i < f.length := by simpa using hi
  obtain ⟨a, b, he, ha, hb, hx, hy⟩ := codes_clause_pair hf i hi'
  have hget : f.getD i [] = [a, b] := by
    rw [← List.getElem_eq_getD (h := hi') []]
    exact he
  have hrow : (setupRowsOf τ f).getD i default =
      (⟨TwoSat.code a, TwoSat.code b, evalLiteral τ a, evalLiteral τ b⟩ : CompressionSetupRow) := by
    rw [setupRowsOf_getD τ f i hi', hget]
    rfl
  rw [hrow]
  refine ⟨TwoSat.code_lt ha, TwoSat.code_lt hb, ?_, ?_, ?_, ?_⟩
  · exact (hcodes.getD (i := 2 * i) (by rw [TwoSat.length_codes hf]; omega)).trans hx
  · simpa only [Nat.add_assoc] using
      (hcodes.getD (i := 2 * i + 1) (by rw [TwoSat.length_codes hf]; omega)).trans hy
  · simpa only [TwoSat.nodeVal_code] using htruth (TwoSat.code a) (TwoSat.code_lt ha)
  · simpa only [TwoSat.nodeVal_code] using htruth (TwoSat.code b) (TwoSat.code_lt hb)

@[simp] theorem setupOccurrenceMask_length (τ : Assignment) (f : CNF) (p : ℕ) :
    (setupOccurrenceMask τ f p).length = f.length := by simp [setupOccurrenceMask]

theorem setupOccurrenceMask_clauses (τ : Assignment) (f : CNF) (p : ℕ) :
    (setupOccurrenceMask τ f p).map Prod.snd = f := by
  simpa only [setupOccurrenceMask, List.map_map, Function.comp_def] using map_getD_range f []

theorem setupOccurrenceMask_getD (τ : Assignment) (f : CNF) (p i : ℕ) (hi : i < f.length) :
    (setupOccurrenceMask τ f p).getD i default =
      (decide (i < p) && evalClause τ (f.getD i []), f.getD i []) := by
  simp [setupOccurrenceMask, List.getD_eq_getElem?_getD, hi]

theorem setupSnapshot_mask {active : ℕ} {memory : ℕ → ℕ}
    (τ : Assignment) (f : CNF) (processed : ℕ) (hf : Clauses2 f)
    (h : Tab memory active f.length (setupActiveValue (setupRowsOf τ f) processed)) :
    MaskTable memory active (setupOccurrenceMask τ f processed) := by
  intro i hi
  have hi' : i < f.length := by simpa using hi
  rw [List.getElem_eq_getD (h := hi) default, setupOccurrenceMask_getD τ f processed i hi']
  have ha := h i hi'
  rw [setupActiveValue_semantic τ f processed i hf hi'] at ha
  cases he : evalClause τ (f.getD i []) <;>
    by_cases hp : i < processed <;>
    simp only [he, hp, decide_true, decide_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, eq_self, and_false, and_true, true_and, false_and,
      ite_true, ite_false] at ha ⊢ <;> exact ha

theorem compressionSetupCaller_spec {S formula active candidate special snapshot processed n : ℕ}
    (f : CNF) (hf : TwoSat.IsTwoCNF n f) (τ : Assignment)
    (has : active + f.length ≤ snapshot ∨ snapshot + f.length ≤ active)
    (hap : active + f.length ≤ special ∨ special + 2 * f.length ≤ active)
    (hsp : snapshot + f.length ≤ special ∨ special + 2 * f.length ≤ snapshot)
    (hinput : ∀ a, (formula ≤ a ∧ a < formula + 2 * f.length) ∨
      (candidate ≤ a ∧ a < candidate + 2 * n) →
      setupOutside active snapshot special f.length f.length a)
    (hspace : formula + 2 * f.length ≤ S ∧ candidate + 2 * n ≤ S ∧
      active + f.length ≤ S ∧ snapshot + f.length ≤ S ∧ special + 2 * f.length ≤ S)
    (c₀ : Config)
    (hg : CompressionSetupGlobals formula active candidate special snapshot processed f.length
      (registerView callerRegister c₀))
    (hcodes : Arr c₀.mem formula (TwoSat.codes f))
    (htruth : TruthTable c₀.mem candidate n τ) :
    HTB S (onCallerRegisters compressionSetupScan) (· = c₀)
      (fun c => SetupScanInv formula active candidate special snapshot processed (setupRowsOf τ f)
        c₀.mem c₀.out f.length (registerView callerRegister c) ∧
        MaskTable c.mem active (setupOccurrenceMask τ f processed) ∧
        Arr c.mem snapshot (maskWords (setupOccurrenceMask τ f processed)) ∧
        TruthTable c.mem candidate n τ ∧
        Frame (onCallerRegisters compressionSetupScan) c₀ c ∧
        ∀ r, c.reg (Flow.rl 0 r) = c₀.reg (Flow.rl 0 r))
      (84 * f.length + 4) := by
  have hs := compressionSetupScan_spec (processed := processed) (oldOutput := c₀.out)
    (setupRowsOf_tables f hf τ hcodes htruth)
    (by simpa using has) (by simpa using hap) (by simpa using hsp)
    (by simpa using hinput) (by simpa using hspace)
  have hp := onCallerRegisters_htb hs
  intro c hc
  subst c
  obtain ⟨d, time, he, hd, ht⟩ := hp c₀ ⟨by simpa using hg, rfl, rfl⟩
  have hd' : SetupScanInv formula active candidate special snapshot processed (setupRowsOf τ f)
      c₀.mem c₀.out f.length (registerView callerRegister d) := by simpa using hd
  have hc : Clauses2 f := fun c hc => (hf c hc).1
  have hactive := setupSnapshot_mask τ f processed hc (by simpa using hd'.2.1)
  have hsnapshot := (setupSnapshot_mask τ f processed hc (by simpa using hd'.2.2.1)).array
  have hcandidate : TruthTable d.mem candidate n τ := by
    intro u hu
    exact (hd'.2.2.2.2.1 (candidate + u) (by
      simpa only [setupRowsOf_length] using
        hinput (candidate + u) (Or.inr ⟨by omega, by omega⟩))).trans (htruth u hu)
  exact ⟨d, time, he, ⟨hd', hactive, hsnapshot, hcandidate, he.frame,
    callerRegister_exec_zero he⟩, by simpa using ht⟩

end STACS2027.Runtimes.BoundedCost
