module

public import Runtimes.BoundedCost.ReferenceCopyRAM
public import Runtimes.BoundedCost.PrefixMaskRAM
public import Runtimes.BoundedCost.CallerRegisters
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

def prefixCheck : Stmt := .seq copyReference (.seq prefixMaskProgram searchScan)

def PrefixCheckGlobals (formula active candidate reference n m processed : ℕ) (c : Config) : Prop :=
  SearchScanGlobals formula active candidate reference m c ∧
    c.reg prefixMaskProcessed = processed ∧ c.reg referenceCopyLength = 2 * n

def PrefixCheckFrame (active reference n m a : ℕ) : Prop :=
  OutsideCells active m a ∧ OutsideCells reference (2 * n) a

def PrefixCheckResult (formula active candidate reference n processed : ℕ)
    (f : CNF) (σ : Assignment) (c₀ c : Config) : Prop :=
  PrefixCheckGlobals formula active candidate reference n f.length processed c ∧
  Arr c.mem formula (TwoSat.codes f) ∧ TruthTable c.mem candidate n σ ∧
  TruthTable c.mem reference n σ ∧ MaskTable c.mem active (prefixOccurrences f processed) ∧
  SearchSummaryRep (summarizePrefix (searchRowsOf σ σ (prefixOccurrences f processed)) f.length) c ∧
  c.reg scanUnsatisfied = unsatisfiedCount σ (f.take processed) ∧
  SameOn (PrefixCheckFrame active reference n f.length) c₀.mem c.mem ∧
  c.out = c₀.out ∧ Frame prefixCheck c₀ c

theorem prefixCheckGlobals_indep_copy (formula active candidate reference n m processed : ℕ) :
    RegIndep (wregs copyReference)
      (PrefixCheckGlobals formula active candidate reference n m processed) := by
  indep [PrefixCheckGlobals, SearchScanGlobals, copyReference, referenceCopyReady,
    ArrayBlocks.copyArray, ArrayBlocks.copyBody, forUp, upLoop, wregs, mov, ld, st, inc, addc]

theorem prefixCheckGlobals_indep_mask (formula active candidate reference n m processed : ℕ) :
    RegIndep (wregs prefixMaskProgram)
      (PrefixCheckGlobals formula active candidate reference n m processed) := by
  indep [PrefixCheckGlobals, SearchScanGlobals, prefixMaskProgram, prefixMaskBody,
    forUp, upLoop, wregs, st, inc, addc]

theorem prefixCheckGlobals_indep_scan (formula active candidate reference n m processed : ℕ) :
    RegIndep (wregs searchScan)
      (PrefixCheckGlobals formula active candidate reference n m processed) := by
  indep [PrefixCheckGlobals, SearchScanGlobals, searchScan, searchScanInit, searchScanBody,
    searchScanUnsatisfied, searchScanRecordConflict, forUp, upLoop, wregs, ld, st, inc, addc, mov]

/-- The actual prefix test refreshes its reference table and occurrence mask,
then performs one readonly clause scan. -/
theorem prefixCheck_spec {S formula active candidate reference n processed : ℕ}
    {f : CNF} {σ : Assignment} (hf : TwoSat.IsTwoCNF n f)
    (hgeo : formula + 2 * f.length ≤ active ∧ active + f.length ≤ candidate ∧
      candidate + 2 * n ≤ reference ∧ reference + 2 * n ≤ S)
    (c₀ : Config) (hg : PrefixCheckGlobals formula active candidate reference n f.length processed c₀)
    (hcodes : Arr c₀.mem formula (TwoSat.codes f)) (htruth : TruthTable c₀.mem candidate n σ) :
    HTB S prefixCheck (· = c₀)
      (PrefixCheckResult formula active candidate reference n processed f σ c₀)
      (16 * n + 116 * f.length + 20) := by
  intro c hc
  subst c
  have hsep : candidate + 2 * n ≤ reference := hgeo.2.2.1
  have hvalues := htruth.array
  have hcopy := copyReference_spec (out := c₀.out) hvalues
    (Or.inr (by simpa using hsep))
    (show candidate + (dualTruthValues n σ).length ≤ S ∧
      reference + (dualTruthValues n σ).length ≤ S by simpa using (show candidate + 2 * n ≤ S ∧ reference + 2 * n ≤ S by omega))
  obtain ⟨c₁, t₁, he₁, hp₁, ht₁⟩ := hcopy c₀
    ⟨⟨hg.1.2.2.1, hg.1.2.2.2.1, by simpa using hg.2.2⟩, rfl, rfl⟩
  have hg₁ := (prefixCheckGlobals_indep_copy formula active candidate reference n f.length processed).exec he₁.exec hg
  obtain ⟨hr₁, hc₁, hf₁⟩ := referenceCopy_truth htruth (Or.inr hsep)
  have hm₁ : c₁.mem = ArrayBlocks.prefixMemory c₀.mem reference (dualTruthValues n σ) (2 * n) := by
    simpa using hp₁.2.1
  rw [← hm₁] at hr₁ hc₁ hf₁
  have hcodes₁ : Arr c₁.mem formula (TwoSat.codes f) := by
    intro i hi
    have hlen := TwoSat.length_codes hf
    exact (hf₁ _ (by rw [hlen] at hi; omega)).trans (hcodes i hi)
  obtain ⟨c₂, t₂, he₂, hp₂, ht₂⟩ := prefixMaskProgram_spec (memory := c₁.mem) (out := c₁.out)
      (S := S) (active := active) (count := f.length) (processed := processed) (by omega) c₁
      ⟨⟨hg₁.1.2.1, hg₁.1.2.2.2.2, hg₁.2.1⟩, rfl, rfl⟩
  have hg₂ := (prefixCheckGlobals_indep_mask formula active candidate reference n f.length processed).exec he₂.exec hg₁
  have hmask := prefixMask_table (f := f) hp₂.2.1
  have hcodes₂ : Arr c₂.mem formula (TwoSat.codes f) := by
    intro i hi
    have hlen := TwoSat.length_codes hf
    exact (hp₂.2.2.1 _ (by unfold OutsideCells; rw [hlen] at hi; omega)).trans (hcodes₁ i hi)
  have hc₂ : TruthTable c₂.mem candidate n σ := by
    intro u hu
    exact (hp₂.2.2.1 _ (by unfold OutsideCells; omega)).trans (hc₁ u hu)
  have hr₂ : TruthTable c₂.mem reference n σ := by
    intro u hu
    exact (hp₂.2.2.1 _ (by unfold OutsideCells; omega)).trans (hr₁ u hu)
  have hrows : ∀ row ∈ prefixOccurrences f processed,
      row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < n := by
    intro row hrow
    exact hf row.2 (by rw [← prefixOccurrences_clauses f processed]; exact List.mem_map_of_mem hrow)
  have hcontract := contractionRowsMem_of_tables hrows
    (by simpa using hcodes₂) hmask hr₂
  have hscanMem := searchRowsMem_of_contraction (τ := σ) (δ := σ)
    (fun row hrow => (hrows row hrow).1) hcontract hc₂
  have hscan := searchScan_spec hscanMem
    (show formula + 2 * (searchRowsOf σ σ (prefixOccurrences f processed)).length ≤ S ∧
      active + (searchRowsOf σ σ (prefixOccurrences f processed)).length ≤ S ∧
      candidate + 2 * n ≤ S ∧ reference + 2 * n ≤ S by simp; omega)
  obtain ⟨c₃, t₃, he₃, hp₃, ht₃⟩ := hscan c₂ ⟨by simpa using hg₂.1, rfl⟩
  have hg₃ := (prefixCheckGlobals_indep_scan formula active candidate reference n f.length processed).exec he₃.exec hg₂
  have he : ExecB S prefixCheck c₀ (t₁ + (t₂ + t₃)) c₃ := .seq he₁ (.seq he₂ he₃)
  refine ⟨c₃, _, he, ?_, ?_⟩
  · refine ⟨hg₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he.frame.out (by decide), he.frame⟩
    · rw [hp₃.2.1]; exact hcodes₂
    · rw [hp₃.2.1]; exact hc₂
    · rw [hp₃.2.1]; exact hr₂
    · rw [hp₃.2.1]; exact hmask
    · simpa using hp₃.2.2
    · have hsemantic := summarizePrefix_unsatisfied_semantic σ σ (prefixOccurrences f processed)
        (fun row hrow => (hrows row hrow).1)
      have hreg : c₃.reg scanUnsatisfied =
          (summarizePrefix (searchRowsOf σ σ (prefixOccurrences f processed))
            (prefixOccurrences f processed).length).unsatisfied := by simpa using hp₃.2.2.1
      simpa [activeOccurrences_prefixOccurrences] using hreg.trans hsemantic
    · intro a ha
      rw [hp₃.2.1, hp₂.2.2.1 a ha.1, hf₁ a ha.2]
  · simp only [dualTruthValues_length, searchRowsOf_length, prefixOccurrences_length] at ht₁ ht₃
    omega

def prefixCheckCaller : Stmt := onCallerRegisters prefixCheck

/-- Register relocation preserves the exact computation and provides the full
caller register frame. In particular every class-zero register survives. -/
theorem prefixCheckCaller_spec {S formula active candidate reference n processed : ℕ}
    {f : CNF} {σ : Assignment} (hf : TwoSat.IsTwoCNF n f)
    (hgeo : formula + 2 * f.length ≤ active ∧ active + f.length ≤ candidate ∧
      candidate + 2 * n ≤ reference ∧ reference + 2 * n ≤ S)
    (c₀ : Config)
    (hg : PrefixCheckGlobals formula active candidate reference n f.length processed
      (registerView callerRegister c₀))
    (hcodes : Arr c₀.mem formula (TwoSat.codes f)) (htruth : TruthTable c₀.mem candidate n σ) :
    HTB S prefixCheckCaller (· = c₀)
      (fun c => PrefixCheckResult formula active candidate reference n processed f σ
        (registerView callerRegister c₀) (registerView callerRegister c) ∧
        Frame prefixCheckCaller c₀ c ∧ ∀ r, r % 4 = 0 → c.reg r = c₀.reg r)
      (16 * n + 116 * f.length + 20) := by
  have h := onCallerRegisters_htb (prefixCheck_spec hf hgeo
    (registerView callerRegister c₀) hg hcodes htruth)
  refine (h.withFrame c₀).mono (fun c hc => ⟨by rw [hc], hc⟩) ?_ (by omega)
  rintro c ⟨hr, hframe⟩
  refine ⟨hr, hframe, ?_⟩
  intro r hzero
  apply hframe.reg r
  rw [onCallerRegisters, renameRegisters_wregs]
  intro hmem
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hmem
  dsimp [callerRegister] at hj
  omega

end STACS2027.Runtimes.BoundedCost
