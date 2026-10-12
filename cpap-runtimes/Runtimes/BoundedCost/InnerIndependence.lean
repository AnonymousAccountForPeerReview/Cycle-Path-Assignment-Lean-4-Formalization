module

public import Runtimes.BoundedCost.InnerRepresentation
import Mathlib.Tactic

/-! Independence of the semantic inner state from the bounded odometer and
power controls, whose physical register class is disjoint from flow state. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def innerControlWrites : List ℕ :=
  (innerCallerRegister wordIndex :: rT :: wregs (renameRegisters innerCallerRegister odo)) ++
    wregs (renameRegisters innerCallerRegister (powTo wordCount rOL))

theorem innerCallerRegister_mod (r : ℕ) : innerCallerRegister r % 4 = 3 := by
  simp [innerCallerRegister, callerRegister, Nat.add_mod]

theorem innerControlWrites_mod {r : ℕ} (hr : r ∈ innerControlWrites) : r % 4 = 3 := by
  simp only [innerControlWrites, List.mem_append, List.mem_cons, renameRegisters_wregs] at hr
  rcases hr with (h | h | h) | h
  · subst r; exact innerCallerRegister_mod _
  · subst r; decide
  all_goals
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
    exact innerCallerRegister_mod i

theorem innerRep_indep (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (depth globalBudget deleted : ℕ) (activeBits forcedBits oldOutput : List ℕ)
    (oldMemory : ℕ → ℕ) (answer : Option Assignment) (digits : List ℕ) :
    Indep innerControlWrites
      (InnerRep F layout nodes original τ depth globalBudget deleted activeBits forcedBits
        oldOutput oldMemory answer digits) := by
  rintro c c' ⟨hreg, hmem, hout⟩ ⟨hb, hans, hframe⟩
  rcases hb with ⟨hpath, hrestore, hactive, hforced, hob, hol, hk, hlength⟩
  have hpath' : PathBasic F layout nodes original τ digits oldOutput c' := by
    rcases hpath with ⟨hg, hc, hr, hz, ho, hd, hl, ha⟩
    refine ⟨?_, ?_, ?_, ?_, hout.trans ho, ?_, ?_, ?_⟩
    · rcases hg with ⟨hg, hcandidate, hregion, hspan⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rcases hg with ⟨hformula, hactive, href, hforced, hlabels, houtput, hn, hm⟩
        constructor
        all_goals first
          | exact (hreg _ (by decide)).trans hformula
          | exact (hreg _ (by decide)).trans hactive
          | exact (hreg _ (by decide)).trans href
          | exact (hreg _ (by decide)).trans hforced
          | exact (hreg _ (by decide)).trans hlabels
          | exact (hreg _ (by decide)).trans houtput
          | exact (hreg _ (by decide)).trans hn
          | exact (hreg _ (by decide)).trans hm
      · exact (hreg _ (by decide)).trans hcandidate
      · exact (hreg _ (by decide)).trans hregion
      · exact (hreg _ (by decide)).trans hspan
    · simpa only [hmem] using hc
    · simpa only [hmem] using hr
    · intro r hr
      have hn : Flow.rl 0 r ∉ innerControlWrites := by
        intro hm
        have hm' := innerControlWrites_mod hm
        have hz' := Flow.rl_mod (by decide : 0 < 4) r
        omega
      exact (hreg _ hn).trans (hz r hr)
    · exact (hreg _ (by decide)).trans hd
    · exact (hreg _ (by decide)).trans hl
    · simpa only [hmem] using ha
  refine ⟨⟨hpath', ?_, ?_, ?_, ?_, ?_, ?_, hlength⟩, ?_, ?_⟩
  · rcases hrestore with ⟨ha, hf, has, hfs, hm, hn, hbudget, hdeleted⟩
    exact ⟨(hreg _ (by decide)).trans ha, (hreg _ (by decide)).trans hf,
      (hreg _ (by decide)).trans has, (hreg _ (by decide)).trans hfs,
      (hreg _ (by decide)).trans hm, (hreg _ (by decide)).trans hn,
      (hreg _ (by decide)).trans hbudget, (hreg _ (by decide)).trans hdeleted⟩
  · simpa only [hmem] using hactive
  · simpa only [hmem] using hforced
  · exact (hreg _ (by decide)).trans hob
  · exact (hreg _ (by decide)).trans hol
  · exact (hreg _ (by decide)).trans hk
  · cases answer with
    | none => exact (hreg _ (by decide)).trans hans
    | some σ => exact ⟨(hreg _ (by decide)).trans hans.1, by simpa only [hmem] using hans.2⟩
  · simpa only [hmem] using hframe

end STACS2027.Runtimes.BoundedCost
