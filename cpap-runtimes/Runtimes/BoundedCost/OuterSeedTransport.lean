module

public import Runtimes.BoundedCost.OuterRepresentation
import Mathlib.Tactic

/-! Building a compression seed preserves all outer-scan input tables and
supplies the exact forced-literal snapshot and deleted occurrence count. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3 Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem globals_seed_frame {layout : CompilerLayout} {n m k depth S time : ℕ} {c c' : Config}
    (hg : Compiler.Globals layout n m k depth (registerView callerRegister c))
    (he : ExecB S (onCallerRegisters compressionSeedSetup) c time c') :
    Compiler.Globals layout n m k depth (registerView callerRegister c') := by
  apply Compiler.globals_reg_frame hg
  intro r hr
  have hcases : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 220 ∨
      r = 222 ∨ r = 223 ∨ r = 225 ∨ r = 226 ∨ r = 300 ∨ r = 344 ∨ r = 345 ∨
      r = 350 ∨ r = 400 ∨ r = 406 ∨ r = 430 ∨ r = 433 ∨ r = 434 ∨ r = 435 := by
    simpa [Compiler.globalRegisters] using hr
  apply he.reg_frame
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact not_mem_renameRegisters_wregs callerRegister_injective (by decide)

theorem outerBasic_seed_transport {F : Stmt} {layout : CompilerLayout}
    {nodes S budget depth processed time : ℕ} {original : CNF} {τ : Assignment}
    {rows : List (Bool × Clause)} {special : CNF} {oldOutput digits : List ℕ} {c₀ c : Config}
    (hgeo : OuterGeometry S layout nodes original.length depth special.length)
    (hrows : rows.length = original.length)
    (hcodes : (TwoSat.codes original).length ≤ 2 * original.length)
    (hspecial : (TwoSat.codes special).length ≤ 2 * special.length)
    (hb : OuterBasic F layout nodes original τ rows special budget depth processed oldOutput digits c₀)
    (he : ExecB S (onCallerRegisters compressionSeedSetup) c₀ time c)
    (hp : SeedScanInv layout.special layout.outerDigits layout.seedForced nodes budget
      (seedRowsOf digits special) c₀.mem c₀.out special.length (registerView callerRegister c)) :
    OuterBasic F layout nodes original τ rows special budget depth processed oldOutput digits c := by
  obtain ⟨hg, hc, hr, hz, ho, hbase, hspecialArray, hob, hol, hk, hdigits, hlen, hcount, hprocessed, halive⟩ := hb
  obtain ⟨hinner, hseedSpecial, hspecialDigits, houterInner⟩ := hgeo
  obtain ⟨hcut, hlabels, hbaseSeed, hseedInner, hinnerOutput⟩ := hinner
  obtain ⟨hhigh, hformula, hactive, hcandidate, href, hforced, hlabelsOutput, houtput⟩ := hcut
  have hf := hp.2.2.1
  refine ⟨globals_seed_frame hg he, ?_, ?_, hz.caller_exec he, hp.2.2.2.2.trans ho,
    ?_, ?_, ?_, ?_, ?_, ?_, hlen, ?_, ?_, ?_⟩
  · intro i hi
    exact (hf _ (by unfold OutsideCells; omega)).trans (hc i hi)
  · intro u hu
    exact (hf _ (by unfold OutsideCells; omega)).trans (hr u hu)
  · intro i hi
    have hi' : i < original.length := by simpa [maskWords_length, hrows] using hi
    exact (hf _ (by unfold OutsideCells; omega)).trans (hbase i hi)
  · intro i hi
    exact (hf _ (by unfold OutsideCells; omega)).trans (hspecialArray i hi)
  · exact (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hob
  · exact (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hol
  · exact (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hk
  · intro i hi
    exact (hf _ (by unfold OutsideCells; omega)).trans (hdigits i hi)
  · exact (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hcount
  · exact (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hprocessed
  · exact (he.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans halive

theorem seedForced_snapshot {base nodes count : ℕ} {memory : ℕ → ℕ}
    {rows : List CompressionSeedRow} (h : Tab memory base (2 * nodes) (seedForcedValue rows count)) :
    Arr memory base (forcedWords nodes (fun u => seedForcedValue rows count u == 1)) := by
  apply ForcedTable.array
  intro u hu
  have hbinary : seedForcedValue rows count u = 0 ∨ seedForcedValue rows count u = 1 := by
    unfold seedForcedValue
    split_ifs <;> simp
  rcases hbinary with hzero | hone
  · simpa only [hzero, Nat.reduceBEq, Bool.false_eq_true, ite_false] using h u hu
  · simpa only [hone, Nat.reduceBEq, ite_true] using h u hu

theorem outerSeed_spec {F : Stmt} {layout : CompilerLayout}
    {nodes S budget depth processed : ℕ} {original : CNF} {τ : Assignment}
    {rows : List (Bool × Clause)} {special : CNF} {oldOutput digits : List ℕ}
    (hf : TwoSat.IsTwoCNF nodes original) (hs : TwoSat.IsTwoCNF nodes special)
    (hgeo : OuterGeometry S layout nodes original.length depth special.length)
    (hrows : rows.length = original.length) (hvalid : ∀ d ∈ digits, d < 3) :
    HTB S (onCallerRegisters compressionSeedSetup)
      (OuterRep F layout nodes original τ rows special budget depth processed oldOutput none digits)
      (fun c => OuterRep F layout nodes original τ rows special budget depth processed oldOutput none digits c ∧
        Arr c.mem layout.seedForced (forcedWords nodes
          (fun u => seedForcedValue (seedRowsOf digits special) special.length u == 1)) ∧
        c.reg (callerRegister seedDeleted) = seedDeletedCount (seedRowsOf digits special) special.length)
      (12 * nodes + 44 * special.length + 11) := by
  intro c₀ ⟨hb, ha⟩
  obtain ⟨hg, hc, hr, hz, ho, hbase, hspecialArray, hob, hol, hk, hdigits, hlen, hcount, hp, halive⟩ := hb
  have hmem := compressionSeedCaller_spec special hs digits hlen hvalid
    (show DisjointCells layout.seedForced (2 * nodes) layout.special (2 * special.length) ∧
      DisjointCells layout.seedForced (2 * nodes) layout.outerDigits special.length by
      obtain ⟨hinner, hseed, hspecial, houter⟩ := hgeo
      unfold DisjointCells
      exact ⟨Or.inl hseed, Or.inl (by omega)⟩)
    (show layout.special + 2 * special.length ≤ S ∧
      layout.outerDigits + special.length ≤ S ∧ layout.seedForced + 2 * nodes ≤ S by
      obtain ⟨⟨hcut, hl, hb, hs, hd⟩, hseed, hspecial, houter⟩ := hgeo
      have hout := hcut.outputSpace
      omega) c₀
    ⟨hg.special, hg.outerDigits, hg.seedForced, hg.nodes, hg.budget, hcount⟩
    hspecialArray hdigits
  obtain ⟨c, time, he, hp, ht⟩ := hmem c₀ rfl
  refine ⟨c, time, he, ?_, ht⟩
  have hb' := outerBasic_seed_transport hgeo hrows (le_of_eq (TwoSat.length_codes hf))
    (le_of_eq (TwoSat.length_codes hs))
    (show OuterBasic F layout nodes original τ rows special budget depth processed oldOutput digits c₀ from
      ⟨hg, hc, hr, hz, ho, hbase, hspecialArray, hob, hol, hk, hdigits, hlen, hcount,
        by assumption, halive⟩) he hp.1
  exact ⟨⟨hb', (he.reg_frame
    (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans ha⟩,
    seedForced_snapshot hp.1.2.1, hp.1.2.2.2.1⟩

end STACS2027.Runtimes.BoundedCost
