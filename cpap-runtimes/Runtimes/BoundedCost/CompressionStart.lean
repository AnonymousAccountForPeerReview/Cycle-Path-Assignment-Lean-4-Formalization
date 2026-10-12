module

public import Runtimes.BoundedCost.OuterHeader
public import Runtimes.BoundedCost.PrefixRAM
public import Runtimes.BoundedCost.CompressionSetupBridge
import Mathlib.Tactic

/-! The actual prefix trigger clears its success flag and partitions the
processed occurrences into the exact compression snapshot and special list. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def compressionStart : Stmt :=
  .seq (.const (callerRegister nodeSuccess) 0) (onCallerRegisters compressionSetupScan)

theorem compressionStart_spec {F : Stmt} {S constant budget index : ℕ} {f : CNF}
    {τ : Assignment} {oldOutput : List ℕ}
    (hf : TwoSat.IsTwoCNF (2 * f.length + 1) f)
    (hspace : (compilerLayout constant f.length budget).space ≤ S)
    (hi : index < f.length)
    (hold : unsatisfiedCount τ (f.take index) ≤ budget)
    (hnew : budget < unsatisfiedCount τ (f.take (index + 1))) :
    let layout := compilerLayout constant f.length budget
    let depth := min budget f.length + 1
    HTB S compressionStart
      (Compiler.CompressionReady F layout f budget depth oldOutput index τ)
      (OuterStart F layout (2 * f.length + 1) f τ (setupOccurrenceMask τ f (index + 1))
        (compressionSpecial τ (f.take index) (f.getD index [])) budget depth (index + 1) oldOutput)
      (84 * f.length + 5) := by
  dsimp only
  let layout := compilerLayout constant f.length budget
  let depth := min budget f.length + 1
  have hc : Clauses2 f := fun c h => (hf c h).1
  have hprefix : f.take (index + 1) = f.take index ++ [f.getD index []] :=
    Compiler.take_next f index hi
  have htrigger : budget < unsatisfiedCount τ (f.take index ++ [f.getD index []]) := by
    rwa [hprefix] at hnew
  have hspecial := setupSpecialPrefix_compression τ f (f.take index) (f.getD index [])
    (index + 1) budget hc (by omega) hprefix hold htrigger
  have hspecialClauses : Clauses2 (compressionSpecial τ (f.take index) (f.getD index [])) :=
    compressionSpecial_clauses2 (fun c h => hc c (List.mem_of_mem_take h))
      (by rw [← List.getElem_eq_getD (h := hi) []]; exact hc _ (List.getElem_mem hi)) τ
  intro c₀ hpre
  obtain ⟨⟨hg, hcodes, hz, hout⟩, hcandidate, href, hprocessed, halive⟩ := hpre
  let c₁ := c₀.setReg (callerRegister nodeSuccess) 0
  have he₁ : ExecB S (.const (callerRegister nodeSuccess) 0) c₀ 1 c₁ := .const _ _ _
  have hglobals₁ : Compiler.Globals layout (2 * f.length + 1) f.length budget depth
      (registerView callerRegister c₁) := by
    apply Compiler.globals_reg_frame hg
    intro r hr
    apply he₁.reg_frame
    simp only [wregs, List.mem_singleton]
    intro he
    have he' := callerRegister_injective he
    subst r
    simp +decide [Compiler.globalRegisters, nodeSuccess] at hr
  have hgsetup : CompressionSetupGlobals layout.formula layout.active layout.candidate
      layout.special layout.baseActive (index + 1) f.length (registerView callerRegister c₁) := by
    exact ⟨hglobals₁.formula, hglobals₁.active, hglobals₁.candidate,
      hglobals₁.special, hglobals₁.baseActive,
      (he₁.reg_frame (by decide)).trans hprocessed, hglobals₁.clauses⟩
  have hsepActive : layout.active + f.length ≤ layout.baseActive := by dsimp [layout, compilerLayout]; omega
  have hsepSpecial : layout.active + f.length ≤ layout.special := by dsimp [layout, compilerLayout]; omega
  have hsepSnapshot : layout.baseActive + f.length ≤ layout.special := by dsimp [layout, compilerLayout]; omega
  have hinputs : ∀ a, (layout.formula ≤ a ∧ a < layout.formula + 2 * f.length) ∨
      (layout.candidate ≤ a ∧ a < layout.candidate + 2 * (2 * f.length + 1)) →
      setupOutside layout.active layout.baseActive layout.special f.length f.length a := by
    intro a ha
    dsimp [layout, compilerLayout, setupOutside] at ha ⊢
    omega
  have hspaces : layout.formula + 2 * f.length ≤ S ∧
      layout.candidate + 2 * (2 * f.length + 1) ≤ S ∧
      layout.active + f.length ≤ S ∧ layout.baseActive + f.length ≤ S ∧
      layout.special + 2 * f.length ≤ S := by
    dsimp [layout, compilerLayout] at hspace ⊢
    omega
  have hcodes₁ : Arr c₁.mem layout.formula (TwoSat.codes f) := hcodes
  have hcandidate₁ : TruthTable c₁.mem layout.candidate (2 * f.length + 1) τ := hcandidate
  obtain ⟨c₂, time, he₂, hpost, ht⟩ :=
    compressionSetupCaller_spec f hf τ (Or.inl hsepActive) (Or.inl hsepSpecial)
      (Or.inl hsepSnapshot) hinputs hspaces c₁ hgsetup hcodes₁ hcandidate₁ c₁ rfl
  obtain ⟨hs, _, hsnapshot, _, hframe, hzero⟩ := hpost
  have hglobals₂ : Compiler.Globals layout (2 * f.length + 1) f.length budget depth
      (registerView callerRegister c₂) := by
    apply Compiler.globals_reg_frame hglobals₁
    intro r hr
    have hcases : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 220 ∨
        r = 222 ∨ r = 223 ∨ r = 225 ∨ r = 226 ∨ r = 300 ∨ r = 344 ∨ r = 345 ∨
        r = 350 ∨ r = 400 ∨ r = 406 ∨ r = 430 ∨ r = 433 ∨ r = 434 ∨ r = 435 := by
      simpa [Compiler.globalRegisters] using hr
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact he₂.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))
  have hmem (a : ℕ) (ha : setupOutside layout.active layout.baseActive layout.special f.length f.length a) :
      c₂.mem a = c₀.mem a := hs.2.2.2.2.1 a (by simpa only [setupRowsOf_length] using ha)
  have hcodes₂ : Arr c₂.mem layout.formula (TwoSat.codes f) := by
    intro i hi
    have hlen : (TwoSat.codes f).length = 2 * f.length := TwoSat.length_codes hf
    exact (hmem _ (hinputs _ (Or.inl ⟨by omega, by omega⟩))).trans (hcodes i hi)
  have href₂ : TruthTable c₂.mem layout.reference (2 * f.length + 1) τ := by
    intro u hu
    have ha : setupOutside layout.active layout.baseActive layout.special f.length f.length
        (layout.reference + u) := by
      dsimp [layout, compilerLayout, setupOutside] at hu ⊢
      omega
    exact (hmem _ ha).trans (href u hu)
  have hz₂ : Compiler.StageZero (Flow.hornSeparator F) c₂ := by
    intro r hr
    exact (hzero r).trans ((he₁.reg_frame (by
      simp only [wregs, List.mem_singleton]
      intro he
      have hm := Flow.rl_mod (by decide : 0 < 4) r
      rw [he] at hm
      norm_num [callerRegister, nodeSuccess] at hm)).trans (hz r hr))
  have hpacked : Arr c₂.mem layout.special
      (TwoSat.codes (compressionSpecial τ (f.take index) (f.getD index []))) := by
    have ha := hs.2.2.2.1
    rw [hspecial.1, clauseCodePairs_codes _ hspecialClauses] at ha
    exact ha
  have hcount : c₂.reg (callerRegister seedSpecialCount) =
      (compressionSpecial τ (f.take index) (f.getD index [])).length := by
    have h := hs.2.2.2.2.2.1
    rw [hspecial.1, List.length_map] at h
    exact h
  refine ⟨c₂, 1 + time, .seq he₁ he₂, ⟨hglobals₂, hcodes₂, href₂, hz₂,
    hs.2.2.2.2.2.2.trans hout, hsnapshot, hpacked, hcount, ?_, ?_, ?_⟩, by omega⟩
  · exact (he₂.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans
      ((he₁.reg_frame (by decide)).trans hprocessed)
  · exact (he₂.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans
      ((he₁.reg_frame (by decide)).trans halive)
  · exact (he₂.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans
      (by simp [c₁])

end STACS2027.Runtimes.BoundedCost
