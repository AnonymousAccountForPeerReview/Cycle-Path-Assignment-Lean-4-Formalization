module

public import Runtimes.BoundedCost.ContractionBuild
public import Runtimes.BoundedCost.CallerRegisters
public import Runtimes.BoundedCost.CandidateDecode
public import Runtimes.BoundedCost.DenseTables
public import Runtimes.BoundedCost.LeastCutBounds
public import Runtimes.Flow.HornSeparator
public import Runtimes.Flow.ReusableCall
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

abbrev leastCutSpan : ℕ := 400

/-- Metadata preparation uses primitive register instructions and preserves the
relocated component registers needed for repeated calls. -/
def leastCutMetadata : Stmt :=
  .seq (.const Flow.callZero 0)
    (.seq (.const Flow.callValue 5)
      (.seq (.add Flow.callSpan (callerRegister leastCutSpan) Flow.callZero)
        (.seq (.add Flow.callInput (callerRegister contractionOutputBase) Flow.callZero)
          (.seq (.add Flow.callLength (callerRegister contractionArcCount) (callerRegister contractionArcCount))
            (.seq (.add Flow.callLength Flow.callLength Flow.callValue)
              (.add Flow.callOutput (callerRegister leastCutSpan) Flow.callZero))))))

def leastCutBackend (F : Stmt) : Stmt :=
  .seq (onCallerRegisters contractionBuild)
    (.ifz (callerRegister contractionIncompatible)
      (.seq leastCutMetadata
        (.seq (Flow.reusableCall (Flow.hornSeparator F))
          (onCallerRegisters CandidateDecode.program))) .skip)

theorem wregs_renameRegisters (φ : ℕ → ℕ) (s : Stmt) :
    wregs (renameRegisters φ s) = (wregs s).map φ := by
  induction s <;> simp_all [renameRegisters, wregs]

theorem callerRegister_wregs_mod (s : Stmt) (r : ℕ)
    (hr : r ∈ wregs (onCallerRegisters s)) : r % 4 = 3 := by
  rw [onCallerRegisters, wregs_renameRegisters] at hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  simp [callerRegister, Nat.add_mod]

theorem callerRegister_exec_zero {S t : ℕ} {s : Stmt} {c d : Config}
    (he : ExecB S (onCallerRegisters s) c t d) (r : ℕ) : d.reg (Flow.rl 0 r) = c.reg (Flow.rl 0 r) := by
  apply he.reg_frame
  intro hr
  have hm := callerRegister_wregs_mod s (Flow.rl 0 r) hr
  have hz := Flow.rl_mod (by decide : 0 < 4) r
  omega

theorem leastCutMetadata_spec {S span output count : ℕ} (c₀ : Config)
    (hs : c₀.reg (callerRegister leastCutSpan) = span)
    (ho : c₀.reg (callerRegister contractionOutputBase) = output)
    (hc : c₀.reg (callerRegister contractionArcCount) = count) :
    HTB S leastCutMetadata (fun c => c = c₀)
      (fun c => c.reg Flow.callSpan = span ∧ c.reg Flow.callInput = output ∧
        c.reg Flow.callLength = 2 * count + 5 ∧ c.reg Flow.callOutput = span ∧
        c.mem = c₀.mem ∧ c.out = c₀.out ∧
        (∀ r, r % 4 = 0 ∨ 152 ≤ r → c.reg r = c₀.reg r)) 7 := by
  refine HTB.run_le (by decide) (by decide) ?_
  intro c h
  subst c
  refine ⟨AddrOK.of_memFree rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [leastCutMetadata, hs]
  · simp +decide [leastCutMetadata, ho]
  · simp +decide [leastCutMetadata, hc, two_mul]
  · simp +decide [leastCutMetadata, hs]
  · simp +decide [leastCutMetadata]
  · simp +decide [leastCutMetadata]
  · intro r hr
    apply run_reg_of_not_mem (by decide)
    simp only [leastCutMetadata, wregs, List.mem_append, List.mem_singleton]
    rcases hr with hr | hr <;>
      simp +decide [Flow.callZero, Flow.callValue, Flow.callSpan, Flow.callInput,
        Flow.callLength, Flow.callOutput] <;> omega

@[mk_iff] structure LeastCutGeometry (S span formula active candidate reference forced labels output n m : ℕ) : Prop where
  high : 8 * span + 1 < formula
  formulaActive : formula + 2 * m ≤ active
  activeCandidate : active + m ≤ candidate
  candidateReference : candidate + 2 * n ≤ reference
  referenceForced : reference + 2 * n ≤ forced
  forcedLabels : forced + 2 * n ≤ labels
  labelsOutput : labels + 2 * n ≤ output
  outputSpace : output + 5 + 2 * m ≤ S

def LeastCutGlobals (formula active candidate reference forced labels output n m span : ℕ)
    (c : Config) : Prop :=
  ContractionGlobals formula active reference forced labels output n m (registerView callerRegister c) ∧
  c.reg (callerRegister CandidateDecode.candidateBase) = candidate ∧
  c.reg (callerRegister CandidateDecode.regionBase) = 4 * span + 1 ∧
  c.reg (callerRegister leastCutSpan) = span

def LeastCutFrame (span candidate labels output n m a : ℕ) : Prop :=
  8 * span + 1 ≤ a ∧ OutsideCells candidate (2 * n) a ∧
    OutsideCells labels (2 * n) a ∧ OutsideCells output (5 + 2 * m) a

def LeastCutRegisterFrame (c₀ c : Config) : Prop :=
  ∀ r, 152 ≤ r → r % 4 ≠ 0 →
    r ∉ wregs (onCallerRegisters contractionBuild) →
    r ∉ wregs (onCallerRegisters CandidateDecode.program) → c.reg r = c₀.reg r

def LeastCutResult (program : Stmt) (span candidate labels output n : ℕ)
    (rows : List (Bool × Clause)) (τ : Assignment) (forced : ℕ → Bool) (c₀ c : Config) : Prop :=
  (c.reg (callerRegister contractionIncompatible) = 1 ↔
    ¬ ∃ σ, Requires σ (denseRequirements n forced)) ∧
  (c.reg (callerRegister contractionIncompatible) = 0 →
    ∃ σ, TruthTable c.mem candidate n σ ∧
      IsLeastCut τ (activeOccurrences rows) (denseRequirements n forced) σ) ∧
  (∀ r, r ∉ wregs program → c.reg (Flow.rl 0 r) = 0) ∧
  LeastCutRegisterFrame c₀ c ∧
  (c.reg (callerRegister contractionIncompatible) = 0 ∨ c.reg (callerRegister contractionIncompatible) = 1) ∧
  SameOn (LeastCutFrame span candidate labels output n rows.length) c₀.mem c.mem ∧
  c.out = c₀.out

theorem candidateDecode_prefix_truth (memory : ℕ → ℕ) (candidate n : ℕ) (σ : Assignment) :
    TruthTable (CandidateDecode.prefixMemory memory candidate σ n) candidate n σ := by
  intro u hu
  simp [CandidateDecode.prefixMemory, CandidateDecode.bit, show candidate ≤ candidate + u by omega,
    show candidate + u < candidate + 2 * n by omega]

theorem activeOccurrences_length_le {α : Type*} (rows : List (Bool × α)) :
    (activeOccurrences rows).length ≤ rows.length := by
  induction rows with
  | nil => simp [activeOccurrences]
  | cons row rows ih => cases row with | mk active clause => cases active <;> simp only [activeOccurrences, Bool.false_eq_true, Bool.true_eq, if_false, if_true, List.length_cons] <;> omega

set_option maxHeartbeats 800000

/-- A fixed reusable backend performs contraction, the sole permitted flow call,
and decoding; its bound is quadratic in the original variable domain. -/
theorem leastCutBackend_spec {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hT : Flow.AlmostLinear T) :
    ∃ C : ℕ, ∀ {S span formula active candidate reference forcedBase labels output n : ℕ}
      (rows : List (Bool × Clause)) (τ : Assignment) (forced : ℕ → Bool) (c₀ : Config),
      3 ≤ n → rows.length ≤ n → span = (C + 1) * (n + 1) ^ 2 →
      (∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < n) →
      evalCNF τ (activeOccurrences rows) = true →
      LeastCutGeometry S span formula active candidate reference forcedBase labels output n rows.length →
      LeastCutGlobals formula active candidate reference forcedBase labels output n rows.length span c₀ →
      TerminalRowsMem forcedBase reference (terminalRowsOf n τ forced) c₀.mem →
      ContractionRowsMem formula active reference n (contractionRowsOf τ rows) c₀.mem →
      TruthTable c₀.mem reference n τ →
      (∀ r, r ∉ wregs (Flow.hornSeparator F) → c₀.reg (Flow.rl 0 r) = 0) →
      HTB S (leastCutBackend F) (fun c => c = c₀)
        (LeastCutResult (Flow.hornSeparator F) span candidate labels output n rows τ forced c₀)
        ((500 + (wregs (Flow.hornSeparator F)).length) * (span + 1)) := by
  obtain ⟨C, hsep⟩ := Flow.hornSeparator_computes hF hT
  refine ⟨C, ?_⟩
  intro S span formula active candidate reference forcedBase labels output n rows τ forced c₀
    hn hm hspan hrows href hgeometry hglobals hterminal hrowMemory htruth hzero
  intro c hc
  subst c
  obtain ⟨hhigh, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hgeometry
  obtain ⟨hglobals, hcandidate, hregion, hspanReg⟩ := hglobals
  have hlen : (contractionRowsOf τ rows).length = rows.length := by simp [contractionRowsOf]
  have hterms : (terminalRowsOf n τ forced).length = n := terminalRowsOf_length n τ forced
  have hspanSize : C * (n + 1) ^ 2 ≤ span ∧ (n + 1) ^ 2 ≤ span := by
    rw [hspan]
    exact ⟨Nat.mul_le_mul_right _ (Nat.le_succ C), by
      simpa using Nat.mul_le_mul_right ((n + 1) ^ 2) (show 1 ≤ C + 1 by omega)⟩
  have hnspan : n + 2 ≤ span := (by nlinarith only [hn] : n + 2 ≤ (n + 1) ^ 2).trans hspanSize.2
  have hinputLength : 5 + 2 * n ≤ span := (by nlinarith only [hn] : 5 + 2 * n ≤ (n + 1) ^ 2).trans hspanSize.2
  have hb := contractionBuild_spec (S := S) (formula := formula) (active := active)
    (reference := reference) (forced := forcedBase) (labels := labels) (output := output)
    (oldOutput := c₀.out) hterminal (by simpa only [hterms] using hrowMemory)
    (by unfold DisjointCells; rw [hterms]; omega)
    (by unfold DisjointCells; rw [hterms]; omega)
    (by unfold DisjointCells; rw [hterms, hlen]; omega)
    (by unfold DisjointCells; rw [hterms, hlen]; omega)
    (by unfold DisjointCells; rw [hlen]; omega)
    (by unfold DisjointCells; rw [hlen]; omega)
    (by unfold DisjointCells; rw [hterms, hlen]; omega)
    (by unfold DisjointCells; rw [hterms, hlen]; omega)
    (by rw [hterms, hlen]; omega)
  have hb' := onCallerRegisters_htb hb
  obtain ⟨cBuild, tBuild, heBuild, hBuild, htBuild⟩ := hb' c₀
    ⟨by simpa only [hterms, hlen] using hglobals, rfl, rfl⟩
  obtain ⟨hgBuild, htLabels, haInput, hmBuild, hcBuild, hfBuild, hoBuild⟩ := hBuild
  have hgBuild' : ContractionGlobals formula active reference forcedBase labels output n rows.length
      (registerView callerRegister cBuild) := by simpa only [hterms, hlen] using hgBuild
  have haInput' : Arr cBuild.mem output
      (Flow.edgeInput (contractedCutNetwork (activeOccurrences rows) (activeOccurrences_twoCNF hrows)
        τ (denseRequirements n forced)) n) := by
    simpa only [registerView, hterms, hlen, contractionEdgeInput_semantic τ n forced rows hrows href]
      using haInput
  have hfBuild' : cBuild.reg (callerRegister contractionIncompatible) =
      if terminalConflictPrefix (terminalRowsOf n τ forced) n then 1 else 0 := by
    simpa only [registerView, hterms] using hfBuild
  have hzBuild (r : ℕ) (hr : r ∉ wregs (Flow.hornSeparator F)) : cBuild.reg (Flow.rl 0 r) = 0 :=
    (callerRegister_exec_zero heBuild r).trans (hzero r hr)
  have hframeBuild (a : ℕ) (ha : OutsideCells labels (2 * n) a ∧
      OutsideCells output (5 + 2 * rows.length) a) : cBuild.mem a = c₀.mem a := by
    exact hmBuild a (by simpa only [hterms, hlen] using ha)
  have hsBuild : cBuild.reg (callerRegister leastCutSpan) = span :=
    (heBuild.reg_frame (by decide)).trans hspanReg
  have hcanBuild : cBuild.reg (callerRegister CandidateDecode.candidateBase) = candidate :=
    (heBuild.reg_frame (by decide)).trans hcandidate
  have hrBuild : cBuild.reg (callerRegister CandidateDecode.regionBase) = 4 * span + 1 :=
    (heBuild.reg_frame (by decide)).trans hregion
  by_cases hconf : terminalConflictPrefix (terminalRowsOf n τ forced) n = true
  · have hflag : cBuild.reg (callerRegister contractionIncompatible) = 1 := by simp [hfBuild', hconf]
    have hbad : ¬ ∃ σ, Requires σ (denseRequirements n forced) := by
      rw [← terminalConsistent_iff_requires τ, ← terminalConflictPrefix_false_iff]
      simp [hconf]
    refine ⟨cBuild, tBuild + 2, ExecB.seq heBuild (ExecB.ifzFalse (by omega) (ExecB.skip cBuild)),
      ⟨by simp [hflag, hbad], ?_, hzBuild, ?_, Or.inr hflag, ?_, hoBuild⟩, ?_⟩
    · intro h; omega
    · intro r hr hm hb hd
      exact heBuild.reg_frame hb
    · intro a ha; exact hframeBuild a ⟨ha.2.2.1, ha.2.2.2⟩
    · rw [hterms, hlen] at htBuild
      exact leastCutIncompatibleTime hnspan hm htBuild
  · have hconfFalse : terminalConflictPrefix (terminalRowsOf n τ forced) n = false := by
      cases h : terminalConflictPrefix (terminalRowsOf n τ forced) n <;> simp_all
    have hcompatible := (terminalConflictPrefix_false_iff τ n forced).mp hconfFalse
    have hflag : cBuild.reg (callerRegister contractionIncompatible) = 0 := by simp [hfBuild', hconfFalse]
    let net := contractedCutNetwork (activeOccurrences rows) (activeOccurrences_twoCNF hrows)
      τ (denseRequirements n forced)
    have hmarcs : (contractedCutArcs τ (activeOccurrences rows) (denseRequirements n forced)).length ≤ rows.length :=
      (contractedCutArcs_length_le τ _ _).trans (activeOccurrences_length_le rows)
    have hmnet := hmarcs.trans hm
    obtain ⟨flow, d, steps, hcompute, htime, hflow, hcut, hvalue, hgreatest⟩ :=
      hsep net n (by omega) hmnet (by omega)
        (contractedCutNetwork_head_ne_source _ _ _ _) (contractedCutNetwork_tail_ne_sink _ _ _ _)
    have hcompute' : ComputesIn (Flow.hornSeparator F) (Flow.edgeInput net n)
        (Flow.maximalRegionBits net flow) steps span := hcompute.mono hspanSize.1
    have hcounter : cBuild.reg (callerRegister contractionArcCount) =
        (contractedCutArcs τ (activeOccurrences rows) (denseRequirements n forced)).length := by
      simpa only [registerView, hterms, hlen,
        contractionArcsPrefix_semantic τ n forced rows hrows href] using hcBuild
    have hmeta := leastCutMetadata_spec (S := S) cBuild hsBuild
      hgBuild'.output hcounter
    obtain ⟨cMeta, tMeta, heMeta, hMeta, htMeta⟩ := hmeta cBuild rfl
    obtain ⟨hsMeta, hiMeta, hlMeta, hoMeta, hmMeta, houtMeta, hrMeta⟩ := hMeta
    have hinputMeta : Arr cMeta.mem output (Flow.edgeInput net n) := by rw [hmMeta]; exact haInput'
    have hcall := Flow.reusableCall_spec (S := S) (span := span) (Flow.hornSeparator F)
      (Flow.edgeInput net n) (Flow.maximalRegionBits net flow) hcompute' (by omega)
      (by simp [Flow.edgeInput_length]; omega) output span (by omega)
      (by simp [Flow.edgeInput_length]; omega) (by omega) cMeta hinputMeta hsMeta hiMeta
      (by simp only [Flow.edgeInput_length]; exact hlMeta)
      hoMeta (fun r hr => (hrMeta (Flow.rl 0 r) (Or.inl (Flow.rl_mod (by decide) r))).trans (hzBuild r hr))
    obtain ⟨cCall, tCall, heCall, hCall, htCall⟩ := hcall cMeta rfl
    have houtLen : (Flow.maximalRegionBits net flow).length = n + 2 := by simp [Flow.maximalRegionBits]
    have hhighCall (a : ℕ) (ha : 8 * span + 1 ≤ a) : cCall.mem a = cBuild.mem a := by
      exact (hCall.memory_high a (by omega) (by rw [houtLen]; omega)).trans (congrFun hmMeta a)
    have hcaller (r : ℕ) (hr : 152 ≤ callerRegister r) :
        cCall.reg (callerRegister r) = cBuild.reg (callerRegister r) :=
      (hCall.2.2.2.2.1 _ hr (by simp [callerRegister, Nat.add_mod])).trans (hrMeta _ (Or.inr hr))
    let region := extendCutRegion (Flow.maximalCutRegion net flow)
    let label := contractVariable τ (denseRequirements n forced)
    have hlabelsCall (x : ℕ) (hx : x < n) :
        label x < n + 2 ∧ cCall.mem (labels + 2 * x) = label x := by
      refine ⟨contractVariable_lt hx τ _, ?_⟩
      rw [hhighCall _ (by omega)]
      have ht := htLabels (2 * x) (by rw [hterms]; omega)
      have hv := terminalLabelValue_code τ n forced (Literal.mk x true) hx
      simpa only [registerView, TwoSat.code, Literal.var] using ht.trans hv
    have hrefCall (x : ℕ) (hx : x < n) :
        cCall.mem (reference + 2 * x) = CandidateDecode.bit (τ x) := by
      rw [hhighCall _ (by omega), hframeBuild _ (by unfold OutsideCells; omega)]
      simpa [CandidateDecode.bit] using truthTable_positive htruth x hx
    have hbitsCall (x : ℕ) (hx : x < n + 2) :
        cCall.mem ((4 * span + 1) + 4 * x) = CandidateDecode.bit (region x) := by
      have h := hCall.2.1 x (by rw [houtLen]; exact hx)
      have ha : (4 * span + 1) + 4 * x = 4 * (span + x) + 1 := by omega
      rw [ha, h]
      simpa [CandidateDecode.bit, region, Flow.maximalRegionBits_get, extendCutRegion, hx]
        using Flow.maximalRegionBits_get net flow ⟨x, hx⟩
    have hdecode := onCallerRegisters_htb (CandidateDecode.program_spec (S := S)
      (candidate := candidate) (reference := reference) (labels := labels) (region := 4 * span + 1)
      (n := n) (nodes := n + 2) (memory := cCall.mem) (O := c₀.out)
      hlabelsCall hrefCall hbitsCall (by unfold CandidateDecode.Separated; omega) (by omega))
    have hgDecode : CandidateDecode.Globals candidate reference labels (4 * span + 1) n
        (registerView callerRegister cCall) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (hcaller _ (by decide)).trans hcanBuild
      · exact (hcaller _ (by decide)).trans hgBuild'.reference
      · exact (hcaller _ (by decide)).trans hgBuild'.labels
      · exact (hcaller _ (by decide)).trans hrBuild
      · exact (hcaller _ (by decide)).trans hgBuild'.nodes
    obtain ⟨cFinal, tDecode, heDecode, hDecode, htDecode⟩ := hdecode cCall
      ⟨hgDecode, rfl, (hCall.2.2.1.trans houtMeta).trans hoBuild⟩
    obtain ⟨hgFinal, hmFinal, hoFinal⟩ := hDecode
    have hflagFinal : cFinal.reg (callerRegister contractionIncompatible) = 0 :=
      (heDecode.reg_frame (by decide)).trans ((hcaller _ (by decide)).trans hflag)
    have hleast := leastCut_of_contractedFiniteCut (activeOccurrences_twoCNF hrows) href hcompatible hcut hgreatest
    have hgood : ∃ σ, Requires σ (denseRequirements n forced) :=
      (terminalConsistent_iff_requires τ _).mp hcompatible
    refine ⟨cFinal, tBuild + (tMeta + (tCall + tDecode) + 1),
      ExecB.seq heBuild (ExecB.ifzTrue hflag (ExecB.seq heMeta (ExecB.seq heCall heDecode))),
      ⟨by simp [hflagFinal, hgood], ?_, ?_, ?_, Or.inl hflagFinal, ?_, hoFinal⟩, ?_⟩
    · intro _
      refine ⟨CandidateDecode.decoded τ label region, ?_, ?_⟩
      · change TruthTable cFinal.mem candidate n _
        rw [show cFinal.mem = CandidateDecode.prefixMemory cCall.mem candidate
          (CandidateDecode.decoded τ label region) n by exact hmFinal]
        exact candidateDecode_prefix_truth _ _ _ _
      · exact hleast
    · intro r hr
      exact (callerRegister_exec_zero heDecode r).trans (hCall.2.2.2.1 r hr)
    · intro r hr hm hb hd
      exact (heDecode.reg_frame hd).trans ((hCall.2.2.2.2.1 r hr hm).trans
        ((hrMeta r (Or.inr hr)).trans (heBuild.reg_frame hb)))
    · intro a ha
      have hd : cFinal.mem a = cCall.mem a := by
        rw [show cFinal.mem = CandidateDecode.prefixMemory cCall.mem candidate
          (CandidateDecode.decoded τ label region) n by exact hmFinal]
        exact CandidateDecode.prefixMemory_outside ha.2.1
      exact hd.trans ((hhighCall a ha.1).trans (hframeBuild a ⟨ha.2.2.1, ha.2.2.2⟩))
    · rw [hterms, hlen] at htBuild
      exact leastCutTotalTime hnspan hm htBuild htMeta htCall htDecode

end STACS2027.Runtimes.BoundedCost
