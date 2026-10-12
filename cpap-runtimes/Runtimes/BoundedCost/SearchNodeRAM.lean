module

public import Runtimes.BoundedCost.LeastCutRAM
public import Runtimes.BoundedCost.SearchMemory
public import Runtimes.BoundedCost.AnnotatedNode
public import Runtimes.BoundedCost.TernaryControl
public import Runtimes.BoundedCost.NodeFrames
import Mathlib.Tactic

/-! A complete annotated search node: actual contraction and flow computation,
readonly clause analysis, and concrete deletion or forcing updates. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

def searchNode (F : Stmt) : Stmt :=
  .seq (leastCutBackend F)
    (.ifz (callerRegister contractionIncompatible)
      (.seq (onCallerRegisters searchScan) (onCallerRegisters annotatedNodeUpdate))
      (.const (callerRegister nodeLive) 0))

theorem LeastCutRegisterFrame.caller {c₀ c : Config} (h : LeastCutRegisterFrame c₀ c)
    {r : ℕ} (hr : 38 ≤ r) (hb : r ∉ wregs contractionBuild)
    (hd : r ∉ wregs CandidateDecode.program) : c.reg (callerRegister r) = c₀.reg (callerRegister r) := by
  apply h
  · simp only [callerRegister]; omega
  · simp [callerRegister, Nat.add_mod]
  · exact not_mem_renameRegisters_wregs callerRegister_injective hb
  · exact not_mem_renameRegisters_wregs callerRegister_injective hd

theorem LeastCutGeometry.read_cells {S span formula active candidate reference forced labels output n m a : ℕ}
    (h : LeastCutGeometry S span formula active candidate reference forced labels output n m)
    (ha : (formula ≤ a ∧ a < formula + 2 * m) ∨ (active ≤ a ∧ a < active + m) ∨
      (reference ≤ a ∧ a < reference + 2 * n) ∨ (forced ≤ a ∧ a < forced + 2 * n)) :
    LeastCutFrame span candidate labels output n m a := by
  obtain ⟨hh, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := h
  unfold LeastCutFrame OutsideCells
  rcases ha with ha | ha | ha | ha <;> omega

theorem contractionRowsMem_frame {S span formula active candidate reference forced labels output n : ℕ}
    {memory next : ℕ → ℕ} {τ : Assignment} {rows : List (Bool × Clause)}
    (hgeo : LeastCutGeometry S span formula active candidate reference forced labels output n rows.length)
    (hmem : ContractionRowsMem formula active reference n (contractionRowsOf τ rows) memory)
    (hframe : SameOn (LeastCutFrame span candidate labels output n rows.length) memory next) :
    ContractionRowsMem formula active reference n (contractionRowsOf τ rows) next := by
  intro i hi
  have hm := hmem i hi
  have hi' : i < rows.length := by simpa [contractionRowsOf] using hi
  rcases hm with ⟨hfirst, hsecond, hf, hs, ha, hrf, hrs⟩
  refine ⟨hfirst, hsecond, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe (formula + 2 * i) (hgeo.read_cells (Or.inl (by omega)))]; exact hf
  · rw [hframe (formula + 2 * i + 1) (hgeo.read_cells (Or.inl (by omega)))]; exact hs
  · rw [hframe (active + i) (hgeo.read_cells (Or.inr (Or.inl (by omega))))]; exact ha
  · rw [hframe (reference + _) (hgeo.read_cells (Or.inr (Or.inr (Or.inl (by omega)))))]; exact hrf
  · rw [hframe (reference + _) (hgeo.read_cells (Or.inr (Or.inr (Or.inl (by omega)))))]; exact hrs

theorem nodeActionMemory_truth {candidate active forced n m : ℕ} {memory : ℕ → ℕ}
    {δ : Assignment} {summary : SearchSummary} {budget choice : ℕ}
    (hc : summary.conflict ≤ m) (hac : active + m ≤ candidate)
    (hcf : candidate + 2 * n ≤ forced) (ht : TruthTable memory candidate n δ) :
    TruthTable (nodeActionMemory (nodeAction summary budget choice) active forced memory) candidate n δ := by
  intro u hu
  have hpoint := ht u hu
  by_cases hs : summary.unsatisfied ≤ budget
  · simpa only [nodeAction, if_pos hs, nodeActionMemory] using hpoint
  by_cases hk : budget < summary.cut
  · simpa only [nodeAction, if_neg hs, if_pos hk, nodeActionMemory] using hpoint
  by_cases hz : summary.conflict = 0
  · simpa only [nodeAction, if_neg hs, if_neg hk, if_pos hz, nodeActionMemory] using hpoint
  by_cases hchoice : choice = 0
  · by_cases hbudget : budget = 0
    · simpa only [nodeAction, if_neg hs, if_neg hk, if_neg hz, if_pos hchoice, if_pos hbudget,
        nodeActionMemory] using hpoint
    · have hne : candidate + u ≠ active + (summary.conflict - 1) := by omega
      simpa only [nodeAction, if_neg hs, if_neg hk, if_neg hz, if_pos hchoice, if_neg hbudget,
        nodeActionMemory, upd_apply, if_neg hne] using hpoint
  by_cases hone : choice = 1
  · have hne : candidate + u ≠ forced + summary.firstLiteral := by omega
    simpa only [nodeAction, if_neg hs, if_neg hk, if_neg hz, if_neg hchoice, if_pos hone,
      nodeActionMemory, upd_apply, if_neg hne] using hpoint
  by_cases htwo : choice = 2
  · have hne : candidate + u ≠ forced + summary.secondLiteral := by omega
    simpa only [nodeAction, if_neg hs, if_neg hk, if_neg hz, if_neg hchoice, if_neg hone, if_pos htwo,
      nodeActionMemory, upd_apply, if_neg hne] using hpoint
  · simpa only [nodeAction, if_neg hs, if_neg hk, if_neg hz, if_neg hchoice, if_neg hone, if_neg htwo,
      nodeActionMemory] using hpoint

def SearchNodeRegisterFrame (c₀ c : Config) : Prop :=
  ∀ r, 38 ≤ r → r ∉ wregs contractionBuild → r ∉ wregs CandidateDecode.program →
    r ∉ wregs searchScan → r ∉ wregs annotatedNodeUpdate →
    c.reg (callerRegister r) = c₀.reg (callerRegister r)

def SearchNodeResult (program : Stmt) (span active candidate forced labels output n : ℕ)
    (rows : List (Bool × Clause)) (τ : Assignment) (required : ℕ → Bool)
    (budget choice success : ℕ) (c₀ c : Config) : Prop :=
  (∀ r, r ∉ wregs program → c.reg (Flow.rl 0 r) = 0) ∧ c.out = c₀.out ∧
  SearchNodeRegisterFrame c₀ c ∧
  SameOn (SearchNodeMemoryFrame span active candidate forced labels output n rows.length) c₀.mem c.mem ∧
  ((¬ ∃ σ, Requires σ (denseRequirements n required)) ∧
      c.reg (callerRegister nodeLive) = 0 ∧ c.reg (callerRegister nodeBudget) = budget ∧
      c.reg (callerRegister nodeSuccess) = success ∨
    ∃ δ memory,
      IsLeastCut τ (activeOccurrences rows) (denseRequirements n required) δ ∧
      SameOn (LeastCutFrame span candidate labels output n rows.length) c₀.mem memory ∧
      TruthTable c.mem candidate n δ ∧
      NodeUpdated active forced budget choice success
        (summarizePrefix (searchRowsOf τ δ rows) rows.length) memory (registerView callerRegister c))

theorem summarizeRow_literal_bounds {bound i : ℕ} {row : SearchRow} {summary : SearchSummary}
    (hr : row.first < bound ∧ row.second < bound)
    (hs : summary.firstLiteral < bound ∧ summary.secondLiteral < bound) :
    (summarizeRow i row summary).firstLiteral < bound ∧
      (summarizeRow i row summary).secondLiteral < bound := by
  unfold summarizeRow
  split <;> try exact hs
  split
  · split <;> first | exact hr | exact hs
  · exact hs

theorem summarizePrefix_literal_bounds {bound : ℕ} {rows : List SearchRow}
    (hb : 0 < bound) (hr : ∀ i, i < rows.length →
      (rows.getD i default).first < bound ∧ (rows.getD i default).second < bound)
    (count : ℕ) (hc : count ≤ rows.length) :
    (summarizePrefix rows count).firstLiteral < bound ∧
      (summarizePrefix rows count).secondLiteral < bound := by
  induction count with
  | zero =>
    change 0 < bound ∧ 0 < bound
    exact ⟨hb, hb⟩
  | succ count ih =>
    rw [summarizePrefix_succ]
    exact summarizeRow_literal_bounds (hr count (by omega)) (ih (by omega))

def NodeControlGlobals (budget choice success : ℕ) (c : Config) : Prop :=
  c.reg (callerRegister nodeBudget) = budget ∧ c.reg (callerRegister nodeChoice) = choice ∧
  c.reg (callerRegister nodeSuccess) = success ∧ c.reg (callerRegister nodeLive) = 1

theorem searchNode_spec {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hT : Flow.AlmostLinear T) :
    ∃ C : ℕ, ∀ {S span formula active candidate reference forcedBase labels output n budget choice success : ℕ}
      (rows : List (Bool × Clause)) (τ : Assignment) (forced : ℕ → Bool) (c₀ : Config),
      3 ≤ n → rows.length ≤ n → span = (C + 1) * (n + 1) ^ 2 →
      (∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < n) →
      evalCNF τ (activeOccurrences rows) = true →
      LeastCutGeometry S span formula active candidate reference forcedBase labels output n rows.length →
      LeastCutGlobals formula active candidate reference forcedBase labels output n rows.length span c₀ →
      TerminalRowsMem forcedBase reference (terminalRowsOf n τ forced) c₀.mem →
      ContractionRowsMem formula active reference n (contractionRowsOf τ rows) c₀.mem →
      TruthTable c₀.mem reference n τ → NodeControlGlobals budget choice success c₀ →
      (∀ r, r ∉ wregs (Flow.hornSeparator F) → c₀.reg (Flow.rl 0 r) = 0) →
      HTB S (searchNode F) (fun c => c = c₀)
        (SearchNodeResult (Flow.hornSeparator F) span active candidate forcedBase labels output n rows τ forced
          budget choice success c₀)
        ((800 + (wregs (Flow.hornSeparator F)).length) * (span + 1)) := by
  obtain ⟨C, hbackend⟩ := leastCutBackend_spec hF hT
  refine ⟨C, ?_⟩
  intro S span formula active candidate reference forcedBase labels output n budget choice success
    rows τ forced c₀ hn hm hspan hrows href hgeo hglobals hterminal hrowsMemory hreference hcontrol hzero
  intro c hc
  subst c
  obtain ⟨cCut, tCut, heCut, hCut, htCut⟩ := hbackend rows τ forced c₀ hn hm hspan hrows href
    hgeo hglobals hterminal hrowsMemory hreference hzero c₀ rfl
  obtain ⟨hbad, hanswer, hzCut, hregs, hbinary, hmemory, hoCut⟩ := hCut
  have hcontrol' : NodeControlGlobals budget choice success cCut := by
    obtain ⟨hk, hchoice, hs, hl⟩ := hcontrol
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals first
      | exact (hregs.caller (by decide) (by decide) (by decide)).trans hk
      | exact (hregs.caller (by decide) (by decide) (by decide)).trans hchoice
      | exact (hregs.caller (by decide) (by decide) (by decide)).trans hs
      | exact (hregs.caller (by decide) (by decide) (by decide)).trans hl
  have hspanSize : n ≤ span := by rw [hspan]; nlinarith
  rcases hbinary with hflag | hflag
  · obtain ⟨δ, ht, hleast⟩ := hanswer hflag
    have hrowCut := contractionRowsMem_frame hgeo hrowsMemory hmemory
    have hsearchMemory := searchRowsMem_of_contraction (fun row hr => (hrows row hr).1) hrowCut ht
    have hscanGlobals : SearchScanGlobals formula active candidate reference rows.length
        (registerView callerRegister cCut) := by
      have hcan := hglobals.2.1
      obtain ⟨hg, _, _, _⟩ := hglobals
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (hregs.caller (by decide) (by decide) (by decide)).trans hg.formula
      · exact (hregs.caller (by decide) (by decide) (by decide)).trans hg.active
      · exact (hregs.caller (by decide) (by decide) (by decide)).trans hcan
      · exact (hregs.caller (by decide) (by decide) (by decide)).trans hg.reference
      · exact (hregs.caller (by decide) (by decide) (by decide)).trans hg.clauses
    have hsearchSpace : formula + 2 * (searchRowsOf τ δ rows).length ≤ S ∧
        active + (searchRowsOf τ δ rows).length ≤ S ∧ candidate + 2 * n ≤ S ∧ reference + 2 * n ≤ S := by
      rw [searchRowsOf_length]
      obtain ⟨_, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hgeo
      omega
    have hscan := onCallerRegisters_htb (searchScan_spec hsearchMemory hsearchSpace)
    obtain ⟨cScan, tScan, heScan, hScan, htScan⟩ := hscan cCut
      ⟨by simpa only [searchRowsOf_length] using hscanGlobals, rfl⟩
    obtain ⟨hgScan, hmScan, hsummary⟩ := hScan
    have hscanControl : NodeControlGlobals budget choice success cScan := by
      obtain ⟨hk, hchoice, hs, hl⟩ := hcontrol'
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals first
        | exact (heScan.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hk
        | exact (heScan.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hchoice
        | exact (heScan.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hs
        | exact (heScan.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans hl
    let summary := summarizePrefix (searchRowsOf τ δ rows) rows.length
    have hconf : summary.conflict ≤ rows.length := summarizePrefix_conflict_le _ _
    have hcodes : summary.firstLiteral < 2 * n ∧ summary.secondLiteral < 2 * n := by
      apply summarizePrefix_literal_bounds (by omega) (count := rows.length)
      · intro i hi
        exact ⟨(hsearchMemory i hi).1, (hsearchMemory i hi).2.1⟩
      · simp
    have hupdateSpace : active + rows.length ≤ S ∧ forcedBase + 2 * n ≤ S := by
      obtain ⟨_, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hgeo
      omega
    have hforced : cScan.reg (callerRegister nodeForcedBase) = forcedBase := by
      obtain ⟨hg, _, _, _⟩ := hglobals
      exact (heScan.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective (by decide))).trans
        ((hregs.caller (by decide) (by decide) (by decide)).trans hg.forced)
    have hupdate := onCallerRegisters_htb (annotatedNodeUpdate_spec hconf hcodes.1 hcodes.2
      hupdateSpace.1 hupdateSpace.2 (memory := cCut.mem) (budget := budget) (choice := choice) (success := success))
    obtain ⟨cUpdated, tUpdated, heUpdated, hUpdated, htUpdated⟩ := hupdate cScan
      ⟨⟨hgScan.2.1, hforced, hscanControl.1, hscanControl.2.1, hscanControl.2.2.1,
        hscanControl.2.2.2, by simpa only [summary, searchRowsOf_length] using hsummary⟩, hmScan⟩
    have hzUpdated (r : ℕ) (hr : r ∉ wregs (Flow.hornSeparator F)) :
        cUpdated.reg (Flow.rl 0 r) = 0 :=
      (callerRegister_exec_zero heUpdated r).trans ((callerRegister_exec_zero heScan r).trans (hzCut r hr))
    have hoUpdated : cUpdated.out = c₀.out :=
      (heUpdated.out_frame (by simp [onCallerRegisters, renameRegisters_writes]; decide)).trans
        ((heScan.out_frame (by simp [onCallerRegisters, renameRegisters_writes]; decide)).trans hoCut)
    have htruthUpdated : TruthTable cUpdated.mem candidate n δ := by
      have hmemup : cUpdated.mem = nodeActionMemory (nodeAction summary budget choice) active forcedBase cCut.mem :=
        hUpdated.2.2.2.2.2.2.2
      rw [hmemup]
      exact nodeActionMemory_truth hconf hgeo.activeCandidate
        (le_trans hgeo.candidateReference (by have := hgeo.referenceForced; omega)) ht
    have hregUpdated : SearchNodeRegisterFrame c₀ cUpdated := by
      intro r hr hb hd hs hu
      exact (heUpdated.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective hu)).trans
        ((heScan.reg_frame (not_mem_renameRegisters_wregs callerRegister_injective hs)).trans
          (hregs.caller hr hb hd))
    have hmemUpdated : SameOn
        (SearchNodeMemoryFrame span active candidate forcedBase labels output n rows.length) c₀.mem cUpdated.mem := by
      intro a ha
      have hmemup : cUpdated.mem = nodeActionMemory (nodeAction summary budget choice) active forcedBase cCut.mem :=
        hUpdated.2.2.2.2.2.2.2
      rw [hmemup]
      exact (nodeActionMemory_outside hconf hcodes.1 hcodes.2 ha.2.1 ha.2.2).trans (hmemory a ha.1)
    refine ⟨cUpdated, tCut + (tScan + tUpdated + 1),
      ExecB.seq heCut (ExecB.ifzTrue hflag (ExecB.seq heScan heUpdated)),
      ⟨hzUpdated, hoUpdated, hregUpdated, hmemUpdated,
        Or.inr ⟨δ, cCut.mem, hleast, hmemory, htruthUpdated, hUpdated⟩⟩, ?_⟩
    rw [searchRowsOf_length] at htScan
    nlinarith
  · have hnone := hbad.mp hflag
    have hePrune : ExecB S (.const (callerRegister nodeLive) 0) cCut 1
        (cCut.setReg (callerRegister nodeLive) 0) := ExecB.const _ _ _
    have hzPruned (r : ℕ) (hr : r ∉ wregs (Flow.hornSeparator F)) :
        (cCut.setReg (callerRegister nodeLive) 0).reg (Flow.rl 0 r) = 0 := by
      have he : Flow.rl 0 r ≠ callerRegister nodeLive := by
        have hmod := Flow.rl_mod (by decide : 0 < 4) r
        simp +decide only [callerRegister, nodeLive] at ⊢
        omega
      simpa [he] using hzCut r hr
    have hregPruned : SearchNodeRegisterFrame c₀ (cCut.setReg (callerRegister nodeLive) 0) := by
      intro r hr hb hd hs hu
      have hne : r ≠ nodeLive := by
        intro he; subst r; exact hu (by decide)
      have hconst : callerRegister r ∉ wregs (.const (callerRegister nodeLive) 0) := by
        simp only [wregs, List.mem_singleton]
        exact fun he => hne (callerRegister_injective he)
      exact (hePrune.reg_frame hconst).trans (hregs.caller hr hb hd)
    have hmemPruned : SameOn
        (SearchNodeMemoryFrame span active candidate forcedBase labels output n rows.length) c₀.mem
        (cCut.setReg (callerRegister nodeLive) 0).mem := by
      intro a ha
      exact hmemory a ha.1
    refine ⟨_, tCut + 2, ExecB.seq heCut (ExecB.ifzFalse (by omega) hePrune),
      ⟨hzPruned, by simpa using hoCut, hregPruned, hmemPruned,
        Or.inl ⟨hnone, ?_, ?_, ?_⟩⟩, ?_⟩
    · simp
    · simpa +decide [callerRegister, nodeBudget, nodeLive] using hcontrol'.1
    · simpa +decide [callerRegister, nodeSuccess, nodeLive] using hcontrol'.2.2.1
    · nlinarith

end STACS2027.Runtimes.BoundedCost
