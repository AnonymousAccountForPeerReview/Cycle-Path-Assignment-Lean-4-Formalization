module

public import Runtimes.BoundedCost.CompilerLayout
public import Runtimes.BoundedCost.OccurrenceTables
public import Runtimes.BoundedCost.LeastCutRAM
public import Runtimes.BoundedCost.PathState
public import Runtimes.BoundedCost.CutFactory
public import Runtimes.BoundedCost.DenseTransitions
import Mathlib.Tactic

/-! Representation of a semantic annotated path in the fixed original
occurrence mask, dense forced-literal table, and concrete caller registers. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

def PathBasic (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (digits : List ℕ) (oldOutput : List ℕ) (c : Config) : Prop :=
  LeastCutGlobals layout.formula layout.active layout.candidate layout.reference layout.forced
    layout.labels layout.edgeInput nodes original.length layout.span c ∧
  Arr c.mem layout.formula (TwoSat.codes original) ∧ TruthTable c.mem layout.reference nodes τ ∧
  (∀ r, r ∉ wregs (Flow.hornSeparator F) → c.reg (Flow.rl 0 r) = 0) ∧
  c.out = oldOutput ∧ c.reg (callerRegister pathDigitsBase) = layout.innerDigits ∧
  c.reg (callerRegister pathDepth) = digits.length ∧ Arr c.mem layout.innerDigits digits

def PathStateRep (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) : SearchPathState → Config → Prop
  | .failed, c => c.reg (callerRegister nodeLive) = 0 ∧ c.reg (callerRegister nodeSuccess) = 0
  | .answered σ, c => c.reg (callerRegister nodeLive) = 0 ∧
      c.reg (callerRegister nodeSuccess) = 1 ∧ TruthTable c.mem layout.candidate nodes σ
  | .running formula required budget, c =>
      ∃ rows : List (Bool × Clause), ∃ forced : ℕ → Bool,
        rows.length = original.length ∧ rows.map Prod.snd = original ∧
        (∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < nodes) ∧
        activeOccurrences rows = formula ∧ MaskTable c.mem layout.active rows ∧
        ForcedTable c.mem layout.forced nodes forced ∧
        (∀ σ, Requires σ (denseRequirements nodes forced) ↔ Requires σ required) ∧
        evalCNF τ formula = true ∧ c.reg (callerRegister nodeBudget) = budget ∧
        c.reg (callerRegister nodeLive) = 1 ∧ c.reg (callerRegister nodeSuccess) = 0

def ActualPathRep (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (digits : List ℕ) (oldOutput : List ℕ)
    (state : SearchPathState) (c : Config) : Prop :=
  PathBasic F layout nodes original τ digits oldOutput c ∧
    PathStateRep layout nodes original τ state c

theorem actualPathRep_live {F : Stmt} {layout : CompilerLayout} {nodes : ℕ} {original : CNF}
    {τ : Assignment} {digits oldOutput : List ℕ} {state : SearchPathState} {c : Config}
    (h : ActualPathRep F layout nodes original τ digits oldOutput state c) :
    c.reg (callerRegister nodeLive) = (if state.live then 1 else 0) := by
  rcases h with ⟨_, hs⟩
  cases state with
  | failed => exact hs.1
  | answered σ => exact hs.1
  | running formula required budget =>
    obtain ⟨rows, forced, hlen, horiginal, hrows, hformula, hmask, hforced, hrequired,
      href, hbudget, hlive, hsuccess⟩ := hs
    exact hlive

theorem actualPathRep_control {F : Stmt} {layout : CompilerLayout} {nodes : ℕ} {original : CNF}
    {τ : Assignment} {digits oldOutput : List ℕ} {state : SearchPathState} {c : Config}
    (h : ActualPathRep F layout nodes original τ digits oldOutput state c) :
    c.reg (callerRegister nodeLive) = (if state.live then 1 else 0) ∧
      c.reg (callerRegister pathDigitsBase) = layout.innerDigits ∧
      c.reg (callerRegister pathDepth) = digits.length ∧ Arr c.mem layout.innerDigits digits :=
  ⟨actualPathRep_live h, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2.1, h.1.2.2.2.2.2.2.2⟩

theorem actualPathRep_indep (F : Stmt) (layout : CompilerLayout) (nodes : ℕ) (original : CNF)
    (τ : Assignment) (digits oldOutput : List ℕ) (state : SearchPathState) :
    Indep [callerRegister pathIndex, rT, callerRegister nodeChoice]
      (ActualPathRep F layout nodes original τ digits oldOutput state) := by
  rintro c c' ⟨hreg, hmem, hout⟩ hp
  rcases hp with ⟨hb, hs⟩
  have hbasic : PathBasic F layout nodes original τ digits oldOutput c' := by
    rcases hb with ⟨hg, hc, hr, hz, ho, hd, hl, ha⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      have hmod := Flow.rl_mod (by decide : 0 < 4) r
      have hn : Flow.rl 0 r ∉ [callerRegister pathIndex, rT, callerRegister nodeChoice] := by
        intro hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h | h | h
        all_goals
          have he := congrArg (fun x : ℕ => x % 4) h
          rw [hmod] at he
          norm_num [callerRegister, pathIndex, nodeChoice, rT] at he
      exact (hreg _ hn).trans (hz r hr)
    · exact hout.trans ho
    · exact (hreg _ (by decide)).trans hd
    · exact (hreg _ (by decide)).trans hl
    · simpa only [hmem] using ha
  refine ⟨hbasic, ?_⟩
  cases state with
  | failed => exact ⟨(hreg _ (by decide)).trans hs.1, (hreg _ (by decide)).trans hs.2⟩
  | answered σ => exact ⟨(hreg _ (by decide)).trans hs.1, (hreg _ (by decide)).trans hs.2.1,
      by simpa only [hmem] using hs.2.2⟩
  | running formula required budget =>
    obtain ⟨rows, forced, hlen, horiginal, hrows, hformula, hmask, hforced, hrequired,
      href, hbudget, hlive, hsuccess⟩ := hs
    exact ⟨rows, forced, hlen, horiginal, hrows, hformula,
      by simpa only [hmem] using hmask, by simpa only [hmem] using hforced,
      hrequired, href, (hreg _ (by decide)).trans hbudget,
      (hreg _ (by decide)).trans hlive, (hreg _ (by decide)).trans hsuccess⟩

end STACS2027.Runtimes.BoundedCost
