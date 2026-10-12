module

public import Runtimes.BoundedCost.Domain
public import Runtimes.BoundedCost.CutNetwork
import Mathlib.Tactic

/-!
# A canonical least-cut factory from the cited flow contract

The global specification uses a finite graph large enough for each formula.
Uniqueness identifies its answer with the graph at the original input's
fixed variable bound used by the RAM implementation.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def literalBound : List Literal → ℕ
  | [] => 0
  | l :: ls => max (l.var + 1) (literalBound ls)

theorem literalBound_member {ls : List Literal} {l : Literal} (hl : l ∈ ls) :
    l.var < literalBound ls := by
  induction ls with
  | nil => simp at hl
  | cons a ls ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · exact lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)
    · exact (ih hl).trans_le (Nat.le_max_right _ _)

def formulaBound (f : CNF) : ℕ := literalBound (f.flatMap id)

theorem formulaBound_twoCNF {f : CNF} (hf : Clauses2 f) :
    TwoSat.IsTwoCNF (formulaBound f) f := by
  intro c hc
  refine ⟨hf c hc, ?_⟩
  intro l hl
  exact literalBound_member (List.mem_flatMap.mpr ⟨c, hc, hl⟩)

/-- Every consistent annotated instance has its least-cut certificate, obtained
from the sole permitted external algorithmic contract. -/
theorem exists_leastCut_of_citedFlow {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T)
    {τ : Assignment} {f : CNF} {L : List Literal}
    (hf : Clauses2 f) (hτ : evalCNF τ f = true) (hL : TerminalConsistent τ L) :
    ∃ δ, IsLeastCut τ f L δ := by
  let n := formulaBound f
  have hfn : TwoSat.IsTwoCNF n f := formulaBound_twoCNF hf
  let net := contractedCutNetwork f hfn τ L
  let padding := n + f.length + 2
  have ha : (contractedCutArcs τ f L).length ≤ padding :=
    (contractedCutArcs_length_le τ f L).trans (by omega)
  have hn : n + 2 ≤ (contractedCutArcs τ f L).length + padding + 2 := by omega
  have hs : 2 ≤ (contractedCutArcs τ f L).length + padding := by omega
  obtain ⟨C, hC⟩ := Flow.paddedMaxFlow_oracle_cut hF hAL
  obtain ⟨bits, steps, d, _, _, _, _, _, hcut, _, hmaximum⟩ :=
    hC net padding ha hn hs (contractedCutNetwork_head_ne_source f hfn τ L)
      (contractedCutNetwork_tail_ne_sink f hfn τ L)
  exact ⟨_, leastCut_of_contractedFiniteCut hfn hτ hL hcut hmaximum⟩

noncomputable def citedFlowLeastCutOperation {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) (τ : Assignment) :
    LeastCutOperation := by
  classical
  intro f L
  exact if h : Clauses2 f ∧ evalCNF τ f = true ∧ TerminalConsistent τ L then
    some (Classical.choose (exists_leastCut_of_citedFlow hF hAL h.1 h.2.1 h.2.2))
  else none

theorem citedFlowLeastCutOperation_correct {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) (τ : Assignment) :
    LeastCutOperationCorrect τ (citedFlowLeastCutOperation hF hAL τ) := by
  classical
  intro f L hf hτ
  by_cases hL : TerminalConsistent τ L
  · have h : Clauses2 f ∧ evalCNF τ f = true ∧ TerminalConsistent τ L := ⟨hf, hτ, hL⟩
    have hex := (terminalConsistent_iff_requires τ L).mp hL
    refine ⟨?_, ?_⟩
    · simp [citedFlowLeastCutOperation, h, hex]
    · intro δ hd
      simp only [citedFlowLeastCutOperation, dite_eq_left h, Option.some.injEq] at hd
      subst δ
      exact Classical.choose_spec (exists_leastCut_of_citedFlow hF hAL hf hτ hL)
  · have h : ¬(Clauses2 f ∧ evalCNF τ f = true ∧ TerminalConsistent τ L) := by
      intro hh; exact hL hh.2.2
    have hn : ¬∃ σ, Requires σ L := by
      simpa only [Requires] using (mt (terminalConsistent_iff_requires τ L).mpr hL)
    simp [citedFlowLeastCutOperation, h, hn]

noncomputable def citedFlowLeastCutFactory {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) : LeastCutFactory :=
  citedFlowLeastCutOperation hF hAL

theorem citedFlowLeastCutFactory_correct {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    LeastCutFactoryCorrect (citedFlowLeastCutFactory hF hAL) :=
  citedFlowLeastCutOperation_correct hF hAL

/-- The finite graph chosen by the implementation gives the canonical factory
answer whenever it supplies the proved least-cut certificate. -/
theorem citedFlowLeastCutOperation_eq_some {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T)
    {τ δ : Assignment} {f : CNF} {L : List Literal} (hf : Clauses2 f)
    (hτ : evalCNF τ f = true) (hδ : IsLeastCut τ f L δ) :
    citedFlowLeastCutOperation hF hAL τ f L = some δ := by
  classical
  have hL := terminalConsistent_of_requires τ hδ.required
  have h : Clauses2 f ∧ evalCNF τ f = true ∧ TerminalConsistent τ L := ⟨hf, hτ, hL⟩
  simp only [citedFlowLeastCutOperation, dite_eq_left h]
  congr 1
  exact isLeastCut_unique
    (Classical.choose_spec (exists_leastCut_of_citedFlow hF hAL hf hτ hL)) hδ

end STACS2027.Runtimes.BoundedCost
