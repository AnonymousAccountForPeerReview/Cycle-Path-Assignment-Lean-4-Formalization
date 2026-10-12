module

public import Runtimes.BoundedCost.Contraction
public import Runtimes.Flow.Separator
import Mathlib.Tactic

/-! # Finite indexed networks for the contracted clause cut graph -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

/-- The unit-capacity numbered graph associated with a bounded endpoint list.
Parallel occurrences keep separate indices. -/
def cutNetwork (nodes : ℕ) (arcs : List (ℕ × ℕ)) (hsize : 2 ≤ nodes)
    (hends : ∀ e ∈ arcs, e.1 < nodes ∧ e.2 < nodes) : Flow.IndexedNetwork nodes arcs.length where
  tail i := ⟨arcs[i.val].1, (hends _ (List.getElem_mem _)).1⟩
  head i := ⟨arcs[i.val].2, (hends _ (List.getElem_mem _)).2⟩
  cost _ := 0
  source := ⟨0, by omega⟩
  sink := ⟨1, by omega⟩
  source_ne_sink := by simp

/-- A maximum finite cut contains all unused numbers as well. -/
def extendCutRegion {nodes : ℕ} (region : Fin nodes → Bool) : ℕ → Bool :=
  fun x => if h : x < nodes then region ⟨x, h⟩ else true

@[simp] theorem extendCutRegion_fin {nodes : ℕ} (region : Fin nodes → Bool) (v : Fin nodes) :
    extendCutRegion region v.val = region v := by simp [extendCutRegion, v.isLt]

theorem cutNetwork_cutSize (nodes : ℕ) (arcs : List (ℕ × ℕ)) (hsize : 2 ≤ nodes)
    (hends : ∀ e ∈ arcs, e.1 < nodes ∧ e.2 < nodes) (region : ℕ → Bool) :
    Flow.cutSize (cutNetwork nodes arcs hsize hends) (fun v => region v.val) =
      variableCutSize arcs region := by
  unfold Flow.cutSize
  rw [← List.sum_ofFn]
  unfold variableCutSize variableArcCut
  simpa [Flow.cutSize, cutNetwork] using
    congrArg List.sum (List.ofFn_getElem_eq_map arcs
      (fun e => if region e.1 && !(region e.2) then (1 : ℕ) else 0))

theorem cutNetwork_extended_cutSize (nodes : ℕ) (arcs : List (ℕ × ℕ)) (hsize : 2 ≤ nodes)
    (hends : ∀ e ∈ arcs, e.1 < nodes ∧ e.2 < nodes) (region : Fin nodes → Bool) :
    Flow.cutSize (cutNetwork nodes arcs hsize hends) region =
      variableCutSize arcs (extendCutRegion region) := by
  simpa only [extendCutRegion_fin] using cutNetwork_cutSize nodes arcs hsize hends
    (extendCutRegion region)

/-- A greatest finite minimum cut gives the exact natural-number certificate used by
the annotated solver, including unused node numbers. -/
theorem maximumSourceCut_of_finite (nodes : ℕ) (arcs : List (ℕ × ℕ)) (hsize : 2 ≤ nodes)
    (hends : ∀ e ∈ arcs, e.1 < nodes ∧ e.2 < nodes) {region : Fin nodes → Bool}
    (hcut : Flow.IsMinimumCut (cutNetwork nodes arcs hsize hends) region)
    (hmaximum : ∀ other : Fin nodes → Bool,
      Flow.IsMinimumCut (cutNetwork nodes arcs hsize hends) other →
        ∀ v, other v = true → region v = true) :
    IsMaximumSourceCut arcs (extendCutRegion region) := by
  have hs : extendCutRegion region 0 = true := by
    have := hcut.1
    simpa [cutNetwork, extendCutRegion, show 0 < nodes by omega] using this
  have ht : extendCutRegion region 1 = false := by
    have := hcut.2.1
    simpa [cutNetwork, extendCutRegion, show 1 < nodes by omega] using this
  refine ⟨hs, ht, ?_, ?_⟩
  · intro other hos hot
    have hmin := hcut.2.2 (fun v => other v.val)
      (by simpa [cutNetwork] using hos) (by simpa [cutNetwork] using hot)
    rwa [cutNetwork_extended_cutSize, cutNetwork_cutSize] at hmin
  · intro other hos hot heq v hv
    by_cases hbound : v < nodes
    · have hother : Flow.IsMinimumCut (cutNetwork nodes arcs hsize hends)
          (fun w => other w.val) := by
        refine ⟨by simpa [cutNetwork] using hos, by simpa [cutNetwork] using hot, ?_⟩
        intro candidate hcs hct
        have hmin := hcut.2.2 candidate hcs hct
        rwa [cutNetwork_cutSize, heq, ← cutNetwork_extended_cutSize] 
      have hm := hmaximum _ hother ⟨v, hbound⟩ hv
      simpa [extendCutRegion, hbound] using hm
    · simp [extendCutRegion, hbound]

/-- The precise graph supplied to the cited flow program for an annotated formula. -/
def contractedCutNetwork {n : ℕ} (f : CNF) (hf : TwoSat.IsTwoCNF n f)
    (reference : Assignment) (required : List Literal) :
    Flow.IndexedNetwork (n + 2) (contractedCutArcs reference f required).length :=
  cutNetwork (n + 2) (contractedCutArcs reference f required) (by omega)
    (fun e he => let h := contractedCutArcs_endpoints hf reference required e he; ⟨h.1, h.2.1⟩)

theorem contractedCutNetwork_head_ne_source {n : ℕ} (f : CNF) (hf : TwoSat.IsTwoCNF n f)
    (reference : Assignment) (required : List Literal) :
    ∀ i, (contractedCutNetwork f hf reference required).head i ≠
      (contractedCutNetwork f hf reference required).source := by
  intro i he
  have hv := contractedCutArcs_endpoints hf reference required
    ((contractedCutArcs reference f required)[i.val]) (List.getElem_mem i.isLt)
  apply hv.2.2.2
  exact congrArg Fin.val he

theorem contractedCutNetwork_tail_ne_sink {n : ℕ} (f : CNF) (hf : TwoSat.IsTwoCNF n f)
    (reference : Assignment) (required : List Literal) :
    ∀ i, (contractedCutNetwork f hf reference required).tail i ≠
      (contractedCutNetwork f hf reference required).sink := by
  intro i he
  have hv := contractedCutArcs_endpoints hf reference required
    ((contractedCutArcs reference f required)[i.val]) (List.getElem_mem i.isLt)
  apply hv.2.2.1
  exact congrArg Fin.val he

/-- The finite cut returned by the flow/Horn stages decodes directly to the least-cut
assignment used by the annotated branch search. -/
theorem leastCut_of_contractedFiniteCut {n : ℕ} {f : CNF} (hf : TwoSat.IsTwoCNF n f)
    {reference : Assignment} (hreference : evalCNF reference f = true)
    {required : List Literal} (hrequired : TerminalConsistent reference required)
    {region : Fin (n + 2) → Bool}
    (hcut : Flow.IsMinimumCut (contractedCutNetwork f hf reference required) region)
    (hmaximum : ∀ other : Fin (n + 2) → Bool,
      Flow.IsMinimumCut (contractedCutNetwork f hf reference required) other →
        ∀ v, other v = true → region v = true) :
    IsLeastCut reference f required (assignmentOfRegion reference
      (liftContractRegion reference required (extendCutRegion region))) := by
  apply leastCut_of_maximumSourceCut (fun clause hclause => (hf clause hclause).1)
    hreference hrequired
  exact maximumSourceCut_of_finite _ _ _ _ hcut hmaximum

end STACS2027.Runtimes.BoundedCost
