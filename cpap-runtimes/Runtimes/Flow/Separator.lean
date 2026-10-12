module

public import Runtimes.Flow.PaddedProjection
public import Runtimes.Flow.Augment
public import Runtimes.Flow.HornQuery
public import Runtimes.Flow.PolynomialBound
import Mathlib.Tactic

/-! # Maximum source-side minimum-cut certificates from the sole cited flow contract -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

/-- The reverse-residual region computed from an optimal padded flow is a minimum cut,
and includes the source side of every other minimum cut. -/
theorem paddedMaxFlow_cut_optimal {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (hpadding : arcs ≤ padding) (hn : nodes ≤ arcs + padding + 2)
    (hhead : ∀ i, net.head i ≠ net.source) (htail : ∀ i, net.tail i ≠ net.sink)
    (bits : List ℕ) (hlen : bits.length = arcs + padding) (hbits : ∀ b ∈ bits, b ≤ 1)
    (hmin : IsMinFlow (paddedMaxFlowNetwork net padding) padding
      (select (paddedMaxFlowNetwork net padding) bits)) :
    IsMinimumCut net (maximalCutRegion net (maxFlowProjection bits)) ∧
      ∀ other : Fin nodes → Bool, IsMinimumCut net other →
        ∀ v, other v = true → maximalCutRegion net (maxFlowProjection bits) v = true := by
  obtain ⟨d, hf, hmax⟩ := paddedMaxFlow_projection_optimal net padding hpadding hn hhead
    htail bits hlen hbits hmin
  have hno := maximumFlow_no_residualReach net hf hmax
  obtain ⟨hcut, _, hgreatest⟩ := maximalCutRegion_minimum net hf hno
  exact ⟨hcut, hgreatest⟩

/-- With global padding, the cited almost-linear oracle costs at most a quadratic function
of the original instance size, even when a branch has erased most original arcs. -/
theorem paddedMaxFlow_oracle_quadratic {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : MinCostFlowSolver F T) (hT : AlmostLinear T) :
    ∃ C : ℕ, ∀ {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ),
      arcs ≤ padding → nodes ≤ arcs + padding + 2 → 2 ≤ arcs + padding →
      (∀ i, net.head i ≠ net.source) → (∀ i, net.tail i ≠ net.sink) →
      ∃ (out : List ℕ) (steps : ℕ),
        RAM.ComputesIn F (netInput (numberedNodeNumber net) nodes padding
          (paddedMaxFlowNetwork net padding)) out steps
          (T (netInput (numberedNodeNumber net) nodes padding
            (paddedMaxFlowNetwork net padding)).length) ∧
        steps ≤ C * (padding + 1) ^ 2 ∧
        FlowAnswer (paddedMaxFlowNetwork net padding) padding out := by
  obtain ⟨K, hK⟩ := hT.polynomialBound
  refine ⟨K * 36, ?_⟩
  intro nodes arcs net padding hpadding hn hsize hhead htail
  obtain ⟨out, steps, hcomputes, hsteps, hanswer⟩ := hF (numberedNodeNumber net) nodes padding
    (paddedMaxFlowNetwork net padding)
    (paddedMaxFlowNetwork_good net padding hn hsize hhead htail)
  refine ⟨out, steps, hcomputes, ?_, hanswer⟩
  have hbound := hK (netInput (numberedNodeNumber net) nodes padding
    (paddedMaxFlowNetwork net padding)).length
  simp only [length_netInput, paddedMaxFlowNetwork_length] at hbound hsteps
  calc
    steps ≤ K * (3 * (arcs + padding) + 5 + 1) ^ 2 := hsteps.trans hbound
    _ ≤ K * (6 * (padding + 1)) ^ 2 := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      omega
    _ = K * 36 * (padding + 1) ^ 2 := by ring

/-- The actual oracle output supplies a maximum integral flow and a maximum source-side
minimum cut. The subsequent cut membership calls are justified by `hornQuery_decision`. -/
theorem paddedMaxFlow_oracle_cut {F : RAM.Stmt} {T : ℕ → ℕ}
    (hF : MinCostFlowSolver F T) (hT : AlmostLinear T) :
    ∃ C : ℕ, ∀ {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ),
      arcs ≤ padding → nodes ≤ arcs + padding + 2 → 2 ≤ arcs + padding →
      (∀ i, net.head i ≠ net.source) → (∀ i, net.tail i ≠ net.sink) →
      ∃ (bits : List ℕ) (steps d : ℕ),
        RAM.ComputesIn F (netInput (numberedNodeNumber net) nodes padding
          (paddedMaxFlowNetwork net padding)) (1 :: bits) steps
          (T (netInput (numberedNodeNumber net) nodes padding
            (paddedMaxFlowNetwork net padding)).length) ∧
        steps ≤ C * (padding + 1) ^ 2 ∧ bits.length = arcs + padding ∧
        (∀ b ∈ bits, b ≤ 1) ∧ IsIndexedFlow net d (maxFlowProjection bits) ∧
        IsMinimumCut net (maximalCutRegion net (maxFlowProjection bits)) ∧
        cutSize net (maximalCutRegion net (maxFlowProjection bits)) = d ∧
        ∀ other : Fin nodes → Bool, IsMinimumCut net other →
          ∀ v, other v = true → maximalCutRegion net (maxFlowProjection bits) v = true := by
  obtain ⟨C, hC⟩ := paddedMaxFlow_oracle_quadratic hF hT
  refine ⟨C, ?_⟩
  intro nodes arcs net padding hpadding hn hsize hhead htail
  obtain ⟨out, steps, hcomputes, hsteps, hanswer⟩ := hC net padding hpadding hn hsize hhead htail
  obtain ⟨bits, d, hout, hlen, hbits, hf, hmax⟩ :=
    paddedMaxFlow_answer_optimal net padding hpadding hn hhead htail out hanswer
  obtain ⟨hcut, hvalue, hgreatest⟩ := maximalCutRegion_minimum net hf
    (maximumFlow_no_residualReach net hf hmax)
  rw [hout] at hcomputes
  exact ⟨bits, steps, d, hcomputes, hsteps, hlen, hbits, hf, hcut, hvalue, hgreatest⟩

end STACS2027.Runtimes.Flow
