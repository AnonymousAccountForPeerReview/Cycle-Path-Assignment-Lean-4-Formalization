module

public import Runtimes.Flow.Statement
public import Runtimes.BoundedCost.Solver

/-!
# Named construction claims

The paper of the manuscript adds to the proof of Theorem 2 (Appendix A): "Given the
enumerated cycles, we can group their edge occurrences by identifier using sorting and construct
the network deterministically in `O(t log(t+1))` time." The formalization's construction
(`Flow.cpap4_flow_ram_semantic`) runs in linear time `C (t + m + 1)` but keeps a dictionary
indexed by the vertex labels, so its memory bound is `C (labelBound g + t + m + 1)`. The variant
whose construction uses memory linear in `t + m` alone (as a sorting-based construction would)
is recorded below as a proposition. The theorem `Flow.sortedNetworkConstruction` in
`Runtimes/Flow/EnumeratedConstruction.lean` proves it for any permutation of the enumerated
cycles. The definitions below retain the exact named claims. General cycle enumeration is
proved by `generalCycleEnumerationRam`; the polynomial-flow and Almost 2-SAT
claims follow from the sole cited almost-linear flow contract.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

/-- A minimum-cost-flow RAM solver with an ordinary polynomial resource bound.
`polynomialMinCostFlowSolverExists_of_almostLinear` derives this claim from the
sole external cited flow contract. -/
def PolynomialMinCostFlowSolverExists : Prop :=
  ∃ (F : RAM.Stmt) (T : ℕ → ℕ) (C exponent : ℕ),
    MinCostFlowSolver F T ∧ ∀ N : ℕ, T N ≤ C * (N + 1) ^ exponent

/-- **The paper construction claim** (proof of Theorem 2): `Flow.cpap4_flow_ram_semantic` with the
network built within `C ((t + m + 1)(log₂(t + 1) + 1))` steps and memory `C (t + m + 1)`,
independent of the vertex labels. Proved by `sortedNetworkConstruction`. -/
def SortedNetworkConstruction : Prop :=
  ∀ {F : RAM.Stmt} {T : ℕ → ℕ}, MinCostFlowSolver F T →
    ∃ (build extract : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (cs : List Cycle), cs.Perm (cycles g 4) →
      ∃ (net out pos : List ℕ) (t₁ t₂ t₃ : ℕ),
        RAM.ComputesIn build (flowInput g cs 4) net t₁ (C * (cs.length + g.length + 1)) ∧
          t₁ ≤ C * ((cs.length + g.length + 1) * (Nat.log 2 (cs.length + 1) + 1)) ∧
        (∃ (num : FlowNode → ℕ) (n : ℕ) (arcs : List Arc), GoodNet num n arcs ∧
          net = netInput num n (2 * cs.length) arcs ∧
          arcs.length = 10 * cs.length ∧ n ≤ 6 * cs.length + 2 ∧
          ∀ B, HasAssignment g 4 B ↔
            ∃ flow, IsFlow arcs flow ∧ flowValue flow = 2 * cs.length ∧ flowCost flow ≤ B) ∧
        RAM.ComputesIn F net out t₂ (T (30 * cs.length + 5)) ∧ t₂ ≤ T (30 * cs.length + 5) ∧
        RAM.ComputesIn extract (flowInput g cs 4 ++ out) pos t₃ (C * (cs.length + g.length + 1)) ∧
          t₃ ≤ C * (cs.length + g.length + 1) ∧
        pos.length = cs.length ∧ (∀ p ∈ pos, p < 4) ∧
        ValidChoices (cs.map selectedOptions) (List.zipWith selected cs pos) ∧
        OptCost g 4 (cost (List.zipWith selected cs pos))

end STACS2027.Runtimes.Flow

namespace STACS2027.Runtimes.BoundedCost

/-- A concrete RAM Almost 2-SAT solver with the manuscript's fixed-parameter
bound. `almostTwoSatFptSolverExists_of_citedFlow` proves this construction using
the complete executed compiler and only the cited flow contract. -/
def AlmostTwoSatFptSolverExists : Prop :=
  ∃ (F : RAM.Stmt) (T : ℕ → ℕ → ℕ), Almost2SatSolver F T ∧ FPTBound T

end STACS2027.Runtimes.BoundedCost

namespace STACS2027.Runtimes

open STACS2027 STACS2027.RAM

/-- General fixed-length cycle enumeration by an actual bounded RAM program.
`generalCycleEnumerationRam` proves this label-independent brute-force bound.
The cited output-sensitive four-cycle bound is verified separately. -/
def GeneralCycleEnumerationRam : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ (E : RAM.Stmt) (C : ℕ), ∀ g : Graph,
    ∃ (cs : List Cycle) (steps : ℕ), cs.Perm (cycles g k) ∧
      RAM.ComputesIn E (graphInput g) cs.flatten steps
        (C * (g.length + 1) ^ (2 * k + 4)) ∧
      steps ≤ C * (g.length + 1) ^ (2 * k + 4)

end STACS2027.Runtimes
