module

public import ApproximationHardness.Registered.Correct
public import ApproximationHardness.LReduction
public import ApproximationHardness.InstanceMap
import Lean.Elab.Tactic.Omega

/-!
# Theorem 11's instance map in the registered machine model

Section 6 requires the instance map of an L-reduction to be computable in
polynomial time. Here the map `f ↦ (formulaGraph k f).reverse` of Theorem 11 is
computed, on the codes `encode f` of the registered foundation, by a single-tape
machine of the foundation's model (`NPCompleteness-Lean4`) within a polynomial
number of steps (`Complexity.PolyTime`): its output is the code of a record list
(`CPAP` instance format of the Section 5 entry) that writes exactly this graph.
-/

@[expose] public section

namespace STACS2027

open Complexity
open Complexity.SAT

/-- **Theorem 11 with a registered-model polynomial-time instance map.** For every
`k ≥ 5` there is a word function `g` computed by a single-tape machine of the
registered foundation in polynomial time (`PolyTime g`) such that, on the code of
every Definition 7 formula `f`, `g` outputs the code of a record list that writes
the graph `(formulaGraph k f).reverse` (with budget `0`), and
`f ↦ (formulaGraph k f).reverse` is an L-reduction from MAX-(≤1,≤2)-SAT to
`CPAP(G, k)` with `α = 5/3`, `β = 1`. -/
theorem cpap_lreduction_polyTime {k : Nat} (hk : 5 ≤ k) :
    ∃ g : Complexity.Word → Complexity.Word, PolyTime g ∧
      (∀ f, LeOneLeTwoCNF f → ∃ recs, g (encode f) = encode recs ∧
        GraphOutput recs (formulaGraph k f).reverse 0) ∧
      LReductionToCPAP LeOneLeTwoCNF (fun f => (formulaGraph k f).reverse) k 5 3 1 1 := by
  refine ⟨Registered.instanceMapWord k, Registered.polyTime_instanceMapWord k, ?_, (cpap_lreduction_computed hk).1⟩
  intro f hf
  refine ⟨(Registered.formulaRecords k f).reverse, Registered.instanceMapWord_encode k f hf.1.1, ?_⟩
  exact Registered.GraphOutput.reverse (Registered.formulaRecords_output k f)

end STACS2027
