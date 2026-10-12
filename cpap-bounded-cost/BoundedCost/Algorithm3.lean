module

public import BoundedCost.Algorithm3Core
public import BoundedCost.Algorithm3Search

/-!
# Algorithm 3 (`alg:BoundedCostFPT`): correctness for `k ≥ 4`

Algorithm 3 of Appendix B, for `k ≥ 4` and a budget `Ψ`, restricts `G` to its `k`-cycle
core, builds `Γ₁` and the overlap constraints, and then

* for `Ψ = 0`, solves `Γ_∅` by 2-SAT;
* for `Ψ ≥ 1`, calls Almost 2-SAT on `(Γ', Ψ)`, returns `⊥` if it fails, takes the deleted
  overlaps `𝓘` and solves `Γ_𝓘` by 2-SAT;

returns `⊥` if the 2-SAT call fails, and otherwise recovers the paths `τ(C)` from the truth
assignment. `algorithm3_correct` states that each step does what the proof of Theorem 4 says,
with the cited solvers (Almost 2-SAT, 2-SAT) left abstract: their outputs are quantified over.
Every assignment it returns is valid for `G` with cost at most `Ψ`, and it returns `⊥` only
when no such assignment exists. The building blocks are in `BoundedCost.Algorithm3Core` (the
core), `BoundedCost.Algorithm3Recovery` (the deleted overlaps and the recovery loop) and
`BoundedCost.Algorithm3Search` (the case `Ψ = 0` and computing `OPT` by increasing `Ψ`). The
min-cost flow branch for `k ≤ 4` (Section 3) and the running times are not covered here
(`k = 4` is covered through the encoding). An instance without `k`-cycles needs no special
case: the statements hold for it, with the empty assignment.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- **Algorithm 3**, correctness (for `k ≥ 4`), run on the `k`-cycle core `G_k` of `g`:
* for `Ψ ≥ 1` (and `Ψ = 0`): if Almost 2-SAT returns a deletion set, keeping the clauses `kept`
  of `Γ'` with at most `Ψ` deleted, then the deleted overlaps `𝓘` number at most `Ψ`, `Γ_𝓘` is
  satisfiable (2-SAT does not fail), and from every solution `σ` of `Γ_𝓘` the recovery loop
  returns an assignment for `CPAP(g, k)` of cost at most `Ψ`; if Almost 2-SAT returns `⊥`, no
  assignment of cost at most `Ψ` exists;
* for `Ψ = 0`: from every solution `σ` of `Γ_∅` the recovery loop returns an assignment of
  cost `0`; if `Γ_∅` is unsatisfiable, no assignment of cost `0` exists. -/
theorem algorithm3_correct {k : Nat} (hk : 4 ≤ k) (g : Graph) (Ψ : Nat) :
    (∀ kept : CNF, kept.Sublist (almostFormula (kCycleCore g k) k Ψ) →
      (almostFormula (kCycleCore g k) k Ψ).length ≤ kept.length + Ψ → Satisfiable kept →
        (deletedOverlaps (kCycleCore g k) k kept).length ≤ Ψ ∧
        Satisfiable (permittedFormula (kCycleCore g k) k (deletedOverlaps (kCycleCore g k) k kept)) ∧
        ∀ σ : Assignment,
          evalCNF σ (permittedFormula (kCycleCore g k) k (deletedOverlaps (kCycleCore g k) k kept)) = true →
            ValidChoices ((cycles g k).map selectedOptions) (recoverAssignment (kCycleCore g k) k σ) ∧
            cost (recoverAssignment (kCycleCore g k) k σ) ≤ Ψ) ∧
    (¬ AlmostSatisfiable (almostFormula (kCycleCore g k) k Ψ) Ψ → ¬ HasAssignment g k Ψ) ∧
    (∀ σ : Assignment, evalCNF σ (permittedFormula (kCycleCore g k) k []) = true →
      ValidChoices ((cycles g k).map selectedOptions) (recoverAssignment (kCycleCore g k) k σ) ∧
      cost (recoverAssignment (kCycleCore g k) k σ) = 0) ∧
    (¬ Satisfiable (permittedFormula (kCycleCore g k) k []) → ¬ HasAssignment g k 0) := by
  have hcyc := cycles_kCycleCore g k
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro kept hsub hlen ⟨τ, hτ⟩
    obtain ⟨hI, hσI⟩ := deletedOverlaps_spec (kCycleCore g k) k Ψ kept hsub hlen
    refine ⟨hI, ⟨τ, hσI τ hτ⟩, fun σ hσ => ?_⟩
    obtain ⟨hv, hc⟩ := recoverAssignment_correct hk (kCycleCore g k) _ σ hσ
    rw [hcyc] at hv
    exact ⟨hv, Nat.le_trans hc hI⟩
  · intro hnot hΨ
    exact hnot ((almostSatisfiable_iff_hasAssignment hk _ Ψ).mpr
      ((hasAssignment_kCycleCore_iff g k Ψ).mpr hΨ))
  · intro σ hσ
    obtain ⟨hv, hc⟩ := recoverAssignment_correct hk (kCycleCore g k) [] σ hσ
    rw [hcyc] at hv
    exact ⟨hv, Nat.le_zero.mp hc⟩
  · intro hnot h0
    exact hnot ((permittedFormula_nil_satisfiable_iff hk _).mpr
      ((hasAssignment_kCycleCore_iff g k 0).mpr h0))

end STACS2027
