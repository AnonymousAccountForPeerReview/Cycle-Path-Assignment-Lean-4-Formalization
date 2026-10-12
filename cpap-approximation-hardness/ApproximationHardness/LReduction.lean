module

public import ApproximationHardness.Completeness
public import ApproximationHardness.RandomAssignment
public import ApproximationHardness.Optima

/-!
# Theorem 11: the L-reduction from MAX-(≤1,≤2)-SAT to CPAP(G, k)

"Together, the two directions establish the exact relation `C* = 2m − S*`. It remains to
verify the two L-reduction inequalities. A uniformly random truth assignment satisfies
each clause with probability at least `3/4`, so `S* ≥ 3m/4`. Therefore
`C* = 2m − S* ≤ (5/3) S*`. For any solution `τ`, the decoded assignment `A` satisfies
`S* − s(A) ≤ c(τ) − (2m − S*) = c(τ) − C*`. Thus the construction is an L-reduction with
`α = 5/3` and `β = 1`."
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- Definition 7: the instances of MAX-(≤1,≤2)-SAT the construction of Theorem 8 accepts. -/
def LeOneLeTwoCNF (f : CNF) : Prop := BoundedOccurrence f ∧ ClauseVariablesDistinct f

/-- The Theorem 8 graph of `f` always has an assignment. -/
theorem formulaGraph_hasAssignment_exists {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f) :
    ∃ B, HasAssignment (formulaGraph k f) k B :=
  ⟨_, formulaGraph_hasAssignment_of_satisfiedCount hk hf hd fun _ => false⟩

/-- `C* = 2m − S*`, as `C* + S* = 2m`. -/
theorem minCost_add_maxSat {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) {S C : Nat} (hS : IsMaxSat f S)
    (hC : IsMinCost (formulaGraph k f) k C) : C + S = 2 * f.length := by
  obtain ⟨⟨a, ha⟩, hmax⟩ := hS
  obtain ⟨hC1, hC2⟩ := hC
  -- `C* ≤ 2m − S*`: the optimal truth assignment yields an assignment of that cost
  have hup := hC2 _ (formulaGraph_hasAssignment_of_satisfiedCount hk hf hd a)
  rw [ha] at hup
  have hSm : S ≤ f.length := by rw [← ha]; exact satisfiedCount_le a f
  -- `2m − S* ≤ C*`: the optimal cycle-path assignment decodes to a truth assignment
  obtain ⟨choose, hchoose, hcost⟩ := (formulaGraph_assignment_iff_family hk hf hd C).mp hC1
  obtain ⟨b, hb⟩ := formulaFamily_cost_lower_bound hk hf hd choose hchoose
  have hb' := hmax b
  change cost (chosenFamily (formulaFamily k hk f) choose) ≤ C at hcost
  omega

/-- `S* ≥ 3m/4`. -/
theorem four_mul_maxSat {f : CNF} (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f)
    {S : Nat} (hS : IsMaxSat f S) : 3 * f.length ≤ 4 * S := by
  obtain ⟨a, ha⟩ := exists_three_quarters (fun c hc => by rcases hf.1 c hc with h | h <;> omega) hd
  have := hS.2 a
  omega

/-- `C* ≤ (5/3) S*`. -/
theorem three_mul_minCost_le {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) {S C : Nat} (hS : IsMaxSat f S)
    (hC : IsMinCost (formulaGraph k f) k C) : 3 * C ≤ 5 * S := by
  have h1 := minCost_add_maxSat hk hf hd hS hC
  have h2 := four_mul_maxSat hf hd hS
  omega

/-- `S* − s(A) ≤ c(τ) − C*` for the truth assignment `A` decoded from any cycle-path
assignment `τ`. -/
theorem decode_error_bound {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) {S C : Nat} (hS : IsMaxSat f S)
    (hC : IsMinCost (formulaGraph k f) k C) (ps : List (List Edge))
    (hv : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) :
    ∃ a : Assignment, S + C ≤ satisfiedCount a f + cost ps := by
  have hassign : HasAssignment (formulaGraph k f) k (cost ps) := ⟨ps, hv, Nat.le_refl _⟩
  obtain ⟨choose, hchoose, hcost⟩ := (formulaGraph_assignment_iff_family hk hf hd _).mp hassign
  obtain ⟨a, ha⟩ := formulaFamily_cost_lower_bound hk hf hd choose hchoose
  change cost (chosenFamily (formulaFamily k hk f) choose) ≤ cost ps at hcost
  have := minCost_add_maxSat hk hf hd hS hC
  exact ⟨a, by omega⟩

/-- `C* = 2m − S*` on Definition 7 instances. -/
theorem cpap_optimum {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {S C : Nat}
    (hS : IsMaxSat f S) (hC : IsMinCost (formulaGraph k f) k C) : C + S = 2 * f.length :=
  minCost_add_maxSat hk hf.1 hf.2 hS hC

/-- **Theorem 11**, the L-reduction: for every `k ≥ 5`, the construction of Theorem 8 is an
L-reduction from MAX-(≤1,≤2)-SAT (on Definition 7 instances) to `CPAP(G, k)` with
`α = 5/3` and `β = 1`. -/
theorem cpap_lreduction {k : Nat} (hk : 5 ≤ k) :
    LReductionToCPAP LeOneLeTwoCNF (formulaGraph k) k 5 3 1 1 := by
  intro f hf S C hS hC
  refine ⟨three_mul_minCost_le hk hf.1 hf.2 hS hC, ?_⟩
  intro ps hv
  obtain ⟨a, ha⟩ := decode_error_bound hk hf.1 hf.2 hS hC ps hv
  exact ⟨a, by omega⟩

end STACS2027
