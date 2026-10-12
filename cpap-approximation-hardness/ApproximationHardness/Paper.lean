module

public import ApproximationHardness.Composition
public import ApproximationHardness.InstanceMap
public import ApproximationHardness.RegisteredInstance
public import ApproximationHardness.LinearRAM
public import ApproximationHardness.Hardness.Main

/-!
# Paper interface: Section 6 and Appendix D of the accompanying paper

This module restates the development in the manuscript's terms. It adds no
construction; each theorem is proved from the development.

Theorem 11 states that, for every fixed `k ≥ 5`, `CPAP(G, k)` is MaxSNP-hard and APX-hard
on general graphs; Corollary 12 that, unless `P = NP`, it admits no PTAS. The proof
(Appendix D) is an L-reduction with `α = 5/3` and `β = 1` from MAX-(≤1,≤2)-SAT, through
the gadget construction of Theorem 8, and Lemma 10, an L-reduction with `α = β = 1` from
3-OCCURRENCE MAX-3-SAT, whose MaxSNP-completeness (ANONYMIZED and ANONYMIZED) and
APX-hardness (ANONYMIZED, from the PCP theorem) the manuscript cites. All of it is
formalized: the quantitative completeness and soundness of the Theorem 8 graph, the relation
`C* = 2m − S*`, the bound `S* ≥ 3m/4`, the two inequalities, Lemma 10's transformation and its
inequalities, their composition, and the polynomial-time computability of the maps in the
registered machine model; the cited results come from the MaxSNP-completeness formalization
Max3SAT-MaxSNP-APX-Lean4 (MaxSNP-completeness and APX-completeness of 3-OCCURRENCE
MAX-3-SAT, the PCP theorem and the inapproximability of MaxSNP-hard problems), to which
3-OCCURRENCE MAX-3-SAT, in that formalization's sense (`Complexity.max3SAT3`, whose clauses may
repeat literals or have fewer than two), is connected by a normalization (`Hardness.normalize`).
Theorem 11 and Corollary 12 are then proved for `CPAP(·, k)` as an optimization problem on words
(`cpapProblem k`): `maxSNP_hardness`, `apx_hardness`, `no_ptas`.
-/

@[expose] public section
namespace STACS2027.Paper
open Complexity.SAT

/-! ## The source problems -/

/-- MAX-(≤1,≤2)-SAT instances, as the Theorem 8 construction accepts them (Definition 7):
"two or three literals per clause, at most one positive occurrence per variable, and at
most two negative occurrences", with distinct variables in each clause. -/
theorem leOneLeTwoCNF_iff (f : CNF) :
    LeOneLeTwoCNF f ↔ BoundedOccurrence f ∧ ClauseVariablesDistinct f := Iff.rfl

/-- 3-OCCURRENCE MAX-3-SAT instances: "every clause contains two or three literals and every
variable occurs at most three times" (Appendix D), the literals of a clause being distinct. -/
theorem threeOccurrence_iff (f : CNF) :
    ThreeOccurrence f ↔ (∀ c ∈ f, c.length = 2 ∨ c.length = 3) ∧ (∀ c ∈ f, c.Nodup) ∧
      ∀ v, occurrences f v true + occurrences f v false ≤ 3 := Iff.rfl

/-- `s(A)`, `S* = max_A s(A)` and `C* = OPT_CPAP(G)` exist. -/
theorem optima_exist {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) :
    (∃ S, IsMaxSat f S) ∧ ∃ C, IsMinCost (formulaGraph k f) k C :=
  ⟨maxSat_exists f, minCost_exists (formulaGraph_hasAssignment_exists hk hf.1 hf.2)⟩

/-! ## Appendix D, proof of Theorem 11 -/

/-- "Any truth assignment `A` determines the paths in the variable gadgets. The clause gadgets
can then be assigned paths of cost one for each satisfied clause and cost two for each
unsatisfied clause, giving total cost `2m − s(A)`. In particular, `C* ≤ 2m − S*`." -/
theorem assignment_from_truth {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) (a : Assignment) :
    HasAssignment (formulaGraph k f) k (2 * f.length - satisfiedCount a f) :=
  formulaGraph_hasAssignment_of_satisfiedCount hk hf.1 hf.2 a

/-- "Conversely, let `τ` be any cycle-path assignment for `G`. Normalize the variable-gadget
paths without increasing the cost [...]. Decode a variable as true when its positive
attachment edge is omitted, and as false when both negative attachment edges are omitted.
[...] Hence `c(τ) ≥ 2m − s(A)`." -/
theorem truth_from_assignment {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f)
    (ps : List (List Edge)) (hv : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) :
    ∃ a : Assignment, 2 * f.length ≤ cost ps + satisfiedCount a f := by
  obtain ⟨choose, hchoose, hcost⟩ :=
    (formulaGraph_assignment_iff_family hk hf.1 hf.2 (cost ps)).mp ⟨ps, hv, Nat.le_refl _⟩
  obtain ⟨a, ha⟩ := formulaFamily_cost_lower_bound hk hf.1 hf.2 choose hchoose
  change cost (chosenFamily (formulaFamily k hk f) choose) ≤ cost ps at hcost
  exact ⟨a, by omega⟩

/-- "Together, the two directions establish the exact relation `C* = 2m − S*`." -/
theorem optimum_relation {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {S C : Nat}
    (hS : IsMaxSat f S) (hC : IsMinCost (formulaGraph k f) k C) : C + S = 2 * f.length :=
  cpap_optimum hk hf hS hC

/-- "A uniformly random truth assignment satisfies each clause with probability at least
`3/4`, so `S* ≥ 3m/4`." -/
theorem random_assignment_bound {f : CNF} (hf : LeOneLeTwoCNF f) {S : Nat} (hS : IsMaxSat f S) :
    3 * f.length ≤ 4 * S :=
  four_mul_maxSat hf.1 hf.2 hS

/-- "Therefore `C* = 2m − S* ≤ (5/3) S*`." -/
theorem alpha_condition {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {S C : Nat}
    (hS : IsMaxSat f S) (hC : IsMinCost (formulaGraph k f) k C) : 3 * C ≤ 5 * S :=
  three_mul_minCost_le hk hf.1 hf.2 hS hC

/-- "For any solution `τ`, the decoded assignment `A` satisfies
`S* − s(A) ≤ c(τ) − (2m − S*) = c(τ) − C*`." -/
theorem beta_condition {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {S C : Nat}
    (hS : IsMaxSat f S) (hC : IsMinCost (formulaGraph k f) k C) (ps : List (List Edge))
    (hv : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) :
    ∃ a : Assignment, S + C ≤ satisfiedCount a f + cost ps :=
  decode_error_bound hk hf.1 hf.2 hS hC ps hv

/-- **Theorem 11**, the L-reduction: "the construction is an L-reduction with `α = 5/3` and
`β = 1`" from MAX-(≤1,≤2)-SAT to `CPAP(G, k)`, for every `k ≥ 5`. -/
theorem gadget_lreduction {k : Nat} (hk : 5 ≤ k) : LReductionToCPAP LeOneLeTwoCNF (formulaGraph k) k 5 3 1 1 :=
  cpap_lreduction hk

/-! ## Appendix D, Lemma 10 -/

/-- Lemma 10's transformation: `r` deleted clauses, the remaining formula `ψ`, the
complemented formula `ψ'`, and `φ' = ψ'` with `r` clauses `(a_j ∨ b_j)` on fresh variables. -/
theorem polarize_construction (f : CNF) :
    polarize f = flipFormula (complemented f) (kept f) ++ padding (variableBound f) (deletedCount f) :=
  rfl

/-- The target formula "satisfies the required occurrence bounds" and has distinct variables in
each clause: it is a MAX-(≤1,≤2)-SAT instance of Definition 7. -/
theorem polarize_target {f : CNF} (hf : ThreeOccurrence f) : LeOneLeTwoCNF (polarize f) :=
  polarize_leOneLeTwo hf

/-- "`OPT(φ') = OPT(φ)`." -/
theorem polarize_optimum {f : CNF} {S S' : Nat} (hS : IsMaxSat f S) (hS' : IsMaxSat (polarize f) S') :
    S' = S :=
  (polarize_maxSat_eq hS hS').symm

/-- "Given any assignment of `φ'`, undo the complementations and restore the eliminated
variables. The recovered assignment satisfies all `r` deleted clauses and at least as many
clauses overall as the target assignment." -/
theorem polarize_recovery (f : CNF) (b : Assignment) :
    satisfiedCount (recover f b) (deletedClauses f) = deletedCount f ∧
      satisfiedCount b (polarize f) ≤ satisfiedCount (recover f b) f :=
  ⟨satisfiedCount_extendPure_deleted f _, satisfiedCount_recover f b⟩

/-- **Lemma 10**: "an L-reduction from 3-OCCURRENCE MAX-3-SAT with `α = β = 1`." -/
theorem leOneLeTwo_lreduction : (∀ f, ThreeOccurrence f → LeOneLeTwoCNF (polarize f)) ∧
    LReductionSat ThreeOccurrence polarize 1 1 1 1 :=
  STACS2027.leOneLeTwo_lreduction

/-- Theorem 11 from 3-OCCURRENCE MAX-3-SAT: the composed L-reduction, with `α = 5/3` and
`β = 1`. "Lemma 10 yields both hardness claims." -/
theorem gadget_lreduction_from_threeOccurrence {k : Nat} (hk : 5 ≤ k) :
    LReductionToCPAP ThreeOccurrence (fun f => formulaGraph k (polarize f)) k 5 3 1 1 :=
  threeOccurrence_cpap_lreduction hk

/-! ## Theorem 11: MaxSNP-hardness and APX-hardness -/

/-- `CPAP(·, k)` as an optimization problem: on the code of records writing a graph `G`, its
optimum is `C* = OPT_CPAP(G)`. -/
theorem cpapProblem_optimum {k : Nat} {recs : CNF} {g : Graph} (hG : GraphOutput recs g 0)
    {C : Nat} : (cpapProblem k).IsOpt (encode recs) C ↔ IsMinCost g k C :=
  cpapProblem_isOpt_iff hG

/-- Theorem 11's reduction at the level of optimization problems: for every `k ≥ 5`,
3-OCCURRENCE MAX-3-SAT L-reduces to `CPAP(·, k)`, with polynomial-time maps of the registered
model (normalization, Lemma 10, Theorem 8; the decoding map and Lemma 10's recovery). -/
theorem cpap_lReducible_paper {k : Nat} (hk : 5 ≤ k) :
    Complexity.LReducible Complexity.max3SAT3 (cpapProblem k) :=
  max3SAT3_lReducible_cpap hk

/-- **Theorem 11**: "For every fixed `k ≥ 5`, `CPAP(G, k)` is MaxSNP-hard." -/
theorem maxSNP_hardness {k : Nat} (hk : 5 ≤ k) : Complexity.MaxSNPHard (cpapProblem k) :=
  cpap_maxSNPHard hk

/-- **Theorem 11**: "... and APX-hard." -/
theorem apx_hardness {k : Nat} (hk : 5 ≤ k) : Complexity.APXHard (cpapProblem k) :=
  cpap_apxHard hk

/-! ## Corollary 12 -/

/-- **Corollary 12**: "Unless `P = NP`, `CPAP(G, k)` admits no PTAS for any fixed `k ≥ 5`." -/
theorem no_ptas {k : Nat} (hk : 5 ≤ k) : (cpapProblem k).HasPTAS → Complexity.PEqNP :=
  cpap_no_ptas hk

/-- Corollary 12, non-uniform form: not even one polynomial-time algorithm for each ratio
`1 + 1/(j+1)` exists unless `P = NP`. -/
theorem no_ptas_nonuniform {k : Nat} (hk : 5 ≤ k) :
    (∀ j, (cpapProblem k).ApproximableWithin (j + 2) (j + 1)) → Complexity.PEqNP :=
  cpap_not_approximable hk

/-- The mechanism of Corollary 12: a cycle-path assignment within a factor `1 + εn/εd` of
`C*` decodes to a truth assignment within a factor `1 − (5/3) εn/εd` of `S*`, so a PTAS for
`CPAP(G, k)` would give a PTAS for MAX-(≤1,≤2)-SAT (and, through Lemma 10, for
3-OCCURRENCE MAX-3-SAT). -/
theorem ptas_transfer {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {S C : Nat}
    (hS : IsMaxSat f S) (hC : IsMinCost (formulaGraph k f) k C) (ps : List (List Edge))
    (hv : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) (εn εd : Nat)
    (happrox : εd * cost ps ≤ (εd + εn) * C) :
    ∃ a : Assignment, 3 * εd * S ≤ 3 * εd * satisfiedCount a f + 5 * εn * S := by
  have := approximation_transfer (cpap_lreduction hk) hf hS hC ps hv εn εd happrox
  simpa using this

/-! ## Computability of the instance map (Section 6) -/

/-- The instance map of Theorem 11 "can be computed in polynomial time": on every Definition 7
formula with `n` variables, the Section 5 word machine (`Paper.gadget_reduction_linear_time` of that
entry, with the trivial endpoint table) performs no preprocessing and no padding and reaches
the Theorem 8 graph, listed in reverse, in at most `(n + 1)(128 k + 160)` transitions; and the
L-reduction of Theorem 11 holds for the graph as computed. -/
theorem instance_map_computed {k : Nat} (hk : 5 ≤ k) :
    LReductionToCPAP LeOneLeTwoCNF (fun f => (formulaGraph k f).reverse) k 5 3 1 1 ∧
    ∀ f, LeOneLeTwoCNF f → ∃ t,
      WordPipeline.Runs (WordPipeline.step (fun _ => false) k f.length) t
        (WordPipeline.initial f) (.done (formulaGraph k f).reverse) ∧
      t ≤ (variableBound f + 1) * (128 * k + 160) :=
  cpap_lreduction_computed hk

/-- On a Definition 7 formula, the full-domain construction of Section 5 (preprocessing,
padding, gluing) produces exactly the Theorem 8 graph. -/
theorem full_domain_is_gadget_graph (k : Nat) {f : CNF} (hf : LeOneLeTwoCNF f) :
    globalReductionGraph k f = formulaGraph k f :=
  globalReductionGraph_leOneLeTwo k hf

/-- Section 6 for Theorem 11, in the registered machine model: the instance map is computed by a
single-tape machine of the NP-completeness foundation in polynomial time (`Complexity.PolyTime`), on the
codes of the registered foundation, and the map it computes is the L-reduction of Theorem 11. -/
theorem gadget_polyTime_instance_map {k : Nat} (hk : 5 ≤ k) :
    ∃ g : Complexity.Word → Complexity.Word, Complexity.PolyTime g ∧
      (∀ f, LeOneLeTwoCNF f → ∃ recs, g (encode f) = encode recs ∧
        GraphOutput recs (formulaGraph k f).reverse 0) ∧
      LReductionToCPAP LeOneLeTwoCNF (fun f => (formulaGraph k f).reverse) k 5 3 1 1 :=
  cpap_lreduction_polyTime hk

/-- **Theorem 8**: "can be transformed in `O(n)` time", on the unit-cost RAM of `ApproximationHardness/RAM/Model.lean`,
in `O(n)` space as well. -/
theorem gadget_reduction_linear_time_ram {k : Nat} (hk : 5 ≤ k) :
    ∃ (prog : RAM.Stmt) (C : Nat), ∀ f, LeOneLeTwoCNF f →
      ∃ (es : List (Nat × Nat)) (t : Nat),
        RAM.ComputesIn prog (RAM.ramInput f) (f.length :: RAM.edgeWord es) t (C * (variableBound f + 1)) ∧
        t ≤ C * (variableBound f + 1) ∧ formulaGraph k f = es.map (fun e => edge e.1 e.2) ∧
        (Satisfiable f ↔ HasAssignment (formulaGraph k f) k f.length) :=
  gadget_reduction_linear_ram hk

end STACS2027.Paper
