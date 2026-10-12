module

public import BoundedCost.Sizes
public import BoundedCost.NamedHoles

/-!
# Paper interface: Section 4 and Appendix B of the accompanying paper

This module restates the development in the manuscript's terms. It adds no
construction; each theorem is proved from the development.

Theorem 4 states that, for `k ≥ 3`, an assignment for `CPAP(G, k)` of cost at most `Ψ`
can be found, or its nonexistence certified, in time
`O(15^Ψ Ψ ((Ψ+1)k²t + kt²)³ + k²t + kt² + Υ_k)`. Its proof (Appendix B, Algorithm 3)
handles `k ≤ 4` by the min-cost flow of Section 3 and, for `k ≥ 5`, encodes the problem
into Almost 2-SAT: the path constraints `Γ₁`, the overlap constraints `λ_u`, the
formula `Γ_𝓘`, and the replicated formula `Γ'`. What is formalized is the encoding,
which the manuscript notes "is valid for every `k ≥ 4`": the correctness of `Γ_𝓘`, the
correctness of clause deletion in `Γ'`, and the counts of variables, path constraints
and candidate overlaps that give the size of `Γ'`. The running time of the cited
Almost 2-SAT algorithm (ANONYMIZED and ANONYMIZED), of 2-SAT (ANONYMIZED, ANONYMIZED and ANONYMIZED)
and of cycle enumeration are not formalized. The correctness of the steps of Algorithm 3
itself — the `k`-cycle core, the deleted overlaps, the recovery of the paths, the case
`Ψ = 0`, and computing `OPT` by increasing `Ψ` — is in `BoundedCost.Algorithm3` and the
modules it imports.

Corollary 5 states that a zero-cost assignment can be found, or its nonexistence
certified, in time `O(k²t + Υ_k)` for `k ≥ 4`. What is formalized is its linear-size
2-CNF encoding: the prefix clauses replacing the pairwise overlap constraints, the
equivalence with the existence of a zero-cost assignment, and the size of the formula.
-/

@[expose] public section
namespace STACS2027.Paper
open Complexity.SAT

/-! ## The encoding -/

/-- "For each `C ∈ 𝒞_k` and `e ∈ E(C)`, introduce a Boolean variable `b_{C,e}`": the
variable of the `j`-th edge of the `i`-th cycle is `b_{C_i, e} = i·k + j`, and distinct
pairs get distinct variables below `kt`. -/
theorem path_variables (g : Graph) (k : Nat) :
    (∀ i j, i < (cycles g k).length → j < k → pathVariable k i j < k * (cycles g k).length) ∧
    (∀ i j i' j', j < k → j' < k → pathVariable k i j = pathVariable k i' j' → i = i' ∧ j = j') ∧
    ∀ i, i < (cycles g k).length → ∀ e ∈ cycleEdges (kCycle g k i),
      edgeVariable g k i e = pathVariable k i (edgePosition g k i e) ∧
        cycleEdgeAt g k i (edgePosition g k i e) = e :=
  ⟨fun _ _ hi hj => pathVariable_lt hi hj,
   fun _ _ _ _ hj hj' h => pathVariable_inj hj hj' h,
   fun _ hi _e he => ⟨rfl, cycleEdgeAt_edgePosition hi he⟩⟩

/-- `Γ₁` "contains the path constraints `¬b_{C,e_a} ∨ ¬b_{C,e_b}` for every `C ∈ 𝒞_k` and
every vertex-disjoint pair `e_a, e_b ∈ E(C)`". -/
theorem path_constraints (g : Graph) (k : Nat) (cl : Clause) :
    cl ∈ pathConstraints g k ↔
      ∃ i a b, i < (cycles g k).length ∧ a < b ∧ b < k ∧
        disjointEdges (cycleEdgeAt g k i a) (cycleEdgeAt g k i b) = true ∧
        cl = [⟨pathVariable k i a, false⟩, ⟨pathVariable k i b, false⟩] :=
  mem_pathConstraints g k cl

/-- The candidate overlaps `𝒰 = {(e, {C, C'}) : {C, C'} ∈ (𝒞_k choose 2), e ∈ E(C) ∩ E(C')}`,
each listed once, with the two cycles in index order. -/
theorem candidate_overlaps (g : Graph) (k : Nat) :
    (∀ u, u ∈ candidateOverlaps g k ↔
      ∃ i i' e, i < i' ∧ i' < (cycles g k).length ∧
        e ∈ cycleEdges (kCycle g k i) ∧ e ∈ cycleEdges (kCycle g k i') ∧ u = (i, i', e)) ∧
    (candidateOverlaps g k).Nodup :=
  ⟨mem_candidateOverlaps g k, candidateOverlaps_nodup g k⟩

/-- "For each `u = (e, {C, C'}) ∈ 𝒰`, the overlap constraint `λ_u = b_{C,e} ∨ b_{C',e}`". -/
theorem overlap_constraint (g : Graph) (k : Nat) (u : Nat × Nat × Edge) :
    overlapClause g k u = [⟨edgeVariable g k u.1 u.2.2, true⟩, ⟨edgeVariable g k u.2.1 u.2.2, true⟩] :=
  rfl

/-- `Γ_𝓘 = Γ₁ ∧ ⋀_{u ∈ 𝒰 ∖ 𝓘} λ_u`. -/
theorem permitted_formula (g : Graph) (k : Nat) (permitted : List (Nat × Nat × Edge)) :
    permittedFormula g k permitted =
      pathConstraints g k ++
        ((candidateOverlaps g k).filter fun u => !permitted.contains u).map (overlapClause g k) :=
  rfl

/-- `Γ'` is `Ψ + 1` copies of `Γ₁` followed by every `λ_u`, "retaining repeated clauses as
distinct occurrences". -/
theorem replicated_formula (g : Graph) (k Ψ : Nat) :
    almostFormula g k Ψ =
      (List.replicate (Ψ + 1) (pathConstraints g k)).flatten ++
        (candidateOverlaps g k).map (overlapClause g k) :=
  rfl

/-! ## Appendix B: correctness of the encoding -/

/-- "`Γ_𝓘` is satisfiable exactly when an assignment exists whose overlaps all belong to `𝓘`"
(for `k ≥ 4`). -/
theorem encoding_correct {k : Nat} (hk : 4 ≤ k) (g : Graph) (permitted : List (Nat × Nat × Edge)) :
    Satisfiable (permittedFormula g k permitted) ↔
      ∃ f : Nat → List Edge, PathsOf g k f ∧
        ∀ u ∈ candidateOverlaps g k, violatedBy f u = true → u ∈ permitted :=
  permittedFormula_satisfiable_iff hk permitted

/-- "The minimum number of overlap constraints whose deletion makes `Γ_∅` satisfiable, while
retaining `Γ₁`, is exactly `OPT`": an assignment of cost at most `Ψ` exists iff some set
`𝓘 ⊆ 𝒰` of at most `Ψ` candidate overlaps makes `Γ_𝓘` satisfiable. -/
theorem clause_deletion_correct {k : Nat} (hk : 4 ≤ k) (g : Graph) (Ψ : Nat) :
    HasAssignment g k Ψ ↔
      ∃ permitted : List (Nat × Nat × Edge), permitted.Sublist (candidateOverlaps g k) ∧
        permitted.length ≤ Ψ ∧ Satisfiable (permittedFormula g k permitted) := by
  constructor
  · rintro ⟨ps, hv, hc⟩
    obtain ⟨hf, hps⟩ := pathsOf_of_validChoices hv
    rw [hps, cost_eq_countP_violated g k hf] at hc
    refine ⟨(candidateOverlaps g k).filter (violatedBy fun i => ps.getD i []),
      List.filter_sublist, ?_, ?_⟩
    · rw [← List.countP_eq_length_filter]
      exact hc
    · exact (permittedFormula_satisfiable_iff hk _).mpr
        ⟨_, hf, fun u hu hv => List.mem_filter.mpr ⟨hu, hv⟩⟩
  · rintro ⟨permitted, _, hlen, hsat⟩
    obtain ⟨f, hf, hperm⟩ := (permittedFormula_satisfiable_iff hk permitted).mp hsat
    refine ⟨_, validChoices_of_pathsOf hf, ?_⟩
    rw [cost_eq_countP_violated g k hf, List.countP_eq_length_filter]
    refine Nat.le_trans ?_ hlen
    apply List.Nodup.length_le_of_subset
    · exact List.filter_sublist.nodup (candidateOverlaps_nodup g k)
    · intro u hu
      have := List.mem_filter.mp hu
      exact hperm u this.1 this.2

/-! ## Theorem 4 -/

/-- **Theorem 4**, the encoding: "Almost 2-SAT accepts `Γ'` exactly when a cycle-path
assignment of cost at most `Ψ` exists" (for `k ≥ 4`). -/
theorem boundedCost_encoding {k : Nat} (hk : 4 ≤ k) (g : Graph) (Ψ : Nat) :
    AlmostSatisfiable (almostFormula g k Ψ) Ψ ↔ HasAssignment g k Ψ :=
  almostSatisfiable_iff_hasAssignment hk g Ψ

/-- Theorem 4, "Running time": "there are `kt` Boolean variables and `k(k−3)t/2` path
constraints", `|𝒰| ≤ kt²/2`, every clause has two literals, and `Γ'` has
`(Ψ+1)|Γ₁| + |𝒰|` clause occurrences. -/
theorem boundedCost_encoding_size (g : Graph) (k Ψ : Nat) :
    (∀ cl ∈ almostFormula g k Ψ, cl.length = 2 ∧ ∀ l ∈ cl, l.var < k * (cycles g k).length) ∧
    2 * (pathConstraints g k).length = k * (k - 3) * (cycles g k).length ∧
    2 * (candidateOverlaps g k).length ≤ k * (cycles g k).length * ((cycles g k).length - 1) ∧
    (almostFormula g k Ψ).length =
      (Ψ + 1) * (pathConstraints g k).length + (candidateOverlaps g k).length :=
  almostFormula_size g k Ψ

/-! ## Corollary 5 -/

/-- The prefix encoding: "for an edge `e` contained in cycles `C₁, …, C_p`", the clauses
`b_{C_i,e} ∨ s_{e,i}` (`1 ≤ i < p`), `¬s_{e,i−1} ∨ s_{e,i}` (`1 < i < p`) and
`b_{C_i,e} ∨ ¬s_{e,i−1}` (`1 < i ≤ p`), indexed from `0` here. -/
theorem prefix_clauses (g : Graph) (k : Nat) (e : Edge) (cl : Clause) :
    cl ∈ prefixClauses g k e ↔
      (∃ x, x < (cyclesThrough g k e).length - 1 ∧
        cl = [⟨edgeVariable g k ((cyclesThrough g k e).getD x 0) e, true⟩,
              ⟨prefixVariable g k e x, true⟩]) ∨
      (∃ x, 0 < x ∧ x < (cyclesThrough g k e).length - 1 ∧
        cl = [⟨prefixVariable g k e (x - 1), false⟩, ⟨prefixVariable g k e x, true⟩]) ∨
      (∃ x, 0 < x ∧ x < (cyclesThrough g k e).length ∧
        cl = [⟨edgeVariable g k ((cyclesThrough g k e).getD x 0) e, true⟩,
              ⟨prefixVariable g k e (x - 1), false⟩]) :=
  mem_prefixClauses g k e cl

/-- "No auxiliary variables or clauses are needed when `p ≤ 1`", and the auxiliary
variables of distinct edges, or distinct indices, are distinct and lie below `2kt`. -/
theorem prefix_variables (g : Graph) (k : Nat) :
    (∀ e, (cyclesThrough g k e).length ≤ 1 → prefixClauses g k e = []) ∧
    (∀ e ∈ edgesOnCycles g k, ∀ x, x < (cyclesThrough g k e).length - 1 →
      prefixVariable g k e x < 2 * (k * (cycles g k).length)) ∧
    ∀ e ∈ edgesOnCycles g k, ∀ e' ∈ edgesOnCycles g k, ∀ x x',
      x < (cyclesThrough g k e).length - 1 → x' < (cyclesThrough g k e').length - 1 →
      prefixVariable g k e x = prefixVariable g k e' x' → e = e' ∧ x = x' := by
  refine ⟨?_, fun e he x hx => prefixVariable_lt he hx,
    fun e he e' he' x x' hx hx' h => prefixVariable_inj he he' hx hx' h⟩
  intro e hp
  have h0 : (cyclesThrough g k e).length - 1 = 0 := by omega
  simp only [prefixClauses, h0, List.range_zero, List.map_nil, List.filterMap_nil, List.nil_append]
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  have := List.mem_range.mp hx
  have : x = 0 := by omega
  subst this
  rfl

/-- Corollary 5, the exact count added in the paper: an edge in `p ≥ 2` cycles
uses exactly `p − 1` distinct auxiliary variables and `3p − 4` clause occurrences. -/
theorem prefix_encoding_count (g : Graph) (k : Nat) (e : Edge)
    (hp : 2 ≤ (cyclesThrough g k e).length) :
    ((List.range ((cyclesThrough g k e).length - 1)).map (prefixVariable g k e)).length =
      (cyclesThrough g k e).length - 1 ∧
    ((List.range ((cyclesThrough g k e).length - 1)).map (prefixVariable g k e)).Nodup ∧
    (prefixClauses g k e).length = 3 * (cyclesThrough g k e).length - 4 :=
  ⟨(prefixAuxiliaryVariables_count g k e).1,
    (prefixAuxiliaryVariables_count g k e).2, prefixEncodingClauseCount g k e hp⟩

/-- **Corollary 5**, the encoding: the zero-cost formula `Γ₁` plus the prefix clauses is
satisfiable iff "a zero-cost cycle-path assignment" exists (for `k ≥ 4`). -/
theorem zeroCost_encoding {k : Nat} (hk : 4 ≤ k) (g : Graph) :
    Satisfiable (zeroCostFormula g k) ↔ HasAssignment g k 0 :=
  zeroCostFormula_satisfiable_iff hk g

/-- Corollary 5, the size: "the resulting formula has `O(kt)` variables and `O(k²t)`
clauses" — every clause has two literals on variables below `2kt`, and there are at most
`|Γ₁| + 3kt` clauses, where `2|Γ₁| = k(k−3)t`. -/
theorem zeroCost_encoding_size (g : Graph) (k : Nat) :
    (∀ cl ∈ zeroCostFormula g k, cl.length = 2 ∧ ∀ l ∈ cl, l.var < 2 * (k * (cycles g k).length)) ∧
    (zeroCostFormula g k).length ≤ (pathConstraints g k).length + 3 * (k * (cycles g k).length) ∧
    2 * (pathConstraints g k).length = k * (k - 3) * (cycles g k).length :=
  zeroCostFormula_size g k

end STACS2027.Paper
