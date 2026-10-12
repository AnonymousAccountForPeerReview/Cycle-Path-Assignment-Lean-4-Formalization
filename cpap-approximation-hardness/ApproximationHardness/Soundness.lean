module

public import ApproximationHardness.Normalization
public import ApproximationHardness.Optimization

/-!
# Soundness: `c(τ) ≥ 2m − s(A)` for the decoded assignment `A`

Proof of Theorem 11, second part: "let `τ` be any cycle-path assignment for `G`. Normalize
the variable-gadget paths without increasing the cost, as in Theorem 8. Decode a variable
as true when its positive attachment edge is omitted, and as false when both negative
attachment edges are omitted. For the resulting truth assignment `A`, every satisfied
clause contributes cost at least one and every unsatisfied clause contributes cost at
least two. Hence `c(τ) ≥ 2m − s(A)`."

The cost of `τ` is decomposed into the costs of the variable gadgets, the costs of the
clause gadgets and the loads at the shared literal ports (`cost_formulaFamily_eq`).
Regrouped by variable (`regroup_by_variable_port`), each variable gadget's share is at
least that of one of its truth states (`variableChosen_weighted_normalizes`), which
defines `A`. Each clause then contributes at least `1`, and at least `2` when all its
literals are false under `A` (`clauseChosen_blocked_lower`).
-/

set_option maxRecDepth 100000

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- The placed clause `j` (empty beyond the formula). -/
def clauseAt (f : CNF) (j : Nat) : List PlacedLiteral := (placeFormula [] f)[j]?.getD []

theorem clauseAt_eq {f : CNF} {j : Nat} (hj : j < (placeFormula [] f).length) :
    clauseAt f j = (placeFormula [] f)[j] := by
  simp [clauseAt, List.getElem?_eq_getElem hj]

/-- The load of the variable gadget of `p`'s variable at `p`'s port. -/
noncomputable def portLoadV (k : Nat) (hk : 5 ≤ k) (choose : Cycle → Nat) (p : PlacedLiteral) : Nat :=
  load (variableChosen k hk choose p.literal.var) (literalPortGlobal k p)

/-- The load of the clause gadget `j` at `p`'s port. -/
noncomputable def portLoadC (k : Nat) (hk : 5 ≤ k) (f : CNF) (choose : Cycle → Nat) (j : Nat) (p : PlacedLiteral) : Nat :=
  load (clauseChosen k hk f choose j) (literalPortGlobal k p)

/-- The load of the truth state `a (var p)` at `p`'s port: `0` if `p` is true, else `1`. -/
noncomputable def stateLoad (k : Nat) (hk : 5 ≤ k) (a : Assignment) (p : PlacedLiteral) : Nat :=
  load (variableExpandedState k hk (a p.literal.var)) (variablePortEdge p.port)

theorem stateLoad_eq {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f) (a : Assignment)
    {p : PlacedLiteral} (hp : p ∈ (placeFormula [] f).flatten) :
    stateLoad k hk a p = if evalLiteral a p.literal then 0 else 1 :=
  variableState_literal_load hk hf hp a

/-! ## The cost decomposition -/

theorem cost_formulaFamily_eq {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) (choose : Cycle → Nat) :
    cost (chosenFamily (formulaFamily k hk f) choose) =
      ((List.range (variableBound f)).map fun v => cost (variableChosen k hk choose v)).sum +
      ((List.range (placeFormula [] f).length).map fun j => cost (clauseChosen k hk f choose j) +
        ((clauseAt f j).map fun p => portLoadV k hk choose p * portLoadC k hk f choose j p).sum).sum := by
  rw [formulaFamily_choices, formulaGraph_cost_decomposition hf (variableChosen k hk choose)
    (clauseChosen k hk f choose)
    (fun v _ p hp => chosenFamily_supported (placedVariableFamily_valid hk) choose p hp)
    (fun j hj p hp => by
      rw [clauseChosen_at hk f choose j hj] at hp
      exact chosenFamily_supported (placedClauseFamily_valid hk hf ⟨j, hj⟩) choose p hp)]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  rw [crossCost_global_eq hk hf hd choose hj', clauseAt_eq hj']
  rfl

/-! ## Regrouping the port terms by variable and port -/

/-- The weight of port `i` of variable `v`: the total load the clause gadgets put there. -/
def portWeight (m : Nat) (cl : Nat → List PlacedLiteral) (B : Nat → PlacedLiteral → Nat) (v i : Nat) : Nat :=
  ((List.range m).map fun j =>
    ((((cl j).filter fun p => p.literal.var == v).filter fun p => p.port == i).map (B j)).sum).sum

theorem regroup_by_variable_port (m n : Nat) (cl : Nat → List PlacedLiteral)
    (hvar : ∀ j, j < m → ∀ p ∈ cl j, p.literal.var < n)
    (hport : ∀ j, j < m → ∀ p ∈ cl j, p.port < 3)
    (A : Nat → Nat → Nat) (B : Nat → PlacedLiteral → Nat) :
    ((List.range m).map fun j => ((cl j).map fun p => A p.literal.var p.port * B j p).sum).sum =
      ((List.range n).map fun v => ((List.range 3).map fun i => A v i * portWeight m cl B v i).sum).sum := by
  -- split each clause by variable
  have h1 : ((List.range m).map fun j => ((cl j).map fun p => A p.literal.var p.port * B j p).sum) =
      (List.range m).map fun j => ((List.range n).map fun v =>
        (((cl j).filter fun p => p.literal.var == v).map fun p => A p.literal.var p.port * B j p).sum).sum := by
    apply List.map_congr_left
    intro j hj
    rw [sum_partition _ _ n (hvar j (List.mem_range.mp hj))]
  rw [h1, sum_map_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro v _
  -- split each variable's literals by port
  have h2 : ((List.range m).map fun j =>
      (((cl j).filter fun p => p.literal.var == v).map fun p => A p.literal.var p.port * B j p).sum) =
      (List.range m).map fun j => ((List.range 3).map fun i =>
        ((((cl j).filter fun p => p.literal.var == v).filter fun p => p.port == i).map fun p =>
          A p.literal.var p.port * B j p).sum).sum := by
    apply List.map_congr_left
    intro j hj
    rw [sum_partition _ _ 3 (fun p hp => hport j (List.mem_range.mp hj) p (List.mem_filter.mp hp).1)]
  rw [h2, sum_map_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  unfold portWeight
  rw [← sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  rw [← sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hpi := (List.mem_filter.mp hp).2
  have hpv := (List.mem_filter.mp (List.mem_filter.mp hp).1).2
  simp only [beq_iff_eq] at hpi hpv
  rw [hpi, hpv]

/-- Each port of each variable gadget is loaded by at most one clause gadget, at most once. -/
theorem portWeight_le_one {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (choose : Cycle → Nat) (hv : ∀ c ∈ formulaFamily k hk f, choose c ∈ c) (v i : Nat) :
    portWeight (placeFormula [] f).length (clauseAt f) (portLoadC k hk f choose) v i ≤ 1 := by
  unfold portWeight
  have hle : ∀ j ∈ List.range (placeFormula [] f).length,
      ((((clauseAt f j).filter fun p => p.literal.var == v).filter fun p => p.port == i).map
        (portLoadC k hk f choose j)).sum ≤
      (clauseAt f j).countP fun p => decide (p.key = (v, i)) := by
    intro j hj
    have hj' := List.mem_range.mp hj
    refine Nat.le_trans (sum_map_le_sum_map _ _ (fun _ => 1) ?_) ?_
    · intro p hp
      have hp' : p ∈ (placeFormula [] f)[j] := by
        rw [← clauseAt_eq hj']
        exact (List.mem_filter.mp (List.mem_filter.mp hp).1).1
      exact clauseChosen_port_load_le_one hk hf hj' choose
        (fun c hc => hv c (formulaFamily_clause_mem hk f ⟨j, hj'⟩ hc)) hp'
    · rw [sum_map_const_one, List.filter_filter, ← List.countP_eq_length_filter]
      apply Nat.le_of_eq
      apply List.countP_congr
      intro p _
      simp [PlacedLiteral.key, and_comm]
  refine Nat.le_trans (sum_map_le_sum_map _ _ _ hle) ?_
  have hflat : ((List.range (placeFormula [] f).length).map fun j =>
      (clauseAt f j).countP fun p => decide (p.key = (v, i))).sum =
      (placeFormula [] f).flatten.countP fun p => decide (p.key = (v, i)) := by
    rw [List.countP_flatten, sum_map_eq_sum_range_getD _ []]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    simp [clauseAt, List.getD_eq_getElem?_getD]
  rw [hflat]
  have hn := hf.placement_keys_nodup
  have hcount := hn.count (a := (v, i))
  rw [List.count_eq_countP, List.countP_map] at hcount
  have : ((placeFormula [] f).flatten.countP fun p => decide (p.key = (v, i))) =
      (placeFormula [] f).flatten.countP ((fun x => x == (v, i)) ∘ PlacedLiteral.key) := by
    apply List.countP_congr; intro p _; simp
  rw [this, hcount]
  split <;> omega

/-! ## The per-clause bound -/

theorem evalClause_placed {f : CNF} {j : Nat} (hj : j < (placeFormula [] f).length) (a : Assignment) :
    evalClause a (f.getD j []) = (placeFormula [] f)[j].any fun p => evalLiteral a p.literal := by
  calc evalClause a (f.getD j [])
      = evalClause a (((placeFormula [] f).map (List.map PlacedLiteral.literal)).getD j []) := by
        rw [placeFormula_forget]
    _ = (placeFormula [] f)[j].any fun p => evalLiteral a p.literal := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
        simp [evalClause, List.any_map, Function.comp_def]

theorem clause_contribution {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (choose : Cycle → Nat) (hv : ∀ c ∈ formulaFamily k hk f, choose c ∈ c) (a : Assignment)
    {j : Nat} (hj : j < (placeFormula [] f).length) :
    1 + (if evalClause a (f.getD j []) then 0 else 1) ≤
      cost (clauseChosen k hk f choose j) +
        ((clauseAt f j).map fun p => stateLoad k hk a p * portLoadC k hk f choose j p).sum := by
  have hvC : ∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], choose c ∈ c :=
    fun c hc => hv c (formulaFamily_clause_mem hk f ⟨j, hj⟩ hc)
  rw [evalClause_placed hj a, clauseAt_eq hj]
  cases hsat : (placeFormula [] f)[j].any fun p => evalLiteral a p.literal
  · -- every literal is false: the sum is the full port load
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hall : ∀ p ∈ (placeFormula [] f)[j], evalLiteral a p.literal = false := by
      intro p hp
      cases h : evalLiteral a p.literal
      · rfl
      · have : ((placeFormula [] f)[j].any fun p => evalLiteral a p.literal) = true :=
          List.any_eq_true.mpr ⟨p, hp, h⟩
        rw [hsat] at this
        cases this
    have hsum : ((placeFormula [] f)[j].map fun p => stateLoad k hk a p * portLoadC k hk f choose j p).sum =
        ((placeFormula [] f)[j].map fun p => portLoadC k hk f choose j p).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [stateLoad_eq hk hf a (List.mem_flatten.mpr ⟨_, List.getElem_mem hj, hp⟩), hall p hp]
      simp
    rw [hsum]
    exact clauseChosen_blocked_lower hk hf hj choose hvC
  · simp only [↓reduceIte, Nat.add_zero]
    have := clauseChosen_cost_positive hk hf hj choose hvC
    omega

theorem unsatisfied_sum (f : CNF) (a : Assignment) :
    ((List.range f.length).map fun j => if evalClause a (f.getD j []) then 0 else 1).sum + satisfiedCount a f =
      f.length := by
  unfold satisfiedCount
  rw [← sum_map_eq_sum_range_getD f [] (fun c => if evalClause a c then 0 else 1)]
  have : (f.map fun c => if evalClause a c then 0 else 1).sum = f.countP fun c => !evalClause a c := by
    rw [← sum_map_countP_eq_length]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c _
    cases evalClause a c <;> simp
  rw [this]
  have h := List.length_eq_countP_add_countP (evalClause a) (l := f)
  have h2 : (f.countP fun c => ¬ evalClause a c = true) = f.countP fun c => !evalClause a c := by
    apply List.countP_congr; intro c _; simp
  omega

/-! ## Soundness -/

/-- The lower bound for a given truth assignment: if every variable gadget's truth state `a v`
is no worse than the chosen paths against the clause weights at its ports, then
`2m − s(a) ≤ c(τ)`. -/
theorem formulaFamily_cost_lower_bound_of {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) (choose : Cycle → Nat)
    (hv : ∀ c ∈ formulaFamily k hk f, choose c ∈ c) (a : Assignment)
    (ha : ∀ v, v < variableBound f →
      weightedLoad (variableExpandedState k hk (a v)) variablePortEdge
          (portWeight (placeFormula [] f).length (clauseAt f) (portLoadC k hk f choose) v) ≤
        cost (variableChosen k hk choose v) +
        weightedLoad (variableChosen k hk choose v)
          (fun i => mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i))
          (portWeight (placeFormula [] f).length (clauseAt f) (portLoadC k hk f choose) v)) :
    2 * f.length ≤ cost (chosenFamily (formulaFamily k hk f) choose) + satisfiedCount a f := by
  classical
  have hm := placeFormula_length [] f
  have hvar : ∀ j, j < (placeFormula [] f).length → ∀ p ∈ clauseAt f j, p.literal.var < variableBound f := by
    intro j hj p hp
    rw [clauseAt_eq hj] at hp
    exact (hf.placed_clause_bounds (List.getElem_mem hj) p hp).1
  have hport : ∀ j, j < (placeFormula [] f).length → ∀ p ∈ clauseAt f j, p.port < 3 := by
    intro j hj p hp
    rw [clauseAt_eq hj] at hp
    exact (hf.placed_clause_bounds (List.getElem_mem hj) p hp).2
  let W := portWeight (placeFormula [] f).length (clauseAt f) (portLoadC k hk f choose)
  rw [cost_formulaFamily_eq hk hf hd choose, sum_map_add]
  -- regroup the port terms of the chosen paths by variable and port
  have hV : ((List.range (placeFormula [] f).length).map fun j =>
      ((clauseAt f j).map fun p => portLoadV k hk choose p * portLoadC k hk f choose j p).sum).sum =
      ((List.range (variableBound f)).map fun v => weightedLoad (variableChosen k hk choose v)
        (fun i => mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i)) (W v)).sum := by
    exact regroup_by_variable_port _ _ (clauseAt f) hvar hport
      (fun v i => load (variableChosen k hk choose v) (mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i)))
      (portLoadC k hk f choose)
  -- regroup the port terms of the truth states by variable and port
  have hS : ((List.range (placeFormula [] f).length).map fun j =>
      ((clauseAt f j).map fun p => stateLoad k hk a p * portLoadC k hk f choose j p).sum).sum =
      ((List.range (variableBound f)).map fun v => weightedLoad (variableExpandedState k hk (a v)) variablePortEdge (W v)).sum := by
    exact regroup_by_variable_port _ _ (clauseAt f) hvar hport
      (fun v i => load (variableExpandedState k hk (a v)) (variablePortEdge i)) (portLoadC k hk f choose)
  have hnormsum : ((List.range (variableBound f)).map fun v =>
      weightedLoad (variableExpandedState k hk (a v)) variablePortEdge (W v)).sum ≤
      ((List.range (variableBound f)).map fun v => cost (variableChosen k hk choose v)).sum +
      ((List.range (variableBound f)).map fun v => weightedLoad (variableChosen k hk choose v)
        (fun i => mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i)) (W v)).sum := by
    rw [← sum_map_add]
    exact sum_map_le_sum_map _ _ _ fun v hv' => ha v (List.mem_range.mp hv')
  -- the per-clause bound
  have hclauses : ((List.range (placeFormula [] f).length).map fun j =>
      1 + (if evalClause a (f.getD j []) then 0 else 1)).sum ≤
      ((List.range (placeFormula [] f).length).map fun j => cost (clauseChosen k hk f choose j)).sum +
      ((List.range (placeFormula [] f).length).map fun j =>
        ((clauseAt f j).map fun p => stateLoad k hk a p * portLoadC k hk f choose j p).sum).sum := by
    rw [← sum_map_add]
    exact sum_map_le_sum_map _ _ _ fun j hj => clause_contribution hk hf choose hv a (List.mem_range.mp hj)
  rw [sum_map_add, sum_map_const_one] at hclauses
  have hunsat := unsatisfied_sum f a
  rw [← hm] at hunsat
  simp only [List.length_range] at hclauses
  omega


/-- For every choice of paths in the Theorem 8 graph of `f`, some truth assignment `A`
satisfies `2m − s(A) ≤ c(τ)`. -/
theorem formulaFamily_cost_lower_bound {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) (choose : Cycle → Nat)
    (hv : ∀ c ∈ formulaFamily k hk f, choose c ∈ c) :
    ∃ a : Assignment, 2 * f.length ≤ cost (chosenFamily (formulaFamily k hk f) choose) + satisfiedCount a f := by
  classical
  have hm := placeFormula_length [] f
  have hvar : ∀ j, j < (placeFormula [] f).length → ∀ p ∈ clauseAt f j, p.literal.var < variableBound f := by
    intro j hj p hp
    rw [clauseAt_eq hj] at hp
    exact (hf.placed_clause_bounds (List.getElem_mem hj) p hp).1
  have hport : ∀ j, j < (placeFormula [] f).length → ∀ p ∈ clauseAt f j, p.port < 3 := by
    intro j hj p hp
    rw [clauseAt_eq hj] at hp
    exact (hf.placed_clause_bounds (List.getElem_mem hj) p hp).2
  -- the weights put on the variable ports by the clause gadgets
  let W := portWeight (placeFormula [] f).length (clauseAt f) (portLoadC k hk f choose)
  have hW : ∀ v i, W v i ≤ 1 := fun v i => portWeight_le_one hk hf choose hv v i
  -- normalize each variable gadget
  have hnorm : ∀ v, v < variableBound f → ∃ t : Bool, weightedLoad (variableExpandedState k hk t) variablePortEdge (W v) ≤
      cost (variableChosen k hk choose v) +
        weightedLoad (variableChosen k hk choose v)
          (fun i => mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i)) (W v) := by
    intro v hv'
    exact variableChosen_weighted_normalizes hk v choose
      (fun c hc => hv c (formulaFamily_variable_mem hk f hv' hc)) (W v) (hW v)
  let a : Assignment := fun v => if h : v < variableBound f then Classical.choose (hnorm v h) else false
  have ha : ∀ v, v < variableBound f → weightedLoad (variableExpandedState k hk (a v)) variablePortEdge (W v) ≤
      cost (variableChosen k hk choose v) +
        weightedLoad (variableChosen k hk choose v)
          (fun i => mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i)) (W v) := by
    intro v hv'
    simpa only [a, dite_eq_left hv'] using Classical.choose_spec (hnorm v hv')
  exact ⟨a, formulaFamily_cost_lower_bound_of hk hf hd choose hv a ha⟩

end STACS2027
