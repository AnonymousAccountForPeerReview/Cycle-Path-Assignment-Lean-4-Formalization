module

public import ApproximationHardness.Sums

/-!
# The variable–clause interaction as a sum over ports

In the Theorem 8 graph, a variable gadget and a clause gadget share only the
identified literal ports (`formulaGraph_shared_edge`). The cross cost between the
chosen paths of the two gadgets is therefore the sum, over those ports, of the
product of the two loads.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem crossCost_append_left (ps qs rs : List (List Edge)) :
    crossCost (ps ++ qs) rs = crossCost ps rs + crossCost qs rs := by
  simp [crossCost, List.map_append, List.sum_append]

theorem crossCost_flatMap_left {α : Type} (xs : List α) (P : α → List (List Edge))
    (rs : List (List Edge)) :
    crossCost (xs.flatMap P) rs = (xs.map fun x => crossCost (P x) rs).sum := by
  induction xs with
  | nil => simp [crossCost]
  | cons x xs ih => simp only [List.flatMap_cons, crossCost_append_left, ih, List.map_cons, List.sum_cons]

theorem sum_map_filter_of_zero {α : Type} (l : List α) (P : α → Bool) (f : α → Nat)
    (h : ∀ x ∈ l, P x = false → f x = 0) : ((l.filter P).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    rw [List.filter_cons]
    cases hx : P x
    · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, ih',
        h x List.mem_cons_self hx, Nat.zero_add]
    · simp only [↓reduceIte, List.map_cons, List.sum_cons, ih']

/-- The overlaps of a path `p` with the paths `qs`, as a sum over a nodup list `S`
containing every edge of `p` that lies on some path of `qs`. -/
theorem overlap_sum_eq_ports (p : List Edge) (qs : List (List Edge))
    {S : List Edge} (hS : S.Nodup) (hshared : ∀ e ∈ p, ∀ q ∈ qs, e ∈ q → e ∈ S) :
    (qs.map (overlap p)).sum = (S.map fun e => p.count e * load qs e).sum := by
  rw [overlap_family]
  have h1 : (S.map fun e => p.count e * load qs e).sum =
      (S.map fun e => (p.filter fun e => S.contains e).count e * load qs e).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro e he
    rw [List.count_filter (by simpa using he)]
  rw [h1, sum_counts S _ (load qs) hS (fun e he => by simpa using (List.mem_filter.mp he).2)]
  symm
  apply sum_map_filter_of_zero
  intro e he hnot
  apply (load_zero_iff qs e).mpr
  intro q hq heq
  have := hshared e he q hq heq
  simp_all

/-- The cross cost of two families of paths sharing edges only inside the nodup list `S` is
the sum over `S` of the products of the loads. -/
theorem crossCost_eq_ports (ps qs : List (List Edge)) {S : List Edge} (hS : S.Nodup)
    (hshared : ∀ p ∈ ps, ∀ e ∈ p, ∀ q ∈ qs, e ∈ q → e ∈ S) :
    crossCost ps qs = (S.map fun e => load ps e * load qs e).sum := by
  unfold crossCost
  have h1 : (ps.map fun p => (qs.map (overlap p)).sum) =
      ps.map fun p => (S.map fun e => p.count e * load qs e).sum := by
    apply List.map_congr_left
    intro p hp
    exact overlap_sum_eq_ports p qs hS (hshared p hp)
  rw [h1, sum_map_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  rw [sum_map_mul_right]
  rfl

theorem nodup_of_length_le_one {α : Type} {l : List α} (h : l.length ≤ 1) : l.Nodup := by
  match l, h with
  | [], _ => exact List.nodup_nil
  | [x], _ => exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

/-- With distinct variables in each clause, at most one literal of a placed clause names a
given variable. -/
theorem placed_clause_filter_var_length {f : CNF} (hd : ClauseVariablesDistinct f)
    {c : List PlacedLiteral} (hc : c ∈ placeFormula [] f) (v : Nat) :
    (c.filter fun p => p.literal.var == v).length ≤ 1 := by
  have hn := hd.placed hc
  have hcount := hn.count (a := v)
  rw [List.count_eq_countP, List.countP_map] at hcount
  rw [← List.countP_eq_length_filter]
  have : (c.countP fun p => p.literal.var == v) = c.countP ((fun x => x == v) ∘ fun p => p.literal.var) := by
    apply List.countP_congr; intro p _; simp
  rw [this, hcount]
  split <;> omega

/-- The literal ports of the literals of clause `j` naming the variable `v`: at most one. -/
def sharedPorts (k : Nat) (f : CNF) (v j : Nat) : List Edge :=
  (((placeFormula [] f)[j]?.getD []).filter fun p => p.literal.var == v).map (literalPortGlobal k)

theorem sharedPorts_nodup {f : CNF} (hd : ClauseVariablesDistinct f) (k v : Nat) {j : Nat}
    (hj : j < (placeFormula [] f).length) : (sharedPorts k f v j).Nodup := by
  apply nodup_of_length_le_one
  simp only [sharedPorts, List.getElem?_eq_getElem hj, Option.getD_some, List.length_map]
  exact placed_clause_filter_var_length hd (List.getElem_mem hj) v

/-- Every edge shared by a path in the variable gadget `v` and a path in the clause
gadget `j` is one of the shared ports. -/
theorem shared_edge_mem_sharedPorts {k : Nat} {f : CNF} {v j : Nat}
    (hv : v < variableBound f) (hj : j < (placeFormula [] f).length) {e : Edge}
    (heV : e ∈ placedVariableGraph k v)
    (heC : e ∈ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j]) :
    e ∈ sharedPorts k f v j := by
  obtain ⟨i, p, _, hip, hvar, rfl⟩ := formulaGraph_shared_edge hv hj heV heC
  simp only [sharedPorts, List.getElem?_eq_getElem hj, Option.getD_some, List.mem_map,
    List.mem_filter]
  refine ⟨p, ⟨List.mem_of_getElem? hip, by simp [hvar]⟩, ?_⟩
  simp only [literalPortGlobal, variablePortEdge, hvar]

/-- The cross cost between the chosen paths of variable gadget `v` and clause gadget `j`. -/
theorem crossCost_variable_clause {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) (choose : Cycle → Nat) {v : Nat} (hv : v < variableBound f)
    {j : Nat} (hj : j < (placeFormula [] f).length) :
    crossCost (variableChosen k hk choose v) (clauseChosen k hk f choose j) =
      ((sharedPorts k f v j).map fun e =>
        load (variableChosen k hk choose v) e * load (clauseChosen k hk f choose j) e).sum := by
  apply crossCost_eq_ports _ _ (sharedPorts_nodup hd k v hj)
  · intro p hp e he q hq heq
    have hpV : p ⊆ placedVariableGraph k v :=
      chosenFamily_supported (placedVariableFamily_valid hk) choose p hp
    rw [clauseChosen_at hk f choose j hj] at hq
    have hqC : q ⊆ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j] :=
      chosenFamily_supported (placedClauseFamily_valid hk hf ⟨j, hj⟩) choose q hq
    exact shared_edge_mem_sharedPorts hv hj (hpV he) (hqC heq)

/-- The cross cost between all variable gadgets and clause gadget `j`, as a sum over the
literals of clause `j`: the load of the literal's variable gadget at its port times the load
of the clause gadget there. -/
theorem crossCost_global_eq {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) (choose : Cycle → Nat) {j : Nat}
    (hj : j < (placeFormula [] f).length) :
    crossCost (globalVariablePaths f (variableChosen k hk choose)) (clauseChosen k hk f choose j) =
      ((placeFormula [] f)[j].map fun p =>
        load (variableChosen k hk choose p.literal.var) (literalPortGlobal k p) *
          load (clauseChosen k hk f choose j) (literalPortGlobal k p)).sum := by
  unfold globalVariablePaths
  rw [crossCost_flatMap_left]
  have h1 : ((List.range (variableBound f)).map fun v =>
      crossCost (variableChosen k hk choose v) (clauseChosen k hk f choose j)) =
      (List.range (variableBound f)).map fun v =>
        (((placeFormula [] f)[j].filter fun p => p.literal.var == v).map fun p =>
          load (variableChosen k hk choose p.literal.var) (literalPortGlobal k p) *
            load (clauseChosen k hk f choose j) (literalPortGlobal k p)).sum := by
    apply List.map_congr_left
    intro v hv
    rw [crossCost_variable_clause hk hf hd choose (List.mem_range.mp hv) hj]
    simp only [sharedPorts, List.getElem?_eq_getElem hj, Option.getD_some, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have := (List.mem_filter.mp hp).2
    simp only [beq_iff_eq] at this
    simp [this]
  rw [h1]
  exact sum_partition _ _ _ (fun p hp => (hf.placed_clause_bounds (List.getElem_mem hj) p hp).1) _

end STACS2027
