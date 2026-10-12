module

public import ApproximationHardness.Soundness

/-!
# Completeness: an assignment of cost at most `2m − s(A)`

Proof of Theorem 11, first part: "any truth assignment `A` determines the paths in the
variable gadgets. The clause gadgets can then be assigned paths of cost one for each
satisfied clause and cost two for each unsatisfied clause, giving total cost
`s(A) + 2(m − s(A)) = 2m − s(A)`."

The variable gadgets take their truth states (cost `0`); a satisfied clause gadget uses
the Theorem 8 witness of one of its true literals, which loads no port of a false literal;
an unsatisfied clause gadget uses the witness of its first literal, whose port is the only
one it loads, at most once, against a variable load of one.
-/

set_option maxRecDepth 100000

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- The assignment `a` with the value of `v` flipped. -/
def flipAt (a : Assignment) (v : Nat) : Assignment := fun x => if x = v then !(a x) else a x

theorem evalLiteral_flipAt_self (a : Assignment) (l : Literal) :
    evalLiteral (flipAt a l.var) l = !(evalLiteral a l) := by
  simp [evalLiteral, flipAt]
  cases l.positive <;> simp

theorem evalLiteral_flipAt_other (a : Assignment) {l : Literal} {v : Nat} (h : l.var ≠ v) :
    evalLiteral (flipAt a v) l = evalLiteral a l := by
  simp [evalLiteral, flipAt, h]

/-- A clause gadget witness for an unsatisfied clause: cost one, loading no literal port
other than that of the first literal. -/
theorem placedClause_unsat_witness {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) (a : Assignment) (j : Fin (placeFormula [] f).length)
    (hunsat : ∀ p ∈ (placeFormula [] f)[j.val], evalLiteral a p.literal = false) :
    ∃ choose : Cycle → Nat,
      (∀ c ∈ placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val], choose c ∈ c) ∧
      cost (chosenFamily (placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val]) choose) = 1 ∧
      (∀ p ∈ (placeFormula [] f)[j.val], p ≠ (placeFormula [] f)[j.val].getD 0 defaultPlaced →
        load (chosenFamily (placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val]) choose)
          (literalPortGlobal k p) = 0) := by
  have hsize := hf.placed_clause_size (List.getElem_mem j.isLt)
  have hpos : 0 < (placeFormula [] f)[j.val].length := by omega
  let p₀ := (placeFormula [] f)[j.val].getD 0 defaultPlaced
  have hp₀ : p₀ ∈ (placeFormula [] f)[j.val] := by
    show (placeFormula [] f)[j.val].getD 0 defaultPlaced ∈ _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos]
    exact List.getElem_mem hpos
  let a' := flipAt a p₀.literal.var
  have hvars := hd.placed (List.getElem_mem j.isLt)
  have hother : ∀ p ∈ (placeFormula [] f)[j.val], p ≠ p₀ → p.literal.var ≠ p₀.literal.var := by
    intro p hp hne he
    exact hne (nodup_map_injective_on (fun p => p.literal.var) hvars hp hp₀ he)
  obtain ⟨choose, hchoose, hcost, hload⟩ := placedClause_sat_witness hk hf a' j
    ⟨p₀, hp₀, by
      show evalLiteral (flipAt a p₀.literal.var) p₀.literal = true
      rw [evalLiteral_flipAt_self, hunsat p₀ hp₀]
      rfl⟩
  refine ⟨choose, hchoose, hcost, ?_⟩
  intro p hp hne
  apply hload p hp
  show evalLiteral (flipAt a p₀.literal.var) p.literal = false
  rw [evalLiteral_flipAt_other a (hother p hp hne)]
  exact hunsat p hp

/-- For every truth assignment `A`, the Theorem 8 graph has a cycle-path assignment of cost at
most `2m − s(A)`. -/
theorem formulaGraph_cost_upper_bound {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) (a : Assignment) :
    ∃ choose : Cycle → Nat, (∀ c ∈ formulaFamily k hk f, choose c ∈ c) ∧
      cost (chosenFamily (formulaFamily k hk f) choose) + satisfiedCount a f ≤ 2 * f.length := by
  classical
  -- the variable gadgets take their truth states
  let Vpick := fun v => Classical.choose (placedVariable_sat_witness hk hf a v)
  have hVspec := fun v => Classical.choose_spec (placedVariable_sat_witness hk hf a v)
  -- each clause gadget takes a witness of cost one
  have hCexists : ∀ j : Fin (placeFormula [] f).length, ∃ pick : Cycle → Nat,
      (∀ c ∈ placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val], pick c ∈ c) ∧
      cost (chosenFamily (placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val]) pick) = 1 ∧
      ((∃ p ∈ (placeFormula [] f)[j.val], evalLiteral a p.literal = true) →
        ∀ p ∈ (placeFormula [] f)[j.val], evalLiteral a p.literal = false →
          load (chosenFamily (placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val]) pick)
            (literalPortGlobal k p) = 0) ∧
      ((∀ p ∈ (placeFormula [] f)[j.val], evalLiteral a p.literal = false) →
        ∀ p ∈ (placeFormula [] f)[j.val], p ≠ (placeFormula [] f)[j.val].getD 0 defaultPlaced →
          load (chosenFamily (placedClauseFamily k hk (variableBound f) j.val (placeFormula [] f)[j.val]) pick)
            (literalPortGlobal k p) = 0) := by
    intro j
    by_cases hsat : ∃ p ∈ (placeFormula [] f)[j.val], evalLiteral a p.literal = true
    · obtain ⟨pick, hv, hc, hl⟩ := placedClause_sat_witness hk hf a j hsat
      refine ⟨pick, hv, hc, fun _ => hl, fun hall => ?_⟩
      obtain ⟨p, hp, hpt⟩ := hsat
      rw [hall p hp] at hpt
      cases hpt
    · have hall : ∀ p ∈ (placeFormula [] f)[j.val], evalLiteral a p.literal = false := by
        intro p hp
        cases h : evalLiteral a p.literal
        · rfl
        · exact absurd ⟨p, hp, h⟩ hsat
      obtain ⟨pick, hv, hc, hl⟩ := placedClause_unsat_witness hk hf hd a j hall
      exact ⟨pick, hv, hc, fun h => absurd h hsat, fun _ => hl⟩
  let Cpick := fun j => if hj : j < (placeFormula [] f).length then Classical.choose (hCexists ⟨j, hj⟩) else fun _ => 0
  have hCspec : ∀ j, ∀ hj : j < (placeFormula [] f).length,
      (∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], Cpick j c ∈ c) ∧
      cost (chosenFamily (placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j]) (Cpick j)) = 1 ∧
      ((∃ p ∈ (placeFormula [] f)[j], evalLiteral a p.literal = true) →
        ∀ p ∈ (placeFormula [] f)[j], evalLiteral a p.literal = false →
          load (chosenFamily (placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j]) (Cpick j))
            (literalPortGlobal k p) = 0) ∧
      ((∀ p ∈ (placeFormula [] f)[j], evalLiteral a p.literal = false) →
        ∀ p ∈ (placeFormula [] f)[j], p ≠ (placeFormula [] f)[j].getD 0 defaultPlaced →
          load (chosenFamily (placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j]) (Cpick j))
            (literalPortGlobal k p) = 0) := by
    intro j hj
    simpa only [Cpick, dite_eq_left hj] using Classical.choose_spec (hCexists ⟨j, hj⟩)
  -- combine
  let pick : Sum Nat Nat → Cycle → Nat := Sum.elim Vpick Cpick
  have hn : ((gadgetIndices f).flatMap (indexedFamily k hk f)).Nodup := by
    rw [formulaFamily_indexed]
    exact distinctCycles_nodup (formulaFamily_distinct hk hf hd)
  obtain ⟨choose, hcombine⟩ := combine_indexed_choices (gadgetIndices f) (indexedFamily k hk f) pick hn
  have hchooseV : ∀ v, v < variableBound f → ∀ c ∈ placedVariableFamily k hk v, choose c = Vpick v c :=
    fun v hv c hc => hcombine (.inl v) (gadgetIndex_variable_mem f hv) c hc
  have hchooseC : ∀ j, ∀ hj : j < (placeFormula [] f).length,
      ∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], choose c = Cpick j c := by
    intro j hj c hc
    apply hcombine (.inr j) (gadgetIndex_clause_mem f hj) c
    rw [indexedFamily_clause_at hk f hj]
    exact hc
  have hVeq : ∀ v, v < variableBound f → variableChosen k hk choose v =
      chosenFamily (placedVariableFamily k hk v) (Vpick v) :=
    fun v hv => List.map_congr_left (fun c hc => congrArg (selectedAt c) (hchooseV v hv c hc))
  have hCeq : ∀ j, ∀ hj : j < (placeFormula [] f).length, clauseChosen k hk f choose j =
      chosenFamily (placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j]) (Cpick j) := by
    intro j hj
    rw [clauseChosen_at hk f choose j hj]
    exact List.map_congr_left (fun c hc => congrArg (selectedAt c) (hchooseC j hj c hc))
  have hchoose : ∀ c ∈ formulaFamily k hk f, choose c ∈ c := by
    intro c hc
    rw [← formulaFamily_indexed] at hc
    obtain ⟨id, hid, hc⟩ := List.mem_flatMap.mp hc
    rw [hcombine id hid c hc]
    cases id with
    | inl v => exact (hVspec v).1 c hc
    | inr j =>
      have hj : j < (placeFormula [] f).length := by simpa [gadgetIndices] using hid
      rw [indexedFamily_clause_at hk f hj] at hc
      exact (hCspec j hj).1 c hc
  refine ⟨choose, hchoose, ?_⟩
  -- the cost
  rw [cost_formulaFamily_eq hk hf hd choose]
  have hvarcost : ((List.range (variableBound f)).map fun v => cost (variableChosen k hk choose v)).sum = 0 := by
    apply sum_map_eq_zero
    intro v hv
    rw [hVeq v (List.mem_range.mp hv)]
    exact (hVspec v).2.1
  have hclause : ∀ j, j < (placeFormula [] f).length →
      cost (clauseChosen k hk f choose j) +
        ((clauseAt f j).map fun p => portLoadV k hk choose p * portLoadC k hk f choose j p).sum ≤
      1 + (if evalClause a (f.getD j []) then 0 else 1) := by
    intro j hj
    obtain ⟨_, hcost, hsatload, hunsatload⟩ := hCspec j hj
    rw [evalClause_placed hj a, clauseAt_eq hj]
    have hVload : ∀ p ∈ (placeFormula [] f)[j], portLoadV k hk choose p = if evalLiteral a p.literal then 0 else 1 := by
      intro p hp
      have hpv := (hf.placed_clause_bounds (List.getElem_mem hj) p hp).1
      unfold portLoadV
      rw [hVeq _ hpv]
      exact (hVspec p.literal.var).2.2 p (List.mem_flatten.mpr ⟨_, List.getElem_mem hj, hp⟩) rfl
    have hCload : ∀ p, portLoadC k hk f choose j p =
        load (chosenFamily (placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j]) (Cpick j))
          (literalPortGlobal k p) := by
      intro p
      unfold portLoadC
      rw [hCeq j hj]
    have hcost' : cost (clauseChosen k hk f choose j) = 1 := by rw [hCeq j hj]; exact hcost
    rw [hcost']
    cases hsat : (placeFormula [] f)[j].any fun p => evalLiteral a p.literal
    · -- unsatisfied: only the first literal's port is loaded, at most once
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hall : ∀ p ∈ (placeFormula [] f)[j], evalLiteral a p.literal = false := by
        intro p hp
        cases h : evalLiteral a p.literal
        · rfl
        · have : ((placeFormula [] f)[j].any fun p => evalLiteral a p.literal) = true :=
            List.any_eq_true.mpr ⟨p, hp, h⟩
          rw [hsat] at this
          cases this
      have hnodup : (placeFormula [] f)[j].Nodup :=
        List.Pairwise.of_map PlacedLiteral.key (fun _ _ h he => h (congrArg PlacedLiteral.key he))
          (hf.placed_clause_nodup (List.getElem_mem hj))
      have hsize := hf.placed_clause_size (List.getElem_mem hj)
      have hpos : 0 < (placeFormula [] f)[j].length := by omega
      have hp₀ : (placeFormula [] f)[j].getD 0 defaultPlaced ∈ (placeFormula [] f)[j] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos]
        exact List.getElem_mem hpos
      have hterm : ∀ p ∈ (placeFormula [] f)[j], portLoadV k hk choose p * portLoadC k hk f choose j p ≤
          if decide (p = (placeFormula [] f)[j].getD 0 defaultPlaced) then 1 else 0 := by
        intro p hp
        by_cases hpe : p = (placeFormula [] f)[j].getD 0 defaultPlaced
        · simp only [hpe, decide_true, ↓reduceIte]
          rw [← hpe, hVload p hp, hall p hp]
          have h1 : portLoadC k hk f choose j p ≤ 1 :=
            clauseChosen_port_load_le_one hk hf hj choose
              (fun c hc => hchoose c (formulaFamily_clause_mem hk f ⟨j, hj⟩ hc)) hp
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_mul]
          exact h1
        · simp only [hpe, decide_false]
          rw [hCload, hunsatload hall p hp hpe]
          simp
      refine Nat.le_trans (Nat.add_le_add_left (sum_map_le_sum_map _ _ _ hterm) 1) ?_
      rw [sum_map_countP_eq_length]
      have : ((placeFormula [] f)[j].countP fun p => decide (p = (placeFormula [] f)[j].getD 0 defaultPlaced)) =
          (placeFormula [] f)[j].count ((placeFormula [] f)[j].getD 0 defaultPlaced) := by
        rw [List.count_eq_countP]
        apply List.countP_congr
        intro p _
        simp
      rw [this, hnodup.count_of_mem hp₀]
      exact Nat.le_refl _
    · -- satisfied: no port carries both loads
      simp only [↓reduceIte, Nat.add_zero]
      have hsome : ∃ p ∈ (placeFormula [] f)[j], evalLiteral a p.literal = true := by
        obtain ⟨p, hp, h⟩ := List.any_eq_true.mp hsat
        exact ⟨p, hp, h⟩
      have hzero : ((placeFormula [] f)[j].map fun p => portLoadV k hk choose p * portLoadC k hk f choose j p).sum = 0 := by
        apply sum_map_eq_zero
        intro p hp
        cases h : evalLiteral a p.literal
        · rw [hCload, hsatload hsome p hp h]; simp
        · rw [hVload p hp, h]; simp
      rw [hzero]
      exact Nat.le_refl _
  have hrhs : ((List.range (placeFormula [] f).length).map fun j =>
      1 + (if evalClause a (f.getD j []) then 0 else 1)).sum =
      (placeFormula [] f).length +
        ((List.range (placeFormula [] f).length).map fun j => if evalClause a (f.getD j []) then 0 else 1).sum := by
    rw [sum_map_add, sum_map_const_one, List.length_range]
  have hsum : ((List.range (placeFormula [] f).length).map fun j => cost (clauseChosen k hk f choose j) +
      ((clauseAt f j).map fun p => portLoadV k hk choose p * portLoadC k hk f choose j p).sum).sum ≤
      ((List.range (placeFormula [] f).length).map fun j => 1 + (if evalClause a (f.getD j []) then 0 else 1)).sum :=
    sum_map_le_sum_map _ _ _ fun j hj => hclause j (List.mem_range.mp hj)
  rw [hrhs] at hsum
  have hunsat := unsatisfied_sum f a
  have hm := placeFormula_length [] f
  rw [← hm] at hunsat
  omega

/-- For every truth assignment `A`, `CPAP(G, k)` has an assignment of cost at most `2m − s(A)`
on the Theorem 8 graph `G` of `f`. -/
theorem formulaGraph_hasAssignment_of_satisfiedCount {k : Nat} (hk : 5 ≤ k) {f : CNF}
    (hf : BoundedOccurrence f) (hd : ClauseVariablesDistinct f) (a : Assignment) :
    HasAssignment (formulaGraph k f) k (2 * f.length - satisfiedCount a f) := by
  obtain ⟨choose, hchoose, hcost⟩ := formulaGraph_cost_upper_bound hk hf hd a
  apply (formulaGraph_assignment_iff_family hk hf hd _).mpr
  refine ⟨choose, hchoose, ?_⟩
  change cost (chosenFamily (formulaFamily k hk f) choose) ≤ _
  omega

end STACS2027
