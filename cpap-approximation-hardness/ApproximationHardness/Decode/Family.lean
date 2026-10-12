module

public import ApproximationHardness.Decode.Explicit
import Lean.Elab.Tactic.Omega

/-!
# The clause loads of the gadget family

On the chosen paths of the gadget family, `clauseLoad` is the weight `portWeight` the clause
gadgets put on the ports of the variable gadgets (`clauseLoad_family`).
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem selectedAt_length {g : Graph} {k : Nat} {c : Cycle} (hc : IsCycle g k c) {x : Nat} (hx : x ∈ c) :
    (selectedAt c x).length = k - 2 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [← (selected_perm_selectedAt hc hi).length_eq]
  unfold selected
  rw [pathEdges_length, List.length_take, List.length_append, List.length_drop, List.length_take, hc.2.1]
  have := hc.1
  have : i < k := hc.2.1 ▸ hi
  rw [Nat.min_eq_left (by omega)]
  omega

/-- The summand of `clauseLoad`. -/
def loadTerm (k v i : Nat) (p : List Edge) : Nat :=
  if outsideBlock k v p then p.count (portEdgeG k v i) else 0

theorem clauseLoad_eq (k : Nat) (ps : List (List Edge)) (v i : Nat) :
    clauseLoad k ps v i = (ps.map (loadTerm k v i)).sum := rfl

theorem loadTerm_perm (k v i : Nat) {p q : List Edge} (h : p.Perm q) : loadTerm k v i p = loadTerm k v i q := by
  unfold loadTerm; rw [outsideBlock_perm k v h, h.count_eq]

/-- A variable gadget's paths contribute nothing. -/
theorem loadTerm_variable {k : Nat} (hk : 5 ≤ k) (pick : Cycle → Nat) {v v' i : Nat}
    {p : List Edge} (hp : p ∈ variableChosen k hk pick v') : loadTerm k v i p = 0 := by
  have hsub := chosenFamily_supported (placedVariableFamily_valid hk) pick p hp
  have hblock : ∀ e ∈ p, blockOf k e.1 = v' ∧ blockOf k e.2 = v' := by
    intro e he
    have hg := hsub he
    rw [mem_mapGraph_edge hg] at hg
    obtain ⟨h1, h2⟩ := placedVariableGraph_endpoints hg
    exact ⟨blockOf_of_variableRegion h1, blockOf_of_variableRegion h2⟩
  unfold loadTerm
  by_cases hv : v' = v
  · subst hv
    have : outsideBlock k v' p = false := by
      unfold outsideBlock
      apply List.any_eq_false.mpr
      intro e he
      obtain ⟨h1, h2⟩ := hblock e he
      simp [h1, h2]
    simp [this]
  · have : p.count (portEdgeG k v i) = 0 := by
      apply List.count_eq_zero_of_not_mem
      intro hE
      have := (hblock _ hE).1
      rw [(portEdgeG_blocks k v i).1] at this
      exact hv this.symm
    simp [this]

/-- Two occurrences of the same variable in a placed clause are equal. -/
theorem placed_var_unique {f : CNF} (hd : ClauseVariablesDistinct f) {c : List PlacedLiteral}
    (hc : c ∈ placeFormula [] f) {q q' : PlacedLiteral} (hq : q ∈ c) (hq' : q' ∈ c)
    (he : q.literal.var = q'.literal.var) : q = q' := by
  have hl := placed_clause_filter_var_length hd hc q.literal.var
  have m1 : q ∈ c.filter fun p => p.literal.var == q.literal.var := List.mem_filter.mpr ⟨hq, by simp⟩
  have m2 : q' ∈ c.filter fun p => p.literal.var == q.literal.var := List.mem_filter.mpr ⟨hq', by simp [he]⟩
  generalize c.filter (fun p => p.literal.var == q.literal.var) = L at hl m1 m2
  match L, hl, m1, m2 with
  | [x], _, m1, m2 => simp at m1 m2; rw [m1, m2]

/-- An edge of a clause gadget with both endpoints in the block of `v` is the port of the clause's
occurrence of `v`. -/
theorem clause_edge_in_block {k : Nat} {f : CNF} (hf : BoundedOccurrence f) {v j : Nat}
    (hv : v < variableBound f) (hj : j < (placeFormula [] f).length) {e : Edge}
    (he : e ∈ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j])
    (h1 : blockOf k e.1 = v) (h2 : blockOf k e.2 = v) :
    ∃ q ∈ (placeFormula [] f)[j], q.literal.var = v ∧ q.port < 3 ∧ e = portEdgeG k v q.port := by
  have hee := mem_mapGraph_edge he
  rw [hee] at he
  obtain ⟨-, hV⟩ := clause_edge_between_variable_regions hf hv hv (j := ⟨j, hj⟩) he
    (variableRegion_of_blockOf h1) (variableRegion_of_blockOf h2)
  obtain ⟨i', q, -, hq, hvq, heq⟩ := formulaGraph_shared_edge hv hj hV he
  have hqm : q ∈ (placeFormula [] f)[j] := List.mem_of_getElem? hq
  have hport := (hf.placed_clause_bounds (List.getElem_mem hj) q hqm).2
  exact ⟨q, hqm, hvq.symm, hport, hee.trans heq⟩

/-- A clause gadget's path through the port leaves the block, so it counts fully. -/
theorem loadTerm_clause {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) (pick : Cycle → Nat) {v i j : Nat}
    (hv : v < variableBound f) (hj : j < (placeFormula [] f).length)
    {p : List Edge} (hp : p ∈ chosenFamily (placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j]) pick)
    (hpick : ∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], pick c ∈ c) :
    loadTerm k v i p = p.count (portEdgeG k v i) := by
  unfold loadTerm
  by_cases hE : portEdgeG k v i ∈ p
  · have hout : outsideBlock k v p = true := by
      cases hno : outsideBlock k v p with
      | true => rfl
      | false =>
        exfalso
        have hall : ∀ e ∈ p, blockOf k e.1 = v ∧ blockOf k e.2 = v := by
          intro e he
          have := List.any_eq_false.mp hno e he
          simpa using this
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
        have hcyc := placedClauseFamily_valid hk hf ⟨j, hj⟩ c hc
        have hsub : ∀ e ∈ selectedAt c (pick c), e ∈ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j] :=
          fun e he => hcyc.2.2.2 e (List.mem_filter.mp he).1
        obtain ⟨qE, hqE, hvE, -, hEq⟩ := clause_edge_in_block hf hv hj (hsub _ hE) (hall _ hE).1 (hall _ hE).2
        have hone : ∀ e ∈ selectedAt c (pick c), e = portEdgeG k v i := by
          intro e he
          obtain ⟨q, hq, hvq, -, heq⟩ := clause_edge_in_block hf hv hj (hsub e he) (hall e he).1 (hall e he).2
          have : q = qE := placed_var_unique hd (List.getElem_mem hj) hq hqE (hvq.trans hvE.symm)
          rw [heq, this, ← hEq]
        have hnd := selectedAt_nodup hcyc (pick c)
        have hlen := selectedAt_length hcyc (hpick c hc)
        have hsubl : selectedAt c (pick c) ⊆ [portEdgeG k v i] := fun e he => by simp [hone e he]
        have := hnd.length_le_of_subset hsubl
        simp at this
        omega
    simp [hout]
  · simp [List.count_eq_zero_of_not_mem hE]

end STACS2027
