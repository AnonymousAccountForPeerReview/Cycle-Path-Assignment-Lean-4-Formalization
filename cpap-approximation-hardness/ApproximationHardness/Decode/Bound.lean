module

public import ApproximationHardness.Decode.Family
import Lean.Elab.Tactic.Omega

/-!
# The decoding map satisfies the second L-reduction inequality
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem sum_flatMap_range {α : Type} (n : Nat) (F : Nat → List α) (g : α → Nat) :
    (((List.range n).flatMap F).map g).sum = ((List.range n).map fun j => ((F j).map g).sum).sum := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.flatMap_append, ih]

/-- On the gadget family, the clause load at a port is the weight of the clause gadgets there. -/
theorem clauseLoad_family {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) (pick : Cycle → Nat) (hpick : ∀ c ∈ formulaFamily k hk f, pick c ∈ c)
    {v : Nat} (hv : v < variableBound f) {i : Nat} (hi : i < 3) :
    clauseLoad k (chosenFamily (formulaFamily k hk f) pick) v i =
      portWeight (placeFormula [] f).length (clauseAt f) (portLoadC k hk f pick) v i := by
  rw [clauseLoad_eq, formulaFamily_choices, List.map_append, List.sum_append]
  have hV : ((globalVariablePaths f (variableChosen k hk pick)).map (loadTerm k v i)).sum = 0 := by
    unfold globalVariablePaths
    rw [sum_flatMap_range]
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    obtain ⟨v', _, rfl⟩ := List.mem_map.mp hx
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    exact loadTerm_variable hk pick hp
  rw [hV, Nat.zero_add]
  unfold globalClausePaths portWeight
  rw [sum_flatMap_range]
  congr 1
  apply List.map_congr_left
  intro j hjm
  have hj := List.mem_range.mp hjm
  -- the clause part
  have hpj : ∀ c ∈ placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], pick c ∈ c := by
    intro c hc
    apply hpick
    apply List.mem_append_right
    apply List.mem_flatten.mpr
    refine ⟨placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j], ?_, hc⟩
    exact List.mem_mapIdx.mpr ⟨j, hj, rfl⟩
  have hL : ((clauseChosen k hk f pick j).map (loadTerm k v i)).sum = load (clauseChosen k hk f pick j) (portEdgeG k v i) := by
    unfold load
    congr 1
    apply List.map_congr_left
    intro p hp
    rw [clauseChosen_at hk f pick j hj] at hp
    exact loadTerm_clause hk hf hd pick hv hj hp hpj
  rw [hL]
  -- the weight
  have hcl : clauseAt f j = (placeFormula [] f)[j] := clauseAt_eq hj
  have hmem : (placeFormula [] f)[j] ∈ placeFormula [] f := List.getElem_mem hj
  have hterm : ∀ q ∈ ((clauseAt f j).filter fun p => p.literal.var == v).filter fun p => p.port == i,
      portLoadC k hk f pick j q = load (clauseChosen k hk f pick j) (portEdgeG k v i) := by
    intro q hq
    have h1 := (List.mem_filter.mp hq).2
    have h2 := (List.mem_filter.mp (List.mem_filter.mp hq).1).2
    simp only [beq_iff_eq] at h1 h2
    unfold portLoadC literalPortGlobal portEdgeG
    rw [h1, h2]
  rw [List.map_congr_left hterm]
  have hlen : (((clauseAt f j).filter fun p => p.literal.var == v).filter fun p => p.port == i).length ≤ 1 := by
    have := placed_clause_filter_var_length hd hmem v
    rw [← hcl] at this
    exact Nat.le_trans (List.length_filter_le _ _) this
  generalize hF : ((clauseAt f j).filter fun p => p.literal.var == v).filter (fun p => p.port == i) = F at hlen hterm
  match F, hlen with
  | [], _ =>
    -- no occurrence of `v` at port `i`: the clause gadget does not contain the port edge
    simp only [List.map_nil, List.sum_nil]
    refine (load_zero_iff _ _).mpr ?_
    intro p hp hE
    rw [clauseChosen_at hk f pick j hj] at hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    have hcyc := placedClauseFamily_valid hk hf ⟨j, hj⟩ c hc
    have hEc := hcyc.2.2.2 _ (List.mem_filter.mp hE).1
    obtain ⟨i', q, -, hq, hvq, heq⟩ := formulaGraph_shared_edge hv hj (portEdgeG_mem k v hi) hEc
    have hqm : q ∈ (placeFormula [] f)[j] := List.mem_of_getElem? hq
    have hport := (hf.placed_clause_bounds hmem q hqm).2
    have hpi : q.port = i := (portEdgeG_inj hport hi (heq.symm.trans rfl)).trans rfl
    have : q ∈ ((clauseAt f j).filter fun p => p.literal.var == v).filter fun p => p.port == i := by
      rw [hcl]
      simp [hqm, hvq, hpi]
    rw [hF] at this
    simp at this
  | [x], _ => simp

theorem weightedLoad_state {k : Nat} (hk : 5 ≤ k) (t : Bool) (w : Nat → Nat) :
    weightedLoad (variableExpandedState k hk t) variablePortEdge w = if t then w 1 + w 2 else w 0 := by
  obtain ⟨h0, h1, h2⟩ := variablePortEdge_values
  obtain ⟨l0, l2, l1⟩ := variableExpandedState_loads hk t
  rw [weightedLoad_eq, h0, h1, h2, l0, l1, l2]
  cases t <;> simp

/-- **The decoding map is an L-reduction decoder** (the second inequality with `β = 1`): for every
assignment `ps` of the Theorem 8 graph of a Definition 7 formula, `S* + C* ≤ s(decodeAssign k ps) + c(ps)`,
that is, `S* − s(A) ≤ c(τ) − C*` for `A = decodeAssign k ps`. -/
theorem decode_error_bound_explicit {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) {S C : Nat} (hS : IsMaxSat f S)
    (hC : IsMinCost (formulaGraph k f) k C) (ps : List (List Edge))
    (hv : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) :
    S + C ≤ satisfiedCount (decodeAssign k ps) f + cost ps := by
  obtain ⟨pick, hpick, hcost, hΦ⟩ := decoder_transport hk hf hd hv
  let W := portWeight (placeFormula [] f).length (clauseAt f) (portLoadC k hk f pick)
  have hW1 : ∀ v i, W v i ≤ 1 := fun v i => portWeight_le_one hk hf pick hpick v i
  have hCL : ∀ v, v < variableBound f → ∀ i, i < 3 → clauseLoad k ps v i = W v i := by
    intro v hv' i hi
    rw [clauseLoad_eq, hΦ (loadTerm k v i) (fun p q h => loadTerm_perm k v i h), ← clauseLoad_eq,
      clauseLoad_family hk hf hd pick hpick hv' hi]
  have ha : ∀ v, v < variableBound f →
      weightedLoad (variableExpandedState k hk (decodeAssign k ps v)) variablePortEdge (W v) ≤
        cost (variableChosen k hk pick v) +
        weightedLoad (variableChosen k hk pick v)
          (fun i => mapEdge (blockVertex (gadgetWidth k) v) (variablePortEdge i)) (W v) := by
    intro v hv'
    obtain ⟨t, ht⟩ := variableChosen_weighted_normalizes hk v pick
      (fun c hc => hpick c (formulaFamily_variable_mem hk f hv' hc)) (W v) (hW1 v)
    refine Nat.le_trans ?_ ht
    rw [weightedLoad_state, weightedLoad_state]
    unfold decodeAssign
    rw [hCL v hv' 0 (by decide), hCL v hv' 1 (by decide), hCL v hv' 2 (by decide)]
    by_cases hle : W v 1 + W v 2 ≤ W v 0
    · simp only [hle, decide_true, ite_true]
      cases t <;> simp <;> omega
    · simp only [hle, decide_false]
      cases t <;> simp <;> omega
  have hlow := formulaFamily_cost_lower_bound_of hk hf hd pick hpick (decodeAssign k ps) ha
  rw [hcost] at hlow
  have := minCost_add_maxSat hk hf hd hS hC
  omega

/-- **Theorem 11 with an explicit decoding map**: for every `k ≥ 5`, every Definition 7 formula `f`
and every assignment `ps` of `formulaGraph k f`, the truth assignment `decodeAssign k ps` satisfies
the second L-reduction inequality with `β = 1`. -/
theorem cpap_lreduction_decoder {k : Nat} (hk : 5 ≤ k) :
    ∀ f, LeOneLeTwoCNF f → ∀ S C, IsMaxSat f S → IsMinCost (formulaGraph k f) k C →
      ∀ ps, ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps →
        S + C ≤ satisfiedCount (decodeAssign k ps) f + cost ps :=
  fun _f hf _ _ hS hC ps hv => decode_error_bound_explicit hk hf.1 hf.2 hS hC ps hv

end STACS2027
