module

public import NPHardness.PlacedWitnesses

/-! Combining independently chosen local assignments without identifying
different cycles or silently discarding any global cycle. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem combine_indexed_choices {α : Type} (ids : List α) (cs : α → List Cycle)
    (pick : α → Cycle → Nat) (hn : (ids.flatMap cs).Nodup) :
    ∃ choose : Cycle → Nat, ∀ id ∈ ids, ∀ c ∈ cs id, choose c = pick id c := by
  let entries := ids.flatMap fun id => (cs id).map fun c => (id,c)
  have hentries : entries.map Prod.snd = ids.flatMap cs := by
    simp [entries,List.map_flatMap,List.map_map,Function.comp_def]
  obtain ⟨choose,hchoose⟩ := image_choice_for_nodup entries Prod.snd
    (fun entry => pick entry.1 entry.2) (hentries ▸ hn)
  refine ⟨choose,?_⟩
  intro id hid c hc
  exact hchoose (id,c) (List.mem_flatMap.mpr ⟨id,hid,List.mem_map.mpr ⟨c,hc,rfl⟩⟩)

def gadgetIndices (f : CNF) : List (Sum Nat Nat) :=
  (List.range (variableBound f)).map Sum.inl ++ (List.range (placeFormula [] f).length).map Sum.inr

noncomputable def indexedFamily (k : Nat) (hk : 5 ≤ k) (f : CNF) : Sum Nat Nat → List Cycle
  | .inl v => placedVariableFamily k hk v
  | .inr j => placedClauseFamily k hk (variableBound f) j ((placeFormula [] f)[j]?.getD [])

theorem formulaFamily_indexed {k : Nat} (hk : 5 ≤ k) (f : CNF) :
    (gadgetIndices f).flatMap (indexedFamily k hk f) = formulaFamily k hk f := by
  unfold gadgetIndices formulaFamily
  rw [mapIdx_eq_range _ []]
  simp only [List.flatMap,List.map_append,List.map_map,List.flatten_append,indexedFamily,Function.comp_def]

theorem gadgetIndex_variable_mem (f : CNF) {v : Nat} (hv : v < variableBound f) :
    Sum.inl v ∈ gadgetIndices f := by simp [gadgetIndices,hv]

theorem gadgetIndex_clause_mem (f : CNF) {j : Nat} (hj : j < (placeFormula [] f).length) :
    Sum.inr j ∈ gadgetIndices f := by simp [gadgetIndices,hj]

theorem indexedFamily_clause_at {k : Nat} (hk : 5 ≤ k) (f : CNF) {j : Nat}
    (hj : j < (placeFormula [] f).length) :
    indexedFamily k hk f (.inr j) = placedClauseFamily k hk (variableBound f) j (placeFormula [] f)[j] := by
  simp [indexedFamily,List.getElem?_eq_getElem hj]

theorem formulaGraph_satisfied_crossCost_zero {k : Nat} {f : CNF} (_hf : BoundedOccurrence f)
    (a : Assignment) (V C : Nat → List (List Edge))
    (hV : ∀ v, v < variableBound f → ∀ p ∈ V v, p ⊆ placedVariableGraph k v)
    (hC : ∀ j, ∀ hj : j < (placeFormula [] f).length, ∀ p ∈ C j,
      p ⊆ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j])
    (htrue : ∀ v, v < variableBound f → ∀ p ∈ (placeFormula [] f).flatten,
      p.literal.var = v → evalLiteral a p.literal = true → load (V v) (literalPortGlobal k p) = 0)
    (hfalse : ∀ j, ∀ hj : j < (placeFormula [] f).length, ∀ p ∈ (placeFormula [] f)[j],
      evalLiteral a p.literal = false → load (C j) (literalPortGlobal k p) = 0)
    (j : Nat) (hj : j < (placeFormula [] f).length) :
    crossCost (globalVariablePaths f V) (C j) = 0 := by
  apply (crossCost_zero_iff _ _).mpr
  intro p hp q hq
  obtain ⟨v,hv,hp⟩ := List.mem_flatMap.mp hp
  have hv' := List.mem_range.mp hv
  unfold overlap
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro n hn
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hn
  apply List.count_eq_zero_of_not_mem
  intro heq
  obtain ⟨i,lit,_,hip,hvar,hport⟩ := formulaGraph_shared_edge hv' hj (hV v hv' p hp he) (hC j hj q hq heq)
  have heport : e = literalPortGlobal k lit := by simpa only [literalPortGlobal,variablePortEdge,hvar] using hport
  have hlit := List.mem_of_getElem? hip
  have hflat := List.mem_flatten.mpr ⟨_,List.getElem_mem hj,hlit⟩
  cases htruth : evalLiteral a lit.literal with
  | false =>
    have hz := hfalse j hj lit hlit htruth
    exact (load_zero_iff (C j) _).mp hz q hq (heport ▸ heq)
  | true =>
    have hz := htrue v hv' lit hflat hvar.symm htruth
    exact (load_zero_iff (V v) _).mp hz p hp (heport ▸ he)

end STACS2027
