module

public import NPHardness.GlobalReduction
public import NPHardness.SizeBounds

/-! Linear output-size bounds. These count edge-list entries and do not
substitute for a running-time theorem in a machine model. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem clauseGraph_edge_bound {k : Nat} (hk : 5 ≤ k) (c : List PlacedLiteral) :
    (clauseGraph k c).length ≤ 10*k := by
  unfold clauseGraph
  split
  · rw [clauseTwoGraph_edge_count k hk]
    split <;> omega
  · rw [clauseThreeGraph_edge_count k hk]
    omega

theorem formulaGraph_edge_bound {k : Nat} (hk : 5 ≤ k) (f : CNF) :
    (formulaGraph k f).length ≤ variableBound f * (2*k) + f.length * (10*k) := by
  have hvar : ((List.range (variableBound f)).flatMap (placedVariableGraph k)).length =
      variableBound f * (2*k-1) := by
    rw [List.length_flatMap]
    have heq : ((List.range (variableBound f)).map fun v => (placedVariableGraph k v).length) =
        (List.range (variableBound f)).map (fun _ => 2*k-1) := by
      apply List.map_congr_left
      intro v _
      simpa only [placedVariableGraph,mapGraph,List.length_map] using variableGraph_edge_count k hk
    rw [heq,sum_map_const,List.length_range]
  have hclause : (((placeFormula [] f).mapIdx (fun j c => placedClauseGraph k (variableBound f) j c)).flatten).length ≤
      f.length * (10*k) := by
    rw [mapIdx_eq_range _ [],List.length_flatten,List.map_map]
    have hle := sum_map_le (List.range (placeFormula [] f).length)
      (fun j => (placedClauseGraph k (variableBound f) j ((placeFormula [] f)[j]?.getD [])).length)
      (fun _ => 10*k) (by
        intro j _
        simpa only [placedClauseGraph,mapGraph,List.length_map] using clauseGraph_edge_bound hk ((placeFormula [] f)[j]?.getD []))
    simpa only [sum_map_const,List.length_range,placeFormula_length,Function.comp_def] using hle
  have hvle : variableBound f * (2*k-1) ≤ variableBound f * (2*k) := Nat.mul_le_mul_left _ (by omega)
  unfold formulaGraph
  rw [List.length_append,hvar]
  omega

theorem clauseBound_le_of_literals {c : Clause} {n : Nat} (h : ∀ l ∈ c, l.var < n) : clauseBound c ≤ n := by
  induction c with
  | nil => simp [clauseBound]
  | cons l c ih =>
    have hl := h l (by simp)
    have ht := ih (fun r hr => h r (by simp [hr]))
    simp only [clauseBound]
    omega

theorem variableBound_le_of_literals {f : CNF} {n : Nat}
    (h : ∀ c ∈ f, ∀ l ∈ c, l.var < n) : variableBound f ≤ n := by
  induction f with
  | nil => simp [variableBound]
  | cons c f ih =>
    have hc := clauseBound_le_of_literals (h c (by simp))
    have ht := ih (fun d hd => h d (by simp [hd]))
    simp only [variableBound]
    omega

theorem FormulaDeletion.variableBound_le {g f : CNF} (h : FormulaDeletion g f) : variableBound g ≤ variableBound f := by
  apply variableBound_le_of_literals
  intro c hc l hl
  have hm := h.1.subset (List.mem_flatten.mpr ⟨c,hc,hl⟩)
  obtain ⟨d,hd,hld⟩ := List.mem_flatten.mp hm
  exact literal_lt_variableBound hd hld

theorem variableBound_append (f g : CNF) : variableBound (f ++ g) = max (variableBound f) (variableBound g) := by
  induction f with
  | nil => simp [variableBound]
  | cons c f ih => simp [variableBound,ih,Nat.max_assoc]

theorem addPaddingClause_variableBound (f : CNF) : variableBound (addPaddingClause f) = variableBound f + 2 := by
  rw [addPaddingClause,variableBound_append]
  simp only [variableBound,clauseBound,paddingClause]
  omega

theorem padFormula_variableBound (r : Nat) (f : CNF) :
    variableBound (padFormula r f) = variableBound f + 2*r := by
  induction r with
  | zero => simp [padFormula]
  | succ r ih => rw [padFormula,addPaddingClause_variableBound,ih]; omega

/-- A uniform explicit output-size bound for the complete preprocessed graph
map, including contradiction outputs and padding for removed clauses. -/
theorem globalReductionGraph_edge_bound {k : Nat} (hk : 5 ≤ k) (f : CNF) :
    (globalReductionGraph k f).length ≤
      (variableBound f + 2*(f.length+1)) * (2*k) + (f.length+1) * (10*k) := by
  have hbound : ∀ g : CNF, variableBound g ≤ variableBound f + 2*(f.length+1) →
      g.length ≤ f.length+1 → (formulaGraph k g).length ≤
        (variableBound f + 2*(f.length+1)) * (2*k) + (f.length+1) * (10*k) := by
    intro g hn hm
    have h := formulaGraph_edge_bound hk g
    have hn' := Nat.mul_le_mul_right (2*k) hn
    have hm' := Nat.mul_le_mul_right (10*k) hm
    omega
  unfold globalReductionGraph
  cases hg : cleanFormula f with
  | none =>
    apply hbound
    · rw [padFormula_variableBound]
      simp only [variableBound]
      omega
    · rw [padFormula_length]
      simp
  | some g =>
    have hdel := (unitReduce_deletion hg).trans (normalizeClauses_deletion f)
    apply hbound
    · rw [padFormula_variableBound]
      have hn := hdel.variableBound_le
      omega
    · rw [padFormula_length]
      have hm := hdel.2.1
      omega

end STACS2027
