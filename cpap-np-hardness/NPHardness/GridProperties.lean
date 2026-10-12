module

public import NPHardness.GridPlacement
public import NPHardness.GlobalSize

/-! Dense variable support and non-repeated variables inside the compiled
source clauses. No preprocessing is required for these particular outputs. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT Complexity.ThreeSAT

theorem gridWheelFamily_literal_bound {V T : Nat} {l : Literal}
    (hl : l ∈ (gridWheelFamily V T).flatten) : l.var < V*(2*T) := by
  have hh := List.count_pos_iff.mpr hl
  rw [gridWheelFamily_count] at hh
  have hm := List.count_pos_iff.mp hh
  simpa using hm

theorem gridWheelFamily_contains {V T v : Nat} (hv : v < V*(2*T)) (b : Bool) :
    (⟨v,b⟩ : Literal) ∈ (gridWheelFamily V T).flatten := by
  apply List.count_pos_iff.mp
  rw [gridWheelFamily_count]
  apply List.count_pos_iff.mpr
  simpa using hv

theorem gridWheelFamily_variableBound (V T : Nat) :
    variableBound (gridWheelFamily V T) = V*(2*T) := by
  apply Nat.le_antisymm
  · apply variableBound_le_of_literals
    intro c hc l hl
    exact gridWheelFamily_literal_bound (List.mem_flatten.mpr ⟨c,hc,hl⟩)
  · by_cases hn : V*(2*T) = 0
    · omega
    have hm := gridWheelFamily_contains (V := V) (T := T) (v := V*(2*T)-1) (by omega) true
    obtain ⟨c,hc,hl⟩ := List.mem_flatten.mp hm
    have hb := literal_lt_variableBound hc hl
    dsimp only at hb
    omega

theorem gridBoundedFormula_variableBound {V S : Nat} {xs : List (Nat × Clause)}
    (hs : ∀ x ∈ xs, x.1 < S)
    (hc : ∀ x ∈ xs, x.2.length ≤ 3 ∧ ∀ l ∈ x.2, l.var < V) :
    variableBound (gridBoundedFormula V S xs) = V*(2*(3*S)) := by
  rw [gridBoundedFormula,variableBound_append,gridWheelFamily_variableBound]
  apply Nat.max_eq_left
  apply variableBound_le_of_literals
  intro c hm l hl
  obtain ⟨ps,hps,rfl⟩ := List.mem_map.mp hm
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hl
  exact gridCopyFormula_indices_below hs hc p (List.mem_flatten.mpr ⟨ps,hps,hp⟩)

theorem gridWheelFamily_distinct (V T : Nat) : ClauseVariablesDistinct (gridWheelFamily V T) := by
  intro c hc
  obtain ⟨v,_,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hc
  have hj' : j < T := by simpa using hj
  have hne : v*(2*T)+2*j+1 ≠ (if j+1 < T then v*(2*T)+2*j+2 else v*(2*T)) := by
    split <;> omega
  simp only [gridAt,gridPair,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl
  · simp [pos,List.nodup_cons]
  · simpa [neg,List.nodup_cons] using hne

theorem sourceCopies_distinct (cs : List (List SourceOccurrence))
    (hn : (cs.flatten.map Prod.snd).Nodup) : ClauseVariablesDistinct (cs.map sourceCopies) := by
  intro c hc
  obtain ⟨ps,hps,rfl⟩ := List.mem_map.mp hc
  have hh := ((List.sublist_flatten_of_mem hps).map Prod.snd).nodup hn
  simpa [sourceCopies,List.map_map,Function.comp_def] using hh

theorem gridBoundedFormula_distinct {V S : Nat} {xs : List (Nat × Clause)}
    (hs : ∀ x ∈ xs, x.1 < S) (hc : ∀ x ∈ xs, x.2.length ≤ 3)
    (hn : xs.Pairwise (fun x y => y.1 < x.1)) :
    ClauseVariablesDistinct (gridBoundedFormula V S xs) := by
  intro c hm
  rcases List.mem_append.mp hm with hm | hm
  · exact gridWheelFamily_distinct V (3*S) c hm
  · exact sourceCopies_distinct _ (gridCopyFormula_indices_nodup hs hc hn) c hm

theorem gridBoundedFormula_perm (V S : Nat) (xs : List (Nat × Clause)) :
    (gridBoundedFormula V S xs).Perm (taggedSplit V (sourceGrid (3*S)) (gridCopyFormula S xs)) :=
  (gridWheelFamily_perm V (3*S)).append (List.Perm.refl _)

theorem gridBoundedFormula_bounded {V S : Nat} {xs : List (Nat × Clause)}
    (hs : ∀ x ∈ xs, x.1 < S) (hc : ∀ x ∈ xs, x.2.length = 2 ∨ x.2.length = 3)
    (hn : xs.Pairwise (fun x y => y.1 < x.1)) : BoundedOccurrence (gridBoundedFormula V S xs) := by
  apply (boundedOccurrence_perm (gridBoundedFormula_perm V S xs)).mpr
  apply taggedSplit_bounded V (sourceGrid (3*S)) _ (sourceGrid_all_nodup _ _)
    (gridCopyFormula_indices_nodup hs (fun x hx => by have := hc x hx; omega) hn)
  intro c hm
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
  simpa only [gridCopyClause_length] using hc x hx

theorem gridBoundedFormula_satisfiable {V S : Nat} {xs : List (Nat × Clause)}
    (hs : ∀ x ∈ xs, x.1 < S)
    (hc : ∀ x ∈ xs, x.2.length ≤ 3 ∧ ∀ l ∈ x.2, l.var < V) :
    Satisfiable (gridBoundedFormula V S xs) ↔ Satisfiable (xs.map Prod.snd) := by
  apply (satisfiable_perm (gridBoundedFormula_perm V S xs)).trans
  have he := taggedSplit_satisfiable V (sourceGrid (3*S)) (gridCopyFormula S xs)
    (sourceGrid_all_nodup _ _) (fun v _ => sourceGrid_variable _ v) (gridCopyFormula_cover hs hc)
  simpa only [gridCopyFormula_forget] using he

end STACS2027
