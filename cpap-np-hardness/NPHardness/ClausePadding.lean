module

public import NPHardness.UnitPreprocess

/-! Fresh, independently satisfiable clauses restore the original budget. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def paddingClause (n : Nat) : Clause := [⟨n,true⟩,⟨n+1,true⟩]
def addPaddingClause (f : CNF) : CNF := f ++ [paddingClause (variableBound f)]

theorem occurrences_append (f g : CNF) (v : Nat) (p : Bool) :
    occurrences (f ++ g) v p = occurrences f v p + occurrences g v p := by
  simp [occurrences,List.flatten_append,List.filter_append]

theorem occurrences_ge_bound {f : CNF} {v : Nat} (hv : variableBound f ≤ v) (p : Bool) :
    occurrences f v p = 0 := by
  rw [occurrences_eq_count]
  apply List.count_eq_zero_of_not_mem
  intro hm
  obtain ⟨c,hc,hl⟩ := List.mem_flatten.mp hm
  have h := literal_lt_variableBound hc hl
  change v < variableBound f at h
  omega

theorem paddingClause_positive_bound (n v : Nat) : occurrences [paddingClause n] v true ≤ 1 := by
  by_cases hn : v = n
  · subst v; simp [occurrences,paddingClause]
  · by_cases hn1 : v = n+1
    · subst v; simp [occurrences,paddingClause]
    · simp [occurrences,paddingClause,Ne.symm hn,Ne.symm hn1]

theorem paddingClause_negative_zero (n v : Nat) : occurrences [paddingClause n] v false = 0 := by
  simp [occurrences,paddingClause]

theorem paddingClause_below_zero {n v : Nat} (hv : v < n) (p : Bool) :
    occurrences [paddingClause n] v p = 0 := by
  have hn : n ≠ v := by omega
  have hn1 : n+1 ≠ v := by omega
  simp [occurrences,paddingClause,hn,hn1]

theorem addPaddingClause_bounded {f : CNF} (hf : BoundedOccurrence f) : BoundedOccurrence (addPaddingClause f) := by
  refine ⟨?_,?_,?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hf.1 c hc
    · have he : c = paddingClause (variableBound f) := by simpa using hc
      exact Or.inl (he ▸ rfl)
  · intro v
    rw [addPaddingClause,occurrences_append]
    by_cases hv : v < variableBound f
    · rw [paddingClause_below_zero hv true,Nat.add_zero]
      exact hf.2.1 v
    · rw [occurrences_ge_bound (by omega) true,Nat.zero_add]
      exact paddingClause_positive_bound _ _
  · intro v
    rw [addPaddingClause,occurrences_append,paddingClause_negative_zero,Nat.add_zero]
    exact hf.2.2 v

theorem addPaddingClause_distinct {f : CNF} (hf : ClauseVariablesDistinct f) :
    ClauseVariablesDistinct (addPaddingClause f) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hf c hc
  · have he : c = paddingClause (variableBound f) := by simpa using hc
    rw [he]
    simp [paddingClause]

theorem addPaddingClause_sat (f : CNF) : Satisfiable (addPaddingClause f) ↔ Satisfiable f := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,List.all_eq_true.mpr ?_⟩
    intro c hc
    exact List.all_eq_true.mp ha c (List.mem_append_left _ hc)
  · rintro ⟨a,ha⟩
    let l : Literal := ⟨variableBound f,true⟩
    let b := assignLiteral l a
    refine ⟨b,List.all_eq_true.mpr ?_⟩
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · have he := evalClause_congr_literals b a c (fun r hr =>
        assignLiteral_away l r a (by have h := literal_lt_variableBound hc hr; change r.var ≠ variableBound f; omega))
      rw [he]
      exact List.all_eq_true.mp ha c hc
    · have he : c = paddingClause (variableBound f) := by simpa using hc
      rw [he]
      exact List.any_eq_true.mpr ⟨l,by simp [l,paddingClause],assignLiteral_self l a⟩

def padFormula : Nat → CNF → CNF
  | 0,f => f
  | r+1,f => addPaddingClause (padFormula r f)

theorem padFormula_length (r : Nat) (f : CNF) : (padFormula r f).length = f.length + r := by
  induction r with
  | zero => simp [padFormula]
  | succ r ih => simp [padFormula,addPaddingClause,ih,Nat.add_assoc]

theorem padFormula_sat (r : Nat) (f : CNF) : Satisfiable (padFormula r f) ↔ Satisfiable f := by
  induction r with
  | zero => exact Iff.rfl
  | succ r ih => exact (addPaddingClause_sat _).trans ih

theorem padFormula_bounded (r : Nat) {f : CNF} (hf : BoundedOccurrence f) : BoundedOccurrence (padFormula r f) := by
  induction r with
  | zero => exact hf
  | succ r ih => exact addPaddingClause_bounded ih

theorem padFormula_distinct (r : Nat) {f : CNF} (hf : ClauseVariablesDistinct f) :
    ClauseVariablesDistinct (padFormula r f) := by
  induction r with
  | zero => exact hf
  | succ r ih => exact addPaddingClause_distinct ih

theorem emptyFormula_bounded : BoundedOccurrence [] := by simp [BoundedOccurrence,occurrences]
theorem emptyFormula_distinct : ClauseVariablesDistinct [] := by simp [ClauseVariablesDistinct]

end STACS2027
