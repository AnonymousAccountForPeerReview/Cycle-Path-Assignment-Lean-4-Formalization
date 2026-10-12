module

public import NPHardness.PlanarSourcePlacement
public import NPHardness.PlanarSourceComputableFormula

/-!
Exact dimensions of the occurrence-ring source. These identities concern the
actual CNF lists, include the zero-occurrence case, and are independent of
sign choices. Only closure of the successor within the occurrence range is
needed for the variable bound; a permutation provides this automatically.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT STACS2027.PlanarGluing

@[simp] theorem copyFormula_length (f : CNF) : (copyFormula f).length=f.length :=
  tagCopies_length 0 f

theorem copyFormula_flatten (f : CNF) :
    (copyFormula f).flatten=f.flatten.zipIdx.map (fun p => (⟨p.2,false⟩ : Literal)) := by
  unfold copyFormula sourceCopies
  rw [←List.map_flatten,tagSource_flatten]

theorem copyFormula_variables (f : CNF) :
    (copyFormula f).flatten.map Literal.var=List.range f.flatten.length := by
  rw [copyFormula_flatten,List.map_map]
  change (f.flatten.zipIdx.map Prod.snd)=List.range f.flatten.length
  simp only [List.zipIdx_map_snd,List.range_eq_range']

@[simp] theorem copyFormula_flatten_length (f : CNF) :
    (copyFormula f).flatten.length=f.flatten.length := by
  rw [copyFormula_flatten,List.length_map,List.length_zipIdx]

@[simp] theorem ringClauses_length (E : Nat) (next : Nat → Nat) (signs : Nat → Bool) :
    (ringClauses E next signs).length=E := by simp [ringClauses]

@[simp] theorem ringFormula_length (f : CNF) (next : Nat → Nat) (signs : Nat → Bool) :
    (ringFormula f next signs).length=f.length+f.flatten.length := by
  simp [ringFormula]

@[simp] theorem ringClauses_flatten_length (E : Nat) (next : Nat → Nat) (signs : Nat → Bool) :
    (ringClauses E next signs).flatten.length=2*E := by
  unfold ringClauses
  induction E with
  | zero => rfl
  | succ E ih =>
    rw [List.range_succ,List.map_append,List.flatten_append,List.length_append,ih]
    simp
    omega

@[simp] theorem ringFormula_flatten_length (f : CNF) (next : Nat → Nat) (signs : Nat → Bool) :
    (ringFormula f next signs).flatten.length=3*f.flatten.length := by
  simp only [ringFormula,List.flatten_append,List.length_append,copyFormula_flatten_length,
    ringClauses_flatten_length]
  omega

theorem copyFormula_variableBound (f : CNF) : variableBound (copyFormula f)=f.flatten.length := by
  have hupper : variableBound (copyFormula f)≤f.flatten.length := by
    apply variableBound_le_of_literals
    intro c hc l hl
    have hm : l.var∈(copyFormula f).flatten.map Literal.var :=
      List.mem_map.mpr ⟨l,List.mem_flatten.mpr ⟨c,hc,hl⟩,rfl⟩
    rw [copyFormula_variables] at hm
    exact List.mem_range.mp hm
  have hlower : f.flatten.length≤variableBound (copyFormula f) := by
    by_cases hzero : f.flatten.length=0
    · omega
    · have hm : f.flatten.length-1∈(copyFormula f).flatten.map Literal.var := by
        rw [copyFormula_variables]
        apply List.mem_range.mpr
        omega
      obtain ⟨l,hl,he⟩ := List.mem_map.mp hm
      obtain ⟨c,hc,hlc⟩ := List.mem_flatten.mp hl
      have hb := literal_lt_variableBound hc hlc
      omega
  omega

/-- The copied clauses already use every label, while a range-preserving
successor introduces no labels outside that exact range. -/
theorem ringFormula_variableBound_of_bounded (f : CNF) (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i, i<f.flatten.length → next i<f.flatten.length) :
    variableBound (ringFormula f next signs)=f.flatten.length := by
  have hring : variableBound (ringClauses f.flatten.length next signs)≤f.flatten.length := by
    apply variableBound_le_of_literals
    intro c hc l hl
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    have hi' := List.mem_range.mp hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl | rfl
    · exact hi'
    · exact hn i hi'
  rw [ringFormula,variableBound_append,copyFormula_variableBound]
  exact Nat.max_eq_left hring

theorem ringFormula_variableBound (f : CNF)
    (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val=(rot.toFun i).val) :
    variableBound (ringFormula f next signs)=f.flatten.length := by
  apply ringFormula_variableBound_of_bounded
  intro i hi
  rw [hn ⟨i,hi⟩]
  exact (rot.toFun ⟨i,hi⟩).isLt

end STACS2027.PlanarSource.Formula

