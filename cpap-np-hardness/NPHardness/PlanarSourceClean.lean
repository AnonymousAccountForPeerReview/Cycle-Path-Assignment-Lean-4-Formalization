module

public import NPHardness.PlanarSourceRotationTablePartition
public import NPHardness.PlanarSourceFormulaSemantics
public import NPHardness.GridProperties

/-! The registered grid has no variable with a single occurrence. Consequently
its occurrence rings contain no tautological one-vertex rings. -/

@[expose] public section
namespace STACS2027.PlanarSource
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Grid
open STACS2027.PlanarGluing
open RotationTable

theorem cellPositions_count (odd : Bool) :
    ∀ p ∈ cellPositions odd, 2≤(cellPositions odd).count p := by
  cases odd <;> decide

theorem RotationTable.GridBlock.variable_twice (W : Nat) (bits : Nat → Nat → Bool×Bool) (B : GridBlock)
    (v : Nat) (hv : v∈(B.formula W bits).flatten.map Literal.var) :
    2≤((B.formula W bits).flatten.map Literal.var).count v := by
  cases B with
  | start k odd =>
    simp only [GridBlock.formula,startG,List.flatten_cons,List.flatten_nil,List.append_nil,
      List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hv ⊢
    rcases hv with rfl | rfl | rfl | rfl <;> (try simp) <;> omega
  | finish k odd =>
    simp only [GridBlock.formula,endG,List.flatten_cons,List.flatten_nil,List.append_nil,
      List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hv ⊢
    rcases hv with rfl | rfl | rfl | rfl <;> (try simp) <;> omega
  | cell k i odd =>
    have hvars := cell_variables W (columnIndex k odd) i odd
      (bits (columnIndex k odd) (row W odd i)).1 (bits (columnIndex k odd) (row W odd i)).2
    rw [GridBlock.formula,hvars] at hv ⊢
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
    exact Nat.le_trans (cellPositions_count odd p hp) List.count_le_count_map
  | rainbow k v' odd =>
    cases odd <;>
      simp only [GridBlock.formula,Bool.false_eq_true,↓reduceIte,rbOdd,rbEven,
        List.flatten_cons,List.flatten_nil,List.append_nil,List.cons_append,List.nil_append,
        List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hv ⊢ <;>
      (rcases hv with rfl | rfl | rfl | rfl <;> simp [List.count_cons] <;> omega)

theorem grid_variable_twice (W m : Nat) (bits : Nat → Nat → Bool×Bool)
    (v : Nat) (hv : v∈(gridCNF W m bits).flatten.map Literal.var) :
    2≤((gridCNF W m bits).flatten.map Literal.var).count v := by
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hv
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hl
  have hp : (l,i)∈(gridCNF W m bits).flatten.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by rw [List.getElem?_eq_getElem hi,he])
  obtain ⟨B,hB,hp⟩ := (globalBlocks_occurrence (q := (m+1)/2) bits (by omega) (l,i)).mp hp
  have hlow := B.variable_twice W bits l.var (List.mem_map.mpr ⟨l,List.fst_mem_of_mem_zipIdx hp,rfl⟩)
  obtain ⟨pre,post,hformula,_⟩ := B.blockAt (q := (m+1)/2) bits (by omega) hB
  rw [hformula,List.flatten_append,List.flatten_append,List.map_append,List.map_append,
    List.count_append,List.count_append]
  omega

theorem count_le_one_of_unique_index (xs : List Nat) (v : Nat)
    (h : ∀ i j (hi : i<xs.length) (hj : j<xs.length), xs[i]=v → xs[j]=v → i=j) :
    xs.count v≤1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    by_cases ha : a=v
    · subst a
      have hn : v∉xs := by
        intro hm
        obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
        have hh := h 0 (i+1) (by simp) (by simp; omega) rfl (by simpa using he)
        omega
      simp [List.count_eq_zero.mpr hn]
    · have hh : ∀ i j (hi : i<xs.length) (hj : j<xs.length), xs[i]=v → xs[j]=v → i=j := by
        intro i j hi hj hvi hvj
        have he := h (i+1) (j+1) (by simp; omega) (by simp; omega) (by simpa using hvi) (by simpa using hvj)
        omega
      simpa [ha] using ih hh

theorem rotation_no_fixed_of_twice (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (ho : ∀ i j : Fin f.flatten.length, Reaches rot.toFun i j ↔
      f.flatten[i.val].var=f.flatten[j.val].var)
    (ht : ∀ v∈f.flatten.map Literal.var, 2≤(f.flatten.map Literal.var).count v)
    (i : Fin f.flatten.length) : rot.toFun i≠i := by
  intro hfixed
  have hreach : ∀ j, f.flatten[i.val].var=f.flatten[j.val].var → i=j := by
    intro j he
    obtain ⟨k,hk⟩ := (ho i j).mpr he
    have hs : ∀ n, iterate rot.toFun n i=i := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [iterate,hfixed,ih]
    exact (hs k).symm.trans hk
  have hlo := ht f.flatten[i.val].var (List.mem_map.mpr ⟨f.flatten[i.val],List.getElem_mem i.isLt,rfl⟩)
  have hhi := count_le_one_of_unique_index (f.flatten.map Literal.var) f.flatten[i.val].var (by
    intro a b ha hb hva hvb
    have ha' : a<f.flatten.length := by simpa only [List.length_map] using ha
    have hb' : b<f.flatten.length := by simpa only [List.length_map] using hb
    have hea : i=⟨a,ha'⟩ := hreach ⟨a,ha'⟩ (by simpa only [List.getElem_map] using hva.symm)
    have heb : i=⟨b,hb'⟩ := hreach ⟨b,hb'⟩ (by simpa only [List.getElem_map] using hvb.symm)
    exact congrArg Fin.val (hea.symm.trans heb))
  omega

theorem Formula.copyFormula_distinct (f : CNF) : ClauseVariablesDistinct (Formula.copyFormula f) := by
  apply sourceCopies_distinct
  rw [tagSource_flatten]
  simpa using (List.nodup_range' (s := 0) (n := f.flatten.length))

theorem Formula.ringFormula_distinct (f : CNF)
    (rot : DartEquiv f.flatten.length f.flatten.length) (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val=(rot.toFun i).val)
    (hfixed : ∀ i, rot.toFun i≠i) : ClauseVariablesDistinct (Formula.ringFormula f next signs) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact Formula.copyFormula_distinct f c hc
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    have hi' : i<f.flatten.length := List.mem_range.mp hi
    have he : i≠next i := by
      intro heq
      apply hfixed ⟨i,hi'⟩
      apply Fin.ext
      exact (hn ⟨i,hi'⟩).symm.trans heq.symm
    simpa using he

theorem Formula.grid_ringFormula_distinct (W m : Nat) (bits : Nat → Nat → Bool×Bool)
    (rot : DartEquiv (gridCNF W m bits).flatten.length (gridCNF W m bits).flatten.length)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin (gridCNF W m bits).flatten.length, next i.val=(rot.toFun i).val)
    (ho : ∀ i j : Fin (gridCNF W m bits).flatten.length, Reaches rot.toFun i j ↔
      (gridCNF W m bits).flatten[i.val].var=(gridCNF W m bits).flatten[j.val].var) :
    ClauseVariablesDistinct (Formula.ringFormula (gridCNF W m bits) next signs) :=
  Formula.ringFormula_distinct _ rot next signs hn
    (rotation_no_fixed_of_twice _ rot ho (grid_variable_twice W m bits))

end STACS2027.PlanarSource
