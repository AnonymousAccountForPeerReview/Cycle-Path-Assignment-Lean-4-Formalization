module

public import Hardness.DecodeList.EndpointsDef
public import Hardness.Decode.Endpoints

/-!
# List forms of the two endpoint decoders: correctness

`finalList_spec` and `initialList_spec` identify the list programs of
`Hardness/DecodeList/EndpointsDef.lean` with `Decode.finalDecode` and `Decode.initialDecode`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.DecodeList

open OAI.UniqueGamesTheorem.Foundations
open OAI.UniqueGamesTheorem.Foundations.PCP
open OAI.UniqueGamesTheorem.Foundations.PCP.Decode

theorem bitValue_eq_toNat (b : Bool) : AlphabetTable.Enumeration.bitValue b = b.toNat := by
  cases b <;> rfl

/-- The list program `finalList` computes `finalDecode`. -/
theorem finalList_spec (table : GraphTables.Table) (y : Word) :
    finalList table.vertices y =
      labelList (finalDecode table (fun i => SAT.assignmentOf y i.val)) := by
  apply List.ext_getElem
  · rw [finalList_length, labelList_length]
  · intro v h1 h2
    have hv : v < table.vertices := by
      rw [finalList_length] at h1
      exact h1
    simp only [finalList, labelList, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [finalDecode_val, Fin.sum_univ_six]
    simp only [bitValue_eq_toNat, finalLabel, Fin.val_zero, Fin.val_one, Fin.val_two,
      Nat.zero_add, Nat.pow_zero, Nat.mul_one]
    have e3 : ((3 : Fin 6) : Nat) = 3 := rfl
    have e4 : ((4 : Fin 6) : Nat) = 4 := rfl
    have e5 : ((5 : Fin 6) : Nat) = 5 := rfl
    rw [e3, e4, e5, Nat.add_comm 1 (6 * v), Nat.add_comm 2 (6 * v), Nat.add_comm 3 (6 * v),
      Nat.add_comm 4 (6 * v), Nat.add_comm 5 (6 * v)]
    omega

/-- The list program `initialList` computes `initialDecode`. -/
theorem initialList_spec (F : Target.Formula)
    (L : Fin (RawInitialTables.table F).vertices → GraphTables.Label) :
    initialList F.variables (labelList L) = List.ofFn (initialDecode F L) := by
  apply List.ext_getElem
  · rw [initialList_length, List.length_ofFn]
  · intro x h1 h2
    have hx : x < (RawInitialTables.table F).vertices := by
      rw [initialList_length] at h1
      rw [RawInitialTables.table_vertices]
      omega
    simp only [initialList, List.getElem_map, List.getElem_range, List.getElem_ofFn,
      initialDecode]
    rw [labelList_getD_of_lt L hx]

end Complexity.DecodeList
