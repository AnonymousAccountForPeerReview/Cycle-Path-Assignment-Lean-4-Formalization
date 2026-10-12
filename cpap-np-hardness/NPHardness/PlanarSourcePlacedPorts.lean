module

public import NPHardness.PlanarSourcePortOrder
public import NPHardness.PlanarSourceDimensions

/-! Exact allocated literal records at the copied and implication occurrence
positions. These connect arithmetic source darts to actual gadget ports. -/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar PlanarGluing PlanarAssembly

theorem ringFormula_placed_flatten (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat→Nat) (signs : Nat→Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val=(rot.toFun i).val) :
    (placeFormula [] (ringFormula f next signs)).flatten =
      (copyFormula f).flatten.map (fun l => PlacedLiteral.mk l 0) ++
      (ringClauses f.flatten.length next signs).flatten.map
        (fun l => PlacedLiteral.mk l (if l.positive then 0 else 1)) := by
  rw [ringFormula_placement f rot next signs hn,List.flatten_append,←List.map_flatten,←List.map_flatten]

theorem copyFormula_get (f : CNF) (i : Fin f.flatten.length) :
    (copyFormula f).flatten[i.val]?=some (⟨i.val,false⟩ : Literal) := by
  rw [copyFormula_flatten,List.getElem?_map,List.getElem?_zipIdx]
  simp [List.getElem?_eq_getElem i.isLt]

theorem ringClauses_get_first (E : Nat) (next : Nat→Nat) (signs : Nat→Bool) (i : Fin E) :
    (ringClauses E next signs).flatten[2*i.val]?=some (⟨i.val,signs i.val⟩ : Literal) := by
  change ((List.range E).flatMap (fun j => [(⟨j,signs j⟩ : Literal),⟨next j,!(signs (next j))⟩]))[2*i.val]? = _
  have h := STACS2027.PlanarOperations.Subdivision.getElem?_flatMap_two
    (List.range E) (fun j => [(⟨j,signs j⟩ : Literal),⟨next j,!(signs (next j))⟩])
    (fun _ => rfl) i.val 0 (by simp) (by decide)
  simpa using h

theorem ringClauses_get_second (E : Nat) (next : Nat→Nat) (signs : Nat→Bool) (i : Fin E) :
    (ringClauses E next signs).flatten[2*i.val+1]?=some (⟨next i.val,!(signs (next i.val))⟩ : Literal) := by
  change ((List.range E).flatMap (fun j => [(⟨j,signs j⟩ : Literal),⟨next j,!(signs (next j))⟩]))[2*i.val+1]? = _
  have h := STACS2027.PlanarOperations.Subdivision.getElem?_flatMap_two
    (List.range E) (fun j => [(⟨j,signs j⟩ : Literal),⟨next j,!(signs (next j))⟩])
    (fun _ => rfl) i.val 1 (by simp) (by decide)
  simpa using h

theorem ringFormula_placed_copy (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat→Nat) (signs : Nat→Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val=(rot.toFun i).val) (i : Fin f.flatten.length) :
    (placeFormula [] (ringFormula f next signs)).flatten[i.val]?=some ⟨⟨i.val,false⟩,0⟩ := by
  rw [ringFormula_placed_flatten f rot next signs hn,List.getElem?_append_left (by rw [List.length_map, copyFormula_flatten_length]; exact i.isLt),
    List.getElem?_map,copyFormula_get]
  rfl

theorem ringFormula_placed_first (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat→Nat) (signs : Nat→Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val=(rot.toFun i).val) (i : Fin f.flatten.length) :
    (placeFormula [] (ringFormula f next signs)).flatten[f.flatten.length+2*i.val]?=
      some ⟨⟨i.val,signs i.val⟩,if signs i.val then 0 else 1⟩ := by
  rw [ringFormula_placed_flatten f rot next signs hn,List.getElem?_append_right (by rw [List.length_map, copyFormula_flatten_length]; omega)]
  simp only [List.length_map,copyFormula_flatten_length,Nat.add_sub_cancel_left,List.getElem?_map]
  rw [ringClauses_get_first]
  rfl

theorem ringFormula_placed_second (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat→Nat) (signs : Nat→Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val=(rot.toFun i).val) (i : Fin f.flatten.length) :
    (placeFormula [] (ringFormula f next signs)).flatten[f.flatten.length+2*i.val+1]?=
      some ⟨⟨next i.val,!(signs (next i.val))⟩,if !(signs (next i.val)) then 0 else 1⟩ := by
  rw [ringFormula_placed_flatten f rot next signs hn,List.getElem?_append_right (by rw [List.length_map, copyFormula_flatten_length]; omega)]
  simp only [List.length_map,copyFormula_flatten_length,show f.flatten.length+2*i.val+1-f.flatten.length=2*i.val+1 by omega,
    List.getElem?_map]
  rw [ringClauses_get_second]
  rfl

end STACS2027.PlanarSource.Formula
