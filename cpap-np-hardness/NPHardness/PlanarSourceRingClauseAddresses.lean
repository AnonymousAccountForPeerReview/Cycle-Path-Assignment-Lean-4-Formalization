module

public import NPHardness.PlanarSourcePlacedDarts
public import NPHardness.PlanarSourceClauseRotation

/-! Exact clause lengths and flattened addresses in the concrete ring source. -/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar Comb PlanarGluing PlanarAssembly
open Embedding Embedding.BipartiteRotation

theorem copyFormula_clause_lengths (f : CNF) : (copyFormula f).map List.length=f.map List.length := by
  have h (n : Nat) : ((tagSource n f).map sourceCopies).map List.length=f.map List.length := by
    induction f generalizing n with
    | nil => rfl
    | cons c f ih => simp [tagSource,sourceCopies,ih]
  exact h 0

theorem ringFormula_clause_lengths (f : CNF) (next : Nat→Nat) (signs : Nat→Bool) :
    (ringFormula f next signs).map List.length=f.map List.length++List.replicate f.flatten.length 2 := by
  simp only [ringFormula,List.map_append,copyFormula_clause_lengths,ringClauses,List.map_map]
  simp only [Function.comp_def,List.length_cons,List.length_nil]
  change _ ++ (List.range f.flatten.length).map (Function.const Nat 2)=_
  rw [List.map_const,List.length_range]

theorem ringFormula_off_copy (f : CNF) (next : Nat→Nat) (signs : Nat→Bool)
    (j : Nat) (hj : j≤f.length) : off (ringFormula f next signs) j=off f j := by
  unfold off Comb.lens
  rw [ringFormula_clause_lengths,List.take_append_of_le_length (by simpa using hj)]

theorem ringFormula_kl_copy (f : CNF) (next : Nat→Nat) (signs : Nat→Bool)
    (j : Nat) (hj : j<f.length) : kl (ringFormula f next signs) j=kl f j := by
  have hr : j<(ringFormula f next signs).length := by rw [ringFormula_length]; omega
  rw [kl_of_lt _ _ hr,kl_of_lt _ _ hj]
  have hl := congrArg (fun ls : List Nat=>ls[j]?) (ringFormula_clause_lengths f next signs)
  rw [List.getElem?_append_left (by simpa only [List.length_map] using hj)] at hl
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hr,List.getElem?_eq_getElem hj,Option.map_some,Option.some.injEq] using hl

theorem ringFormula_off_ring (f : CNF) (next : Nat→Nat) (signs : Nat→Bool)
    (i : Nat) (hi : i≤f.flatten.length) :
    off (ringFormula f next signs) (f.length+i)=f.flatten.length+2*i := by
  unfold off Comb.lens
  rw [ringFormula_clause_lengths,List.take_append]
  simp only [List.length_map,Nat.add_sub_cancel_left,List.take_replicate,List.sum_append,
    Nat.min_eq_left hi,List.sum_replicate_nat]
  rw [List.take_of_length_le (by simp),←List.length_flatten]
  omega

theorem ringFormula_kl_ring (f : CNF) (next : Nat→Nat) (signs : Nat→Bool)
    (i : Nat) (hi : i<f.flatten.length) :
    kl (ringFormula f next signs) (f.length+i)=2 := by
  have hr : f.length+i<(ringFormula f next signs).length := by rw [ringFormula_length]; omega
  rw [kl_of_lt _ _ hr]
  have hl := congrArg (fun ls : List Nat=>ls[f.length+i]?) (ringFormula_clause_lengths f next signs)
  rw [List.getElem?_append_right (show (f.map List.length).length≤f.length+i by simp)] at hl
  simp only [List.getElem?_map,List.getElem?_eq_getElem hr,Option.map_some,List.length_map,Nat.add_sub_cancel_left] at hl
  simpa only [List.getElem?_replicate,hi,↓reduceIte,Option.some.injEq] using hl

end STACS2027.PlanarSource.Formula
