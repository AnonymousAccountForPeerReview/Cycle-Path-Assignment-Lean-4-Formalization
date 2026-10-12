module

public import NPHardness.PlanarSourceClean

/-! Explicit port allocation for the compiled planar occurrence-ring source.
The copied clauses use the first negative port; each implication uses its
unique positive port or the second negative port. -/

@[expose] public section
namespace STACS2027.PlanarSource
open Complexity Complexity.SAT PlanarGluing

theorem placeLiterals_counts (past ls : List Literal) (r : Literal → Nat) (hn : ls.Nodup)
    (hc : ∀ l∈ls, past.count l=r l) :
    placeLiterals past ls=ls.map (fun l => PlacedLiteral.mk l (r l)) := by
  induction ls generalizing past with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨hl,ht⟩ := List.nodup_cons.mp hn
    rw [placeLiterals,hc l (by simp),ih (past++[l]) ht]
    · rfl
    · intro q hq
      have he : l≠q := fun he => hl (he ▸ hq)
      simp [List.count_append,hc q (by simp [hq]),he]

theorem placeFormula_counts (past : List Literal) (f : CNF) (r : Literal → Nat)
    (hn : f.flatten.Nodup) (hc : ∀ l∈f.flatten, past.count l=r l) :
    placeFormula past f=f.map (List.map (fun l => PlacedLiteral.mk l (r l))) := by
  induction f generalizing past with
  | nil => rfl
  | cons c f ih =>
    obtain ⟨hcn,hfn,hdis⟩ := List.nodup_append.mp hn
    rw [placeFormula,placeLiterals_counts past c r hcn
      (fun l hl => hc l (List.mem_append_left _ hl)),ih (past++c) hfn]
    · rfl
    · intro l hl
      have he : l∉c := fun hm => hdis l hm l hl rfl
      rw [List.count_append,List.count_eq_zero.mpr he,Nat.add_zero]
      exact hc l (List.mem_append_right _ hl)

namespace Formula

theorem copyFormula_count (f : CNF) (v : Nat) (b : Bool) :
    (copyFormula f).flatten.count ⟨v,b⟩=if b then 0 else (List.range f.flatten.length).count v := by
  rw [← occurrences_eq_count,copyFormula,sourceCopies_occurrences]
  simp [tagSource_flatten]

theorem copyFormula_nodup (f : CNF) : (copyFormula f).flatten.Nodup := by
  apply List.nodup_iff_count.mpr
  intro l
  cases l with
  | mk v b =>
    rw [copyFormula_count]
    cases b
    · exact List.nodup_iff_count.mp List.nodup_range v
    · change 0≤1; decide

theorem copyFormula_placement (f : CNF) :
    placeFormula [] (copyFormula f)=(copyFormula f).map (List.map (fun l => PlacedLiteral.mk l 0)) :=
  placeFormula_uniform [] _ 0 (copyFormula_nodup f) (by simp)

theorem ringClauses_nodup {E : Nat} (rot : DartEquiv E E) (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin E, next i.val=(rot.toFun i).val) :
    (ringClauses E next signs).flatten.Nodup := by
  apply List.nodup_iff_count.mpr
  intro l
  cases l with
  | mk v b =>
    rw [← occurrences_eq_count,ringClauses_occurrences rot next signs hn]
    exact List.nodup_iff_count.mp List.nodup_range v

theorem ringClauses_variable_lt {E : Nat} (rot : DartEquiv E E) (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin E, next i.val=(rot.toFun i).val)
    (l : Literal) (hl : l∈(ringClauses E next signs).flatten) : l.var<E := by
  have h := List.count_pos_iff.mpr hl
  have hc := ringClauses_occurrences rot next signs hn l.var l.positive
  rw [occurrences_eq_count] at hc
  have he : (⟨l.var,l.positive⟩ : Literal)=l := by cases l; rfl
  rw [he] at hc
  rw [hc] at h
  exact List.mem_range.mp (List.count_pos_iff.mp h)

theorem ringClauses_placement (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val=(rot.toFun i).val) :
    placeFormula (copyFormula f).flatten (ringClauses f.flatten.length next signs)=
      (ringClauses f.flatten.length next signs).map
        (List.map (fun l => PlacedLiteral.mk l (if l.positive then 0 else 1))) := by
  apply placeFormula_counts _ _ _ (ringClauses_nodup rot next signs hn)
  intro l hl
  have hv := ringClauses_variable_lt rot next signs hn l hl
  have hc := copyFormula_count f l.var l.positive
  have he : (⟨l.var,l.positive⟩ : Literal)=l := by cases l; rfl
  rw [he] at hc
  rw [hc]
  simp only [List.count_range,hv,ite_true]

theorem ringFormula_placement (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val=(rot.toFun i).val) :
    placeFormula [] (ringFormula f next signs)=
      (copyFormula f).map (List.map (fun l => PlacedLiteral.mk l 0)) ++
      (ringClauses f.flatten.length next signs).map
        (List.map (fun l => PlacedLiteral.mk l (if l.positive then 0 else 1))) := by
  rw [ringFormula,placeFormula_append,List.nil_append,copyFormula_placement,
    ringClauses_placement f rot next signs hn]

end Formula
end STACS2027.PlanarSource
