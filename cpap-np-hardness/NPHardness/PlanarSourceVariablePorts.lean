module

public import NPHardness.PlanarSourcePlacedDarts
public import NPHardness.PlanarAssemblyProfilePieces

/-! Exact allocated ports of the three actual incidence darts at each
occurrence-copy variable, and their sign-controlled cyclic predecessor. -/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar PlanarGluing PlanarAssembly
open Embedding Embedding.BipartiteRotation

def ringOccurrence (f:CNF) (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (d:Fin (6*f.flatten.length)) : OccurrenceIndex (ringFormula f (nextIndex B) signs) :=
  ⟨((placedRingDarts f (nextIndex B) signs).toFun d).val/2,by
    have h:=((placedRingDarts f (nextIndex B) signs).toFun d).isLt
    omega⟩

theorem ringOccurrence_eq_of_get (f:CNF) (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (d:Fin (6*f.flatten.length)) (v:Nat) (p:PlacedLiteral)
    (hv:((ringDarts f.flatten.length).toFun d).val/2=v)
    (hget:(placeFormula [] (ringFormula f (nextIndex B) signs)).flatten[v]?=some p) :
    PlanarAssembly.occurrence (ringFormula f (nextIndex B) signs) (ringOccurrence f B signs d)=p := by
  have hi:(ringOccurrence f B signs d).val=v:=hv
  rw [←hi,List.getElem?_eq_getElem (ringOccurrence f B signs d).isLt] at hget
  exact Option.some.inj hget

theorem variableRole_occurrence (f:CNF) (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (i:Fin f.flatten.length) (role:Fin 3) :
    PlanarAssembly.occurrence (ringFormula f (nextIndex B) signs)
      (ringOccurrence f B signs (variableRoleDart B i role))=rolePlacedLiteral i.val (signs i.val) role := by
  rcases (by decide:∀r:Fin 3,r=0∨r=1∨r=2) role with rfl|rfl|rfl
  · apply ringOccurrence_eq_of_get f B signs _ i.val _
    · simp only [variableRoleDart,↓reduceIte,ringDarts_zero,Nat.mul_div_right,show 0<2 by decide]
    · exact ringFormula_placed_copy f B.varRot (nextIndex B) signs (nextIndex_at B) i
  · apply ringOccurrence_eq_of_get f B signs _ (f.flatten.length+2*i.val) _
    · simp only [variableRoleDart,show ¬(1:Fin 3)=0 by decide,↓reduceIte,ringDarts_two]
      omega
    · exact ringFormula_placed_first f B.varRot (nextIndex B) signs (nextIndex_at B) i
  · apply ringOccurrence_eq_of_get f B signs _ (f.flatten.length+2*(B.varRot.invFun i).val+1) _
    · simp only [variableRoleDart,show ¬(2:Fin 3)=0 by decide,show ¬(2:Fin 3)=1 by decide,↓reduceIte,ringDarts_five]
      omega
    · have h:=ringFormula_placed_second f B.varRot (nextIndex B) signs (nextIndex_at B) (B.varRot.invFun i)
      rw [nextIndex_at,B.varRot.right_inv] at h
      exact h

theorem variableRole_even (f:CNF) (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (i:Fin f.flatten.length) (role:Fin 3) :
    ((placedRingDarts f (nextIndex B) signs).toFun (variableRoleDart B i role)).val%2=0 := by
  rw [placedRingDarts_val]
  rcases (by decide:∀r:Fin 3,r=0∨r=1∨r=2) role with rfl|rfl|rfl
  · simp [variableRoleDart,ringDarts_zero]
  · simp [variableRoleDart,ringDarts_two]; omega
  · simp [variableRoleDart,ringDarts_five]; omega

theorem variableRole_vertex (f:CNF) (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (i:Fin f.flatten.length) (role:Fin 3) :
    occurrenceVertex (ringFormula f (nextIndex B) signs)
      ((placedRingDarts f (nextIndex B) signs).toFun (variableRoleDart B i role))=Sum.inl i.val := by
  unfold occurrenceVertex
  rw [variableRole_even]
  simp only [↓reduceIte]
  change Sum.inl (PlanarAssembly.occurrence (ringFormula f (nextIndex B) signs)
    (ringOccurrence f B signs (variableRoleDart B i role))).literal.var=Sum.inl i.val
  rw [variableRole_occurrence]
  unfold rolePlacedLiteral
  split <;> rfl

theorem reflectedVariableNext_eq_signed (sign:Bool) (p:Fin 3) :
    reflectedVariableNext sign p=variableSignedNext sign p :=
  (by decide:∀s:Bool,∀p:Fin 3,reflectedVariableNext s p=variableSignedNext s p) sign p

end STACS2027.PlanarSource.Formula
