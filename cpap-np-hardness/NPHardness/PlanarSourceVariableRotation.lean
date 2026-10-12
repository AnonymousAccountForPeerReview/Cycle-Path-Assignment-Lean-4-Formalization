module

public import NPHardness.PlanarSourceVariablePorts
public import NPHardness.PlanarAssemblySourcePortNumbers

/-! The executable sign rule realizes the predecessor of every actual
variable-node dart in the expanded source rotation. -/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar PlanarGluing PlanarAssembly
open Embedding Embedding.BipartiteRotation

theorem variableRole_portNumber (f:CNF) (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (i:Fin f.flatten.length) (role:Fin 3) :
    sourcePortNumber (ringFormula f (nextIndex B) signs)
      ((placedRingDarts f (nextIndex B) signs).toFun (variableRoleDart B i role))=
      (variableRolePort (signs i.val) role).val := by
  unfold sourcePortNumber
  rw [variableRole_even]
  simp only [↓reduceIte]
  change (PlanarAssembly.occurrence (ringFormula f (nextIndex B) signs)
    (ringOccurrence f B signs (variableRoleDart B i role))).port=_
  rw [variableRole_occurrence,rolePlacedLiteral_port]

theorem variableRole_port_predecessor (f:CNF) (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (i:Fin f.flatten.length) (role:Fin 3) :
    let F:=ringFormula f (nextIndex B) signs
    let I:=placedRingMap f B signs
    let d:=(placedRingDarts f (nextIndex B) signs).toFun (variableRoleDart B i role)
    sourcePortNumber F (I.face (I.edge d))=
      if sourceForward signs F d then (sourcePortNumber F d+1)%sourcePortCount F d
      else (sourcePortNumber F d+sourcePortCount F d-1)%sourcePortCount F d := by
  dsimp only
  rw [placedRingMap_predecessor,variableRoleDart_predecessor,variableRole_portNumber,
    variableRolePort_predecessor,reflectedVariableNext_eq_signed,variableSignedNext_val]
  unfold sourceForward sourcePortCount
  rw [variableRole_vertex,variableRole_portNumber]
  cases hs:signs i.val <;> simp [hs]

theorem even_expanded_role (f:CNF) (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (d:Fin (6*f.flatten.length))
    (hd:((placedRingDarts f (nextIndex B) signs).toFun d).val%2=0) :
    ∃i:Fin f.flatten.length,∃r:Fin 3,d=variableRoleDart B i r := by
  apply six_cases (fun d=>((placedRingDarts f (nextIndex B) signs).toFun d).val%2=0 →
    ∃i:Fin f.flatten.length,∃r:Fin 3,d=variableRoleDart B i r) ?_ d hd
  intro i
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro _; exact ⟨i,0,rfl⟩
  · intro h
    rw [placedRingDarts_val,ringDarts_one] at h
    omega
  · intro _; exact ⟨i,1,rfl⟩
  · intro h
    rw [placedRingDarts_val,ringDarts_three] at h
    omega
  · intro h
    rw [placedRingDarts_val,ringDarts_four] at h
    omega
  · intro _
    refine ⟨B.varRot.toFun i,2,?_⟩
    simp [variableRoleDart,B.varRot.left_inv]

theorem placedRingMap_even_predecessor (f:CNF) (B:BipartiteRotation f.flatten.length) (signs:Nat→Bool)
    (d:Fin (2*(placeFormula [] (ringFormula f (nextIndex B) signs)).flatten.length))
    (hd:d.val%2=0) :
    let F:=ringFormula f (nextIndex B) signs
    let I:=placedRingMap f B signs
    sourcePortNumber F (I.face (I.edge d))=
      if sourceForward signs F d then (sourcePortNumber F d+1)%sourcePortCount F d
      else (sourcePortNumber F d+sourcePortCount F d-1)%sourcePortCount F d := by
  let e:=placedRingDarts f (nextIndex B) signs
  have h:(e.toFun (e.invFun d)).val%2=0:=by rw [e.right_inv];exact hd
  obtain ⟨i,r,he⟩:=even_expanded_role f B signs (e.invFun d) h
  have hde:d=e.toFun (variableRoleDart B i r):=by rw [←he,e.right_inv]
  rw [hde]
  exact variableRole_port_predecessor f B signs i r

end STACS2027.PlanarSource.Formula
