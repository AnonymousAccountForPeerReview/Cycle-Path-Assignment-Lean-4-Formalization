module

public import NPHardness.PlanarSourceRingClauseAddresses
public import NPHardness.PlanarAssemblyOccurrenceAddress

/-! Actual odd source darts follow the inverse literal-slot cycle, including
both original copied clauses and the new two-literal implication clauses. -/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT Complexity.Planar Comb PlanarGluing PlanarAssembly
open Embedding Embedding.BipartiteRotation

def CanonicalClauseRotation (f : CNF) (B : BipartiteRotation f.flatten.length) : Prop :=
  ∀i,(B.clause.invFun i).val=off f (oj f i.val)+
    (ot f i.val+kl f (oj f i.val)-1)%kl f (oj f i.val)

theorem copiedClause_port_data (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat→Bool) (i : Fin f.flatten.length) :
    let F:=ringFormula f (nextIndex B) signs
    let d:=(placedRingDarts f (nextIndex B) signs).toFun (d6 i 1)
    sourcePortNumber F d=ot f i.val ∧ sourcePortCount F d=kl f (oj f i.val) ∧
      sourceForward signs F d=false := by
  have hi : i.val<nM f := by
    have he := (ComputableComb.incidence_length_nM f).symm.trans (incidenceGraph_length_flatten f)
    omega
  obtain ⟨hj,ht,hoff⟩ := occ_spec f i.val hi
  have hh := odd_offset_port_data signs (ringFormula f (nextIndex B) signs)
    ((placedRingDarts f (nextIndex B) signs).toFun (d6 i 1)) (oj f i.val) (ot f i.val)
    (by rw [ringFormula_length]; omega)
    (by rw [ringFormula_kl_copy f _ _ _ hj]; exact ht)
    (by rw [placedRingDarts_val,ringDarts_one,ringFormula_off_copy f _ _ _ (by omega),hoff])
  rw [ringFormula_kl_copy f _ _ _ hj] at hh
  exact hh

theorem copiedClause_port_predecessor (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat→Bool) (hc : CanonicalClauseRotation f B) (i : Fin f.flatten.length) :
    let F:=ringFormula f (nextIndex B) signs
    let I:=placedRingMap f B signs
    let d:=(placedRingDarts f (nextIndex B) signs).toFun (d6 i 1)
    sourcePortNumber F (I.face (I.edge d))=
      if sourceForward signs F d then (sourcePortNumber F d+1)%sourcePortCount F d
      else (sourcePortNumber F d+sourcePortCount F d-1)%sourcePortCount F d := by
  dsimp only
  have hi : i.val<nM f := by
    have he := (ComputableComb.incidence_length_nM f).symm.trans (incidenceGraph_length_flatten f)
    omega
  obtain ⟨hj,ht,_⟩ := occ_spec f i.val hi
  have hh := odd_offset_port_data signs (ringFormula f (nextIndex B) signs)
    ((placedRingDarts f (nextIndex B) signs).toFun (d6 (B.clause.invFun i) 1)) (oj f i.val)
    ((ot f i.val+kl f (oj f i.val)-1)%kl f (oj f i.val))
    (by rw [ringFormula_length]; omega)
    (by rw [ringFormula_kl_copy f _ _ _ hj]; exact Nat.mod_lt _ (by omega))
    (by rw [placedRingDarts_val,ringDarts_one,ringFormula_off_copy f _ _ _ (by omega),hc i])
  rw [placedRingMap_predecessor,copiedClause_predecessor,hh.1]
  have hd := copiedClause_port_data f B signs i
  rw [hd.1,hd.2.1,hd.2.2]
  rfl

theorem clauseRole_port_data (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat→Bool) (i : Fin f.flatten.length) (role : Fin 2) :
    let F:=ringFormula f (nextIndex B) signs
    let d:=(placedRingDarts f (nextIndex B) signs).toFun (clauseRoleDart i role)
    sourcePortNumber F d=role.val ∧ sourcePortCount F d=2 ∧ sourceForward signs F d=false := by
  have hh := odd_offset_port_data signs (ringFormula f (nextIndex B) signs)
    ((placedRingDarts f (nextIndex B) signs).toFun (clauseRoleDart i role)) (f.length+i.val) role.val
    (by rw [ringFormula_length]; have := i.isLt; omega)
    (by rw [ringFormula_kl_ring f _ _ _ i.isLt]; exact role.isLt)
    (by
      rw [ringFormula_off_ring f _ _ _ (Nat.le_of_lt i.isLt)]
      rcases (by decide : ∀r:Fin 2,r=0 ∨ r=1) role with rfl | rfl
      · rw [show clauseRoleDart i 0=d6 i 3 from rfl,placedRingDarts_val,ringDarts_three]; simp; omega
      · rw [show clauseRoleDart i 1=d6 i 4 from rfl,placedRingDarts_val,ringDarts_four]; simp; omega)
  rw [ringFormula_kl_ring f _ _ _ i.isLt] at hh
  exact hh

theorem clauseRole_port_predecessor (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat→Bool) (i : Fin f.flatten.length) (role : Fin 2) :
    let F:=ringFormula f (nextIndex B) signs
    let I:=placedRingMap f B signs
    let d:=(placedRingDarts f (nextIndex B) signs).toFun (clauseRoleDart i role)
    sourcePortNumber F (I.face (I.edge d))=
      if sourceForward signs F d then (sourcePortNumber F d+1)%sourcePortCount F d
      else (sourcePortNumber F d+sourcePortCount F d-1)%sourcePortCount F d := by
  dsimp only
  rw [placedRingMap_predecessor,clauseRoleDart_predecessor,(clauseRole_port_data f B signs i _).1]
  have hd := clauseRole_port_data f B signs i role
  rw [hd.1,hd.2.1,hd.2.2]
  rcases (by decide : ∀r:Fin 2,r=0 ∨ r=1) role with rfl | rfl <;> decide

theorem odd_expanded_role (f : CNF) (B : BipartiteRotation f.flatten.length) (signs : Nat→Bool)
    (d : Fin (6*f.flatten.length))
    (hd : ((placedRingDarts f (nextIndex B) signs).toFun d).val%2≠0) :
    (∃i:Fin f.flatten.length,d=d6 i 1) ∨
    (∃i:Fin f.flatten.length,∃r:Fin 2,d=clauseRoleDart i r) := by
  apply six_cases (fun d=>((placedRingDarts f (nextIndex B) signs).toFun d).val%2≠0 →
    (∃i:Fin f.flatten.length,d=d6 i 1) ∨
    (∃i:Fin f.flatten.length,∃r:Fin 2,d=clauseRoleDart i r)) ?_ d hd
  intro i
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro h; rw [placedRingDarts_val,ringDarts_zero] at h; omega
  · intro _; exact Or.inl ⟨i,rfl⟩
  · intro h; rw [placedRingDarts_val,ringDarts_two] at h; omega
  · intro _; exact Or.inr ⟨i,0,rfl⟩
  · intro _; exact Or.inr ⟨i,1,rfl⟩
  · intro h; rw [placedRingDarts_val,ringDarts_five] at h; omega

theorem placedRingMap_odd_predecessor (f : CNF) (B : BipartiteRotation f.flatten.length)
    (signs : Nat→Bool) (hc : CanonicalClauseRotation f B)
    (d : Fin (2*(placeFormula [] (ringFormula f (nextIndex B) signs)).flatten.length))
    (hd : d.val%2≠0) :
    let F:=ringFormula f (nextIndex B) signs
    let I:=placedRingMap f B signs
    sourcePortNumber F (I.face (I.edge d))=
      if sourceForward signs F d then (sourcePortNumber F d+1)%sourcePortCount F d
      else (sourcePortNumber F d+sourcePortCount F d-1)%sourcePortCount F d := by
  let e:=placedRingDarts f (nextIndex B) signs
  have h:(e.toFun (e.invFun d)).val%2≠0:=by rw [e.right_inv]; exact hd
  rcases odd_expanded_role f B signs (e.invFun d) h with ⟨i,he⟩ | ⟨i,r,he⟩
  · have hde:d=e.toFun (d6 i 1):=by rw [←he,e.right_inv]
    rw [hde]
    exact copiedClause_port_predecessor f B signs hc i
  · have hde:d=e.toFun (clauseRoleDart i r):=by rw [←he,e.right_inv]
    rw [hde]
    exact clauseRole_port_predecessor f B signs i r

end STACS2027.PlanarSource.Formula
