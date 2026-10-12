module

public import NPHardness.PlanarAssemblyProfilePieces

/-! Concrete allocated port numbers for source incidence darts, and the
bridge from an explicit predecessor-number equation to uniform local order. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

noncomputable def sourcePortNumber (f:CNF) (d:Fin (2*(placeFormula [] f).flatten.length)) : Nat :=
  let i:OccurrenceIndex f:=⟨d.val/2,by have:=d.isLt;omega⟩
  if d.val%2=0 then (occurrence f i).port else (occurrencePosition f i).slot.val

@[simp] theorem sourcePortNumber_even (f:CNF) (i:OccurrenceIndex f) :
    sourcePortNumber f (occurrenceDart i false)=(occurrence f i).port := by
  simp only [sourcePortNumber,occurrenceDart,Bool.false_eq_true,↓reduceIte,Nat.add_zero,
    Nat.mul_mod_right,Nat.mul_div_right,show 0<2 by decide]

@[simp] theorem sourcePortNumber_odd (f:CNF) (i:OccurrenceIndex f) :
    sourcePortNumber f (occurrenceDart i true)=(occurrencePosition f i).slot.val := by
  have hd:(2*i.val+1)/2=i.val:=by omega
  have hm:(2*i.val+1)%2=1:=by omega
  simp only [sourcePortNumber,occurrenceDart,↓reduceIte,hm,show ¬1=0 by decide,↓reduceIte]
  exact congrArg (fun j:OccurrenceIndex f=>(occurrencePosition f j).slot.val) (Fin.ext hd)

theorem piecePortIndex_number {k:Nat} {f:CNF} (hf:BoundedOccurrence f)
    (j:PieceIndex k f) (i:Fin (pieceUsedCount k f j)) :
    (piecePortIndex hf j i).val=sourcePortNumber f ((pieceNodeIndex k f j).dart i) := by
  by_cases hj:j.val<variableBound f
  · rw [pieceNodeIndex_variable j hj,sourcePortNumber_even]
    simp only [piecePortIndex,Fin.val_cast,pieceUsedPort,hj,↓reduceDIte,variableUsedPort,occurrenceLocalPort]
  · rw [pieceNodeIndex_clause j hj,sourcePortNumber_odd]
    simp only [piecePortIndex,Fin.val_cast,pieceUsedPort,hj,↓reduceDIte,clauseUsedPort,pieceClauseIndex]

noncomputable def sourcePortCount (f:CNF) (d:Fin (2*(placeFormula [] f).flatten.length)) : Nat :=
  match occurrenceVertex f d with
  | .inl _=>3
  | .inr j=>((placeFormula [] f)[j]?.getD []).length

noncomputable def sourceForward (signs:Nat→Bool) (f:CNF)
    (d:Fin (2*(placeFormula [] f).flatten.length)) : Bool :=
  match occurrenceVertex f d with
  | .inl v=>signs v
  | .inr _=>false

theorem sourcePortCount_piece {k:Nat} {f:CNF} (hf:BoundedOccurrence f)
    (j:PieceIndex k f) (i:Fin (pieceUsedCount k f j)) :
    sourcePortCount f ((pieceNodeIndex k f j).dart i)=(piecePorts k f j).length := by
  unfold sourcePortCount
  rw [(pieceNodeIndex k f j).vertex,piecePorts_length hf]
  by_cases hj:j.val<variableBound f
  · simp only [pieceVertex,pieceFullCount,hj,↓reduceIte,↓reduceDIte]
  · have hc: j.val-variableBound f<(placeFormula [] f).length:=(pieceClauseIndex k f j hj).isLt
    simp only [pieceVertex,pieceFullCount,hj,↓reduceIte,↓reduceDIte,pieceClauseIndex,
      List.getElem?_eq_getElem hc,Option.getD_some]

theorem sourceForward_piece {k:Nat} {f:CNF} (signs:Nat→Bool)
    (j:PieceIndex k f) (i:Fin (pieceUsedCount k f j)) :
    sourceForward signs f ((pieceNodeIndex k f j).dart i)=
      (decide (j.val<variableBound f) && signs j.val) := by
  unfold sourceForward
  rw [(pieceNodeIndex k f j).vertex]
  by_cases hj:j.val<variableBound f <;> simp [pieceVertex,hj]

/-- An explicit arithmetic rule on actual source dart numbers is sufficient
to prove every desired local port order. No geometric choice is computed here. -/
theorem piece_profile_source_order {k:Nat} {f:CNF} (hf:BoundedOccurrence f) (signs:Nat→Bool)
    (I:Hypermap (2*(placeFormula [] f).flatten.length))
    (hnode:∀a b,Reaches I.node a b ↔ occurrenceVertex f a=occurrenceVertex f b)
    (hpred:∀d,sourcePortNumber f (I.face (I.edge d))=
      if sourceForward signs f d then (sourcePortNumber f d+1)%sourcePortCount f d
      else (sourcePortNumber f d+sourcePortCount f d-1)%sourcePortCount f d)
    (j:PieceIndex k f) (i:Fin (pieceUsedCount k f j)) :
    pieceProfileNext signs j (piecePortIndex hf j i)=
      piecePortIndex hf j ((pieceNodeIndex k f j).order I hnode i) := by
  apply Fin.ext
  rw [piecePortIndex_number,(pieceNodeIndex k f j).order_spec,hpred,
    sourcePortCount_piece hf,sourceForward_piece,←piecePortIndex_number hf]
  unfold pieceProfileNext
  dsimp only
  by_cases hj:j.val<variableBound f <;> cases signs j.val <;> simp [hj]

end STACS2027.PlanarAssembly
