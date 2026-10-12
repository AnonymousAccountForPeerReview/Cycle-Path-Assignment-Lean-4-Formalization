module

public import NPHardness.PlanarAssemblySourcePieces
public import NPHardness.PlanarAssemblyChosenMaps

/-! Exact match between uniform source-node enumerations and the selected
ports of the corresponding concrete gadget block. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

theorem piecePorts_length {k : Nat} {f : CNF} (hf : BoundedOccurrence f) (j : PieceIndex k f) :
    (piecePorts k f j).length=pieceFullCount k f j := by
  by_cases hj:j.val<variableBound f
  · simp only [piecePorts,pieceFullCount,hj,↓reduceDIte,placedVariablePorts_length]
  · simp only [piecePorts,pieceFullCount,hj,↓reduceDIte]
    exact ungluedClausePorts_length _ _ _ _ (by
      have := hf.placed_clause_size (List.getElem_mem (clauseIndexOfPiece j hj).isLt)
      omega)

/-- The used source slot interpreted in the complete local port list. -/
noncomputable def piecePortIndex {k : Nat} {f : CNF} (hf : BoundedOccurrence f) (j : PieceIndex k f)
    (i : Fin (pieceUsedCount k f j)) : Fin (piecePorts k f j).length :=
  Fin.cast (piecePorts_length hf j).symm (pieceUsedPort hf j i)

theorem pieceNodeIndex_variable {k : Nat} {f : CNF} (j : PieceIndex k f)
    (hj:j.val<variableBound f) (i : Fin (pieceUsedCount k f j)) :
    (pieceNodeIndex k f j).dart i=
      occurrenceDart (variableOccurrenceIndex f j.val
        ⟨i.val,by simpa only [pieceUsedCount,hj,↓reduceIte] using i.isLt⟩) false := by
  simp only [pieceNodeIndex,hj,↓reduceDIte,NodeDartIndex.transport,variableNodeIndex]

 theorem pieceNodeIndex_clause {k : Nat} {f : CNF} (j : PieceIndex k f)
    (hj:¬j.val<variableBound f) (i : Fin (pieceUsedCount k f j)) :
    (pieceNodeIndex k f j).dart i=
      occurrenceDart (clauseOccurrenceIndex f (j.val-variableBound f)
        ⟨i.val,by simpa only [pieceUsedCount,hj,↓reduceIte] using i.isLt⟩) true := by
  simp only [pieceNodeIndex,hj,↓reduceDIte,NodeDartIndex.transport,clauseNodeIndex]

theorem ChosenPieces.block_port_congr {k : Nat} {f : CNF} (L : ChosenPieces k f)
    {a b : PieceIndex k f} (hab : a=b)
    (i : Fin (piecePorts k f a).length) (j : Fin (piecePorts k f b).length)
    (hij : i.val=j.val) :
    blockDart (ungluedFormulaPieces k f) a ((L a).port i)=
      blockDart (ungluedFormulaPieces k f) b ((L b).port j) := by
  subst b
  have he : i=j := Fin.ext hij
  rw [he]

theorem ChosenPieces.sourcePort_piece_match {k : Nat} {f : CNF}
    (L : ChosenPieces k f) (hf : BoundedOccurrence f) (j : PieceIndex k f)
    (i : Fin (pieceUsedCount k f j)) :
    (L.choices hf).sourcePort hf ((pieceNodeIndex k f j).dart i)=
      blockDart (ungluedFormulaPieces k f) j ((L j).port (piecePortIndex hf j i)) := by
  by_cases hj:j.val<variableBound f
  · rw [pieceNodeIndex_variable j hj,LocalPortChoices.sourcePort_even]
    unfold LocalPortChoices.variableOccurrencePort
    rw [L.variable_global_port]
    have hvar : occurrenceVariable hf (variableOccurrenceIndex f j.val
        ⟨i.val,by simpa only [pieceUsedCount,hj,↓reduceIte] using i.isLt⟩)=⟨j.val,hj⟩ := by
      apply Fin.ext
      exact variableOccurrenceIndex_vertex f j.val _
    rw [hvar]
    have hpiece : variablePieceIndex k f ⟨j.val,hj⟩=j := Fin.ext rfl
    apply L.block_port_congr hpiece
    simp only [piecePortIndex,Fin.val_cast,variablePortIndex,pieceUsedPort,hj,↓reduceDIte,variableUsedPort]
  · rw [pieceNodeIndex_clause j hj,LocalPortChoices.sourcePort_odd]
    unfold LocalPortChoices.clauseOccurrencePort
    rw [L.clause_global_port]
    let a : Fin (clauseOccurrences f (j.val-variableBound f)).length :=
      ⟨i.val,by simpa only [pieceUsedCount,hj,↓reduceIte] using i.isLt⟩
    have hclause : (occurrencePosition f (clauseOccurrenceIndex f (j.val-variableBound f) a)).clause=
        pieceClauseIndex k f j hj := by
      apply Fin.ext
      exact clauseOccurrenceIndex_vertex f (j.val-variableBound f) a
    have hpiece : clausePieceIndex k f (pieceClauseIndex k f j hj)=j := by
      apply Fin.ext
      change variableBound f+(j.val-variableBound f)=j.val
      omega
    have hblock := (congrArg (clausePieceIndex k f) hclause).trans hpiece
    apply L.block_port_congr hblock
    simp only [piecePortIndex,Fin.val_cast,clausePortIndex,pieceUsedPort,hj,↓reduceDIte,clauseUsedPort,pieceClauseIndex]

end STACS2027.PlanarAssembly
