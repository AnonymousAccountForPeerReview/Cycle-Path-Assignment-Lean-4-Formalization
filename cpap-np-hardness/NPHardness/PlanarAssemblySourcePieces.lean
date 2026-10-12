module

public import NPHardness.PlanarAssemblySourcePorts

/-! Uniform source-node indexing over the concatenated gadget blocks. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

abbrev PieceIndex (k : Nat) (f : CNF) := Fin (ungluedFormulaPieces k f).length

def pieceClauseIndex (k : Nat) (f : CNF) (j : PieceIndex k f) (h : ¬j.val<variableBound f) :
    Fin (placeFormula [] f).length := ⟨j.val-variableBound f,by
  have hj := j.isLt
  simp only [ungluedFormulaPieces,List.length_append,List.length_map,List.length_range,List.length_mapIdx] at hj
  omega⟩

def pieceVertex (k : Nat) (f : CNF) (j : PieceIndex k f) : Sum Nat Nat :=
  if j.val<variableBound f then Sum.inl j.val else Sum.inr (j.val-variableBound f)

noncomputable def pieceUsedCount (k : Nat) (f : CNF) (j : PieceIndex k f) : Nat :=
  if j.val<variableBound f then (variableOccurrences f j.val).length
  else (clauseOccurrences f (j.val-variableBound f)).length

def pieceFullCount (k : Nat) (f : CNF) (j : PieceIndex k f) : Nat :=
  if h:j.val<variableBound f then 3 else (placeFormula [] f)[(pieceClauseIndex k f j h).val].length

noncomputable def pieceNodeIndex (k : Nat) (f : CNF) (j : PieceIndex k f) :
    NodeDartIndex (occurrenceVertex f) (pieceVertex k f j) (pieceUsedCount k f j) :=
  if hj:j.val<variableBound f then
    (variableNodeIndex f j.val).transport
      (by simp only [pieceUsedCount,hj,↓reduceIte]) (by simp only [pieceVertex,hj,↓reduceIte])
  else (clauseNodeIndex f (j.val-variableBound f)).transport
      (by simp only [pieceUsedCount,hj,↓reduceIte]) (by simp only [pieceVertex,hj,↓reduceIte])

noncomputable def pieceUsedPort {k : Nat} {f : CNF} (hf : BoundedOccurrence f) (j : PieceIndex k f)
    (i : Fin (pieceUsedCount k f j)) : Fin (pieceFullCount k f j) :=
  if h:j.val<variableBound f then
    let a : Fin (variableOccurrences f j.val).length := ⟨i.val,by simpa only [pieceUsedCount,h,↓reduceIte] using i.isLt⟩
    ⟨(variableUsedPort hf j.val a).val,by simpa only [pieceFullCount,h,↓reduceDIte] using (variableUsedPort hf j.val a).isLt⟩
  else
    let a : Fin (clauseOccurrences f (j.val-variableBound f)).length := ⟨i.val,by simpa only [pieceUsedCount,h,↓reduceIte] using i.isLt⟩
    ⟨(clauseUsedPort f (pieceClauseIndex k f j h) a).val,by
      simpa only [pieceFullCount,h,↓reduceDIte] using (clauseUsedPort f (pieceClauseIndex k f j h) a).isLt⟩

theorem pieceUsedPort_injective {k : Nat} {f : CNF} (hf : BoundedOccurrence f) (j : PieceIndex k f)
    (a b : Fin (pieceUsedCount k f j)) (h : pieceUsedPort hf j a=pieceUsedPort hf j b) : a=b := by
  have hv := congrArg Fin.val h
  by_cases hj:j.val<variableBound f
  · let a' : Fin (variableOccurrences f j.val).length := ⟨a.val,by simpa only [pieceUsedCount,hj,↓reduceIte] using a.isLt⟩
    let b' : Fin (variableOccurrences f j.val).length := ⟨b.val,by simpa only [pieceUsedCount,hj,↓reduceIte] using b.isLt⟩
    have he : variableUsedPort hf j.val a'=variableUsedPort hf j.val b' := by
      apply Fin.ext
      simpa only [pieceUsedPort,hj,↓reduceDIte] using hv
    have hval := congrArg (fun x:Fin (variableOccurrences f j.val).length=>x.val) (variableUsedPort_injective hf j.val a' b' he)
    exact Fin.ext hval
  · let a' : Fin (clauseOccurrences f (j.val-variableBound f)).length := ⟨a.val,by simpa only [pieceUsedCount,hj,↓reduceIte] using a.isLt⟩
    let b' : Fin (clauseOccurrences f (j.val-variableBound f)).length := ⟨b.val,by simpa only [pieceUsedCount,hj,↓reduceIte] using b.isLt⟩
    have he : clauseUsedPort f (pieceClauseIndex k f j hj) a'=clauseUsedPort f (pieceClauseIndex k f j hj) b' := by
      apply Fin.ext
      simpa only [pieceUsedPort,hj,↓reduceDIte] using hv
    have hval := congrArg (fun x:Fin (clauseOccurrences f (j.val-variableBound f)).length=>x.val) (clauseUsedPort_injective f (pieceClauseIndex k f j hj) a' b' he)
    exact Fin.ext hval

theorem pieceUsedCount_le_three {k : Nat} {f : CNF} (hf : BoundedOccurrence f) (j : PieceIndex k f) :
    pieceUsedCount k f j≤3 := by
  unfold pieceUsedCount
  split
  · exact variableOccurrences_le_three hf j.val
  · exact clauseOccurrences_le_three hf (pieceClauseIndex k f j ‹_›)

/-- A selected source dart in a given block has exactly that block's incidence
vertex label. This is independent of any rotation or face choice. -/
theorem LocalPortChoices.sourcePort_piece_vertex {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (d : Fin (2*(placeFormula [] f).flatten.length)) (j : PieceIndex k f)
    (u : Fin (2*(ungluedFormulaPieces k f)[j.val].length))
    (h : C.sourcePort hf d=blockDart (ungluedFormulaPieces k f) j u) :
    occurrenceVertex f d=pieceVertex k f j := by
  unfold sourcePort at h
  unfold occurrenceVertex
  dsimp only at h ⊢
  split at h
  · rename_i hd
    simp only [hd,↓reduceIte]
    have hj := congrArg Fin.val (blockDart_block_injective (ungluedFormulaPieces k f) h)
    change (occurrence f _).literal.var=j.val at hj
    have hv := occurrence_variable_lt hf (⟨d.val/2,by have := d.isLt; omega⟩ : OccurrenceIndex f)
    have hjv : j.val<variableBound f := by rw [←hj]; exact hv
    simp only [pieceVertex,hjv,↓reduceIte,hj]
  · rename_i hd
    simp only [hd,↓reduceIte]
    have hj := congrArg Fin.val (blockDart_block_injective (ungluedFormulaPieces k f) h)
    change variableBound f+(occurrencePosition f _).clause.val=j.val at hj
    have hjv : ¬j.val<variableBound f := by omega
    simp only [pieceVertex,hjv,↓reduceIte]
    congr 1
    omega

/-- The finite node index covers every selected source dart whose port lies
inside this gadget block. -/
theorem LocalPortChoices.sourcePort_piece_complete {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (d : Fin (2*(placeFormula [] f).flatten.length)) (j : PieceIndex k f)
    (u : Fin (2*(ungluedFormulaPieces k f)[j.val].length))
    (h : C.sourcePort hf d=blockDart (ungluedFormulaPieces k f) j u) :
    ∃i,(pieceNodeIndex k f j).dart i=d :=
  (pieceNodeIndex k f j).complete d (C.sourcePort_piece_vertex hf d j u h)

/-- Every source incidence dart occurs in some local finite node enumeration. -/
theorem pieceNodeIndex_complete {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    (d : Fin (2*(placeFormula [] f).flatten.length)) :
    ∃j:PieceIndex k f,∃i,(pieceNodeIndex k f j).dart i=d := by
  obtain ⟨i,s,rfl⟩ := occurrenceDart_cases d
  cases s
  · let j := variablePieceIndex k f (occurrenceVariable hf i)
    refine ⟨j,?_⟩
    apply (pieceNodeIndex k f j).complete
    rw [occurrenceVertex_even]
    simp only [pieceVertex,j,variablePieceIndex,occurrenceVariable,
      occurrence_variable_lt hf i,↓reduceIte]
  · let j := clausePieceIndex k f (occurrencePosition f i).clause
    refine ⟨j,?_⟩
    apply (pieceNodeIndex k f j).complete
    rw [occurrenceVertex_odd]
    simp only [pieceVertex,j,clausePieceIndex,show ¬variableBound f+(occurrencePosition f i).clause.val<variableBound f by omega,
      ↓reduceIte,Nat.add_sub_cancel_left]

end STACS2027.PlanarAssembly
