module

public import NPHardness.PlanarAssemblyIndexDarts

/-! Concrete local-to-global port-dart indexing. Local selections remain
parameters so that their orientation can follow the given incidence rotation.
Every selection is tied to its actual port edge by a lookup equation. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT

def variablePieceIndex (k : Nat) (f : CNF) (v : Fin (variableBound f)) :
    Fin (ungluedFormulaPieces k f).length :=
  ⟨v.val, by simp only [ungluedFormulaPieces, List.length_append, List.length_map,
    List.length_range, List.length_mapIdx]; have := v.isLt; omega⟩

def clausePieceIndex (k : Nat) (f : CNF) (j : Fin (placeFormula [] f).length) :
    Fin (ungluedFormulaPieces k f).length :=
  ⟨variableBound f+j.val, by simp only [ungluedFormulaPieces, List.length_append,
    List.length_map, List.length_range, List.length_mapIdx]; have := j.isLt; omega⟩

theorem variablePiece_eq (k : Nat) (f : CNF) (v : Fin (variableBound f)) :
    (ungluedFormulaPieces k f)[(variablePieceIndex k f v).val] = placedVariableGraph k v.val := by
  simp only [ungluedFormulaPieces, variablePieceIndex]
  rw [List.getElem_append_left (by simp)]
  simp

theorem clausePiece_eq (k : Nat) (f : CNF) (j : Fin (placeFormula [] f).length) :
    (ungluedFormulaPieces k f)[(clausePieceIndex k f j).val] =
      ungluedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val] := by
  simp only [ungluedFormulaPieces, clausePieceIndex]
  rw [List.getElem_append_right (by simp)]
  simp

def variableGlobalDart (k : Nat) (f : CNF) (v : Fin (variableBound f))
    (d : Fin (2*(placedVariableGraph k v.val).length)) :
    Fin (2*(ungluedFormulaPieces k f).flatten.length) :=
  blockDart (ungluedFormulaPieces k f) (variablePieceIndex k f v)
    (Fin.cast (by rw [variablePiece_eq]) d)

def clauseGlobalDart (k : Nat) (f : CNF) (j : Fin (placeFormula [] f).length)
    (d : Fin (2*(ungluedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]).length)) :
    Fin (2*(ungluedFormulaPieces k f).flatten.length) :=
  blockDart (ungluedFormulaPieces k f) (clausePieceIndex k f j)
    (Fin.cast (by rw [clausePiece_eq]) d)

theorem variableGlobalDart_lookup (k : Nat) (f : CNF) (v : Fin (variableBound f))
    (d : Fin (2*(placedVariableGraph k v.val).length)) :
    (ungluedFormulaGraph k f)[(variableGlobalDart k f v d).val/2]? =
      (placedVariableGraph k v.val)[d.val/2]? := by
  have h := blockDart_edge_lookup (ungluedFormulaPieces k f) (variablePieceIndex k f v)
    (Fin.cast (by rw [variablePiece_eq]) d)
  simpa only [variableGlobalDart, blockDart, ungluedFormulaPieces_flatten, variablePiece_eq, Fin.val_cast] using h

theorem clauseGlobalDart_lookup (k : Nat) (f : CNF) (j : Fin (placeFormula [] f).length)
    (d : Fin (2*(ungluedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]).length)) :
    (ungluedFormulaGraph k f)[(clauseGlobalDart k f j d).val/2]? =
      (ungluedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val])[d.val/2]? := by
  have h := blockDart_edge_lookup (ungluedFormulaPieces k f) (clausePieceIndex k f j)
    (Fin.cast (by rw [clausePiece_eq]) d)
  simpa only [clauseGlobalDart, blockDart, ungluedFormulaPieces_flatten, clausePiece_eq, Fin.val_cast] using h

theorem variableGlobalDart_piece_injective (k : Nat) (f : CNF)
    {v w : Fin (variableBound f)}
    {d : Fin (2*(placedVariableGraph k v.val).length)}
    {e : Fin (2*(placedVariableGraph k w.val).length)}
    (h : variableGlobalDart k f v d = variableGlobalDart k f w e) : v=w := by
  have hi := blockDart_block_injective (ungluedFormulaPieces k f) h
  have hv := congrArg (fun d => d.val) hi
  exact Fin.ext hv

theorem clauseGlobalDart_piece_injective (k : Nat) (f : CNF)
    {i j : Fin (placeFormula [] f).length}
    {d : Fin (2*(ungluedClauseGraph k (variableBound f) i.val (placeFormula [] f)[i.val]).length)}
    {e : Fin (2*(ungluedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]).length)}
    (h : clauseGlobalDart k f i d = clauseGlobalDart k f j e) : i=j := by
  have hi := congrArg Fin.val (blockDart_block_injective (ungluedFormulaPieces k f) h)
  change variableBound f+i.val = variableBound f+j.val at hi
  exact Fin.ext (by omega)

theorem variableGlobalDart_injective (k : Nat) (f : CNF) (v : Fin (variableBound f))
    {d e : Fin (2*(placedVariableGraph k v.val).length)}
    (h : variableGlobalDart k f v d = variableGlobalDart k f v e) : d=e := by
  have hi := blockDart_injective (ungluedFormulaPieces k f) (variablePieceIndex k f v) h
  have hv := congrArg (fun d => d.val) hi
  exact Fin.ext hv

theorem clauseGlobalDart_injective (k : Nat) (f : CNF) (j : Fin (placeFormula [] f).length)
    {d e : Fin (2*(ungluedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]).length)}
    (h : clauseGlobalDart k f j d = clauseGlobalDart k f j e) : d=e := by
  have hi := blockDart_injective (ungluedFormulaPieces k f) (clausePieceIndex k f j) h
  have hv := congrArg (fun d => d.val) hi
  exact Fin.ext hv

theorem variableGlobalDart_ne_clauseGlobalDart (k : Nat) (f : CNF)
    (v : Fin (variableBound f)) (j : Fin (placeFormula [] f).length)
    (d : Fin (2*(placedVariableGraph k v.val).length))
    (e : Fin (2*(ungluedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]).length)) :
    variableGlobalDart k f v d ≠ clauseGlobalDart k f j e := by
  intro h
  have hi := congrArg Fin.val (blockDart_block_injective (ungluedFormulaPieces k f) h)
  change v.val = variableBound f+j.val at hi
  have := v.isLt
  omega

/-- The original position of one allocated occurrence in the clause list. -/
structure OccurrencePosition (f : CNF) (p : PlacedLiteral) where
  clause : Fin (placeFormula [] f).length
  slot : Fin (placeFormula [] f)[clause.val].length
  value : (placeFormula [] f)[clause.val][slot.val] = p

theorem occurrencePosition_exists (f : CNF) (i : Fin (placeFormula [] f).flatten.length) :
    Nonempty (OccurrencePosition f (placeFormula [] f).flatten[i.val]) := by
  obtain ⟨c,hc,hp⟩ := List.mem_flatten.mp (List.getElem_mem i.isLt)
  obtain ⟨j,hj,hjc⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨s,hs,hsp⟩ := List.mem_iff_getElem.mp hp
  subst c
  exact ⟨⟨⟨j,hj⟩,⟨s,hs⟩,hsp⟩⟩

noncomputable def occurrencePosition (f : CNF) (i : Fin (placeFormula [] f).flatten.length) :
    OccurrencePosition f (placeFormula [] f).flatten[i.val] :=
  Classical.choice (occurrencePosition_exists f i)

theorem placedOccurrences_nodup (f : CNF) : (placeFormula [] f).flatten.Nodup := by
  rw [placeFormula_flatten]
  exact placeLiterals_nodup [] f.flatten

/-- Local dart choices must name the actual allocated port edge. The finite
injection fields can be obtained from `cofacial_choose_darts`. Orientations
and face orders are deliberately not fixed by this record. -/
structure LocalPortChoices (k : Nat) (f : CNF) where
  varDart : ∀ v : Fin (variableBound f), Fin 3 → Fin (2*(placedVariableGraph k v.val).length)
  clause : ∀ j : Fin (placeFormula [] f).length,
    Fin (placeFormula [] f)[j.val].length →
      Fin (2*(ungluedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val]).length)
  variable_injective : ∀ v i j, varDart v i = varDart v j → i=j
  clause_injective : ∀ j i t, clause j i = clause j t → i=t
  variable_edge : ∀ v i, (placedVariableGraph k v.val)[(varDart v i).val/2]? =
    some (mapEdge (blockVertex (gadgetWidth k) v.val)
      (edge (variableEndpoint i.val false) (variableEndpoint i.val true)))
  clause_edge : ∀ j i,
    (ungluedClauseGraph k (variableBound f) j.val (placeFormula [] f)[j.val])[(clause j i).val/2]? =
    some (mapEdge (blockVertex (gadgetWidth k) (variableBound f+j.val))
      (edge (clauseEndpoint i.val false) (clauseEndpoint i.val true)))

end STACS2027.PlanarAssembly
