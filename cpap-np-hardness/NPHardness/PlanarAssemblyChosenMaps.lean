module

public import NPHardness.PlanarAssemblySphericalPlaced
public import NPHardness.PlanarAssemblyPieces

/-! A uniform family of chosen local spherical embeddings and full port
selectors gives the exact concatenated map and occurrence-port selections. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

/-- A chosen spherical map and actual lookup-certified port darts. -/
structure EmbeddingPorts (g ports : Graph) where
  map : Hypermap (2*g.length)
  embedding : IsGraphEmbedding g map
  spherical : 2*map.componentCount+2*g.length≤map.eulerRhs
  port : Fin ports.length → Fin (2*g.length)
  injective : ∀ i j, port i=port j → i=j
  lookup : ∀ i, g[(port i).val/2]?=some ports[i.val]

def clauseIndexOfPiece {k : Nat} {f : CNF} (i : Fin (ungluedFormulaPieces k f).length)
    (hi : ¬ i.val < variableBound f) : Fin (placeFormula [] f).length :=
  ⟨i.val-variableBound f,by
    have hh := i.isLt
    simp only [ungluedFormulaPieces,List.length_append,List.length_map,
      List.length_range,List.length_mapIdx] at hh
    omega⟩

def piecePorts (k : Nat) (f : CNF) (i : Fin (ungluedFormulaPieces k f).length) : Graph :=
  if hi : i.val<variableBound f then placedVariablePorts k i.val
  else ungluedClausePorts k (variableBound f) (clauseIndexOfPiece i hi).val
    (placeFormula [] f)[(clauseIndexOfPiece i hi).val]

@[simp] theorem piecePorts_variable (k : Nat) (f : CNF) (v : Fin (variableBound f)) :
    piecePorts k f (variablePieceIndex k f v)=placedVariablePorts k v.val := by
  simp only [piecePorts,variablePieceIndex,v.isLt,↓reduceDIte]

@[simp] theorem piecePorts_clause (k : Nat) (f : CNF) (j : Fin (placeFormula [] f).length) :
    piecePorts k f (clausePieceIndex k f j)=
      ungluedClausePorts k (variableBound f) j.val (placeFormula [] f)[j.val] := by
  simp only [piecePorts,clausePieceIndex,clauseIndexOfPiece,
    show ¬variableBound f+j.val<variableBound f by omega,↓reduceDIte,Nat.add_sub_cancel_left]

theorem piece_variable_eq {k : Nat} {f : CNF} (i : Fin (ungluedFormulaPieces k f).length)
    (hi : i.val < variableBound f) :
    (ungluedFormulaPieces k f)[i.val]=placedVariableGraph k i.val :=
  variablePiece_eq k f ⟨i.val,hi⟩

theorem piece_clause_eq {k : Nat} {f : CNF} (i : Fin (ungluedFormulaPieces k f).length)
    (hi : ¬ i.val < variableBound f) :
    (ungluedFormulaPieces k f)[i.val]=
      ungluedClauseGraph k (variableBound f) (clauseIndexOfPiece i hi).val
        (placeFormula [] f)[(clauseIndexOfPiece i hi).val] := by
  have he : i=clausePieceIndex k f (clauseIndexOfPiece i hi) := by
    apply Fin.ext
    change i.val=variableBound f+(i.val-variableBound f)
    omega
  conv => lhs; rw [he]
  exact clausePiece_eq k f (clauseIndexOfPiece i hi)

theorem piecePorts_spherical {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    (i : Fin (ungluedFormulaPieces k f).length) :
    HasSphericalCofacialPorts (ungluedFormulaPieces k f)[i.val] (piecePorts k f i) := by
  by_cases hi : i.val<variableBound f
  · rw [piece_variable_eq i hi]
    simp only [piecePorts,hi,↓reduceDIte]
    exact placedVariableGraph_sphericalPorts k i.val
  · rw [piece_clause_eq i hi]
    simp only [piecePorts,hi,↓reduceDIte]
    exact ungluedClauseGraph_sphericalPorts _ _ _ _
      (hf.placed_clause_size (List.getElem_mem (clauseIndexOfPiece i hi).isLt))

theorem piecePorts_nodup {k : Nat} {f : CNF}
    (i : Fin (ungluedFormulaPieces k f).length) : (piecePorts k f i).Nodup := by
  unfold piecePorts
  split
  · exact placedVariablePorts_nodup _ _
  · exact ungluedClausePorts_nodup _ _ _ _

abbrev ChosenPieces (k : Nat) (f : CNF) :=
  (i : Fin (ungluedFormulaPieces k f).length) →
    EmbeddingPorts (ungluedFormulaPieces k f)[i.val] (piecePorts k f i)

def ChosenPieces.maps {k : Nat} {f : CNF} (L : ChosenPieces k f) :
    LocalMaps (ungluedFormulaPieces k f) := fun i => (L i).map

def variablePortIndex (k : Nat) (f : CNF) (v : Fin (variableBound f)) (i : Fin 3) :
    Fin (piecePorts k f (variablePieceIndex k f v)).length :=
  Fin.cast (by rw [piecePorts_variable,placedVariablePorts_length]) i

def clausePortIndex (k : Nat) (f : CNF) (hf : BoundedOccurrence f)
    (j : Fin (placeFormula [] f).length) (i : Fin (placeFormula [] f)[j.val].length) :
    Fin (piecePorts k f (clausePieceIndex k f j)).length :=
  Fin.cast (by rw [piecePorts_clause,ungluedClausePorts_length _ _ _ _ (by
    have := hf.placed_clause_size (List.getElem_mem j.isLt); omega)]) i

def ChosenPieces.choices {k : Nat} {f : CNF} (L : ChosenPieces k f) (hf : BoundedOccurrence f) :
    LocalPortChoices k f where
  varDart v i := Fin.cast (by rw [variablePiece_eq])
    ((L (variablePieceIndex k f v)).port (variablePortIndex k f v i))
  clause j i := Fin.cast (by rw [clausePiece_eq])
    ((L (clausePieceIndex k f j)).port (clausePortIndex k f hf j i))
  variable_injective v i j he := by
    have hh := congrArg Fin.val he
    have hp := (L (variablePieceIndex k f v)).injective _ _ (Fin.ext hh)
    apply Fin.ext
    exact congrArg (fun x : Fin (piecePorts k f (variablePieceIndex k f v)).length => x.val) hp
  clause_injective j i t he := by
    have hh := congrArg Fin.val he
    have hp := (L (clausePieceIndex k f j)).injective _ _ (Fin.ext hh)
    apply Fin.ext
    exact congrArg (fun x : Fin (piecePorts k f (clausePieceIndex k f j)).length => x.val) hp
  variable_edge v i := by
    have hh := (L (variablePieceIndex k f v)).lookup (variablePortIndex k f v i)
    simpa only [variablePiece_eq,piecePorts_variable,variablePortIndex,Fin.val_cast,
      placedVariablePorts_getElem] using hh
  clause_edge j i := by
    have hh := (L (clausePieceIndex k f j)).lookup (clausePortIndex k f hf j i)
    have hi : (placeFormula [] f)[j.val].length≤3 := by
      have := hf.placed_clause_size (List.getElem_mem j.isLt); omega
    simpa only [clausePiece_eq,piecePorts_clause,clausePortIndex,Fin.val_cast,
      ungluedClausePorts_getElem _ _ _ _ hi i] using hh

theorem ChosenPieces.variable_global_port {k : Nat} {f : CNF} (L : ChosenPieces k f)
    (hf : BoundedOccurrence f) (v : Fin (variableBound f)) (i : Fin 3) :
    variableGlobalDart k f v ((L.choices hf).varDart v i) =
      blockDart (ungluedFormulaPieces k f) (variablePieceIndex k f v)
        ((L (variablePieceIndex k f v)).port (variablePortIndex k f v i)) := by
  apply Fin.ext
  rfl

theorem ChosenPieces.clause_global_port {k : Nat} {f : CNF} (L : ChosenPieces k f)
    (hf : BoundedOccurrence f) (j : Fin (placeFormula [] f).length)
    (i : Fin (placeFormula [] f)[j.val].length) :
    clauseGlobalDart k f j ((L.choices hf).clause j i) =
      blockDart (ungluedFormulaPieces k f) (clausePieceIndex k f j)
        ((L (clausePieceIndex k f j)).port (clausePortIndex k f hf j i)) := by
  apply Fin.ext
  rfl

theorem ChosenPieces.spherical {k : Nat} {f : CNF} (L : ChosenPieces k f) :
    2*(piecesMap (ungluedFormulaPieces k f) L.maps).componentCount+
      2*(ungluedFormulaPieces k f).flatten.length ≤
      (piecesMap (ungluedFormulaPieces k f) L.maps).eulerRhs :=
  piecesMap_spherical _ L.maps (fun i => (L i).spherical)

theorem blockGraph_end {g : Graph} {width : Nat} (hb : VerticesBelow g width)
    (ho : EdgesOrdered g) (tag d : Nat) (hd : d<2*(mapGraph (blockVertex width tag) g).length) :
    ∃ u, u<width ∧ halfEdgeEnd (mapGraph (blockVertex width tag) g) d=some (blockVertex width tag u) := by
  have hd' : d<2*g.length := by simpa only [mapGraph,List.length_map] using hd
  obtain ⟨u,hu,he⟩ := halfEdgeEnd_bound hb hd'
  refine ⟨u,hu,?_⟩
  rw [mapGraph_block_eq ho,halfEdgeEnd_relabel,he]
  rfl

theorem piece_end (k : Nat) (f : CNF) (i : Fin (ungluedFormulaPieces k f).length)
    (d : Nat) (hd : d<2*(ungluedFormulaPieces k f)[i.val].length) :
    ∃ u, u<gadgetWidth k ∧ halfEdgeEnd (ungluedFormulaPieces k f)[i.val] d=
      some (blockVertex (gadgetWidth k) i.val u) := by
  by_cases hi : i.val<variableBound f
  · rw [piece_variable_eq i hi] at hd ⊢
    exact blockGraph_end (variableGraph_below k) (realizeLinks_ordered _ _) i.val d hd
  · rw [piece_clause_eq i hi] at hd ⊢
    obtain ⟨u,hu,he⟩ := blockGraph_end (clauseGraph_below k _) (clauseGraph_ordered k _)
      (variableBound f+(clauseIndexOfPiece i hi).val) d hd
    have ht : variableBound f+(clauseIndexOfPiece i hi).val=i.val := by
      change variableBound f+(i.val-variableBound f)=i.val
      omega
    exact ⟨u,hu,he.trans (congrArg (fun tag => some (blockVertex (gadgetWidth k) tag u)) ht)⟩

theorem formulaPieces_disjoint (k : Nat) (f : CNF)
    (i j : Fin (ungluedFormulaPieces k f).length) (hij : i≠j)
    (d : Fin (2*(ungluedFormulaPieces k f)[i.val].length))
    (e : Fin (2*(ungluedFormulaPieces k f)[j.val].length)) :
    halfEdgeEnd (ungluedFormulaPieces k f)[i.val] d.val ≠
      halfEdgeEnd (ungluedFormulaPieces k f)[j.val] e.val := by
  obtain ⟨u,hu,he⟩ := piece_end k f i d.val d.isLt
  obtain ⟨v,hv,hf⟩ := piece_end k f j e.val e.isLt
  rw [he,hf]
  intro h
  exact hij (Fin.ext (blockVertex_injective hu hv (Option.some.inj h)).1)

/-- The chosen disjoint local embeddings give a registered embedding of the
actual concatenated graph; vertex-block separation is proved here. -/
theorem ChosenPieces.embedding {k : Nat} {f : CNF} (L : ChosenPieces k f) :
    IsGraphEmbedding (ungluedFormulaPieces k f).flatten
      (piecesMap (ungluedFormulaPieces k f) L.maps) :=
  piecesMap_embedding _ L.maps (fun i => (L i).embedding) (fun i => (L i).spherical)
    (formulaPieces_disjoint k f)

end STACS2027.PlanarAssembly
