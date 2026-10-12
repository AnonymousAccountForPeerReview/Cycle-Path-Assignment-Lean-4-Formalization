module

public import NPHardness.PlanarAssemblyProfileChoices

/-! Explicit fixed port-order and endpoint-side functions for every actual
variable/clause block, parameterized only by the source variable signs. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

theorem SphericalPortProfile.reindex {g:Graph} {m r:Nat}
    {ports:Fin m→Edge} {next:Fin m→Fin m} {side:Fin m→Bool}
    (hp:SphericalPortProfile g ports next side) (e:DartEquiv r m)
    (ports':Fin r→Edge) (next':Fin r→Fin r) (side':Fin r→Bool)
    (hports:∀i,ports' i=ports (e.toFun i))
    (hnext:∀i,e.toFun (next' i)=next (e.toFun i))
    (hside:∀i,side' i=side (e.toFun i)) :
    SphericalPortProfile g ports' next' side' := by
  obtain ⟨G,hG,hs,p,hi,he,hn,hsi⟩:=hp
  refine ⟨G,hG,hs,fun i=>p (e.toFun i),?_,?_,?_,?_⟩
  · intro i j hij
    exact e.injective (hi _ _ hij)
  · intro i
    rw [he,hports]
  · intro i
    obtain ⟨k,hk,hend,hinside⟩:=hn (e.toFun i)
    refine ⟨k,hk,?_,?_⟩
    · dsimp only
      rw [hnext]
      exact hend
    · intro r hr hrk j
      exact hinside r hr hrk (e.toFun j)
  · intro i
    rw [hsi,hside]

/-- Cyclic successor for a positive-sign variable, predecessor otherwise;
clauses always use the predecessor of their literal-slot cyclic order. -/
def pieceProfileNext {k:Nat} {f:CNF} (signs:Nat→Bool) (j:PieceIndex k f)
    (i:Fin (piecePorts k f j).length) : Fin (piecePorts k f j).length :=
  ⟨if j.val<variableBound f ∧ signs j.val=true then (i.val+1)%(piecePorts k f j).length
   else (i.val+(piecePorts k f j).length-1)%(piecePorts k f j).length,
    by have hp:0<(piecePorts k f j).length:=by have:=i.isLt;omega
       split <;> exact Nat.mod_lt _ hp⟩

def pieceProfileSide {k:Nat} {f:CNF} (signs:Nat→Bool) (j:PieceIndex k f)
    (i:Fin (piecePorts k f j).length) : Bool :=
  if j.val<variableBound f then ((i.val==0)==!(signs j.val)) else true

theorem variableSignedNext_val (s:Bool) (i:Fin 3) :
    (variableSignedNext s i).val=if s then (i.val+1)%3 else (i.val+2)%3 :=
  (by decide:∀s:Bool,∀i:Fin 3,(variableSignedNext s i).val=if s then (i.val+1)%3 else (i.val+2)%3) s i

theorem clauseThreePortNext_val (i:Fin 3) : (clauseThreePortNext i).val=(i.val+2)%3 :=
  (by decide:∀i:Fin 3,(clauseThreePortNext i).val=(i.val+2)%3) i

theorem clauseTwoPortNext_val (i:Fin 2) : (clauseTwoPortNext i).val=(i.val+1)%2 :=
  (by decide:∀i:Fin 2,(clauseTwoPortNext i).val=(i.val+1)%2) i

/-- Every actual gadget block admits its prescribed directed spherical profile
for every natural parameter, without a run-time embedding search. -/
theorem piece_signed_profile {k:Nat} {f:CNF} (hf:BoundedOccurrence f) (signs:Nat→Bool)
    (j:PieceIndex k f) :
    SphericalPortProfile (ungluedFormulaPieces k f)[j.val]
      (fun i=>(piecePorts k f j)[i.val]) (pieceProfileNext signs j) (pieceProfileSide signs j) := by
  by_cases hj:j.val<variableBound f
  · have hl:(piecePorts k f j).length=3:=by
      simp only [piecePorts,hj,↓reduceDIte,placedVariablePorts_length]
    have hp:=placedVariableGraph_signed_profile k j.val (signs j.val)
    rw [piece_variable_eq j hj]
    apply hp.reindex (DartEquiv.cast hl)
    · intro i
      simp only [piecePorts,hj,↓reduceDIte]
      exact placedVariablePorts_getElem k j.val ⟨i.val,by rw [←hl];exact i.isLt⟩
    · intro i
      apply Fin.ext
      rw [variableSignedNext_val]
      change (pieceProfileNext signs j i).val=if signs j.val then _ else _
      unfold pieceProfileNext
      simp only [hj,true_and,hl,DartEquiv.cast]
      cases signs j.val <;> simp <;> omega
    · intro i
      change (if j.val<variableBound f then ((i.val==0)==!(signs j.val)) else true)=
        (((⟨i.val,by rw [←hl];exact i.isLt⟩:Fin 3)==0)==!(signs j.val))
      simp only [hj,↓reduceIte]
      rfl
  · let t:=clauseIndexOfPiece j hj
    have hsize:=hf.placed_clause_size (List.getElem_mem t.isLt)
    have hsmall:(placeFormula [] f)[(clauseIndexOfPiece j hj).val].length≤3:=by
      change (placeFormula [] f)[t.val].length≤3
      omega
    have hl:(piecePorts k f j).length=(placeFormula [] f)[t.val].length:=by
      simp only [piecePorts,hj,↓reduceDIte]
      exact ungluedClausePorts_length _ _ _ _ hsmall
    rw [piece_clause_eq j hj]
    rcases hsize with hsize|hsize
    · have hl2:(piecePorts k f j).length=2:=hl.trans hsize
      have hg:ungluedClauseGraph k (variableBound f) t.val (placeFormula [] f)[t.val]=
          mapGraph (blockVertex (gadgetWidth k) (variableBound f+t.val)) (clauseTwoGraph k):=by
        simp only [ungluedClauseGraph,clauseGraph,hsize,↓reduceIte]
      rw [hg]
      apply (placedClauseTwoGraph_port_profile k (variableBound f+t.val)).reindex (DartEquiv.cast hl2)
      · intro i
        simp only [piecePorts,hj,↓reduceDIte]
        exact ungluedClausePorts_getElem _ _ _ _ hsmall
          ⟨i.val,by rw [←hl];exact i.isLt⟩
      · intro i
        apply Fin.ext
        rw [clauseTwoPortNext_val]
        change (pieceProfileNext signs j i).val=(i.val+1)%2
        simp only [pieceProfileNext,hj,false_and,↓reduceIte,hl2]
        congr 1
      · intro i
        simp only [pieceProfileSide,hj,↓reduceIte]
    · have hl3:(piecePorts k f j).length=3:=hl.trans hsize
      have hg:ungluedClauseGraph k (variableBound f) t.val (placeFormula [] f)[t.val]=
          mapGraph (blockVertex (gadgetWidth k) (variableBound f+t.val)) (clauseThreeGraph k):=by
        simp only [ungluedClauseGraph,clauseGraph,hsize,show ¬3=2 by decide,↓reduceIte]
      rw [hg]
      apply (placedClauseThreeGraph_port_profile k (variableBound f+t.val)).reindex (DartEquiv.cast hl3)
      · intro i
        simp only [piecePorts,hj,↓reduceDIte]
        exact ungluedClausePorts_getElem _ _ _ _ hsmall
          ⟨i.val,by rw [←hl];exact i.isLt⟩
      · intro i
        apply Fin.ext
        rw [clauseThreePortNext_val]
        change (pieceProfileNext signs j i).val=(i.val+2)%3
        simp only [pieceProfileNext,hj,false_and,↓reduceIte,hl3]
        congr 1
      · intro i
        simp only [pieceProfileSide,hj,↓reduceIte]

end STACS2027.PlanarAssembly
