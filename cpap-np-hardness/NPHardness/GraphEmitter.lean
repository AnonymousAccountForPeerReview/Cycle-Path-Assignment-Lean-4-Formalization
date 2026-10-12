module

public import NPHardness.GraphPrograms
public import NPHardness.LocatedGraph

/-! A complete graph-and-budget transducer, expressed as a finite program
accepted by the foundation's polynomial-time Turing-machine compiler. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT Complexity.StackTableauEmitter

def gridVariablesExpr {m n : Nat} (root : ClauseProgram m) (C : NumExpr n) : NumExpr n :=
  .mul (.add C (.const 1)) (.mul (.const 2) (.mul (.const 3) (emitterSlotsExpr root C)))

theorem gridVariablesExpr_eval {m n : Nat} (root : ClauseProgram m) (C : NumExpr n) (env : Env n) :
    (gridVariablesExpr root C).eval env = (C.eval env+1)*(2*(3*emitterSlots root (C.eval env))) := by
  simp [gridVariablesExpr,NumExpr.eval,emitterSlotsExpr_eval]

def gridCopyExprs {m n : Nat} (root : ClauseProgram m) (ls : List (LiteralExpr n))
    (C slot : NumExpr n) : List (LiteralExpr n) :=
  ls.zipIdx.map fun p =>
    ⟨.add (.mul p.1.index (.mul (.const 6) (emitterSlotsExpr root C)))
      (.add (.mul slot (.const 6)) (.const (2*p.2 + if p.1.positive then 0 else 1))),false⟩

theorem gridCopyExprs_eval {m n : Nat} (root : ClauseProgram m) (ls : List (LiteralExpr n))
    (C slot : NumExpr n) (env : Env n) :
    (gridCopyExprs root ls C slot).map (fun l => l.eval env) =
      sourceCopies (gridCopyClause (emitterSlots root (C.eval env)) (slot.eval env)
        (ls.map (fun l => l.eval env))) := by
  exact List.singleton_inj.mp (gridCopyTemplate_emit root ls C slot [] env)

def copyGraphTemplate {m n : Nat} (root : ClauseProgram m) (k : Nat)
    (ls : List (LiteralExpr n)) (C slot : NumExpr n) : ClauseProgram n :=
  clauseGraphProgram k (gridVariablesExpr root C) slot 1 (gridCopyExprs root ls C slot)

theorem copyGraphTemplate_emit {m n : Nat} (root : ClauseProgram m) (k : Nat)
    (ls : List (LiteralExpr n)) (C slot : NumExpr n) (input : Complexity.SAT.Word) (env : Env n) :
    (copyGraphTemplate root k ls C slot).emit input env =
      clauseGraphRecords k ((C.eval env+1)*(2*(3*emitterSlots root (C.eval env)))) (slot.eval env) 1
        (sourceCopies (gridCopyClause (emitterSlots root (C.eval env)) (slot.eval env)
          (ls.map (fun l => l.eval env)))) := by
  rw [copyGraphTemplate,clauseGraphProgram_emit,gridVariablesExpr_eval,gridCopyExprs_eval]

def sourceWheelEmitter {n : Nat} (p : ClauseProgram n) (C : NumExpr n) : ClauseProgram n :=
  gridWheelProgram (.add C (.const 1)) (.mul (.const 3) (emitterSlotsExpr p C))

theorem sourceWheelEmitter_emit {n : Nat} (p : ClauseProgram n) (C : NumExpr n)
    (input : Complexity.SAT.Word) (env : Env n) :
    (sourceWheelEmitter p C).emit input env = gridWheelFamily (C.eval env+1) (3*emitterSlots p (C.eval env)) := by
  simp only [sourceWheelEmitter,gridWheelProgram_emit,NumExpr.eval,emitterSlotsExpr_eval]

def graphEmitter {n : Nat} (k : Nat) (p : ClauseProgram n) (C D : NumExpr n) : ClauseProgram n :=
  .seq (variableGraphProgram k (gridVariablesExpr p C))
    (.seq (transformParameterized (fun ls R slot => clauseGraphProgram k R slot 0 ls)
      (sourceWheelEmitter p C) D (emitterSlotsExpr p C) (gridVariablesExpr p C))
      (transformAllocated (copyGraphTemplate p k) p C (.const 0)))

theorem graphEmitter_output {n : Nat} (k : Nat) (p : ClauseProgram n) (C D : NumExpr n)
    (input : Complexity.SAT.Word) (env : Env n) :
    let S := emitterSlots p (C.eval env)
    let N := (C.eval env+1)*(2*(3*S))
    let ws := allocatedEmit (sourceWheelEmitter p C) input env (D.eval env) S
    let xs := allocatedEmit p input env (C.eval env) 0
    GraphOutput ((graphEmitter k p C D).emit input env)
      (locatedGraph k N (gridLocated S ws xs)) (ws.length+xs.length) := by
  dsimp only
  let S := emitterSlots p (C.eval env)
  let N := (C.eval env+1)*(2*(3*S))
  let ws := allocatedEmit (sourceWheelEmitter p C) input env (D.eval env) S
  let xs := allocatedEmit p input env (C.eval env) 0
  have hw := transformParameterized_emit (fun ls R slot => clauseGraphProgram k R slot 0 ls)
    (fun N slot c => clauseGraphRecords k N slot 0 c)
    (fun ls R slot input env => clauseGraphProgram_emit k R slot 0 ls input env)
    (sourceWheelEmitter p C) D (emitterSlotsExpr p C) (gridVariablesExpr p C) input env
  have hx := transformAllocated_emit (copyGraphTemplate p k)
    (fun C slot c => clauseGraphRecords k ((C+1)*(2*(3*emitterSlots p C))) slot 1
      (sourceCopies (gridCopyClause (emitterSlots p C) slot c)))
    (copyGraphTemplate_emit p k) p C (.const 0) input env
  simp only [graphEmitter,ClauseProgram.emit,variableGraphProgram_emit,hw,hx,
    gridVariablesExpr_eval,emitterSlotsExpr_eval,NumExpr.eval]
  have hv : GraphOutput
      (graphRecords ((List.range N).reverse.flatMap (placedVariableGraph k)))
      ((List.range N).reverse.flatMap (placedVariableGraph k)) 0 := by
    apply graphRecords_output
    intro e he
    obtain ⟨v,_,he⟩ := List.mem_flatMap.mp he
    exact mapGraph_normalized _ _ e he
  have hwo := GraphOutput.flatMap ws (fun x => clauseGraphRecords k N x.1 0 x.2)
    (fun x => placedClauseGraph k N x.1 (x.2.map (fun l => PlacedLiteral.mk l 0))) (fun _ => 1)
    (fun x _ => clauseGraphRecords_output k N x.1 0 x.2)
  have hxo := GraphOutput.flatMap xs
    (fun x => clauseGraphRecords k N x.1 1 (sourceCopies (gridCopyClause S x.1 x.2)))
    (fun x => placedClauseGraph k N x.1 ((sourceCopies (gridCopyClause S x.1 x.2)).map (fun l => PlacedLiteral.mk l 1)))
    (fun _ => 1) (fun x _ => clauseGraphRecords_output k N x.1 1 _)
  simpa only [sum_map_const,Nat.mul_one,Nat.zero_add,locatedGraph,gridLocated,
    List.flatMap_append,List.flatMap_map,locateClause,locateCopyClause,Function.comp_def]
    using hv.append (hwo.append hxo)

end STACS2027
