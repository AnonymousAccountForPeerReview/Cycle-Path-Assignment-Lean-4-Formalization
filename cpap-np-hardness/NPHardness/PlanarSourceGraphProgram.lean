module
public import NPHardness.PlanarSourceGraphBlocks
import Lean.Elab.Tactic.Omega
@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar Grid
open Complexity.Planar.Emit

/-- Exact number of source literal occurrences, hence of copied variables. -/
def Layout.occurrenceCount {n : Nat} (d : Layout n) : NumExpr n :=
  .add (.mul d.M (d.columnSize true)) (.mul (mulN 4 d.W) (subN d.M 1))

theorem Layout.occurrenceCount_eval {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n)
    (hq : 2*d.Q.eval env=d.M.eval env ∨ 2*d.Q.eval env=d.M.eval env+1) :
    d.occurrenceCount.eval env=(d.source w env).flatten.length := by
  have h := Index.grid_size true (d.W.eval env) (d.M.eval env) (d.Q.eval env) (d.bits w env) hq
  change (d.source w env).flatten.length=d.M.eval env*(48*d.W.eval env+8)+(d.M.eval env-1)*d.W.eval env*4 at h
  rw [h]
  simp only [Layout.occurrenceCount,Layout.columnSize,mulN,subN,addN,NumExpr.eval,↓reduceIte]
  ac_rfl

@[simp] theorem Layout.occurrenceCount_lift_eval {n : Nat} (d : Layout n) (env : Env n) (i : Nat) :
    d.lift.occurrenceCount.eval (extend i env)=d.occurrenceCount.eval env := by
  simp only [Layout.occurrenceCount,Layout.columnSize,Layout.lift,addN,mulN,subN,NumExpr.eval,NumExpr.eval_lift,↓reduceIte]

/-- A descending machine loop emits variable gadgets in ascending label order. -/
def ascendingVariableGraphProgram {n : Nat} (k : Nat) (V : NumExpr n) : ClauseProgram n :=
  .forDown V (graphProgram (fun v => .add (.mul (revE V.lift (.var 0)) (.const (gadgetWidth k))) (.const v)) (variableGraph k))

theorem ascendingVariableGraphProgram_emit {n : Nat} (k : Nat) (V : NumExpr n)
    (w : SAT.Word) (env : Env n) :
    (ascendingVariableGraphProgram k V).emit w env=
      graphRecords ((List.range (V.eval env)).flatMap (placedVariableGraph k)) := by
  simp only [ascendingVariableGraphProgram,ClauseProgram.emit_forDown,graphProgram_emit]
  have hmap : (List.range (V.eval env)).reverse.map (fun i => V.eval env-1-i)=List.range (V.eval env) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_reverse,List.getElem_range,List.length_range]
      simp only [List.length_range] at hj
      omega
  have he (i : Nat) :
      mapGraph (fun x => (NumExpr.add (.mul (revE V.lift (.var 0)) (.const (gadgetWidth k))) (.const x)).eval (extend i env)) (variableGraph k)=
        placedVariableGraph k (V.eval env-1-i) := by
    simp only [placedVariableGraph,NumExpr.eval,revE_eval,NumExpr.eval_lift,extend_zero]
    congr 1
  simp only [he,graphRecords,List.map_flatMap]
  have hh := congrArg (List.flatMap (fun i => (placedVariableGraph k i).map graphRecord)) hmap
  simpa only [List.flatMap_map] using hh

def Layout.startGraphProgram {n : Nat} (d : Layout n) (k : Nat) (column : NumExpr n)
    (odd ring : Bool) : ClauseProgram n :=
  if ring then ringGraphBlock k d.occurrenceCount d.formulaLength
    (d.startOccurrences column odd) [0,1,1,0] (d.startCandidates column odd)
  else copyGraphBlock k d.occurrenceCount (d.columnBase column odd false) (d.columnBase column odd true)
    (startTemplates d.W (twoE column (if odd then 1 else 0)))

def Layout.cellGraphProgram {n : Nat} (d : Layout n) (k : Nat) (column idx : NumExpr n)
    (odd ring : Bool) : ClauseProgram n :=
  if ring then ringGraphBlock k d.occurrenceCount d.formulaLength
    (d.cellOccurrences column idx odd) (cellPositions odd) (d.cellCandidates column idx odd)
  else copyGraphBlock k d.occurrenceCount (d.cellBase column idx odd false) (d.cellBase column idx odd true)
    (d.cellTemplates column idx odd)

def Layout.endGraphProgram {n : Nat} (d : Layout n) (k : Nat) (column : NumExpr n)
    (odd ring : Bool) : ClauseProgram n :=
  if ring then ringGraphBlock k d.occurrenceCount d.formulaLength
    (d.endOccurrences column odd) [0,1,1,0] (d.endCandidates column odd)
  else copyGraphBlock k d.occurrenceCount (d.endBase column odd false) (d.endBase column odd true)
    (endTemplates d.W (twoE column (if odd then 1 else 0)))

def Layout.rainbowGraphProgram {n : Nat} (d : Layout n) (k : Nat) (column row : NumExpr n)
    (odd ring : Bool) : ClauseProgram n :=
  if ring then ringGraphBlock k d.occurrenceCount d.formulaLength
    (d.rainbowOccurrences column row odd) [0,1,0,1] (d.rainbowCandidates column row odd)
  else copyGraphBlock k d.occurrenceCount (d.rainbowBase column row odd false) (d.rainbowBase column row odd true)
    (rainbowTemplates d.W (twoE column (if odd then 1 else 0)) row odd)

def Layout.columnGraphProgram {n : Nat} (d : Layout n) (k : Nat) (column : NumExpr n)
    (odd ring : Bool) : ClauseProgram n :=
  .seq (.seq (d.startGraphProgram k column odd ring)
    (.forDown d.W (d.lift.cellGraphProgram k column.lift (.var 0) odd ring)))
    (d.endGraphProgram k column odd ring)

def Layout.graphPhase {n : Nat} (d : Layout n) (k : Nat) (ring : Bool) : ClauseProgram n :=
  .seq (.seq (.seq
    (.forDown d.M (.ifLe (twoE (.var 0) 1) d.M.lift
      (d.lift.columnGraphProgram k (.var 0) false ring) .skip))
    (.forDown d.M (.ifLe (twoE (.var 0) 2) d.M.lift
      (d.lift.columnGraphProgram k (.var 0) true ring) .skip)))
    (.forDown d.M (.ifLe (twoE (.var 0) 2) d.M.lift
      (.forDown d.W.lift (d.lift.lift.rainbowGraphProgram k (.var 1) (.var 0) false ring)) .skip)))
    (.forDown d.M (.ifLe (twoE (.var 0) 3) d.M.lift
      (.forDown d.W.lift (d.lift.lift.rainbowGraphProgram k (.var 1) (.var 0) true ring)) .skip))

/-- Exact source block order with dense graph tags and ascending variables. -/
def Layout.graphProgram {n : Nat} (d : Layout n) (k : Nat) : ClauseProgram n :=
  .seq (.seq (ascendingVariableGraphProgram k d.occurrenceCount) (d.graphPhase k false))
    (d.graphPhase k true)

def gridGraphProgram {n : Nat} (k : Nat) (A M R W : NumExpr n) : ClauseProgram n :=
  .forDown (addN M 1)
    ((halfGuard M.lift (.var 0)).select
      (Layout.graphProgram ⟨A.lift,M.lift,R.lift,W.lift,.var 0⟩ k) .skip)

theorem gridGraphProgram_emit {n : Nat} (k : Nat) (A M R W : NumExpr n) (w : SAT.Word) (env : Env n) :
    (gridGraphProgram k A M R W).emit w env=
      (Layout.graphProgram ⟨A.lift,M.lift,R.lift,W.lift,.var 0⟩ k).emit w
        (extend ((M.eval env+1)/2) env) := by
  simp only [gridGraphProgram,ClauseProgram.emit_forDown,addN,NumExpr.eval,
    Test.select_emit,ClauseProgram.emit_skip]
  rw [Complexity.Planar.Emit.flatMap_single (i0 := (M.eval env+1)/2) (by omega)]
  · have hh : (halfGuard M.lift (NumExpr.var (0 : Fin (n+1)))).eval w
        (extend ((M.eval env+1)/2) env)=true := by
      rw [halfGuard_eval]
      simp only [NumExpr.eval,extend_zero,NumExpr.eval_lift]
    exact ite_eq_left hh
  · intro i hi hne
    have hh : ¬(halfGuard M.lift (NumExpr.var (0 : Fin (n+1)))).eval w (extend i env)=true := by
      rw [halfGuard_eval]
      simpa only [NumExpr.eval,extend_zero,NumExpr.eval_lift] using hne
    exact ite_eq_right hh

end STACS2027.PlanarSource.Packed
