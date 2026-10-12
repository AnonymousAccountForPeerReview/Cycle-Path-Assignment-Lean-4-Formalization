module

public import NPHardness.PlanarSourcePackedLayout
public import Complexity.Planar.Reduction

/-!
The complete, closed-syntax packed grid program.  It emits one packed copy
clause per original grid clause, followed by locally selected implication
clauses.  Candidate lists, keys, tests, packed addresses, and sign reads are
all fixed syntax compiled by the registered emitter compiler.

The compiler theorem below establishes polynomial runtime of this actual
program.  Identification of its emitted formula with the verified planar
ring expansion additionally needs the neighborhood and indexing theorems;
runtime alone does not assert source NP-hardness.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Grid
open Complexity.Planar.Emit

def sequence {n : Nat} : List (ClauseProgram n) → ClauseProgram n
  | [] => .skip
  | p :: ps => .seq p (sequence ps)

theorem sequence_emit {n : Nat} (ps : List (ClauseProgram n)) (w : SAT.Word) (env : Env n) :
    (sequence ps).emit w env = ps.flatMap (fun p => p.emit w env) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [sequence, ClauseProgram.emit_seq, List.flatMap_cons, ih]

def ringBlock {n : Nat} (ps : List (Occurrence n)) (positions : List Nat)
    (candidates : Nat → List (Occurrence n)) : ClauseProgram n :=
  sequence ((ps.zip positions).map fun p => successorProgram p.1 (candidates p.2))

def cellPositions (odd : Bool) : List Nat :=
  (cellT false false).flatMap fun t =>
    if t.2 != odd then t.1.map Prod.fst else (t.1.map Prod.fst).reverse

def Layout.cellProgram {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd ring : Bool) : ClauseProgram n :=
  if ring then ringBlock (d.cellOccurrences k idx odd) (cellPositions odd)
    (d.cellCandidates k idx odd)
  else copyBlock (d.cellBase k idx odd true) (d.cellTemplates k idx odd)

def Layout.startProgram {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd ring : Bool) : ClauseProgram n :=
  if ring then ringBlock (d.startOccurrences k odd) [0,1,1,0] (d.startCandidates k odd)
  else copyBlock (d.columnBase k odd true)
    (startTemplates d.W (twoE k (if odd then 1 else 0)))

def Layout.endProgram {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd ring : Bool) : ClauseProgram n :=
  if ring then ringBlock (d.endOccurrences k odd) [0,1,1,0] (d.endCandidates k odd)
  else copyBlock (d.endBase k odd true)
    (endTemplates d.W (twoE k (if odd then 1 else 0)))

def Layout.rainbowProgram {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd ring : Bool) : ClauseProgram n :=
  if ring then ringBlock (d.rainbowOccurrences k v odd) [0,1,0,1]
    (d.rainbowCandidates k v odd)
  else copyBlock (d.rainbowBase k v odd true)
    (rainbowTemplates d.W (twoE k (if odd then 1 else 0)) v odd)

def Layout.columnProgram {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd ring : Bool) : ClauseProgram n :=
  .seq (.seq (d.startProgram k odd ring)
    (.forDown d.W (d.lift.cellProgram k.lift (.var 0) odd ring)))
    (d.endProgram k odd ring)

def Layout.gridPhase {n : Nat} (d : Layout n) (ring : Bool) : ClauseProgram n :=
  .seq (.seq (.seq
    (.forDown d.M (.ifLe (twoE (.var 0) 1) d.M.lift
      (d.lift.columnProgram (.var 0) false ring) .skip))
    (.forDown d.M (.ifLe (twoE (.var 0) 2) d.M.lift
      (d.lift.columnProgram (.var 0) true ring) .skip)))
    (.forDown d.M (.ifLe (twoE (.var 0) 2) d.M.lift
      (.forDown d.W.lift (d.lift.lift.rainbowProgram (.var 1) (.var 0) false ring)) .skip)))
    (.forDown d.M (.ifLe (twoE (.var 0) 3) d.M.lift
      (.forDown d.W.lift (d.lift.lift.rainbowProgram (.var 1) (.var 0) true ring)) .skip))

def Layout.program {n : Nat} (d : Layout n) : ClauseProgram n :=
  .seq (d.gridPhase false) (d.gridPhase true)

def halfGuard {n : Nat} (m q : NumExpr n) : Test n :=
  .or (Test.eq (mulN 2 q) m) (Test.eq (mulN 2 q) (addN m 1))

/-- A counted loop selects the unique ceiling-half value using only arithmetic
comparisons.  Division is not introduced as a runtime primitive. -/
def gridProgram {n : Nat} (A M R W : NumExpr n) : ClauseProgram n :=
  .forDown (addN M 1)
    ((halfGuard M.lift (.var 0)).select
      (Layout.program ⟨A.lift,M.lift,R.lift,W.lift,.var 0⟩) .skip)

theorem halfGuard_eval {n : Nat} (m q : NumExpr n) (w : SAT.Word) (env : Env n) :
    (halfGuard m q).eval w env = true ↔ q.eval env = (m.eval env+1)/2 := by
  have hh : (halfGuard m q).eval w env = true ↔
      2*q.eval env = m.eval env ∨ 2*q.eval env = m.eval env+1 := by
    change ((Test.eq (mulN 2 q) m).eval w env ||
      (Test.eq (mulN 2 q) (addN m 1)).eval w env) = true ↔ _
    rw [Bool.or_eq_true, Test.eval_eq, Test.eval_eq]
    exact or_congr
      ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩
      ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩
  exact hh.trans (by omega)

theorem gridProgram_emit {n : Nat} (A M R W : NumExpr n) (w : SAT.Word) (env : Env n) :
    (gridProgram A M R W).emit w env =
      (Layout.program ⟨A.lift,M.lift,R.lift,W.lift,.var 0⟩).emit w
        (extend ((M.eval env+1)/2) env) := by
  simp only [gridProgram, ClauseProgram.emit_forDown, addN, NumExpr.eval,
    Test.select_emit, ClauseProgram.emit_skip]
  rw [Complexity.Planar.Emit.flatMap_single (i0 := (M.eval env+1)/2) (by omega)]
  · have hh : (halfGuard M.lift (NumExpr.var (0 : Fin (n+1)))).eval w
        (extend ((M.eval env+1)/2) env) = true := by
      rw [halfGuard_eval]
      simp only [NumExpr.eval, extend_zero, NumExpr.eval_lift]
    exact ite_eq_left hh
  · intro i hi hne
    have hh : ¬ (halfGuard M.lift (NumExpr.var (0 : Fin (n+1)))).eval w
        (extend i env) = true := by
      rw [halfGuard_eval]
      simpa only [NumExpr.eval, extend_zero, NumExpr.eval_lift] using hne
    exact ite_eq_right hh

theorem cellProgram_copies {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    (d.cellProgram k idx odd false).emit w env =
      copiesAt ((d.cellBase k idx odd true).eval env)
        (cellCNF (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)) (idx.eval env) odd
          (bitsW w (d.A.eval env) (d.M.eval env) (d.R.eval env) (d.W.eval env)
            (2*k.eval env+(if odd then 1 else 0)) (row (d.W.eval env) odd (idx.eval env)))) := by
  simp only [Layout.cellProgram, Bool.false_eq_true, ite_false, copyBlock_emit,
    Layout.cellTemplates, cellTemplates_eval, Test.eval, posE_eval, rowE_eval,
    twoE, NumExpr.eval, bitsW]

end STACS2027.PlanarSource.Packed
