module

public import NPHardness.PlanarSourcePackedBlocks

/-!
Arithmetic addresses and finite local neighborhoods for the registered grid.
`Q` denotes the ceiling of half the column count and is selected by a checked
arithmetic guard in the complete emitter.  Every local neighborhood contains
whole fixed blocks; the successor test discards their inactive or unrelated
occurrences.  Thus it uses no search over an externally supplied rotation.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Grid
open Complexity.Planar.Emit

structure Layout (n : Nat) where
  A : NumExpr n
  M : NumExpr n
  R : NumExpr n
  W : NumExpr n
  Q : NumExpr n

def Layout.lift {n : Nat} (d : Layout n) : Layout (n + 1) :=
  ⟨d.A.lift,d.M.lift,d.R.lift,d.W.lift,d.Q.lift⟩

def Layout.columnSize {n : Nat} (d : Layout n) (literal : Bool) : NumExpr n :=
  if literal then addN (mulN 48 d.W) 8 else addN (mulN 20 d.W) 4

def Layout.formulaLength {n : Nat} (d : Layout n) : NumExpr n :=
  .add (.mul d.M (d.columnSize false)) (.mul (mulN 2 d.W) (subN d.M 1))

def Layout.variableCount {n : Nat} (d : Layout n) : NumExpr n :=
  .mul d.M (colLenE d.W)

def Layout.columnBase {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd literal : Bool) : NumExpr n :=
  if odd then .add (.mul d.Q (d.columnSize literal))
    (.mul (revE (.sub d.M d.Q) k) (d.columnSize literal))
  else .mul (revE d.Q k) (d.columnSize literal)

def Layout.cellBase {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd literal : Bool) : NumExpr n :=
  .add (addN (d.columnBase k odd literal) (if literal then 4 else 2))
    (mulN (if literal then 48 else 20) (revE d.W idx))

def Layout.endBase {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd literal : Bool) : NumExpr n :=
  .add (addN (d.columnBase k odd literal) (if literal then 4 else 2))
    (mulN (if literal then 48 else 20) d.W)

def Layout.rainbowBase {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd literal : Bool) : NumExpr n :=
  let size := mulN (if literal then 4 else 2) d.W
  let base := .mul d.M (d.columnSize literal)
  let prior := if odd then .add (.mul (.sub d.M d.Q) size)
      (.mul (.sub (subN d.Q 2) k) size)
    else .mul (revE (.sub d.M d.Q) k) size
  .add (.add base prior) (mulN (if literal then 4 else 2) (revE d.W v))

def Layout.columnLive {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool) : Test n :=
  .le (twoE k (if odd then 2 else 1)) d.M

def Layout.cellLive {n : Nat} (d : Layout n) (k idx : NumExpr n) (odd : Bool) : Test n :=
  .and (d.columnLive k odd) (.le (addN idx 1) d.W)

def Layout.rainbowLive {n : Nat} (d : Layout n) (k v : NumExpr n) (odd : Bool) : Test n :=
  .and (.le (twoE k (if odd then 3 else 2)) d.M) (.le (addN v 1) d.W)

def Layout.cellTemplates {n : Nat} (d : Layout n) (k idx : NumExpr n) (odd : Bool) :
    List (Template n) :=
  let j := twoE k (if odd then 1 else 0)
  Packed.cellTemplates d.W j idx odd
    (.input (posE d.A d.M d.R d.W j (rowE d.W odd idx) 1))
    (.input (posE d.A d.M d.R d.W j (rowE d.W odd idx) 0))

def Layout.cellOccurrences {n : Nat} (d : Layout n) (k idx : NumExpr n) (odd : Bool) :
    List (Occurrence n) :=
  blockOccurrences (d.cellLive k idx odd) d.formulaLength d.variableCount
    (d.cellBase k idx odd false) (d.cellBase k idx odd true) (d.cellTemplates k idx odd)

def Layout.startOccurrences {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool) :
    List (Occurrence n) :=
  blockOccurrences (d.columnLive k odd) d.formulaLength d.variableCount
    (d.columnBase k odd false) (d.columnBase k odd true)
    (startTemplates d.W (twoE k (if odd then 1 else 0)))

def Layout.endOccurrences {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool) :
    List (Occurrence n) :=
  blockOccurrences (d.columnLive k odd) d.formulaLength d.variableCount
    (d.endBase k odd false) (d.endBase k odd true)
    (endTemplates d.W (twoE k (if odd then 1 else 0)))

def Layout.rainbowOccurrences {n : Nat} (d : Layout n) (k v : NumExpr n) (odd : Bool) :
    List (Occurrence n) :=
  blockOccurrences (d.rainbowLive k v odd) d.formulaLength d.variableCount
    (d.rainbowBase k v odd false) (d.rainbowBase k v odd true)
    (rainbowTemplates d.W (twoE k (if odd then 1 else 0)) v odd)

/-- Disable out-of-bound neighboring blocks without removing their syntax. -/
def gate {n : Nat} (test : Test n) (xs : List (Occurrence n)) : List (Occurrence n) :=
  xs.map fun p => {p with live := .and test p.live}

/-- Chain vertex at `cellOff W j idx`, including both boundary gadgets. -/
def Layout.chainCandidates {n : Nat} (d : Layout n) (k idx : NumExpr n) (odd : Bool) :
    List (Occurrence n) :=
  d.cellOccurrences k idx odd ++
    gate (.le (.const 1) idx) (d.cellOccurrences k (subN idx 1) odd) ++
    gate (Test.eq idx (.const 0)) (d.startOccurrences k odd) ++
    gate (Test.eq idx d.W) (d.endOccurrences k odd)

def Layout.cellCandidates {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (position : Nat) : List (Occurrence n) :=
  if position = 0 then d.chainCandidates k idx odd
  else if position = 9 then d.chainCandidates k (addN idx 1) odd
  else if position = 1 then
    d.cellOccurrences k idx odd ++
      (if odd then d.rainbowOccurrences k (revE d.W idx) false
       else gate (.le (.const 1) k) (d.rainbowOccurrences (subN k 1) idx true))
  else if position = 8 then
    d.cellOccurrences k idx odd ++
      d.rainbowOccurrences k (if odd then revE d.W idx else idx) odd
  else d.cellOccurrences k idx odd

def Layout.startCandidates {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool)
    (position : Nat) : List (Occurrence n) :=
  if position = 0 then d.startOccurrences k odd else d.chainCandidates k (.const 0) odd

def Layout.endCandidates {n : Nat} (d : Layout n) (k : NumExpr n) (odd : Bool)
    (position : Nat) : List (Occurrence n) :=
  if position = 0 then d.chainCandidates k d.W odd else d.endOccurrences k odd

def Layout.rainbowCandidates {n : Nat} (d : Layout n) (k v : NumExpr n) (odd : Bool)
    (endpoint : Nat) : List (Occurrence n) :=
  if odd then
    if endpoint = 0 then d.cellCandidates (addN k 1) v false 1
    else d.cellCandidates k (revE d.W v) true 8
  else if endpoint = 0 then d.cellCandidates k v false 8
    else d.cellCandidates k (revE d.W v) true 1

end STACS2027.PlanarSource.Packed
