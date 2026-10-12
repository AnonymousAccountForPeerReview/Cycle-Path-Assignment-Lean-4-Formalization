module

public import NPHardness.PlanarSourcePackedSuccessor
public import NPHardness.SourceOccurrences

/-!
Packed occurrence descriptors for fixed grid blocks.  Every number in a
descriptor is an expression in the registered emitter syntax; every sign is
an input test.  In particular, successor tests do not receive a table of
precomputed answers.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Grid
open Complexity.Planar.Emit

def addN {n : Nat} (a : NumExpr n) (b : Nat) : NumExpr n := .add a (.const b)
def mulN {n : Nat} (a : Nat) (b : NumExpr n) : NumExpr n := .mul (.const a) b
def subN {n : Nat} (a : NumExpr n) (b : Nat) : NumExpr n := .sub a (.const b)

structure Template (n : Nat) where
  literals : List (NumExpr n × Test n)
  top : Bool

def Template.eval {n : Nat} (t : Template n) (w : SAT.Word) (env : Env n) : Clause :=
  t.literals.map fun l => ⟨l.1.eval env,l.2.eval w env⟩

def orientExpr {n : Nat} (K v : NumExpr n) (top : Bool) : NumExpr n :=
  if top then v else .sub (subN K 1) v

/-- The three cases in the registered comb key, written as arithmetic syntax. -/
def keyExpr {n : Nat} (N K j : NumExpr n) (t : Template n) (slot : Nat) : NumExpr n :=
  let lo := orientExpr K (t.literals.headD (.const 0,.const false)).1 t.top
  let hi := orientExpr K (t.literals.getLastD (.const 0,.const false)).1 t.top
  if slot = 0 then
    .add (.mul (addN (mulN 2 hi) (if t.literals.length = 2 then 1 else 0)) (addN N 1)) j
  else if slot + 1 = t.literals.length then
    .add (.mul (addN (mulN 2 (.add (addN K 1) lo))
      (if t.literals.length = 2 then 0 else 1)) (addN N 1)) (.sub N j)
  else .add (.mul (mulN 2 K) (addN N 1)) N

def templateOccurrences {n : Nat} (live : Test n) (N K clauseBase literalBase : NumExpr n)
    (t : Template n) : List (Occurrence n) :=
  t.literals.zipIdx.map fun p =>
    ⟨live,addN literalBase p.2,p.1.1,t.top,keyExpr N K clauseBase t p.2,p.1.2⟩

def blockOccurrences {n : Nat} (live : Test n) (N K : NumExpr n) :
    NumExpr n → NumExpr n → List (Template n) → List (Occurrence n)
  | _, _, [] => []
  | cb, lb, t :: ts => templateOccurrences live N K cb lb t ++
      blockOccurrences live N K (addN cb 1) (addN lb t.literals.length) ts

/-- Copies of a block use packed occurrence indices and all-negative signs. -/
def copyBlock {n : Nat} : NumExpr n → List (Template n) → ClauseProgram n
  | _, [] => .skip
  | base, t :: ts => .seq
      (.clause (t.literals.zipIdx.map fun p => ⟨addN base p.2,false⟩))
      (copyBlock (addN base t.literals.length) ts)

def copiesAt (base : Nat) : CNF → CNF
  | [] => []
  | c :: cs => [(c.zipIdx.map fun p => ⟨base+p.2,false⟩)] ++ copiesAt (base+c.length) cs

theorem copyBlock_emit {n : Nat} (base : NumExpr n) (ts : List (Template n))
    (w : SAT.Word) (env : Env n) :
    (copyBlock base ts).emit w env =
      copiesAt (base.eval env) (ts.map fun t => t.eval w env) := by
  induction ts generalizing base with
  | nil => rfl
  | cons t ts ih =>
      simp only [copyBlock, ClauseProgram.emit_seq, ClauseProgram.emit_clause, ih,
        List.map_cons, copiesAt, Template.eval, List.zipIdx_map, List.map_map,
        List.length_map, addN, NumExpr.eval, LiteralExpr.eval, Function.comp_def,
        Prod.map, id_eq]

/-- Select among four fixed signs after reading the two occurrence bits. -/
def signChoice {n : Nat} (bp bn : Test n) (s00 s01 s10 s11 : Bool) : Test n :=
  .or (.and bp (.or (.and bn (.const s11)) (.and (.not bn) (.const s10))))
    (.and (.not bp) (.or (.and bn (.const s01)) (.and (.not bn) (.const s00))))

theorem signChoice_eval {n : Nat} (bp bn : Test n) (s00 s01 s10 s11 : Bool)
    (w : SAT.Word) (env : Env n) :
    (signChoice bp bn s00 s01 s10 s11).eval w env =
      if bp.eval w env then (if bn.eval w env then s11 else s10)
      else (if bn.eval w env then s01 else s00) := by
  by_cases hp : bp.eval w env = true <;> by_cases hn : bn.eval w env = true <;>
    simp_all [signChoice, Test.eval]

def templateSign (bp bn : Bool) (clause slot : Nat) : Bool :=
  ((((cellT bp bn)[clause]?).getD ([],false)).1[slot]?).getD (0,false) |>.2

def cellTemplates {n : Nat} (W j idx : NumExpr n) (odd : Bool) (bp bn : Test n) :
    List (Template n) :=
  (cellT false false).zipIdx.map fun p =>
    let literals := p.1.1.zipIdx.map fun l =>
      (addN (cellOffE W j idx) l.1.1,
        signChoice bp bn
          (templateSign false false p.2 l.2) (templateSign false true p.2 l.2)
          (templateSign true false p.2 l.2) (templateSign true true p.2 l.2))
    ⟨if p.1.2 != odd then literals else literals.reverse,p.1.2 != odd⟩

def startTemplates {n : Nat} (W j : NumExpr n) : List (Template n) :=
  [⟨[(colBaseE W j,.const true),(addN (colBaseE W j) 1,.const false)],true⟩,
   ⟨[(addN (colBaseE W j) 1,.const false),(colBaseE W j,.const false)],false⟩]

set_option maxRecDepth 4096 in
theorem cellTemplates_eval {n : Nat} (W j idx : NumExpr n) (odd : Bool)
    (bp bn : Test n) (w : SAT.Word) (env : Env n) :
    (cellTemplates W j idx odd bp bn).map (fun t => t.eval w env) =
      cellCNF (W.eval env) (j.eval env) (idx.eval env) odd
        (bp.eval w env,bn.eval w env) := by
  by_cases hp : bp.eval w env = true <;> by_cases hn : bn.eval w env = true <;>
    cases odd <;>
    simp_all [cellTemplates, Template.eval, signChoice_eval, templateSign,
      cellCNF, cellT, orT, crossT, inst, addN, NumExpr.eval]

def endTemplates {n : Nat} (W j : NumExpr n) : List (Template n) :=
  [⟨[(cellOffE W j W,.const true),(addN (cellOffE W j W) 1,.const true)],true⟩,
   ⟨[(addN (cellOffE W j W) 1,.const false),(cellOffE W j W,.const true)],false⟩]

def rainbowTemplates {n : Nat} (W j v : NumExpr n) (odd : Bool) : List (Template n) :=
  if odd then
    [⟨[(addN (cellOffE W (addN j 1) v) 1,.const true),
        (addN (cellOffE W j (revE W v)) 8,.const false)],false⟩,
     ⟨[(addN (cellOffE W (addN j 1) v) 1,.const false),
        (addN (cellOffE W j (revE W v)) 8,.const true)],false⟩]
  else
    [⟨[(addN (cellOffE W j v) 8,.const false),
        (addN (cellOffE W (addN j 1) (revE W v)) 1,.const true)],true⟩,
     ⟨[(addN (cellOffE W j v) 8,.const true),
        (addN (cellOffE W (addN j 1) (revE W v)) 1,.const false)],true⟩]

theorem startTemplates_eval {n : Nat} (W j : NumExpr n) (w : SAT.Word) (env : Env n) :
    (startTemplates W j).map (fun t => t.eval w env) = startG (W.eval env) (j.eval env) := rfl

theorem endTemplates_eval {n : Nat} (W j : NumExpr n) (w : SAT.Word) (env : Env n) :
    (endTemplates W j).map (fun t => t.eval w env) = endG (W.eval env) (j.eval env) := rfl

theorem rainbowTemplates_eval {n : Nat} (W j v : NumExpr n) (odd : Bool)
    (w : SAT.Word) (env : Env n) :
    (rainbowTemplates W j v odd).map (fun t => t.eval w env) =
      if odd then rbOdd (W.eval env) (j.eval env) (v.eval env)
      else rbEven (W.eval env) (j.eval env) (v.eval env) := by
  cases odd <;> rfl

end STACS2027.PlanarSource.Packed
