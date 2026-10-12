module

public import ApproximationHardness.RAM.SpecB
public import ApproximationHardness.Registered.Records
import Lean.Elab.Tactic.Omega

/-!
# A linear-time RAM program for the Theorem 8 graph

Input format (`ramInput f`): the number of clauses, then for each clause its
length followed by `var, sign` for each literal (`sign = 1` for a positive
literal). Output (`ramOutput k f`): the budget `m = |f|`, then the two endpoints
of every edge of the Theorem 8 graph, in the order of Section 5's edge list.

The program (`program k`) has three passes: the first computes the number of
variables `n = variableBound f` and the input length; the second emits the `n`
variable gadgets and stores the block start of every variable in a table; the
third emits the clause gadgets, finding the port of each occurrence from a
table of occurrence counts indexed by literal. Every gadget has constant size
for fixed `k`, so the program runs in `O(n + m)` steps.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-! ### Input and output -/

/-- The sign of a literal as a number: `1` if positive, `0` if negative. -/
def signCode (l : Literal) : Nat := if l.positive then 1 else 0
/-- A literal as two input numbers: its variable and its sign. -/
def litCode (l : Literal) : List Nat := [l.var, signCode l]
/-- A clause as input numbers: its length, then its literals. -/
def clauseCode (c : Clause) : List Nat := c.length :: c.flatMap litCode
/-- The RAM input of a formula: the number of clauses, then the clauses. -/
def ramInput (f : CNF) : List Nat := f.length :: f.flatMap clauseCode

/-- The edges of `g` relabelled by `t`, as unnormalized pairs. -/
def rawPairs (t : Nat → Nat) (g : Graph) : List (Nat × Nat) := g.map fun e => (t e.1, t e.2)

def varPairs (k v₀ t : Nat) : List (Nat × Nat) :=
  (List.range' v₀ t).flatMap fun v => rawPairs (blockVertex (gadgetWidth k) v) (variableGraph k)

def clausePairs (k n j : Nat) (past : List Literal) (c : Clause) : List (Nat × Nat) :=
  rawPairs (clauseVertex (gadgetWidth k) n j (placeLiterals past c)) (clauseGraph k (placeLiterals past c))

def clausePairsFrom (k n : Nat) : Nat → List Literal → CNF → List (Nat × Nat)
  | _, _, [] => []
  | j, past, c :: f => clausePairs k n j past c ++ clausePairsFrom k n (j + 1) (past ++ c) f

/-- The edges of the Theorem 8 graph, in the order of its edge list, before normalization. -/
def formulaPairs (k : Nat) (f : CNF) : List (Nat × Nat) :=
  varPairs k 0 (variableBound f) ++ clausePairsFrom k (variableBound f) 0 [] f

/-- A list of pairs written as numbers: both entries of every pair, in order. -/
def edgeWord (es : List (Nat × Nat)) : List Nat := es.flatMap fun e => [e.1, e.2]

/-- The output: the budget, then the endpoints of every edge. -/
def ramOutput (k : Nat) (f : CNF) : List Nat := f.length :: edgeWord (formulaPairs k f)

theorem formulaRecords_pairs (k : Nat) (f : CNF) :
    Registered.formulaRecords k f = (formulaPairs k f).map fun e => Registered.pairRecord e.1 e.2 := by
  have hraw : ∀ t g, Registered.rawRecords t g = (rawPairs t g).map fun e => Registered.pairRecord e.1 e.2 := by
    intro t g; simp [Registered.rawRecords, rawPairs]
  have hc : ∀ j past (f : CNF), Registered.clauseRecordsFrom k (variableBound f) j past f =
      (clausePairsFrom k (variableBound f) j past f).map fun e => Registered.pairRecord e.1 e.2 := by
    intro j past f
    generalize variableBound f = n
    induction f generalizing j past with
    | nil => rfl
    | cons c f ih =>
      simp [Registered.clauseRecordsFrom, clausePairsFrom, ih, Registered.clauseRecords, clausePairs, hraw]
  simp only [Registered.formulaRecords, formulaPairs, List.map_append, hc, Registered.varRecords, varPairs,
    List.map_flatMap, hraw]

/-- The output's pairs, normalized, are the edges of the Theorem 8 graph. -/
theorem formulaGraph_eq_pairs (k : Nat) (f : CNF) :
    formulaGraph k f = (formulaPairs k f).map fun e => edge e.1 e.2 := by
  have h := (Registered.formulaRecords_output k f).2.1
  rw [formulaRecords_pairs] at h
  rw [← h]
  simp only [instructionGraph]
  rw [List.filterMap_map, ← List.filterMap_eq_map]
  congr 1

/-! ### Registers -/

namespace Reg
abbrev p : Nat := 0
abbrev m : Nat := 1
abbrev len : Nat := 2
abbrev v : Nat := 3
abbrev sg : Nat := 4
abbrev n : Nat := 5
abbrev t : Nat := 6
abbrev one : Nat := 7
abbrev N : Nat := 8
abbrev B : Nat := 9
abbrev vb : Nat := 10
abbrev cv : Nat := 11
abbrev vi : Nat := 12
abbrev W : Nat := 13
abbrev cb : Nat := 14
abbrev addr : Nat := 15
abbrev cc : Nat := 16
abbrev x : Nat := 27
abbrev zero : Nat := 28
end Reg

/-- The block register and the two endpoint registers of slot `i`. -/
def bReg (i : Nat) : Nat := 17 + i
def eReg (i : Nat) (side : Bool) : Nat := 20 + 2 * i + (if side then 1 else 0)

open Stmt

/-! ### The first pass -/

/-- One literal of the first pass: `n := max n (var + 1)`. -/
def litA : Stmt :=
  seqs [sub Reg.len Reg.len Reg.one, Stmt.load Reg.v Reg.p, add Reg.p Reg.p Reg.one, add Reg.p Reg.p Reg.one,
    add Reg.v Reg.v Reg.one, sub Reg.t Reg.v Reg.n, ifz Reg.t skip (add Reg.n Reg.v Reg.zero)]

def clauseA : Stmt :=
  seq (seqs [sub Reg.m Reg.m Reg.one, Stmt.load Reg.len Reg.p, add Reg.p Reg.p Reg.one]) (loop Reg.len litA)

def passA : Stmt :=
  seq (seqs [const Reg.one 1, const Reg.p 0, Stmt.load Reg.m Reg.p, add Reg.p Reg.p Reg.one, write Reg.m])
    (seq (loop Reg.m clauseA) (seqs [add Reg.N Reg.p Reg.zero, add Reg.B Reg.N Reg.n, add Reg.B Reg.B Reg.n]))

/-! ### The variable gadgets -/

/-- Emit the edge `(base + a, base + b)`. -/
def edgeConst (base a b : Nat) : List Stmt :=
  [const Reg.t a, add Reg.x base Reg.t, write Reg.x, const Reg.t b, add Reg.x base Reg.t, write Reg.x]

def varEmit (k : Nat) : List Stmt := (variableGraph k).flatMap fun e => edgeConst Reg.vb e.1 e.2

def varBody (k : Nat) : Stmt :=
  seqs ([sub Reg.cv Reg.cv Reg.one, add Reg.addr Reg.B Reg.vi, store Reg.addr Reg.vb] ++ varEmit k ++
    [add Reg.vb Reg.vb Reg.W, add Reg.vi Reg.vi Reg.one])

def passV (k : Nat) : Stmt :=
  seq (seqs [const Reg.W (gadgetWidth k), const Reg.vb 0, const Reg.vi 0, add Reg.cv Reg.n Reg.zero])
    (seq (loop Reg.cv (varBody k)) (seqs [add Reg.cb Reg.vb Reg.zero]))

/-! ### The clause gadgets -/

/-- Read one literal into slot `i`: its port endpoints and the block of its variable. -/
def readLit (i : Nat) : Stmt :=
  seqs [Stmt.load Reg.v Reg.p, add Reg.p Reg.p Reg.one, Stmt.load Reg.sg Reg.p, add Reg.p Reg.p Reg.one,
    add Reg.addr Reg.N Reg.v, add Reg.addr Reg.addr Reg.v, add Reg.addr Reg.addr Reg.sg,
    Stmt.load Reg.cc Reg.addr, add Reg.t Reg.cc Reg.one, store Reg.addr Reg.t,
    ifz Reg.sg
      (ifz Reg.cc (seq (const (eReg i false) 4) (const (eReg i true) 5))
        (seq (const (eReg i false) 0) (const (eReg i true) 3)))
      (seq (const (eReg i false) 2) (const (eReg i true) 6)),
    add Reg.addr Reg.B Reg.v, Stmt.load (bReg i) Reg.addr]

/-- `x :=` the global vertex of the local gadget vertex `a` of a clause with `len` literals. -/
def endpointCode (len a : Nat) : List Stmt :=
  match clausePortAt a with
  | some (i, side) => if i < len then [add Reg.x (bReg i) (eReg i side)] else [const Reg.t a, add Reg.x Reg.cb Reg.t]
  | none => [const Reg.t a, add Reg.x Reg.cb Reg.t]

def clauseEmit (k len : Nat) : List Stmt :=
  (Registered.gadgetEdges k len).flatMap fun e =>
    endpointCode len e.1 ++ [write Reg.x] ++ endpointCode len e.2 ++ [write Reg.x]

def clauseB (k : Nat) : Stmt :=
  seqs [sub Reg.m Reg.m Reg.one, Stmt.load Reg.len Reg.p, add Reg.p Reg.p Reg.one, readLit 0, readLit 1,
    const Reg.t 2, sub Reg.t Reg.len Reg.t,
    ifz Reg.t (seqs (clauseEmit k 2)) (seq (readLit 2) (seqs (clauseEmit k 3))),
    add Reg.cb Reg.cb Reg.W]

def passB (k : Nat) : Stmt :=
  seq (seqs [const Reg.p 0, Stmt.load Reg.m Reg.p, add Reg.p Reg.p Reg.one]) (loop Reg.m (clauseB k))

/-- The program. -/
def program (k : Nat) : Stmt := seq passA (seq (passV k) (passB k))

end STACS2027.RAM
