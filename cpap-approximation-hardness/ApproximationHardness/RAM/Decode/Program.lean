module

public import ApproximationHardness.RAM.Decode.Scan
public import ApproximationHardness.Decode.Bound
import Lean.Elab.Tactic.Omega

/-!
# A linear-time RAM program for the decoding map of Theorem 11

Input `decInput f ps`: the formula as `ramInput f`, then the assignment as `pathsCode ps` (the
number of paths, then for each path its number of edges followed by the two endpoints of every
edge). Output `decOutput k f ps`: for every variable `v < n` the bit of `decodeAssign k ps v`
(`1` for true).

The program (`decProgram k`):

* `passAq`: `n`, and the end `N` of `ramInput f`;
* skips over the paths to find the end `E` of the input;
* fills, for every vertex `x < S = (n + m) w` (`w = gadgetWidth k`), the cells `E + 2x` and
  `E + 2x + 1` with the block `x / w` and the offset `x % w` of `x`, block by block;
* for every path: reads its edges once to decide whether they all lie in one block (`flag = 0`),
  and if not, reads them again and adds one to the counter `Wb + 3v + i` of every port edge `i` of
  a variable `v < n` it contains (`Wb = E + 2S`);
* writes, for every `v < n`, `1` if `W₁ + W₂ ≤ W₀` and `0` otherwise.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT
open Stmt

/-! ### Input and output -/

/-- An edge as two numbers. -/
def edgeCode (e : Edge) : List Nat := [e.1, e.2]
/-- A path: its number of edges, then its edges. -/
def pathCode (p : List Edge) : List Nat := p.length :: p.flatMap edgeCode
/-- A list of paths: their number, then the paths. -/
def pathsCode (ps : List (List Edge)) : List Nat := ps.length :: ps.flatMap pathCode
/-- The input of the decoding program: the formula, then the assignment. -/
def decInput (f : CNF) (ps : List (List Edge)) : List Nat := ramInput f ++ pathsCode ps
/-- The output of the decoding program: the decoded truth values of the variables `0, …, n − 1`. -/
def decOutput (k : Nat) (f : CNF) (ps : List (List Edge)) : List Nat :=
  (List.range (variableBound f)).map fun v => if decodeAssign k ps v then 1 else 0

/-! ### Registers -/

namespace DR
abbrev np : Nat := 50
abbrev E : Nat := 51
abbrev bi : Nat := 52
abbrev u : Nat := 53
abbrev x : Nat := 54
abbrev w : Nat := 55
abbrev addr : Nat := 56
abbrev Wb : Nat := 57
abbrev len : Nat := 58
abbrev cnt : Nat := 59
abbrev ps : Nat := 60
abbrev b0 : Nat := 61
abbrev flag : Nat := 62
abbrev ex : Nat := 63
abbrev ey : Nat := 64
abbrev bx : Nat := 65
abbrev bY : Nat := 66
abbrev ox : Nat := 67
abbrev oy : Nat := 68
abbrev t : Nat := 69
abbrev t2 : Nat := 70
abbrev z1 : Nat := 71
abbrev z2 : Nat := 72
abbrev z3 : Nat := 73
abbrev v : Nat := 74
abbrev vi : Nat := 75
abbrev w0 : Nat := 76
abbrev w1 : Nat := 77
abbrev w2 : Nat := 78
abbrev nb : Nat := 79
abbrev ui : Nat := 80
end DR

/-! ### Finding the end of the input -/

def scanPre : Stmt := seqs [Stmt.load DR.np Reg.p, add Reg.p Reg.p Reg.one]

def skipPath : Stmt :=
  seqs [sub DR.np DR.np Reg.one, Stmt.load DR.len Reg.p, add Reg.p Reg.p Reg.one, add DR.t DR.len DR.len,
    add Reg.p Reg.p DR.t]

/-! ### The block and offset tables -/

/-- `E := p`, `w := gadgetWidth k`, `nb := m + n` blocks, `x := 0`, `bi := 0`. -/
def tabPre (k : Nat) : Stmt :=
  seqs [add DR.E Reg.p Reg.zero, const DR.w (gadgetWidth k), const DR.addr 0, Stmt.load DR.nb DR.addr,
    add DR.nb DR.nb Reg.n, const DR.x 0, const DR.bi 0]

/-- Cell `x` of block `bi`, at offset `ui`. -/
def fillCell : Stmt :=
  seqs [sub DR.u DR.u Reg.one, add DR.addr DR.E DR.x, add DR.addr DR.addr DR.x, store DR.addr DR.bi,
    add DR.addr DR.addr Reg.one, store DR.addr DR.ui, add DR.x DR.x Reg.one, add DR.ui DR.ui Reg.one]

def fillBlock : Stmt :=
  seq (seqs [sub DR.nb DR.nb Reg.one, add DR.u DR.w Reg.zero, const DR.ui 0])
    (seq (loop DR.u fillCell) (add DR.bi DR.bi Reg.one))

/-! ### The paths -/

/-- `d := blk[r]`. -/
def blkOf (r d : Nat) : List Stmt := [add DR.addr DR.E r, add DR.addr DR.addr r, Stmt.load d DR.addr]
/-- `d := off[r]`. -/
def offOf (r d : Nat) : List Stmt := [add DR.addr DR.E r, add DR.addr DR.addr r, add DR.addr DR.addr Reg.one,
  Stmt.load d DR.addr]

/-- Read the edge at `p` into `ex, ey` and their blocks into `bx, bY`. -/
def readEdge : List Stmt :=
  [sub DR.cnt DR.cnt Reg.one, Stmt.load DR.ex Reg.p, add Reg.p Reg.p Reg.one, Stmt.load DR.ey Reg.p,
    add Reg.p Reg.p Reg.one] ++ blkOf DR.ex DR.bx ++ blkOf DR.ey DR.bY

/-- `flag := 1` if `r ≠ b0`. -/
def flagIfNe (r : Nat) : List Stmt :=
  [sub DR.t r DR.b0, sub DR.t2 DR.b0 r, add DR.t DR.t DR.t2, ifz DR.t skip (const DR.flag 1)]

def flagEdge : Stmt := seqs (readEdge ++ flagIfNe DR.bx ++ flagIfNe DR.bY)

/-- Add one to `W[3 bx + i]` if the offsets are `(a, b)`. -/
def portInc (i a b : Nat) : Stmt :=
  seqs [const DR.z1 a, sub DR.z2 DR.ox DR.z1, sub DR.z1 DR.z1 DR.ox, add DR.z2 DR.z2 DR.z1,
    const DR.z1 b, sub DR.z3 DR.oy DR.z1, sub DR.z1 DR.z1 DR.oy, add DR.z3 DR.z3 DR.z1, add DR.z2 DR.z2 DR.z3,
    ifz DR.z2 (seqs [add DR.addr DR.bx DR.bx, add DR.addr DR.addr DR.bx, add DR.addr DR.addr DR.Wb,
      const DR.z1 i, add DR.addr DR.addr DR.z1, Stmt.load DR.z1 DR.addr, add DR.z1 DR.z1 Reg.one,
      store DR.addr DR.z1]) skip]

def countEdge : Stmt :=
  seqs (readEdge ++ [sub DR.t DR.bx DR.bY, sub DR.t2 DR.bY DR.bx, add DR.t DR.t DR.t2,
    ifz DR.t (seq (sub DR.t2 Reg.n DR.bx) (ifz DR.t2 skip
      (seqs (offOf DR.ex DR.ox ++ offOf DR.ey DR.oy ++ [portInc 0 2 6, portInc 1 4 5, portInc 2 0 3])))) skip])

def pathPre : Stmt :=
  seqs [sub DR.np DR.np Reg.one, Stmt.load DR.len Reg.p, add Reg.p Reg.p Reg.one, add DR.ps Reg.p Reg.zero,
    const DR.flag 0, ifz DR.len skip (seqs (Stmt.load DR.ex Reg.p :: blkOf DR.ex DR.b0)), add DR.cnt DR.len Reg.zero]

def pathBody : Stmt :=
  seq pathPre (seq (loop DR.cnt flagEdge)
    (ifz DR.flag skip (seq (seqs [add Reg.p DR.ps Reg.zero, add DR.cnt DR.len Reg.zero]) (loop DR.cnt countEdge))))

/-- `Wb := E + 2x` (`x = S` after the tables), `p := N + 1`, `np := |ps|`. -/
def procPre : Stmt :=
  seqs [add DR.Wb DR.E DR.x, add DR.Wb DR.Wb DR.x, add Reg.p Reg.N Reg.zero, Stmt.load DR.np Reg.p,
    add Reg.p Reg.p Reg.one]

/-! ### The output -/

def outPre : Stmt := seqs [add DR.v Reg.n Reg.zero, const DR.vi 0]

def outBodyD : Stmt :=
  seqs [sub DR.v DR.v Reg.one, add DR.addr DR.vi DR.vi, add DR.addr DR.addr DR.vi, add DR.addr DR.addr DR.Wb,
    Stmt.load DR.w0 DR.addr, add DR.addr DR.addr Reg.one, Stmt.load DR.w1 DR.addr, add DR.addr DR.addr Reg.one,
    Stmt.load DR.w2 DR.addr, add DR.t DR.w1 DR.w2, sub DR.t DR.t DR.w0,
    ifz DR.t (write Reg.one) (write Reg.zero), add DR.vi DR.vi Reg.one]

/-! ### The program -/

def decProgram (k : Nat) : Stmt :=
  seq passAq (seq scanPre (seq (loop DR.np skipPath) (seq (tabPre k) (seq (loop DR.nb fillBlock)
    (seq procPre (seq (loop DR.np pathBody) (seq outPre (loop DR.v outBodyD))))))))

end STACS2027.RAM
