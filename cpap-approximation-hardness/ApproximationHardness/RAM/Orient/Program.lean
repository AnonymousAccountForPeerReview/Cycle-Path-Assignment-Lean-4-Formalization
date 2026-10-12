module

public import ApproximationHardness.RAM.Decode.Scan
public import ApproximationHardness.Planar.ExplicitOrientation
import Lean.Elab.Tactic.Omega

/-!
# A linear-time RAM program for the planar gadget orientation

Input `orInput f rot`: the formula as `ramInput f`, then a rotation list `rot` (the node
permutation of an embedding of the incidence graph, listed dart by dart). Output
`orOutput f rot`: for every occurrence `i < M` the orientation bit `flipBit f N i`
(`1` for true) of `ApproximationHardness.Planar.ExplicitOrientation`, where `N d = rot[d]`.

The program (`orProgram`), with `N = |ramInput f|`, `E = 2N` and `B = E + 2n`:

* `passAq`: `n = variableBound f`, and `N`;
* one pass over the clauses: for clause `j` with first occurrence `o = off j`, its sign
  `cs = [|j| = 3 ∧ rot[2o + 1] = 2(o + 2) + 1]`; for each of its literals, the occurrence
  number `occ`, its port (`0` if positive, else one more than the counter of earlier equal
  negative literals, kept in cell `E + 2v`), the first positive occurrence of each variable
  (plus one, in cell `E + 2v + 1`), and the record `port, v, port, cs` in cells `B + 4 occ, …`;
* one pass over the occurrences: the bit `[port = 0] ⊕ vs ⊕ cs`, where the variable sign `vs`
  reads the port record of the dart `rot[2 i₀]` (`i₀` the positive occurrence) at `B + 2 rot[2 i₀]`.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT
open Stmt

/-! ### Input and output -/

/-- The input of the orientation program: the formula, then the rotation list. -/
def orInput (f : CNF) (rot : List Nat) : List Nat := ramInput f ++ rot

/-- The node permutation read from a rotation list. -/
def rotFun (rot : List Nat) (d : Nat) : Nat := rot.getD d 0

/-- The output: the orientation bits, as numbers. -/
def orOutput (f : CNF) (rot : List Nat) : List Nat :=
  (PlanarAssembly.orientationBits f (rotFun rot)).map fun b => if b then 1 else 0

/-! ### Registers -/

namespace OR
abbrev E : Nat := 90
abbrev B : Nat := 91
abbrev occ : Nat := 92
abbrev cnt : Nat := 93
abbrev L : Nat := 94
abbrev cs : Nat := 95
abbrev t : Nat := 96
abbrev t2 : Nat := 97
abbrev a : Nat := 98
abbrev x : Nat := 99
abbrev y : Nat := 100
abbrev v : Nat := 101
abbrev s : Nat := 102
abbrev nc : Nat := 103
abbrev port : Nat := 104
abbrev q : Nat := 105
abbrev i : Nat := 106
abbrev a1 : Nat := 107
abbrev vs : Nat := 108
abbrev d : Nat := 109
abbrev pd : Nat := 110
abbrev sm : Nat := 111
abbrev three : Nat := 112
abbrev five : Nat := 113
abbrev two : Nat := 114
end OR

/-! ### The program -/

/-- `E := 2N`, `B := E + 2n`, `p := 1`, `m := ramInput[0]`, `occ := 0`, and constants. -/
def orPre : Stmt :=
  seqs [add OR.E Reg.N Reg.N, add OR.B OR.E Reg.n, add OR.B OR.B Reg.n, const Reg.p 1, const OR.a 0,
    Stmt.load Reg.m OR.a, const OR.occ 0, const OR.two 2, const OR.three 3, const OR.five 5]

/-- Read the length of a clause and compute its sign. -/
def orClausePre : Stmt :=
  seqs [sub Reg.m Reg.m Reg.one, Stmt.load OR.L Reg.p, add Reg.p Reg.p Reg.one,
    sub OR.t OR.L OR.three, sub OR.t2 OR.three OR.L, add OR.t OR.t OR.t2, const OR.cs 0,
    ifz OR.t (seqs [add OR.a Reg.N OR.occ, add OR.a OR.a OR.occ, add OR.a OR.a Reg.one, Stmt.load OR.x OR.a,
        add OR.y OR.occ OR.occ, add OR.y OR.y OR.five, sub OR.t OR.x OR.y, sub OR.t2 OR.y OR.x,
        add OR.t OR.t OR.t2, ifz OR.t (const OR.cs 1) skip]) skip,
    add OR.cnt OR.L Reg.zero]

/-- One literal occurrence: its port, the positive-occurrence table, and its record. -/
def orLit : Stmt :=
  seqs [sub OR.cnt OR.cnt Reg.one, Stmt.load OR.v Reg.p, add Reg.p Reg.p Reg.one,
    Stmt.load OR.s Reg.p, add Reg.p Reg.p Reg.one, add OR.a OR.E OR.v, add OR.a OR.a OR.v,
    ifz OR.s (seqs [Stmt.load OR.nc OR.a, add OR.port OR.nc Reg.one, store OR.a OR.port])
      (seqs [const OR.port 0, add OR.a OR.a Reg.one, Stmt.load OR.q OR.a,
        ifz OR.q (seqs [add OR.q OR.occ Reg.one, store OR.a OR.q]) skip]),
    add OR.a OR.B OR.occ, add OR.a OR.a OR.occ, add OR.a OR.a OR.occ, add OR.a OR.a OR.occ,
    store OR.a OR.port, add OR.a OR.a Reg.one, store OR.a OR.v, add OR.a OR.a Reg.one, store OR.a OR.port,
    add OR.a OR.a Reg.one, store OR.a OR.cs, add OR.occ OR.occ Reg.one]

def orClause : Stmt := seq orClausePre (loop OR.cnt orLit)

def orOutPre : Stmt := seqs [add OR.cnt OR.occ Reg.zero, const OR.i 0]

/-- The variable sign of the variable in `OR.v`, into `OR.vs`. -/
def orVarSign : List Stmt :=
  [const OR.vs 0, add OR.a OR.E OR.v, add OR.a OR.a OR.v, add OR.a OR.a Reg.one, Stmt.load OR.q OR.a,
    ifz OR.q skip (seqs [sub OR.q OR.q Reg.one, add OR.a Reg.N OR.q, add OR.a OR.a OR.q, Stmt.load OR.d OR.a,
      add OR.a OR.B OR.d, add OR.a OR.a OR.d, Stmt.load OR.pd OR.a,
      sub OR.t OR.pd OR.two, sub OR.t2 OR.two OR.pd, add OR.t OR.t OR.t2, ifz OR.t (const OR.vs 1) skip])]

/-- One output bit: `[port = 0] ⊕ vs ⊕ cs`. -/
def orOut : Stmt :=
  seqs ([sub OR.cnt OR.cnt Reg.one,
    add OR.a OR.B OR.i, add OR.a OR.a OR.i, add OR.a OR.a OR.i, add OR.a OR.a OR.i,
    Stmt.load OR.port OR.a, add OR.a OR.a Reg.one, Stmt.load OR.v OR.a, add OR.a OR.a Reg.one,
    add OR.a OR.a Reg.one, Stmt.load OR.cs OR.a,
    const OR.a1 0, ifz OR.port (const OR.a1 1) skip] ++ orVarSign ++
    [add OR.sm OR.a1 OR.vs, add OR.sm OR.sm OR.cs,
    sub OR.t OR.sm Reg.one, sub OR.t2 Reg.one OR.sm, add OR.t OR.t OR.t2,
    ifz OR.t (write Reg.one) (seqs [sub OR.t OR.sm OR.three, sub OR.t2 OR.three OR.sm, add OR.t OR.t OR.t2,
      ifz OR.t (write Reg.one) (write Reg.zero)]),
    add OR.i OR.i Reg.one])

def orProgram : Stmt :=
  seq passAq (seq orPre (seq (loop Reg.m orClause) (seq orOutPre (loop OR.cnt orOut))))

end STACS2027.RAM
