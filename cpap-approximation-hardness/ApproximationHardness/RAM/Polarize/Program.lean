module

public import ApproximationHardness.RAM.Pass
public import ApproximationHardness.Polarize
import Lean.Elab.Tactic.Omega

/-!
# A linear-time RAM program for Lemma 10's transformation

Input `ramInput f`, output `ramInput (polarize f)` (the same format: the number of
clauses, then each clause as its length and `var, sign` per literal). The program
(`polProgram`) makes five passes over the input, each clause handled by a loop-free
block (clauses have two or three literals):

* `passA` of the Theorem 8 program: `n = variableBound f`, the input length `N` and
  `B = N + 2n`; it also writes the clause count `|f| = |polarize f|`;
* `cntBody`: the occurrence count of every literal `(v, s)`, in the cell `N + 2v + s`;
* `keepBody`: for every clause, whether Lemma 10 deletes it (`delCode`: a tautology,
  or a variable occurring three times with one polarity, read from the count table);
  the deleted clauses are counted (`r`), and the positive occurrences of every variable
  in the kept clauses are counted in the cell `B + v`;
* `outBody`: every kept clause is written, the sign of the variables with two positive
  kept occurrences complemented;
* `padBody`: the `r` padding clauses `(x_{n+2j} ∨ x_{n+2j+1})`.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT
open Stmt

namespace PR
abbrev v0 : Nat := 30
abbrev s0 : Nat := 31
abbrev v1 : Nat := 32
abbrev s1 : Nat := 33
abbrev v2 : Nat := 34
abbrev s2 : Nat := 35
abbrev addr : Nat := 36
abbrev x : Nat := 37
abbrev y : Nat := 38
abbrev z : Nat := 39
abbrev u : Nat := 40
abbrev del : Nat := 41
abbrev r : Nat := 42
abbrev two : Nat := 43
abbrev three : Nat := 44
abbrev w : Nat := 45
end PR

/-! ### Reading a clause -/

/-- Read the literal at `p` into the registers `vr` (variable) and `sr` (sign). -/
def rdLit (vr sr : Nat) : Stmt :=
  seqs [Stmt.load vr Reg.p, add Reg.p Reg.p Reg.one, Stmt.load sr Reg.p, add Reg.p Reg.p Reg.one]

/-- Read a clause of two or three literals: its length into `len`, its literals into the slots
`(v0, s0)`, `(v1, s1)` and, for three literals, `(v2, s2)`; one clause fewer is left (`m`). -/
def readClause : Stmt :=
  seqs [sub Reg.m Reg.m Reg.one, Stmt.load Reg.len Reg.p, add Reg.p Reg.p Reg.one, rdLit PR.v0 PR.s0,
    rdLit PR.v1 PR.s1, sub Reg.t Reg.len PR.two, ifz Reg.t skip (rdLit PR.v2 PR.s2)]

/-- Run `s` on the third literal only when the clause has three literals. -/
def ifThird (s : Stmt) : Stmt := seq (sub Reg.t Reg.len PR.two) (ifz Reg.t skip s)

/-- Restart at the first clause: `m := |f|`, `p := 1`. -/
def restart : Stmt := seqs [const Reg.p 0, Stmt.load Reg.m Reg.p, add Reg.p Reg.p Reg.one]

/-! ### The count pass -/

/-- Increment the count of the literal `(vr, sr)` in the cell `N + 2 vr + sr`. -/
def cntLit (vr sr : Nat) : Stmt :=
  seqs [add PR.addr Reg.N vr, add PR.addr PR.addr vr, add PR.addr PR.addr sr, Stmt.load PR.x PR.addr,
    add PR.x PR.x Reg.one, store PR.addr PR.x]

def cntBody : Stmt := seqs [readClause, cntLit PR.v0 PR.s0, cntLit PR.v1 PR.s1, ifThird (cntLit PR.v2 PR.s2)]

/-! ### Deleted clauses -/

/-- `del := 1` if the literals in the two slots have the same variable and opposite signs. -/
def tautPair (va sa vb sb : Nat) : Stmt :=
  seqs [sub PR.x va vb, sub PR.y vb va, add PR.x PR.x PR.y, sub PR.y sa sb, sub PR.z sb sa, add PR.y PR.y PR.z,
    ifz PR.x (ifz PR.y skip (const PR.del 1)) skip]

/-- `del := 1` if the variable `vr` occurs three times, all with the same sign: its counts
`x` (negative) and `y` (positive) are `0, 3` or `3, 0`. -/
def pureLit (vr : Nat) : Stmt :=
  seqs [add PR.addr Reg.N vr, add PR.addr PR.addr vr, Stmt.load PR.x PR.addr, add PR.addr PR.addr Reg.one,
    Stmt.load PR.y PR.addr,
    sub PR.z PR.y PR.three, sub PR.u PR.three PR.y, add PR.z PR.z PR.u, ifz PR.x (ifz PR.z (const PR.del 1) skip) skip,
    sub PR.z PR.x PR.three, sub PR.u PR.three PR.x, add PR.z PR.z PR.u, ifz PR.y (ifz PR.z (const PR.del 1) skip) skip]

/-- `del ≠ 0` iff Lemma 10 deletes the clause in the slots. -/
def delCode : Stmt :=
  seqs [const PR.del 0, tautPair PR.v0 PR.s0 PR.v1 PR.s1, pureLit PR.v0, pureLit PR.v1,
    ifThird (seqs [tautPair PR.v0 PR.s0 PR.v2 PR.s2, tautPair PR.v1 PR.s1 PR.v2 PR.s2, pureLit PR.v2])]

/-! ### The kept clauses -/

/-- Count a positive literal `(vr, sr)` in the cell `B + vr`. -/
def kpLit (vr sr : Nat) : Stmt :=
  ifz sr skip (seqs [add PR.addr Reg.B vr, Stmt.load PR.x PR.addr, add PR.x PR.x Reg.one, store PR.addr PR.x])

def keepBody : Stmt :=
  seqs [readClause, delCode,
    ifz PR.del (seqs [kpLit PR.v0 PR.s0, kpLit PR.v1 PR.s1, ifThird (kpLit PR.v2 PR.s2)]) (add PR.r PR.r Reg.one)]

/-! ### The output -/

/-- Write the literal `(vr, sr)`, its sign complemented if its variable has at least two positive
kept occurrences (the count in the cell `B + vr`). -/
def outLit (vr sr : Nat) : Stmt :=
  seqs [write vr, add PR.addr Reg.B vr, Stmt.load PR.x PR.addr, sub PR.y PR.two PR.x,
    ifz PR.y (sub PR.z Reg.one sr) (add PR.z sr Reg.zero), write PR.z]

def outBody : Stmt :=
  seqs [readClause, delCode,
    ifz PR.del (seqs [write Reg.len, outLit PR.v0 PR.s0, outLit PR.v1 PR.s1, ifThird (outLit PR.v2 PR.s2)]) skip]

/-! ### The padding -/

/-- One padding clause `(x_w ∨ x_{w+1})`; `w` advances by two. -/
def padBody : Stmt :=
  seqs [sub PR.r PR.r Reg.one, write PR.two, write PR.w, write Reg.one, add PR.w PR.w Reg.one, write PR.w,
    write Reg.one, add PR.w PR.w Reg.one]

/-! ### The program -/

def polSetup : Stmt := seqs [const PR.two 2, const PR.three 3, const PR.r 0]

def polProgram : Stmt :=
  seq passA (seq polSetup (seq restart (seq (loop Reg.m cntBody) (seq restart (seq (loop Reg.m keepBody)
    (seq restart (seq (loop Reg.m outBody) (seq (add PR.w Reg.n Reg.zero) (loop PR.r padBody)))))))))

end STACS2027.RAM
