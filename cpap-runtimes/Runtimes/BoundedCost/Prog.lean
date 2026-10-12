module

public import Runtimes.BoundedCost.Spec
public import Runtimes.BoundedCost.Solver
public import Runtimes.Sort.Front
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: registers and programs

**Input** (`boundedCostInput g k Ψ`): the input of Corollary 5 (`m = |g|`, the `2m` ends of the edges
of `g`, `k`, the number `t` of enumerated simple `k`-cycles, and their vertices, cycle after
cycle), then `Ψ`.

**Registers**: Corollary 5's block `250–291` (globals `gK … gNC`, scratch `sQ … sOk`), and
`gPSI = 292` (`Ψ`), `gPS1 = 293` (the number of copies of the path constraints), `294–297`
(the reading of the solver's answer). The linear 2-SAT phase owns `200–249`, the sorting front
end `Sort.front` the blocks `100–137`, `800–816` and `830`.

**The formula** `form5` (all loops are counted loops, no memory is indexed by a vertex label):
1. `stepInit5`: Corollary 5's `stepInit` (read `m`, `k`, `t`; `gV`, `gKT = kt`, `gNV = 2kt`,
   `rFREE` = the end of the cycles, the address of `Ψ`), then `readPsi`: `gPSI := Ψ`, the cell of
   `Ψ` is cleared (free memory), `gPS1 := Ψ + 1`, or `0` if `t = 0` (then there is no path
   constraint, and no copy costs a step);
2. `Sort.front` (`Runtimes/Sort/Front.lean`): the edge identifiers `EID[q]` of the occurrences by
   a stable merge sort of the labels and outerplanar package's `PairIds` module;
3. `allocSeen`: a zero table `SEEN` with one cell per distinct edge (the mark table);
4. `stepPcs`: `gPS1` times Corollary 5's generation of the path constraints (`pcRow` for each
   cycle), the codes pushed at `gCL`;
5. `stepOv`: for each pair `i < i'` of cycles: mark the edges of `C_{i'}` with their variable
   `+ 1` (`markBody`), scan the edges of `C_i` and emit `b_{ik+j} ∨ b_{v-1}` when the mark `v` of
   the edge is nonzero (`scanBody`, `emitOv`), clear the marks (`clearBody`).

**The programs**:
* `build5 = form5 ; stepOut`: writes the solver's input `a2In (shiftF Γ') Ψ` — `Ψ`, `|Γ'|`, and
  the codes of `Γ'` plus `2` (the variables renamed `v ↦ v + 1`, so that the list of true
  variables of the answer ends at the first zero cell);
* `extract5 = stepInit ; readAns ; stepRec`, on the input followed by the solver's answer: the
  flag `ok = z₀`; if `ok = 1`, the true variables `T` (from position `2 + |D|` of the answer,
  until a zero, at most `kt` of them) are written as bits into a zero table `AS` placed after the
  answer (`AS[y − 1] := 1` for `y ∈ T`), and Corollary 5's recovery `stepRec` writes `[0]` or
  `1` and the omitted positions;
* `zero5 = form5 ; callSat5 ; stepRec` (`Ψ = 0`): the linear 2-SAT phase on `Γ' = Γ_∅`, then the
  recovery.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost

/-- `Ψ`. -/
abbrev gPSI : ℕ := 292
/-- The number of copies of the path constraints (`Ψ + 1`, or `0` without cycles). -/
abbrev gPS1 : ℕ := 293
/-- The reading pointer in the solver's answer. -/
abbrev eP : ℕ := 294
/-- The end flag of the list of true variables. -/
abbrev eD : ℕ := 295
/-- The constant `1`. -/
abbrev eOne : ℕ := 296
/-- A value read. -/
abbrev eY : ℕ := 297

/-! ### The formula -/

/-- Reading `Ψ` at the end of the input (`rFREE`), freeing its cell, and the number of copies. -/
def readPsi : Stmt :=
  .seq (.load gPSI rFREE) (.seq (.const sX 0) (.seq (.store rFREE sX) (.seq (addc gPS1 gPSI 1)
    (.ifz gT (.const gPS1 0) .skip))))

/-- Phase 1. -/
def stepInit5 : Stmt := .seq stepInit readPsi

/-- Phase 3: the mark table (`NE` zero cells). -/
def allocSeen : Stmt := .seq (mov gSEEN rFREE) (.add rFREE rFREE ZeroCost.gNE)

/-- One copy of the path constraints. -/
def pcCopy : Stmt := .seq (.const sBase 0) (forUp sI gT pcRow)

/-- Phase 4: `gPS1` copies of the path constraints. -/
def stepPcs : Stmt := .seq (mov gCL rFREE) (.seq (.const gNC 0) (forUp sR gPS1 pcCopy))

/-- Marking position `j = sJ` of `C_{i'}` (`sW = i'k`): `SEEN[EID[i'k + j]] := i'k + j + 1`. -/
def markBody : Stmt :=
  .seq (.add sP sW sJ) (.seq (ld sE gEID sP) (.seq (addc sZ sP 1) (st gSEEN sE sZ)))

/-- The overlap clause `b_q ∨ b_{v-1}` (`q = sP`, `v = sZ`): codes `2q`, `2(v − 1)`. -/
def emitOv : Stmt :=
  .seq (.add sU sP sP) (.seq (push sU) (.seq (subc sV sZ 1) (.seq (.add sV sV sV)
    (.seq (push sV) (inc gNC)))))

/-- Scanning position `j = sJ` of `C_i` (`sBase = ik`): emit a clause if the edge is marked. -/
def scanBody : Stmt :=
  .seq (.add sP sBase sJ) (.seq (ld sE gEID sP) (.seq (ld sZ gSEEN sE) (.ifz sZ .skip emitOv)))

/-- Clearing position `j = sJ` of `C_{i'}`. -/
def clearBody : Stmt :=
  .seq (.add sP sW sJ) (.seq (ld sE gEID sP) (.seq (.const sZ 0) (st gSEEN sE sZ)))

/-- The overlap clauses of the pair `(C_i, C_{i'})`. -/
def ovPair : Stmt := .seq (forUp sJ gK markBody) (.seq (forUp sJ gK scanBody) (forUp sJ gK clearBody))

/-- The pair `(i, i') = (sI, sA)`, if `i < i'`; then `sW += k`. -/
def ovPairT : Stmt := .seq (ifLt sI sA ovPair .skip) (.add sW sW gK)

/-- The overlap clauses of `C_i` with the later cycles. -/
def ovRow : Stmt := .seq (.const sW 0) (.seq (forUp sA gT ovPairT) (.add sBase sBase gK))

/-- Phase 5: the overlap clauses. -/
def stepOv : Stmt := .seq (.const sBase 0) (forUp sI gT ovRow)

/-- **The formula `Γ'` in memory.** -/
def form5 : Stmt :=
  .seq stepInit5 (.seq Sort.front (.seq allocSeen (.seq stepPcs stepOv)))

/-! ### The construction -/

/-- Writing code `sQ`, plus `2`. -/
def outBody : Stmt := .seq (ld sY gCL sQ) (.seq (addc sY sY 2) (.write sY))

/-- The output phase: `Ψ`, `|Γ'|`, the codes plus `2`. -/
def stepOut : Stmt :=
  .seq (.write gPSI) (.seq (.write gNC) (.seq (.add sX gNC gNC) (forUp sQ sX outBody)))

/-- **The construction** of Theorem 4: writes `a2In (shiftF Γ') Ψ`. -/
def build5 : Stmt := .seq form5 stepOut

/-! ### The extraction -/

/-- Entry `sI` of the list of true variables, until the first zero: `AS[y − 1] := 1`. -/
def readBody : Stmt :=
  .ifz eD (.seq (ld eY eP sI) (.ifz eY (.const eD 1) (.seq (dec eY) (st TwoSat.tAS eY eOne))))
    .skip

/-- Before the list of true variables: `|D|`, the start `P` of `T`, the table at `P + kt`. -/
def readPre : Stmt :=
  .seq (inc eP) (.seq (.load eY eP) (.seq (.add eP eP eY) (.seq (inc eP)
    (.seq (.add TwoSat.tAS eP gKT) (.seq (.const eD 0) (.const eOne 1))))))

/-- The list of true variables, after the flag. -/
def readT : Stmt := .seq readPre (forUp sI gKT readBody)

/-- Reading the solver's answer, which starts at `rFREE + 1` (after `Ψ`). -/
def readAns : Stmt :=
  .seq (.seq (addc eP rFREE 1) (.load TwoSat.tOK eP)) (.ifz TwoSat.tOK .skip readT)

/-- **The extraction** of Theorem 4, on the input followed by the solver's answer. -/
def extract5 : Stmt := .seq stepInit (.seq readAns stepRec)

/-! ### `Ψ = 0` -/

/-- The arguments of the 2-SAT phase: `n = kt`, `m = gNC`, the codes at `gCL`. -/
def satMoves : Stmt := .seq (mov TwoSat.tN gKT) (.seq (mov TwoSat.tM gNC) (mov TwoSat.tCL gCL))

/-- The linear 2-SAT phase on the formula. -/
def callSat5 : Stmt := .seq satMoves TwoSat.twoSat

/-- **The machine for `Ψ = 0`**: the formula, 2-SAT, the recovery. -/
def zero5 : Stmt := .seq form5 (.seq callSat5 stepRec)

end STACS2027.Runtimes.BoundedCost
