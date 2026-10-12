module

public import Runtimes.ZeroCostFormula
public import Runtimes.TwoSatPhase
public import Outerplanar.RAM.BoundedLib
public import Outerplanar.RAM.PairIdsRank
import Mathlib.Tactic

/-!
# Corollary 5 on the RAM: input, registers, layout and program

**Input** (`zeroCostInput g k`): `graphInput g ++ k :: t :: verts g k`, that is `m = |g|`, the
`2m` ends of the edges of `g`, then `k`, the number `t` of enumerated simple `k`-cycles, and
the vertices of the cycles `C_0, …, C_{t-1}` of `cycles g k`, cycle after cycle (`k` each).
The cycles are part of the input because the manuscript's bound `O(k²t + Υ_k)` charges their
enumeration separately (`Υ_k`).

**Registers**: the block `250–299` (globals `gK … gNC` at `250–266`, scratch from `270`); the
2-SAT phase `TwoSat.twoSat` owns `200–249`, outerplanar package's module `PairIds.pairIds` (B2) owns
`100–109` and `120–137`.

**Program** `zeroCostProg`, phase by phase (all loops are counted loops):
1. `stepInit`: read `m`, `k`, `t`; `gV := 2m + 3` (the cycles), `gKT := kt`, `gNV := 2kt`,
   `rFREE := 2m + 3 + kt` (the end of the input);
2. `stepMax`: the largest label `gMX`;
3. `stepDict`: the label dictionary at `gD` (`M + 1` cells, `mem[D + x] = id x + 1`, `M` the
   largest cycle label, `M < labelBound g`) and the number of vertices `gN`;
4. `stepEdges`: for each occurrence `q = ik + j` (cycle `i`, position `j`), its edge
   `{verts[q], verts[ik + next k j]}` (smaller end first) and the ids of its ends, stored as the
   pair `(PU[q], PV[q])`; then outerplanar package's module `PairIds.pairIds` (B2: a counting sort of the
   pairs by first id and a timestamped scan, no `N × N` table) stores the identifier of every
   occurrence (its index among the distinct pairs, in order of first appearance) in `EID[q]`
   and the counts `CNT[id]`;
5. `stepOff`: the offsets `OFF[e] = kt + Σ_{e' < e} (CNT[e'] − 1)` and a zero array `SEEN`;
6. `stepPc`: the literal codes of the path constraints, pushed at `rFREE` from `gCL` on, the
   number of clauses in `gNC`;
7. `stepOcc`: for each occurrence `q`, with `e = EID[q]`, `x = SEEN[e]`, `p = CNT[e]`,
   `o = OFF[e]`: the codes of `occClOf q x p o`, then `SEEN[e] := x + 1`;
8. `callSat`: `tN := 2kt`, `tM := gNC`, `tCL := gCL`, then the 2-SAT phase `TwoSat.twoSat`;
9. `stepRec`: if `tOK = 0`, write `0`; otherwise write `1` and, for each cycle `i`, the first
   position `i₀ < k` such that every edge of `C_i` whose variable is true (`AS[ik + j] = 1`) is
   incident to the vertex at `i₀` (`0` if there is none).

**Layout** (from the end of the input `bD`): the dictionary (`M + 1 ≤ labelBound g` cells), `PU`,
`PV` (`kt` each), the memory of `PairIds.pairIds` from `bPI` (its sort and leaders, then `EID`,
`CNT`), `OFF`, `SEEN` (one cell per distinct edge), the codes from `bCL`, then the 2-SAT phase.
The programs never depend on `cycles g k`: they read `k`, `t` and the vertex list from the
input, so phases 1–4 run unchanged on any list of cycles in this input format.
-/

@[expose] public section

namespace STACS2027.Runtimes.ZeroCost

open STACS2027 STACS2027.RAM

/-! ### Input -/

/-- **The input of Corollary 5's machine**: the graph, `k`, `t`, the vertices of the cycles. -/
def zeroCostInput (g : Graph) (k : ℕ) : List ℕ :=
  graphInput g ++ k :: (cycles g k).length :: verts g k

/-! ### Registers -/

/-- `k`. -/
abbrev gK : ℕ := 250
/-- `t`, the number of cycles. -/
abbrev gT : ℕ := 251
/-- The address of the cycles in the input. -/
abbrev gV : ℕ := 252
/-- `kt`. -/
abbrev gKT : ℕ := 253
/-- `2kt`, the number of variables given to the 2-SAT phase. -/
abbrev gNV : ℕ := 254
/-- The largest label. -/
abbrev gMX : ℕ := 255
/-- The base of the label dictionary. -/
abbrev gD : ℕ := 256
/-- The number of vertices `N`. -/
abbrev gN : ℕ := 257
/-- The base of the first ids `PU` of the pairs of the occurrences. -/
abbrev gPU : ℕ := 258
/-- The base of the second ids `PV` of the pairs of the occurrences. -/
abbrev gPV : ℕ := 259
/-- The base of the edge identifiers of the occurrences. -/
abbrev gEID : ℕ := 260
/-- The base of the counts. -/
abbrev gCNT : ℕ := 261
/-- The number of distinct edges seen. -/
abbrev gNE : ℕ := 262
/-- The base of the offsets. -/
abbrev gOFF : ℕ := 263
/-- The base of the ranks seen so far. -/
abbrev gSEEN : ℕ := 264
/-- The base of the literal codes. -/
abbrev gCL : ℕ := 265
/-- The number of clauses. -/
abbrev gNC : ℕ := 266

/-- Scratch: occurrence counter, address. -/
abbrev sQ : ℕ := 270
/-- Scratch: the cycle counter. -/
abbrev sI : ℕ := 271
/-- Scratch: the position counter. -/
abbrev sJ : ℕ := 272
/-- Scratch. -/
abbrev sX : ℕ := 273
/-- Scratch. -/
abbrev sY : ℕ := 274
/-- Scratch. -/
abbrev sP : ℕ := 275
/-- Scratch. -/
abbrev sU : ℕ := 276
/-- Scratch. -/
abbrev sV : ℕ := 277
/-- Scratch. -/
abbrev sW : ℕ := 278
/-- Scratch. -/
abbrev sZ : ℕ := 279
/-- Scratch. -/
abbrev sC : ℕ := 280
/-- Scratch: accumulator. -/
abbrev sAcc : ℕ := 281
/-- Scratch: `ik`, the first occurrence of the current cycle. -/
abbrev sBase : ℕ := 282
/-- Scratch: an edge identifier. -/
abbrev sE : ℕ := 283
/-- Scratch: a rank. -/
abbrev sR : ℕ := 284
/-- Scratch: an offset. -/
abbrev sO : ℕ := 285
/-- Scratch: a prefix variable. -/
abbrev sS : ℕ := 286
/-- Scratch: a position. -/
abbrev sA : ℕ := 287
/-- Scratch: a position. -/
abbrev sB : ℕ := 288
/-- Scratch: found flag. -/
abbrev sF : ℕ := 289
/-- Scratch: the position found. -/
abbrev sRes : ℕ := 290
/-- Scratch: test flag. -/
abbrev sOk : ℕ := 291

/-! ### Layout -/

section layout

variable (g : Graph) (k : ℕ)

/-- The address of the cycles. -/
def bV : ℕ := 2 * g.length + 3
/-- The label dictionary (`M + 1` cells), at the end of the input. -/
def bD : ℕ := bV g + k * (cycles g k).length
/-- The first ids `PU` of the occurrences (`kt` cells). -/
def bPU : ℕ := bD g k + maxV g k + 1
/-- The second ids `PV` of the occurrences (`kt` cells). -/
def bPV : ℕ := bPU g k + k * (cycles g k).length
/-- The free address at the call of `PairIds.pairIds`. -/
def bPI : ℕ := bPV g k + k * (cycles g k).length
/-- The identifiers of the occurrences (`kt` cells), stored by `PairIds.pairIds` after its sort
and leaders. -/
def bEID : ℕ := PairIds.leadsEnd (nV g k) (k * (cycles g k).length) (bPI g k)
/-- The counts (`kt` cells). -/
def bCNT : ℕ := bEID g k + k * (cycles g k).length
/-- The offsets (one cell per distinct edge). -/
def bOFF : ℕ := bCNT g k + k * (cycles g k).length
/-- The ranks seen (one cell per distinct edge). -/
def bSEEN : ℕ := bOFF g k + (edgesOnCycles g k).length
/-- The literal codes. -/
def bCL : ℕ := bSEEN g k + (edgesOnCycles g k).length

theorem bEID_eq : bEID g k = bPI g k + 4 * nV g k + 2 * (k * (cycles g k).length) + 1 := by
  have := PairIds.leads_eqs (nV g k) (k * (cycles g k).length) (bPI g k)
  unfold bEID; omega

theorem layout_eqs : bV g = 2 * g.length + 3 ∧ bD g k = bV g + k * (cycles g k).length ∧
    bPU g k = bD g k + maxV g k + 1 ∧ bPV g k = bPU g k + k * (cycles g k).length ∧
    bPI g k = bPV g k + k * (cycles g k).length ∧
    bEID g k = bPI g k + 4 * nV g k + 2 * (k * (cycles g k).length) + 1 ∧
    bCNT g k = bEID g k + k * (cycles g k).length ∧
    bOFF g k = bCNT g k + k * (cycles g k).length ∧
    bSEEN g k = bOFF g k + (edgesOnCycles g k).length ∧
    bCL g k = bSEEN g k + (edgesOnCycles g k).length :=
  ⟨rfl, rfl, rfl, rfl, rfl, bEID_eq g k, rfl, rfl, rfl, rfl⟩

/-- The end of the memory of `PairIds.pairIds` is `bOFF`. -/
theorem idsEnd_eq : PairIds.idsEnd (nV g k) (k * (cycles g k).length) (bPI g k) = bOFF g k := rfl

theorem length_zeroCostInput : (zeroCostInput g k).length = bD g k := by
  simp [zeroCostInput, bD, bV, length_verts]; ring

theorem nE_le : (edgesOnCycles g k).length ≤ k * (cycles g k).length := by
  have := length_eprefix_le (g := g) (k := k) (k * (cycles g k).length)
  rwa [eprefix_full] at this

/-- The regions of phases 1–5 fit below `S ≥ bCL` (one inequality per region). -/
theorem fits {S : ℕ} (hS : bCL g k ≤ S) :
    bD g k ≤ S ∧ bD g k + (maxV g k + 1) ≤ S ∧ bPU g k + k * (cycles g k).length ≤ S ∧
      bPV g k + k * (cycles g k).length ≤ S ∧ bEID g k + k * (cycles g k).length ≤ S ∧
      bCNT g k + k * (cycles g k).length ≤ S ∧ bOFF g k + (edgesOnCycles g k).length ≤ S ∧
      bSEEN g k + (edgesOnCycles g k).length ≤ S := by
  have := layout_eqs g k; omega

end layout

/-! ### Pushing a code -/

/-- `mem[rFREE] := reg r; rFREE += 1`. -/
def push (r : ℕ) : Stmt := .seq (.store rFREE r) (inc rFREE)

theorem run_push (r : ℕ) (c : Config) :
    run (push r) c = ((c.setMem (c.reg rFREE) (c.reg r)).setReg rT 1).setReg rFREE (c.reg rFREE + 1) := by
  simp [push, run_inc]

theorem ZeroFrom.upd_at {m : ℕ → ℕ} {F : ℕ} (h : ZeroFrom m F) (v : ℕ) : ZeroFrom (upd m F v) (F + 1) :=
  fun a ha => by
    have hne : a ≠ F := by omega
    simp only [upd_apply, hne, ↓reduceIte]; exact h a (by omega)

/-- Reassociating a sequence. -/
theorem HT.assoc {a b u : Stmt} {P Q : Config → Prop} {n : ℕ} (h : HT (.seq (.seq a b) u) P Q n) :
    HT (.seq a (.seq b u)) P Q n := by
  intro c hc
  obtain ⟨c', t, he, hq, ht⟩ := h c hc
  cases he with
  | seq h₁ h₂ =>
    cases h₁ with
    | seq h₁₁ h₁₂ => exact ⟨c', _, Exec.seq h₁₁ (Exec.seq h₁₂ h₂), hq, by omega⟩

/-! ### The program -/

/-- Phase 1a: `sX := m`; `gV := 2m + 3`; `gK := mem[2m + 1]`; `gT := mem[2m + 2]`. -/
def initRead : Stmt :=
  .seq (.load sX 0) (.seq (.add sX sX sX) (.seq (addc gV sX 3) (.seq (subc sY gV 2)
    (.seq (.load gK sY) (.seq (subc sY gV 1) (.load gT sY))))))

/-- Phase 1c: `rFREE := gV + kt`, `gNV := 2kt`. -/
def initFin : Stmt := .seq (.add rFREE gV gKT) (.add gNV gKT gKT)

/-- Phase 1. -/
def stepInit : Stmt := .seq initRead (.seq (mul gKT gK gT sQ) initFin)

/-- One step of the largest-label scan. -/
def maxBody : Stmt := .seq (ld sX gV sQ) (ifLt gMX sX (mov gMX sX) .skip)

/-- Phase 2: the largest label. -/
def stepMax : Stmt := .seq (.const gMX 0) (forUp sQ gKT maxBody)

/-- The dictionary allocation: `gD := rFREE`, `rFREE += M + 1`, `gN := 0`. -/
def dictInit : Stmt := .seq (mov gD rFREE) (.seq (.add rFREE rFREE gMX) (.seq (inc rFREE) (.const gN 0)))

/-- One step of the dictionary pass: a new label gets the next id. -/
def dictBody : Stmt :=
  .seq (ld sX gV sQ) (.seq (.add sY gD sX) (.seq (.load sZ sY)
    (.ifz sZ (.seq (inc gN) (.store sY gN)) .skip)))

/-- Phase 3: the dictionary. -/
def stepDict : Stmt := .seq dictInit (forUp sQ gKT dictBody)

/-- The position of the second end of the edge at position `sJ` of the current cycle:
`sQ + 1` if `sJ + 1 < k`, else `sBase`. -/
def nextPos : Stmt := .seq (addc sP sJ 1) (ifLt sP gK (addc sP sQ 1) (mov sP sBase))

/-- `sQ := sBase + sJ`; `sX := verts[sQ]`. -/
def edgeA : Stmt := .seq (.add sQ sBase sJ) (ld sX gV sQ)

/-- Order `sX ≤ sY`. -/
def minmax : Stmt := ifLt sY sX (swap sX sY) .skip

/-- The ids of the ends in `sU`, `sV` (ids are dictionary entries `- 1`). -/
def edgeIds : Stmt := .seq (ld sU gD sX) (.seq (dec sU) (.seq (ld sV gD sY) (dec sV)))

/-- Reading occurrence `q = sBase + sJ`: its ends (ordered) and their ids `sU`, `sV`. -/
def edgeRead : Stmt := .seq edgeA (.seq nextPos (.seq (ld sY gV sP) (.seq minmax edgeIds)))

/-- `PU[q] := sU`, `PV[q] := sV`. -/
def edgePut : Stmt := .seq (st gPU sQ sU) (st gPV sQ sV)

/-- One occurrence of the id pass. -/
def edgeBody : Stmt := .seq edgeRead edgePut

/-- One cycle of the id pass. -/
def edgeRow : Stmt := .seq (forUp sJ gK edgeBody) (.add sBase sBase gK)

/-- The arguments of `PairIds.pairIds`: the pairs at `PU`, `PV`, `kt` of them, ids below `N`. -/
def idsArgs : Stmt :=
  .seq (mov PairIds.rPU gPU) (.seq (mov PairIds.rPV gPV) (.seq (mov PairIds.rPL gKT)
    (mov PairIds.rPN gN)))

/-- The results of `PairIds.pairIds`: `gEID`, `gCNT`, `gNE`. -/
def idsBack : Stmt := .seq (mov gEID PairIds.rID) (.seq (mov gCNT PairIds.rCT) (mov gNE PairIds.rNE))

/-- Phase 4: the id pairs of the occurrences, then their identifiers and counts (B2). -/
def stepEdges : Stmt :=
  .seq (alloc gPU gKT) (.seq (alloc gPV gKT) (.seq (.const sBase 0) (.seq (forUp sI gT edgeRow)
    (.seq idsArgs (.seq PairIds.pairIds idsBack)))))

/-- One offset: `OFF[e] := acc`, `acc += CNT[e] − 1`. -/
def offBody : Stmt := .seq (st gOFF sE sAcc) (.seq (ld sC gCNT sE) (.seq (.add sAcc sAcc sC) (dec sAcc)))

/-- Phase 5: the offsets and the zero array `SEEN`. -/
def stepOff : Stmt :=
  .seq (alloc gOFF gNE) (.seq (alloc gSEEN gNE) (.seq (mov sAcc gKT) (forUp sE gNE offBody)))

/-- The path constraint `¬b_{base + a} ∨ ¬b_{base + b}`: codes `2(base + a) + 1`, `2(base + b) + 1`. -/
def pcEmit : Stmt :=
  .seq (.add sU sBase sA) (.seq (.add sU sU sU) (.seq (inc sU) (.seq (push sU)
    (.seq (.add sV sBase sB) (.seq (.add sV sV sV) (.seq (inc sV) (.seq (push sV) (inc gNC))))))))

/-- The pair of positions `a, b`: a constraint if `a + 1 < b` and not `a = 0, b + 1 = k`. -/
def pcBody : Stmt :=
  .seq (addc sX sA 1) (ifLt sX sB (.seq (addc sY sB 1) (.ifz sA (ifEq sY gK .skip pcEmit) pcEmit)) .skip)

/-- All pairs with first position `a`. -/
def pcRowA : Stmt := forUp sB gK pcBody

/-- One cycle of the path constraints. -/
def pcRow : Stmt := .seq (forUp sA gK pcRowA) (.add sBase sBase gK)

/-- Phase 6: the path constraints. -/
def stepPc : Stmt := .seq (mov gCL rFREE) (.seq (.const gNC 0) (.seq (.const sBase 0) (forUp sI gT pcRow)))

/-- Reading occurrence `sQ`: `e`, its rank `x`, its count `p`, its offset `o`, `s = o + x`,
`sX = x + 1`. -/
def occRead : Stmt :=
  .seq (ld sE gEID sQ) (.seq (ld sR gSEEN sE) (.seq (ld sP gCNT sE) (.seq (ld sO gOFF sE)
    (.seq (.add sS sO sR) (addc sX sR 1)))))

/-- `b_q ∨ s_x`: codes `2q`, `2s`. -/
def emit1 : Stmt := .seq (.add sU sQ sQ) (.seq (push sU) (.seq (.add sV sS sS) (.seq (push sV) (inc gNC))))

/-- `¬s_{x-1} ∨ s_x`: codes `2(s − 1) + 1`, `2s`. -/
def emit2 : Stmt :=
  .seq (subc sU sS 1) (.seq (.add sU sU sU) (.seq (inc sU) (.seq (push sU) (.seq (.add sV sS sS)
    (.seq (push sV) (inc gNC))))))

/-- `b_q ∨ ¬s_{x-1}`: codes `2q`, `2(s − 1) + 1`. -/
def emit3 : Stmt :=
  .seq (.add sU sQ sQ) (.seq (push sU) (.seq (subc sV sS 1) (.seq (.add sV sV sV) (.seq (inc sV)
    (.seq (push sV) (inc gNC))))))

/-- The three conditional clauses of an occurrence. -/
def occEmit : Stmt :=
  .seq (ifLt sX sP emit1 .skip) (.seq (.ifz sR .skip (ifLt sX sP emit2 .skip)) (.ifz sR .skip emit3))

/-- One occurrence of the prefix-clause pass. -/
def occBody : Stmt := .seq occRead (.seq occEmit (st gSEEN sE sX))

/-- Phase 7: the prefix clauses. -/
def stepOcc : Stmt := forUp sQ gKT occBody

/-- Phase 8: the 2-SAT call. -/
def callSat : Stmt := .seq (mov TwoSat.tN gNV) (.seq (mov TwoSat.tM gNC) (.seq (mov TwoSat.tCL gCL) TwoSat.twoSat))

/-- The test of a true variable: `sOk := 0` unless one end of the edge at position `sJ` is `sC`. -/
def recCheck : Stmt :=
  .seq (ld sX gV sQ) (.seq nextPos (.seq (ld sY gV sP) (ifEq sX sC .skip (ifEq sY sC .skip (.const sOk 0)))))

/-- Position `sJ` of the test. -/
def recBody : Stmt := .seq (.add sQ sBase sJ) (.seq (ld sZ TwoSat.tAS sQ) (.ifz sZ .skip recCheck))

/-- After the test of position `sA`: record it if it is the first that passes. -/
def recUpd : Stmt := .ifz sF (.ifz sOk .skip (.seq (mov sRes sA) (.const sF 1))) .skip

/-- The test of position `sA` of the current cycle. -/
def recA : Stmt :=
  .seq (.const sOk 1) (.seq (.add sQ sBase sA) (.seq (ld sC gV sQ) (.seq (forUp sJ gK recBody) recUpd)))

/-- One cycle of the recovery: the first position passing the test, written. -/
def recRow : Stmt :=
  .seq (.const sF 0) (.seq (.const sRes 0) (.seq (forUp sA gK recA) (.seq (.write sRes) (.add sBase sBase gK))))

/-- Phase 9: the answer. -/
def stepRec : Stmt :=
  .ifz TwoSat.tOK (.seq (.const sX 0) (.write sX))
    (.seq (.const sX 1) (.seq (.write sX) (.seq (.const sBase 0) (forUp sI gT recRow))))

/-- **The machine of Corollary 5.** -/
def zeroCostProg : Stmt :=
  .seq stepInit (.seq stepMax (.seq stepDict (.seq stepEdges (.seq stepOff
    (.seq stepPc (.seq stepOcc (.seq callSat stepRec)))))))

end STACS2027.Runtimes.ZeroCost
