module

public import Outerplanar.RAM.PolyIface
public import Outerplanar.RAM.Lib
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver (the tables): registers and program

Phase P3 fills the tables `table s α` and `argTab s α` of every segment `s` of `segOrder`
(children before parents). The program, from the bottom up:

* `inCyc`: is the edge `(rEX, rEY)` an edge of the pool cycle at `rCB`?
  (`k` consecutive pairs `(c[j], c[j + 1 mod k])`, test `chk`);
* `isSel`: is it a selected edge of the cycle `rI` with omitted index `rV`? (the cycle base
  `POOL + i * k` by `mul`, the omitted vertex, `inCyc`);
* `loadCost`: adds `pairCount (loadAt s vals e)` to `rTOT` (a scan of the relevant cycles,
  adding the count so far at every selected one);
* `childCost`: adds `table w (childIdx s w vals)` to `rTOT` for the child `w = (rX, rY)`: its
  index from the slot id `FSID[fOff s + q]` of the slot `q`, its boundary cycles from `gBIDX`, each
  digit found by a scan of the relevant cycles of `s` (`scanBody`), the code by
  `acc += pw * d; pw *= k` (`encBody`);
* `total`: the cost of a configuration: the load cost of `s`, then the slots of the face
  (`slotBody`: a side adds its load cost, a child its table entry);
* `odo`: the odometer on the digits at `rOB` (`rOL` digits);
* `betaBody`/`alphaBody`: the minimization over `β` (keeping the first strict minimum) and
  the loop over `α` storing `TAB`, `ARG`;
* `segBody`: the data of the segment `j`, the powers `k ^ nb`, `k ^ nc` (`pow`), the
  relevant cycles `REL` and the digits `VAL` (fresh), then the `α` loop;
* `prep k`: `k`, `toffInit` (the table offsets and the allocation of `TAB`, `ARG`); then the
  loop over the segments `segLoop`: `poly3 k`.
-/

@[expose] public section

namespace STACS2027.RAM.P3

/-! ### Registers -/

/-- The cycle length `k`. -/
abbrev rK : ℕ := 84
/-- The segment index `j`. -/
abbrev rJ : ℕ := 86
/-- Base of the relevant cycles of the current segment. -/
abbrev rREL : ℕ := 87
/-- Base of the digits of the current configuration. -/
abbrev rVAL : ℕ := 88
/-- `|bnd s|`. -/
abbrev rNB : ℕ := 89
/-- `|topIdx s|`. -/
abbrev rNC : ℕ := 90
/-- `|rel s|`. -/
abbrev rNR : ℕ := 91
/-- `k ^ |bnd s|`. -/
abbrev rPB : ℕ := 92
/-- `k ^ |topIdx s|`. -/
abbrev rPC : ℕ := 93
/-- The configuration `α`. -/
abbrev rA : ℕ := 94
/-- The configuration `β`. -/
abbrev rB : ℕ := 95
/-- The best total so far. -/
abbrev rBEST : ℕ := 96
/-- The best `β` so far. -/
abbrev rARGB : ℕ := 97
/-- The table offset of the current segment. -/
abbrev rTO : ℕ := 98
/-- The face offset of the current segment. -/
abbrev rFO : ℕ := 99
/-- The number of slots of the current face. -/
abbrev rFL : ℕ := 100
/-- The first end of the current segment. -/
abbrev rSA : ℕ := 101
/-- The second end of the current segment. -/
abbrev rSB : ℕ := 102
/-- Base of the digits of `β`. -/
abbrev rVB : ℕ := 103
/-- The total of the current configuration. -/
abbrev rTOT : ℕ := 104
/-- The slot counter. -/
abbrev rQ : ℕ := 105
/-- The first vertex of the slot. -/
abbrev rX : ℕ := 106
/-- The second vertex of the slot. -/
abbrev rY : ℕ := 107
/-- The first end of the edge whose load is counted. -/
abbrev rEX : ℕ := 108
/-- The second end of the edge whose load is counted. -/
abbrev rEY : ℕ := 109
/-- The load counted so far. -/
abbrev rCNT : ℕ := 110
/-- The counter over the relevant cycles. -/
abbrev rR : ℕ := 111
/-- The pool index of a relevant cycle. -/
abbrev rI : ℕ := 112
/-- Its omitted index. -/
abbrev rV : ℕ := 113
/-- The selection flag. -/
abbrev rSEL : ℕ := 114
/-- The base of the cycle in the pool. -/
abbrev rCB : ℕ := 115
/-- The omitted vertex. -/
abbrev rW : ℕ := 116
/-- The counter over the edges of a cycle. -/
abbrev rJJ : ℕ := 117
/-- The first vertex of an edge of the cycle. -/
abbrev rPA : ℕ := 118
/-- The second vertex of an edge of the cycle. -/
abbrev rPN : ℕ := 119
/-- Product. -/
abbrev rM : ℕ := 120
/-- Counter of the multiplications. -/
abbrev rMK : ℕ := 121
/-- The index of the child segment. -/
abbrev rWI : ℕ := 122
/-- The boundary offset of the child. -/
abbrev rWB : ℕ := 123
/-- The number of boundary cycles of the child. -/
abbrev rBL : ℕ := 124
/-- The counter over the boundary cycles of the child. -/
abbrev rT2 : ℕ := 125
/-- The code of the child configuration. -/
abbrev rACC : ℕ := 126
/-- The power of `k`. -/
abbrev rPW : ℕ := 127
/-- A digit. -/
abbrev rDI : ℕ := 128
/-- The pool index searched for. -/
abbrev rIX : ℕ := 129
/-- The counter of the scan. -/
abbrev rR2 : ℕ := 130
/-- Temporary. -/
abbrev rU : ℕ := 131
/-- Odometer: base of the digits. -/
abbrev rOB : ℕ := 132
/-- Odometer: number of digits. -/
abbrev rOL : ℕ := 133
/-- Odometer: counter. -/
abbrev rOT : ℕ := 134
/-- Odometer: carry. -/
abbrev rCY : ℕ := 135
/-- Odometer: digit. -/
abbrev rOD : ℕ := 136
/-- The boundary offset of the current segment. -/
abbrev rSBO : ℕ := 137
/-- The first top cycle of the current segment. -/
abbrev rTS : ℕ := 138
/-- Power: the exponent. -/
abbrev rPE : ℕ := 139
/-- Power: the counter. -/
abbrev rPT : ℕ := 140
/-- Power: the result. -/
abbrev rPR : ℕ := 141
/-- Temporary of the first pass. -/
abbrev rN1 : ℕ := 142
/-- Counter of the first pass. -/
abbrev rX2 : ℕ := 143
/-- Accumulator of the first pass. -/
abbrev rACC2 : ℕ := 144

/-! ### The selected edges -/

/-- `rSEL := 1` if `{rPA, rPN} = {rEX, rEY}` (for `rEX < rEY`). -/
def chk : Stmt :=
  ifEq rPA rEX (ifEq rPN rEY (.const rSEL 1) .skip)
    (ifEq rPA rEY (ifEq rPN rEX (.const rSEL 1) .skip) .skip)

/-- The edge `(c[jj], c[jj + 1 mod k])` of the cycle at `rCB`. -/
def icBody : Stmt :=
  .seq (ld rPA rCB rJJ) (.seq (addc rU rJJ 1) (.seq (ifEq rU rK (.const rU 0) .skip)
    (.seq (ld rPN rCB rU) chk)))

/-- Is `(rEX, rEY)` an edge of the cycle at `rCB`? (`rSEL` set to `1` if so.) -/
def inCyc : Stmt := forUp rJJ rK icBody

/-- The multiplication of the cycle base. -/
def selPre : Stmt :=
  .seq (mul rM rI rK rMK) (.seq (.add rCB gPOOL rM) (.seq (ld rW rCB rV) (.const rSEL 0)))

/-- Clear the flag if the omitted vertex is an end of the edge. -/
def selPost : Stmt := .seq (ifEq rW rEX (.const rSEL 0) .skip) (ifEq rW rEY (.const rSEL 0) .skip)

/-- Is `(rEX, rEY)` selected in the cycle `rI` with omitted index `rV`? -/
def isSel : Stmt := .seq selPre (.seq inCyc selPost)

/-- Count the cycle `REL[r]` with the digit `VAL[r]`. -/
def lcBody : Stmt :=
  .seq (ld rI rREL rR) (.seq (ld rV rVAL rR) (.seq isSel
    (.ifz rSEL .skip (.seq (.add rTOT rTOT rCNT) (inc rCNT)))))

/-- Add `pairCount` of the load of `(rEX, rEY)` to `rTOT`. -/
def loadCost : Stmt := .seq (.const rCNT 0) (forUp rR rNR lcBody)

/-! ### The children -/

/-- The scan: `rDI := VAL[r]` if `REL[r] = rIX`. -/
def scanBody : Stmt := .seq (ld rU rREL rR2) (ifEq rU rIX (ld rDI rVAL rR2) .skip)

/-- Read the boundary cycle `t` of the child. -/
def encRd : Stmt := .seq (.add rU rWB rT2) (.seq (ld rIX gBIDX rU) (.const rDI 0))

/-- One digit of the child configuration. -/
def encBody : Stmt :=
  .seq encRd (.seq (forUp rR2 rNR scanBody)
    (.seq (mul rM rPW rDI rMK) (.seq (.add rACC rACC rM) (.seq (mul rM rPW rK rMK) (mov rPW rM)))))

/-- The child `(rX, rY)` of the slot `rQ`: its index (the slot id `FSID[rFO + rQ]` minus one),
its boundary cycles. -/
def ccPre : Stmt :=
  .seq (.add rU rFO rQ) (.seq (ld rWI gFSID rU) (.seq (dec rWI)
    (.seq (ld rWB gBOFF rWI) (.seq (addc rU rWI 1) (.seq (ld rBL gBOFF rU) (.seq (.sub rBL rBL rWB)
      (.seq (.const rACC 0) (.const rPW 1))))))))

/-- Add the table entry of the child. -/
def ccPost : Stmt :=
  .seq (ld rU gTOFF rWI) (.seq (.add rU rU rACC) (.seq (ld rU gTAB rU) (.add rTOT rTOT rU)))

/-- Add `table w (childIdx s w vals)` to `rTOT` for the child `w = (rX, rY)`. -/
def childCost : Stmt := .seq ccPre (.seq (forUp rT2 rBL encBody) ccPost)

/-! ### A configuration -/

/-- Read the slot `q`. -/
def slotRd : Stmt :=
  .seq (.add rU rFO rQ) (.seq (ld rX gFV rU) (.seq (inc rU) (.seq (ld rY gFV rU) (addc rU rX 1))))

/-- A side. -/
def sideCost : Stmt := .seq (.seq (mov rEX rX) (mov rEY rY)) loadCost

/-- One slot of the face. -/
def slotBody : Stmt := .seq slotRd (ifEq rY rU sideCost childCost)

/-- Start the total with the segment itself. -/
def totInit : Stmt := .seq (.const rTOT 0) (.seq (mov rEX rSA) (mov rEY rSB))

/-- The total of the configuration in `VAL`. -/
def total : Stmt := .seq totInit (.seq loadCost (forUp rQ rFL slotBody))

/-! ### The odometer and the powers -/

/-- One digit of the odometer. -/
def odoBody : Stmt :=
  .ifz rCY .skip (.seq (ld rOD rOB rOT) (.seq (inc rOD)
    (.seq (ifEq rOD rK (.const rOD 0) (.const rCY 0)) (st rOB rOT rOD))))

/-- The odometer: add one to the `rOL` digits at `rOB`. -/
def odo : Stmt := .seq (.const rCY 1) (forUp rOT rOL odoBody)

/-- One multiplication by `k`. -/
def powBody : Stmt := .seq (mul rM rPR rK rMK) (mov rPR rM)

/-- `rPR := k ^ reg rPE`. -/
def pow : Stmt := .seq (.const rPR 1) (forUp rPT rPE powBody)

/-! ### The minimization -/

/-- Keep the current configuration. -/
def keep : Stmt := .seq (mov rBEST rTOT) (mov rARGB rB)

/-- Keep the current configuration if it is the first or strictly better. -/
def keepB : Stmt := .ifz rB keep (ifLt rTOT rBEST keep .skip)

/-- The arguments of the odometer on the digits of `β`. -/
def bOdoArgs : Stmt := .seq (mov rOB rVB) (mov rOL rNC)

/-- One `β`. -/
def betaBody : Stmt := .seq total (.seq keepB (.seq bOdoArgs odo))

/-- Store the entry of `α`. -/
def store : Stmt := .seq (.add rU rTO rA) (.seq (st gTAB rU rBEST) (st gARG rU rARGB))

/-- Start the minimization. -/
def aInit : Stmt := .seq (.const rBEST 0) (.const rARGB 0)

/-- The arguments of the odometer on the digits of `α`. -/
def aOdoArgs : Stmt := .seq (mov rOB rVAL) (mov rOL rNB)

/-- One `α`. -/
def alphaBody : Stmt := .seq aInit (.seq (forUp rB rPC betaBody) (.seq store (.seq aOdoArgs odo)))

/-! ### A segment -/

/-- Read the data of the segment `j`. -/
def segRd : Stmt :=
  .seq (ld rSA gSA rJ) (.seq (ld rSB gSB rJ) (.seq (ld rFO gFOFF rJ) (.seq (addc rU rJ 1)
    (.seq (ld rFL gFOFF rU) (.seq (.sub rFL rFL rFO) (.seq (dec rFL)
    (.seq (ld rSBO gBOFF rJ) (.seq (ld rNB gBOFF rU) (.seq (.sub rNB rNB rSBO)
    (.seq (ld rTS gTST rJ) (.seq (ld rNC gTST rU) (.seq (.sub rNC rNC rTS)
    (.seq (.add rNR rNB rNC) (ld rTO gTOFF rJ))))))))))))))

/-- `dst := k ^ reg src`. -/
def powTo (dst src : ℕ) : Stmt := .seq (mov rPE src) (.seq pow (mov dst rPR))

/-- The powers `k ^ nb`, `k ^ nc`. -/
def segPow : Stmt := .seq (powTo rPB rNB) (powTo rPC rNC)

/-- One relevant cycle: `REL[r] := BIDX[bo + r]` or `TS + r - nb`. -/
def relBody : Stmt :=
  ifLt rR rNB (.seq (.add rU rSBO rR) (.seq (ld rU gBIDX rU) (st rREL rR rU)))
    (.seq (.add rU rTS rR) (.seq (.sub rU rU rNB) (st rREL rR rU)))

/-- Allocate the digits. -/
def valAlloc : Stmt := .seq (alloc rVAL rNR) (.add rVB rVAL rNB)

/-- The relevant cycles and the digits. -/
def segRel : Stmt := .seq (alloc rREL rNR) (.seq (forUp rR rNR relBody) valAlloc)

/-- One segment. -/
def segBody : Stmt := .seq segRd (.seq segPow (.seq segRel (forUp rA rPB alphaBody)))

/-! ### The first pass and the phase -/

/-- Read the number of boundary cycles of the segment `rX2`. -/
def toffRd : Stmt :=
  .seq (ld rU gBOFF rX2) (.seq (addc rN1 rX2 1) (.seq (ld rPE gBOFF rN1) (.sub rPE rPE rU)))

/-- Store the next table offset. -/
def toffSt : Stmt := .seq (.add rACC2 rACC2 rPR) (st gTOFF rN1 rACC2)

/-- One table offset. -/
def toffBody : Stmt := .seq toffRd (.seq pow toffSt)

/-- Allocate the table offsets. -/
def toffAlloc : Stmt := .seq (addc rN1 gNS 1) (.seq (alloc gTOFF rN1) (.const rACC2 0))

/-- Allocate the tables. -/
def tabAlloc : Stmt := .seq (alloc gTAB rACC2) (alloc gARG rACC2)

/-- The table offsets, and the tables. -/
def toffInit : Stmt := .seq toffAlloc (.seq (forUp rX2 gNS toffBody) tabAlloc)

/-- The first pass: `k`, the table offsets, the tables. -/
def prep (k : ℕ) : Stmt := .seq (.const rK k) toffInit

/-- The loop over the segments. -/
def segLoop : Stmt := forUp rJ gNS segBody

/-- **Phase P3** of the polygon solver, for cycle length `k`. -/
def poly3 (k : ℕ) : Stmt := .seq (prep k) segLoop

end STACS2027.RAM.P3
