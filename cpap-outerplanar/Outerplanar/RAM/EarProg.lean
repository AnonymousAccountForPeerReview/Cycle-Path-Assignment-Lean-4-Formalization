module

public import Outerplanar.RAM.Iface
public import Outerplanar.RAM.EarLL
public import Outerplanar.RAM.EarSpecR
public import Outerplanar.RAM.BoundedLib
public import Outerplanar.Algo.EarStatic
public import Outerplanar.Algo.EarPeel
import Mathlib.Tactic

/-!
# The ear-elimination machine: program, layout and memory representation

The program `earProg` computes `Ear.earHam N L` for the local graph of `EarIn N L` (`N` in
`gVN`, the edge ends at `gLU`, `gLV`, `|L|` in `gLN`), as `Ear.earHam` describes it, in
`O(N + |L|)` time **and space** (no `N × N` matrix):

1. **Initialization** (`O(N + |L|)`): fresh regions — the peeling's degrees `PD`, removed flags
   `PRM`, stack `PSTK` and out-neighbours `OUT1`, `OUT2` (`N` cells each), then the list heads
   `HD`, the degrees `DEG`, the dead flags `DEAD`, the stack `STK` (`4 N + 1` cells: its length
   is at most the potential), the log as three arrays `LGV`, `LGU`, `LGW` (`N` cells each,
   elimination order), the node pool `VAL`, `NXT` (`2 |L| + 2 N + 1` cells each: node `q ≥ 1`
   holds a value and the next node), the successor array `SUCC` and the output `gHAM` (`N` cells
   each). The edge loop prepends to the lists and counts the degrees; the stack loop pushes the
   vertices of degree two in increasing order.
2. **Peeling** (`peelProg`, `Outerplanar/Algo/EarPeel.lean`): the vertices of degree at most two
   are stacked; a popped vertex `x` is removed, its alive neighbours (scanning its list) lose a
   degree (a vertex reaching two is stacked) and the first two are recorded in `OUT1[x]`,
   `OUT2[x]` (`x` itself if missing). It stops when its stack is empty (linear time on every
   input). When `L` has an outerplanar Hamiltonian cycle, every edge `u w` is then recorded
   (`w ∈ OUT[u]` or `u ∈ OUT[w]`): `Ear.peel_orient`.
3. **Elimination** (`mainLoop`, a `while` loop on `stack ≠ [] ∧ 3 < cnt`): pop `v`; if alive
   with degree two, scan its whole list for the first two alive entries `u`, `w`, kill `v`, log
   `(v, u, w)`, and either lower the degrees of `u` and `w` (pushing a vertex of degree two) or
   add the virtual edge (two new nodes). Whether `u w` is an edge is asked of the orientation
   (`outChk`, four cells): by `Ear.query_static` the query never hits a virtual edge.
4. **Reconstruction** (`recon`): the first three alive vertices, the successors of the triangle,
   the reinsertion of the logged vertices (log scanned backwards), the walk into `gHAM`.

Memory: the layout `bPD F`, …, `bEND F N M` from the initial free address `F` (`bEND_le`:
`bEND F N M ≤ F + 21 (N + M + 1)`; `fits`: every region below a bound `S ≥ bEND F N M`), and
`EMem`, the representation of an abstract `Ear.State` (plus the successor table and the output
prefix of the reconstruction) from `bHD` on, the memory below `bHD` (the input, and the
peeling's regions) being that of a fixed `m₀`; one lemma per kind of store (`EMem.prepend`,
`EMem.setDeg`, `EMem.kill`, `EMem.push`, `EMem.log`, `EMem.setSucc`, `EMem.hamSnoc`,
`EMem.pop`; `EMem.updLow` for the stores of the peeling).

Address proofs (`HTB S`, `S ≥ bEND F N M`): the tactics `lay_unfold` / `lomega` / `ear_addr`
unfold the layout into sums of `F`, `N`, `M` before `omega` (with the bases as atoms and their
eighteen equations in the context, each `omega` call took seconds and the file ran out of
memory).
-/

@[expose] public section

namespace STACS2027.RAM.EarR

open STACS2027 STACS2027.Ear

/-! ### Registers (all scratch, `≥ rS`) -/

/-- Base of the first out-neighbours. -/
abbrev rO1 : ℕ := 100
/-- Base of the second out-neighbours. -/
abbrev rO2 : ℕ := 101
/-- Base of the list heads. -/
abbrev rHD : ℕ := 102
/-- Base of the degrees. -/
abbrev rDEG : ℕ := 103
/-- Base of the dead flags. -/
abbrev rDEAD : ℕ := 104
/-- Base of the stack. -/
abbrev rSTK : ℕ := 105
/-- Base of the logged vertices. -/
abbrev rLGV : ℕ := 106
/-- Base of the first logged neighbours. -/
abbrev rLGU : ℕ := 107
/-- Base of the second logged neighbours. -/
abbrev rLGW : ℕ := 108
/-- Base of the node values. -/
abbrev rVAL : ℕ := 109
/-- Base of the node successors. -/
abbrev rNXT : ℕ := 110
/-- Base of the successor array of the reconstruction. -/
abbrev rSUCC : ℕ := 111
/-- The constant `2`. -/
abbrev rTWO : ℕ := 112
/-- Stack size. -/
abbrev rSP : ℕ := 113
/-- Number of alive vertices. -/
abbrev rCNT : ℕ := 114
/-- Log length. -/
abbrev rLC : ℕ := 115
/-- Next free node. -/
abbrev rNP : ℕ := 116
/-- Loop counter. -/
abbrev rI : ℕ := 117
/-- Scratch. -/
abbrev rA : ℕ := 118
/-- Scratch. -/
abbrev rB : ℕ := 119
/-- The popped vertex. -/
abbrev rV : ℕ := 120
/-- First neighbour. -/
abbrev rU : ℕ := 121
/-- Second neighbour. -/
abbrev rW : ℕ := 122
/-- Scratch (scanned entry; first surviving vertex). -/
abbrev rX : ℕ := 123
/-- Number of alive entries seen by a scan. -/
abbrev rK : ℕ := 124
/-- A node pointer. -/
abbrev rP : ℕ := 125
/-- Scratch. -/
abbrev rQ : ℕ := 126
/-- Scratch. -/
abbrev rZ : ℕ := 127
/-- A degree. -/
abbrev rD : ℕ := 128
/-- Second surviving vertex. -/
abbrev rY : ℕ := 129
/-- Current vertex of the walk. -/
abbrev rC : ℕ := 130
/-- Base of the peeling degrees. -/
abbrev rPD : ℕ := 131
/-- An allocation size. -/
abbrev rSZ : ℕ := 132
/-- Base of the removed flags of the peeling. -/
abbrev rPRM : ℕ := 133
/-- Base of the stack of the peeling. -/
abbrev rPSTK : ℕ := 134
/-- Stack size of the peeling. -/
abbrev rPSP : ℕ := 135

/-! ### Layout -/

/-- Size of the node pool (`2 |L| + 2 N + 1` cells). -/
def poolSz (N M : ℕ) : ℕ := 2 * M + 2 * N + 1
/-- Degrees of the peeling (`N` cells). -/
def bPD (F : ℕ) : ℕ := F
/-- Removed flags of the peeling (`N` cells). -/
def bPRM (F N : ℕ) : ℕ := F + N
/-- Stack of the peeling (`N` cells: it holds distinct vertices). -/
def bPSTK (F N : ℕ) : ℕ := bPRM F N + N
/-- First out-neighbours (`N` cells). -/
def bO1 (F N : ℕ) : ℕ := bPSTK F N + N
/-- Second out-neighbours (`N` cells). -/
def bO2 (F N : ℕ) : ℕ := bO1 F N + N
/-- List heads (`N` cells). -/
def bHD (F N : ℕ) : ℕ := bO2 F N + N
/-- Degrees (`N` cells). -/
def bDEG (F N : ℕ) : ℕ := bHD F N + N
/-- Dead flags (`N` cells). -/
def bDEAD (F N : ℕ) : ℕ := bDEG F N + N
/-- Stack (`4 N + 1` cells). -/
def bSTK (F N : ℕ) : ℕ := bDEAD F N + N
/-- Logged vertices (`N` cells). -/
def bLGV (F N : ℕ) : ℕ := bSTK F N + (4 * N + 1)
/-- First logged neighbours (`N` cells). -/
def bLGU (F N : ℕ) : ℕ := bLGV F N + N
/-- Second logged neighbours (`N` cells). -/
def bLGW (F N : ℕ) : ℕ := bLGU F N + N
/-- Node values (`poolSz` cells). -/
def bVAL (F N : ℕ) : ℕ := bLGW F N + N
/-- Node successors (`poolSz` cells). -/
def bNXT (F N M : ℕ) : ℕ := bVAL F N + poolSz N M
/-- Successor array (`N` cells). -/
def bSUCC (F N M : ℕ) : ℕ := bNXT F N M + poolSz N M
/-- The output (`N` cells). -/
def bHAM (F N M : ℕ) : ℕ := bSUCC F N M + N
/-- End of the memory used. -/
def bEND (F N M : ℕ) : ℕ := bHAM F N M + N

/-- `lay_unfold` unfolds the layout everywhere, so that `omega` sees the bases as sums of `F`,
`N`, `M` (with the bases as atoms and their equations in the context, `omega` is very slow). -/
macro "lay_unfold" : tactic => `(tactic| simp -failIfUnchanged only [bPD, bPRM, bPSTK, bO1, bO2,
  bHD, bDEG, bDEAD, bSTK, bLGV, bLGU, bLGW, bVAL, bNXT, bSUCC, bHAM, bEND, poolSz] at *)

/-- `omega` after `lay_unfold`. -/
macro "lomega" : tactic => `(tactic| (lay_unfold; omega))

/-- `ear_addr [l₁, …]`: `addr_ok [l₁, …]` (`BoundedLib.lean`) with the layout unfolded (in the
context and in the goal). -/
syntax (name := earAddrTac) "ear_addr" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ear_addr) => `(tactic| ear_addr [])
  | `(tactic| ear_addr [$ls,*]) => `(tactic| (lay_unfold; addr_ok [$ls,*, bPD, bPRM, bPSTK, bO1,
      bO2, bHD, bDEG, bDEAD, bSTK, bLGV, bLGU, bLGW, bVAL, bNXT, bSUCC, bHAM, bEND, poolSz]))

/-- **The layout is linear**: `21 N + 4 |L| + 3` cells from `F`. -/
theorem bEND_le (F N M : ℕ) : bEND F N M ≤ F + 21 * (N + M + 1) := by
  lomega

/-- The regions fit below a bound `S ≥ bEND F N M`. -/
theorem fits {S F N M : ℕ} (hS : bEND F N M ≤ S) :
    bPD F + N ≤ S ∧ bPRM F N + N ≤ S ∧ bPSTK F N + N ≤ S ∧ bO1 F N + N ≤ S ∧ bO2 F N + N ≤ S ∧
      bHD F N + N ≤ S ∧ bDEG F N + N ≤ S ∧ bDEAD F N + N ≤ S ∧ bSTK F N + (4 * N + 1) ≤ S ∧
      bLGV F N + N ≤ S ∧ bLGU F N + N ≤ S ∧ bLGW F N + N ≤ S ∧ bVAL F N + poolSz N M ≤ S ∧
      bNXT F N M + poolSz N M ≤ S ∧ bSUCC F N M + N ≤ S ∧ bHAM F N M + N ≤ S ∧ F ≤ S := by
  lomega

/-! ### The program -/

/-- Prepend `y` to the list of `x`, as the new node `np`. -/
def prepend (x y : ℕ) : Stmt :=
  .seq (ld rZ rHD x) (.seq (st rVAL rNP y) (.seq (st rNXT rNP rZ) (.seq (st rHD x rNP) (inc rNP))))
/-- `deg[x] += 1`. -/
def incDeg (x : ℕ) : Stmt := .seq (ld rZ rDEG x) (.seq (inc rZ) (st rDEG x rZ))
/-- Push `x`. -/
def push (x : ℕ) : Stmt := .seq (st rSTK rSP x) (inc rSP)
/-- `deg[x] -= 1`; push `x` if its degree becomes two. -/
def decDegP (x : ℕ) : Stmt :=
  .seq (ld rD rDEG x) (.seq (dec rD) (.seq (st rDEG x rD) (ifEq rD rTWO (push x) .skip)))

/-- The first allocations: the regions of the peeling, heads, degrees, dead flags, stack. -/
def allocs1 : Stmt :=
  .seq (alloc rPD gVN) (.seq (alloc rPRM gVN) (.seq (alloc rPSTK gVN) (.seq (alloc rO1 gVN)
    (.seq (alloc rO2 gVN) (.seq (alloc rHD gVN) (.seq (alloc rDEG gVN) (.seq (alloc rDEAD gVN)
    (.seq (.add rSZ gVN gVN) (.seq (.add rSZ rSZ rSZ) (.seq (inc rSZ) (alloc rSTK rSZ)))))))))))
/-- The other allocations, and the initial registers. -/
def allocs2 : Stmt :=
  .seq (alloc rLGV gVN) (.seq (alloc rLGU gVN) (.seq (alloc rLGW gVN)
    (.seq (.add rSZ gLN gVN) (.seq (.add rSZ rSZ rSZ) (.seq (inc rSZ) (.seq (alloc rVAL rSZ)
    (.seq (alloc rNXT rSZ) (.seq (alloc rSUCC gVN) (.seq (alloc gHAM gVN)
    (.seq (.const rTWO 2) (.seq (.const rNP 1) (.seq (.const rSP 0)
    (.seq (mov rCNT gVN) (.seq (.const rLC 0) (.const rPSP 0)))))))))))))))
/-- One edge `(a, b)` of the input: `b` prepended to the list of `a`, then `a` to the list of
`b`, degrees. -/
def edgeBody : Stmt :=
  .seq (ld rA gLU rI) (.seq (ld rB gLV rI) (.seq (prepend rA rB) (.seq (prepend rB rA)
    (.seq (incDeg rA) (incDeg rB)))))
/-- Push `i` if its degree is two. -/
def stkBody : Stmt := .seq (ld rD rDEG rI) (ifEq rD rTWO (push rI) .skip)

/-- The loop test: `rT ≠ 0` iff `sp ≠ 0 ∧ 3 < cnt`. -/
def mcond : Stmt := .seq (.const rT 3) (.seq (.sub rT rCNT rT) (.ifz rSP (.const rT 0) .skip))
/-- Pop `v`, read its dead flag. -/
def pop : Stmt := .seq (dec rSP) (.seq (ld rV rSTK rSP) (ld rA rDEAD rV))
/-- Start of the scan of the list of `v`. -/
def scanInit : Stmt := .seq (.const rK 0) (.seq (.const rU 0) (.seq (.const rW 0) (ld rP rHD rV)))
/-- An alive entry `x`: the first becomes `u`, the second `w`. -/
def scanUpd : Stmt :=
  .seq (.ifz rK (mov rU rX) (.seq (subc rQ rK 1) (.ifz rQ (mov rW rX) .skip))) (inc rK)
/-- One node of the scan. -/
def scanBody : Stmt :=
  .seq (ld rX rVAL rP) (.seq (ld rQ rDEAD rX) (.seq (.ifz rQ scanUpd .skip) (ld rP rNXT rP)))
/-- The scan test: `p ≠ 0`. -/
def scanCond : Stmt := .add rT rP rZERO
/-- The scan of the whole list of `v`. -/
def scan : Stmt := .seq scanInit (whileC scanCond scanBody)
/-- Kill `v`, `cnt -= 1`, log `(v, u, w)`. -/
def killLog : Stmt :=
  .seq (st rDEAD rV rONE) (.seq (dec rCNT) (.seq (st rLGV rLC rV) (.seq (st rLGU rLC rU)
    (.seq (st rLGW rLC rW) (inc rLC)))))
/-- `rZ := 1` if the cell `b + x` holds `y`. -/
def eqChk (b x y : ℕ) : Stmt := .seq (ld rA b x) (ifEq rA y (.const rZ 1) .skip)
/-- `rZ := 1` if `w` is an out-neighbour of `u` or `u` one of `w`, else `0` (the adjacency test
of the orientation). -/
def outChk : Stmt :=
  .seq (.const rZ 0) (.seq (eqChk rO1 rU rW) (.seq (eqChk rO2 rU rW) (.seq (eqChk rO1 rW rU)
    (eqChk rO2 rW rU))))
/-- The virtual edge `u w`. -/
def addVirt : Stmt := .seq (prepend rU rW) (prepend rW rU)
/-- Lower the degrees of `u`, then `w`. -/
def decBoth : Stmt := .seq (decDegP rU) (decDegP rW)
/-- The elimination of `v` once `u`, `w` are known. -/
def elimBlk : Stmt := .seq killLog (.seq outChk (.ifz rZ addVirt decBoth))
/-- Check the degree of the alive popped vertex. -/
def checkDeg : Stmt := .seq (ld rD rDEG rV) (ifEq rD rTWO (.seq scan elimBlk) .skip)
/-- One round of the elimination loop. -/
def mbody : Stmt := .seq pop (.ifz rA checkDeg .skip)
/-- **The elimination loop.** -/
def mainLoop : Stmt := whileC mcond mbody

/-- Push `x` on the stack of the peeling. -/
def ppush (x : ℕ) : Stmt := .seq (st rPSTK rPSP x) (inc rPSP)
/-- `PD[i] := DEG[i]`; stack `i` if at most two. -/
def pInitBody : Stmt := .seq (ld rD rDEG rI) (.seq (st rPD rI rD) (ifLe rD rTWO (ppush rI) .skip))
/-- An alive entry `x` of the removed vertex's list: record it (`scanUpd`), lower its degree,
stack it when the degree becomes two. -/
def pUpd : Stmt :=
  .seq scanUpd (.seq (ld rD rPD rX) (.seq (dec rD) (.seq (st rPD rX rD)
    (ifEq rD rTWO (ppush rX) .skip))))
/-- One node of the scan of the peeling. -/
def pScanBody : Stmt :=
  .seq (ld rX rVAL rP) (.seq (ld rQ rPRM rX) (.seq (.ifz rQ pUpd .skip) (ld rP rNXT rP)))
/-- Start of the scan of the list of the removed vertex `v` (`u`, `w` default to `v`). -/
def pScanInit : Stmt := .seq (.const rK 0) (.seq (mov rU rV) (.seq (mov rW rV) (ld rP rHD rV)))
/-- The scan of the list of the removed vertex. -/
def pScan : Stmt := .seq pScanInit (whileC scanCond pScanBody)
/-- Pop `v` from the stack of the peeling and remove it. -/
def pPop : Stmt := .seq (dec rPSP) (.seq (ld rV rPSTK rPSP) (st rPRM rV rONE))
/-- One round of the peeling: pop and remove `v`, scan its list, record its out-neighbours. -/
def pBody : Stmt := .seq pPop (.seq pScan (.seq (st rO1 rV rU) (st rO2 rV rW)))
/-- The test of the peeling: its stack is nonempty. -/
def pCond : Stmt := .add rT rPSP rZERO
/-- **The peeling.** -/
def peelProg : Stmt := .seq (forUp rI gVN pInitBody) (whileC pCond pBody)

/-- **Initialization** (with the peeling). -/
def initProg : Stmt :=
  .seq (.seq (.seq allocs1 allocs2) (.seq (forUp rI gLN edgeBody) (forUp rI gVN stkBody))) peelProg

/-- Start of the search for the three surviving vertices. -/
def triInit : Stmt := .seq (.const rK 0) (.seq (.const rX 0) (.seq (.const rY 0) (.const rZ 0)))
/-- An alive vertex `i`: the first becomes `x`, the second `y`, the third `z`. -/
def triUpd : Stmt :=
  .seq (.ifz rK (mov rX rI) (.seq (subc rQ rK 1) (.ifz rQ (mov rY rI)
    (.seq (subc rQ rK 2) (.ifz rQ (mov rZ rI) .skip))))) (inc rK)
/-- One vertex of the search. -/
def triBody : Stmt := .seq (ld rA rDEAD rI) (.ifz rA triUpd .skip)
/-- The successors of the triangle `x → y → z → x`. -/
def succInit : Stmt := .seq (st rSUCC rX rY) (.seq (st rSUCC rY rZ) (st rSUCC rZ rX))
/-- Reinsert the logged vertex `lc - 1 - i`. -/
def reinsBody : Stmt :=
  .seq (.sub rP rLC rI) (.seq (dec rP) (.seq (ld rV rLGV rP) (.seq (ld rU rLGU rP)
    (.seq (ld rW rLGW rP) (.seq (ld rQ rSUCC rU)
    (ifEq rQ rW (.seq (st rSUCC rU rV) (st rSUCC rV rW)) (.seq (st rSUCC rW rV) (st rSUCC rV rU))))))))
/-- One step of the final walk. -/
def walkBody : Stmt := .seq (st gHAM rI rC) (ld rC rSUCC rC)
/-- **The reconstruction.** -/
def recon : Stmt :=
  .seq triInit (.seq (forUp rI gVN triBody) (.seq succInit (.seq (forUp rI rLC reinsBody)
    (.seq (mov rC rX) (forUp rI gVN walkBody)))))

/-- **The ear-elimination program.** -/
def earProg : Stmt := .seq initProg (.seq mainLoop recon)

/-! ### Constant registers -/

/-- The registers that keep their value from the end of the allocations on. -/
@[mk_iff] structure Glob (N M F : ℕ) (c : Config) : Prop where
  zero : c.reg rZERO = 0
  one : c.reg rONE = 1
  vn : c.reg gVN = N
  two : c.reg rTWO = 2
  pd : c.reg rPD = bPD F
  prm : c.reg rPRM = bPRM F N
  pstk : c.reg rPSTK = bPSTK F N
  o1 : c.reg rO1 = bO1 F N
  o2 : c.reg rO2 = bO2 F N
  hd : c.reg rHD = bHD F N
  deg : c.reg rDEG = bDEG F N
  dead : c.reg rDEAD = bDEAD F N
  stk : c.reg rSTK = bSTK F N
  lgv : c.reg rLGV = bLGV F N
  lgu : c.reg rLGU = bLGU F N
  lgw : c.reg rLGW = bLGW F N
  val : c.reg rVAL = bVAL F N
  nxt : c.reg rNXT = bNXT F N M
  succ : c.reg rSUCC = bSUCC F N M
  ham : c.reg gHAM = bHAM F N M
  free : c.reg rFREE = bEND F N M

/-- The registers written after the allocations. -/
def WV : List ℕ :=
  [rT, rSP, rCNT, rLC, rNP, rI, rA, rB, rV, rU, rW, rX, rK, rP, rQ, rZ, rD, rY, rC, rPSP]

theorem Glob.regIndep (N M F : ℕ) : RegIndep WV (Glob N M F) := by indep [glob_iff]

/-! ### The memory representation -/

/-- The memory holding the abstract state `s` (the stack bottom first, the log in elimination
order), the successor table `succ` and the output prefix `ham`, with nodes below `np`; the
memory below `bHD F N` (the input and the regions of the peeling) is that of `m₀`, the memory
from `bEND` on is zero. -/
structure EMem (N M F : ℕ) (m₀ : ℕ → ℕ) (s : State) (succ : ℕ → ℕ) (ham : List ℕ) (np : ℕ)
    (m : ℕ → ℕ) : Prop where
  adj : AdjRep m (bHD F N) (bVAL F N) (bNXT F N M) N np s.adj
  deg : Tab m (bDEG F N) N s.deg
  dead : Tab m (bDEAD F N) N (fun v => if s.dead v = true then 1 else 0)
  stk : Arr m (bSTK F N) s.stack.reverse
  lgv : Arr m (bLGV F N) (s.log.reverse.map Prod.fst)
  lgu : Arr m (bLGU F N) (s.log.reverse.map fun e => e.2.1)
  lgw : Arr m (bLGW F N) (s.log.reverse.map fun e => e.2.2)
  sucT : Tab m (bSUCC F N M) N succ
  hamA : Arr m (bHAM F N M) ham
  same : SameOn (· < bHD F N) m₀ m
  zero : ZeroFrom m (bEND F N M)
  npS : np ≤ poolSz N M
  stkS : s.stack.length ≤ 4 * N + 1
  logS : s.log.length ≤ N
  hamS : ham.length ≤ N

namespace EMem

variable {N M F : ℕ} {m₀ m : ℕ → ℕ} {s : State} {succ : ℕ → ℕ} {ham : List ℕ} {np : ℕ}

/-- A store below `bHD` (in a region of the peeling), with the frozen memory following it. -/
theorem updLow (h : EMem N M F m s succ ham np m) {a : ℕ} (ha : a < bHD F N) (v : ℕ) :
    EMem N M F (upd m a v) s succ ham np (upd m a v) := by
  have hs := h.stkS
  have hl := h.logS
  have hh := h.hamS
  have hn := h.npS
  exact ⟨h.adj.upd_of_disjoint (by lomega) (by lomega) (by lomega), h.deg.upd_of_disjoint (by lomega),
    h.dead.upd_of_disjoint (by lomega), h.stk.upd_of_disjoint (by simp; lomega),
    h.lgv.upd_of_disjoint (by simp; lomega), h.lgu.upd_of_disjoint (by simp; lomega),
    h.lgw.upd_of_disjoint (by simp; lomega), h.sucT.upd_of_disjoint (by lomega),
    h.hamA.upd_of_disjoint (by lomega), SameOn.refl _ _, h.zero.upd (by lomega),
    h.npS, h.stkS, h.logS, h.hamS⟩

/-- The frozen memory below `bHD` can be taken to be the current one. -/
theorem rebase (h : EMem N M F m₀ s succ ham np m) : EMem N M F m s succ ham np m :=
  ⟨h.adj, h.deg, h.dead, h.stk, h.lgv, h.lgu, h.lgw, h.sucT, h.hamA, SameOn.refl _ _, h.zero,
    h.npS, h.stkS, h.logS, h.hamS⟩

/-- Prepend `y` to the list of `x` (new node `np`). -/
theorem prepend (h : EMem N M F m₀ s succ ham np m) {x : ℕ} (y : ℕ) (hx : x < N) (hn : 0 < np)
    (hnS : np + 1 ≤ poolSz N M) :
    EMem N M F m₀ { s with adj := Function.update s.adj x (y :: s.adj x) } succ ham (np + 1)
      (upd (upd (upd m (bVAL F N + np) y) (bNXT F N M + np) (m (bHD F N + x))) (bHD F N + x) np) := by
  have hs := h.stkS
  have hl := h.logS
  have hh := h.hamS
  refine ⟨h.adj.prepend hx hn (by lomega) (by lomega),
    ((h.deg.upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega),
    ((h.dead.upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega),
    ((h.stk.upd_of_disjoint (by simp; lomega)).upd_of_disjoint (by simp; lomega)).upd_of_disjoint
      (by simp; lomega),
    ((h.lgv.upd_of_disjoint (by simp; lomega)).upd_of_disjoint (by simp; lomega)).upd_of_disjoint
      (by simp; lomega),
    ((h.lgu.upd_of_disjoint (by simp; lomega)).upd_of_disjoint (by simp; lomega)).upd_of_disjoint
      (by simp; lomega),
    ((h.lgw.upd_of_disjoint (by simp; lomega)).upd_of_disjoint (by simp; lomega)).upd_of_disjoint
      (by simp; lomega),
    ((h.sucT.upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega),
    ((h.hamA.upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega),
    ((h.same.upd_of_ge (by lomega) _).upd_of_ge (by lomega) _).upd_of_ge (by lomega) _,
    ((h.zero.upd (by lomega)).upd (by lomega)).upd (by lomega), hnS, h.stkS, h.logS, h.hamS⟩

/-- `deg[x] := d`. -/
theorem setDeg (h : EMem N M F m₀ s succ ham np m) {x : ℕ} (d : ℕ) (hx : x < N) :
    EMem N M F m₀ { s with deg := Function.update s.deg x d } succ ham np (upd m (bDEG F N + x) d) := by
  have hs := h.stkS
  have hl := h.logS
  have hh := h.hamS
  have hn := h.npS
  exact ⟨h.adj.upd_of_disjoint (by lomega) (by lomega) (by lomega), h.deg.upd rfl,
    h.dead.upd_of_disjoint (by lomega), h.stk.upd_of_disjoint (by simp; lomega),
    h.lgv.upd_of_disjoint (by simp; lomega), h.lgu.upd_of_disjoint (by simp; lomega),
    h.lgw.upd_of_disjoint (by simp; lomega), h.sucT.upd_of_disjoint (by lomega),
    h.hamA.upd_of_disjoint (by lomega), h.same.upd_of_ge (by lomega) _, h.zero.upd (by lomega),
    h.npS, h.stkS, h.logS, h.hamS⟩

/-- `dead[v] := 1`. -/
theorem kill (h : EMem N M F m₀ s succ ham np m) {v : ℕ} (hv : v < N) :
    EMem N M F m₀ { s with dead := Function.update s.dead v true } succ ham np
      (upd m (bDEAD F N + v) 1) := by
  have hs := h.stkS
  have hl := h.logS
  have hh := h.hamS
  have hn := h.npS
  refine ⟨h.adj.upd_of_disjoint (by lomega) (by lomega) (by lomega), h.deg.upd_of_disjoint (by lomega),
    ?_, h.stk.upd_of_disjoint (by simp; lomega),
    h.lgv.upd_of_disjoint (by simp; lomega), h.lgu.upd_of_disjoint (by simp; lomega),
    h.lgw.upd_of_disjoint (by simp; lomega), h.sucT.upd_of_disjoint (by lomega),
    h.hamA.upd_of_disjoint (by lomega), h.same.upd_of_ge (by lomega) _, h.zero.upd (by lomega),
    h.npS, h.stkS, h.logS, h.hamS⟩
  refine (h.dead.upd (i := v) (v := 1) rfl).congr_fun fun x _ => ?_
  by_cases hx : x = v
  · subst hx; simp
  · simp [Function.update_of_ne hx]

/-- Push `x` (at `bSTK + |stack|`). -/
theorem push (h : EMem N M F m₀ s succ ham np m) (x : ℕ) (hS : s.stack.length + 1 ≤ 4 * N + 1) :
    EMem N M F m₀ { s with stack := x :: s.stack } succ ham np
      (upd m (bSTK F N + s.stack.length) x) := by
  have hl := h.logS
  have hh := h.hamS
  have hn := h.npS
  refine ⟨h.adj.upd_of_disjoint (by lomega) (by lomega) (by lomega), h.deg.upd_of_disjoint (by lomega),
    h.dead.upd_of_disjoint (by lomega), ?_,
    h.lgv.upd_of_disjoint (by simp; lomega), h.lgu.upd_of_disjoint (by simp; lomega),
    h.lgw.upd_of_disjoint (by simp; lomega), h.sucT.upd_of_disjoint (by lomega),
    h.hamA.upd_of_disjoint (by lomega), h.same.upd_of_ge (by lomega) _, h.zero.upd (by lomega),
    h.npS, by simpa using hS, h.logS, h.hamS⟩
  simpa using h.stk.upd_snoc (x := x) (by simp)

/-- Log `(v, u, w)` (at index `|log|` of the three log arrays). -/
theorem log (h : EMem N M F m₀ s succ ham np m) (v u w : ℕ) (hS : s.log.length + 1 ≤ N) :
    EMem N M F m₀ { s with log := (v, u, w) :: s.log } succ ham np
      (upd (upd (upd m (bLGV F N + s.log.length) v) (bLGU F N + s.log.length) u)
        (bLGW F N + s.log.length) w) := by
  have hs := h.stkS
  have hh := h.hamS
  have hn := h.npS
  refine ⟨((h.adj.upd_of_disjoint (by lomega) (by lomega) (by lomega)).upd_of_disjoint (by lomega) (by lomega)
      (by lomega)).upd_of_disjoint (by lomega) (by lomega) (by lomega),
    ((h.deg.upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega),
    ((h.dead.upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega),
    ((h.stk.upd_of_disjoint (by simp; lomega)).upd_of_disjoint (by simp; lomega)).upd_of_disjoint
      (by simp; lomega), ?_, ?_, ?_,
    ((h.sucT.upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega),
    ((h.hamA.upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega)).upd_of_disjoint (by lomega),
    ((h.same.upd_of_ge (by lomega) _).upd_of_ge (by lomega) _).upd_of_ge (by lomega) _,
    ((h.zero.upd (by lomega)).upd (by lomega)).upd (by lomega), h.npS, h.stkS, by simpa using hS,
    h.hamS⟩
  · have := ((h.lgv.upd_snoc (a := bLGV F N + s.log.length) (x := v) (by simp)).upd_of_disjoint
      (a := bLGU F N + s.log.length) (v := u) (by simp; lomega)).upd_of_disjoint
      (a := bLGW F N + s.log.length) (v := w) (by simp; lomega)
    simpa using this
  · have := ((h.lgu.upd_of_disjoint (a := bLGV F N + s.log.length) (v := v)
      (by simp; lomega)).upd_snoc (a := bLGU F N + s.log.length) (x := u) (by simp)).upd_of_disjoint
      (a := bLGW F N + s.log.length) (v := w) (by simp; lomega)
    simpa using this
  · have := ((h.lgw.upd_of_disjoint (a := bLGV F N + s.log.length) (v := v)
      (by simp; lomega)).upd_of_disjoint (a := bLGU F N + s.log.length) (v := u)
      (by simp; lomega)).upd_snoc (a := bLGW F N + s.log.length) (x := w) (by simp)
    simpa using this

/-- `succ[x] := y`. -/
theorem setSucc (h : EMem N M F m₀ s succ ham np m) {x : ℕ} (y : ℕ) (hx : x < N) :
    EMem N M F m₀ s (Function.update succ x y) ham np (upd m (bSUCC F N M + x) y) := by
  have hs := h.stkS
  have hl := h.logS
  have hh := h.hamS
  have hn := h.npS
  exact ⟨h.adj.upd_of_disjoint (by lomega) (by lomega) (by lomega), h.deg.upd_of_disjoint (by lomega),
    h.dead.upd_of_disjoint (by lomega), h.stk.upd_of_disjoint (by simp; lomega),
    h.lgv.upd_of_disjoint (by simp; lomega), h.lgu.upd_of_disjoint (by simp; lomega),
    h.lgw.upd_of_disjoint (by simp; lomega), h.sucT.upd rfl,
    h.hamA.upd_of_disjoint (by lomega), h.same.upd_of_ge (by lomega) _, h.zero.upd (by lomega),
    h.npS, h.stkS, h.logS, h.hamS⟩

/-- Append `x` to the output. -/
theorem hamSnoc (h : EMem N M F m₀ s succ ham np m) (x : ℕ) (hS : ham.length + 1 ≤ N) :
    EMem N M F m₀ s succ (ham ++ [x]) np (upd m (bHAM F N M + ham.length) x) := by
  have hs := h.stkS
  have hl := h.logS
  have hn := h.npS
  exact ⟨h.adj.upd_of_disjoint (by lomega) (by lomega) (by lomega), h.deg.upd_of_disjoint (by lomega),
    h.dead.upd_of_disjoint (by lomega), h.stk.upd_of_disjoint (by simp; lomega),
    h.lgv.upd_of_disjoint (by simp; lomega), h.lgu.upd_of_disjoint (by simp; lomega),
    h.lgw.upd_of_disjoint (by simp; lomega), h.sucT.upd_of_disjoint (by lomega),
    h.hamA.upd_snoc rfl, h.same.upd_of_ge (by lomega) _, h.zero.upd (by lomega),
    h.npS, h.stkS, h.logS, by simpa using hS⟩

/-- Popping does not change the memory. -/
theorem pop (h : EMem N M F m₀ s succ ham np m) {v : ℕ} {rest : List ℕ} (hs : s.stack = v :: rest) :
    EMem N M F m₀ { s with stack := rest } succ ham np m := by
  have hstk := h.stk
  rw [hs, List.reverse_cons] at hstk
  have hS := h.stkS
  rw [hs] at hS
  exact ⟨h.adj, h.deg, h.dead, hstk.prefix, h.lgv, h.lgu, h.lgw, h.sucT, h.hamA,
    h.same, h.zero, h.npS, by simp at hS ⊢; omega, h.logS, h.hamS⟩

end EMem

end STACS2027.RAM.EarR
