module

public import Runtimes.Flow.EdgeSpec
public import Runtimes.ZeroCostProg
public import Outerplanar.RAM.Lib
import Mathlib.Tactic

/-!
# The flow-network machines: input, registers, layout and programs

**Input** of the construction machines (`flowInput g cs k`): `graphInput g ++ k :: t :: verts cs`,
i.e. `m = |g|`, the `2m` ends of the edges of `g`, then `k`, the number `t` of cycles, and the
vertices of the cycles `C_0, …, C_{t-1}` of the list `cs`, cycle after cycle (`k` each) — the
format of `ZeroCost.zeroCostInput` (which is `flowInput g (cycles g k) k`), for any list `cs`, e.g. a
permutation of `cycles g k` produced by an enumeration algorithm.

**Registers**: the edge pass is Corollary 5's front end, so it uses Corollary 5's registers
(`250–299`), outerplanar package's `PairIds.pairIds` (`100–109`, `120–137`); the registers it leaves to
the output phases have the names `gT gNE gEID gCNT` here (aliases of Corollary 5's). The output
and extraction phases use `561` (`gEB`) and the scratch block `570–587`.

**Programs** (all loops are counted loops):
* `edgePhase = ZeroCost.stepInit; ZeroCost.stepMax; ZeroCost.stepDict; ZeroCost.stepEdges` (shared by
  `k = 4` and `k = 3`; the programs of Corollary 5 read `k`, `t` and the vertices from the
  input and do not depend on the list of cycles): read `m`, `k`, `t`; the largest label `M`; the
  label dictionary (`M + 1` cells, allocated, not cleared); the id pairs `(PU[q], PV[q])` of the
  occurrences `q = ik + j`, and `PairIds.pairIds` (a counting sort of the pairs and a
  timestamped scan, no table indexed by pairs): `EID[q] = eid cs q`, `CNT[id]` the counts, `gNE`
  the number of distinct edges;
* `out4` (`k = 4`): the header `n, 10t, 0, 1, 2t` (`n = 2 + 2t + E`), the source arcs, the
  opposing-pair arcs (the edge node of occurrence `q` is `2 + 2t + EID[q]`) and the sink bundles
  (`CNT[r]` arcs `2 + 2t + r → 1` with costs `0, 1, …`); `build4 = edgePhase; out4`;
* `out3` (`k = 3`): the same for the triangle network, `n = 2 + t + E`, `7t` arcs, value `t`;
  `build3 = edgePhase; out3`;
* `extract4`, `extract3`: on the input followed by the solver's answer `1 :: bits`, for each
  cycle the position read off the bits of its arcs (`readOff4`, `readOff3`).

**Layout** of the construction (from the end of the input `bD`, as Corollary 5's): the
dictionary (`maxV cs + 1 ≤ labelBound g` cells), `PU`, `PV` (`kt` each), the memory of
`PairIds.pairIds` from `bPI` (its sort and leaders, then `EID`, `CNT`), ending at `bOFF`.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

/-! ### Input -/

/-- **The input of the flow machines**: the graph, `k`, `t`, the vertices of the cycles `cs`. -/
def flowInput (g : Graph) (cs : List Cycle) (k : ℕ) : List ℕ :=
  graphInput g ++ k :: cs.length :: verts cs

/-! ### Registers -/

/-- `k` (Corollary 5's register). -/
abbrev gK : ℕ := ZeroCost.gK
/-- `t`, the number of cycles. -/
abbrev gT : ℕ := ZeroCost.gT
/-- The address of the cycles in the input. -/
abbrev gV : ℕ := ZeroCost.gV
/-- `kt`. -/
abbrev gKT : ℕ := ZeroCost.gKT
/-- `2kt`. -/
abbrev gNV : ℕ := ZeroCost.gNV
/-- The largest label `M`. -/
abbrev gMX : ℕ := ZeroCost.gMX
/-- The base of the label dictionary. -/
abbrev gD : ℕ := ZeroCost.gD
/-- The number of vertices. -/
abbrev gN : ℕ := ZeroCost.gN
/-- The base of the first ids of the pairs. -/
abbrev gPU : ℕ := ZeroCost.gPU
/-- The base of the second ids of the pairs. -/
abbrev gPV : ℕ := ZeroCost.gPV
/-- The base of the identifiers of the occurrences. -/
abbrev gEID : ℕ := ZeroCost.gEID
/-- The base of the counts. -/
abbrev gCNT : ℕ := ZeroCost.gCNT
/-- The number of distinct edges. -/
abbrev gNE : ℕ := ZeroCost.gNE
/-- The number of the first edge node (`2 + 2t` or `2 + t`). -/
abbrev gEB : ℕ := 561

/-- Scratch: occurrence, address. -/
abbrev sQ : ℕ := 570
/-- Scratch: cycle counter. -/
abbrev sI : ℕ := 571
/-- Scratch: position counter. -/
abbrev sJ : ℕ := 572
/-- Scratch: first end. -/
abbrev sX : ℕ := 573
/-- Scratch: second end. -/
abbrev sY : ℕ := 574
/-- Scratch: position of the second end. -/
abbrev sP : ℕ := 575
/-- Scratch: identifier `+ 1`. -/
abbrev sZ : ℕ := 578
/-- Scratch: a count. -/
abbrev sC : ℕ := 579
/-- Scratch: `ik`, the first occurrence of the current cycle. -/
abbrev sBase : ℕ := 580
/-- Scratch: the current node number. -/
abbrev sA : ℕ := 581
/-- Scratch: an edge node number. -/
abbrev sE : ℕ := 582
/-- Scratch: the identifier counter. -/
abbrev sR : ℕ := 583
/-- Scratch: the constant `1`. -/
abbrev sOne : ℕ := 584
/-- Scratch: the constant `0`. -/
abbrev sZ0 : ℕ := 585
/-- Scratch: an address in the answer of the solver. -/
abbrev sB : ℕ := 586
/-- Scratch: the constant `3`. -/
abbrev sThree : ℕ := 587

/-! ### Layout -/

section layout

variable (g : Graph) (cs : List Cycle) (k : ℕ)

/-- The address of the cycles. -/
def bV : ℕ := 2 * g.length + 3
/-- The label dictionary (`M + 1` cells), at the end of the input. -/
def bD : ℕ := bV g + k * cs.length
/-- The first ids `PU` of the occurrences (`kt` cells). -/
def bPU : ℕ := bD g cs k + maxV cs + 1
/-- The second ids `PV` of the occurrences (`kt` cells). -/
def bPV : ℕ := bPU g cs k + k * cs.length
/-- The free address at the call of `PairIds.pairIds`. -/
def bPI : ℕ := bPV g cs k + k * cs.length
/-- The identifiers of the occurrences (`kt` cells), stored by `PairIds.pairIds`. -/
def bEID : ℕ := PairIds.leadsEnd (nV cs) (k * cs.length) (bPI g cs k)
/-- The counts (`kt` cells). -/
def bCNT : ℕ := bEID g cs k + k * cs.length
/-- The end of the memory of the edge pass. -/
def bOFF : ℕ := bCNT g cs k + k * cs.length

theorem bEID_eq : bEID g cs k = bPI g cs k + 4 * nV cs + 2 * (k * cs.length) + 1 := by
  have := PairIds.leads_eqs (nV cs) (k * cs.length) (bPI g cs k)
  unfold bEID; omega

theorem layout_eqs : bV g = 2 * g.length + 3 ∧ bD g cs k = bV g + k * cs.length ∧
    bPU g cs k = bD g cs k + maxV cs + 1 ∧ bPV g cs k = bPU g cs k + k * cs.length ∧
    bPI g cs k = bPV g cs k + k * cs.length ∧
    bEID g cs k = bPI g cs k + 4 * nV cs + 2 * (k * cs.length) + 1 ∧
    bCNT g cs k = bEID g cs k + k * cs.length ∧ bOFF g cs k = bCNT g cs k + k * cs.length :=
  ⟨rfl, rfl, rfl, rfl, rfl, bEID_eq g cs k, rfl, rfl⟩

/-- The end of the memory of `PairIds.pairIds` is `bOFF`. -/
theorem idsEnd_eq : PairIds.idsEnd (nV cs) (k * cs.length) (bPI g cs k) = bOFF g cs k := rfl

end layout

/-! ### Phases 1–4: the edge pass -/

/-- **The edge pass** (phases 1–4): Corollary 5's front end. -/
def edgePhase : Stmt :=
  .seq ZeroCost.stepInit (.seq ZeroCost.stepMax (.seq ZeroCost.stepDict ZeroCost.stepEdges))

/-! ### The output of the networks -/

/-- The arc from node `sA` to the edge node of occurrence `sBase + j`, of cost `0`. -/
def pairArc (j : ℕ) : Stmt :=
  .seq (addc sQ sBase j) (.seq (ld sE gEID sQ) (.seq (.add sE gEB sE) (.seq (.write sA)
    (.seq (.write sE) (.write sZ0)))))

/-- The `CNT[sR]` arcs from the edge node `sE` to the sink. -/
def sinkInner : Stmt := .seq (.write sE) (.seq (.write sOne) (.write sJ))

/-- The bundle of the edge with identifier `sR`. -/
def sinkBody : Stmt := .seq (ld sC gCNT sR) (.seq (.add sE gEB sR) (forUp sJ sC sinkInner))

/-- The sink bundles. -/
def outSink : Stmt := forUp sR gNE sinkBody

/-- The header of the four-cycle network: `2 + 2t + E, 10t, 0, 1, 2t`; `gEB := 2 + 2t`. -/
def hdr4 : Stmt :=
  .seq (.add sA gT gT) (.seq (addc gEB sA 2) (.seq (.add sX gEB gNE) (.seq (.write sX)
    (.seq (.add sY sA sA) (.seq (.add sY sY sY) (.seq (.add sY sY sA) (.seq (.write sY)
    (.seq (.const sZ0 0) (.seq (.write sZ0) (.seq (.const sOne 1) (.seq (.write sOne)
    (.write sA))))))))))))

/-- The two source arcs of a four-cycle. -/
def srcBody4 : Stmt :=
  .seq (.write sZ0) (.seq (.write sA) (.seq (.write sZ0) (.seq (inc sA) (.seq (.write sZ0)
    (.seq (.write sA) (.seq (.write sZ0) (inc sA)))))))

/-- The source arcs of the four-cycle network. -/
def src4 : Stmt := .seq (.const sA 2) (forUp sI gT srcBody4)

/-- The four opposing-pair arcs of a four-cycle: `x_{C,{e₁,e₃}} → y_{e₁}, y_{e₃}`, then
`x_{C,{e₂,e₄}} → y_{e₂}, y_{e₄}`. -/
def pairBody4 : Stmt :=
  .seq (pairArc 0) (.seq (pairArc 2) (.seq (inc sA) (.seq (pairArc 1) (.seq (pairArc 3)
    (.seq (inc sA) (addc sBase sBase 4))))))

/-- The opposing-pair arcs. -/
def pair4 : Stmt := .seq (.const sA 2) (.seq (.const sBase 0) (forUp sI gT pairBody4))

/-- The output of the four-cycle network. -/
def out4 : Stmt := .seq hdr4 (.seq src4 (.seq pair4 outSink))

/-- **The construction machine of Theorem 2.** -/
def build4 : Stmt := .seq edgePhase out4

/-- The header of the triangle network: `2 + t + E, 7t, 0, 1, t`; `gEB := 2 + t`. -/
def hdr3 : Stmt :=
  .seq (addc gEB gT 2) (.seq (.add sX gEB gNE) (.seq (.write sX) (.seq (.add sA gT gT)
    (.seq (.add sY sA sA) (.seq (.add sY sY sA) (.seq (.add sY sY gT) (.seq (.write sY)
    (.seq (.const sZ0 0) (.seq (.write sZ0) (.seq (.const sOne 1) (.seq (.write sOne)
    (.write gT))))))))))))

/-- The source arc of a triangle. -/
def srcBody3 : Stmt := .seq (.write sZ0) (.seq (.write sA) (.seq (.write sZ0) (inc sA)))

/-- The source arcs of the triangle network. -/
def src3 : Stmt := .seq (.const sA 2) (forUp sI gT srcBody3)

/-- The three arcs of a triangle node. -/
def triBody3 : Stmt :=
  .seq (pairArc 0) (.seq (pairArc 1) (.seq (pairArc 2) (.seq (inc sA) (addc sBase sBase 3))))

/-- The triangle arcs. -/
def tri3 : Stmt := .seq (.const sA 2) (.seq (.const sBase 0) (forUp sI gT triBody3))

/-- The output of the triangle network. -/
def out3 : Stmt := .seq hdr3 (.seq src3 (.seq tri3 outSink))

/-- **The construction machine of the triangle corollary.** -/
def build3 : Stmt := .seq edgePhase out3

/-! ### The extraction of an assignment -/

/-- Reading `m`, `t`; `sB := 2m + 3 + 4t + 1 + 2t` (the bits of the opposing-pair arcs). -/
def exInit4 : Stmt :=
  .seq (.load sX 0) (.seq (.add sX sX sX) (.seq (addc gV sX 3) (.seq (subc sY gV 1)
    (.seq (.load gT sY) (.seq (.add sZ gT gT) (.seq (.add sY sZ sZ) (.seq (.add sB gV sY)
    (.seq (inc sB) (.seq (.add sB sB sZ) (.seq (.const sOne 1) (.const sThree 3)))))))))))

/-- The position of one four-cycle: `optionIndex (bit₁ ≠ 0) (bit₃ ≠ 0)`. -/
def exBody4 : Stmt :=
  .seq (ld sX sB sOne) (.seq (ld sY sB sThree) (.seq
    (.ifz sX (.ifz sY (.const sP 3) (.const sP 2)) (.ifz sY (.const sP 0) (.const sP 1)))
    (.seq (.write sP) (addc sB sB 4))))

/-- **The extraction machine of Theorem 2.** -/
def extract4 : Stmt := .seq exInit4 (forUp sI gT exBody4)

/-- Reading `m`, `t`; `sB := 2m + 3 + 3t + 1 + t` (the bits of the triangle arcs). -/
def exInit3 : Stmt :=
  .seq (.load sX 0) (.seq (.add sX sX sX) (.seq (addc gV sX 3) (.seq (subc sY gV 1)
    (.seq (.load gT sY) (.seq (.add sZ gT gT) (.seq (.add sY sZ gT) (.seq (.add sB gV sY)
    (.seq (inc sB) (.seq (.add sB sB gT) (.const sOne 1))))))))))

/-- The position of one triangle: `2` if its first arc carries flow, else `0` if its second
does, else `1`. -/
def exBody3 : Stmt :=
  .seq (.load sX sB) (.seq (ld sY sB sOne) (.seq
    (.ifz sX (.ifz sY (.const sP 1) (.const sP 0)) (.const sP 2))
    (.seq (.write sP) (addc sB sB 3))))

/-- **The extraction machine of the triangle corollary.** -/
def extract3 : Stmt := .seq exInit3 (forUp sI gT exBody3)

end STACS2027.Runtimes.Flow
