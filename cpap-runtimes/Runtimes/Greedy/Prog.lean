module

public import Runtimes.Greedy.Spec
public import Runtimes.ZeroCostEdges
import Mathlib.Tactic

/-!
# Lemma 15 on the RAM: registers, layout and program

**Input**: Corollary 5's (`ZeroCost.zeroCostInput g k = graphInput g ++ k :: t :: verts g k`): the
graph, `k`, the number `t` of enumerated simple `k`-cycles and their vertices, cycle after cycle.
The enumeration is charged separately (the manuscript's `Υ_k`).

**Program** `greedyProg`:
1. Corollary 5's front end, phases 1–4 (`stepInit`, `stepMax`, `stepDict`, `stepEdges`, all
   `HTB S`, without a matrix): the identifier `EID[q] = eidOf g k q` of every occurrence
   `q = ik + p` (the edge at position `p` of `C_i`), i.e. the index of its edge among the `nE ≤ kt`
   distinct cycle edges;
2. `stepLoad`: the load table `LD` (`nE` cells, fresh and hence zero), indexed by identifiers;
3. `stepGreedy`: for each cycle `i < t` (`cycBody`, `O(k)` steps):
   * `sumPhase`: the total `tot = Σ_{p < k} LD[EID[ik + p]]`;
   * `choosePhase`: for each option `j < k`, its load-sum `tot − LD(j) − LD(prv j)` (the option
     omits the edges at the positions `j` and `prv j = j − 1 mod k`; the load at `prv j` is
     carried over from the previous option in `xY`), keeping the first minimum (`xBV`, `xBJ`);
   * `.write xBJ`: the chosen option;
   * `updInit`, `updPhase`: `LD[EID[ik + p]] += 1` for every position `p ∉ {J, prv J}` of the
     chosen option `J`;
   * `xB += k`.

The manuscript evaluates the options by a sliding window (remove the departing edge, add the
entering one); subtracting the two omitted loads from the total is the same `O(1)` per option.

**Registers**: `300–313` (Corollary 5 uses `250–291`, outerplanar package's `PairIds` `100–137`).
**Memory**: everything below `bOFF g k` (Corollary 5's layout up to the counts), then the load
table: `grSpace g k = bOFF g k + nE`.
-/

@[expose] public section

namespace STACS2027.Runtimes.Greedy

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost

/-! ### Registers -/

/-- The base of the load table. -/
abbrev xLD : ℕ := 300
/-- `ik`, the first occurrence of the current cycle. -/
abbrev xB : ℕ := 301
/-- The cycle counter. -/
abbrev xI : ℕ := 302
/-- The position counter (sum and update). -/
abbrev xP : ℕ := 303
/-- The option counter. -/
abbrev xJ : ℕ := 304
/-- The total load of the current cycle. -/
abbrev xTot : ℕ := 305
/-- The best load-sum so far. -/
abbrev xBV : ℕ := 306
/-- The best option so far. -/
abbrev xBJ : ℕ := 307
/-- Scratch: an occurrence. -/
abbrev xQ : ℕ := 308
/-- Scratch: an edge identifier. -/
abbrev xE : ℕ := 309
/-- Scratch: a load. -/
abbrev xX : ℕ := 310
/-- The load at the position before the current option. -/
abbrev xY : ℕ := 311
/-- The load-sum of the current option. -/
abbrev xV : ℕ := 312
/-- The position before the chosen option. -/
abbrev xBP : ℕ := 313

/-! ### Layout -/

/-- The memory of the machine: Corollary 5's layout up to `bOFF g k`, then the load table
(`nE` cells). -/
def grSpace (g : Graph) (k : ℕ) : ℕ := bOFF g k + (edgesOnCycles g k).length

theorem bEID_kt_le (g : Graph) (k : ℕ) : bEID g k + k * (cycles g k).length ≤ bOFF g k := by
  have := layout_eqs g k; omega

/-- The two regions read and written by the greedy phases fit below `S ≥ grSpace g k`. -/
theorem fitsG {g : Graph} {k S : ℕ} (hS : grSpace g k ≤ S) :
    bEID g k + k * (cycles g k).length ≤ S ∧ bOFF g k + (edgesOnCycles g k).length ≤ S := by
  have := bEID_kt_le g k; unfold grSpace at hS; omega

/-! ### The program -/

/-- Phase 5: the load table `LD` (`nE` fresh cells). -/
def stepLoad : Stmt := alloc xLD ZeroCost.gNE

/-- `xTot += LD[EID[xB + xP]]`. -/
def sumBody : Stmt :=
  .seq (.add xQ xB xP) (.seq (ld xE gEID xQ) (.seq (ld xX xLD xE) (.add xTot xTot xX)))

/-- The total load of the current cycle. -/
def sumPhase : Stmt := .seq (.const xTot 0) (forUp xP gK sumBody)

/-- `xY := LD[EID[xB + k − 1]]` (the load at the position before option `0`); `xBV := tot + 1`,
`xBJ := 0`. -/
def chooseInit : Stmt :=
  .seq (.add xQ xB gK) (.seq (dec xQ) (.seq (ld xE gEID xQ) (.seq (ld xY xLD xE)
    (.seq (addc xBV xTot 1) (.const xBJ 0)))))

/-- `xV := tot − LD(xJ) − xY` (the load-sum of option `xJ`), `xY := LD(xJ)`. -/
def readV : Stmt :=
  .seq (.add xQ xB xJ) (.seq (ld xE gEID xQ) (.seq (ld xX xLD xE) (.seq (.sub xV xTot xX)
    (.seq (.sub xV xV xY) (mov xY xX)))))

/-- A strictly better option. -/
def better : Stmt := .seq (mov xBV xV) (mov xBJ xJ)

/-- Option `xJ`. -/
def chooseBody : Stmt := .seq readV (ifLt xV xBV better .skip)

/-- The first option of minimum load-sum, in `xBJ`. -/
def choosePhase : Stmt := .seq chooseInit (forUp xJ gK chooseBody)

/-- `xBP := prv k xBJ`. -/
def updInit : Stmt := .seq (mov xBP xBJ) (.seq (.ifz xBJ (mov xBP gK) .skip) (dec xBP))

/-- `LD[EID[xB + xP]] += 1`. -/
def incLoad : Stmt :=
  .seq (.add xQ xB xP) (.seq (ld xE gEID xQ) (.seq (ld xX xLD xE) (.seq (inc xX) (st xLD xE xX))))

/-- Position `xP`: on the chosen path unless it is `xBJ` or `xBP`. -/
def updBody : Stmt := ifEq xP xBJ .skip (ifEq xP xBP .skip incLoad)

/-- The loads of the edges of the chosen path. -/
def updPhase : Stmt := forUp xP gK updBody

/-- One cycle of Algorithm 1. -/
def cycBody : Stmt :=
  .seq sumPhase (.seq choosePhase (.seq (.write xBJ) (.seq updInit (.seq updPhase (.add xB xB gK)))))

/-- Phase 6: Algorithm 1. -/
def stepGreedy : Stmt := .seq (.const xB 0) (forUp xI gT cycBody)

/-- **The machine of Lemma 15.** -/
def greedyProg : Stmt :=
  .seq stepInit (.seq stepMax (.seq stepDict (.seq stepEdges (.seq stepLoad stepGreedy))))

end STACS2027.Runtimes.Greedy
