module

public import Outerplanar.RAM.R0
public import Outerplanar.Algo.SolveCorrect
public import Outerplanar.RAM.BoundedHT

/-!
# Interfaces between the phases of the machine

The states between the phases of the machine of Theorem 21, fixed in
advance so that the phases can be written and verified independently:

* `GraphBase g c`: what every graph-level phase keeps from R0 (registers `rZERO`, `rONE`,
  `gM`, `gN`, `gNE`; the labels and the edge ends; free memory above `rFREE`);
* `R1Post` (after the depth-first search): CSR neighbour lists of `idEdges g`
  (`csrOff`, `csrAdj`), the arrays `pre`, `par` of `dfsOf g` and its preorder `ord`;
* `R2Post` (after the low points and heads): `lowOf`, `headOf`;
* `R3Post` (after bucketing the blocks): the blocks `blocksOf g`, concatenated, with their
  start offsets `blockStarts g`;
* the block solver: `BlockIn g E c` (the edges `E` of the current block at offset `gBS`, the
  labels, a zero scratch array `LOC` of `numV g` cells), `BlockGood E` (the hypothesis under
  which the polygon branch receives a polygon), and `BlockSpec k prog CB`: `prog` appends the
  labels of `(solveBlock k E).flatten` to the output in at most `CB * (|E| + 1)` steps, keeping
  the memory below the initial `rFREE` (so `LOC` is zero again), in **linear space**: an `HTB`
  triple for every bound `S ≥ F + CB * (|E| + 1)` (`F` the initial `rFREE`), with the final
  `rFREE` at most `F + CB * (|E| + 1)`;
* the polygon solver: `PolyIn pg n omap c` (the polygon's edges at `gPU`, `gPV`, the output map
  `omap` from positions to labels at `gOMAP`) and `PolySpecB k prog CP`: `prog` appends
  `(Poly.polyOut pg n k).flatten` mapped by `omap` in at most `CP * (n + |pg| + 1)` steps, in
  linear space (an `HTB` triple for every `S ≥ F + CP * (n + |pg| + 1)`, final `rFREE` at most
  that), the form the block solver uses.

Register blocks: R4 (the block loop and the block solver) uses `50–69` (the ear elimination's
interface `53–58`), the polygon solver `70–99`; scratch registers start at `rS = 100`.

* the ear elimination: `EarIn N L c` (the local graph at `gLU`, `gLV`) and `EarSpec prog CE`:
  on a local graph with an outerplanar Hamiltonian cycle, `prog` stores `Ear.earHam N L` at
  `gHAM` in at most `CE * (N + |L| + 1)` steps, touching only the addresses below
  `F + CE * (N + |L| + 1)` (`F` the initial `rFREE`; an `HTB` triple).
-/

@[expose] public section

namespace STACS2027.RAM

open STACS2027.Algo

/-! ### Registers of the block loop and the polygon solver -/

/-- Offset of the current block in the block edge arrays `gBU`, `gBV`. -/
abbrev gBS : ℕ := 50
/-- Number of edges of the current block. -/
abbrev gBL : ℕ := 51
/-- Base of the scratch array `LOC` (`numV g` cells, zero between blocks). -/
abbrev gLOC : ℕ := 52
/-- Number of positions `n` of the polygon. -/
abbrev gPN : ℕ := 60
/-- Number of edges of the polygon. -/
abbrev gPE : ℕ := 61
/-- Base of the first ends of the polygon's edges. -/
abbrev gPU : ℕ := 62
/-- Base of the second ends of the polygon's edges. -/
abbrev gPV : ℕ := 63
/-- Base of the output map (position ↦ label). -/
abbrev gOMAP : ℕ := 64
/-- First register the polygon solver may use for its own data (up to `99`). -/
abbrev gP0 : ℕ := 70

/-! ### Graph-level phases -/

/-- What the graph-level phases keep from R0. -/
structure GraphBase (g : Graph) (c : Config) : Prop where
  zero : c.reg rZERO = 0
  one : c.reg rONE = 1
  m : c.reg gM = g.length
  n : c.reg gN = numV g
  ne : c.reg gNE = (idEdges g).length
  lb : Arr c.mem (c.reg gLB) (labels g)
  eu : Arr c.mem (c.reg gEU) ((idEdges g).map Prod.fst)
  ev : Arr c.mem (c.reg gEV) ((idEdges g).map Prod.snd)
  free : ZeroFrom c.mem (c.reg rFREE)
  below : c.reg gLB + numV g ≤ c.reg rFREE ∧ c.reg gEU + (idEdges g).length ≤ c.reg rFREE ∧
    c.reg gEV + (idEdges g).length ≤ c.reg rFREE

/-- The state after R0 is a `GraphBase` (with the empty output). -/
theorem R0.R0Post.base {g : Graph} {c : Config} (h : R0.R0Post g c) : GraphBase g c where
  zero := h.zero
  one := h.one
  m := h.m
  n := h.n
  ne := h.ne
  lb := h.lb
  eu := h.eu
  ev := h.ev
  free := h.free
  below := by
    have hl := h.layout
    have h1 : (labels g).length ≤ 2 * g.length := by
      have := numV_le g
      simpa [numV] using this
    have h2 : (idEdges g).length ≤ g.length := length_idEdges_le g
    have h3 : numV g = (labels g).length := rfl
    omega

/-- CSR offsets: entry `v` (for `v ≤ N`) is the total length of the neighbour lists of the
vertices below `v`. -/
def csrOff (E : List Edge) (N : ℕ) : List ℕ :=
  (List.range (N + 1)).map fun v => ((List.range v).map fun u => (nbOf E u).length).sum

/-- CSR neighbour entries: the neighbour lists of `0, …, N - 1`, concatenated. -/
def csrAdj (E : List Edge) (N : ℕ) : List ℕ := (List.range N).flatMap (nbOf E)

/-- The state after R1 (neighbour lists and the depth-first search). -/
structure R1Post (g : Graph) (c : Config) : Prop where
  base : GraphBase g c
  off : Arr c.mem (c.reg gOFF) (csrOff (idEdges g) (numV g))
  adj : Arr c.mem (c.reg gADJ) (csrAdj (idEdges g) (numV g))
  pre : Tab c.mem (c.reg gPRE) (numV g) (dfsOf g).pre
  par : Tab c.mem (c.reg gPAR) (numV g) (dfsOf g).par
  ord : Arr c.mem (c.reg gORD) (dfsOf g).ord
  below : c.reg gOFF + (numV g + 1) ≤ c.reg rFREE ∧
    c.reg gADJ + (csrAdj (idEdges g) (numV g)).length ≤ c.reg rFREE ∧
    c.reg gPRE + numV g ≤ c.reg rFREE ∧ c.reg gPAR + numV g ≤ c.reg rFREE ∧
    c.reg gORD + (dfsOf g).ord.length ≤ c.reg rFREE

/-- The low points of the search. -/
def lowsOf (g : Graph) : ℕ → ℕ := lowOf (dfsOf g) (nbOf (idEdges g))

/-- The heads of the search. -/
def headsOf (g : Graph) : ℕ → ℕ := headOf (dfsOf g) (lowsOf g)

/-- The state after R2 (low points and heads). -/
structure R2Post (g : Graph) (c : Config) : Prop where
  r1 : R1Post g c
  low : Tab c.mem (c.reg gLOW) (numV g) (lowsOf g)
  head : Tab c.mem (c.reg gHEAD) (numV g) (headsOf g)
  below : c.reg gLOW + numV g ≤ c.reg rFREE ∧ c.reg gHEAD + numV g ≤ c.reg rFREE

/-- The start offsets of the blocks `0, …, N - 1` in their concatenation (and the total
length last). -/
def blockStarts (g : Graph) : List ℕ :=
  (List.range (numV g + 1)).map fun h => (((blocksOf g).take h).map List.length).sum

/-- The state after R3 (the blocks, bucketed by head). -/
structure R3Post (g : Graph) (c : Config) : Prop where
  base : GraphBase g c
  bst : Arr c.mem (c.reg gBST) (blockStarts g)
  bu : Arr c.mem (c.reg gBU) ((blocksOf g).flatten.map Prod.fst)
  bv : Arr c.mem (c.reg gBV) ((blocksOf g).flatten.map Prod.snd)
  below : c.reg gBST + (numV g + 1) ≤ c.reg rFREE ∧
    c.reg gBU + (blocksOf g).flatten.length ≤ c.reg rFREE ∧
    c.reg gBV + (blocksOf g).flatten.length ≤ c.reg rFREE

/-! ### The block solver -/

/-- The state on entry to the block solver, for the block `E`. -/
structure BlockIn (g : Graph) (E : List Edge) (c : Config) : Prop where
  zero : c.reg rZERO = 0
  one : c.reg rONE = 1
  n : c.reg gN = numV g
  lb : Arr c.mem (c.reg gLB) (labels g)
  bl : c.reg gBL = E.length
  bu : Arr c.mem (c.reg gBU + c.reg gBS) (E.map Prod.fst)
  bv : Arr c.mem (c.reg gBV + c.reg gBS) (E.map Prod.snd)
  loc : Arr c.mem (c.reg gLOC) (List.replicate (numV g) 0)
  free : ZeroFrom c.mem (c.reg rFREE)
  below : c.reg gLB + numV g ≤ c.reg rFREE ∧ c.reg gBU + c.reg gBS + E.length ≤ c.reg rFREE ∧
    c.reg gBV + c.reg gBS + E.length ≤ c.reg rFREE ∧ c.reg gLOC + numV g ≤ c.reg rFREE

/-- The hypothesis on a block under which the polygon branch of `solveBlock` receives a
polygon (it holds for the blocks of a `K_{2,3}`-minor-free graph, given Lemma 19). -/
def BlockGood (E : List Edge) : Prop :=
  3 ≤ (blockVerts E).length → ¬ ((blockVerts E).length = 4 ∧ E.length = 6) →
    IsPolygon (localEdges (Ear.earHam (blockVerts E).length (localEdges (blockVerts E) E))
      (localEdges (blockVerts E) E)) (blockVerts E).length

/-- The specification of the block solver `prog`: on a block `E` (ids below `numV g`, smaller
end first, each edge once) satisfying `BlockGood`, it appends the labels of
`(solveBlock k E).flatten` to the output within `CB * (|E| + 1)` steps, allocating fresh
memory only and restoring the memory below the initial `rFREE`, in **linear space**: the run
touches only addresses below any bound `S ≥ F + CB * (|E| + 1)` (`F` the initial `rFREE`), and
the final `rFREE` is at most `F + CB * (|E| + 1)`. -/
def BlockSpec (k : ℕ) (prog : Stmt) (CB : ℕ) : Prop :=
  ∀ (S : ℕ) (g : Graph) (E : List Edge) (c₀ : Config), (∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) →
    E.Nodup → BlockGood E → c₀.reg rFREE + CB * (E.length + 1) ≤ S →
    HTB S prog (fun c => BlockIn g E c ∧ c = c₀)
      (fun c => c.out = c₀.out ++ (solveBlock k E).flatten.map (labelOf g) ∧
        SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧ ZeroFrom c.mem (c.reg rFREE) ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE ≤ c₀.reg rFREE + CB * (E.length + 1))
      (CB * (E.length + 1))

/-! ### The polygon solver -/

/-- The state on entry to the polygon solver: the polygon `pg` on `n` positions and the
output map `omap` (position ↦ label). -/
structure PolyIn (pg : Graph) (n : ℕ) (omap : List ℕ) (c : Config) : Prop where
  zero : c.reg rZERO = 0
  one : c.reg rONE = 1
  pn : c.reg gPN = n
  pe : c.reg gPE = pg.length
  pu : Arr c.mem (c.reg gPU) (pg.map Prod.fst)
  pv : Arr c.mem (c.reg gPV) (pg.map Prod.snd)
  om : Arr c.mem (c.reg gOMAP) omap
  omap_len : omap.length = n
  free : ZeroFrom c.mem (c.reg rFREE)
  below : c.reg gPU + pg.length ≤ c.reg rFREE ∧ c.reg gPV + pg.length ≤ c.reg rFREE ∧
    c.reg gOMAP + n ≤ c.reg rFREE

/-- **The specification of the polygon solver in linear space** (in the form of `EarSpec`): on a
polygon (edges smaller end first, each once), `prog`
appends `(Poly.polyOut pg n k).flatten` mapped by `omap` within `CP * (n + |pg| + 1)` steps,
allocating fresh memory only, and the run touches only addresses below any bound
`S ≥ F + CP * (n + |pg| + 1)` (`F` the initial `rFREE`); the final `rFREE` is at most
`F + CP * (n + |pg| + 1)`. -/
def PolySpecB (k : ℕ) (prog : Stmt) (CP : ℕ) : Prop :=
  ∀ (S : ℕ) (pg : Graph) (n : ℕ) (omap : List ℕ) (c₀ : Config), IsPolygon pg n →
    (∀ e ∈ pg, e.1 < e.2) → pg.Nodup → c₀.reg rFREE + CP * (n + pg.length + 1) ≤ S →
    HTB S prog (fun c => PolyIn pg n omap c ∧ c = c₀)
      (fun c => c.out = c₀.out ++ (Poly.polyOut pg n k).flatten.map (fun p => omap.getD p 0) ∧
        SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧ ZeroFrom c.mem (c.reg rFREE) ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE ≤ c₀.reg rFREE + CP * (n + pg.length + 1))
      (CP * (n + pg.length + 1))

/-! ### The ear elimination (inside the block solver) -/

/-- Number of vertices `N` of the current block (= `|blockVerts E|`). -/
abbrev gVN : ℕ := 53
/-- Base of the block's vertex list `blockVerts E`. -/
abbrev gVS : ℕ := 54
/-- Number of local edges. -/
abbrev gLN : ℕ := 55
/-- Base of the first ends of the local edges. -/
abbrev gLU : ℕ := 56
/-- Base of the second ends of the local edges. -/
abbrev gLV : ℕ := 57
/-- Base of the Hamiltonian cycle found by the ear elimination (`N` cells). -/
abbrev gHAM : ℕ := 58
/-- A register the block solver may use for its own data (as are `65–69`). -/
abbrev gB1 : ℕ := 59

/-- The state on entry to the ear elimination: the local graph `L` on `0, …, N - 1`. -/
structure EarIn (N : ℕ) (L : List Edge) (c : Config) : Prop where
  zero : c.reg rZERO = 0
  one : c.reg rONE = 1
  vn : c.reg gVN = N
  ln : c.reg gLN = L.length
  lu : Arr c.mem (c.reg gLU) (L.map Prod.fst)
  lv : Arr c.mem (c.reg gLV) (L.map Prod.snd)
  free : ZeroFrom c.mem (c.reg rFREE)
  below : c.reg gLU + L.length ≤ c.reg rFREE ∧ c.reg gLV + L.length ≤ c.reg rFREE

/-- The specification of the ear elimination program `prog`: on a local graph (edges smaller
end first, ends below `N`, each edge once, `N ≥ 3`) with an outerplanar Hamiltonian cycle `ham0`
through all of `0, …, N - 1`, it stores `Ear.earHam N L` at a fresh `gHAM` within
`CE * (N + |L| + 1)` steps, and in **linear space**: the run touches only addresses below any
bound `S ≥ F + CE * (N + |L| + 1)` (`F` the initial `rFREE`), and the final `rFREE` is at most
`F + CE * (N + |L| + 1)`. It allocates fresh memory only and writes no output. -/
def EarSpec (prog : Stmt) (CE : ℕ) : Prop :=
  ∀ (S N : ℕ) (L : List Edge) (c₀ : Config), (∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) → L.Nodup → 3 ≤ N →
    (∃ ham0, OuterplanarHam L ham0 ∧ ∀ v, v < N → v ∈ ham0) →
    c₀.reg rFREE + CE * (N + L.length + 1) ≤ S →
    HTB S prog (fun c => EarIn N L c ∧ c = c₀)
      (fun c => Arr c.mem (c.reg gHAM) (Ear.earHam N L) ∧ c.reg gHAM + N ≤ c.reg rFREE ∧
        c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        ZeroFrom c.mem (c.reg rFREE) ∧ c₀.reg rFREE ≤ c.reg rFREE ∧
        c.reg rFREE ≤ c₀.reg rFREE + CE * (N + L.length + 1))
      (CE * (N + L.length + 1))

end STACS2027.RAM
