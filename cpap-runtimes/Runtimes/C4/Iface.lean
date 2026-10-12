module

public import Runtimes.C4.Grouped
public import Outerplanar.RAM.R1Spec

/-!
# Four-cycle listing: the interfaces between the RAM phases

The machine is `r0 ; r1 ; peel ; orient ; size ; enum ; emit`.
The phases R0 and R1 of the outerplanar package package are reused as they are; the states between
the new phases are fixed here, so that the phases can be written and verified independently.

* `C4Base g c`: what every new phase keeps — R1's post (`R1Post`: the labels, the id edges,
  the CSR offsets `csrOff (idEdges g) N` at `gOFF` and neighbour entries at `gADJ`, i.e. the
  lists `nb g v` at `gADJ + R1.ps (idEdges g) v`, free memory from `rFREE`).
* `PeelPost g c` (after PEEL): the positions `peelPos g` at `gPOS` (`N` cells).
* `OrientPost g c` (after ORIENT): the out-degrees `|outL g (peelPos g) v|` at `gODEG`
  (`N` cells) and the out-lists `outL g (peelPos g) v` at `gOADJ + R1.ps (idEdges g) v`
  (inside the segment of `nb g v`; `gOADJ` has `2 |E|` cells).
* `SizePost g c` (after SIZE): `gP = numPaths g (peelPos g)`. ENUM allocates its arrays (the
  triples, the sort, the stamps and list heads, the node pool, the cycle array) itself, at
  its initial `rFREE`, so that every phase stores only at or above its initial `rFREE`.
* `EnumPost g c` (after ENUM): the cycles `(enumOutS g).flatten` (in labels, four entries per
  cycle, `length_flatten_enumOutS`; a permutation of `cycles g 4`, `enumOutS_perm`) at `gCYC`,
  their number in `gT`.

Each phase `ph ∈ {peel, orient, size, enum}` is specified within a space bound `S` above its
layout (`HTB S`):
`HTB S ph (fun c => Pre g c ∧ c = c₀) (fun c => Post g c ∧ c.out = c₀.out ∧
SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧ c₀.reg rFREE ≤ c.reg rFREE ∧
c.reg rFREE ≤ c₀.reg rFREE + size) (C * (g.length + 1 + …))` for
`c₀.reg rFREE + size ≤ S`, writing only `rT`, `rFREE`, the block `30–49` below and scratch
registers `≥ 100`.

Registers (the block `30–49`, as R2/R3 of outerplanar package are not run in this machine):
`gCUR gDEL gBH gPOS` (PEEL), `gODEG gOADJ` (ORIENT), `gP` (SIZE),
`gTX gTY gTZ gSRT gSTP gHDS gPOOL gCYC gT gNP` (ENUM); `47–49` are spare.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM

/-! ### Registers -/

/-- PEEL: base of the current degrees `CUR` (`N` cells). -/
abbrev gCUR : ℕ := 30
/-- PEEL: base of the removed flags `DEL` (`N` cells). -/
abbrev gDEL : ℕ := 31
/-- PEEL: base of the bucket heads `BH` (`N` cells; `0` = empty bucket). -/
abbrev gBH : ℕ := 32
/-- PEEL: base of the positions `POS` (`N` cells): `POS[v] = peelPos g v`. -/
abbrev gPOS : ℕ := 33
/-- ORIENT: base of the out-degrees `ODEG` (`N` cells). -/
abbrev gODEG : ℕ := 34
/-- ORIENT: base of the out-lists `OADJ` (`2 |E|` cells, segment of `v` at `OFF[v]`). -/
abbrev gOADJ : ℕ := 35
/-- SIZE: the number of inserted 2-paths `numPaths g (peelPos g)`. -/
abbrev gP : ℕ := 36
/-- ENUM: base of the first key components `X` of the inserted 2-paths (`P` cells; the keys
of the counting sort). -/
abbrev gTX : ℕ := 37
/-- ENUM: base of the second key components `Y` (`P` cells). -/
abbrev gTY : ℕ := 38
/-- ENUM: base of the node pool `POOL` (`2 P` cells: centre, next). -/
abbrev gPOOL : ℕ := 39
/-- ENUM: base of the cycle array `CYC` (four cells per reported cycle). -/
abbrev gCYC : ℕ := 40
/-- ENUM: the number of reported cycles. -/
abbrev gT : ℕ := 41
/-- ENUM: the number of written triples (generation), twice the number of inserted 2-paths
(report walk: the next node is `POOL + NP`). -/
abbrev gNP : ℕ := 42
/-- ENUM: base of the centres `Z` (`P` cells). -/
abbrev gTZ : ℕ := 43
/-- ENUM: base of the indices sorted by the first key component (`P` cells). -/
abbrev gSRT : ℕ := 44
/-- ENUM: base of the time stamps `STP` (`N` cells; `STP[y] = x + 1` iff the list head of `y`
is valid for the current first component `x`). -/
abbrev gSTP : ℕ := 45
/-- ENUM: base of the list heads `HDS` (`N` cells; `0` = empty list). -/
abbrev gHDS : ℕ := 46

/-! ### Phase interfaces -/

/-- What every phase of the four-cycle machine keeps: R1's post. -/
structure C4Base (g : Graph) (c : Config) : Prop where
  r1 : R1Post g c

/-- The state after PEEL: the positions in the peeling order. -/
structure PeelPost (g : Graph) (c : Config) : Prop where
  base : C4Base g c
  pos : Tab c.mem (c.reg gPOS) (numV g) (peelPos g)
  below : c.reg gPOS + numV g ≤ c.reg rFREE

/-- The state after ORIENT: the out-degrees and the out-lists of the peeling orientation. -/
structure OrientPost (g : Graph) (c : Config) : Prop where
  peel : PeelPost g c
  odeg : Tab c.mem (c.reg gODEG) (numV g) fun v => (outL g (peelPos g) v).length
  oadj : ∀ v < numV g, Arr c.mem (c.reg gOADJ + R1.ps (idEdges g) v) (outL g (peelPos g) v)
  below : c.reg gODEG + numV g ≤ c.reg rFREE ∧
    c.reg gOADJ + 2 * (idEdges g).length ≤ c.reg rFREE

/-- The state after SIZE: the number of inserted 2-paths. -/
structure SizePost (g : Graph) (c : Config) : Prop where
  orient : OrientPost g c
  p : c.reg gP = numPaths g (peelPos g)

/-- The state after ENUM: the reported cycles, in labels, concatenated. -/
structure EnumPost (g : Graph) (c : Config) : Prop where
  base : C4Base g c
  t : c.reg gT = (enumOutS g).length
  cyc : Arr c.mem (c.reg gCYC) (enumOutS g).flatten
  below : c.reg gCYC + 4 * (enumOutS g).length ≤ c.reg rFREE

end STACS2027.Runtimes.C4
