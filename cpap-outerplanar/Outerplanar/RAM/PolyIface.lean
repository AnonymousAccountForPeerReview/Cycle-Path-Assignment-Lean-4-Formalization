module

public import Outerplanar.RAM.Iface
public import Outerplanar.Algo.Poly

/-!
# Interfaces between the phases of the polygon solver

The polygon solver (specification `Poly.polyOut`, interface `PolySpecB`) runs in four phases,
each a `PolyPhaseB` triple (linear time and space).
With `S = segOrder pg n` (the segments, smaller first) and `NS = |S|`:

* **P1 (structure)** → `Poly1Post`: the segments `S` (arrays of their ends `gSA`, `gSB`), the
  face vertices of every segment, concatenated in the order of `S` (`gFV`), with their offsets
  `gFOFF`, and parallel to `gFV` the slot ids `gFSID` (`fsidCat`: for the face vertex `q` of a
  face, `1 +` the index in `S` of the slot from `q` to the next face vertex if it is a child
  segment, `0` for a side and for the last face vertex). No table is indexed by pairs of
  positions: the phases look slots up by their index in the face;
* **P2 (cycles)** → `Poly2Post`: the pool `Poly.pool` (each cycle has `k` entries; flattened
  at `gPOOL`), the start of the cycles of each top segment (`gTST`, prefix sums of the
  `rpF … k` counts, so `topIdx s` is a range by `topIdx_eq`), and the boundary lists `bnd s`,
  concatenated (`gBIDX`) with offsets `gBOFF`;
* **P3 (tables)** → `Poly3Post`: the tables `table s α` and the minimizing `argTab s α` for
  `α < k ^ |bnd s|`, concatenated in the order of `S` (`gTAB`, `gARG`), with offsets `gTOFF`;
* **P4 (backtracking and output)**: `backtrack`, `valOf`, and the output.

Registers `70–83` hold the interface data below; `84–99` are free for the phases' own use
(clobbered by later phases).
-/

@[expose] public section

namespace STACS2027.RAM

open STACS2027.Poly

/-! ### Registers -/

/-- Number of segments. -/
abbrev gNS : ℕ := 70
/-- Base of the first ends of the segments (in `segOrder`). -/
abbrev gSA : ℕ := 71
/-- Base of the second ends of the segments. -/
abbrev gSB : ℕ := 72
/-- Base of the slot ids (parallel to the face vertices `gFV`, `|faceCat|` cells). -/
abbrev gFSID : ℕ := 73
/-- Base of the face offsets (`NS + 1` cells). -/
abbrev gFOFF : ℕ := 74
/-- Base of the concatenated face vertices. -/
abbrev gFV : ℕ := 75
/-- Number of cycles in the pool. -/
abbrev gNP : ℕ := 76
/-- Base of the flattened pool. -/
abbrev gPOOL : ℕ := 77
/-- Base of the top-cycle starts (`NS + 1` cells). -/
abbrev gTST : ℕ := 78
/-- Base of the boundary-list offsets (`NS + 1` cells). -/
abbrev gBOFF : ℕ := 79
/-- Base of the concatenated boundary lists. -/
abbrev gBIDX : ℕ := 80
/-- Base of the table offsets (`NS + 1` cells). -/
abbrev gTOFF : ℕ := 81
/-- Base of the concatenated tables. -/
abbrev gTAB : ℕ := 82
/-- Base of the concatenated minimizing configurations. -/
abbrev gARG : ℕ := 83
/-- First register free for a polygon phase's own use (up to `99`). -/
abbrev gPx : ℕ := 84

/-! ### Abstract data -/

/-- Prefix sums: `[0, l₀, l₀ + l₁, …, ∑ l]` (length `|l| + 1`). -/
def prefixSums (l : List ℕ) : List ℕ := (List.range (l.length + 1)).map fun i => (l.take i).sum

/-- The id of a pair of positions: `1 +` its index in `segOrder` if it is a segment, else `0`. -/
def segId (pg : Graph) (n : ℕ) (p : ℕ × ℕ) : ℕ :=
  if p ∈ segOrder pg n then (segOrder pg n).idxOf p + 1 else 0

/-- The slot ids of the face of `s`, one per face vertex `q`: the id of the slot from `q` to the
next face vertex (`0` for a side, and for the last face vertex, paired with `0`). -/
def faceSids (pg : Graph) (n : ℕ) (s : ℕ × ℕ) : List ℕ :=
  (List.range (faceVerts pg n s).length).map fun q =>
    segId pg n ((faceVerts pg n s).getD q 0, (faceVerts pg n s).getD (q + 1) 0)

/-- The slot ids of all faces, concatenated in the order of `segOrder` (parallel to `faceCat`). -/
def fsidCat (pg : Graph) (n : ℕ) : List ℕ := (segOrder pg n).flatMap (faceSids pg n)

/-- The face offsets. -/
def faceOffs (pg : Graph) (n : ℕ) : List ℕ :=
  prefixSums ((segOrder pg n).map fun s => (faceVerts pg n s).length)

/-- The face vertices of all segments, concatenated. -/
def faceCat (pg : Graph) (n : ℕ) : List ℕ := (segOrder pg n).flatMap (faceVerts pg n)

/-- The starts of the cycles of each top segment in the pool. -/
def topStarts (pg : Graph) (n k : ℕ) : List ℕ :=
  prefixSums ((segOrder pg n).map fun s => (rpF pg n k n s.1 s.2 k).length)

/-- The boundary-list offsets. -/
def bndOffs (pg : Graph) (n k : ℕ) : List ℕ :=
  prefixSums ((segOrder pg n).map fun s => (bnd pg n k s).length)

/-- The boundary lists, concatenated. -/
def bndCat (pg : Graph) (n k : ℕ) : List ℕ := (segOrder pg n).flatMap (bnd pg n k)

/-- The table offsets. -/
def tabOffs (pg : Graph) (n k : ℕ) : List ℕ :=
  prefixSums ((segOrder pg n).map fun s => k ^ (bnd pg n k s).length)

/-- The tables, concatenated. -/
def tabCat (pg : Graph) (n k : ℕ) : List ℕ :=
  (segOrder pg n).flatMap fun s => (List.range (k ^ (bnd pg n k s).length)).map (table pg n k s)

/-- The minimizing configurations, concatenated. -/
def argCat (pg : Graph) (n k : ℕ) : List ℕ :=
  (segOrder pg n).flatMap fun s => (List.range (k ^ (bnd pg n k s).length)).map (argTab pg n k s)

/-! ### The states between the phases -/

/-- The state after P1. -/
structure Poly1Post (pg : Graph) (n : ℕ) (omap : List ℕ) (c : Config) : Prop where
  base : PolyIn pg n omap c
  ns : c.reg gNS = (segOrder pg n).length
  sa : Arr c.mem (c.reg gSA) ((segOrder pg n).map Prod.fst)
  sb : Arr c.mem (c.reg gSB) ((segOrder pg n).map Prod.snd)
  fsid : Arr c.mem (c.reg gFSID) (fsidCat pg n)
  foff : Arr c.mem (c.reg gFOFF) (faceOffs pg n)
  fv : Arr c.mem (c.reg gFV) (faceCat pg n)
  below : c.reg gSA + (segOrder pg n).length ≤ c.reg rFREE ∧
    c.reg gSB + (segOrder pg n).length ≤ c.reg rFREE ∧
    c.reg gFSID + (fsidCat pg n).length ≤ c.reg rFREE ∧
    c.reg gFOFF + ((segOrder pg n).length + 1) ≤ c.reg rFREE ∧
    c.reg gFV + (faceCat pg n).length ≤ c.reg rFREE

/-- The state after P2. -/
structure Poly2Post (pg : Graph) (n k : ℕ) (omap : List ℕ) (c : Config) : Prop where
  p1 : Poly1Post pg n omap c
  np : c.reg gNP = (pool pg n k).length
  pl : Arr c.mem (c.reg gPOOL) (pool pg n k).flatten
  tst : Arr c.mem (c.reg gTST) (topStarts pg n k)
  boff : Arr c.mem (c.reg gBOFF) (bndOffs pg n k)
  bidx : Arr c.mem (c.reg gBIDX) (bndCat pg n k)
  below : c.reg gPOOL + (pool pg n k).flatten.length ≤ c.reg rFREE ∧
    c.reg gTST + ((segOrder pg n).length + 1) ≤ c.reg rFREE ∧
    c.reg gBOFF + ((segOrder pg n).length + 1) ≤ c.reg rFREE ∧
    c.reg gBIDX + (bndCat pg n k).length ≤ c.reg rFREE

/-- The state after P3. -/
structure Poly3Post (pg : Graph) (n k : ℕ) (omap : List ℕ) (c : Config) : Prop where
  p2 : Poly2Post pg n k omap c
  toff : Arr c.mem (c.reg gTOFF) (tabOffs pg n k)
  tb : Arr c.mem (c.reg gTAB) (tabCat pg n k)
  ag : Arr c.mem (c.reg gARG) (argCat pg n k)
  below : c.reg gTOFF + ((segOrder pg n).length + 1) ≤ c.reg rFREE ∧
    c.reg gTAB + (tabCat pg n k).length ≤ c.reg rFREE ∧
    c.reg gARG + (argCat pg n k).length ≤ c.reg rFREE

/-- The common shape of the phase triples: for every bound `S` that leaves room for the phase's
fresh memory (`c₀.reg rFREE + C * (n + |pg| + 1) ≤ S`), from `Pre` (and the ghost `c₀`) the
phase reaches `Post` by an `ExecB S` run (every load and store below `S`) within
`C * (n + |pg| + 1)` steps, without output, storing only at or above the initial free pointer,
which moves up by at most `C * (n + |pg| + 1)`. -/
def PolyPhaseB (prog : Stmt) (pg : Graph) (n : ℕ) (Pre Post : Config → Prop) (C : ℕ) : Prop :=
  ∀ (S : ℕ) (c₀ : Config), c₀.reg rFREE + C * (n + pg.length + 1) ≤ S →
    HTB S prog (fun c => Pre c ∧ c = c₀)
      (fun c => Post c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE ≤ c₀.reg rFREE + C * (n + pg.length + 1))
      (C * (n + pg.length + 1))

end STACS2027.RAM
