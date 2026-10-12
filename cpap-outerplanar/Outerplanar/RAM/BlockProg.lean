module

public import Outerplanar.RAM.BlockAbs
import Mathlib.Tactic

/-!
# The block solver: the program

On entry (`BlockIn g E c`): the block's edges `E` at `gBU + gBS`, `gBV + gBS` (`m = gBL`
edges), the labels at `gLB`, a zero scratch array `LOC` of `numV g` cells at `gLOC`, all below
`F = rFREE`. With `m = |E|`, the program `blockProg k earProg polyProg`:

1. `initB`: allocates the copies `CU`, `CV` of the edges (`m` cells each, at `F`, `F + m`),
   the vertex array `VS` (`2m` cells, at `F + 2m`, `gVS`) and the local edges `LU`, `LV`
   (`m` cells each, at `F + 4m`, `F + 5m`; `gLU`, `gLV`, `gLN := m`); `gVN := 0`;
2. `copy`: copies the edges to `CU`, `CV` (the edge arrays might share cells with `LOC`,
   which the next steps write: the interface does not exclude it);
3. `collect`: the vertices `blockVerts E` in order of first appearance into `VS`
   (`N = gVN` of them), with `LOC[v] := ` local id `+ 1` on first sight;
4. `localE`: the local edges `edge (LOC[a] - 1) (LOC[b] - 1)` into `LU`, `LV`;
5. `reset`: `LOC[v] := 0` for `v ∈ vs` (from here on the memory below `F` is the initial
   one, so the labels can be read safely);
6. `dispatch`: `N ≤ 2`: nothing; `N = 4 ∧ m = 6`: `k4Prog k` writes the labels of the
   `K₄` patterns `k4Base k`; otherwise `polyBranch`: the ear elimination `earProg`
   (Hamiltonian cycle at `gHAM`), the allocations `pInit` (`gPN := N`, `gPE := m`), the
   positions `POS[ham[p]] := p` (`posLoop`), the polygon `edge (POS[u]) (POS[v])` at `gPU`,
   `gPV` (`pgLoop`), the output map `OMAP[p] := labels[vs[ham[p]]]` at `gOMAP` (`omLoop`), and
   the polygon solver `polyProg`.

`blockProg_wregs`: the program writes only `rT`, `rFREE` and registers `≥ gVN`.
-/

@[expose] public section

namespace STACS2027.RAM.Block

open STACS2027.Algo

/-! ### Registers -/

/-- Base of the positions array (`N` cells). -/
abbrev gPOS : ℕ := 65
/-- Base of the copy of the first ends of the edges. -/
abbrev gCU : ℕ := 66
/-- Base of the copy of the second ends of the edges. -/
abbrev gCV : ℕ := 67
/-- Loop counter. -/
abbrev rI : ℕ := 100
/-- Scratch: a vertex. -/
abbrev rA : ℕ := 101
/-- Scratch: a vertex. -/
abbrev rB : ℕ := 102
/-- Scratch: first end of a renamed edge. -/
abbrev rU : ℕ := 103
/-- Scratch: second end of a renamed edge. -/
abbrev rV : ℕ := 104
/-- Scratch: a test value. -/
abbrev rX : ℕ := 105
/-- Scratch: a test value. -/
abbrev rY : ℕ := 106
/-- Scratch: a constant. -/
abbrev rC : ℕ := 107
/-- Scratch: an address offset. -/
abbrev rP : ℕ := 108
/-- Scratch: `2m`. -/
abbrev r2L : ℕ := 109

/-! ### Steps 1–5 -/

/-- Step 1: the allocations. -/
def initB : Stmt :=
  .seq (alloc gCU gBL) (.seq (alloc gCV gBL) (.seq (.add r2L gBL gBL) (.seq (alloc gVS r2L)
    (.seq (alloc gLU gBL) (.seq (alloc gLV gBL) (.seq (mov gLN gBL) (.const gVN 0)))))))

/-- Copy edge `rI`. -/
def copyBody : Stmt :=
  .seq (.add rP gBS rI) (.seq (ld rA gBU rP) (.seq (st gCU rI rA) (.seq (ld rA gBV rP) (st gCV rI rA))))

/-- Step 2: the copies of the edges. -/
def copy : Stmt := forUp rI gBL copyBody

/-- Visit the vertex in register `x`: if `LOC[x] = 0`, append `x` to `VS` and set
`LOC[x] := N`. -/
def visit (x : ℕ) : Stmt :=
  .seq (ld rY gLOC x) (.ifz rY (.seq (st gVS gVN x) (.seq (inc gVN) (st gLOC x gVN))) .skip)

/-- Visit both ends of edge `rI`. -/
def collBody : Stmt := .seq (ld rA gCU rI) (.seq (ld rB gCV rI) (.seq (visit rA) (visit rB)))

/-- Step 3: the vertices. -/
def collect : Stmt := forUp rI gBL collBody

/-- `(rU, rV) := (min, max)`. -/
def order : Stmt := ifLt rV rU (swap rU rV) .skip

/-- The local ids `LOC[a] - 1`, `LOC[b] - 1` of the ends of edge `rI`. -/
def locRead : Stmt :=
  .seq (ld rA gCU rI) (.seq (ld rU gLOC rA) (.seq (dec rU) (.seq (ld rB gCV rI)
    (.seq (ld rV gLOC rB) (dec rV)))))

/-- The local edge of edge `rI`. -/
def locBody : Stmt := .seq locRead (.seq order (.seq (st gLU rI rU) (st gLV rI rV)))

/-- Step 4: the local edges. -/
def localE : Stmt := forUp rI gBL locBody

/-- Reset `LOC` at the vertex `VS[rI]`. -/
def resBody : Stmt := .seq (ld rA gVS rI) (st gLOC rA rZERO)

/-- Step 5: `LOC` is zero again. -/
def reset : Stmt := forUp rI gVN resBody

/-! ### Step 6: the dispatch -/

/-- Write the label of `vs[i]`. -/
def wlab (i : ℕ) : Stmt := .seq (.const rI i) (.seq (ld rA gVS rI) (.seq (ld rA gLB rA) (.write rA)))

/-- Write the labels of `vs[i]` for the indices `l`. -/
def wlabs (l : List ℕ) : Stmt := l.foldr (fun i s => .seq (wlab i) s) .skip

/-- The `K₄` branch. -/
def k4Prog (k : ℕ) : Stmt := wlabs (k4Base k).flatten

/-- Allocations of the polygon branch: `POS` (`N` cells), `PU`, `PV` (`m` cells each), `OMAP`
(`N` cells); `gPE := m`, `gPN := N`. -/
def pInit : Stmt :=
  .seq (alloc gPOS gVN) (.seq (alloc gPU gLN) (.seq (alloc gPV gLN) (.seq (alloc gOMAP gVN)
    (.seq (mov gPE gLN) (mov gPN gVN)))))

/-- `POS[HAM[rI]] := rI`. -/
def posBody : Stmt := .seq (ld rA gHAM rI) (st gPOS rA rI)

/-- The positions on the Hamiltonian cycle. -/
def posLoop : Stmt := forUp rI gVN posBody

/-- The positions `POS[u]`, `POS[v]` of the ends of local edge `rI`. -/
def pgRead : Stmt := .seq (ld rA gLU rI) (.seq (ld rU gPOS rA) (.seq (ld rB gLV rI) (ld rV gPOS rB)))

/-- The polygon edge of local edge `rI`. -/
def pgBody : Stmt := .seq pgRead (.seq order (.seq (st gPU rI rU) (st gPV rI rV)))

/-- The polygon. -/
def pgLoop : Stmt := forUp rI gLN pgBody

/-- `OMAP[rI] := labels[VS[HAM[rI]]]`. -/
def omBody : Stmt := .seq (ld rA gHAM rI) (.seq (ld rA gVS rA) (.seq (ld rA gLB rA) (st gOMAP rI rA)))

/-- The output map. -/
def omLoop : Stmt := forUp rI gVN omBody

/-- The polygon branch. -/
def polyBranch (earProg polyProg : Stmt) : Stmt :=
  .seq earProg (.seq pInit (.seq posLoop (.seq pgLoop (.seq omLoop polyProg))))

/-- `rX := N - 2` (zero iff `N ≤ 2`). -/
def smallTest : Stmt := .seq (.const rC 2) (.sub rX gVN rC)

/-- `rX := |N - 4| + |m - 6|` (zero iff `N = 4 ∧ m = 6`). -/
def k4Test : Stmt :=
  .seq (.const rC 4) (.seq (.sub rX gVN rC) (.seq (.sub rY rC gVN) (.seq (.add rX rX rY)
    (.seq (.const rC 6) (.seq (.sub rY gBL rC) (.seq (.add rX rX rY) (.seq (.sub rY rC gBL)
      (.add rX rX rY))))))))

/-- Step 6. -/
def dispatch (k : ℕ) (earProg polyProg : Stmt) : Stmt :=
  .seq smallTest (.ifz rX .skip (.seq k4Test (.ifz rX (k4Prog k) (polyBranch earProg polyProg))))

/-- **The block solver** for cycle length `k`, given the ear elimination `earProg` and the
polygon solver `polyProg`. -/
def blockProg (k : ℕ) (earProg polyProg : Stmt) : Stmt :=
  .seq initB (.seq copy (.seq collect (.seq localE (.seq reset (dispatch k earProg polyProg)))))

/-! ### Footprint -/

theorem wregs_wlabs (l : List ℕ) : ∀ r ∈ wregs (wlabs l), r = rI ∨ r = rA := by
  induction l with
  | nil => simp [wlabs, wregs]
  | cons i l ih =>
    intro r hr
    simp only [wlabs, List.foldr_cons, wregs_seq, List.mem_append] at hr ih
    rcases hr with hr | hr
    · simp only [wlab, wregs_seq, wregs_ld, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, wregs] at hr
      omega
    · exact ih r hr

theorem stores_wlabs (l : List ℕ) : stores (wlabs l) = false := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [wlabs, List.foldr_cons, stores_seq, Bool.or_eq_false_iff] at ih ⊢
    exact ⟨rfl, ih⟩

theorem loopFree_wlabs (l : List ℕ) : LoopFree (wlabs l) := by
  induction l with
  | nil => trivial
  | cons i l ih =>
    simp only [wlabs, List.foldr_cons] at ih ⊢
    exact ⟨⟨trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩, ih⟩

theorem size_wlabs (l : List ℕ) : size (wlabs l) = 6 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [wlabs, List.foldr_cons, List.length_cons] at ih ⊢
    rw [size, ih]
    simp [wlab, size]
    omega

/-- The fixed part of the program (without the subprograms) writes only `rT`, `rFREE` and
registers `≥ gVN`. -/
theorem wregs_fixed : ∀ r ∈ wregs initB ++ wregs copy ++ wregs collect ++ wregs localE ++
    wregs reset ++ wregs smallTest ++ wregs k4Test ++ wregs pInit ++ wregs posLoop ++
    wregs pgLoop ++ wregs omLoop, r = rT ∨ r = rFREE ∨ gVN ≤ r := by
  intro r hr
  simp [initB, copy, copyBody, collect, collBody, visit, localE, locBody, locRead, order, reset,
    resBody, smallTest, k4Test, pInit, posLoop, posBody, pgLoop, pgBody, pgRead, omLoop, omBody,
    wregs] at hr
  simp only [rT, rFREE, gVN, gCU, gCV, gVS, gLU, gLV, gLN, gPOS, gPU, gPV, gPE, gPN, gOMAP, rI, rA,
    rB, rU, rV, rX, rY, rC, rP, r2L] at hr ⊢
  omega

/-- **Footprint of the block solver**: only `rT`, `rFREE` and registers `≥ gVN` are written,
given the footprints of the ear elimination and of the polygon solver. -/
theorem blockProg_wregs {k : ℕ} {earProg polyProg : Stmt}
    (hearW : ∀ r ∈ wregs earProg, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r)
    (hpolyW : ∀ r ∈ wregs polyProg, r = rT ∨ r = rFREE ∨ gP0 ≤ r) :
    ∀ r ∈ wregs (blockProg k earProg polyProg), r = rT ∨ r = rFREE ∨ gVN ≤ r := by
  intro r hr
  have hf := wregs_fixed r
  simp only [blockProg, dispatch, polyBranch, wregs_seq, List.mem_append, wregs] at hr hf
  have h1 : r = rT ∨ r = rFREE ∨ gVN ≤ r ↔ r = 3 ∨ r = 2 ∨ 53 ≤ r := Iff.rfl
  rw [h1]
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  any_goals (apply hf; simp [hr])
  · simp at hr
  · have := wregs_wlabs _ r hr; simp only [rI, rA] at this; omega
  · rcases hearW r hr with h | h | h | h <;> simp only [rT, rFREE, gHAM, rS] at h <;> omega
  · rcases hpolyW r hr with h | h | h <;> simp only [rT, rFREE, gP0] at h <;> omega

end STACS2027.RAM.Block
