module

public import Outerplanar.RAM.R3
public import Outerplanar.RAM.MainGood
public import Outerplanar.RAM.BoundedLib
import Outerplanar.RAM.Poly1Lib
import Mathlib.Tactic

/-!
# The block loop (phase R4)

After phase R3 (`R3Post g c₀`: the blocks `blocksOf g` concatenated at `gBU`, `gBV`, their
starts `blockStarts g` at `gBST`, `BST[h] = bs g h`, `BST[N] = |E|`), the program
`blockLoop bp`

1. allocates the scratch array `LOC` (`numV g` cells at the old free address, `gLOC`), which
   is zero (`ZeroFrom`);
2. for `h = 0, …, N - 1` (`N = numV g`, counter `rH`): `gBS := BST[h]`,
   `gBL := BST[h + 1] - BST[h]` (`setBlock`), and runs the block solver `bp` on the block
   `h` (`blk g h = bk g |E| h`, the `h`-th block, `R3.blocksOf_eq`), stored at
   `gBU + gBS`, `gBV + gBS` (`P1.arr_flatMap_get`).

`blockLoop_spec`: given the block solver's specification `BlockSpec k bp CB` (in linear space)
and its footprint (it writes only `rT`, `rFREE` and registers `≥ gVN = 53`, so it keeps the
counter `rH`, the registers of `R3Post`, `gLOC`), and `BlockGood` for every block, the block
loop appends `solve k g` to the output within `CL CB * (m + 1)` steps (`CL CB = 3 CB + 28`), in
the space `loopEnd g F₀ CB = F₀ + N + CB (|E| + N)` (`loopEnd_le`: at most `F₀ + CL CB (m + 1)`).

The loop invariant `LoopInv` keeps the registers of `R3Post` and `gLOC`, the memory below
`F₀ + N` (`F₀` the free address on entry; so the arrays of `R3Post` survive and `LOC` is zero
again after each block: the block solver restores the memory below its own initial free
address), `ZeroFrom`, the output prefix `outPre k g j` (the outputs of the first `j` blocks),
and the free address `rFREE ≤ F₀ + N + CB (bs j + j)`. Blocks never free memory, so the space
is the sum of the blocks' bounds `CB (|E_h| + 1)`, which is linear:
`∑_h CB (|E_h| + 1) = CB (|E| + N)` with `∑_h |E_h| = |E|` (`sum_blk`, `R3.bs_total`).
Time: `∑_h (CB (|E_h| + 1) + 11) + 6 = CB (|E| + N) + 11 N + 6`, with `N ≤ 2m`, `|E| ≤ m`.
-/

@[expose] public section

namespace STACS2027.RAM.Main

open STACS2027.Algo

variable {S : ℕ}

/-! ### The program -/

/-- The block counter `h` (one of the reserved registers `4–9`: the block solver writes only
`rT`, `rFREE` and registers `≥ gVN`). -/
abbrev rH : ℕ := 4
/-- `h + 1`. -/
abbrev rH1 : ℕ := 5

/-- Setting up block `h = reg rH`: `gBS := BST[h]`, `gBL := BST[h + 1] - BST[h]`. -/
def setBlock : Stmt :=
  .seq (ld gBS gBST rH) (.seq (addc rH1 rH 1) (.seq (ld gBL gBST rH1) (.sub gBL gBL gBS)))

/-- One round of the block loop: set up block `h`, run the block solver `bp`. -/
def loopBody (bp : Stmt) : Stmt := .seq setBlock bp

/-- **The block loop**: allocate the zero scratch array `LOC` (`numV g` cells), then run the
block solver `bp` on the blocks `h = 0, …, numV g - 1`. -/
def blockLoop (bp : Stmt) : Stmt := .seq (alloc gLOC gN) (forUp rH gN (loopBody bp))

/-- The constant of the running time of the block loop, given that of the block solver. -/
def CL (CB : ℕ) : ℕ := 3 * CB + 28

/-- The memory of the block loop from the free address `F` on entry: `LOC` (`N` cells) and the
blocks, `CB (|E_h| + 1)` cells each (`∑_h (|E_h| + 1) = |E| + N`). -/
def loopEnd (g : Graph) (F CB : ℕ) : ℕ := F + numV g + CB * ((idEdges g).length + numV g)

/-- The memory of the block loop is linear. -/
theorem loopEnd_le (g : Graph) (F CB : ℕ) : loopEnd g F CB ≤ F + CL CB * (g.length + 1) := by
  have h1 := R0.numV_le g
  have h2 := R0.length_idEdges_le g
  have h3 : CB * ((idEdges g).length + numV g) ≤ 3 * (CB * g.length) := by
    calc CB * ((idEdges g).length + numV g) ≤ CB * (3 * g.length) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (CB * g.length) := by ring
  have h4 : CL CB * (g.length + 1) = 3 * (CB * g.length) + 3 * CB + 28 * g.length + 28 := by
    simp only [CL]; ring
  simp only [loopEnd]
  omega

/-! ### The abstract side -/

/-- The block `h`: the edges of key `h` (`= (blocksOf g)[h]`, `R3.blocksOf_eq`). -/
def blk (g : Graph) (h : ℕ) : List Edge := R3.bk g (idEdges g).length h

/-- There is one block (possibly empty) per vertex. -/
theorem length_blocksOf (g : Graph) : (blocksOf g).length = numV g := by
  simp [blocksOf]

theorem blk_mem {g : Graph} {h : ℕ} (hh : h < numV g) : blk g h ∈ blocksOf g := by
  rw [R3.blocksOf_eq]
  exact List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩

theorem getElem_blocksOf {g : Graph} {h : ℕ} (hh : h < (blocksOf g).length) :
    (blocksOf g)[h] = blk g h := by
  simp only [R3.blocksOf_eq, List.getElem_map, List.getElem_range, blk]

/-- The total size of the first `h` blocks is their start. -/
theorem sum_blk (g : Graph) (h : ℕ) :
    ∑ j ∈ Finset.range h, (blk g j).length = R3.bs g h := by
  induction h with
  | zero => simp [R3.bs]
  | succ h ih => rw [Finset.sum_range_succ, ih, R3.bs_succ]; rfl

/-- The output of the first `j` blocks. -/
def outPre (k : ℕ) (g : Graph) (j : ℕ) : List ℕ :=
  ((blocksOf g).take j).flatMap fun E => (solveBlock k E).flatten.map (labelOf g)

theorem outPre_zero (k : ℕ) (g : Graph) : outPre k g 0 = [] := by simp [outPre]

/-- One more block: its output is appended. -/
theorem outPre_succ (k : ℕ) {g : Graph} {j : ℕ} (hj : j < numV g) :
    outPre k g (j + 1) = outPre k g j ++ (solveBlock k (blk g j)).flatten.map (labelOf g) := by
  have hl : j < (blocksOf g).length := by rw [length_blocksOf]; exact hj
  rw [outPre, outPre, List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some,
    List.flatMap_append, getElem_blocksOf hl]
  simp

/-- The block outputs, concatenated, are the labels of the concatenated cycles. -/
theorem flatMap_out (k : ℕ) (g : Graph) :
    ∀ L : List (List Edge), (L.flatMap fun E => (solveBlock k E).flatten.map (labelOf g)) =
      (L.flatMap (solveBlock k)).flatMap fun c => c.map (labelOf g)
  | [] => rfl
  | E :: L => by
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_append, flatMap_out k g L,
      List.map_flatten]
    rfl

/-- After all blocks, the output is `solve k g`. -/
theorem outPre_full (k : ℕ) (g : Graph) : outPre k g (numV g) = solve k g := by
  rw [outPre, List.take_of_length_le (by rw [length_blocksOf]), flatMap_out]
  rfl

/-! ### The invariant -/

/-- The invariant of the block loop before block `j` (`c₀`: the configuration on entry,
`F₀ = c₀.reg rFREE`; `CB`: the constant of the block solver). -/
@[mk_iff] structure LoopInv (k CB : ℕ) (g : Graph) (c₀ : Config) (j : ℕ) (c : Config) : Prop where
  zero : c.reg rZERO = 0
  one : c.reg rONE = 1
  n : c.reg gN = numV g
  lb : c.reg gLB = c₀.reg gLB
  bst : c.reg gBST = c₀.reg gBST
  bu : c.reg gBU = c₀.reg gBU
  bv : c.reg gBV = c₀.reg gBV
  loc : c.reg gLOC = c₀.reg rFREE
  same : SameOn (· < c₀.reg rFREE + numV g) c₀.mem c.mem
  free : ZeroFrom c.mem (c.reg rFREE)
  le : c₀.reg rFREE + numV g ≤ c.reg rFREE
  out : c.out = c₀.out ++ outPre k g j
  fr : c.reg rFREE ≤ c₀.reg rFREE + numV g + CB * (R3.bs g j + j)

/-! ### Reads -/

section reads

variable {g : Graph} {c₀ : Config} {m : ℕ → ℕ}

/-- The block starts. -/
theorem bst_read (hR : R3Post g c₀) (hS : SameOn (· < c₀.reg rFREE + numV g) c₀.mem m) {i : ℕ}
    (hi : i ≤ numV g) : m (c₀.reg gBST + i) = R3.bs g i := by
  have hb := hR.below
  have hlen : i < (blockStarts g).length := by simp [blockStarts]; omega
  rw [hS _ (show _ < _ by omega), hR.bst.get hlen]
  simp only [R3.blockStarts_eq, List.getElem_map, List.getElem_range]

/-- The first ends of the block `j`. -/
theorem bu_read (hR : R3Post g c₀) (hS : SameOn (· < c₀.reg rFREE + numV g) c₀.mem m) {j : ℕ}
    (hj : j < numV g) : Arr m (c₀.reg gBU + R3.bs g j) ((blk g j).map Prod.fst) := by
  have h := hR.bu
  rw [R3.flatten_fst] at h
  have h2 := P1.arr_flatMap_get (fun h => (R3.bk g (idEdges g).length h).map Prod.fst) _ h j hj
  have hoff : P1.partOff (fun h => (R3.bk g (idEdges g).length h).map Prod.fst) j = R3.bs g j := by
    simp [P1.partOff, R3.bs]
  rw [hoff] at h2
  have hb := hR.below
  have hl := R3.length_flatten g
  have hle := R3.bs_add_le_total g hj
  exact h2.of_below hS (by simp only [List.length_map]; omega)

/-- The second ends of the block `j`. -/
theorem bv_read (hR : R3Post g c₀) (hS : SameOn (· < c₀.reg rFREE + numV g) c₀.mem m) {j : ℕ}
    (hj : j < numV g) : Arr m (c₀.reg gBV + R3.bs g j) ((blk g j).map Prod.snd) := by
  have h := hR.bv
  rw [R3.flatten_snd] at h
  have h2 := P1.arr_flatMap_get (fun h => (R3.bk g (idEdges g).length h).map Prod.snd) _ h j hj
  have hoff : P1.partOff (fun h => (R3.bk g (idEdges g).length h).map Prod.snd) j = R3.bs g j := by
    simp [P1.partOff, R3.bs]
  rw [hoff] at h2
  have hb := hR.below
  have hl := R3.length_flatten g
  have hle := R3.bs_add_le_total g hj
  exact h2.of_below hS (by simp only [List.length_map]; omega)

end reads

/-! ### The steps -/

/-- The effect of `setBlock`: `gBS := BST[h]`, `gBL := BST[h + 1] - BST[h]`, memory unchanged. -/
theorem run_setBlock (c : Config) :
    (RAM.run setBlock c).reg gBS = c.mem (c.reg gBST + c.reg rH) ∧
      (RAM.run setBlock c).reg gBL =
        c.mem (c.reg gBST + (c.reg rH + 1)) - c.mem (c.reg gBST + c.reg rH) ∧
      (RAM.run setBlock c).mem = c.mem := by
  simp +decide only [setBlock, run_seq', run_ld, run_addc (show rH ≠ rT by decide), run_sub,
    setReg_reg, setReg_mem, ↓reduceIte]

/-- The invariant does not mention the registers written by `setBlock` nor the counter. -/
theorem loopInv_indep (k CB : ℕ) (g : Graph) (c₀ : Config) (j : ℕ) (W : List ℕ)
    (hW : ∀ r ∈ W, r = gBS ∨ r = rT ∨ r = rH1 ∨ r = gBL ∨ r = rH) :
    Indep W (LoopInv k CB g c₀ j) := by
  intro c c' hA hI
  have hr : ∀ r, r ≠ gBS → r ≠ rT → r ≠ rH1 → r ≠ gBL → r ≠ rH → c'.reg r = c.reg r :=
    fun r h1 h2 h3 h4 h5 => hA.reg r fun hm => by
      rcases hW r hm with h | h | h | h | h <;> contradiction
  rw [loopInv_iff] at hI ⊢
  simp (disch := decide) only [hr, hA.mem, hA.out]
  exact hI

/-- Setting up block `j`: the state on entry to the block solver. -/
theorem setBlock_spec (k CB : ℕ) {g : Graph} {c₀ : Config} (hR : R3Post g c₀)
    (hS : c₀.reg rFREE ≤ S) {j : ℕ} (hj : j < numV g) :
    HTB S setBlock (fun c => LoopInv k CB g c₀ j c ∧ c.reg rH = j ∧ c.reg gN = numV g)
      (fun c => (LoopInv k CB g c₀ j c ∧ c.reg rH = j ∧ c.reg gN = numV g) ∧
        BlockIn g (blk g j) c) 7 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hI, hj', hn⟩ => ⟨?_, ?_⟩
  · have := hR.below
    addr_ok [setBlock, hI.bst, hj']
  obtain ⟨hbs, hbl, hmem⟩ := run_setBlock c
  have hreg : ∀ r, r ∉ wregs setBlock → (RAM.run setBlock c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hI' : LoopInv k CB g c₀ j (RAM.run setBlock c) :=
    (loopInv_indep k CB g c₀ j _ (by decide)).run (by decide) rfl rfl hI
  have hS := hI'.same
  have hb := hR.below
  have hb0 := hR.base.below
  have hl := R3.length_flatten g
  have hle := R3.bs_add_le_total g hj
  have hnv : numV g = (labels g).length := rfl
  have hbs' : (RAM.run setBlock c).reg gBS = R3.bs g j := by
    rw [hbs, hj', hI.bst, bst_read hR hI.same hj.le]
  refine ⟨⟨hI', (hreg rH (by decide)).trans hj', (hreg gN (by decide)).trans hn⟩,
    ⟨hI'.zero, hI'.one, hI'.n, ?_, ?_, ?_, ?_, ?_, hI'.free, ?_⟩⟩
  · rw [hI'.lb]; exact hR.base.lb.of_below hS (by omega)
  · rw [hbl, hj', hI.bst, bst_read hR hI.same hj, bst_read hR hI.same hj.le, R3.bs_succ]
    simp [blk]
  · rw [hI'.bu, hbs']; exact bu_read hR hS hj
  · rw [hI'.bv, hbs']; exact bv_read hR hS hj
  · rw [hI'.loc]; exact (hR.base.free.arr le_rfl _).of_below hS (by simp)
  · rw [hI'.lb, hI'.bu, hI'.bv, hI'.loc, hbs']
    have := hI'.le
    simp only [blk]
    omega

/-- The registers below `gVN` other than `rT`, `rFREE` are not written by a block solver
with the footprint of `blockProg_wregs`. -/
theorem not_mem_of_footprint {bp : Stmt} (hW : ∀ r ∈ wregs bp, r = rT ∨ r = rFREE ∨ gVN ≤ r)
    {r : ℕ} (hr : r < gVN) (hT : r ≠ rT) (hF : r ≠ rFREE) : r ∉ wregs bp := fun hm => by
  rcases hW r hm with h | h | h
  · exact hT h
  · exact hF h
  · omega

/-- **One round of the block loop**: block `j` is solved and its output appended. -/
theorem body_spec {k CB : ℕ} {bp : Stmt} (hbp : BlockSpec k bp CB)
    (hW : ∀ r ∈ wregs bp, r = rT ∨ r = rFREE ∨ gVN ≤ r) {g : Graph} {c₀ : Config}
    (hR : R3Post g c₀) (hgood : ∀ E ∈ blocksOf g, BlockGood E)
    (hS : loopEnd g (c₀.reg rFREE) CB ≤ S) {j : ℕ} (hj : j < numV g) :
    HTB S (loopBody bp) (fun c => LoopInv k CB g c₀ j c ∧ c.reg rH = j ∧ c.reg gN = numV g)
      (fun c => LoopInv k CB g c₀ (j + 1) c ∧ c.reg rH = j ∧ c.reg gN = numV g)
      (7 + CB * ((blk g j).length + 1)) := by
  have hS0 : c₀.reg rFREE ≤ S := by simp only [loopEnd] at hS; omega
  refine (setBlock_spec k CB hR hS0 hj).seq (HTB.of_forall fun c' ⟨⟨hI, hj', hn⟩, hB⟩ => ?_)
  have hm := blk_mem hj
  have hbs : CB * (R3.bs g (j + 1) + (j + 1)) =
      CB * (R3.bs g j + j) + CB * ((blk g j).length + 1) := by
    rw [R3.bs_succ]; simp only [blk]; ring
  have hmono : CB * (R3.bs g (j + 1) + (j + 1)) ≤ CB * ((idEdges g).length + numV g) := by
    rw [← R3.bs_total g]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add (R3.bs_mono g hj) hj)
  have hfr := hI.fr
  have hSb : c'.reg rFREE + CB * ((blk g j).length + 1) ≤ S := by
    simp only [loopEnd] at hS; omega
  refine ((hbp S g (blk g j) c' (blocksOf_ends hm) (blocksOf_nodup hm) (hgood _ hm) hSb).withFrame
    c').mono (fun c hc => by subst hc; exact ⟨⟨hB, rfl⟩, rfl⟩)
    (fun c ⟨⟨hout, hS', hZ, hF, hF'⟩, hfr'⟩ => ?_) le_rfl
  have hreg : ∀ r, r < gVN → r ≠ rT → r ≠ rFREE → c.reg r = c'.reg r :=
    fun r h1 h2 h3 => hfr'.reg r (not_mem_of_footprint hW h1 h2 h3)
  have hle := hI.le
  refine ⟨⟨(hreg _ (by decide) (by decide) (by decide)).trans hI.zero,
    (hreg _ (by decide) (by decide) (by decide)).trans hI.one,
    (hreg _ (by decide) (by decide) (by decide)).trans hI.n,
    (hreg _ (by decide) (by decide) (by decide)).trans hI.lb,
    (hreg _ (by decide) (by decide) (by decide)).trans hI.bst,
    (hreg _ (by decide) (by decide) (by decide)).trans hI.bu,
    (hreg _ (by decide) (by decide) (by decide)).trans hI.bv,
    (hreg _ (by decide) (by decide) (by decide)).trans hI.loc,
    hI.same.trans (hS'.mono fun a (ha : a < _) => show a < _ by omega), hZ, by omega, ?_,
    by omega⟩,
    (hreg _ (by decide) (by decide) (by decide)).trans hj',
    (hreg _ (by decide) (by decide) (by decide)).trans hn⟩
  rw [hout, hI.out, outPre_succ k hj, List.append_assoc]

/-- The allocation of `LOC`: the invariant before the first block. -/
theorem alloc_spec (k CB : ℕ) {g : Graph} {c₀ : Config} (hR : R3Post g c₀) :
    HTB S (alloc gLOC gN) (fun c => c = c₀)
      (fun c => LoopInv k CB g c₀ 0 c ∧ c.reg gN = numV g) 3 :=
  HTB.run_le (by decide) (by decide) fun c hc => by
    subst hc
    refine ⟨AddrOK.of_memFree rfl, ?_⟩
    rw [run_alloc (by decide) (by decide)]
    have hn := hR.base.n
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, SameOn.refl _ _, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp +decide [hR.base.zero, hR.base.one, hn, outPre_zero, R3.bs]
    exact hR.base.free.mono (by omega)

/-- **The block loop** (phase R4): from `R3Post g`, given the block solver's specification
`BlockSpec k bp CB` and footprint, and `BlockGood` for every block, `blockLoop bp` appends
`solve k g` to the output within `CL CB * (m + 1)` steps, in the space
`loopEnd g F₀ CB` (`F₀` the free address on entry), which bounds the final `rFREE`. -/
theorem blockLoop_spec {k CB : ℕ} {bp : Stmt} (hbp : BlockSpec k bp CB)
    (hW : ∀ r ∈ wregs bp, r = rT ∨ r = rFREE ∨ gVN ≤ r) (g : Graph) (c₀ : Config)
    (hgood : ∀ E ∈ blocksOf g, BlockGood E) (hS : loopEnd g (c₀.reg rFREE) CB ≤ S) :
    HTB S (blockLoop bp) (fun c => R3Post g c ∧ c = c₀)
      (fun c => c.out = c₀.out ++ solve k g ∧ c.reg rFREE ≤ loopEnd g (c₀.reg rFREE) CB)
      (CL CB * (g.length + 1)) := by
  refine HTB.of_forall fun c ⟨hR, hc⟩ => ?_
  subst hc
  have hl := HTB.forUp (i := rH) (n := gN) (N := numV g) (body := loopBody bp) (LoopInv k CB g c)
    (fun j => 7 + CB * ((blk g j).length + 1)) (by decide) (by decide) (by decide)
    (fun j => loopInv_indep k CB g c j _ (by decide)) (fun j hj => body_spec hbp hW hR hgood hS hj)
  refine ((alloc_spec k CB hR).seq hl).mono (fun _ h => h)
    (fun c' ⟨hI, _, _⟩ => ⟨by rw [hI.out, outPre_full], ?_⟩) ?_
  · have := hI.fr
    rw [R3.bs_total] at this
    simp only [loopEnd]; omega
  have hsum : ∑ j ∈ Finset.range (numV g), (7 + CB * ((blk g j).length + 1) + 4) =
      CB * (R3.bs g (numV g) + numV g) + 11 * numV g := by
    rw [← sum_blk]
    induction numV g with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; ring
  rw [hsum, R3.bs_total]
  have h1 := R0.numV_le g
  have h2 := R0.length_idEdges_le g
  have h3 : CB * ((idEdges g).length + numV g) ≤ 3 * (CB * g.length) := by
    calc CB * ((idEdges g).length + numV g) ≤ CB * (3 * g.length) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (CB * g.length) := by ring
  have h4 : CL CB * (g.length + 1) = 3 * (CB * g.length) + 3 * CB + 28 * g.length + 28 := by
    simp only [CL]; ring
  omega

end STACS2027.RAM.Main
