module

public import Outerplanar.RAM.R1Spec
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Phase R1: the program, its memory layout, and the CSR neighbour lists

Phase R1 starts in a `GraphBase g` configuration (`N = numV g` vertices, the `ne` edges
`E = idEdges g` at `gEU`, `gEV`) with first free address `F`. It

1. `alloc1`: allocates (all zero) the degree array `DEG` (`N` cells, base `F`), the offsets
   `OFF` (`N + 1`), the fill counters `FIL` (`N`), the CSR array `ADJ` (`2 ne`), and the arrays
   of the search `PRE`, `PAR`, `PTR`, `ORD`, `STK` (`N` each); `rFREE := endL g F`;
2. `stepDeg`: for each edge `(a, b)`: `DEG[a]++`, `DEG[b]++` (after `j` edges `DEG` holds
   `cnt E j`, `DegMem`);
3. `stepPre`: prefix sums `OFF[v + 1] := OFF[v] + DEG[v]`, so `OFF` holds `ps E` (`PreMem`);
4. `stepFill`: for each edge `(a, b)`: `ADJ[OFF[a] + FIL[a]++] := b`, `ADJ[OFF[b] + FIL[b]++] := a`
   (after `j` edges the segment of `v` holds `nbOf (E.take j) v`, `FillMem`);
5. `stepDfs`: the depth-first search, one `DFS.step` per round of a `while` loop (proved in
   `R1Dfs.lean`).

This file contains the program, the layout, the register invariant `Glob`, and the proofs of
steps 1–4 (`stepCsr_spec`).

Space: every triple is stated within a bound `S` on the accessed addresses, under the
hypothesis `hS : endL g (c₀.reg rFREE) ≤ S` (`HTB S`); the regions enter the address proofs
through `fits` (one inequality per region), and `endL_le` bounds the layout linearly. The
memory-free blocks reuse their `HT` proofs (`HTB.of_HT`), the loop-free blocks with memory
access add an address proof (`HTB.of_HT_addrOK`, or inline in `HTB.run_le`).
-/

@[expose] public section

namespace STACS2027.RAM.R1

open STACS2027.Algo

variable {S : ℕ}

/-! ### Scratch registers of the phase -/

/-- Loop counter. -/
abbrev rI : ℕ := 100
/-- A value read from memory. -/
abbrev rX : ℕ := 101
/-- A second value read from memory. -/
abbrev rY : ℕ := 102
/-- First end of the current edge. -/
abbrev rU : ℕ := 103
/-- Second end of the current edge; the top of the stack. -/
abbrev rV : ℕ := 104
/-- An index. -/
abbrev rP : ℕ := 105
/-- `OFF[v] + PTR[v]`: the position of the next neighbour of the top `v`. -/
abbrev rA : ℕ := 106
/-- `OFF[v + 1]`: the end of the neighbour list of the top `v`. -/
abbrev rB : ℕ := 107
/-- The next neighbour of the top. -/
abbrev rW : ℕ := 108
/-- Running prefix sum. -/
abbrev rAcc : ℕ := 109
/-- Base of the degree array `DEG`. -/
abbrev rDEG : ℕ := 110
/-- Base of the fill counters `FIL`. -/
abbrev rFIL : ℕ := 111
/-- The next root candidate `r` (the candidates are `r, r + 1, …, N - 1`). -/
abbrev rR : ℕ := 112

/-! ### The program -/

/-- Step 1: allocation of all arrays. -/
def alloc1 : Stmt :=
  .seq (alloc rDEG gN) (.seq (addc rX gN 1) (.seq (alloc gOFF rX) (.seq (alloc rFIL gN)
    (.seq (.add rX gNE gNE) (.seq (alloc gADJ rX) (.seq (alloc gPRE gN) (.seq (alloc gPAR gN)
    (.seq (alloc gPTR gN) (.seq (alloc gORD gN) (alloc gSTK gN))))))))))

/-- Read the ends of edge `rI` into `rU`, `rV`. -/
def readEdge : Stmt := .seq (ld rU gEU rI) (ld rV gEV rI)

/-- `mem[reg b + reg x] += 1`. -/
def bump (b x : ℕ) : Stmt := .seq (ld rX b x) (.seq (inc rX) (st b x rX))

/-- One edge of the degree pass. -/
def degBody : Stmt := .seq readEdge (.seq (bump rDEG rU) (bump rDEG rV))
/-- Step 2: the degrees. -/
def stepDeg : Stmt := forUp rI gNE degBody

/-- One vertex of the prefix sums: `rAcc += DEG[i]; OFF[i + 1] := rAcc`. -/
def preBody : Stmt :=
  .seq (ld rX rDEG rI) (.seq (.add rAcc rAcc rX) (.seq (addc rP rI 1) (st gOFF rP rAcc)))
/-- Step 3: the offsets. -/
def stepPre : Stmt := .seq (.const rAcc 0) (forUp rI gN preBody)

/-- Append `reg y` to the neighbour list of `reg x`: `ADJ[OFF[x] + FIL[x]] := y; FIL[x]++`. -/
def put (x y : ℕ) : Stmt :=
  .seq (ld rX rFIL x) (.seq (ld rY gOFF x) (.seq (.add rY rY rX) (.seq (st gADJ rY y)
    (.seq (inc rX) (st rFIL x rX)))))

/-- One edge of the fill pass. -/
def fillBody : Stmt := .seq readEdge (.seq (put rU rV) (put rV rU))
/-- Step 4: the CSR array. -/
def stepFill : Stmt := forUp rI gNE fillBody

/-- Visit `reg x` with parent `reg p`: `ORD[cnt] := x; cnt++; PRE[x] := cnt; PAR[x] := p`,
`STK[sp] := x; sp++`. -/
def visit (x p : ℕ) : Stmt :=
  .seq (st gORD gCNT x) (.seq (inc gCNT) (.seq (st gPRE x gCNT) (.seq (st gPAR x p)
    (.seq (st gSTK gSP x) (inc gSP)))))

/-- Empty stack: try the next root candidate `r`. -/
def rootStep : Stmt := .seq (ld rX gPRE rR) (.seq (.ifz rX (visit rR rR) .skip) (inc rR))

/-- The top `v` of the stack, `rA := OFF[v] + PTR[v]`, `rX := PTR[v]`, `rB := OFF[v + 1]`. -/
def topRead : Stmt :=
  .seq (subc rP gSP 1) (.seq (ld rV gSTK rP) (.seq (ld rA gOFF rV) (.seq (ld rX gPTR rV)
    (.seq (.add rA rA rX) (.seq (addc rP rV 1) (ld rB gOFF rP))))))

/-- The next neighbour `w := ADJ[rA]` of the top `v`; `PTR[v]++`; `rY := PRE[w]`. -/
def advRead : Stmt := .seq (ld rW gADJ rA) (.seq (inc rX) (.seq (st gPTR rV rX) (ld rY gPRE rW)))

/-- Examine the next neighbour, visiting it if new. -/
def advance : Stmt := .seq advRead (.ifz rY (visit rW rV) .skip)

/-- Non-empty stack: examine the next neighbour of the top, or pop it. -/
def topStep : Stmt := .seq topRead (ifLt rA rB advance (dec gSP))

/-- One step of the search. -/
def dfsBody : Stmt := .ifz gSP rootStep topStep

/-- The loop test: `rT := (N - r) + sp` (zero iff the search has halted). -/
def dfsCond : Stmt := .seq (.sub rT gN rR) (.add rT rT gSP)

/-- `sp := 0; cnt := 0; r := 0`. -/
def dfsInit : Stmt := .seq (.const gSP 0) (.seq (.const gCNT 0) (.const rR 0))

/-- Step 5: the depth-first search. -/
def stepDfs : Stmt := .seq dfsInit (whileC dfsCond dfsBody)

/-- Steps 1–4: the CSR neighbour lists. -/
def stepCsr : Stmt := .seq alloc1 (.seq stepDeg (.seq stepPre stepFill))

/-- **Phase R1.** -/
def r1 : Stmt := .seq stepCsr stepDfs

/-! ### The layout -/

section layout

variable (g : Graph) (F : ℕ)

/-- The offsets `OFF` (`N + 1` cells); the degrees `DEG` are at `F` (`N` cells). -/
def bOFF : ℕ := F + numV g
/-- The fill counters `FIL` (`N` cells). -/
def bFIL : ℕ := bOFF g F + (numV g + 1)
/-- The CSR array `ADJ` (`2 ne` cells). -/
def bADJ : ℕ := bFIL g F + numV g
/-- The preorder numbers `PRE` (`N` cells). -/
def bPRE : ℕ := bADJ g F + 2 * (idEdges g).length
/-- The parents `PAR` (`N` cells). -/
def bPAR : ℕ := bPRE g F + numV g
/-- The neighbour pointers `PTR` (`N` cells). -/
def bPTR : ℕ := bPAR g F + numV g
/-- The preorder list `ORD` (`N` cells). -/
def bORD : ℕ := bPTR g F + numV g
/-- The stack `STK` (`N` cells). -/
def bSTK : ℕ := bORD g F + numV g
/-- The end of the memory used by R1. -/
def endL : ℕ := bSTK g F + numV g

/-- The layout as equations (for `omega`). -/
theorem layout_eqs : bOFF g F = F + numV g ∧ bFIL g F = bOFF g F + (numV g + 1) ∧
    bADJ g F = bFIL g F + numV g ∧ bPRE g F = bADJ g F + 2 * (idEdges g).length ∧
    bPAR g F = bPRE g F + numV g ∧ bPTR g F = bPAR g F + numV g ∧
    bORD g F = bPTR g F + numV g ∧ bSTK g F = bORD g F + numV g ∧
    endL g F = bSTK g F + numV g :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end layout

/-- The regions of R1 fit below `S`: one inequality per region (the form in which `omega` uses
the layout efficiently — a chain of layout equations such as `layout_eqs` in the context makes
every `omega` call slow). -/
theorem fits (g : Graph) {F : ℕ} (hS : endL g F ≤ S) :
    F + numV g ≤ S ∧ bOFF g F + (numV g + 1) ≤ S ∧ bFIL g F + numV g ≤ S ∧
      bADJ g F + 2 * (idEdges g).length ≤ S ∧ bPRE g F + numV g ≤ S ∧ bPAR g F + numV g ≤ S ∧
      bPTR g F + numV g ≤ S ∧ bORD g F + numV g ≤ S ∧ bSTK g F + numV g ≤ S := by
  have hL := layout_eqs g F
  omega

/-- The layout of R1 is linear: `endL g F ≤ F + 18 (m + 1)`. -/
theorem endL_le (g : Graph) (F : ℕ) : endL g F ≤ F + 18 * (g.length + 1) := by
  have hL := layout_eqs g F
  have h1 := R0.numV_le g
  have h2 := R0.length_idEdges_le g
  omega

/-! ### Global registers fixed after the allocation -/

/-- The registers that keep their value from the end of step 1 on (`F = c₀.reg rFREE`). -/
@[mk_iff] structure Glob (g : Graph) (c₀ c : Config) : Prop where
  n : c.reg gN = numV g
  ne : c.reg gNE = (idEdges g).length
  eu : c.reg gEU = c₀.reg gEU
  ev : c.reg gEV = c₀.reg gEV
  free : c.reg rFREE = endL g (c₀.reg rFREE)
  deg : c.reg rDEG = c₀.reg rFREE
  off : c.reg gOFF = bOFF g (c₀.reg rFREE)
  fil : c.reg rFIL = bFIL g (c₀.reg rFREE)
  adj : c.reg gADJ = bADJ g (c₀.reg rFREE)
  pre : c.reg gPRE = bPRE g (c₀.reg rFREE)
  par : c.reg gPAR = bPAR g (c₀.reg rFREE)
  ptr : c.reg gPTR = bPTR g (c₀.reg rFREE)
  ord : c.reg gORD = bORD g (c₀.reg rFREE)
  stk : c.reg gSTK = bSTK g (c₀.reg rFREE)

/-- The registers written by steps 2–5. -/
def W1 : List ℕ := [rT, rI, rX, rY, rU, rV, rP, rA, rB, rW, rAcc, rR, gSP, gCNT]

theorem Glob.regIndep (g : Graph) (c₀ : Config) : RegIndep W1 (Glob g c₀) := by indep [glob_iff]

/-- The edge ends in a memory that agrees with the initial one below `F`. -/
theorem edge_ends {g : Graph} {c₀ : Config} (hB : GraphBase g c₀) {m : ℕ → ℕ}
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {j : ℕ} (hj : j < (idEdges g).length) :
    m (c₀.reg gEU + j) = (idEdges g)[j].1 ∧ m (c₀.reg gEV + j) = (idEdges g)[j].2 := by
  have hu := (hB.eu.of_below hS (by simpa using hB.below.2.1)).get (i := j) (by simpa using hj)
  have hv := (hB.ev.of_below hS (by simpa using hB.below.2.2)).get (i := j) (by simpa using hj)
  simp only [List.getElem_map] at hu hv
  exact ⟨hu, hv⟩

/-! ### Step 1: allocation -/

/-- The memory during the degree pass, with the degree counts `f`. -/
structure DegMem (g : Graph) (c₀ : Config) (f : ℕ → ℕ) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  deg : Tab m (c₀.reg rFREE) (numV g) f
  zero : ZeroFrom m (bOFF g (c₀.reg rFREE))

/-- The invariant of the degree pass after `j` edges. -/
def DegInv (g : Graph) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  Glob g c₀ c ∧ DegMem g c₀ (cnt (idEdges g) j) c.mem

theorem alloc1_spec (g : Graph) (c₀ : Config) (hB : GraphBase g c₀) :
    HTB S alloc1 (fun c => c = c₀) (fun c => DegInv g c₀ 0 c ∧ c.reg gNE = (idEdges g).length) 34 :=
    HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  have hL := layout_eqs g (c.reg rFREE)
  simp only [alloc1, run_seq', run_alloc (show gN ≠ rT by decide) (show rDEG ≠ gN by decide),
    run_addc (show gN ≠ rT by decide), run_alloc (show rX ≠ rT by decide) (show gOFF ≠ rX by decide),
    run_alloc (show gN ≠ rT by decide) (show rFIL ≠ gN by decide), run_add,
    run_alloc (show rX ≠ rT by decide) (show gADJ ≠ rX by decide),
    run_alloc (show gN ≠ rT by decide) (show gPRE ≠ gN by decide),
    run_alloc (show gN ≠ rT by decide) (show gPAR ≠ gN by decide),
    run_alloc (show gN ≠ rT by decide) (show gPTR ≠ gN by decide),
    run_alloc (show gN ≠ rT by decide) (show gORD ≠ gN by decide),
    run_alloc (show gN ≠ rT by decide) (show gSTK ≠ gN by decide)]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  all_goals try (simp +decide [hB.n, hB.ne, hL] <;> omega)
  simp only [setReg_mem, cnt_zero]
  exact ⟨SameOn.refl _ _, hB.free.tab le_rfl _, hB.free.mono (by omega)⟩

/-! ### Step 2: the degrees -/

theorem readEdge_run {g : Graph} {c₀ c : Config} (hB : GraphBase g c₀) (hG : Glob g c₀ c)
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem) {j : ℕ} (hi : c.reg rI = j)
    (hj : j < (idEdges g).length) :
    (run readEdge c).reg rU = (idEdges g)[j].1 ∧ (run readEdge c).reg rV = (idEdges g)[j].2 ∧
      Agree [rU, rV] c (run readEdge c) := by
  obtain ⟨ha, hb⟩ := edge_ends hB hS hj
  refine ⟨?_, ?_, agree_run (by decide) rfl rfl (by decide) c⟩ <;>
    simp +decide [readEdge, hG.eu, hG.ev, hi, ha, hb]

theorem DegMem.bmp {g : Graph} {c₀ : Config} {f : ℕ → ℕ} {m : ℕ → ℕ} (h : DegMem g c₀ f m)
    {u : ℕ} (hu : u < numV g) :
    DegMem g c₀ (R1.bmp f u) (upd m (c₀.reg rFREE + u) (f u + 1)) := by
  have hL := layout_eqs g (c₀.reg rFREE)
  exact ⟨h.same.upd_of_ge (by omega) _, h.deg.upd rfl, h.zero.upd (by omega)⟩

theorem loopFree_bump (b x : ℕ) : LoopFree (bump b x) := by simp [bump, LoopFree]
theorem wregs_bump (b x : ℕ) : wregs (bump b x) = [rX, rX, rT, rX, rT] := rfl

/-- Incrementing the degree of the vertex in register `x`. -/
theorem bump_run {g : Graph} {c₀ c : Config} {f : ℕ → ℕ} {x u : ℕ} (hx : x = rU ∨ x = rV)
    (hG : Glob g c₀ c) (hM : DegMem g c₀ f c.mem) (hxu : c.reg x = u) (hu : u < numV g) :
    Glob g c₀ (run (bump rDEG x) c) ∧ DegMem g c₀ (R1.bmp f u) (run (bump rDEG x) c).mem ∧
      ∀ r, r ≠ rX → r ≠ rT → (run (bump rDEG x) c).reg r = c.reg r := by
  have hfu : c.mem (c₀.reg rFREE + u) = f u := hM.deg.get hu
  have hreg : ∀ r, r ≠ rX → r ≠ rT → (run (bump rDEG x) c).reg r = c.reg r := fun r h1 h2 =>
    run_reg_of_not_mem (loopFree_bump _ _) (by rw [wregs_bump]; simp [h1, h2]) c
  refine ⟨(Glob.regIndep g c₀).run_of_sub (loopFree_bump _ _) (by rw [wregs_bump]; decide) hG,
    ?_, hreg⟩
  have hxX : x ≠ rX ∧ x ≠ rT := by rcases hx with rfl | rfl <;> decide
  simpa [bump, run_inc, run_st, hG.deg, hxu, hfu, hxX.1, hxX.2] using hM.bmp hu

theorem degBody_spec (g : Graph) (c₀ : Config) (hB : GraphBase g c₀) (j : ℕ)
    (hj : j < (idEdges g).length) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S degBody (fun c => DegInv g c₀ j c ∧ c.reg rI = j ∧ c.reg gNE = (idEdges g).length)
      (fun c => DegInv g c₀ (j + 1) c ∧ c.reg rI = j ∧ c.reg gNE = (idEdges g).length) 16 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hG, hM⟩, hi, _⟩ => by
    obtain ⟨he₁, he₂⟩ := edge_ends hB hM.same hj
    have := idEdges_lt_get hj
    have := hB.below
    have := fits g hS
    addr_ok [degBody, readEdge, bump, hG.eu, hG.ev, hG.deg, hi, he₁, he₂]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hi, hn⟩ => ?_
  obtain ⟨hU, hV, hAg⟩ := readEdge_run hB hG hM.same hi hj
  obtain ⟨ha, hb⟩ := idEdges_lt_get hj
  have hne := idEdges_ne hj
  have hG₁ : Glob g c₀ (run readEdge c) := (Glob.regIndep g c₀).indep.mono (by decide) _ _ hAg hG
  have hM₁ : DegMem g c₀ (cnt (idEdges g) j) (run readEdge c).mem := by rw [hAg.mem]; exact hM
  obtain ⟨hG₂, hM₂, hr₂⟩ := bump_run (Or.inl rfl) hG₁ hM₁ hU ha
  obtain ⟨hG₃, hM₃, hr₃⟩ := bump_run (Or.inr rfl) hG₂ hM₂
    (by rw [hr₂ _ (by decide) (by decide), hV]) hb
  rw [← cnt_succ hj hne] at hM₃
  simp only [degBody, run_seq']
  refine ⟨⟨hG₃, hM₃⟩, ?_, ?_⟩
  · rw [hr₃ _ (by decide) (by decide), hr₂ _ (by decide) (by decide), hAg.reg _ (by decide), hi]
  · rw [hr₃ _ (by decide) (by decide), hr₂ _ (by decide) (by decide), hAg.reg _ (by decide), hn]

/-- **Step 2**: the degree counts of all edges. -/
theorem stepDeg_spec (g : Graph) (c₀ : Config) (hB : GraphBase g c₀) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S stepDeg (fun c => DegInv g c₀ 0 c ∧ c.reg gNE = (idEdges g).length)
      (fun c => DegInv g c₀ (idEdges g).length c ∧ c.reg rI = (idEdges g).length ∧
        c.reg gNE = (idEdges g).length) ((idEdges g).length * 20 + 3) :=
  HTB.forUpC (i := rI) (n := gNE) (N := (idEdges g).length) (body := degBody) (DegInv g c₀) 16
    (by decide) (by decide) (by decide) (fun j => by indep [DegInv, glob_iff])
    (fun j hj => degBody_spec g c₀ hB j hj hS)

/-! ### Step 3: the offsets -/

/-- The memory during the prefix sums, after `v` vertices. -/
structure PreMem (g : Graph) (c₀ : Config) (v : ℕ) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  deg : Tab m (c₀.reg rFREE) (numV g) fun u => (nbOf (idEdges g) u).length
  off : Tab m (bOFF g (c₀.reg rFREE)) (numV g + 1) fun i => if i ≤ v then ps (idEdges g) i else 0
  zero : ZeroFrom m (bFIL g (c₀.reg rFREE))

/-- The invariant of the prefix sums after `v` vertices. -/
def PreInv (g : Graph) (c₀ : Config) (v : ℕ) (c : Config) : Prop :=
  Glob g c₀ c ∧ c.reg rAcc = ps (idEdges g) v ∧ PreMem g c₀ v c.mem

theorem PreMem.snoc {g : Graph} {c₀ : Config} {v : ℕ} {m : ℕ → ℕ} (h : PreMem g c₀ v m)
    (hv : v < numV g) :
    PreMem g c₀ (v + 1)
      (upd m (bOFF g (c₀.reg rFREE) + (v + 1)) (ps (idEdges g) v + (nbOf (idEdges g) v).length)) := by
  have hL := layout_eqs g (c₀.reg rFREE)
  refine ⟨h.same.upd_of_ge (by omega) _, h.deg.upd_of_disjoint (by omega), ?_, h.zero.upd (by omega)⟩
  refine (h.off.upd rfl).congr_fun fun i _ => ?_
  rw [← ps_succ]
  by_cases hi : i = v + 1
  · subst hi; simp
  · rw [Function.update_of_ne hi]
    by_cases hiv : i ≤ v
    · simp [hiv, show i ≤ v + 1 by omega]
    · simp [hiv, show ¬ i ≤ v + 1 by omega]

theorem preBody_spec (g : Graph) (c₀ : Config) (v : ℕ) (hv : v < numV g)
    (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S preBody (fun c => PreInv g c₀ v c ∧ c.reg rI = v ∧ c.reg gN = numV g)
      (fun c => PreInv g c₀ (v + 1) c ∧ c.reg rI = v ∧ c.reg gN = numV g) 7 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hG, _, _⟩, hi, _⟩ => by
    have := fits g hS
    addr_ok [preBody, hG.deg, hG.off, hi]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hacc, hM⟩, hi, hn⟩ => ?_
  have hd : c.mem (c₀.reg rFREE + v) = (nbOf (idEdges g) v).length := hM.deg.get hv
  refine ⟨⟨(Glob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [preBody, run_seq', run_ld, run_add, run_addc (show rI ≠ rT by decide),
      run_st (show rAcc ≠ rT by decide)]
  · simp +decide [hd, hacc, ps_succ, hG.deg, hi]
  · simpa +decide [hd, hacc, hG.off, hG.deg, hi] using hM.snoc hv
  · simp +decide [hi]
  · simp +decide [hn]

/-- **Step 3**: the offsets `ps E`. -/
theorem stepPre_spec (g : Graph) (c₀ : Config) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S stepPre (fun c => DegInv g c₀ (idEdges g).length c ∧ c.reg rI = (idEdges g).length ∧
        c.reg gNE = (idEdges g).length)
      (fun c => PreInv g c₀ (numV g) c ∧ c.reg rI = numV g ∧ c.reg gN = numV g)
      (1 + (numV g * 11 + 3)) := by
  have h0 : HTB S (.const rAcc 0) (fun c => DegInv g c₀ (idEdges g).length c ∧
      c.reg rI = (idEdges g).length ∧ c.reg gNE = (idEdges g).length)
      (fun c => PreInv g c₀ 0 c ∧ c.reg gN = numV g) 1 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, _, _⟩ => ⟨trivial, ?_⟩
    have hL := layout_eqs g (c₀.reg rFREE)
    simp only [run_const]
    refine ⟨⟨(Glob.regIndep g c₀).setReg (by decide) _ hG, by simp +decide, ?_⟩, by
      simp +decide [hG.n]⟩
    simp only [setReg_mem]
    refine ⟨hM.same, by simpa [cnt_full] using hM.deg, ?_, hM.zero.mono (by omega)⟩
    intro i hi
    rw [hM.zero.get (by omega)]
    by_cases h : i ≤ 0
    · simp [show i = 0 by omega]
    · simp [h]
  have hl := HTB.forUpC (i := rI) (n := gN) (N := numV g) (body := preBody) (PreInv g c₀) 7
    (by decide) (by decide) (by decide) (fun j => by indep [PreInv, glob_iff])
    (fun j hj => preBody_spec g c₀ j hj hS)
  exact h0.seq hl

/-! ### Step 4: the CSR array -/

/-- The memory during the fill pass, with the neighbour lists `L` filled in so far. -/
structure FillMem (g : Graph) (c₀ : Config) (L : ℕ → List ℕ) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  off : Tab m (bOFF g (c₀.reg rFREE)) (numV g + 1) (ps (idEdges g))
  fil : Tab m (bFIL g (c₀.reg rFREE)) (numV g) fun v => (L v).length
  adj : ∀ v, v < numV g → Arr m (bADJ g (c₀.reg rFREE) + ps (idEdges g) v) (L v)
  len : ∀ v, v < numV g → (L v).length ≤ (nbOf (idEdges g) v).length
  zero : ZeroFrom m (bPRE g (c₀.reg rFREE))

/-- The invariant of the fill pass after `j` edges. -/
def FillInv (g : Graph) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  Glob g c₀ c ∧ FillMem g c₀ (nbOf ((idEdges g).take j)) c.mem

/-- Appending `w` to the list of `u`: two stores. -/
theorem FillMem.app {g : Graph} {c₀ : Config} {L : ℕ → List ℕ} {m : ℕ → ℕ} (h : FillMem g c₀ L m)
    {u : ℕ} (hu : u < numV g) (hlt : (L u).length < (nbOf (idEdges g) u).length) (w : ℕ) :
    FillMem g c₀ (R1.app L u w)
      (upd (upd m (bADJ g (c₀.reg rFREE) + (ps (idEdges g) u + (L u).length)) w)
        (bFIL g (c₀.reg rFREE) + u) ((L u).length + 1)) := by
  have hL := layout_eqs g (c₀.reg rFREE)
  have hps := idEdges_ps g
  have hu1 := ps_add_le (idEdges g) (show u < u + 1 by omega)
  have huN := ps_mono (idEdges g) (show u + 1 ≤ numV g by omega)
  rw [ps_succ] at huN
  refine ⟨(h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _,
    (h.off.upd_of_disjoint (by omega)).upd_of_disjoint (by omega), ?_, ?_, ?_,
    (h.zero.upd (by omega)).upd (by omega)⟩
  · refine ((h.fil.upd_of_disjoint (by omega)).upd rfl).congr_fun fun v _ => ?_
    rw [length_app]; rfl
  · intro v hv
    by_cases hvu : v = u
    · subst hvu
      simp only [R1.app, Function.update_self]
      exact (h.adj v hv).upd_snoc (by omega) |>.upd_of_disjoint (by simp; omega)
    · simp only [R1.app, Function.update_of_ne hvu]
      have hlv := h.len v hv
      refine ((h.adj v hv).upd_of_disjoint ?_).upd_of_disjoint (by omega)
      rcases Nat.lt_or_gt_of_ne hvu with hvu' | hvu'
      · have := ps_add_le (idEdges g) hvu'
        right; omega
      · have := ps_mono (idEdges g) (show u + 1 ≤ v by omega)
        rw [ps_succ] at this
        left; omega
  · intro v hv
    by_cases hvu : v = u
    · subst hvu; simp only [R1.app, Function.update_self, List.length_append,
        List.length_singleton]; omega
    · simp only [R1.app, Function.update_of_ne hvu]; exact h.len v hv

theorem loopFree_put (x y : ℕ) : LoopFree (put x y) := by simp [put, LoopFree]
theorem wregs_put (x y : ℕ) : wregs (put x y) = [rX, rX, rY, rY, rY, rT, rT, rX, rT] := rfl

/-- Appending the vertex in register `y` to the list of the vertex in register `x`. -/
theorem put_run {g : Graph} {c₀ c : Config} {L : ℕ → List ℕ} {x y u w : ℕ}
    (hxy : x = rU ∧ y = rV ∨ x = rV ∧ y = rU) (hG : Glob g c₀ c) (hM : FillMem g c₀ L c.mem)
    (hxu : c.reg x = u) (hyw : c.reg y = w) (hu : u < numV g)
    (hlt : (L u).length < (nbOf (idEdges g) u).length) :
    Glob g c₀ (run (put x y) c) ∧ FillMem g c₀ (R1.app L u w) (run (put x y) c).mem ∧
      ∀ r, r ≠ rX → r ≠ rY → r ≠ rT → (run (put x y) c).reg r = c.reg r := by
  have hfu : c.mem (bFIL g (c₀.reg rFREE) + u) = (L u).length := hM.fil.get hu
  have hou : c.mem (bOFF g (c₀.reg rFREE) + u) = ps (idEdges g) u := hM.off.get (by omega)
  have hreg : ∀ r, r ≠ rX → r ≠ rY → r ≠ rT → (run (put x y) c).reg r = c.reg r :=
    fun r h1 h2 h3 => run_reg_of_not_mem (loopFree_put _ _) (by rw [wregs_put]; simp [h1, h2, h3]) c
  refine ⟨(Glob.regIndep g c₀).run_of_sub (loopFree_put _ _) (by rw [wregs_put]; decide) hG, ?_,
    hreg⟩
  have hx : x ≠ rX ∧ x ≠ rY ∧ x ≠ rT ∧ y ≠ rX ∧ y ≠ rY ∧ y ≠ rT := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨hx1, hx2, hx3, hy1, hy2, hy3⟩ := hx
  have := hM.app hu hlt w
  simpa +decide [put, run_inc, run_st, hG.fil, hG.off, hG.adj, hxu, hyw, hfu, hou, hx1, hx2, hx3,
    hy1, hy2, hy3] using this

/-- The addresses of `readEdge`: the input arrays of the edge ends. -/
theorem readEdge_addrOK {g : Graph} {c₀ c : Config} (hB : GraphBase g c₀) (hG : Glob g c₀ c)
    {j : ℕ} (hi : c.reg rI = j) (hj : j < (idEdges g).length) (hS : endL g (c₀.reg rFREE) ≤ S) :
    AddrOK S readEdge c := by
  have := hB.below
  have := fits g hS
  addr_ok [readEdge, hG.eu, hG.ev, hi]

/-- The addresses of `put x y` (hypotheses of `put_run`). -/
theorem put_addrOK {g : Graph} {c₀ c : Config} {L : ℕ → List ℕ} {x y u : ℕ}
    (hxy : x = rU ∧ y = rV ∨ x = rV ∧ y = rU) (hG : Glob g c₀ c) (hM : FillMem g c₀ L c.mem)
    (hxu : c.reg x = u) (hu : u < numV g) (hlt : (L u).length < (nbOf (idEdges g) u).length)
    (hS : endL g (c₀.reg rFREE) ≤ S) : AddrOK S (put x y) c := by
  have hfu : c.mem (bFIL g (c₀.reg rFREE) + u) = (L u).length := hM.fil.get hu
  have hou : c.mem (bOFF g (c₀.reg rFREE) + u) = ps (idEdges g) u := hM.off.get (by omega)
  have := fits g hS
  have hps := idEdges_ps g
  have huN := ps_mono (idEdges g) (show u + 1 ≤ numV g by omega)
  rw [ps_succ] at huN
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> addr_ok [put, hG.fil, hG.off, hG.adj, hxu, hfu, hou]

theorem fillBody_spec (g : Graph) (c₀ : Config) (hB : GraphBase g c₀) (j : ℕ)
    (hj : j < (idEdges g).length) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S fillBody (fun c => FillInv g c₀ j c ∧ c.reg rI = j ∧ c.reg gNE = (idEdges g).length)
      (fun c => FillInv g c₀ (j + 1) c ∧ c.reg rI = j ∧ c.reg gNE = (idEdges g).length) 28 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hi, hn⟩ => ?_
  obtain ⟨hU, hV, hAg⟩ := readEdge_run hB hG hM.same hi hj
  obtain ⟨ha, hb⟩ := idEdges_lt_get hj
  have hne := idEdges_ne hj
  have hsucc := nbOf_take_succ_eq hj hne
  have hla : (nbOf ((idEdges g).take j) (idEdges g)[j].1).length <
      (nbOf (idEdges g) (idEdges g)[j].1).length := by
    have h1 := length_nbOf_take_le (idEdges g) (j + 1) (idEdges g)[j].1
    rw [hsucc] at h1
    simp only [R1.app, Function.update_of_ne hne, Function.update_self, List.length_append,
      List.length_singleton] at h1
    omega
  have hlb : (R1.app (nbOf ((idEdges g).take j)) (idEdges g)[j].1 (idEdges g)[j].2
      (idEdges g)[j].2).length < (nbOf (idEdges g) (idEdges g)[j].2).length := by
    have h1 := length_nbOf_take_le (idEdges g) (j + 1) (idEdges g)[j].2
    rw [hsucc] at h1
    simp only [R1.app, Function.update_self, List.length_append, List.length_singleton] at h1 ⊢
    rw [Function.update_of_ne hne.symm] at h1 ⊢
    omega
  have hG₁ : Glob g c₀ (run readEdge c) := (Glob.regIndep g c₀).indep.mono (by decide) _ _ hAg hG
  have hM₁ : FillMem g c₀ (nbOf ((idEdges g).take j)) (run readEdge c).mem := by
    rw [hAg.mem]; exact hM
  obtain ⟨hG₂, hM₂, hr₂⟩ := put_run (Or.inl ⟨rfl, rfl⟩) hG₁ hM₁ hU hV ha hla
  have hV₂ : (run (put rU rV) (run readEdge c)).reg rV = (idEdges g)[j].2 := by
    rw [hr₂ _ (by decide) (by decide) (by decide), hV]
  obtain ⟨hG₃, hM₃, hr₃⟩ := put_run (Or.inr ⟨rfl, rfl⟩) hG₂ hM₂ hV₂
    (by rw [hr₂ _ (by decide) (by decide) (by decide), hU]) hb hlb
  rw [← hsucc] at hM₃
  refine ⟨(readEdge_addrOK hB hG hi hj hS).seq ((put_addrOK (Or.inl ⟨rfl, rfl⟩) hG₁ hM₁ hU ha hla
    hS).seq (put_addrOK (Or.inr ⟨rfl, rfl⟩) hG₂ hM₂ hV₂ hb hlb hS)), ?_⟩
  simp only [fillBody, run_seq']
  refine ⟨⟨hG₃, hM₃⟩, ?_, ?_⟩
  · rw [hr₃ _ (by decide) (by decide) (by decide), hr₂ _ (by decide) (by decide) (by decide),
      hAg.reg _ (by decide), hi]
  · rw [hr₃ _ (by decide) (by decide) (by decide), hr₂ _ (by decide) (by decide) (by decide),
      hAg.reg _ (by decide), hn]

/-- **Step 4**: the CSR array. -/
theorem stepFill_spec (g : Graph) (c₀ : Config) (hB : GraphBase g c₀) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S stepFill (fun c => FillInv g c₀ 0 c ∧ c.reg gNE = (idEdges g).length)
      (fun c => FillInv g c₀ (idEdges g).length c ∧ c.reg rI = (idEdges g).length ∧
        c.reg gNE = (idEdges g).length) ((idEdges g).length * 32 + 3) :=
  HTB.forUpC (i := rI) (n := gNE) (N := (idEdges g).length) (body := fillBody) (FillInv g c₀) 28
    (by decide) (by decide) (by decide) (fun j => by indep [FillInv, glob_iff])
    (fun j hj => fillBody_spec g c₀ hB j hj hS)

/-! ### Steps 1–4 -/

/-- The CSR arrays, fixed from the end of step 4 on. -/
structure CsrMem (g : Graph) (c₀ : Config) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  off : Tab m (bOFF g (c₀.reg rFREE)) (numV g + 1) (ps (idEdges g))
  adj : ∀ v, v < numV g → Arr m (bADJ g (c₀.reg rFREE) + ps (idEdges g) v) (nbOf (idEdges g) v)

/-- Stores into the arrays of the search keep the CSR arrays. -/
theorem CsrMem.upd {g : Graph} {c₀ : Config} {m : ℕ → ℕ} (h : CsrMem g c₀ m) {a : ℕ}
    (ha : bPRE g (c₀.reg rFREE) ≤ a) (v : ℕ) : CsrMem g c₀ (RAM.upd m a v) := by
  have hL := layout_eqs g (c₀.reg rFREE)
  have hps := idEdges_ps g
  refine ⟨h.same.upd_of_ge (by omega) _, h.off.upd_of_disjoint (by omega), fun u hu => ?_⟩
  have := ps_mono (idEdges g) (show u + 1 ≤ numV g by omega)
  rw [ps_succ] at this
  exact (h.adj u hu).upd_of_disjoint (by omega)

/-- **Steps 1–4**: allocation and the CSR neighbour lists. -/
theorem stepCsr_spec (g : Graph) (c₀ : Config) (hB : GraphBase g c₀) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S stepCsr (fun c => c = c₀)
      (fun c => Glob g c₀ c ∧ CsrMem g c₀ c.mem ∧ ZeroFrom c.mem (bPRE g (c₀.reg rFREE)))
      (34 + ((idEdges g).length * 20 + 3 + (1 + (numV g * 11 + 3) +
        ((idEdges g).length * 32 + 3)))) := by
  have h3 := (stepPre_spec g c₀ hS).post (Q' := fun c => FillInv g c₀ 0 c ∧
      c.reg gNE = (idEdges g).length) fun c ⟨⟨hG, _, hM⟩, _, _⟩ => by
    have hL := layout_eqs g (c₀.reg rFREE)
    refine ⟨⟨hG, hM.same, hM.off.congr_fun fun i hi => by simp [show i ≤ numV g by omega], ?_,
      fun v _ => by simp, fun v _ => by simp, hM.zero.mono (by omega)⟩, hG.ne⟩
    simpa [cnt_zero] using hM.zero.tab (b := bFIL g (c₀.reg rFREE)) le_rfl (numV g)
  have h4 := (stepFill_spec g c₀ hB hS).post (Q' := fun c => Glob g c₀ c ∧ CsrMem g c₀ c.mem ∧
      ZeroFrom c.mem (bPRE g (c₀.reg rFREE))) fun c ⟨⟨hG, hM⟩, _, _⟩ => by
    rw [List.take_length] at hM
    exact ⟨hG, ⟨hM.same, hM.off, hM.adj⟩, hM.zero⟩
  exact (alloc1_spec g c₀ hB).seq ((stepDeg_spec g c₀ hB hS).seq (h3.seq h4))

end STACS2027.RAM.R1
