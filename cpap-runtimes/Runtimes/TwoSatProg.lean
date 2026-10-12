module

public import Outerplanar.RAM.BoundedLib
public import Runtimes.TwoSatSpec
import Mathlib.Tactic

/-!
# Linear-time 2-SAT on the RAM: registers, layout, allocation, complements and arcs

The 2-SAT phase of the machine works on a 2-CNF over `n` variables with `m` clauses, given
as the list `cl` of the `2m` literal codes (`TwoSat.codes f`) stored at `tCL`. With
`N = 2n` nodes and `M = 2m` arcs it

1. `allocT`: allocates (all zero, since fresh) the arrays `NEG` (`N` cells), `AU`, `AV`
   (`M`), `DEG` (`N`), `OFF` (`N + 1`), `FIL` (`N`), `ADJ` (`M`), `LAB`, `PTR`, `STK`, `SS`,
   `BB` (`N` each) and the output `AS` (`n` cells), in this order from the initial `rFREE`;
2. `stepNeg`: `NEG[u] = neg u` for `u < N` (`NEG[2x] = 2x + 1`, `NEG[2x + 1] = 2x`);
3. `stepArc`: the arcs `AU[k] → AV[k]` of `arcsOfCodes cl`: for clause `j` with codes
   `a = cl[2j]`, `b = cl[2j + 1]`, arc `2j` is `neg a → b` and arc `2j + 1` is `neg b → a`;
4. the out-neighbour lists in CSR form (`TwoSatCsr.lean`); 5. the path-based search
   (`TwoSatSearch.lean`); 6. the answer (`TwoSatPhase.lean`).

## Registers (block `200–249`)
* interface: `tN = 200` (`n`), `tM = 201` (`m`), `tCL = 202` (base of the codes), and the
  outputs `tOK = 203` (`1` iff satisfiable) and `tAS = 204` (base of the assignment);
* globals of the phase `205–223`, scratch `230–241`.
The phase writes no other register except the macro temporary `rT` and `rFREE`.

## Space
Every triple is stated within a bound `S` on the accessed addresses (`HTB S`), under the
hypothesis `hS : endL n m F ≤ S` (`F` the initial `rFREE`): the phase reads the codes (below
`F`) and its own arrays (`F … endL n m F`, `endL_le`: at most `F + 19 (n + m + 1)` cells).
The regions enter the address proofs through `fits` (one inequality per region).
-/

@[expose] public section

namespace STACS2027.Runtimes.TwoSat

open STACS2027.RAM

variable {S : ℕ}

/-! ### Registers -/

/-- Interface: the number of variables `n`. -/
abbrev tN : ℕ := 200
/-- Interface: the number of clauses `m`. -/
abbrev tM : ℕ := 201
/-- Interface: the base of the `2m` literal codes. -/
abbrev tCL : ℕ := 202
/-- Output: `1` if the formula is satisfiable, `0` otherwise. -/
abbrev tOK : ℕ := 203
/-- Output: the base of the assignment (`n` cells holding `0` or `1`). -/
abbrev tAS : ℕ := 204
/-- `N = 2n`, the number of nodes. -/
abbrev tN2 : ℕ := 205
/-- `M = 2m`, the number of arcs. -/
abbrev tM2 : ℕ := 206
/-- Base of `NEG` (complements). -/
abbrev tNEG : ℕ := 207
/-- Base of `AU` (arc tails). -/
abbrev tAU : ℕ := 208
/-- Base of `AV` (arc heads). -/
abbrev tAV : ℕ := 209
/-- Base of `DEG` (out-degrees). -/
abbrev tDEG : ℕ := 210
/-- Base of `OFF` (CSR offsets). -/
abbrev tOFF : ℕ := 211
/-- Base of `FIL` (fill counters). -/
abbrev tFIL : ℕ := 212
/-- Base of `ADJ` (CSR out-neighbours). -/
abbrev tADJ : ℕ := 213
/-- Base of `LAB` (labels of the search). -/
abbrev tLAB : ℕ := 214
/-- Base of `PTR` (arc pointers of the search). -/
abbrev tPTR : ℕ := 215
/-- Base of `STK` (the search stack, bottom first). -/
abbrev tSTK : ℕ := 216
/-- Base of `SS` (the stack `S` of the search). -/
abbrev tSS : ℕ := 217
/-- Base of `BB` (the boundary stack `B`, bottom first). -/
abbrev tBB : ℕ := 218
/-- The size of the search stack. -/
abbrev tSP : ℕ := 219
/-- The size of `S`. -/
abbrev tSSP : ℕ := 220
/-- The size of `B`. -/
abbrev tBP : ℕ := 221
/-- The next root candidate. -/
abbrev tNXT : ℕ := 222
/-- The label of the next component, `N + 1 + nc`. -/
abbrev tVAL : ℕ := 223
/-- Scratch: loop counter. -/
abbrev sI : ℕ := 230
/-- Scratch. -/
abbrev sX : ℕ := 231
/-- Scratch. -/
abbrev sY : ℕ := 232
/-- Scratch. -/
abbrev sU : ℕ := 233
/-- Scratch. -/
abbrev sV : ℕ := 234
/-- Scratch. -/
abbrev sP : ℕ := 235
/-- Scratch. -/
abbrev sA : ℕ := 236
/-- Scratch. -/
abbrev sB : ℕ := 237
/-- Scratch. -/
abbrev sW : ℕ := 238
/-- Scratch. -/
abbrev sH : ℕ := 239
/-- Scratch: running sum. -/
abbrev sAcc : ℕ := 240
/-- Scratch. -/
abbrev sQ : ℕ := 241

/-! ### The interface -/

/-- The state on entry to the 2-SAT phase: `n` in `tN`, `m` in `tM`, the codes `cl` at `tCL`,
free memory from `rFREE` on. -/
structure TwoSatIn (n m : ℕ) (cl : List ℕ) (c : Config) : Prop where
  rn : c.reg tN = n
  rm : c.reg tM = m
  codes : Arr c.mem (c.reg tCL) cl
  free : ZeroFrom c.mem (c.reg rFREE)
  below : c.reg tCL + cl.length ≤ c.reg rFREE

/-! ### The layout -/

section layout

variable (n m F : ℕ)

/-- `AU` (`M` cells); `NEG` is at `F` (`N` cells). -/
def bAU : ℕ := F + 2 * n
/-- `AV` (`M` cells). -/
def bAV : ℕ := bAU n F + 2 * m
/-- `DEG` (`N` cells). -/
def bDEG : ℕ := bAV n m F + 2 * m
/-- `OFF` (`N + 1` cells). -/
def bOFF : ℕ := bDEG n m F + 2 * n
/-- `FIL` (`N` cells). -/
def bFIL : ℕ := bOFF n m F + (2 * n + 1)
/-- `ADJ` (`M` cells). -/
def bADJ : ℕ := bFIL n m F + 2 * n
/-- `LAB` (`N` cells). -/
def bLAB : ℕ := bADJ n m F + 2 * m
/-- `PTR` (`N` cells). -/
def bPTR : ℕ := bLAB n m F + 2 * n
/-- `STK` (`N` cells). -/
def bSTK : ℕ := bPTR n m F + 2 * n
/-- `SS` (`N` cells). -/
def bSS : ℕ := bSTK n m F + 2 * n
/-- `BB` (`N` cells). -/
def bBB : ℕ := bSS n m F + 2 * n
/-- `AS` (`n` cells, the output). -/
def bAS : ℕ := bBB n m F + 2 * n
/-- The end of the memory of the phase. -/
def endL : ℕ := bAS n m F + n

/-- The layout as equations (for `omega`). -/
theorem layout_eqs : bAU n F = F + 2 * n ∧ bAV n m F = bAU n F + 2 * m ∧
    bDEG n m F = bAV n m F + 2 * m ∧ bOFF n m F = bDEG n m F + 2 * n ∧
    bFIL n m F = bOFF n m F + (2 * n + 1) ∧ bADJ n m F = bFIL n m F + 2 * n ∧
    bLAB n m F = bADJ n m F + 2 * m ∧ bPTR n m F = bLAB n m F + 2 * n ∧
    bSTK n m F = bPTR n m F + 2 * n ∧ bSS n m F = bSTK n m F + 2 * n ∧
    bBB n m F = bSS n m F + 2 * n ∧ bAS n m F = bBB n m F + 2 * n ∧ endL n m F = bAS n m F + n :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The memory of the phase is linear: `endL n m F ≤ F + 19 (n + m + 1)`. -/
theorem endL_le : endL n m F ≤ F + 19 * (n + m + 1) := by
  have := layout_eqs n m F; omega

end layout

/-- The regions of the phase fit below `S` (one inequality per region). -/
theorem fits {n m F : ℕ} (hS : endL n m F ≤ S) :
    F + 2 * n ≤ S ∧ bAU n F + 2 * m ≤ S ∧ bAV n m F + 2 * m ≤ S ∧ bDEG n m F + 2 * n ≤ S ∧
      bOFF n m F + (2 * n + 1) ≤ S ∧ bFIL n m F + 2 * n ≤ S ∧ bADJ n m F + 2 * m ≤ S ∧
      bLAB n m F + 2 * n ≤ S ∧ bPTR n m F + 2 * n ≤ S ∧ bSTK n m F + 2 * n ≤ S ∧
      bSS n m F + 2 * n ≤ S ∧ bBB n m F + 2 * n ≤ S ∧ bAS n m F + n ≤ S := by
  have := layout_eqs n m F; omega

/-! ### Allocation, complements, arcs: the program -/

/-- Step 1: `N := 2n`, `M := 2m`, and the allocation of all arrays. -/
def allocT : Stmt :=
  .seq (.add tN2 tN tN) (.seq (.add tM2 tM tM) (.seq (alloc tNEG tN2) (.seq (alloc tAU tM2)
    (.seq (alloc tAV tM2) (.seq (alloc tDEG tN2) (.seq (addc sX tN2 1) (.seq (alloc tOFF sX)
    (.seq (alloc tFIL tN2) (.seq (alloc tADJ tM2) (.seq (alloc tLAB tN2) (.seq (alloc tPTR tN2)
    (.seq (alloc tSTK tN2) (.seq (alloc tSS tN2) (.seq (alloc tBB tN2) (alloc tAS tN)))))))))))))))

/-- One variable of the complement table: `NEG[2i] := 2i + 1`, `NEG[2i + 1] := 2i`. -/
def negBody : Stmt :=
  .seq (.add sP sI sI) (.seq (addc sY sP 1) (.seq (st tNEG sP sY) (st tNEG sY sP)))

/-- Step 2: the complement table. -/
def stepNeg : Stmt := forUp sI tN negBody

/-- One clause: `a = cl[2i]`, `b = cl[2i + 1]`; arcs `neg a → b` (number `2i`) and `neg b → a`
(number `2i + 1`). -/
def arcBody : Stmt :=
  .seq (.add sP sI sI) (.seq (addc sQ sP 1) (.seq (ld sU tCL sP) (.seq (ld sV tCL sQ)
    (.seq (ld sX tNEG sU) (.seq (ld sY tNEG sV) (.seq (st tAU sP sX) (.seq (st tAV sP sV)
    (.seq (st tAU sQ sY) (st tAV sQ sU)))))))))

/-- Step 3: the arcs. -/
def stepArc : Stmt := forUp sI tM arcBody

/-! ### Global registers fixed after the allocation -/

/-- The registers that keep their value from the end of step 1 on (`F = c₀.reg rFREE`). -/
@[mk_iff] structure Glob (n m : ℕ) (c₀ c : Config) : Prop where
  rn : c.reg tN = n
  rm : c.reg tM = m
  rcl : c.reg tCL = c₀.reg tCL
  rn2 : c.reg tN2 = 2 * n
  rm2 : c.reg tM2 = 2 * m
  rfree : c.reg rFREE = endL n m (c₀.reg rFREE)
  rneg : c.reg tNEG = c₀.reg rFREE
  rau : c.reg tAU = bAU n (c₀.reg rFREE)
  rav : c.reg tAV = bAV n m (c₀.reg rFREE)
  rdeg : c.reg tDEG = bDEG n m (c₀.reg rFREE)
  roff : c.reg tOFF = bOFF n m (c₀.reg rFREE)
  rfil : c.reg tFIL = bFIL n m (c₀.reg rFREE)
  radj : c.reg tADJ = bADJ n m (c₀.reg rFREE)
  rlab : c.reg tLAB = bLAB n m (c₀.reg rFREE)
  rptr : c.reg tPTR = bPTR n m (c₀.reg rFREE)
  rstk : c.reg tSTK = bSTK n m (c₀.reg rFREE)
  rss : c.reg tSS = bSS n m (c₀.reg rFREE)
  rbb : c.reg tBB = bBB n m (c₀.reg rFREE)
  ras : c.reg tAS = bAS n m (c₀.reg rFREE)

/-- The registers written after step 1. -/
def WT : List ℕ := [rT, tOK, tSP, tSSP, tBP, tNXT, tVAL, sI, sX, sY, sU, sV, sP, sA, sB, sW, sH,
  sAcc, sQ]

theorem Glob.regIndep (n m : ℕ) (c₀ : Config) : RegIndep WT (Glob n m c₀) := by indep [glob_iff]

/-- The codes, in a memory that agrees with the initial one below `F`. -/
theorem codes_get {n m : ℕ} {cl : List ℕ} {c₀ : Config} (hB : TwoSatIn n m cl c₀) {mm : ℕ → ℕ}
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem mm) {k : ℕ} (hk : k < cl.length) :
    mm (c₀.reg tCL + k) = cl.getD k 0 :=
  (hB.codes.of_below hS hB.below).getD hk

/-! ### The arcs as functions -/

/-- Tail of arc `k`. -/
def au (cl : List ℕ) (k : ℕ) : ℕ := ((arcsOfCodes cl).getD k (0, 0)).1
/-- Head of arc `k`. -/
def av (cl : List ℕ) (k : ℕ) : ℕ := ((arcsOfCodes cl).getD k (0, 0)).2

theorem length_arcsOfCodes : ∀ (m : ℕ) (cl : List ℕ), cl.length = 2 * m →
    (arcsOfCodes cl).length = 2 * m
  | 0, [], _ => rfl
  | m + 1, a :: b :: rest, h => by
    simp only [arcsOfCodes, List.length_cons]
    rw [length_arcsOfCodes m rest (by simp at h; omega)]; ring
  | 0, _ :: _, h => by simp at h
  | m + 1, [], h => by simp at h
  | m + 1, [_], h => by simp at h; omega

/-- The two arcs of clause `j`. -/
theorem arcs_get : ∀ (cl : List ℕ) (j : ℕ), 2 * j + 1 < cl.length →
    au cl (2 * j) = neg (cl.getD (2 * j) 0) ∧ av cl (2 * j) = cl.getD (2 * j + 1) 0 ∧
    au cl (2 * j + 1) = neg (cl.getD (2 * j + 1) 0) ∧ av cl (2 * j + 1) = cl.getD (2 * j) 0
  | a :: b :: rest, 0, _ => by simp [au, av, arcsOfCodes]
  | a :: b :: rest, j + 1, h => by
    have := arcs_get rest j (by simp at h; omega)
    simp only [au, av] at this ⊢
    rw [show 2 * (j + 1) = 2 * j + 2 by ring]
    simpa [arcsOfCodes] using this
  | [], _, h => by simp at h
  | [_], _, h => by simp at h

/-! ### Step 1: allocation -/

/-- The memory during step 2, after `j` variables. -/
structure NegMem (n m : ℕ) (c₀ : Config) (j : ℕ) (mm : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem mm
  tneg : Tab mm (c₀.reg rFREE) (2 * j) neg
  zero : ZeroFrom mm (bAU n (c₀.reg rFREE))

/-- The invariant of step 2 after `j` variables. -/
def NegInv (n m : ℕ) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  Glob n m c₀ c ∧ NegMem n m c₀ j c.mem

theorem allocT_spec (n m : ℕ) (cl : List ℕ) (c₀ : Config) (hB : TwoSatIn n m cl c₀) :
    HTB S allocT (fun c => c = c₀) (fun c => NegInv n m c₀ 0 c ∧ c.reg tN = n) 46 :=
    HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  have hL := layout_eqs n m (c.reg rFREE)
  simp only [allocT, run_seq', run_add, run_addc (show tN2 ≠ rT by decide),
    run_alloc (show tN2 ≠ rT by decide) (show tNEG ≠ tN2 by decide),
    run_alloc (show tM2 ≠ rT by decide) (show tAU ≠ tM2 by decide),
    run_alloc (show tM2 ≠ rT by decide) (show tAV ≠ tM2 by decide),
    run_alloc (show tN2 ≠ rT by decide) (show tDEG ≠ tN2 by decide),
    run_alloc (show sX ≠ rT by decide) (show tOFF ≠ sX by decide),
    run_alloc (show tN2 ≠ rT by decide) (show tFIL ≠ tN2 by decide),
    run_alloc (show tM2 ≠ rT by decide) (show tADJ ≠ tM2 by decide),
    run_alloc (show tN2 ≠ rT by decide) (show tLAB ≠ tN2 by decide),
    run_alloc (show tN2 ≠ rT by decide) (show tPTR ≠ tN2 by decide),
    run_alloc (show tN2 ≠ rT by decide) (show tSTK ≠ tN2 by decide),
    run_alloc (show tN2 ≠ rT by decide) (show tSS ≠ tN2 by decide),
    run_alloc (show tN2 ≠ rT by decide) (show tBB ≠ tN2 by decide),
    run_alloc (show tN ≠ rT by decide) (show tAS ≠ tN by decide)]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  all_goals try (simp +decide [hB.rn, hB.rm] <;> omega)
  simp only [setReg_mem]
  exact ⟨SameOn.refl _ _, by simp, hB.free.mono (by omega)⟩

/-! ### Step 2: complements -/

theorem NegMem.snoc {n m : ℕ} {c₀ : Config} {j : ℕ} {mm : ℕ → ℕ} (h : NegMem n m c₀ j mm)
    (hj : j < n) :
    NegMem n m c₀ (j + 1) (upd (upd mm (c₀.reg rFREE + 2 * j) (2 * j + 1))
      (c₀.reg rFREE + (2 * j + 1)) (2 * j)) := by
  have hL := layout_eqs n m (c₀.reg rFREE)
  refine ⟨(h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _, ?_,
    (h.zero.upd (by omega)).upd (by omega)⟩
  have h1 := (h.tneg.upd_of_disjoint (a := c₀.reg rFREE + 2 * j) (v := 2 * j + 1)
    (by omega)).snoc (by simp [neg_even])
  have h2 := (h1.upd_of_disjoint (a := c₀.reg rFREE + (2 * j + 1)) (v := 2 * j)
    (by omega)).snoc (by simp [neg_odd])
  rwa [show 2 * j + 1 + 1 = 2 * (j + 1) by ring] at h2

theorem negBody_spec (n m : ℕ) (c₀ : Config) (hS : endL n m (c₀.reg rFREE) ≤ S) (j : ℕ)
    (hj : j < n) :
    HTB S negBody (fun c => NegInv n m c₀ j c ∧ c.reg sI = j ∧ c.reg tN = n)
      (fun c => NegInv n m c₀ (j + 1) c ∧ c.reg sI = j ∧ c.reg tN = n) 8 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hG, _⟩, hi, _⟩ => by
    have := fits hS
    addr_ok [negBody, hG.rneg, hi]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hi, hn⟩ => ?_
  refine ⟨⟨(Glob.regIndep n m c₀).run_of_sub (by decide) (by decide) hG, ?_⟩, ?_, ?_⟩ <;>
    simp only [negBody, run_seq', run_add, run_addc (show sP ≠ rT by decide),
      run_st (show sY ≠ rT by decide), run_st (show sP ≠ rT by decide)]
  · have := hM.snoc hj
    simpa +decide [hG.rneg, hi, show j + j = 2 * j by ring, show 2 * j + 1 = j + j + 1 by ring]
      using this
  · simp +decide [hi]
  · simp +decide [hn]

theorem stepNeg_spec (n m : ℕ) (c₀ : Config) (hS : endL n m (c₀.reg rFREE) ≤ S) :
    HTB S stepNeg (fun c => NegInv n m c₀ 0 c ∧ c.reg tN = n)
      (fun c => NegInv n m c₀ n c ∧ c.reg sI = n ∧ c.reg tN = n) (n * 12 + 3) :=
  HTB.forUpC (i := sI) (n := tN) (N := n) (body := negBody) (NegInv n m c₀) 8
    (by decide) (by decide) (by decide) (fun j => by indep [NegInv, glob_iff])
    (fun j hj => negBody_spec n m c₀ hS j hj)

/-! ### Step 3: arcs -/

/-- The memory during step 3, after `j` clauses. -/
structure ArcMem (n m : ℕ) (cl : List ℕ) (c₀ : Config) (j : ℕ) (mm : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem mm
  tneg : Tab mm (c₀.reg rFREE) (2 * n) neg
  tau : Tab mm (bAU n (c₀.reg rFREE)) (2 * j) (au cl)
  tav : Tab mm (bAV n m (c₀.reg rFREE)) (2 * j) (av cl)
  zero : ZeroFrom mm (bDEG n m (c₀.reg rFREE))

/-- The invariant of step 3 after `j` clauses. -/
def ArcInv (n m : ℕ) (cl : List ℕ) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  Glob n m c₀ c ∧ ArcMem n m cl c₀ j c.mem

theorem ArcMem.snoc {n m : ℕ} {cl : List ℕ} {c₀ : Config} {j : ℕ} {mm : ℕ → ℕ}
    (h : ArcMem n m cl c₀ j mm) (hj : j < m) (hcl : cl.length = 2 * m) :
    ArcMem n m cl c₀ (j + 1)
      (upd (upd (upd (upd mm (bAU n (c₀.reg rFREE) + 2 * j) (neg (cl.getD (2 * j) 0)))
        (bAV n m (c₀.reg rFREE) + 2 * j) (cl.getD (2 * j + 1) 0))
        (bAU n (c₀.reg rFREE) + (2 * j + 1)) (neg (cl.getD (2 * j + 1) 0)))
        (bAV n m (c₀.reg rFREE) + (2 * j + 1)) (cl.getD (2 * j) 0)) := by
  have hL := layout_eqs n m (c₀.reg rFREE)
  obtain ⟨e1, e2, e3, e4⟩ := arcs_get cl j (by omega)
  refine ⟨(((h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge
    (by omega) _, (((h.tneg.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint
    (by omega)).upd_of_disjoint (by omega), ?_, ?_,
    (((h.zero.upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)⟩
  · have h1 := (((h.tau.upd_of_disjoint (a := bAU n (c₀.reg rFREE) + 2 * j)
      (v := neg (cl.getD (2 * j) 0)) (by omega)).snoc (by simp [e1])).upd_of_disjoint
      (a := bAV n m (c₀.reg rFREE) + 2 * j) (v := cl.getD (2 * j + 1) 0) (by omega))
    have h2 := ((h1.upd_of_disjoint (a := bAU n (c₀.reg rFREE) + (2 * j + 1))
      (v := neg (cl.getD (2 * j + 1) 0)) (by omega)).snoc (by simp [e3, hL])).upd_of_disjoint
      (a := bAV n m (c₀.reg rFREE) + (2 * j + 1)) (v := cl.getD (2 * j) 0) (by omega)
    rwa [show 2 * j + 1 + 1 = 2 * (j + 1) by ring] at h2
  · have h1 := (((h.tav.upd_of_disjoint (a := bAU n (c₀.reg rFREE) + 2 * j)
      (v := neg (cl.getD (2 * j) 0)) (by omega)).upd_of_disjoint
      (a := bAV n m (c₀.reg rFREE) + 2 * j) (v := cl.getD (2 * j + 1) 0) (by omega)).snoc
      (by simp [e2, hL]))
    have h2 := ((h1.upd_of_disjoint (a := bAU n (c₀.reg rFREE) + (2 * j + 1))
      (v := neg (cl.getD (2 * j + 1) 0)) (by omega)).upd_of_disjoint
      (a := bAV n m (c₀.reg rFREE) + (2 * j + 1)) (v := cl.getD (2 * j) 0) (by omega)).snoc
      (by simp [e4])
    rwa [show 2 * j + 1 + 1 = 2 * (j + 1) by ring] at h2

theorem arcBody_spec (n m : ℕ) (cl : List ℕ) (c₀ : Config) (hB : TwoSatIn n m cl c₀)
    (hcl : cl.length = 2 * m) (hok : CodesOk n cl) (hS : endL n m (c₀.reg rFREE) ≤ S) (j : ℕ)
    (hj : j < m) :
    HTB S arcBody (fun c => ArcInv n m cl c₀ j c ∧ c.reg sI = j ∧ c.reg tM = m)
      (fun c => ArcInv n m cl c₀ (j + 1) c ∧ c.reg sI = j ∧ c.reg tM = m) 21 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hi, hm⟩ => ?_
  have ha := codes_get hB hM.same (k := 2 * j) (by omega)
  have hb := codes_get hB hM.same (k := 2 * j + 1) (by omega)
  have hal : cl.getD (2 * j) 0 < 2 * n := by
    rw [getD_eq_getElem' (by omega)]; exact hok _ (List.getElem_mem _)
  have hbl : cl.getD (2 * j + 1) 0 < 2 * n := by
    rw [getD_eq_getElem' (by omega)]; exact hok _ (List.getElem_mem _)
  have hna := hM.tneg.get hal
  have hnb := hM.tneg.get hbl
  have e1 : j + j = 2 * j := by ring
  refine ⟨by
    have := fits hS
    have := hB.below
    addr_ok [arcBody, hG.rcl, hG.rneg, hG.rau, hG.rav, hi, e1, ha, hb], ?_⟩
  have hL := layout_eqs n m (c₀.reg rFREE)
  refine ⟨⟨(Glob.regIndep n m c₀).run_of_sub (by decide) (by decide) hG, ?_⟩, ?_, ?_⟩ <;>
    simp only [arcBody, run_seq', run_add, run_addc (show sP ≠ rT by decide), run_ld,
      run_st (show sX ≠ rT by decide), run_st (show sV ≠ rT by decide),
      run_st (show sY ≠ rT by decide), run_st (show sU ≠ rT by decide)]
  · have := hM.snoc hj hcl
    have e1 : j + j = 2 * j := by ring
    simp +decide only [setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hi, e1, hG.rcl,
      hG.rneg, hG.rau, hG.rav]
    rw [ha, hb, hna, hnb]
    have ne1 : bAU n (c₀.reg rFREE) + 2 * j ≠ c₀.reg tCL + (2 * j + 1) := by
      have := hB.below; omega
    simpa [ne1] using this
  · simp +decide [hi]
  · simp +decide [hm]

theorem stepArc_spec (n m : ℕ) (cl : List ℕ) (c₀ : Config) (hB : TwoSatIn n m cl c₀)
    (hcl : cl.length = 2 * m) (hok : CodesOk n cl) (hS : endL n m (c₀.reg rFREE) ≤ S) :
    HTB S stepArc (fun c => ArcInv n m cl c₀ 0 c ∧ c.reg tM = m)
      (fun c => ArcInv n m cl c₀ m c ∧ c.reg sI = m ∧ c.reg tM = m) (m * 25 + 3) :=
  HTB.forUpC (i := sI) (n := tM) (N := m) (body := arcBody) (ArcInv n m cl c₀) 21
    (by decide) (by decide) (by decide) (fun j => by indep [ArcInv, glob_iff])
    (fun j hj => arcBody_spec n m cl c₀ hB hcl hok hS j hj)

end STACS2027.Runtimes.TwoSat
