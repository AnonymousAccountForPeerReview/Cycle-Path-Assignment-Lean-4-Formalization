module

public import Outerplanar.RAM.R2Spec
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Phase R2 (low points and heads): the program and the low-point pass

Phase R2 starts in an `R1Post g` configuration `c₀` (`N = numV g` vertices, the CSR arrays
`OFF`, `ADJ`, the tables `PRE`, `PAR` and the preorder list `ORD` of the search `dfsOf g`) with
first free address `F`. It

1. `r2Alloc`: allocates the tables `LOW` (`gLOW = F`, `N` cells) and `HEAD`
   (`gHEAD = F + N`, `N` cells), both zero, `rFREE := F + 2 N`;
2. `stepLow`: for `i = 0, …, N - 1`, with `v = ORD[N - 1 - i]` (`vOf g i`): `rSK :=` the
   parent of `v` (or `N` for a root, `skOf g v`), `acc := PRE[v]`, and for the positions
   `p ∈ [OFF[v], OFF[v + 1])` with `w = ADJ[p]`: unless `w = rSK`,
   `acc := min acc (PAR[w] = v ? LOW[w] : PRE[w])`; then `LOW[v] := acc`. After `i` rounds
   `LOW` holds `lowF g i`; after the inner position `p`, `acc = accF … (p - OFF[v])`;
3. `stepHead` (in `R2.lean`): for `i = 0, …, N - 1`, with `v = ORD[i]`, `p = PAR[v]`:
   `HEAD[v] := v` if `p = v` or `PRE[p] ≤ LOW[v]`, else `HEAD[v] := HEAD[p]`.

This file contains the program, the register invariant `Glob`, the reads of the R1 data
(`rd_pre`, `rd_par`, `rd_ord`, `rd_off`, `rd_adj`) and the proof of steps 1–2
(`stepLow_spec`, in `90 |E| + 33 N + 3` steps).

Space: the triples are stated within a bound `S ≥ endL g F = F + 2N` (`HTB S`); the arrays of
R1 that are read lie below `F` (`R1Post.below`), and `fits` collects one inequality per region.
-/

@[expose] public section

namespace STACS2027.RAM.R2

open STACS2027.Algo

variable {S : ℕ}

/-! ### Scratch registers of the phase -/

/-- Loop counter (vertices). -/
abbrev rI : ℕ := 100
/-- The current vertex `v`. -/
abbrev rV : ℕ := 101
/-- The skipped neighbour of `v` (`skOf g v`). -/
abbrev rSK : ℕ := 102
/-- The low-point accumulator. -/
abbrev rAcc : ℕ := 103
/-- `OFF[v]`. -/
abbrev rA : ℕ := 104
/-- `OFF[v + 1]`. -/
abbrev rB : ℕ := 105
/-- Loop counter (positions in the CSR array). -/
abbrev rJ : ℕ := 106
/-- The current neighbour `w`. -/
abbrev rW : ℕ := 107
/-- A value read from memory. -/
abbrev rX : ℕ := 108
/-- A second value read from memory. -/
abbrev rY : ℕ := 109
/-- An index; the parent of `v` in the head pass. -/
abbrev rP : ℕ := 110

/-! ### The program -/

/-- Step 1: `LOW`, `HEAD` (`N` cells each). -/
def r2Alloc : Stmt := .seq (alloc gLOW gN) (alloc gHEAD gN)

/-- `v := ORD[N - 1 - i]`, `rSK := skOf g v`, `acc := PRE[v]`, `rA := OFF[v]`,
`rB := OFF[v + 1]`. -/
def lowHead : Stmt :=
  .seq (.sub rP gN rI) (.seq (dec rP) (.seq (ld rV gORD rP) (.seq (ld rSK gPAR rV)
    (.seq (ifEq rSK rV (mov rSK gN) .skip) (.seq (ld rAcc gPRE rV) (.seq (ld rA gOFF rV)
    (.seq (addc rP rV 1) (ld rB gOFF rP))))))))

/-- `acc := min acc (PAR[w] = v ? LOW[w] : PRE[w])`. -/
def lowMin : Stmt :=
  .seq (ld rY gPAR rW) (.seq (ld rX gPRE rW) (.seq (ifEq rY rV (ld rX gLOW rW) .skip)
    (ifLt rX rAcc (mov rAcc rX) .skip)))

/-- The neighbour `w = ADJ[j]`: skipped if it is `rSK`. -/
def lowInner : Stmt := .seq (ld rW gADJ rJ) (ifEq rW rSK .skip lowMin)

/-- One vertex of the low-point pass. -/
def lowBody : Stmt := .seq lowHead (.seq (forRange rJ rA rB lowInner) (st gLOW rV rAcc))

/-- Step 2: the low points, in reverse preorder. -/
def stepLow : Stmt := forUp rI gN lowBody

/-- `p ≠ v`: `HEAD[v] := PRE[p] ≤ LOW[v] ? v : HEAD[p]`. -/
def headElse : Stmt :=
  .seq (ld rX gPRE rP) (.seq (ld rY gLOW rV) (ifLe rX rY (st gHEAD rV rV)
    (.seq (ld rX gHEAD rP) (st gHEAD rV rX))))

/-- One vertex `v = ORD[i]` of the head pass, `p = PAR[v]`. -/
def headBody : Stmt :=
  .seq (ld rV gORD rI) (.seq (ld rP gPAR rV) (ifEq rP rV (st gHEAD rV rV) headElse))

/-- Step 3: the heads, in preorder. -/
def stepHead : Stmt := forUp rI gN headBody

/-- **Phase R2.** -/
def r2 : Stmt := .seq r2Alloc (.seq stepLow stepHead)

/-! ### Global registers fixed after the allocation -/

/-- The registers that keep their value from the end of step 1 on (`F = c₀.reg rFREE`). -/
@[mk_iff] structure Glob (g : Graph) (c₀ c : Config) : Prop where
  n : c.reg gN = numV g
  low : c.reg gLOW = c₀.reg rFREE
  head : c.reg gHEAD = c₀.reg rFREE + numV g
  free : c.reg rFREE = c₀.reg rFREE + numV g + numV g
  off : c.reg gOFF = c₀.reg gOFF
  adj : c.reg gADJ = c₀.reg gADJ
  pre : c.reg gPRE = c₀.reg gPRE
  par : c.reg gPAR = c₀.reg gPAR
  ord : c.reg gORD = c₀.reg gORD

/-- The registers written by steps 2–3. -/
def W2 : List ℕ := [rT, rI, rV, rSK, rAcc, rA, rB, rJ, rW, rX, rY, rP]

theorem Glob.regIndep (g : Graph) (c₀ : Config) : RegIndep W2 (Glob g c₀) := by indep [glob_iff]

/-! ### The layout -/

/-- The end of the memory used by R2: `LOW`, `HEAD` (`N` cells each) from the free address
`F`. -/
def endL (g : Graph) (F : ℕ) : ℕ := F + numV g + numV g

/-- The layout of R2 is linear. -/
theorem endL_le (g : Graph) (F : ℕ) : endL g F ≤ F + 4 * (g.length + 1) := by
  have := R0.numV_le g; unfold endL; omega

/-- The regions read or written by R2 fit below `S` (one inequality per region). -/
theorem fits {g : Graph} {c₀ : Config} (hR : R1Post g c₀) (hS : endL g (c₀.reg rFREE) ≤ S) :
    c₀.reg gOFF + (numV g + 1) ≤ S ∧ c₀.reg gADJ + 2 * (idEdges g).length ≤ S ∧
      c₀.reg gPRE + numV g ≤ S ∧ c₀.reg gPAR + numV g ≤ S ∧ c₀.reg gORD + numV g ≤ S ∧
      c₀.reg rFREE + numV g + numV g ≤ S := by
  have hb := hR.below
  rw [R1.length_csrAdj, R1.idEdges_ps, length_ord] at hb
  unfold endL at hS
  omega

/-! ### Reading the data of R1 -/

section reads

variable {g : Graph} {c₀ : Config} {m : ℕ → ℕ}

theorem rd_pre (hR : R1Post g c₀) (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {v : ℕ}
    (hv : v < numV g) : m (c₀.reg gPRE + v) = (dfsOf g).pre v :=
  (hR.pre.of_below hS hR.below.2.2.1).get hv

theorem rd_par (hR : R1Post g c₀) (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {v : ℕ}
    (hv : v < numV g) : m (c₀.reg gPAR + v) = (dfsOf g).par v :=
  (hR.par.of_below hS hR.below.2.2.2.1).get hv

theorem rd_ord (hR : R1Post g c₀) (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {k : ℕ}
    (hk : k < numV g) : m (c₀.reg gORD + k) = (dfsOf g).ord.getD k 0 :=
  (hR.ord.of_below hS hR.below.2.2.2.2).getD (by rw [length_ord]; exact hk)

theorem rd_off (hR : R1Post g c₀) (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {v : ℕ}
    (hv : v ≤ numV g) : m (c₀.reg gOFF + v) = R1.ps (idEdges g) v := by
  have h := hR.off.of_below hS (by simpa [R1.csrOff_eq] using hR.below.1)
  rw [h.get (by simp [R1.csrOff_eq]; omega)]
  simp [R1.csrOff_eq]

theorem rd_adj (hR : R1Post g c₀) (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {v k : ℕ}
    (hv : v < numV g) (hk : k < (nbOf (idEdges g) v).length) :
    m (c₀.reg gADJ + (R1.ps (idEdges g) v + k)) = (nbOf (idEdges g) v)[k] := by
  rw [← Nat.add_assoc]
  exact (arr_csrAdj_seg (hR.adj.of_below hS hR.below.2.1) hv).get hk

end reads

/-! ### Step 1: allocation -/

/-- The memory during the low-point pass, with the low points `f`. -/
structure LowMem (g : Graph) (c₀ : Config) (f : ℕ → ℕ) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  low : Tab m (c₀.reg rFREE) (numV g) f
  zero : ZeroFrom m (c₀.reg rFREE + numV g)

/-- Storing a low point. -/
theorem LowMem.upd {g : Graph} {c₀ : Config} {f : ℕ → ℕ} {m : ℕ → ℕ} (h : LowMem g c₀ f m)
    {v : ℕ} (hv : v < numV g) (x : ℕ) :
    LowMem g c₀ (Function.update f v x) (RAM.upd m (c₀.reg rFREE + v) x) :=
  ⟨h.same.upd_of_ge (by omega) _, h.low.upd rfl, h.zero.upd (by omega)⟩

/-- The invariant of the low-point pass after `i` vertices. -/
def LowInv (g : Graph) (c₀ : Config) (i : ℕ) (c : Config) : Prop :=
  Glob g c₀ c ∧ LowMem g c₀ (lowF g i) c.mem

theorem r2Alloc_spec (g : Graph) (c₀ : Config) (hR : R1Post g c₀) :
    HTB S r2Alloc (fun c => c = c₀) (fun c => LowInv g c₀ 0 c ∧ c.reg gN = numV g) 6 :=
    HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  have hn := hR.base.n
  simp only [r2Alloc, run_seq', run_alloc (show gN ≠ rT by decide) (show gLOW ≠ gN by decide),
    run_alloc (show gN ≠ rT by decide) (show gHEAD ≠ gN by decide)]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  all_goals try (simp +decide [hn] <;> omega)
  simp only [setReg_mem, lowF_zero]
  exact ⟨SameOn.refl _ _, hR.base.free.tab le_rfl _, hR.base.free.mono (by omega)⟩

/-! ### Step 2: the low points -/

/-- The invariant of the inner loop (vertex `vOf g i`, CSR position `j`). -/
def InInv (g : Graph) (c₀ : Config) (i j : ℕ) (c : Config) : Prop :=
  Glob g c₀ c ∧ LowMem g c₀ (lowF g i) c.mem ∧ c.reg rI = i ∧ c.reg rV = vOf g i ∧
    c.reg rSK = skOf g (vOf g i) ∧
    c.reg rAcc = accF g (lowF g i) (vOf g i) (j - R1.ps (idEdges g) (vOf g i))

theorem lowHead_spec (g : Graph) (c₀ : Config) (hR : R1Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) (i : ℕ) (hi : i < numV g) :
    HTB S lowHead (fun c => LowInv g c₀ i c ∧ c.reg rI = i ∧ c.reg gN = numV g)
      (fun c => InInv g c₀ i (R1.ps (idEdges g) (vOf g i)) c ∧
        c.reg rA = R1.ps (idEdges g) (vOf g i) ∧
        c.reg rB = R1.ps (idEdges g) (vOf g i) + (nbOf (idEdges g) (vOf g i)).length ∧
        R1.ps (idEdges g) (vOf g i) ≤
          R1.ps (idEdges g) (vOf g i) + (nbOf (idEdges g) (vOf g i)).length) 23 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hG, hM⟩, hi', hn⟩ => by
    have hv : vOf g i < numV g := vOf_lt hi
    have hord : c.mem (c₀.reg gORD + (numV g - i - 1)) = vOf g i := by
      rw [rd_ord hR hM.same (by omega), vOf, show numV g - i - 1 = numV g - 1 - i by omega]
    have := fits hR hS
    addr_ok [lowHead, hG.ord, hG.par, hG.pre, hG.off, hn, hi', hord]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hi', hn⟩ => ?_
  have hv : vOf g i < numV g := vOf_lt hi
  have hord : c.mem (c₀.reg gORD + (numV g - i - 1)) = vOf g i := by
    rw [rd_ord hR hM.same (by omega), vOf, show numV g - i - 1 = numV g - 1 - i by omega]
  have hpar := rd_par hR hM.same hv
  have hpre := rd_pre hR hM.same hv
  have hoff := rd_off hR hM.same (le_of_lt hv)
  have hoff1 : c.mem (c₀.reg gOFF + (vOf g i + 1)) =
      R1.ps (idEdges g) (vOf g i) + (nbOf (idEdges g) (vOf g i)).length := by
    rw [rd_off hR hM.same (by omega), R1.ps_succ]
  have hmem : (run lowHead c).mem = c.mem := run_mem_of_stores (by decide) rfl c
  have hrun : ∀ r, r ∉ wregs lowHead → (run lowHead c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  by_cases hp : (dfsOf g).par (vOf g i) = vOf g i
  all_goals
    refine ⟨⟨(Glob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, by rw [hmem]; exact hM,
      by rw [hrun rI (by decide), hi'], ?_, ?_, ?_⟩, ?_, ?_, by omega⟩
    all_goals
      simp +decide only [lowHead, run_seq', run_sub, run_dec (show rP ≠ rT by decide), run_ld,
        run_ifEq (show rSK ≠ rT by decide) (show rV ≠ rT by decide),
        run_mov (show gN ≠ rT by decide), run_addc (show rV ≠ rT by decide), run_skip,
        setReg_reg, setReg_mem, ↓reduceIte, hG.ord, hG.par, hG.pre, hG.off, hn, hi', hord, hpar, hp, skOf, hpre, hoff, hoff1, Nat.sub_self, accF_zero]

/-- The effect of the inner block on the accumulator. -/
theorem lowInner_acc (c : Config) : (run lowInner c).reg rAcc =
    if c.mem (c.reg gADJ + c.reg rJ) = c.reg rSK then c.reg rAcc
    else min (c.reg rAcc) (if c.mem (c.reg gPAR + c.mem (c.reg gADJ + c.reg rJ)) = c.reg rV
      then c.mem (c.reg gLOW + c.mem (c.reg gADJ + c.reg rJ))
      else c.mem (c.reg gPRE + c.mem (c.reg gADJ + c.reg rJ))) := by
  simp +decide only [lowInner, lowMin, run_seq', run_ld,
    run_ifEq (show rW ≠ rT by decide) (show rSK ≠ rT by decide),
    run_ifEq (show rY ≠ rT by decide) (show rV ≠ rT by decide), run_ifLt,
    run_mov (show rX ≠ rT by decide), run_skip, setReg_reg, setReg_mem, ↓reduceIte]
  split_ifs <;> simp_all +decide <;> omega

theorem lowInner_spec (g : Graph) (c₀ : Config) (hR : R1Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) (i : ℕ) (hi : i < numV g)
    (j : ℕ) (hj1 : R1.ps (idEdges g) (vOf g i) ≤ j)
    (hj2 : j < R1.ps (idEdges g) (vOf g i) + (nbOf (idEdges g) (vOf g i)).length) :
    HTB S lowInner (fun c => InInv g c₀ i j c ∧ c.reg rJ = j ∧
        c.reg rB = R1.ps (idEdges g) (vOf g i) + (nbOf (idEdges g) (vOf g i)).length)
      (fun c => InInv g c₀ i (j + 1) c ∧ c.reg rJ = j ∧
        c.reg rB = R1.ps (idEdges g) (vOf g i) + (nbOf (idEdges g) (vOf g i)).length) 41 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hG, hM, _, hV, _, _⟩, hJ, _⟩ => by
    have hv : vOf g i < numV g := vOf_lt hi
    have hk : j - R1.ps (idEdges g) (vOf g i) < (nbOf (idEdges g) (vOf g i)).length := by omega
    have hw : (nbOf (idEdges g) (vOf g i))[j - R1.ps (idEdges g) (vOf g i)] < numV g :=
      R1.lt_of_mem_nbOf (List.getElem_mem hk)
    have hadj : c.mem (c₀.reg gADJ + j) =
        (nbOf (idEdges g) (vOf g i))[j - R1.ps (idEdges g) (vOf g i)] := by
      have := rd_adj hR hM.same hv hk
      rwa [show R1.ps (idEdges g) (vOf g i) + (j - R1.ps (idEdges g) (vOf g i)) = j by omega] at this
    have hps := R1.ps_mono (idEdges g) (show vOf g i + 1 ≤ numV g by omega)
    rw [R1.ps_succ, R1.idEdges_ps] at hps
    have := fits hR hS
    addr_ok [lowInner, lowMin, hG.adj, hG.par, hG.pre, hG.low, hJ, hV, hadj]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hM, hI, hV, hSK, hAcc⟩, hJ, hB⟩ => ?_
  have hv : vOf g i < numV g := vOf_lt hi
  have hk : j - R1.ps (idEdges g) (vOf g i) < (nbOf (idEdges g) (vOf g i)).length := by omega
  have hw : (nbOf (idEdges g) (vOf g i))[j - R1.ps (idEdges g) (vOf g i)] < numV g :=
    R1.lt_of_mem_nbOf (List.getElem_mem hk)
  have hadj : c.mem (c.reg gADJ + c.reg rJ) =
      (nbOf (idEdges g) (vOf g i))[j - R1.ps (idEdges g) (vOf g i)] := by
    have := rd_adj hR hM.same hv hk
    rw [show R1.ps (idEdges g) (vOf g i) + (j - R1.ps (idEdges g) (vOf g i)) = j by omega] at this
    rw [hG.adj, hJ, this]
  have hpar : c.mem (c.reg gPAR + (nbOf (idEdges g) (vOf g i))[j - R1.ps (idEdges g) (vOf g i)]) =
      (dfsOf g).par (nbOf (idEdges g) (vOf g i))[j - R1.ps (idEdges g) (vOf g i)] := by
    rw [hG.par]; exact rd_par hR hM.same hw
  have hpre : c.mem (c.reg gPRE + (nbOf (idEdges g) (vOf g i))[j - R1.ps (idEdges g) (vOf g i)]) =
      (dfsOf g).pre (nbOf (idEdges g) (vOf g i))[j - R1.ps (idEdges g) (vOf g i)] := by
    rw [hG.pre]; exact rd_pre hR hM.same hw
  have hlow : c.mem (c.reg gLOW + (nbOf (idEdges g) (vOf g i))[j - R1.ps (idEdges g) (vOf g i)]) =
      lowF g i (nbOf (idEdges g) (vOf g i))[j - R1.ps (idEdges g) (vOf g i)] := by
    rw [hG.low]; exact hM.low.get hw
  have hAg : Agree [rW, rT, rY, rX, rAcc] c (run lowInner c) :=
    agree_run (by decide) rfl rfl (by decide) c
  refine ⟨⟨((Glob.regIndep g c₀).indep.mono (by decide)) c _ hAg hG, by rw [hAg.mem]; exact hM,
    by rw [hAg.reg rI (by decide), hI], by rw [hAg.reg rV (by decide), hV],
    by rw [hAg.reg rSK (by decide), hSK], ?_⟩, by rw [hAg.reg rJ (by decide), hJ],
    by rw [hAg.reg rB (by decide), hB]⟩
  rw [lowInner_acc, hadj, hpar, hpre, hlow, hSK, hAcc, hV,
    show j + 1 - R1.ps (idEdges g) (vOf g i) = j - R1.ps (idEdges g) (vOf g i) + 1 by omega,
    accF_succ g _ hk]

/-- Storing the low point of `v`. -/
theorem lowTail_spec (g : Graph) (c₀ : Config) (hR : R1Post g c₀) (hS : endL g (c₀.reg rFREE) ≤ S)
    (i : ℕ) (hi : i < numV g) :
    HTB S (st gLOW rV rAcc)
      (fun c => InInv g c₀ i (R1.ps (idEdges g) (vOf g i) + (nbOf (idEdges g) (vOf g i)).length) c ∧
        c.reg rJ = R1.ps (idEdges g) (vOf g i) + (nbOf (idEdges g) (vOf g i)).length ∧
        c.reg rB = R1.ps (idEdges g) (vOf g i) + (nbOf (idEdges g) (vOf g i)).length)
      (fun c => LowInv g c₀ (i + 1) c ∧ c.reg rI = i ∧ c.reg gN = numV g) 2 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hG, _, _, hV, _, _⟩, _, _⟩ => by
    have hv : vOf g i < numV g := vOf_lt hi
    have := fits hR hS
    addr_ok [hG.low, hV]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hM, hI, hV, _, hAcc⟩, _, _⟩ => ?_
  rw [run_st (by decide)]
  have hv := vOf_lt hi
  refine ⟨⟨(Glob.regIndep g c₀).setReg (by decide) _ ((Glob.regIndep g c₀).setMem _ _ hG), ?_⟩,
    by simp +decide [hI], by simp +decide [hG.n]⟩
  simp only [setReg_mem, setMem_mem_upd, hG.low, hV, hAcc]
  rw [lowF_succ g hi, ← accF_full, Nat.add_sub_cancel_left]
  exact hM.upd hv _

/-- One vertex of the low-point pass, in `45 |nb v| + 29` steps. -/
theorem lowBody_spec (g : Graph) (c₀ : Config) (hR : R1Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) (i : ℕ) (hi : i < numV g) :
    HTB S lowBody (fun c => LowInv g c₀ i c ∧ c.reg rI = i ∧ c.reg gN = numV g)
      (fun c => LowInv g c₀ (i + 1) c ∧ c.reg rI = i ∧ c.reg gN = numV g)
      (45 * (nbOf (idEdges g) (vOf g i)).length + 29) := by
  have h2 := HTB.forRange (i := rJ) (a := rA) (n := rB) (A := R1.ps (idEdges g) (vOf g i))
    (N := R1.ps (idEdges g) (vOf g i) + (nbOf (idEdges g) (vOf g i)).length) (body := lowInner)
    (InInv g c₀ i) (fun _ => 41) (by decide) (by decide) (by decide) (by decide)
    (fun j => by indep [InInv, glob_iff]) (fun j hj1 hj2 => lowInner_spec g c₀ hR hS i hi j hj1 hj2)
  refine ((lowHead_spec g c₀ hR hS i hi).seq (h2.seq (lowTail_spec g c₀ hR hS i hi))).weaken ?_
  simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  omega

/-- **Step 2**: the low points, in `90 |E| + 33 N + 3` steps. -/
theorem stepLow_spec (g : Graph) (c₀ : Config) (hR : R1Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S stepLow (fun c => LowInv g c₀ 0 c ∧ c.reg gN = numV g)
      (fun c => LowInv g c₀ (numV g) c ∧ c.reg rI = numV g ∧ c.reg gN = numV g)
      (90 * (idEdges g).length + 33 * numV g + 3) := by
  have h := HTB.forUp (i := rI) (n := gN) (N := numV g) (body := lowBody) (LowInv g c₀)
    (fun i => 45 * (nbOf (idEdges g) (vOf g i)).length + 29) (by decide) (by decide) (by decide)
    (fun j => by indep [LowInv, glob_iff]) (fun i hi => lowBody_spec g c₀ hR hS i hi)
  refine h.weaken (le_of_eq ?_)
  have hs := sum_deg g
  have : ∑ i ∈ Finset.range (numV g), (45 * (nbOf (idEdges g) (vOf g i)).length + 29 + 4) =
      45 * ∑ i ∈ Finset.range (numV g), (nbOf (idEdges g) (vOf g i)).length + 33 * numV g := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  omega

end STACS2027.RAM.R2
