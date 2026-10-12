module

public import Outerplanar.RAM.R3Spec
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Phase R3 (blocks): the program and the stable counting sort

Phase R3 starts in an `R2Post g` configuration `c₀` (`N = numV g` vertices, the `ne` edges
`E = idEdges g` at `gEU`, `gEV`, the tables `PRE` of the search and `HEAD` of the heads) with
first free address `F`. The key of an edge `e = (a, b)` is `HEAD[PRE[a] < PRE[b] ? b : a]`
(`keyOf`, `key g e`). It

1. `r3Alloc`: allocates (all zero) the bucket counts `CNT` (`N` cells, base `F`), the bucket
   starts `BST` (`gBST`, `N + 1`), the fill counters `FIL` (`N`), and the bucketed edge ends
   `BU`, `BV` (`gBU`, `gBV`, `ne` cells each); `rFREE := endL g F`;
2. `stepCnt`: for each edge: `CNT[key e]++` (after `j` edges `CNT[h] = |bk g j h|`);
3. `stepPre`: prefix sums `BST[h + 1] := BST[h] + CNT[h]`, so `BST` holds `bs g`;
4. `stepFill`: for each edge `e = (a, b)` of key `k`: `p := BST[k] + FIL[k]`, `BU[p] := a`,
   `BV[p] := b`, `FIL[k]++` (after `j` edges the segment of bucket `h` holds `bk g j h`).

This file contains the program, the layout, the register invariant `Glob`, and the triples of
the steps (`r3Alloc_spec`, `stepCnt_spec`, `stepPre_spec`, `stepFill_spec`), within a bound
`S ≥ endL g F` on the accessed addresses (`HTB S`; `fits`: one inequality per region, the arrays
read from earlier phases lying below `F`; `endL_le`: `endL g F ≤ F + 8 (m + 1)`).
-/

@[expose] public section

namespace STACS2027.RAM.R3

open STACS2027.Algo

variable {S : ℕ}

/-! ### Scratch registers of the phase -/

/-- Loop counter. -/
abbrev rI : ℕ := 100
/-- First end of the current edge. -/
abbrev rU : ℕ := 101
/-- Second end of the current edge. -/
abbrev rV : ℕ := 102
/-- A value read from memory. -/
abbrev rX : ℕ := 103
/-- A second value read from memory. -/
abbrev rY : ℕ := 104
/-- The lower end of the current edge. -/
abbrev rL : ℕ := 105
/-- The key of the current edge. -/
abbrev rK : ℕ := 106
/-- Running prefix sum. -/
abbrev rAcc : ℕ := 107
/-- An index. -/
abbrev rP : ℕ := 108
/-- Base of the bucket counts `CNT`. -/
abbrev rCNT : ℕ := 109
/-- Base of the fill counters `FIL`. -/
abbrev rFIL : ℕ := 110

/-! ### The program -/

/-- Step 1: allocation of all arrays. -/
def r3Alloc : Stmt :=
  .seq (alloc rCNT gN) (.seq (addc rX gN 1) (.seq (alloc gBST rX) (.seq (alloc rFIL gN)
    (.seq (alloc gBU gNE) (alloc gBV gNE)))))

/-- The ends `rU`, `rV` of edge `rI` and its key `rK = HEAD[lower end]`. -/
def keyOf : Stmt :=
  .seq (ld rU gEU rI) (.seq (ld rV gEV rI) (.seq (ld rX gPRE rU) (.seq (ld rY gPRE rV)
    (.seq (ifLt rX rY (mov rL rV) (mov rL rU)) (ld rK gHEAD rL)))))

/-- One edge of the counting pass: `CNT[key]++`. -/
def cntBody : Stmt := .seq keyOf (.seq (ld rX rCNT rK) (.seq (inc rX) (st rCNT rK rX)))
/-- Step 2: the bucket sizes. -/
def stepCnt : Stmt := forUp rI gNE cntBody

/-- One bucket of the prefix sums: `rAcc += CNT[i]; BST[i + 1] := rAcc`. -/
def preBody : Stmt :=
  .seq (ld rX rCNT rI) (.seq (.add rAcc rAcc rX) (.seq (addc rP rI 1) (st gBST rP rAcc)))
/-- Step 3: the bucket starts. -/
def stepPre : Stmt := .seq (.const rAcc 0) (forUp rI gN preBody)

/-- One edge of the fill pass: `p := BST[key] + FIL[key]`, `BU[p] := a`, `BV[p] := b`,
`FIL[key]++`. -/
def fillBody : Stmt :=
  .seq keyOf (.seq (ld rX rFIL rK) (.seq (ld rY gBST rK) (.seq (.add rY rY rX)
    (.seq (st gBU rY rU) (.seq (st gBV rY rV) (.seq (inc rX) (st rFIL rK rX)))))))
/-- Step 4: the bucketed edges. -/
def stepFill : Stmt := forUp rI gNE fillBody

/-- **Phase R3.** -/
def r3 : Stmt := .seq r3Alloc (.seq stepCnt (.seq stepPre stepFill))

/-! ### The layout -/

section layout

variable (g : Graph) (F : ℕ)

/-- The bucket starts `BST` (`N + 1` cells); the counts `CNT` are at `F` (`N` cells). -/
def bBST : ℕ := F + numV g
/-- The fill counters `FIL` (`N` cells). -/
def bFIL : ℕ := bBST g F + (numV g + 1)
/-- The first ends of the bucketed edges `BU` (`ne` cells). -/
def bBU : ℕ := bFIL g F + numV g
/-- The second ends of the bucketed edges `BV` (`ne` cells). -/
def bBV : ℕ := bBU g F + (idEdges g).length
/-- The end of the memory used by R3. -/
def endL : ℕ := bBV g F + (idEdges g).length

/-- The layout as equations (for `omega`). -/
theorem layout_eqs : bBST g F = F + numV g ∧ bFIL g F = bBST g F + (numV g + 1) ∧
    bBU g F = bFIL g F + numV g ∧ bBV g F = bBU g F + (idEdges g).length ∧
    endL g F = bBV g F + (idEdges g).length := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The layout of R3 is linear. -/
theorem endL_le : endL g F ≤ F + 8 * (g.length + 1) := by
  have := layout_eqs g F
  have := R0.numV_le g
  have := R0.length_idEdges_le g
  omega

end layout

/-- The regions read or written by R3 fit below `S` (one inequality per region). -/
theorem fits {g : Graph} {c₀ : Config} (hR : R2Post g c₀) (hS : endL g (c₀.reg rFREE) ≤ S) :
    c₀.reg gEU + (idEdges g).length ≤ S ∧ c₀.reg gEV + (idEdges g).length ≤ S ∧
      c₀.reg gPRE + numV g ≤ S ∧ c₀.reg gHEAD + numV g ≤ S ∧ c₀.reg rFREE + numV g ≤ S ∧
      bBST g (c₀.reg rFREE) + (numV g + 1) ≤ S ∧ bFIL g (c₀.reg rFREE) + numV g ≤ S ∧
      bBU g (c₀.reg rFREE) + (idEdges g).length ≤ S ∧ bBV g (c₀.reg rFREE) + (idEdges g).length ≤ S := by
  have hL := layout_eqs g (c₀.reg rFREE)
  have h1 := hR.r1.base.below
  have h2 := hR.r1.below
  have h3 := hR.below
  omega

/-! ### Global registers fixed after the allocation -/

/-- The registers that keep their value from the end of step 1 on (`F = c₀.reg rFREE`). -/
@[mk_iff] structure Glob (g : Graph) (c₀ c : Config) : Prop where
  n : c.reg gN = numV g
  ne : c.reg gNE = (idEdges g).length
  eu : c.reg gEU = c₀.reg gEU
  ev : c.reg gEV = c₀.reg gEV
  pre : c.reg gPRE = c₀.reg gPRE
  head : c.reg gHEAD = c₀.reg gHEAD
  free : c.reg rFREE = endL g (c₀.reg rFREE)
  cnt : c.reg rCNT = c₀.reg rFREE
  bst : c.reg gBST = bBST g (c₀.reg rFREE)
  fil : c.reg rFIL = bFIL g (c₀.reg rFREE)
  bu : c.reg gBU = bBU g (c₀.reg rFREE)
  bv : c.reg gBV = bBV g (c₀.reg rFREE)

/-- The registers written by steps 2–4. -/
def W3 : List ℕ := [rT, rI, rU, rV, rX, rY, rL, rK, rAcc, rP]

theorem Glob.regIndep (g : Graph) (c₀ : Config) : RegIndep W3 (Glob g c₀) := by indep [glob_iff]

/-! ### The keys -/

theorem rd_head {g : Graph} {c₀ : Config} {m : ℕ → ℕ} (hR : R2Post g c₀)
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {v : ℕ} (hv : v < numV g) :
    m (c₀.reg gHEAD + v) = headsOf g v :=
  (hR.head.of_below hS hR.below.2).get hv

/-- Reading the edge `rI` and its key. -/
theorem keyOf_run {g : Graph} {c₀ c : Config} (hR : R2Post g c₀) (hG : Glob g c₀ c)
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem) {j : ℕ} (hi : c.reg rI = j)
    (hj : j < (idEdges g).length) :
    (run keyOf c).reg rU = (idEdges g)[j].1 ∧ (run keyOf c).reg rV = (idEdges g)[j].2 ∧
      (run keyOf c).reg rK = key g (idEdges g)[j] ∧
      Agree [rU, rV, rX, rY, rL, rK, rT] c (run keyOf c) := by
  obtain ⟨ha, hb⟩ := R1.edge_ends hR.r1.base hS hj
  obtain ⟨hla, hlb⟩ := R1.idEdges_lt_get hj
  have hpa := R2.rd_pre hR.r1 hS hla
  have hpb := R2.rd_pre hR.r1 hS hlb
  have hha := rd_head hR hS hla
  have hhb := rd_head hR hS hlb
  refine ⟨?_, ?_, ?_, agree_run (by decide) rfl rfl (by decide) c⟩
  all_goals
    simp +decide only [keyOf, run_seq', run_ld, run_ifLt, run_mov (show rV ≠ rT by decide),
      run_mov (show rU ≠ rT by decide), setReg_reg, setReg_mem, ↓reduceIte, hG.eu, hG.ev,
      hG.pre, hi, ha, hb, hpa, hpb]
  all_goals
    by_cases h : (dfsOf g).pre (idEdges g)[j].1 < (dfsOf g).pre (idEdges g)[j].2 <;>
      simp +decide only [h, ↓reduceIte, setReg_reg, setReg_mem, hG.head, key, lowerOf, hha, hhb]

/-- The addresses of `keyOf` (hypotheses of `keyOf_run`): the edge ends, `PRE`, `HEAD`. -/
theorem keyOf_addrOK {g : Graph} {c₀ c : Config} (hR : R2Post g c₀) (hG : Glob g c₀ c)
    (hSm : SameOn (· < c₀.reg rFREE) c₀.mem c.mem) {j : ℕ} (hi : c.reg rI = j)
    (hj : j < (idEdges g).length) (hS : endL g (c₀.reg rFREE) ≤ S) : AddrOK S keyOf c := by
  obtain ⟨ha, hb⟩ := R1.edge_ends hR.r1.base hSm hj
  obtain ⟨hla, hlb⟩ := R1.idEdges_lt_get hj
  have := fits hR hS
  addr_ok [keyOf, hG.eu, hG.ev, hG.pre, hG.head, hi, ha, hb]

/-! ### Step 1: allocation -/

/-- The memory during the counting pass, with the counts `f`. -/
structure CntMem (g : Graph) (c₀ : Config) (f : ℕ → ℕ) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  cnt : Tab m (c₀.reg rFREE) (numV g) f
  zero : ZeroFrom m (bBST g (c₀.reg rFREE))

/-- The invariant of the counting pass after `j` edges. -/
def CntInv (g : Graph) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  Glob g c₀ c ∧ CntMem g c₀ (fun h => (bk g j h).length) c.mem

theorem r3Alloc_spec (g : Graph) (c₀ : Config) (hR : R2Post g c₀) :
    HTB S r3Alloc (fun c => c = c₀) (fun c => CntInv g c₀ 0 c ∧ c.reg gNE = (idEdges g).length)
      17 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  have hB := hR.r1.base
  have hL := layout_eqs g (c.reg rFREE)
  simp only [r3Alloc, run_seq', run_alloc (show gN ≠ rT by decide) (show rCNT ≠ gN by decide),
    run_addc (show gN ≠ rT by decide), run_alloc (show rX ≠ rT by decide) (show gBST ≠ rX by decide),
    run_alloc (show gN ≠ rT by decide) (show rFIL ≠ gN by decide),
    run_alloc (show gNE ≠ rT by decide) (show gBU ≠ gNE by decide),
    run_alloc (show gNE ≠ rT by decide) (show gBV ≠ gNE by decide)]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  all_goals try (simp +decide [hB.n, hB.ne, hL] <;> omega)
  simp only [setReg_mem, bk_zero, List.length_nil]
  exact ⟨SameOn.refl _ _, hB.free.tab le_rfl _, hB.free.mono (by omega)⟩

/-! ### Step 2: the bucket sizes -/

theorem CntMem.bmp {g : Graph} {c₀ : Config} {f : ℕ → ℕ} {m : ℕ → ℕ} (h : CntMem g c₀ f m)
    {k : ℕ} (hk : k < numV g) :
    CntMem g c₀ (Function.update f k (f k + 1)) (upd m (c₀.reg rFREE + k) (f k + 1)) := by
  have hL := layout_eqs g (c₀.reg rFREE)
  exact ⟨h.same.upd_of_ge (by omega) _, h.cnt.upd rfl, h.zero.upd (by omega)⟩

theorem cnt_succ (g : Graph) {j : ℕ} (hj : j < (idEdges g).length) :
    (fun h => (bk g (j + 1) h).length) = Function.update (fun h => (bk g j h).length)
      (key g (idEdges g)[j]) ((bk g j (key g (idEdges g)[j])).length + 1) := by
  funext h
  rw [length_bk_succ g hj]
  by_cases hk : h = key g (idEdges g)[j]
  · subst hk; simp
  · rw [Function.update_of_ne hk]; simp [Ne.symm hk]

theorem cntBody_spec (g : Graph) (c₀ : Config) (hR : R2Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) (j : ℕ) (hj : j < (idEdges g).length) :
    HTB S cntBody (fun c => CntInv g c₀ j c ∧ c.reg rI = j ∧ c.reg gNE = (idEdges g).length)
      (fun c => CntInv g c₀ (j + 1) c ∧ c.reg rI = j ∧ c.reg gNE = (idEdges g).length) 22 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hi, hn⟩ => ?_
  obtain ⟨-, -, hK, hAg⟩ := keyOf_run hR hG hM.same hi hj
  have hk := key_get_lt hj
  have hG₁ : Glob g c₀ (run keyOf c) := ((Glob.regIndep g c₀).indep.mono (by decide)) _ _ hAg hG
  have hc : (run keyOf c).mem ((run keyOf c).reg rCNT + (run keyOf c).reg rK) =
      (bk g j (key g (idEdges g)[j])).length := by
    rw [hG₁.cnt, hK, hAg.mem]; exact hM.cnt.get hk
  have hfit := fits hR hS
  refine ⟨(keyOf_addrOK hR hG hM.same hi hj hS).seq (by addr_ok [hG₁.cnt, hK]),
    ⟨(Glob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_⟩, ?_, ?_⟩
  · simp +decide only [cntBody, run_seq', run_ld, run_inc (show rX ≠ rT by decide),
      run_st (show rX ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd, ↓reduceIte, hc]
    rw [hG₁.cnt, hK, hAg.mem, cnt_succ g hj]
    exact hM.bmp hk
  · rw [run_reg_of_not_mem (s := cntBody) (r := rI) (by decide) (by decide) c, hi]
  · rw [run_reg_of_not_mem (s := cntBody) (r := gNE) (by decide) (by decide) c, hn]

/-- **Step 2**: the bucket sizes. -/
theorem stepCnt_spec (g : Graph) (c₀ : Config) (hR : R2Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S stepCnt (fun c => CntInv g c₀ 0 c ∧ c.reg gNE = (idEdges g).length)
      (fun c => CntInv g c₀ (idEdges g).length c ∧ c.reg rI = (idEdges g).length ∧
        c.reg gNE = (idEdges g).length) ((idEdges g).length * 26 + 3) :=
  HTB.forUpC (i := rI) (n := gNE) (N := (idEdges g).length) (body := cntBody) (CntInv g c₀) 22
    (by decide) (by decide) (by decide) (fun j => by indep [CntInv, glob_iff])
    (fun j hj => cntBody_spec g c₀ hR hS j hj)

/-! ### Step 3: the bucket starts -/

/-- The memory during the prefix sums, after `v` buckets. -/
structure PreMem (g : Graph) (c₀ : Config) (v : ℕ) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  cnt : Tab m (c₀.reg rFREE) (numV g) fun h => (bk g (idEdges g).length h).length
  bst : Tab m (bBST g (c₀.reg rFREE)) (numV g + 1) fun h => if h ≤ v then bs g h else 0
  zero : ZeroFrom m (bFIL g (c₀.reg rFREE))

/-- The invariant of the prefix sums after `v` buckets. -/
def PreInv (g : Graph) (c₀ : Config) (v : ℕ) (c : Config) : Prop :=
  Glob g c₀ c ∧ c.reg rAcc = bs g v ∧ PreMem g c₀ v c.mem

theorem PreMem.snoc {g : Graph} {c₀ : Config} {v : ℕ} {m : ℕ → ℕ} (h : PreMem g c₀ v m)
    (hv : v < numV g) :
    PreMem g c₀ (v + 1)
      (upd m (bBST g (c₀.reg rFREE) + (v + 1)) (bs g v + (bk g (idEdges g).length v).length)) := by
  have hL := layout_eqs g (c₀.reg rFREE)
  refine ⟨h.same.upd_of_ge (by omega) _, h.cnt.upd_of_disjoint (by omega), ?_, h.zero.upd (by omega)⟩
  refine (h.bst.upd rfl).congr_fun fun i _ => ?_
  rw [← bs_succ]
  by_cases hi : i = v + 1
  · subst hi; simp
  · rw [Function.update_of_ne hi]
    by_cases hiv : i ≤ v
    · simp [hiv, show i ≤ v + 1 by omega]
    · simp [hiv, show ¬ i ≤ v + 1 by omega]

theorem preBody_spec (g : Graph) (c₀ : Config) (hR : R2Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) (v : ℕ) (hv : v < numV g) :
    HTB S preBody (fun c => PreInv g c₀ v c ∧ c.reg rI = v ∧ c.reg gN = numV g)
      (fun c => PreInv g c₀ (v + 1) c ∧ c.reg rI = v ∧ c.reg gN = numV g) 7 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hG, _, _⟩, hi, _⟩ => by
    have := fits hR hS
    addr_ok [preBody, hG.cnt, hG.bst, hi]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hacc, hM⟩, hi, hn⟩ => ?_
  have hd : c.mem (c₀.reg rFREE + v) = (bk g (idEdges g).length v).length := hM.cnt.get hv
  refine ⟨⟨(Glob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [preBody, run_seq', run_ld, run_add, run_addc (show rI ≠ rT by decide),
      run_st (show rAcc ≠ rT by decide)]
  · simp +decide [hd, hacc, bs_succ, hG.cnt, hi]
  · simpa +decide [hd, hacc, hG.bst, hG.cnt, hi] using hM.snoc hv
  · simp +decide [hi]
  · simp +decide [hn]

/-- **Step 3**: the bucket starts `bs g`. -/
theorem stepPre_spec (g : Graph) (c₀ : Config) (hR : R2Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S stepPre (fun c => CntInv g c₀ (idEdges g).length c ∧ c.reg rI = (idEdges g).length ∧
        c.reg gNE = (idEdges g).length)
      (fun c => PreInv g c₀ (numV g) c ∧ c.reg rI = numV g ∧ c.reg gN = numV g)
      (1 + (numV g * 11 + 3)) := by
  have h0 : HTB S (.const rAcc 0) (fun c => CntInv g c₀ (idEdges g).length c ∧
      c.reg rI = (idEdges g).length ∧ c.reg gNE = (idEdges g).length)
      (fun c => PreInv g c₀ 0 c ∧ c.reg gN = numV g) 1 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, _, _⟩ => ?_
    have hL := layout_eqs g (c₀.reg rFREE)
    simp only [run_const]
    refine ⟨⟨(Glob.regIndep g c₀).setReg (by decide) _ hG, by simp +decide [bs], ?_⟩, by
      simp +decide [hG.n]⟩
    simp only [setReg_mem]
    refine ⟨hM.same, hM.cnt, ?_, hM.zero.mono (by omega)⟩
    intro i hi
    rw [hM.zero.get (by omega)]
    by_cases h : i ≤ 0
    · simp [show i = 0 by omega, bs]
    · simp [h]
  have hl := HTB.forUpC (i := rI) (n := gN) (N := numV g) (body := preBody) (PreInv g c₀) 7
    (by decide) (by decide) (by decide) (fun j => by indep [PreInv, glob_iff])
    (fun j hj => preBody_spec g c₀ hR hS j hj)
  exact h0.seq hl

/-! ### Step 4: the bucketed edges -/

/-- The memory during the fill pass, with the buckets `L` filled in so far. -/
structure FillMem (g : Graph) (c₀ : Config) (L : ℕ → List Edge) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  bst : Tab m (bBST g (c₀.reg rFREE)) (numV g + 1) (bs g)
  fil : Tab m (bFIL g (c₀.reg rFREE)) (numV g) fun h => (L h).length
  bu : ∀ h, h < numV g → Arr m (bBU g (c₀.reg rFREE) + bs g h) ((L h).map Prod.fst)
  bv : ∀ h, h < numV g → Arr m (bBV g (c₀.reg rFREE) + bs g h) ((L h).map Prod.snd)
  len : ∀ h, h < numV g → (L h).length ≤ (bk g (idEdges g).length h).length
  zero : ZeroFrom m (endL g (c₀.reg rFREE))

/-- The invariant of the fill pass after `j` edges. -/
def FillInv (g : Graph) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  Glob g c₀ c ∧ FillMem g c₀ (bk g j) c.mem

/-- Appending the edge `e` to the bucket `k`: three stores. -/
theorem FillMem.app {g : Graph} {c₀ : Config} {L : ℕ → List Edge} {m : ℕ → ℕ}
    (h : FillMem g c₀ L m) {k : ℕ} (hk : k < numV g)
    (hlt : (L k).length < (bk g (idEdges g).length k).length) (e : Edge) :
    FillMem g c₀ (Function.update L k (L k ++ [e]))
      (upd (upd (upd m (bBU g (c₀.reg rFREE) + (bs g k + (L k).length)) e.1)
        (bBV g (c₀.reg rFREE) + (bs g k + (L k).length)) e.2)
        (bFIL g (c₀.reg rFREE) + k) ((L k).length + 1)) := by
  have hL := layout_eqs g (c₀.reg rFREE)
  have htot := bs_add_le_total g hk
  refine ⟨((h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge (by omega) _,
    ((h.bst.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    ?_, ?_, ?_, ?_, ((h.zero.upd (by omega)).upd (by omega)).upd (by omega)⟩
  · refine (((h.fil.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd rfl).congr_fun
      fun v _ => ?_
    by_cases hv : v = k
    · subst hv; simp
    · rw [Function.update_of_ne hv, Function.update_of_ne hv]
  · intro v hv
    by_cases hvk : v = k
    · subst hvk
      simp only [Function.update_self, List.map_append, List.map_cons, List.map_nil]
      exact (((h.bu v hv).upd_snoc (by simp; omega)).upd_of_disjoint (by simp; omega)).upd_of_disjoint
        (by simp; omega)
    · simp only [Function.update_of_ne hvk]
      have hlv := h.len v hv
      have htv := bs_add_le_total g hv
      refine (((h.bu v hv).upd_of_disjoint ?_).upd_of_disjoint (by simp; omega)).upd_of_disjoint
        (by simp; omega)
      rcases Nat.lt_or_gt_of_ne hvk with hvk' | hvk'
      · have := bs_add_le g hvk'
        right; simp; omega
      · have := bs_add_le g hvk'
        left; omega
  · intro v hv
    by_cases hvk : v = k
    · subst hvk
      simp only [Function.update_self, List.map_append, List.map_cons, List.map_nil]
      exact (((h.bv v hv).upd_of_disjoint (by simp; omega)).upd_snoc (by simp; omega)).upd_of_disjoint
        (by simp; omega)
    · simp only [Function.update_of_ne hvk]
      have hlv := h.len v hv
      have htv := bs_add_le_total g hv
      refine (((h.bv v hv).upd_of_disjoint (by simp; omega)).upd_of_disjoint ?_).upd_of_disjoint
        (by simp; omega)
      rcases Nat.lt_or_gt_of_ne hvk with hvk' | hvk'
      · have := bs_add_le g hvk'
        right; simp; omega
      · have := bs_add_le g hvk'
        left; omega
  · intro v hv
    by_cases hvk : v = k
    · subst hvk; simp only [Function.update_self, List.length_append, List.length_singleton]; omega
    · simp only [Function.update_of_ne hvk]; exact h.len v hv

theorem fillBody_spec (g : Graph) (c₀ : Config) (hR : R2Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) (j : ℕ) (hj : j < (idEdges g).length) :
    HTB S fillBody (fun c => FillInv g c₀ j c ∧ c.reg rI = j ∧ c.reg gNE = (idEdges g).length)
      (fun c => FillInv g c₀ (j + 1) c ∧ c.reg rI = j ∧ c.reg gNE = (idEdges g).length) 29 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hi, hn⟩ => ?_
  obtain ⟨hU, hV, hK, hAg⟩ := keyOf_run hR hG hM.same hi hj
  have hk := key_get_lt hj
  have hG₁ : Glob g c₀ (run keyOf c) := ((Glob.regIndep g c₀).indep.mono (by decide)) _ _ hAg hG
  have hlt : (bk g j (key g (idEdges g)[j])).length <
      (bk g (idEdges g).length (key g (idEdges g)[j])).length := by
    have h1 := length_bk_le g (j + 1) (key g (idEdges g)[j])
    rw [length_bk_succ g hj] at h1
    simpa using h1
  have hf : (run keyOf c).mem ((run keyOf c).reg rFIL + (run keyOf c).reg rK) =
      (bk g j (key g (idEdges g)[j])).length := by
    rw [hG₁.fil, hK, hAg.mem]; exact hM.fil.get hk
  have hb : (run keyOf c).mem ((run keyOf c).reg gBST + (run keyOf c).reg rK) =
      bs g (key g (idEdges g)[j]) := by
    rw [hG₁.bst, hK, hAg.mem]; exact hM.bst.get (by omega)
  have hfit := fits hR hS
  have htot := bs_add_le_total g hk
  have hf' := hf
  have hb' := hb
  rw [hG₁.fil, hK] at hf'
  rw [hG₁.bst, hK] at hb'
  refine ⟨(keyOf_addrOK hR hG hM.same hi hj hS).seq
    (by addr_ok [hG₁.fil, hG₁.bst, hG₁.bu, hG₁.bv, hK, hf', hb']),
    ⟨(Glob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_⟩, ?_, ?_⟩
  · simp +decide only [fillBody, run_seq', run_ld, run_add, run_inc (show rX ≠ rT by decide),
      run_st (show rU ≠ rT by decide), run_st (show rV ≠ rT by decide),
      run_st (show rX ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd, setMem_reg,
      ↓reduceIte, hf, hb]
    rw [hG₁.fil, hG₁.bu, hG₁.bv, hK, hU, hV, hAg.mem, bk_succ_eq g hj]
    exact hM.app hk hlt (idEdges g)[j]
  · rw [run_reg_of_not_mem (s := fillBody) (r := rI) (by decide) (by decide) c, hi]
  · rw [run_reg_of_not_mem (s := fillBody) (r := gNE) (by decide) (by decide) c, hn]

/-- **Step 4**: the bucketed edges. -/
theorem stepFill_spec (g : Graph) (c₀ : Config) (hR : R2Post g c₀)
    (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S stepFill (fun c => FillInv g c₀ 0 c ∧ c.reg gNE = (idEdges g).length)
      (fun c => FillInv g c₀ (idEdges g).length c ∧ c.reg rI = (idEdges g).length ∧
        c.reg gNE = (idEdges g).length) ((idEdges g).length * 33 + 3) :=
  HTB.forUpC (i := rI) (n := gNE) (N := (idEdges g).length) (body := fillBody) (FillInv g c₀) 29
    (by decide) (by decide) (by decide) (fun j => by indep [FillInv, glob_iff])
    (fun j hj => fillBody_spec g c₀ hR hS j hj)

end STACS2027.RAM.R3
