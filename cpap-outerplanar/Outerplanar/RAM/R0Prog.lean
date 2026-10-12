module

public import Outerplanar.RAM.R0Spec
public import Outerplanar.RAM.PairIds
import Mathlib.Tactic

/-!
# Phase R0 (parsing): the program and its memory layout

The machine starts on `graphInput g` (`m = g.length` in cell `0`, the ends of pair `j` in
cells `2j + 1`, `2j + 2`). Phase R0 computes, in `O(m)` steps and `O(labelBound g + m)` cells:

1. `stepMax`: `rONE := 1`, `gM := m`, and the largest entry `gMX := maxLab g`;
2. `stepLayout`: the dictionary base `gD := D = 2m + 1` (cells `D + x`, `x ≤ M`, zero
   initially since they lie beyond the input: `M + 1 = labelBound g` cells),
   `rFREE := D + M + 1`, and five arrays: the labels (`gLB`, `2m` cells), the edge ends
   (`gEU`, `gEV`, `m` cells each), the id pairs (`PU`, `PV` at `PairIds.rPU`, `PairIds.rPV`,
   `m` cells each);
3. `stepLabels`: for each pair `(a, b)` with `a < b`, for `x = a` then `x = b`: if
   `mem[D + x] = 0` then append `x` to the labels and set `mem[D + x] := ` its id `+ 1`;
4. `stepIds` (`R0Edges.lean`): for each pair `(a, b)` with `a < b`: `(u, v)` = the ids of
   `a, b` (dictionary `- 1`), ordered, appended to `PU`, `PV` (`idPairs g`, `L` pairs,
   `PairIds.rPL = L`);
5. `PairIds.pairLeads` (`PairIds.lean`): the leaders
   `LEAD[q] = (idPairs g).idxOf (idPairs g)[q]` by a stable counting sort of the pairs and a
   timestamped scan (`O(N + L)` time and space, no `N × N` table);
6. `stepKeep` (`R0Edges.lean`): for `q < L` with `LEAD[q] = q` (a first occurrence), append
   `(PU[q], PV[q])` to the edge arrays: they then hold `(idPairs g).eraseDups = idEdges g`.

The layout (`baseD g`, …, `endR0 g`) is a function of `g`; `endR0_le`:
`endR0 g ≤ 20 * (labelBound g + g.length + 1)`.

Every triple is stated within a space bound `S` with the hypothesis `hS : endR0 g ≤ S`
(`HTB S`).
-/

@[expose] public section

namespace STACS2027.RAM.R0

open STACS2027.Algo

variable {S : ℕ}

/-! ### Scratch registers of the phase -/

/-- Loop counter. -/
abbrev rI : ℕ := 100
/-- `2m`. -/
abbrev r2M : ℕ := 101
/-- Input pointer. -/
abbrev rP : ℕ := 102
/-- First end of the current pair. -/
abbrev rA : ℕ := 103
/-- Second end of the current pair. -/
abbrev rB : ℕ := 104
/-- The current entry (largest-label loop); the leader (keep pass). -/
abbrev rX : ℕ := 105
/-- A dictionary address. -/
abbrev rQ : ℕ := 106
/-- A dictionary value. -/
abbrev rY : ℕ := 107
/-- First id. -/
abbrev rU : ℕ := 108
/-- Second id. -/
abbrev rV : ℕ := 109

/-! ### The program -/

/-- `rONE := 1; gM := mem[0]; r2M := 2m; gMX := 0`. -/
def maxInit : Stmt := .seq (.const rONE 1) (.seq (.load gM rZERO) (.seq (.add r2M gM gM) (.const gMX 0)))
/-- One step of the largest-entry scan: `rX := mem[i + 1]`; `gMX := max gMX rX`. -/
def maxBody : Stmt := .seq (addc rP rI 1) (.seq (.load rX rP) (ifLt gMX rX (mov gMX rX) .skip))
/-- Step 1. -/
def stepMax : Stmt := .seq maxInit (forUp rI r2M maxBody)

/-- Step 2: the layout. -/
def stepLayout : Stmt :=
  .seq (addc gD r2M 1) (.seq (.add rFREE gD gMX) (.seq (inc rFREE) (.seq (alloc gLB r2M)
    (.seq (alloc gEU gM) (.seq (alloc gEV gM) (.seq (alloc PairIds.rPU gM) (.seq (alloc PairIds.rPV gM)
    (.seq (.const gN 0) (.const rP 1)))))))))

/-- Read the pair at `rP` into `rA`, `rB` and advance `rP` by two. -/
def readPair : Stmt := .seq (.load rA rP) (.seq (inc rP) (.seq (.load rB rP) (inc rP)))

/-- Add the label in register `x` to the labels if it is new. -/
def visit (x : ℕ) : Stmt :=
  .seq (.add rQ gD x) (.seq (.load rY rQ)
    (.ifz rY (.seq (st gLB gN x) (.seq (inc gN) (.store rQ gN))) .skip))

/-- One pair of the label pass. -/
def labBody : Stmt := .seq readPair (ifLt rA rB (.seq (visit rA) (visit rB)) .skip)
/-- Step 3. -/
def stepLabels : Stmt := forUp rI gM labBody

/-- `rU, rV :=` the ids of `rA`, `rB` (dictionary `- 1`), ordered. -/
def edgeIds : Stmt :=
  .seq (ld rU gD rA) (.seq (dec rU) (.seq (ld rV gD rB) (.seq (dec rV) (ifLt rV rU (swap rU rV) .skip))))
/-- Append the id pair `(rU, rV)` to `PU`, `PV`. -/
def idsIns : Stmt :=
  .seq edgeIds (.seq (st PairIds.rPU PairIds.rPL rU) (.seq (st PairIds.rPV PairIds.rPL rV)
    (inc PairIds.rPL)))
/-- One pair of the id pass. -/
def idsBody : Stmt := .seq readPair (ifLt rA rB idsIns .skip)
/-- `L := 0`, `rP := 1`, `N := gN` (the arguments of `PairIds.pairLeads`). -/
def idsInit : Stmt := .seq (.const PairIds.rPL 0) (.seq (.const rP 1) (mov PairIds.rPN gN))
/-- Step 4: the id pairs. -/
def stepIds : Stmt := .seq idsInit (forUp rI gM idsBody)

/-- Append `(PU[q], PV[q])` to the edge arrays. -/
def keepAdd : Stmt :=
  .seq (ld rU PairIds.rPU rI) (.seq (ld rV PairIds.rPV rI) (.seq (st gEU gNE rU)
    (.seq (st gEV gNE rV) (inc gNE))))
/-- One index of the keep pass: a first occurrence (`LEAD[q] = q`) is appended. -/
def keepBody : Stmt := .seq (ld rX PairIds.rLD rI) (ifEq rX rI keepAdd .skip)
/-- Step 6: the distinct id pairs, in order of first appearance. -/
def stepKeep : Stmt := .seq (.const gNE 0) (forUp rI PairIds.rPL keepBody)

/-- **Phase R0.** -/
def r0 : Stmt :=
  .seq stepMax (.seq stepLayout (.seq stepLabels (.seq stepIds (.seq PairIds.pairLeads stepKeep))))

/-! ### The layout -/

/-- The dictionary base `D = 2m + 1` (`M + 1 = labelBound g` cells). -/
def baseD (g : Graph) : ℕ := 2 * g.length + 1
/-- The label array (`2m` cells). -/
def baseLB (g : Graph) : ℕ := baseD g + maxLab g + 1
/-- The first ends of the edges (`m` cells). -/
def baseEU (g : Graph) : ℕ := baseLB g + 2 * g.length
/-- The second ends of the edges (`m` cells). -/
def baseEV (g : Graph) : ℕ := baseEU g + g.length
/-- The first ends of the id pairs `PU` (`m` cells). -/
def basePU (g : Graph) : ℕ := baseEV g + g.length
/-- The second ends of the id pairs `PV` (`m` cells). -/
def basePV (g : Graph) : ℕ := basePU g + g.length
/-- The free address on entry to `PairIds.pairLeads`. -/
def baseB2 (g : Graph) : ℕ := basePV g + g.length
/-- The end of the memory used by R0. -/
def endR0 (g : Graph) : ℕ := PairIds.leadsEnd (numV g) (idPairs g).length (baseB2 g)

/-- The layout as equations (for `omega`). -/
theorem layout_eqs (g : Graph) : baseD g = 2 * g.length + 1 ∧ baseLB g = baseD g + maxLab g + 1 ∧
    baseEU g = baseLB g + 2 * g.length ∧ baseEV g = baseEU g + g.length ∧
    basePU g = baseEV g + g.length ∧ basePV g = basePU g + g.length ∧
    baseB2 g = basePV g + g.length ∧
    endR0 g = PairIds.leadsEnd (numV g) (idPairs g).length (baseB2 g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The regions of R0 fit below `S` (one inequality per region). -/
theorem fits (g : Graph) (hS : endR0 g ≤ S) :
    baseLB g + 2 * g.length < S ∧ baseEU g + g.length < S ∧ baseEV g + g.length < S ∧
      basePU g + g.length < S ∧ basePV g + g.length < S ∧ baseB2 g < S ∧
      baseLB g = baseD g + maxLab g + 1 ∧ baseD g = 2 * g.length + 1 := by
  have hL := layout_eqs g
  have := PairIds.leads_eqs (numV g) (idPairs g).length (baseB2 g)
  unfold endR0 at hS
  omega

/-- **The memory of R0 is linear in the label bound and the input length.** -/
theorem endR0_le (g : Graph) : endR0 g ≤ 20 * (labelBound g + g.length + 1) := by
  have hL := layout_eqs g
  have h1 := PairIds.leadsEnd_le (numV g) (idPairs g).length (baseB2 g)
  have h2 := numV_le g
  have h3 := length_idPairs_le g
  rw [labelBound_eq]
  omega

/-! ### Global registers fixed after step 2 -/

/-- The global registers of R0 that keep their value from step 2 on. -/
@[mk_iff] structure Glob (g : Graph) (c : Config) : Prop where
  one : c.reg rONE = 1
  m : c.reg gM = g.length
  mx : c.reg gMX = maxLab g
  d : c.reg gD = baseD g
  lb : c.reg gLB = baseLB g
  eu : c.reg gEU = baseEU g
  ev : c.reg gEV = baseEV g
  pu : c.reg PairIds.rPU = basePU g
  pv : c.reg PairIds.rPV = basePV g

/-- The registers written by steps 3–6 that are not in `Glob`. -/
def W0 : List ℕ := [rT, rI, rP, rA, rB, rX, rQ, rY, rU, rV, gN, gNE, rFREE, PairIds.rPL,
  PairIds.rPN]

theorem Glob.regIndep (g : Graph) : RegIndep W0 (Glob g) := by indep [glob_iff]

/-! ### Step 1: the largest entry -/

/-- The invariant of the largest-entry scan after `j` entries. -/
def MaxInv (g : Graph) (j : ℕ) (c : Config) : Prop :=
  c.reg rONE = 1 ∧ c.reg gM = g.length ∧ c.reg gMX = ((ents g).take j).foldl max 0 ∧
    c.mem = (initial (graphInput g)).mem

theorem maxInit_spec (g : Graph) (hS : endR0 g ≤ S) :
    HTB S maxInit (fun c => c = initial (graphInput g))
      (fun c => MaxInv g 0 c ∧ c.reg r2M = 2 * g.length) 4 :=
  HTB.of_HT_addrOK (by decide) (fun c hc => by
    have := fits g hS
    subst hc; addr_ok [maxInit, initial_reg]) <| HT.run_le (by decide) (by decide) fun c hc => by
    subst hc
    simp +decide [maxInit, MaxInv, initial_mem, graphInput]; omega

theorem maxBody_spec (g : Graph) (hS : endR0 g ≤ S) (j : ℕ) (hj : j < 2 * g.length) :
    HTB S maxBody (fun c => MaxInv g j c ∧ c.reg rI = j ∧ c.reg r2M = 2 * g.length)
      (fun c => MaxInv g (j + 1) c ∧ c.reg rI = j ∧ c.reg r2M = 2 * g.length) 8 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨_, hi, _⟩ => by
    have := fits g hS
    addr_ok [maxBody, hi]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨h1, hm, hmx, hmem⟩, hi, h2m⟩ => ?_
  have he : c.mem (j + 1) = (ents g)[j]'(by simpa using hj) := by
    rw [hmem, initial_mem, graphInput_getD_succ g j hj]
  have hfold := foldl_max_take_succ (ents g) j (by simpa using hj)
  simp only [maxBody, run_seq', run_addc (show rI ≠ rT by decide), run_load, run_ifLt,
    run_mov (show rX ≠ rT by decide), run_skip]
  simp +decide only [setReg_reg, setReg_mem, ↓reduceIte, hi, he, hmx]
  split_ifs with hlt
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp +decide [h1, hm, hi, h2m, hmem, hfold]; omega
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp +decide [h1, hm, hi, h2m, hmem, hfold, hmx]; omega

/-- **Step 1**: `rONE = 1`, `gM = m`, `gMX = maxLab g`, memory untouched. -/
theorem stepMax_spec (g : Graph) (hS : endR0 g ≤ S) :
    HTB S stepMax (fun c => c = initial (graphInput g))
      (fun c => MaxInv g (2 * g.length) c ∧ c.reg r2M = 2 * g.length) (24 * g.length + 7) := by
  have hl := HTB.forUpC (i := rI) (n := r2M) (N := 2 * g.length) (body := maxBody) (MaxInv g) 8
    (by decide) (by decide) (by decide) (fun j => by indep [MaxInv])
    (fun j hj => maxBody_spec g hS j hj)
  exact ((maxInit_spec g hS).seq hl).mono (fun _ h => h) (fun c ⟨h, _, h2⟩ => ⟨h, h2⟩) (by omega)

theorem maxInv_full {g : Graph} {c : Config} (h : MaxInv g (2 * g.length) c) : c.reg gMX = maxLab g := by
  rw [h.2.2.1, maxLab, ← length_ents, List.take_length]

/-! ### Step 2: the layout -/

/-- The memory during the label pass, after the labels `L`. -/
structure LabMem (g : Graph) (L : List ℕ) (m : ℕ → ℕ) : Prop where
  input : Arr m 0 (graphInput g)
  dict : Tab m (baseD g) (maxLab g + 1) (dictOf L)
  lab : Arr m (baseLB g) (L ++ List.replicate (2 * g.length - L.length) 0)
  zero : ZeroFrom m (baseEU g)

/-- The state of the label pass after the labels `L`. -/
@[mk_iff] structure LabRep (g : Graph) (L : List ℕ) (c : Config) : Prop where
  glob : Glob g c
  free : c.reg rFREE = baseB2 g
  n : c.reg gN = L.length
  mem : LabMem g L c.mem

theorem LabRep.indep (g : Graph) (L : List ℕ) : Indep [rT, rI, rP, rA, rB, rQ, rY] (LabRep g L) := by
  indep [labRep_iff, glob_iff]

/-- **Step 2** (memory-free). -/
theorem stepLayout_spec (g : Graph) :
    HTB S stepLayout (fun c => MaxInv g (2 * g.length) c ∧ c.reg r2M = 2 * g.length)
      (fun c => LabRep g [] c ∧ c.reg rP = 1) 22 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hM, h2m⟩ => ?_
  have hmx := maxInv_full hM
  obtain ⟨h1, hm, -, hmem⟩ := hM
  have hz := zeroFrom_initial (graphInput g)
  simp only [length_graphInput] at hz
  have hL := layout_eqs g
  simp only [stepLayout, run_seq', run_addc (show r2M ≠ rT by decide), run_add,
    run_inc (show rFREE ≠ rT by decide), run_alloc (show r2M ≠ rT by decide) (show gLB ≠ r2M by decide),
    run_alloc (show gM ≠ rT by decide) (show gEU ≠ gM by decide),
    run_alloc (show gM ≠ rT by decide) (show gEV ≠ gM by decide),
    run_alloc (show gM ≠ rT by decide) (show PairIds.rPU ≠ gM by decide),
    run_alloc (show gM ≠ rT by decide) (show PairIds.rPV ≠ gM by decide), run_const]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  all_goals try (simp +decide [h1, hm, hmx, h2m, hL] <;> omega)
  · simp only [setReg_mem, hmem]
    refine ⟨arr_initial _, ?_, ?_, hz.mono (by omega)⟩
    · simpa using hz.tab (b := baseD g) (by omega) (maxLab g + 1)
    · simpa using hz.arr (b := baseLB g) (by omega) (2 * g.length)

/-! ### Step 3: the labels -/

/-- Appending a new label `a`: store it at the end of the label array and its id `+ 1` in the
dictionary. -/
theorem LabMem.snoc {g : Graph} {L : List ℕ} {m : ℕ → ℕ} {a : ℕ} (h : LabMem g L m)
    (ha : a ≤ maxLab g) (haL : a ∉ L) (hlen : L.length + 1 ≤ 2 * g.length) :
    LabMem g (L ++ [a]) (upd (upd m (baseLB g + L.length) a) (baseD g + a) (L.length + 1)) := by
  have hL := layout_eqs g
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (h.input.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega)
  · rw [dictOf_snoc haL]
    exact (h.dict.upd_of_disjoint (by omega)).upd (by omega)
  · have hl := h.lab
    rw [show 2 * g.length - L.length = (2 * g.length - (L.length + 1)) + 1 by omega] at hl
    have := (hl.push (x := a) rfl).upd_of_disjoint (a := baseD g + a) (v := L.length + 1)
      (by simp; omega)
    simpa using this
  · exact (h.zero.upd (by omega)).upd (by omega)

theorem visit_wregs (x : ℕ) : ∀ r ∈ wregs (visit x), r ∈ [rQ, rY, rT, gN] := by
  simp [visit, wregs]

theorem visit_wregs_W0 (x : ℕ) : ∀ r ∈ wregs (visit x), r ∈ W0 := fun r hr => by
  have := visit_wregs x r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl <;> decide

theorem loopFree_visit (x : ℕ) : LoopFree (visit x) := by simp [visit, LoopFree]

/-- **Visiting a label**: the labels grow by `ext`; the accesses are in the dictionary and
the label array. -/
theorem visit_run {g : Graph} {L : List ℕ} {x a : ℕ} {c : Config} (hx : x = rA ∨ x = rB)
    (hR : LabRep g L c) (hxa : c.reg x = a) (ha : a ≤ maxLab g) (hlen : (ext L a).length ≤ 2 * g.length)
    (hS : endR0 g ≤ S) :
    LabRep g (ext L a) (run (visit x) c) ∧ AddrOK S (visit x) c := by
  have hy : c.mem (baseD g + a) = dictOf L a := hR.mem.dict.get (by omega)
  have hxT : x ≠ rT ∧ x ≠ rQ ∧ x ≠ rY ∧ x ≠ gN := by rcases hx with rfl | rfl <;> decide
  have hd := hR.glob.d
  have hlb := hR.glob.lb
  have hn := hR.n
  have hlL := length_le_ext L a
  refine ⟨⟨(Glob.regIndep g).run_of_sub (loopFree_visit x) (visit_wregs_W0 x) hR.glob,
    (run_reg_of_not_mem (loopFree_visit x) (fun h => by have := visit_wregs x _ h; simp at this) c).trans
      hR.free, ?_, ?_⟩, ?_⟩
  rotate_left 2
  · have := fits g hS
    rcases hx with rfl | rfl <;> addr_ok [visit, hd, hlb, hn, hxa]
  all_goals
    simp +decide only [visit, run_seq', run_add, run_load, run_ifz', setReg_reg, ↓reduceIte, hd, hxa,
      setReg_mem, hy]
  · by_cases haL : a ∈ L
    · have h0 : dictOf L a ≠ 0 := fun h => dictOf_eq_zero_iff.mp h haL
      simp +decide [h0, ext_of_mem haL, hn]
    · have h0 : dictOf L a = 0 := dictOf_eq_zero_iff.mpr haL
      simp +decide [h0, ext_of_not_mem haL, run_st hxT.1, run_inc, hn]
  · by_cases haL : a ∈ L
    · have h0 : dictOf L a ≠ 0 := fun h => dictOf_eq_zero_iff.mp h haL
      simp only [h0, ↓reduceIte, run_skip, setReg_mem, ext_of_mem haL]
      exact hR.mem
    · have h0 : dictOf L a = 0 := dictOf_eq_zero_iff.mpr haL
      rw [ext_of_not_mem haL] at hlen ⊢
      have hlen' : L.length + 1 ≤ 2 * g.length := by simpa using hlen
      have hmem := hR.mem.snoc ha haL hlen'
      simpa +decide [h0, run_st hxT.1, run_inc, hlb, hn, hxa, hd, hxT.2.1, hxT.2.2.1] using hmem

/-- Reading a pair. -/
theorem readPair_run (c : Config) :
    (run readPair c).reg rA = c.mem (c.reg rP) ∧ (run readPair c).reg rB = c.mem (c.reg rP + 1) ∧
      (run readPair c).reg rP = c.reg rP + 2 ∧ Agree [rA, rB, rP, rT] c (run readPair c) := by
  refine ⟨by simp +decide [readPair, run_inc], by simp +decide [readPair, run_inc],
    by simp +decide [readPair, run_inc], agree_run (by decide) rfl rfl (by decide) c⟩

/-- The input cells read by `readPair`. -/
theorem readPair_addrOK {g : Graph} {c : Config} {j : ℕ} (hp : c.reg rP = 2 * j + 1)
    (hj : j < g.length) (hS : endR0 g ≤ S) : AddrOK S readPair c := by
  have := fits g hS
  addr_ok [readPair, hp]

/-- The invariant of the label pass after `j` pairs. -/
def LabInv (g : Graph) (j : ℕ) (c : Config) : Prop :=
  LabRep g (labels (g.take j)) c ∧ c.reg rP = 2 * j + 1

theorem labBody_spec (g : Graph) (hS : endR0 g ≤ S) (j : ℕ) (hj : j < g.length) :
    HTB S labBody (fun c => LabInv g j c ∧ c.reg rI = j ∧ c.reg gM = g.length)
      (fun c => LabInv g (j + 1) c ∧ c.reg rI = j ∧ c.reg gM = g.length) 27 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hp⟩, hi, hm⟩ => ?_
  have hA₀ := readPair_addrOK hp hj hS
  obtain ⟨ha, hb⟩ := input_pair hR.mem.input hj
  obtain ⟨hA, hB, hP, hAg⟩ := readPair_run c
  rw [hp, ha] at hA
  rw [hp, show 2 * j + 1 + 1 = 2 * j + 2 by omega, hb] at hB
  rw [hp] at hP
  have hR₁ : LabRep g (labels (g.take j)) (run readPair c) :=
    ((LabRep.indep g _).mono (by decide)) c _ hAg hR
  have hi₁ : (run readPair c).reg rI = j := (hAg.reg rI (by decide)).trans hi
  have hm₁ : (run readPair c).reg gM = g.length := (hAg.reg gM (by decide)).trans hm
  have hlen := length_labels_take_le g (j + 1)
  have hent := pair_mem_ents g j hj
  have hvis : ∀ r, r ≠ rQ → r ≠ rY → r ≠ rT → r ≠ gN → ∀ x c, (run (visit x) c).reg r = c.reg r :=
    fun r h1 h2 h3 h4 x c => run_reg_of_not_mem (loopFree_visit x)
      (fun h => by have := visit_wregs x r h; simp_all) c
  unfold LabInv
  rw [labels_take_succ g j hj] at hlen ⊢
  by_cases hab : g[j].1 < g[j].2
  · simp only [hab, ↓reduceIte] at hlen ⊢
    have hR₂ := (LabRep.indep g _).setReg (d := rT) (by decide) (g[j].2 - g[j].1) hR₁
    obtain ⟨h3, a3⟩ := visit_run (x := rA) (Or.inl rfl) hR₂ (by simp +decide [hA])
      (le_maxLab hent.1) (le_trans (length_le_ext _ g[j].2) (by omega)) hS
    obtain ⟨h4, a4⟩ := visit_run (x := rB) (Or.inr rfl) h3
      (by rw [hvis rB (by decide) (by decide) (by decide) (by decide)]; simp +decide [hB])
      (le_maxLab hent.2) (by omega) hS
    refine ⟨hA₀.seq (AddrOK.ifLt (fun _ => ?_) (fun _ => by simp)), ?_⟩
    · rw [hA, hB]; exact a3.seq a4
    simp only [labBody, run_seq', run_ifLt, hA, hB, hab, ↓reduceIte]
    refine ⟨⟨h4, ?_⟩, ?_, ?_⟩ <;>
      rw [hvis _ (by decide) (by decide) (by decide) (by decide),
        hvis _ (by decide) (by decide) (by decide) (by decide)]
    · simp +decide [hP]; omega
    · simp +decide [hi₁]
    · simp +decide [hm₁]
  · simp only [hab, ↓reduceIte]
    refine ⟨hA₀.seq (AddrOK.ifLt (fun h => by rw [hA, hB] at h; exact absurd h hab)
      (fun _ => by simp)), ?_⟩
    simp only [labBody, run_seq', run_ifLt, hA, hB, hab, ↓reduceIte]
    refine ⟨⟨(LabRep.indep g _).setReg (d := rT) (by decide) _ hR₁, ?_⟩, ?_, ?_⟩
    · simp +decide [hP]; omega
    · simp +decide [hi₁]
    · simp +decide [hm₁]

/-- **Step 3**: the label pass. -/
theorem stepLabels_spec (g : Graph) (hS : endR0 g ≤ S) :
    HTB S stepLabels (fun c => LabInv g 0 c ∧ c.reg gM = g.length)
      (fun c => LabInv g g.length c ∧ c.reg rI = g.length ∧ c.reg gM = g.length) (g.length * 31 + 3) :=
  HTB.forUpC (i := rI) (n := gM) (N := g.length) (body := labBody) (LabInv g) 27
    (by decide) (by decide) (by decide) (fun j => by indep [LabInv, labRep_iff, glob_iff])
    (fun j hj => labBody_spec g hS j hj)

end STACS2027.RAM.R0
