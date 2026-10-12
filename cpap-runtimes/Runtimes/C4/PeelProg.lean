module

public import Runtimes.C4.RamBase
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Phase PEEL: the program, its representation, and the loop-free blocks

Phase PEEL computes the peeling order of `Spec.lean` with a lazy bucket queue.
It starts in a `C4Base g` configuration `c₀` with first free address `F = c₀.reg rFREE`, and

1. `peelAlloc`: allocates `CUR` (`F`), `DEL` (`F + N`), `BH` (`F + 2N`), `POS` (`F + 3N`),
   `N` cells each; the stack nodes are allocated from `F + 4N` on, two cells each
   (value, successor), by `pushB` (push the vertex `xW` onto bucket `xD`);
2. `stepInit` (`forUp xI gN initBody`): `CUR[v] := OFF[v + 1] - OFF[v] = |nb v|` and push `v`
   onto bucket `|nb v|` — the state `pinitPre (nb g) v` (`pinitPre_succ`);
3. `stepMain`: `xS := 0` (the number of removed vertices), `xP := 0` (the bucket pointer), then
   one `pstep` per round of `whileC peelCond peelBody`: read the head of bucket `xP`; if it
   is empty advance the pointer, else pop the top `v`, and if `DEL[v] = 0` and `CUR[v] = xP`
   remove `v`: `DEL[v] := 1`, `POS[v] := xS`, `xS += 1`, relax every neighbour
   (`forRange xJ xA xB relaxBody`, `xA = OFF[v]`, `xB = OFF[v + 1]`), `xP -= 1`.

The representation `PRep g c₀ k s c` of an abstract state `s : PState` (with `k` valid cells
of `CUR`): the global registers (`PGlob`), `CUR`/`DEL` as tables of `s.cur`/`s.del`, the
positions of the removed vertices in `POS`, every bucket `d < N` as a linked list from
`BH[d]` with nodes in `[F + 4N, rFREE)`, and free memory from `rFREE`. Memory steps on `upd`:
`PMem.push`, `PMem.extCur`, `PMem.setCur`, `PMem.pop`, `PMem.removeHead`; `run` lemmas for the
loop-free blocks, each with the address bound `AddrOK S` of the block for any `S` above the
layout end `peelEnd g F = F + 6N + 4 |E|` (`peel_fits`): `pushB_run`, `initBody_run`,
`relaxBody_run`, `popRead_run`, `removeHead_run`.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM

/-! ### The program -/

/-- Step 1: the arrays `CUR`, `DEL`, `BH`, `POS`. -/
def peelAlloc : Stmt :=
  .seq (alloc gCUR gN) (.seq (alloc gDEL gN) (.seq (alloc gBH gN) (alloc gPOS gN)))

/-- Push the vertex `xW` onto bucket `xD`: a new node at `rFREE` holding `xW` and the old
head. -/
def pushB : Stmt :=
  .seq (ld xH gBH xD) (.seq (.store rFREE xW) (.seq (addc xQ rFREE 1) (.seq (.store xQ xH)
    (.seq (st gBH xD rFREE) (addc rFREE rFREE 2)))))

/-- `CUR[i] := OFF[i + 1] - OFF[i]`, `xW := i`, `xD := CUR[i]`. -/
def initPre : Stmt :=
  .seq (ld xX gOFF xI) (.seq (addc xQ xI 1) (.seq (ld xY gOFF xQ) (.seq (.sub xD xY xX)
    (.seq (st gCUR xI xD) (mov xW xI)))))

/-- One vertex of the initialization. -/
def initBody : Stmt := .seq initPre pushB

/-- Step 2: the initial buckets. -/
def stepInit : Stmt := forUp xI gN initBody

/-- Relax the neighbour `xW` (not removed): `CUR[w] -= 1`, push `w` onto its new bucket. -/
def relaxDo : Stmt := .seq (ld xD gCUR xW) (.seq (dec xD) (.seq (st gCUR xW xD) pushB))

/-- One neighbour `w = ADJ[xJ]` of the removed vertex. -/
def relaxBody : Stmt := .seq (ld xW gADJ xJ) (.seq (ld xX gDEL xW) (.ifz xX relaxDo .skip))

/-- Removal of `v = xV`, before the relaxation: `DEL[v] := 1`, `POS[v] := xS`, `xS += 1`,
`xA := OFF[v]`, `xB := OFF[v + 1]`. -/
def removeHead : Stmt :=
  .seq (st gDEL xV rONE) (.seq (st gPOS xV xS) (.seq (inc xS) (.seq (ld xA gOFF xV)
    (.seq (addc xQ xV 1) (ld xB gOFF xQ)))))

/-- Removal of `v = xV`. -/
def removeV : Stmt := .seq removeHead (.seq (forRange xJ xA xB relaxBody) (dec xP))

/-- Pop the top `v` of bucket `xP` (head in `xH`); `xX := DEL[v]`, `xY := CUR[v]`. -/
def popRead : Stmt :=
  .seq (.load xV xH) (.seq (addc xQ xH 1) (.seq (.load xX xQ) (.seq (st gBH xP xX)
    (.seq (ld xX gDEL xV) (ld xY gCUR xV)))))

/-- Pop, and remove the popped vertex if its entry is valid. -/
def popStep : Stmt := .seq popRead (.ifz xX (ifEq xY xP removeV .skip) .skip)

/-- One round of the peeling loop. -/
def peelBody : Stmt := .seq (ld xH gBH xP) (.ifz xH (inc xP) popStep)

/-- The loop test: `N - xS` (zero iff all vertices are removed). -/
def peelCond : Stmt := .sub rT gN xS

/-- Step 3: the peeling loop. -/
def stepMain : Stmt := .seq (.const xS 0) (.seq (.const xP 0) (whileC peelCond peelBody))

/-- **Phase PEEL.** -/
def peel : Stmt := .seq peelAlloc (.seq stepInit stepMain)

/-! ### The layout -/

section layout

variable (g : Graph) (F : ℕ)

/-- `DEL` (`N` cells); `CUR` is at `F`. -/
def bDEL : ℕ := F + numV g
/-- `BH` (`N` cells). -/
def bBH : ℕ := F + 2 * numV g
/-- `POS` (`N` cells). -/
def bPOS : ℕ := F + 3 * numV g
/-- The first stack node. -/
def bNODE : ℕ := F + 4 * numV g

/-- The end of PEEL's memory: the four arrays and at most `N + 2 |E|` stack nodes (one per
push: `N` initial pushes and at most one per relaxed neighbour, `Σ_v |nb v| = 2 |E|`). -/
def peelEnd : ℕ := F + 6 * numV g + 4 * (idEdges g).length

theorem peel_layout : bDEL g F = F + numV g ∧ bBH g F = F + 2 * numV g ∧
    bPOS g F = F + 3 * numV g ∧ bNODE g F = F + 4 * numV g := ⟨rfl, rfl, rfl, rfl⟩

/-- The regions of PEEL fit below `S` (one inequality per region). -/
theorem peel_fits {S : ℕ} (hS : peelEnd g F ≤ S) :
    F + numV g ≤ S ∧ bDEL g F + numV g ≤ S ∧ bBH g F + numV g ≤ S ∧ bPOS g F + numV g ≤ S ∧
      bNODE g F + 2 * numV g + 4 * (idEdges g).length ≤ S := by
  simp only [peelEnd, bDEL, bBH, bPOS, bNODE] at hS ⊢
  omega

end layout

/-! ### Representation -/

/-- The registers fixed during PEEL (after the allocation). -/
@[mk_iff] structure PGlob (g : Graph) (c₀ c : Config) : Prop where
  one : c.reg rONE = 1
  n : c.reg gN = numV g
  off : c.reg gOFF = c₀.reg gOFF
  adj : c.reg gADJ = c₀.reg gADJ
  cur : c.reg gCUR = c₀.reg rFREE
  del : c.reg gDEL = bDEL g (c₀.reg rFREE)
  bh : c.reg gBH = bBH g (c₀.reg rFREE)
  pos : c.reg gPOS = bPOS g (c₀.reg rFREE)

/-- The registers written by PEEL after the allocation. -/
def WP : List ℕ := [rT, rFREE, xI, xJ, xA, xB, xV, xW, xX, xY, xH, xQ, xD, xS, xP]

theorem PGlob.regIndep (g : Graph) (c₀ : Config) : RegIndep WP (PGlob g c₀) := by
  indep [pGlob_iff]

/-- The memory during PEEL: the abstract state `s` (with `k` valid cells of `CUR`), first free
address `fr`. -/
structure PMem (g : Graph) (c₀ : Config) (k : ℕ) (s : PState) (fr : ℕ) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  kle : k ≤ numV g
  cur : Tab m (c₀.reg rFREE) k s.cur
  del : Tab m (bDEL g (c₀.reg rFREE)) (numV g) fun v => if s.del v then 1 else 0
  pos : ∀ v < numV g, v ∈ s.ord → m (bPOS g (c₀.reg rFREE) + v) = s.ord.idxOf v
  bh : ∀ d < numV g, LL m (bNODE g (c₀.reg rFREE)) fr (m (bBH g (c₀.reg rFREE) + d)) (s.stk d)
  low : bNODE g (c₀.reg rFREE) ≤ fr
  zero : ZeroFrom m fr

/-- The machine represents the abstract peeling state `s`. -/
@[mk_iff] structure PRep (g : Graph) (c₀ : Config) (k : ℕ) (s : PState) (c : Config) : Prop where
  glob : PGlob g c₀ c
  mem : PMem g c₀ k s (c.reg rFREE) c.mem

theorem PRep.indep (g : Graph) (c₀ : Config) (k : ℕ) (s : PState) :
    Indep [rT, xI, xJ, xA, xB, xV, xW, xX, xY, xH, xQ, xD, xS, xP] (PRep g c₀ k s) := by
  indep [pRep_iff, pGlob_iff]

/-! ### Memory steps -/

section mem

variable {g : Graph} {c₀ : Config} {k : ℕ} {s : PState} {fr : ℕ} {m : ℕ → ℕ}

/-- Pushing `w` onto bucket `d`: three stores (new node at `fr`, then the head). -/
theorem PMem.push (h : PMem g c₀ k s fr m) {w d : ℕ} (hd : d < numV g) :
    PMem g c₀ k (C4.push s w d) (fr + 2)
      (RAM.upd (RAM.upd (RAM.upd m fr w) (fr + 1) (m (bBH g (c₀.reg rFREE) + d)))
        (bBH g (c₀.reg rFREE) + d) fr) := by
  have hL := peel_layout g (c₀.reg rFREE)
  have hlow := h.low
  have hk := h.kle
  refine ⟨((h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge (by omega) _, hk,
    ((h.cur.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    ((h.del.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    ?_, ?_, by omega, ?_⟩
  · intro v hv hvo
    rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
    exact h.pos v hv hvo
  · intro d' hd'
    have hm : ∀ q, bNODE g (c₀.reg rFREE) ≤ q → q < fr →
        RAM.upd (RAM.upd (RAM.upd m fr w) (fr + 1) (m (bBH g (c₀.reg rFREE) + d)))
          (bBH g (c₀.reg rFREE) + d) fr q = m q := by
      intro q h1 h2
      rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
    rw [push_stk]
    by_cases hdd : d' = d
    · subst hdd
      simp only [↓reduceIte, upd_same]
      refine LL.push (h.bh d' hd') hlow hm ?_ ?_
      · rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega), upd_same]
      · rw [upd_ne _ _ (by omega), upd_same]
    · simp only [hdd, ↓reduceIte]
      rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
      exact ((h.bh d' hd').congr hm).mono (by omega)
  · exact ((h.zero.mono (by omega)).upd (by omega) |>.upd (by omega)).upd (by omega)

/-- Initializing one more cell of `CUR`. -/
theorem PMem.extCur (h : PMem g c₀ k s fr m) (hk : k < numV g) :
    PMem g c₀ (k + 1) s fr (RAM.upd m (c₀.reg rFREE + k) (s.cur k)) := by
  have hL := peel_layout g (c₀.reg rFREE)
  have hlow := h.low
  refine ⟨h.same.upd_of_ge (by omega) _, hk, (h.cur.upd_of_disjoint (by omega)).snoc
    (by simp), h.del.upd_of_disjoint (by omega), ?_, ?_, hlow, h.zero.upd (by omega)⟩
  · intro v hv hvo
    rw [upd_ne _ _ (by omega)]; exact h.pos v hv hvo
  · intro d hd
    rw [upd_ne _ _ (by omega)]
    exact (h.bh d hd).upd (by omega)

/-- Setting the current degree of `w < k`. -/
theorem PMem.setCur (h : PMem g c₀ k s fr m) {w : ℕ} (hw : w < k) (x : ℕ) :
    PMem g c₀ k { s with cur := Function.update s.cur w x } fr
      (RAM.upd m (c₀.reg rFREE + w) x) := by
  have hL := peel_layout g (c₀.reg rFREE)
  have hlow := h.low
  have hk := h.kle
  refine ⟨h.same.upd_of_ge (by omega) _, hk, h.cur.upd rfl, h.del.upd_of_disjoint (by omega),
    ?_, ?_, hlow, h.zero.upd (by omega)⟩
  · intro v hv hvo
    rw [upd_ne _ _ (by omega)]; exact h.pos v hv hvo
  · intro d hd
    rw [upd_ne _ _ (by omega)]
    exact (h.bh d hd).upd (by omega)

/-- Popping the top of bucket `p`: the head becomes the successor of the old head. -/
theorem PMem.pop (h : PMem g c₀ k s fr m) {p v : ℕ} {rest : List ℕ} (hp : p < numV g)
    (he : s.stk p = v :: rest) :
    PMem g c₀ k { s with stk := Function.update s.stk p rest } fr
      (RAM.upd m (bBH g (c₀.reg rFREE) + p) (m (m (bBH g (c₀.reg rFREE) + p) + 1))) := by
  have hL := peel_layout g (c₀.reg rFREE)
  have hlow := h.low
  have hk := h.kle
  refine ⟨h.same.upd_of_ge (by omega) _, hk, h.cur.upd_of_disjoint (by omega),
    h.del.upd_of_disjoint (by omega), ?_, ?_, hlow, h.zero.upd (by omega)⟩
  · intro v hv hvo
    rw [upd_ne _ _ (by omega)]; exact h.pos v hv hvo
  · intro d hd
    simp only [Function.update_apply]
    by_cases hdp : d = p
    · subst hdp
      simp only [↓reduceIte, upd_same]
      have h1 := h.bh d hd
      rw [he] at h1
      exact h1.2.2.2.upd (by omega)
    · simp only [hdp, ↓reduceIte]
      rw [upd_ne _ _ (by omega)]
      exact (h.bh d hd).upd (by omega)

/-- Marking `v` removed and recording its position. -/
theorem PMem.removeHead (h : PMem g c₀ k s fr m) {v : ℕ} (hv : v < numV g) (hvo : v ∉ s.ord) :
    PMem g c₀ k { s with del := Function.update s.del v true, ord := s.ord ++ [v] } fr
      (RAM.upd (RAM.upd m (bDEL g (c₀.reg rFREE) + v) 1) (bPOS g (c₀.reg rFREE) + v)
        s.ord.length) := by
  have hL := peel_layout g (c₀.reg rFREE)
  have hlow := h.low
  have hk := h.kle
  refine ⟨(h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _, hk,
    (h.cur.upd_of_disjoint (by omega)).upd_of_disjoint (by omega), ?_, ?_, ?_, hlow,
    (h.zero.upd (by omega)).upd (by omega)⟩
  · refine ((h.del.upd rfl).upd_of_disjoint (by omega)).congr_fun fun u _ => ?_
    by_cases hu : u = v
    · subst hu; simp
    · simp [Function.update_of_ne hu]
  · intro u hu huo
    by_cases huv : u = v
    · subst huv
      rw [upd_same, List.idxOf_append_of_notMem hvo]
      simp
    · rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
      have hu' : u ∈ s.ord := by simpa [huv] using huo
      rw [List.idxOf_append_of_mem hu']
      exact h.pos u hu hu'
  · intro d hd
    rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega)]
    exact ((h.bh d hd).upd (by omega)).upd (by omega)

end mem

/-! ### Loop-free blocks

Each `…_run` lemma also gives the address bound `AddrOK S …` of the block, for any `S` above
PEEL's layout (`peelEnd`); a push needs two free cells below `S` (`c.reg rFREE + 2 ≤ S`). -/

section blocks

variable {g : Graph} {c₀ c : Config} {k : ℕ} {s : PState} {S : ℕ}

theorem PMem.ofEq {fr fr' : ℕ} {m : ℕ → ℕ} (h : PMem g c₀ k s fr m) (e : fr = fr') :
    PMem g c₀ k s fr' m := e ▸ h

/-- **Push** of `w = xW` onto the bucket `d = xD`. -/
theorem pushB_run (hR : PRep g c₀ k s c) {w d : ℕ} (hw : c.reg xW = w) (hd : c.reg xD = d)
    (hdN : d < numV g) (hS : peelEnd g (c₀.reg rFREE) ≤ S) (hfr : c.reg rFREE + 2 ≤ S) :
    PRep g c₀ k (C4.push s w d) (run pushB c) ∧
      (∀ r, r ≠ xH → r ≠ xQ → r ≠ rT → r ≠ rFREE → (run pushB c).reg r = c.reg r) ∧
      (run pushB c).reg rFREE = c.reg rFREE + 2 ∧ AddrOK S pushB c := by
  have hG := hR.glob
  have hF := peel_fits g (c₀.reg rFREE) hS
  refine ⟨⟨(PGlob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_⟩, fun r h1 h2 h3 h4 =>
    run_reg_of_not_mem (by decide) (by simp [pushB, wregs, h1, h2, h3, h4]) c,
    by simp +decide [pushB, run_st, run_addc], by addr_ok [pushB, hG.bh, hd]⟩
  have := hR.mem.push (w := w) hdN
  simpa +decide [pushB, run_st, run_addc, hG.bh, hw, hd] using this

/-- **Initialization** of vertex `i`. -/
theorem initBody_run (hB : C4Base g c₀) {i : ℕ} (hR : PRep g c₀ i (pinitPre (nb g) i) c)
    (hi : c.reg xI = i) (hiN : i < numV g) (hS : peelEnd g (c₀.reg rFREE) ≤ S)
    (hfr : c.reg rFREE + 2 ≤ S) :
    PRep g c₀ (i + 1) (pinitPre (nb g) (i + 1)) (run initBody c) ∧
      (run initBody c).reg xI = i ∧ (run initBody c).reg gN = numV g ∧
      (run initBody c).reg rFREE = c.reg rFREE + 2 ∧ AddrOK S initBody c := by
  have hG := hR.glob
  have hS' := hR.mem.same
  have hF := peel_fits g (c₀.reg rFREE) hS
  have hb := hB.bounds
  have ho0 : c.mem (c₀.reg gOFF + i) = R1.ps (idEdges g) i := hB.offR hS' (by omega)
  have ho1 : c.mem (c₀.reg gOFF + (i + 1)) = R1.ps (idEdges g) (i + 1) := hB.offR hS' (by omega)
  have hcur : (pinitPre (nb g) i).cur i = (nb g i).length := by rw [(pinitPre_fields _ i).2.1]
  have hdeg : R1.ps (idEdges g) (i + 1) - R1.ps (idEdges g) i = (nb g i).length := by
    rw [R1.ps_succ]; simp
  have hA₁ : AddrOK S initPre c := by addr_ok [initPre, hG.off, hG.cur, hi]
  have hR1 : PRep g c₀ (i + 1) (pinitPre (nb g) i) (run initPre c) := by
    refine ⟨(PGlob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_⟩
    have := hR.mem.extCur hiN
    rw [hcur] at this
    simpa +decide [initPre, run_st, run_addc, run_mov, hG.off, hG.cur, hi, ho0, ho1, hdeg]
      using this
  have hw : (run initPre c).reg xW = i := by simp +decide [initPre, run_st, run_addc, run_mov, hi]
  have hd : (run initPre c).reg xD = (nb g i).length := by
    simp +decide [initPre, run_st, run_addc, run_mov, hi, hG.off, ho0, ho1, hdeg]
  have hfr₁ : (run initPre c).reg rFREE = c.reg rFREE := by
    simp +decide [initPre, run_st, run_addc, run_mov]
  obtain ⟨hR2, hreg, hfr₂, hA₂⟩ := pushB_run hR1 hw hd ((nbOk g).length_lt hiN) hS
    (by rw [hfr₁]; exact hfr)
  rw [pinitPre_succ]
  simp only [initBody, run_seq']
  refine ⟨hR2, ?_, ?_, by rw [hfr₂, hfr₁], hA₁.seq hA₂⟩
  · rw [hreg _ (by decide) (by decide) (by decide) (by decide)]
    simp +decide [initPre, run_st, run_addc, run_mov, hi]
  · rw [hreg _ (by decide) (by decide) (by decide) (by decide)]
    simp +decide [initPre, run_st, run_addc, run_mov, hG.n]

/-- **Relaxing** the neighbour `w = ADJ[xJ]` (the `i`-th neighbour of `v`). -/
theorem relaxBody_run (hB : C4Base g c₀) {s' : PState} (hR : PRep g c₀ (numV g) s' c)
    {v i : ℕ} (hv : v < numV g) (hi : i < (nb g v).length)
    (hj : c.reg xJ = R1.ps (idEdges g) v + i)
    (hcw : s'.del ((nb g v).getD i 0) = false → s'.cur ((nb g v).getD i 0) < numV g)
    (hS : peelEnd g (c₀.reg rFREE) ≤ S) (hfr : c.reg rFREE + 2 ≤ S) :
    PRep g c₀ (numV g) (relax s' ((nb g v).getD i 0)) (run relaxBody c) ∧
      (∀ r, r ≠ xW → r ≠ xX → r ≠ xD → r ≠ xH → r ≠ xQ → r ≠ rT → r ≠ rFREE →
        (run relaxBody c).reg r = c.reg r) ∧
      (run relaxBody c).reg rFREE ≤ c.reg rFREE + 2 ∧ AddrOK S relaxBody c := by
  have hG := hR.glob
  have hL := peel_layout g (c₀.reg rFREE)
  have hF := peel_fits g (c₀.reg rFREE) hS
  have hb := hB.bounds
  set w := (nb g v).getD i 0 with hw_def
  have hwN : w < numV g := (nbOk g).lt v w (by rw [hw_def, getD_eq_getElem' hi]; simp)
  have hadj : c.mem (c₀.reg gADJ + (R1.ps (idEdges g) v + i)) = w := hB.adjR hR.mem.same hv hi
  have hdel : c.mem (bDEL g (c₀.reg rFREE) + w) = if s'.del w then 1 else 0 := hR.mem.del.get hwN
  have hcur : c.mem (c₀.reg rFREE + w) = s'.cur w := hR.mem.cur.get hwN
  have hpsv : R1.ps (idEdges g) v + i < 2 * (idEdges g).length := by
    have h1 : R1.ps (idEdges g) v + (nb g v).length ≤ R1.ps (idEdges g) (numV g) :=
      R1.ps_add_le (idEdges g) (show v < numV g from hv)
    rw [R1.idEdges_ps] at h1
    omega
  -- the two loads
  set c₁ := run (.seq (ld xW gADJ xJ) (ld xX gDEL xW)) c with hc₁
  have hA₁ : AddrOK S (.seq (ld xW gADJ xJ) (ld xX gDEL xW)) c := by
    addr_ok [hG.adj, hG.del, hj, hadj]
  have hR₁ : PRep g c₀ (numV g) s' c₁ :=
    (PRep.indep g c₀ (numV g) s').mono (W' := [xW, xX]) (by decide) c c₁
      (agree_run (by decide) rfl rfl (by decide) c) hR
  have hW₁ : c₁.reg xW = w := by simp +decide [hc₁, hG.adj, hj, hadj]
  have hX₁ : c₁.reg xX = if s'.del w then 1 else 0 := by
    simp +decide [hc₁, hG.adj, hG.del, hj, hadj, hdel]
  have hreg₁ : ∀ r, r ≠ xW → r ≠ xX → c₁.reg r = c.reg r := fun r h1 h2 =>
    run_reg_of_not_mem (by decide) (by simp [wregs, h1, h2]) c
  have hrun : run relaxBody c = run (.ifz xX relaxDo .skip) c₁ := by simp [relaxBody, hc₁]
  have hA : AddrOK S (.ifz xX relaxDo .skip) c₁ → AddrOK S relaxBody c := fun h =>
    ⟨hA₁.1, hA₁.2, by simpa [hc₁] using h⟩
  rw [hrun]
  cases hdw : s'.del w
  · -- not removed: decrement and push
    have hX0 : c₁.reg xX = 0 := by rw [hX₁, hdw]; simp
    simp only [run_ifz', hX0, ↓reduceIte]
    have hcw' := hcw hdw
    have hG₁ := hR₁.glob
    have hcur₁ : c₁.mem (c₀.reg rFREE + w) = s'.cur w := hR₁.mem.cur.get hwN
    set c₂ := run (.seq (ld xD gCUR xW) (.seq (dec xD) (st gCUR xW xD))) c₁ with hc₂
    have hA₂ : AddrOK S (.seq (ld xD gCUR xW) (.seq (dec xD) (st gCUR xW xD))) c₁ := by
      addr_ok [hG₁.cur, hW₁]
    have hR₂ : PRep g c₀ (numV g) { s' with cur := Function.update s'.cur w (s'.cur w - 1) } c₂ := by
      refine ⟨(PGlob.regIndep g c₀).run_of_sub (by decide) (by decide) hG₁, ?_⟩
      have := hR₁.mem.setCur hwN (s'.cur w - 1)
      simpa +decide [hc₂, run_st, run_dec, hG₁.cur, hW₁, hcur₁] using this
    have hW₂ : c₂.reg xW = w := by simp +decide [hc₂, run_st, run_dec, hW₁]
    have hD₂ : c₂.reg xD = s'.cur w - 1 := by
      simp +decide [hc₂, run_st, run_dec, hW₁, hG₁.cur, hcur₁]
    have hfr₂ : c₂.reg rFREE = c.reg rFREE := by
      rw [show c₂.reg rFREE = c₁.reg rFREE by simp +decide [hc₂, run_st, run_dec],
        hreg₁ rFREE (by decide) (by decide)]
    obtain ⟨hR₃, hreg₃, hfr₃, hA₃⟩ := pushB_run hR₂ hW₂ hD₂ (by omega) hS (by rw [hfr₂]; exact hfr)
    have hrun₂ : run relaxDo c₁ = run pushB c₂ := by simp [relaxDo, hc₂]
    refine ⟨?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, by rw [hrun₂, hfr₃, hfr₂],
      hA ⟨fun _ => ?_, fun h => absurd hX0 h⟩⟩
    · rw [hrun₂]
      have : relax s' w = C4.push { s' with cur := Function.update s'.cur w (s'.cur w - 1) } w
          (s'.cur w - 1) := by simp [relax, hdw]
      rw [this]; exact hR₃
    · rw [hrun₂, hreg₃ r h4 h5 h6 h7, hc₂,
        run_reg_of_not_mem (by decide) (by simp [wregs, h3, h6]), hreg₁ r h1 h2]
    · exact hA₂.1.seq (hA₂.2.1.seq (hA₂.2.2.seq (by simpa [hc₂] using hA₃)))
  · -- removed: nothing
    have hX0 : c₁.reg xX ≠ 0 := by rw [hX₁, hdw]; simp
    simp only [run_ifz', hX0, ↓reduceIte, run_skip]
    have : relax s' w = s' := by simp [relax, hdw]
    rw [this]
    exact ⟨hR₁, fun r h1 h2 _ _ _ _ _ => hreg₁ r h1 h2,
      by rw [hreg₁ rFREE (by decide) (by decide)]; omega,
      hA ⟨fun h => absurd h hX0, fun _ => trivial⟩⟩

/-- **Pop** of the top `v` of bucket `p = xP` (head in `xH`); then `xX = DEL[v]`,
`xY = CUR[v]`. -/
theorem popRead_run (hR : PRep g c₀ (numV g) s c) {p v : ℕ} {rest : List ℕ} (hp : p < numV g)
    (hvN : v < numV g) (hP : c.reg xP = p) (he : s.stk p = v :: rest)
    (hH : c.reg xH = c.mem (bBH g (c₀.reg rFREE) + p)) (hS : peelEnd g (c₀.reg rFREE) ≤ S)
    (hfr : c.reg rFREE ≤ S) :
    PRep g c₀ (numV g) { s with stk := Function.update s.stk p rest } (run popRead c) ∧
      (run popRead c).reg xV = v ∧ (run popRead c).reg xX = (if s.del v then 1 else 0) ∧
      (run popRead c).reg xY = s.cur v ∧
      (∀ r, r ≠ xV → r ≠ xQ → r ≠ xX → r ≠ xY → r ≠ rT → (run popRead c).reg r = c.reg r) ∧
      AddrOK S popRead c := by
  have hG := hR.glob
  have hF := peel_fits g (c₀.reg rFREE) hS
  have hLL := hR.mem.bh p hp
  rw [he] at hLL
  have hv : c.mem (c.mem (bBH g (c₀.reg rFREE) + p)) = v := hLL.2.2.1
  have hnode := hLL.2.1
  set c₁ := run (.seq (.load xV xH) (.seq (addc xQ xH 1) (.seq (.load xX xQ) (st gBH xP xX)))) c
    with hc₁
  have hA : AddrOK S popRead c := by
    addr_ok [popRead, hG.bh, hG.del, hG.cur, hP, hH, hv]
  have hR₁ : PRep g c₀ (numV g) { s with stk := Function.update s.stk p rest } c₁ := by
    refine ⟨(PGlob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_⟩
    have := hR.mem.pop hp he
    simpa +decide [hc₁, run_st, run_addc, hG.bh, hP, hH] using this
  have hV₁ : c₁.reg xV = v := by simp +decide [hc₁, run_st, run_addc, hH, hv]
  have hG₁ := hR₁.glob
  have hdel : c₁.mem (bDEL g (c₀.reg rFREE) + v) = if s.del v then 1 else 0 :=
    hR₁.mem.del.get hvN
  have hcur : c₁.mem (c₀.reg rFREE + v) = s.cur v := hR₁.mem.cur.get hvN
  have hrun : run popRead c = run (.seq (ld xX gDEL xV) (ld xY gCUR xV)) c₁ := by
    simp [popRead, hc₁]
  rw [hrun]
  refine ⟨(PRep.indep g c₀ (numV g) _).mono (W' := [xX, xY]) (by decide) c₁ _
    (agree_run (by decide) rfl rfl (by decide) c₁) hR₁, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, hA⟩
  · simp +decide [hV₁]
  · simp +decide [hV₁, hG₁.del, hdel]
  · simp +decide [hV₁, hG₁.cur, hG₁.del, hcur]
  · rw [run_reg_of_not_mem (by decide) (by simp [wregs, h3, h4]), hc₁,
      run_reg_of_not_mem (by decide) (by simp [wregs, h1, h2, h3, h5])]

/-- **Removal**, before the relaxation: mark `v = xV`, record its position `xS`, `xS += 1`,
`xA := OFF[v]`, `xB := OFF[v + 1]`. -/
theorem removeHead_run (hB : C4Base g c₀) (hR : PRep g c₀ (numV g) s c) {v : ℕ}
    (hv : v < numV g) (hvo : v ∉ s.ord) (hV : c.reg xV = v) (hS : c.reg xS = s.ord.length)
    (hSp : peelEnd g (c₀.reg rFREE) ≤ S) :
    PRep g c₀ (numV g) { s with del := Function.update s.del v true, ord := s.ord ++ [v] }
        (run removeHead c) ∧
      (run removeHead c).reg xS = s.ord.length + 1 ∧
      (run removeHead c).reg xA = R1.ps (idEdges g) v ∧
      (run removeHead c).reg xB = R1.ps (idEdges g) (v + 1) ∧
      (∀ r, r ≠ xS → r ≠ xA → r ≠ xB → r ≠ xQ → r ≠ rT → (run removeHead c).reg r = c.reg r) ∧
      AddrOK S removeHead c := by
  have hG := hR.glob
  have hF := peel_fits g (c₀.reg rFREE) hSp
  have hb := hB.bounds
  have hA : AddrOK S removeHead c := by
    addr_ok [removeHead, hG.del, hG.pos, hG.off, hV]
  set c₁ := run (.seq (st gDEL xV rONE) (.seq (st gPOS xV xS) (inc xS))) c with hc₁
  have hR₁ : PRep g c₀ (numV g)
      { s with del := Function.update s.del v true, ord := s.ord ++ [v] } c₁ := by
    refine ⟨(PGlob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_⟩
    have := hR.mem.removeHead hv hvo
    simpa +decide [hc₁, run_st, run_inc, hG.del, hG.pos, hG.one, hV, hS] using this
  have hG₁ := hR₁.glob
  have hS₁ := hR₁.mem.same
  have hV₁ : c₁.reg xV = v := by simp +decide [hc₁, run_st, run_inc, hV]
  have ho0 : c₁.mem (c₀.reg gOFF + v) = R1.ps (idEdges g) v := hB.offR hS₁ (by omega)
  have ho1 : c₁.mem (c₀.reg gOFF + (v + 1)) = R1.ps (idEdges g) (v + 1) := hB.offR hS₁ (by omega)
  have hrun : run removeHead c =
      run (.seq (ld xA gOFF xV) (.seq (addc xQ xV 1) (ld xB gOFF xQ))) c₁ := by
    simp [removeHead, hc₁]
  rw [hrun]
  refine ⟨(PRep.indep g c₀ (numV g) _).mono (W' := [xA, xQ, rT, xB]) (by decide) c₁ _
    (agree_run (by decide) rfl rfl (by decide) c₁) hR₁, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, hA⟩
  · simp +decide [run_addc, hc₁, run_st, run_inc, hS]
  · simp +decide [run_addc, hV₁, hG₁.off, ho0]
  · simp +decide [run_addc, hV₁, hG₁.off, ho1]
  · rw [run_reg_of_not_mem (by decide) (by simp [wregs, h2, h3, h4, h5]), hc₁,
      run_reg_of_not_mem (by decide) (by simp [wregs, h1, h5])]

end blocks

end STACS2027.Runtimes.C4
