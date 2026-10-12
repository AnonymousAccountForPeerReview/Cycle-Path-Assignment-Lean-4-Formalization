module

public import Outerplanar.RAM.BlockProg
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# The block solver: steps 1–5 (before the dispatch)

The state between steps 1 and 5 (`Rep`): the input registers (`Glob`), the layout registers
(`Lay`: with `F = c₀.reg rFREE` and `m = |E|`, the copies `CU`, `CV` at `F`, `F + m`, the
vertices `VS` at `F + 2m`, the local edges `LU`, `LV` at `F + 4m`, `F + 5m`, and
`rFREE = F + 6m`), the number of vertices found `gVN`, the output (unchanged), and the memory
(`BMem`): the five arrays, the scratch array `LOC` as a table, the memory below `F` outside
`LOC` unchanged, zero from `F + 6m` on. Every store is one of the update lemmas `BMem.upd_*`.

* `initB_spec`: the allocations;
* `copy_spec`: the copies of the edges (while `LOC` is still zero, so the memory below `F` is
  the initial one, `BMem.sameOn_zero`);
* `collect_spec`: the vertices `blockVerts (E.take j)` and `LOC = dictOf` of them
  (`blockVerts_take_succ`);
* `localE_spec`: the local edges `localEdges vs E` (`LOC[a] - 1 = vs.idxOf a`);
* `reset_spec`: `LOC` zero again.

All triples are `HTB S` triples (linear space): steps 1–5 allocate the six arrays of `6m` cells
at `F` and touch only them, the block's edges, `LOC` and the labels (all below `F`), so they run
below every bound `S ≥ F + 6m` (`hS`). The address obligations are `addr_ok` goals of the loop
bodies (`visit_addrOK` for the vertex visit).
-/

@[expose] public section

namespace STACS2027.RAM.Block

open STACS2027.Algo

variable {S : ℕ}

/-! ### Registers kept throughout -/

/-- The input registers, kept by the whole block solver. -/
@[mk_iff] structure Glob (c₀ c : Config) : Prop where
  zero : c.reg rZERO = 0
  one : c.reg rONE = 1
  n : c.reg gN = c₀.reg gN
  lb : c.reg gLB = c₀.reg gLB
  bl : c.reg gBL = c₀.reg gBL
  bs : c.reg gBS = c₀.reg gBS
  bu : c.reg gBU = c₀.reg gBU
  bv : c.reg gBV = c₀.reg gBV
  loc : c.reg gLOC = c₀.reg gLOC

theorem Glob.of_regs {c₀ c c' : Config} (h : Glob c₀ c)
    (hr : ∀ r, r < gVN → r ≠ rT → r ≠ rFREE → c'.reg r = c.reg r) : Glob c₀ c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨(hr _ (by decide) (by decide) (by decide)).trans h0,
    (hr _ (by decide) (by decide) (by decide)).trans h1,
    (hr _ (by decide) (by decide) (by decide)).trans h2,
    (hr _ (by decide) (by decide) (by decide)).trans h3,
    (hr _ (by decide) (by decide) (by decide)).trans h4,
    (hr _ (by decide) (by decide) (by decide)).trans h5,
    (hr _ (by decide) (by decide) (by decide)).trans h6,
    (hr _ (by decide) (by decide) (by decide)).trans h7,
    (hr _ (by decide) (by decide) (by decide)).trans h8⟩

/-- A register below `gVN`, other than `rT`, `rFREE`, is not written by a program with the
footprint of the block solver. -/
theorem not_mem_of_footprint {s : Stmt} (hW : ∀ r ∈ wregs s, r = rT ∨ r = rFREE ∨ gVN ≤ r)
    {r : ℕ} (h1 : r < gVN) (h2 : r ≠ rT) (h3 : r ≠ rFREE) : r ∉ wregs s := fun hr => by
  rcases hW r hr with h | h | h
  · exact h2 h
  · exact h3 h
  · exact absurd h1 (Nat.not_lt.mpr h)

theorem Glob.frame {s : Stmt} (hW : ∀ r ∈ wregs s, r = rT ∨ r = rFREE ∨ gVN ≤ r)
    {c₀ c c' : Config} (h : Glob c₀ c) (hfr : Frame s c c') : Glob c₀ c' :=
  h.of_regs fun _ h1 h2 h3 => hfr.reg _ (not_mem_of_footprint hW h1 h2 h3)

theorem Glob.run {s : Stmt} (hs : LoopFree s) (hW : ∀ r ∈ wregs s, r = rT ∨ r = rFREE ∨ gVN ≤ r)
    {c₀ c : Config} (h : Glob c₀ c) : Glob c₀ (RAM.run s c) :=
  h.frame hW (run_frame hs c)

/-- The scratch registers of steps 1–6. -/
abbrev W : List ℕ := [rT, rI, rA, rB, rU, rV, rX, rY, rC, rP, r2L]

theorem footprint_of_W {s : Stmt} (hW : ∀ r ∈ wregs s, r ∈ W) :
    ∀ r ∈ wregs s, r = rT ∨ r = rFREE ∨ gVN ≤ r := fun r hr => by
  have := hW r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- The layout registers of steps 1–5. -/
@[mk_iff] structure Lay (E : List Edge) (c₀ c : Config) : Prop where
  cu : c.reg gCU = c₀.reg rFREE
  cv : c.reg gCV = c₀.reg rFREE + E.length
  vs : c.reg gVS = c₀.reg rFREE + 2 * E.length
  lu : c.reg gLU = c₀.reg rFREE + 4 * E.length
  lv : c.reg gLV = c₀.reg rFREE + 5 * E.length
  ln : c.reg gLN = E.length
  free : c.reg rFREE = c₀.reg rFREE + 6 * E.length

/-! ### The memory of steps 1–5 -/

/-- The memory between steps 1 and 5: the copies `cu`, `cv`, the vertices `vs`, the local
edges `lu`, `lv`, the table `loc` in `LOC`, the rest below `F` unchanged, zero from `F + 6m`. -/
structure BMem (g : Graph) (E : List Edge) (c₀ : Config) (cu cv vs : List ℕ) (loc : ℕ → ℕ)
    (lu lv : List ℕ) (m : ℕ → ℕ) : Prop where
  mcu : Arr m (c₀.reg rFREE) cu
  mcv : Arr m (c₀.reg rFREE + E.length) cv
  mvs : Arr m (c₀.reg rFREE + 2 * E.length) vs
  mlu : Arr m (c₀.reg rFREE + 4 * E.length) lu
  mlv : Arr m (c₀.reg rFREE + 5 * E.length) lv
  mloc : Tab m (c₀.reg gLOC) (numV g) loc
  frame : SameOn (fun a => a < c₀.reg rFREE ∧ ¬ (c₀.reg gLOC ≤ a ∧ a < c₀.reg gLOC + numV g))
    c₀.mem m
  zero : ZeroFrom m (c₀.reg rFREE + 6 * E.length)
  lcu : cu.length ≤ E.length
  lcv : cv.length ≤ E.length
  lvs : vs.length ≤ 2 * E.length
  llu : lu.length ≤ E.length
  llv : lv.length ≤ E.length

section BMem

variable {g : Graph} {E : List Edge} {c₀ : Config} {cu cv vs lu lv : List ℕ} {loc : ℕ → ℕ}
  {m : ℕ → ℕ}

theorem BMem.upd_cu (h : BMem g E c₀ cu cv vs loc lu lv m)
    (hloc : c₀.reg gLOC + numV g ≤ c₀.reg rFREE) (hlen : cu.length < E.length) {a : ℕ}
    (ha : a = c₀.reg rFREE + cu.length) (x : ℕ) :
    BMem g E c₀ (cu ++ [x]) cv vs loc lu lv (upd m a x) := by
  obtain ⟨hcu, hcv, hvs, hlu, hlv, hl, hf, hz, l1, l2, l3, l4, l5⟩ := h
  exact ⟨hcu.upd_snoc ha, hcv.upd_of_disjoint (by omega), hvs.upd_of_disjoint (by omega),
    hlu.upd_of_disjoint (by omega), hlv.upd_of_disjoint (by omega), hl.upd_of_disjoint (by omega),
    hf.upd (fun h' => absurd h'.1 (by omega)), hz.upd (by omega), by simp; omega, l2, l3, l4, l5⟩

theorem BMem.upd_cv (h : BMem g E c₀ cu cv vs loc lu lv m)
    (hloc : c₀.reg gLOC + numV g ≤ c₀.reg rFREE) (hlen : cv.length < E.length) {a : ℕ}
    (ha : a = c₀.reg rFREE + E.length + cv.length) (x : ℕ) :
    BMem g E c₀ cu (cv ++ [x]) vs loc lu lv (upd m a x) := by
  obtain ⟨hcu, hcv, hvs, hlu, hlv, hl, hf, hz, l1, l2, l3, l4, l5⟩ := h
  exact ⟨hcu.upd_of_disjoint (by omega), hcv.upd_snoc ha, hvs.upd_of_disjoint (by omega),
    hlu.upd_of_disjoint (by omega), hlv.upd_of_disjoint (by omega), hl.upd_of_disjoint (by omega),
    hf.upd (fun h' => absurd h'.1 (by omega)), hz.upd (by omega), l1, by simp; omega, l3, l4, l5⟩

theorem BMem.upd_vs (h : BMem g E c₀ cu cv vs loc lu lv m)
    (hloc : c₀.reg gLOC + numV g ≤ c₀.reg rFREE) (hlen : vs.length < 2 * E.length) {a : ℕ}
    (ha : a = c₀.reg rFREE + 2 * E.length + vs.length) (x : ℕ) :
    BMem g E c₀ cu cv (vs ++ [x]) loc lu lv (upd m a x) := by
  obtain ⟨hcu, hcv, hvs, hlu, hlv, hl, hf, hz, l1, l2, l3, l4, l5⟩ := h
  exact ⟨hcu.upd_of_disjoint (by omega), hcv.upd_of_disjoint (by omega), hvs.upd_snoc ha,
    hlu.upd_of_disjoint (by omega), hlv.upd_of_disjoint (by omega), hl.upd_of_disjoint (by omega),
    hf.upd (fun h' => absurd h'.1 (by omega)), hz.upd (by omega), l1, l2, by simp; omega, l4, l5⟩

theorem BMem.upd_lu (h : BMem g E c₀ cu cv vs loc lu lv m)
    (hloc : c₀.reg gLOC + numV g ≤ c₀.reg rFREE) (hlen : lu.length < E.length) {a : ℕ}
    (ha : a = c₀.reg rFREE + 4 * E.length + lu.length) (x : ℕ) :
    BMem g E c₀ cu cv vs loc (lu ++ [x]) lv (upd m a x) := by
  obtain ⟨hcu, hcv, hvs, hlu, hlv, hl, hf, hz, l1, l2, l3, l4, l5⟩ := h
  exact ⟨hcu.upd_of_disjoint (by omega), hcv.upd_of_disjoint (by omega),
    hvs.upd_of_disjoint (by omega), hlu.upd_snoc ha, hlv.upd_of_disjoint (by omega),
    hl.upd_of_disjoint (by omega), hf.upd (fun h' => absurd h'.1 (by omega)), hz.upd (by omega),
    l1, l2, l3, by simp; omega, l5⟩

theorem BMem.upd_lv (h : BMem g E c₀ cu cv vs loc lu lv m)
    (hloc : c₀.reg gLOC + numV g ≤ c₀.reg rFREE) (hlen : lv.length < E.length) {a : ℕ}
    (ha : a = c₀.reg rFREE + 5 * E.length + lv.length) (x : ℕ) :
    BMem g E c₀ cu cv vs loc lu (lv ++ [x]) (upd m a x) := by
  obtain ⟨hcu, hcv, hvs, hlu, hlv, hl, hf, hz, l1, l2, l3, l4, l5⟩ := h
  exact ⟨hcu.upd_of_disjoint (by omega), hcv.upd_of_disjoint (by omega),
    hvs.upd_of_disjoint (by omega), hlu.upd_of_disjoint (by omega), hlv.upd_snoc ha,
    hl.upd_of_disjoint (by omega), hf.upd (fun h' => absurd h'.1 (by omega)), hz.upd (by omega),
    l1, l2, l3, l4, by simp; omega⟩

theorem BMem.upd_loc (h : BMem g E c₀ cu cv vs loc lu lv m)
    (hloc : c₀.reg gLOC + numV g ≤ c₀.reg rFREE) {i : ℕ} (hi : i < numV g) {a : ℕ}
    (ha : a = c₀.reg gLOC + i) (x : ℕ) :
    BMem g E c₀ cu cv vs (Function.update loc i x) lu lv (upd m a x) := by
  obtain ⟨hcu, hcv, hvs, hlu, hlv, hl, hf, hz, l1, l2, l3, l4, l5⟩ := h
  exact ⟨hcu.upd_of_disjoint (by omega), hcv.upd_of_disjoint (by omega),
    hvs.upd_of_disjoint (by omega), hlu.upd_of_disjoint (by omega),
    hlv.upd_of_disjoint (by omega), hl.upd ha, hf.upd (fun h' => h'.2 ⟨by omega, by omega⟩),
    hz.upd (by omega), l1, l2, l3, l4, l5⟩

/-- With `LOC` zero, the memory below `F` is the initial one. -/
theorem BMem.sameOn_zero (h : BMem g E c₀ cu cv vs (fun _ => 0) lu lv m)
    (hz : Arr c₀.mem (c₀.reg gLOC) (List.replicate (numV g) 0)) :
    SameOn (· < c₀.reg rFREE) c₀.mem m := by
  intro a ha
  by_cases hin : c₀.reg gLOC ≤ a ∧ a < c₀.reg gLOC + numV g
  · have h1 := h.mloc.get' (i := a - c₀.reg gLOC) (a := a) (by omega) (by omega)
    have h2 := (arr_replicate.mp hz) (a - c₀.reg gLOC) (by omega)
    rw [show c₀.reg gLOC + (a - c₀.reg gLOC) = a by omega] at h2
    rw [h1, h2]
  · exact h.frame a ⟨ha, hin⟩

end BMem

/-! ### The state of steps 1–5 -/

/-- The state between steps 1 and 5. -/
@[mk_iff] structure Rep (g : Graph) (E : List Edge) (c₀ : Config) (cu cv vs : List ℕ)
    (loc : ℕ → ℕ) (lu lv : List ℕ) (c : Config) : Prop where
  glob : Glob c₀ c
  lay : Lay E c₀ c
  vn : c.reg gVN = vs.length
  out : c.out = c₀.out
  mem : BMem g E c₀ cu cv vs loc lu lv c.mem

theorem Rep.indep (g : Graph) (E : List Edge) (c₀ : Config) (cu cv vs : List ℕ) (loc : ℕ → ℕ)
    (lu lv : List ℕ) : Indep W (Rep g E c₀ cu cv vs loc lu lv) := by
  indep [rep_iff, glob_iff, lay_iff]

/-- A loop-free block writing scratch registers and possibly `gVN`, with a new memory. -/
theorem Rep.run_of' {g : Graph} {E : List Edge} {c₀ : Config} {cu cv vs lu lv : List ℕ}
    {loc : ℕ → ℕ} {s : Stmt} (hs : LoopFree s) (hW : ∀ r ∈ wregs s, r ∈ gVN :: W)
    (hw : writes s = false) {c : Config} (hR : Rep g E c₀ cu cv vs loc lu lv c)
    {cu' cv' vs' lu' lv' : List ℕ} {loc' : ℕ → ℕ} (hvn : (RAM.run s c).reg gVN = vs'.length)
    (hm : BMem g E c₀ cu' cv' vs' loc' lu' lv' (RAM.run s c).mem) :
    Rep g E c₀ cu' cv' vs' loc' lu' lv' (RAM.run s c) := by
  have hr : ∀ r, r ∉ gVN :: W → (RAM.run s c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem hs (fun h => hr (hW r h)) c
  have hW' : ∀ r ∈ wregs s, r = rT ∨ r = rFREE ∨ gVN ≤ r := fun r hr' => by
    have := hW r hr'
    simp only [W, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hR.lay
  refine ⟨hR.glob.run hs hW', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hvn, ?_, hm⟩
  · rw [hr _ (by decide), h1]
  · rw [hr _ (by decide), h2]
  · rw [hr _ (by decide), h3]
  · rw [hr _ (by decide), h4]
  · rw [hr _ (by decide), h5]
  · rw [hr _ (by decide), h6]
  · rw [hr _ (by decide), h7]
  · rw [run_out_of_writes hs hw, hR.out]

/-- A loop-free block writing scratch registers only, with a new memory. -/
theorem Rep.run_of {g : Graph} {E : List Edge} {c₀ : Config} {cu cv vs lu lv : List ℕ}
    {loc : ℕ → ℕ} {s : Stmt} (hs : LoopFree s) (hW : ∀ r ∈ wregs s, r ∈ W)
    (hw : writes s = false) {c : Config} (hR : Rep g E c₀ cu cv vs loc lu lv c)
    {cu' cv' vs' lu' lv' : List ℕ} {loc' : ℕ → ℕ} (hvs : vs'.length = vs.length)
    (hm : BMem g E c₀ cu' cv' vs' loc' lu' lv' (RAM.run s c).mem) :
    Rep g E c₀ cu' cv' vs' loc' lu' lv' (RAM.run s c) :=
  hR.run_of' hs (fun r hr => List.mem_cons_of_mem _ (hW r hr)) hw
    (by rw [run_reg_of_not_mem hs (fun h => by have := hW _ h; simp at this) c, hR.vn, hvs]) hm

/-! ### Step 1: the allocations -/

theorem Glob.init {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀) : Glob c₀ c₀ :=
  ⟨hB.zero, hB.one, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem initB_footprint : ∀ r ∈ wregs initB, r = rT ∨ r = rFREE ∨ gVN ≤ r := by decide

theorem initB_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀) :
    HTB S initB (fun c => BlockIn g E c ∧ c = c₀)
      (fun c => Rep g E c₀ [] [] [] (fun _ => 0) [] [] c ∧ c.reg gBL = E.length) 20 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨_, hc⟩ => ⟨AddrOK.of_memFree rfl, ?_⟩
  subst hc
  have hbl := hB.bl
  have hloc := hB.loc
  have hfree := hB.free
  refine ⟨⟨(Glob.init hB).run (by decide) initB_footprint, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp +decide [lay_iff, initB, run_alloc, run_mov, hbl]
    omega
  · simp +decide [initB, run_alloc, run_mov]
  · rw [run_out_of_writes (by decide) (by decide)]
  · rw [run_mem_of_stores (by decide) (by decide)]
    refine ⟨arr_nil _ _, arr_nil _ _, arr_nil _ _, arr_nil _ _, arr_nil _ _,
      fun i hi => (arr_replicate.mp hloc) i hi, SameOn.refl _ _, hfree.mono (by omega),
      by simp, by simp, by simp, by simp, by simp⟩
  · simp +decide [initB, run_alloc, run_mov, hbl]

/-! ### Step 2: the copies -/

/-- The edges, read from the initial memory. -/
theorem edge_read {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀) {m : ℕ → ℕ}
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {j : ℕ} (hj : j < E.length) :
    m (c₀.reg gBU + (c₀.reg gBS + j)) = E[j].1 ∧ m (c₀.reg gBV + (c₀.reg gBS + j)) = E[j].2 := by
  have hb := hB.below
  constructor
  · rw [hS _ (show _ < c₀.reg rFREE by omega), hB.bu.get' (i := j) (by simpa using hj) (by omega)]
    simp
  · rw [hS _ (show _ < c₀.reg rFREE by omega), hB.bv.get' (i := j) (by simpa using hj) (by omega)]
    simp

theorem copyBody_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hS : c₀.reg rFREE + 6 * E.length ≤ S) (j : ℕ) (hj : j < E.length) :
    HTB S copyBody
      (fun c => Rep g E c₀ ((E.take j).map Prod.fst) ((E.take j).map Prod.snd) [] (fun _ => 0) [] []
        c ∧ c.reg rI = j ∧ c.reg gBL = E.length)
      (fun c => Rep g E c₀ ((E.take (j + 1)).map Prod.fst) ((E.take (j + 1)).map Prod.snd) []
        (fun _ => 0) [] [] c ∧ c.reg rI = j ∧ c.reg gBL = E.length) 9 := by
  refine HTB.of_HT_addrOK (by decide) (fun c ⟨hR, hi, _⟩ => by
    have hb := hB.below
    addr_ok [copyBody, hR.glob.bs, hR.glob.bu, hR.glob.bv, hR.lay.cu, hR.lay.cv, hi]) ?_
  refine HT.run_le (by decide) (by decide) fun c ⟨hR, hi, hn⟩ => ?_
  have hb := hB.below
  obtain ⟨hu, hv⟩ := edge_read hB (hR.mem.sameOn_zero hB.loc) hj
  have hne : c₀.reg gBV + (c₀.reg gBS + j) ≠ c₀.reg rFREE + j := by omega
  have hmem : (RAM.run copyBody c).mem = upd (upd c.mem (c₀.reg rFREE + j) E[j].1)
      (c₀.reg rFREE + E.length + j) E[j].2 := by
    simp +decide only [copyBody, run_seq', run_add, run_ld, run_st (show rA ≠ rT by decide),
      setReg_reg, setReg_mem, setMem_mem_upd, setMem_reg, ↓reduceIte, hR.glob.bs, hR.glob.bu,
      hR.glob.bv, hR.lay.cu, hR.lay.cv, hi, hu, upd_apply, hne, hv]
  refine ⟨hR.run_of (by decide) (by decide) (by decide) rfl ?_,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hi,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hn⟩
  rw [hmem, map_take_succ _ _ hj, map_take_succ _ _ hj]
  exact (hR.mem.upd_cu hb.2.2.2 (by simp; omega) (by simp; omega) _).upd_cv hb.2.2.2
    (by simp; omega) (by simp; omega) _

/-- **Step 2**: the copies. -/
theorem copy_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hS : c₀.reg rFREE + 6 * E.length ≤ S) :
    HTB S copy (fun c => Rep g E c₀ [] [] [] (fun _ => 0) [] [] c ∧ c.reg gBL = E.length)
      (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) [] (fun _ => 0) [] [] c ∧
        c.reg gBL = E.length) (E.length * 13 + 3) := by
  have hl := HTB.forUpC (i := rI) (n := gBL) (N := E.length) (body := copyBody)
    (fun j => Rep g E c₀ ((E.take j).map Prod.fst) ((E.take j).map Prod.snd) [] (fun _ => 0) [] [])
    9 (by decide) (by decide) (by decide) (fun j => (Rep.indep _ _ _ _ _ _ _ _ _).mono (by decide))
    (fun j hj => copyBody_spec hB hS j hj)
  refine hl.mono (fun c ⟨h, h'⟩ => ⟨by simpa using h, h'⟩) (fun c ⟨h, _, h'⟩ => ⟨by simpa using h, h'⟩)
    (by omega)

/-! ### Step 3: the vertices -/

theorem loopFree_visit (x : ℕ) : LoopFree (visit x) :=
  ⟨loopFree_ld _ _ _, ⟨loopFree_st _ _ _, loopFree_inc _, loopFree_st _ _ _⟩, trivial⟩

theorem wregs_visit (x : ℕ) : wregs (visit x) = [rY, rY, rT, rT, gVN, rT] := rfl

theorem visit_wregs (x : ℕ) : ∀ r ∈ wregs (visit x), r ∈ gVN :: W := by
  rw [wregs_visit]; decide

/-- **Visiting a vertex** `a` (in register `x`): the vertices grow by `R0.ext`. -/
theorem visit_run {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀) {x : ℕ}
    (hx : x = rA ∨ x = rB) {cu cv V : List ℕ} {c : Config}
    (hR : Rep g E c₀ cu cv V (R0.dictOf V) [] [] c) {a : ℕ} (ha : c.reg x = a) (han : a < numV g)
    (hlen : (R0.ext V a).length ≤ 2 * E.length) :
    Rep g E c₀ cu cv (R0.ext V a) (R0.dictOf (R0.ext V a)) [] [] (RAM.run (visit x) c) := by
  have hloc := hB.below.2.2.2
  have hy : c.mem (c₀.reg gLOC + a) = R0.dictOf V a := hR.mem.mloc.get han
  have hgl := hR.glob.loc
  have hvsr := hR.lay.vs
  have hvn := hR.vn
  have hxs : x ≠ rT ∧ x ≠ rY ∧ x ≠ gVN := by rcases hx with rfl | rfl <;> decide
  obtain ⟨hxT, hxY, hxN⟩ := hxs
  by_cases haV : a ∈ V
  · have h0 : R0.dictOf V a ≠ 0 := fun h => R0.dictOf_eq_zero_iff.mp h haV
    have hrun : RAM.run (visit x) c = c.setReg rY (R0.dictOf V a) := by
      simp +decide only [visit, run_seq', run_ld, run_ifz', setReg_reg, ↓reduceIte,
        hgl, ha, hy, h0, run_skip]
    rw [hrun, R0.ext_of_mem haV]
    exact (Rep.indep _ _ _ _ _ _ _ _ _).setReg (by decide) _ hR
  · have h0 : R0.dictOf V a = 0 := R0.dictOf_eq_zero_iff.mpr haV
    rw [R0.ext_of_not_mem haV] at hlen ⊢
    rw [R0.dictOf_snoc haV]
    simp only [List.length_append, List.length_singleton] at hlen
    refine hR.run_of' (loopFree_visit x) (visit_wregs x) rfl ?_ ?_
    · simp +decide [visit, run_st, run_inc, hgl, ha, hy, h0, hvn, hxT, hxY, hxN]
    · have hmem : (RAM.run (visit x) c).mem = upd (upd c.mem
          (c₀.reg rFREE + 2 * E.length + V.length) a) (c₀.reg gLOC + a) (V.length + 1) := by
        simp +decide [visit, run_st, run_inc, hgl, ha, hy, h0, hvn, hvsr, hxT, hxY, hxN]
      rw [hmem]
      exact (hR.mem.upd_vs hloc (by omega) rfl a).upd_loc hloc han rfl _

/-- The addresses of a vertex visit: `LOC[a]` and, for a new vertex, the next cell of `VS`. -/
theorem visit_addrOK {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀) {x : ℕ}
    (hx : x = rA ∨ x = rB) {cu cv V : List ℕ} {c : Config}
    (hR : Rep g E c₀ cu cv V (R0.dictOf V) [] [] c) {a : ℕ} (ha : c.reg x = a) (han : a < numV g)
    (hlen : (R0.ext V a).length ≤ 2 * E.length) (hS : c₀.reg rFREE + 6 * E.length ≤ S) :
    AddrOK S (visit x) c := by
  have hy : c.mem (c₀.reg gLOC + a) = R0.dictOf V a := hR.mem.mloc.get han
  have hV : R0.dictOf V a = 0 → V.length + 1 ≤ 2 * E.length := fun h => by
    rw [R0.ext_of_not_mem (R0.dictOf_eq_zero_iff.mp h)] at hlen; simpa using hlen
  have hloc := hB.below.2.2.2
  have hgl := hR.glob.loc
  have hvsr := hR.lay.vs
  have hvn := hR.vn
  rcases hx with rfl | rfl <;> addr_ok [visit, hgl, hvsr, hvn, ha, hy]

theorem collBody_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hS : c₀.reg rFREE + 6 * E.length ≤ S) (j : ℕ)
    (hj : j < E.length) :
    HTB S collBody
      (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts (E.take j))
        (R0.dictOf (blockVerts (E.take j))) [] [] c ∧ c.reg rI = j ∧ c.reg gBL = E.length)
      (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts (E.take (j + 1)))
        (R0.dictOf (blockVerts (E.take (j + 1)))) [] [] c ∧ c.reg rI = j ∧
        c.reg gBL = E.length) 24 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hi, hn⟩ => ?_
  have hu : c.mem (c.reg gCU + c.reg rI) = E[j].1 := by
    rw [hR.lay.cu, hi, hR.mem.mcu.get (by simpa using hj)]; simp
  have hv : c.mem (c.reg gCV + c.reg rI) = E[j].2 := by
    rw [hR.lay.cv, hi, hR.mem.mcv.get (by simpa using hj)]; simp
  have hEj := hE E[j] (List.getElem_mem hj)
  have hlen := length_blockVerts_take_le E (j + 1)
  rw [blockVerts_take_succ E hj] at hlen ⊢
  have hlen1 := R0.length_le_ext (R0.ext (blockVerts (E.take j)) E[j].1) E[j].2
  have hcu := hR.lay.cu
  have hcv := hR.lay.cv
  simp only [collBody, run_seq', run_ld, addrOK_seq, addrOK_ld]
  have hR1 := (Rep.indep _ _ _ _ _ _ _ _ _).setReg (d := rB) (by decide) (c.mem (c.reg gCV + c.reg rI))
    ((Rep.indep _ _ _ _ _ _ _ _ _).setReg (d := rA) (by decide) (c.mem (c.reg gCU + c.reg rI)) hR)
  have hra : ((c.setReg rA (c.mem (c.reg gCU + c.reg rI))).setReg rB
      (c.mem (c.reg gCV + c.reg rI))).reg rA = E[j].1 := by simp +decide [hu]
  have h3 := visit_run hB (Or.inl rfl) hR1 hra (by omega) (by omega)
  have hrb : (RAM.run (visit rA) ((c.setReg rA (c.mem (c.reg gCU + c.reg rI))).setReg rB
      (c.mem (c.reg gCV + c.reg rI)))).reg rB = E[j].2 := by
    rw [run_reg_of_not_mem (loopFree_visit _) (by decide)]; simp +decide [hv]
  have h4 := visit_run hB (Or.inr rfl) h3 hrb hEj.2 (by omega)
  refine ⟨⟨by omega, by simp +decide only [setReg_reg, ↓reduceIte]; omega,
    visit_addrOK hB (Or.inl rfl) hR1 hra (by omega) (by omega) hS,
    visit_addrOK hB (Or.inr rfl) h3 hrb hEj.2 (by omega) hS⟩, h4, ?_, ?_⟩
  · rw [run_reg_of_not_mem (loopFree_visit _) (by decide),
      run_reg_of_not_mem (loopFree_visit _) (by decide)]
    simp +decide [hi]
  · rw [run_reg_of_not_mem (loopFree_visit _) (by decide),
      run_reg_of_not_mem (loopFree_visit _) (by decide)]
    simp +decide [hn]

/-- **Step 3**: the vertices `blockVerts E` and `LOC = dictOf` of them. -/
theorem collect_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hS : c₀.reg rFREE + 6 * E.length ≤ S) :
    HTB S collect (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) [] (fun _ => 0) [] [] c ∧
        c.reg gBL = E.length)
      (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E)
        (R0.dictOf (blockVerts E)) [] [] c ∧ c.reg gBL = E.length) (E.length * 28 + 3) := by
  have hl := HTB.forUpC (i := rI) (n := gBL) (N := E.length) (body := collBody)
    (fun j => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts (E.take j))
      (R0.dictOf (blockVerts (E.take j))) [] [])
    24 (by decide) (by decide) (by decide) (fun j => (Rep.indep _ _ _ _ _ _ _ _ _).mono (by decide))
    (fun j hj => collBody_spec hB hE hS j hj)
  refine hl.mono (fun c ⟨h, h'⟩ => ⟨?_, h'⟩) (fun c ⟨h, _, h'⟩ => ⟨by simpa using h, h'⟩) le_rfl
  have he : blockVerts (E.take 0) = [] := by simp [blockVerts]
  rw [he, R0.dictOf_nil]
  exact h

/-! ### Step 4: the local edges -/

/-- `order` puts the smaller of `rU`, `rV` first. -/
theorem order_run (c : Config) :
    (RAM.run order c).reg rU = (edge (c.reg rU) (c.reg rV)).1 ∧
      (RAM.run order c).reg rV = (edge (c.reg rU) (c.reg rV)).2 ∧
      Agree [rT, rU, rV] c (RAM.run order c) := by
  refine ⟨?_, ?_, agree_run (by decide) rfl rfl (by decide) c⟩
  all_goals
    simp only [order, run_ifLt, run_swap (show rU ≠ rV by decide), run_skip, edge]
    split_ifs with h <;> simp +decide <;> omega

/-- The local graph of the block. -/
abbrev locG (E : List Edge) : List Edge := localEdges (blockVerts E) E

theorem locBody_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hS : c₀.reg rFREE + 6 * E.length ≤ S) (j : ℕ)
    (hj : j < E.length) :
    HTB S locBody
      (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E)
        (R0.dictOf (blockVerts E)) (((locG E).take j).map Prod.fst)
        (((locG E).take j).map Prod.snd) c ∧ c.reg rI = j ∧ c.reg gBL = E.length)
      (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E)
        (R0.dictOf (blockVerts E)) (((locG E).take (j + 1)).map Prod.fst)
        (((locG E).take (j + 1)).map Prod.snd) c ∧ c.reg rI = j ∧ c.reg gBL = E.length) 22 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hi, hn⟩ => ?_
  have hloc := hB.below.2.2.2
  have hu : c.mem (c.reg gCU + c.reg rI) = E[j].1 := by
    rw [hR.lay.cu, hi, hR.mem.mcu.get (by simpa using hj)]; simp
  have hv : c.mem (c.reg gCV + c.reg rI) = E[j].2 := by
    rw [hR.lay.cv, hi, hR.mem.mcv.get (by simpa using hj)]; simp
  have hEj := hE E[j] (List.getElem_mem hj)
  have hA : AddrOK S locBody c := by
    have hu' : c.mem (c₀.reg rFREE + j) = E[j].1 := by rw [← hu, hR.lay.cu, hi]
    have hv' : c.mem (c₀.reg rFREE + E.length + j) = E[j].2 := by rw [← hv, hR.lay.cv, hi]
    addr_ok [locBody, locRead, order, hR.lay.cu, hR.lay.cv, hR.glob.loc, hR.lay.lu, hR.lay.lv,
      hi, hu', hv']
  refine ⟨hA, ?_⟩
  have hm := ends_mem_blockVerts E[j] (List.getElem_mem hj)
  have hla : c.mem (c.reg gLOC + E[j].1) = (blockVerts E).idxOf E[j].1 + 1 := by
    rw [hR.glob.loc, hR.mem.mloc.get (by omega), dictOf_of_mem hm.1]
  have hlb : c.mem (c.reg gLOC + E[j].2) = (blockVerts E).idxOf E[j].2 + 1 := by
    rw [hR.glob.loc, hR.mem.mloc.get (by omega), dictOf_of_mem hm.2]
  have hr6 : (RAM.run locRead c).reg rU = (blockVerts E).idxOf E[j].1 ∧
      (RAM.run locRead c).reg rV = (blockVerts E).idxOf E[j].2 := by
    constructor <;> simp +decide [locRead, run_dec, hu, hv, hla, hlb]
  have hag6 : Agree W c (RAM.run locRead c) := agree_run (by decide) rfl rfl (by decide) c
  obtain ⟨h7u, h7v, hag7⟩ := order_run (RAM.run locRead c)
  rw [hr6.1, hr6.2] at h7u h7v
  have hag := hag6.trans (hag7.mono (by decide))
  have hjL : j < (locG E).length := by simpa [length_localEdges] using hj
  have hri : (RAM.run order (RAM.run locRead c)).reg rI = j := by
    rw [run_reg_of_not_mem (by decide) (by decide), run_reg_of_not_mem (by decide) (by decide), hi]
  have hmem : (RAM.run locBody c).mem = upd (upd c.mem (c₀.reg rFREE + 4 * E.length + j)
      ((locG E)[j]).1) (c₀.reg rFREE + 5 * E.length + j) ((locG E)[j]).2 := by
    rw [getElem_localEdges]
    simp +decide only [locBody, run_seq', run_st (show rU ≠ rT by decide),
      run_st (show rV ≠ rT by decide), setReg_mem, setMem_mem_upd, setReg_reg, setMem_reg,
      ↓reduceIte, h7u, h7v, hag.mem, hag.reg gLU (by decide), hag.reg gLV (by decide),
      hri, hR.lay.lu, hR.lay.lv]
  refine ⟨hR.run_of (by decide) (by decide) (by decide) rfl ?_,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hi,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hn⟩
  rw [hmem, map_take_succ _ _ hjL, map_take_succ _ _ hjL]
  exact (hR.mem.upd_lu hloc (by simp; omega) (by simp; omega) _).upd_lv hloc (by simp; omega)
    (by simp; omega) _

/-- **Step 4**: the local edges. -/
theorem localE_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hS : c₀.reg rFREE + 6 * E.length ≤ S) :
    HTB S localE (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E)
        (R0.dictOf (blockVerts E)) [] [] c ∧ c.reg gBL = E.length)
      (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E)
        (R0.dictOf (blockVerts E)) ((locG E).map Prod.fst) ((locG E).map Prod.snd) c)
      (E.length * 26 + 3) := by
  have hl := HTB.forUpC (i := rI) (n := gBL) (N := E.length) (body := locBody)
    (fun j => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E)
      (R0.dictOf (blockVerts E)) (((locG E).take j).map Prod.fst) (((locG E).take j).map Prod.snd))
    22 (by decide) (by decide) (by decide) (fun j => (Rep.indep _ _ _ _ _ _ _ _ _).mono (by decide))
    (fun j hj => locBody_spec hB hE hS j hj)
  have hlen : (locG E).length = E.length := length_localEdges _ _
  refine hl.mono (fun c ⟨h, h'⟩ => ⟨by simpa using h, h'⟩) (fun c ⟨h, _⟩ => ?_) le_rfl
  rw [← hlen, List.take_length] at h
  exact h

/-! ### Step 5: the reset -/

/-- `LOC` after the reset of the first `j` vertices. -/
def resF (vs : List ℕ) (j : ℕ) (x : ℕ) : ℕ := if x ∈ vs.take j then 0 else R0.dictOf vs x

theorem resF_zero (vs : List ℕ) : resF vs 0 = R0.dictOf vs := by
  funext x; simp [resF]

theorem resF_length (vs : List ℕ) : resF vs vs.length = fun _ => 0 := by
  funext x
  simp only [resF, List.take_length]
  split_ifs with h
  · rfl
  · exact R0.dictOf_eq_zero_iff.mpr h

theorem resF_succ (vs : List ℕ) {j : ℕ} (hj : j < vs.length) :
    resF vs (j + 1) = Function.update (resF vs j) vs[j] 0 := by
  funext x
  have hmem : x ∈ vs.take (j + 1) ↔ x ∈ vs.take j ∨ x = vs[j] := by
    rw [take_succ_eq vs hj, List.mem_append, List.mem_singleton]
  simp only [resF, Function.update_apply, hmem]
  by_cases hx : x = vs[j]
  · simp only [hx, or_true, ↓reduceIte]
  · simp only [hx, or_false, ↓reduceIte]

theorem resBody_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hS : c₀.reg rFREE + 6 * E.length ≤ S) (j : ℕ)
    (hj : j < (blockVerts E).length) :
    HTB S resBody
      (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E) (resF (blockVerts E) j)
        ((locG E).map Prod.fst) ((locG E).map Prod.snd) c ∧ c.reg rI = j ∧
        c.reg gVN = (blockVerts E).length)
      (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E)
        (resF (blockVerts E) (j + 1)) ((locG E).map Prod.fst) ((locG E).map Prod.snd) c ∧
        c.reg rI = j ∧ c.reg gVN = (blockVerts E).length) 4 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hi, hn⟩ => ?_
  have hloc := hB.below.2.2.2
  have hx : c.mem (c.reg gVS + c.reg rI) = (blockVerts E)[j] := by
    rw [hR.lay.vs, hi, hR.mem.mvs.get hj]
  have hlt := lt_of_mem_blockVerts hE (List.getElem_mem hj)
  have hN := length_blockVerts_le E
  have hA : AddrOK S resBody c := by
    have hx' : c.mem (c₀.reg rFREE + 2 * E.length + j) = (blockVerts E)[j] := by
      rw [← hx, hR.lay.vs, hi]
    addr_ok [resBody, hR.lay.vs, hR.glob.loc, hi, hx']
  have hmem : (RAM.run resBody c).mem = upd c.mem (c₀.reg gLOC + (blockVerts E)[j]) 0 := by
    simp +decide only [resBody, run_seq', run_ld, run_st (show rZERO ≠ rT by decide), setReg_mem,
      setMem_mem_upd, setReg_reg, ↓reduceIte, hx, hR.glob.loc, hR.glob.zero]
  refine ⟨hA, hR.run_of (by decide) (by decide) (by decide) rfl ?_,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hi,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hn⟩
  rw [hmem, resF_succ _ hj]
  exact hR.mem.upd_loc hloc hlt rfl 0

/-- **Step 5**: `LOC` is zero again. -/
theorem reset_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hS : c₀.reg rFREE + 6 * E.length ≤ S) :
    HTB S reset (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E)
        (R0.dictOf (blockVerts E)) ((locG E).map Prod.fst) ((locG E).map Prod.snd) c)
      (fun c => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E) (fun _ => 0)
        ((locG E).map Prod.fst) ((locG E).map Prod.snd) c)
      ((blockVerts E).length * 8 + 3) := by
  have hl := HTB.forUpC (i := rI) (n := gVN) (N := (blockVerts E).length) (body := resBody)
    (fun j => Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E) (resF (blockVerts E) j)
      ((locG E).map Prod.fst) ((locG E).map Prod.snd))
    4 (by decide) (by decide) (by decide) (fun j => (Rep.indep _ _ _ _ _ _ _ _ _).mono (by decide))
    (fun j hj => resBody_spec hB hE hS j hj)
  refine hl.mono (fun c h => ⟨?_, h.vn⟩) (fun c ⟨h, _⟩ => ?_) le_rfl
  · rw [resF_zero]; exact h
  · rw [resF_length] at h; exact h

end STACS2027.RAM.Block
