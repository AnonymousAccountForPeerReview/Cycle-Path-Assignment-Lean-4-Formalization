module

public import Outerplanar.RAM.R1Prog
import Mathlib.Tactic

/-!
# Phase R1: the depth-first search (step 5)

The machine simulates `DFS.step` for the neighbour lists `nbOf E` (`E = idEdges g`) and the
root candidates `List.range N`, one step per round of the loop `whileC dfsCond dfsBody`.

* Representation (`DfsRep g c₀ s c`): the arrays `PRE`, `PAR`, `PTR` hold `s.pre`, `s.par`,
  `s.ptr` on `[0, N)`, `ORD` holds `s.ord`, `STK` holds `s.stk` reversed (top last) with
  `gSP = |s.stk|`, `gCNT = s.cnt`, and the root candidates are `s.rs = [r, N)` with `r` in
  `rR`; the CSR arrays (`CsrMem`) are unchanged.
* Memory steps: `DfsMem.visit` (four stores), `DfsMem.bump`, `DfsMem.pop`.
* One round (`dfsBody_run`): from a non-halted reachable state `s`, `dfsBody` yields a
  representation of `DFS.step nb s` (cases `step_root`, `step_skip`, `step_push`, `step_exam`,
  `step_pop`).
* The loop (`stepDfs_spec`): invariant "the machine represents `DFS.run nb k (init vs)` for
  some `k`", measure `DFS.mu` (read off the machine, `muC`), so at most
  `mu (init) = 3 N + 2 |E|` rounds; when the test is zero the state is halted, hence it is
  `dfsOf g` (`drun_eq_final`).
* Space: the addresses of one step (`dfsBody_addrOK`, one lemma per sub-block, along the case
  analysis of `dfsBody_run`) are inside the regions of the layout (`fits`); the top of the stack
  is inside its region because the stack holds distinct vertices (`length_stk_le`).
-/

@[expose] public section

namespace STACS2027.RAM.R1

open STACS2027.Algo

variable {S : ℕ}

/-! ### Representation of the search -/

/-- The memory during the search, for the abstract state `s`. -/
structure DfsMem (g : Graph) (c₀ : Config) (s : DFS.State) (m : ℕ → ℕ) : Prop where
  csr : CsrMem g c₀ m
  pre : Tab m (bPRE g (c₀.reg rFREE)) (numV g) s.pre
  par : Tab m (bPAR g (c₀.reg rFREE)) (numV g) s.par
  ptr : Tab m (bPTR g (c₀.reg rFREE)) (numV g) s.ptr
  ord : Arr m (bORD g (c₀.reg rFREE)) s.ord
  stk : Arr m (bSTK g (c₀.reg rFREE)) s.stk.reverse
  zero : ZeroFrom m (endL g (c₀.reg rFREE))

/-- The machine represents the state `s` of the search. -/
@[mk_iff] structure DfsRep (g : Graph) (c₀ : Config) (s : DFS.State) (c : Config) : Prop where
  glob : Glob g c₀ c
  sp : c.reg gSP = s.stk.length
  cnt : c.reg gCNT = s.cnt
  root : c.reg rR ≤ numV g
  rs : s.rs = List.range' (c.reg rR) (numV g - c.reg rR)
  mem : DfsMem g c₀ s c.mem

theorem DfsRep.indep (g : Graph) (c₀ : Config) (s : DFS.State) :
    Indep [rT, rI, rX, rY, rU, rV, rP, rA, rB, rW, rAcc] (DfsRep g c₀ s) := by
  indep [dfsRep_iff, glob_iff]

/-! ### Memory steps -/

section mem

variable {g : Graph} {c₀ : Config} {s : DFS.State} {m : ℕ → ℕ}

/-- Visiting `w` with parent `p`: four stores. -/
theorem DfsMem.visit (h : DfsMem g c₀ s m) {w p : ℕ} (hw : w < numV g)
    (hcnt : s.cnt = s.ord.length) (hord : s.ord.length < numV g) (hstk : s.stk.length < numV g) :
    DfsMem g c₀ (visitS s w p)
      (upd (upd (upd (upd m (bORD g (c₀.reg rFREE) + s.cnt) w) (bPRE g (c₀.reg rFREE) + w)
        (s.cnt + 1)) (bPAR g (c₀.reg rFREE) + w) p) (bSTK g (c₀.reg rFREE) + s.stk.length) w) := by
  have hL := layout_eqs g (c₀.reg rFREE)
  refine ⟨(((h.csr.upd (by omega) _).upd (by omega) _).upd (by omega) _).upd (by omega) _,
    ?_, ?_, ?_, ?_, ?_, (((h.zero.upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)⟩
  · exact (((h.pre.upd_of_disjoint (by omega)).upd rfl).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)
  · exact (((h.par.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd rfl).upd_of_disjoint
      (by omega)
  · exact (((h.ptr.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)).upd_of_disjoint (by omega)
  · exact (((h.ord.upd_snoc (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)).upd_of_disjoint (by simp; omega)
  · show Arr _ _ (w :: s.stk).reverse
    rw [List.reverse_cons]
    exact (((h.stk.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)).upd_snoc (by simp)

/-- Advancing the pointer of `v`. -/
theorem DfsMem.bump (h : DfsMem g c₀ s m) {v : ℕ} (hv : v < numV g) :
    DfsMem g c₀ (bumpS s v) (upd m (bPTR g (c₀.reg rFREE) + v) (s.ptr v + 1)) := by
  have hL := layout_eqs g (c₀.reg rFREE)
  exact ⟨h.csr.upd (by omega) _, h.pre.upd_of_disjoint (by omega),
    h.par.upd_of_disjoint (by omega), h.ptr.upd rfl, h.ord.upd_of_disjoint (by omega),
    h.stk.upd_of_disjoint (by omega), h.zero.upd (by omega)⟩

/-- Popping the top. -/
theorem DfsMem.pop (h : DfsMem g c₀ s m) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest) :
    DfsMem g c₀ { s with stk := rest } m := by
  have hs := h.stk
  rw [hst, List.reverse_cons] at hs
  exact ⟨h.csr, h.pre, h.par, h.ptr, h.ord, hs.prefix, h.zero⟩

/-- The memory does not depend on the root candidates. -/
theorem DfsMem.setRs (h : DfsMem g c₀ s m) (rs' : List ℕ) : DfsMem g c₀ { s with rs := rs' } m :=
  ⟨h.csr, h.pre, h.par, h.ptr, h.ord, h.stk, h.zero⟩

end mem

/-! ### Loop-free blocks -/

theorem wregs_visit (x p : ℕ) : wregs (visit x p) = [rT, rT, gCNT, rT, rT, rT, rT, gSP] := rfl
theorem loopFree_visit (x p : ℕ) : LoopFree (visit x p) := by simp [visit, LoopFree]

/-- Visiting the vertex in register `x` with the parent in register `p`. -/
theorem visit_run {g : Graph} {c₀ c : Config} {s : DFS.State} {x p w pv : ℕ}
    (hxp : x = rR ∧ p = rR ∨ x = rW ∧ p = rV) (hR : DfsRep g c₀ s c) (hx : c.reg x = w)
    (hp : c.reg p = pv) (hw : w < numV g) (hcnt : s.cnt = s.ord.length)
    (hord : s.ord.length < numV g) (hstk : s.stk.length < numV g) :
    DfsRep g c₀ (visitS s w pv) (run (visit x p) c) ∧
      ∀ r, r ≠ gCNT → r ≠ gSP → r ≠ rT → (run (visit x p) c).reg r = c.reg r := by
  have hreg : ∀ r, r ≠ gCNT → r ≠ gSP → r ≠ rT → (run (visit x p) c).reg r = c.reg r :=
    fun r h1 h2 h3 => run_reg_of_not_mem (loopFree_visit _ _)
      (by rw [wregs_visit]; simp [h1, h2, h3]) c
  have hx' : x ≠ rT ∧ x ≠ gCNT ∧ x ≠ gSP ∧ p ≠ rT ∧ p ≠ gCNT ∧ p ≠ gSP := by
    rcases hxp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨hx1, hx2, hx3, hp1, hp2, hp3⟩ := hx'
  have hG := hR.glob
  refine ⟨⟨(Glob.regIndep g c₀).run_of_sub (loopFree_visit _ _) (by rw [wregs_visit]; decide) hG,
    ?_, ?_, ?_, ?_, ?_⟩, hreg⟩
  · simp +decide [visit, run_inc, run_st, hR.sp, visitS, hx1, hp1]
  · simp +decide [visit, run_inc, run_st, hR.cnt, visitS, hx1, hx2, hp1]
  · rw [hreg _ (by decide) (by decide) (by decide)]; exact hR.root
  · rw [hreg _ (by decide) (by decide) (by decide)]; exact hR.rs
  · have := hR.mem.visit (p := pv) hw hcnt hord hstk
    simpa +decide [visit, run_inc, run_st, hG.ord, hG.pre, hG.par, hG.stk, hR.cnt, hR.sp, hx, hp,
      hx1, hx2, hx3, hp1, hp2, hp3] using this

/-- Moving to the next root candidate. -/
theorem incRoot_run {g : Graph} {c₀ c : Config} {s : DFS.State} (hR : DfsRep g c₀ s c)
    (hr : c.reg rR < numV g) :
    DfsRep g c₀ { s with rs := List.range' (c.reg rR + 1) (numV g - (c.reg rR + 1)) }
      (run (inc rR) c) := by
  rw [run_inc (by decide)]
  refine ⟨(Glob.regIndep g c₀).setReg (by decide) _ ((Glob.regIndep g c₀).setReg (by decide) _
    hR.glob), ?_, ?_, ?_, ?_, by simp only [setReg_mem]; exact hR.mem.setRs _⟩
  · simp +decide [hR.sp]
  · simp +decide [hR.cnt]
  · simp +decide; omega
  · simp +decide

/-! ### One step of the search -/

section step

variable {g : Graph} {c₀ c : Config} {s : DFS.State}

/-- Empty stack: the next root candidate. -/
theorem rootStep_run (hR : DfsRep g c₀ s c)
    (hI : DFS.Inv (List.range (numV g)) (nbOf (idEdges g)) s) (hO : DFS.OrdInv s)
    (hst : s.stk = []) (hh : ¬ DFS.Halted s) :
    DfsRep g c₀ (DFS.step (nbOf (idEdges g)) s) (run rootStep c) := by
  have hr : c.reg rR < numV g := by
    by_contra h
    apply hh
    refine ⟨hst, ?_⟩
    rw [hR.rs, show numV g - c.reg rR = 0 by omega]; rfl
  have hrs : s.rs = c.reg rR :: List.range' (c.reg rR + 1) (numV g - (c.reg rR + 1)) := by
    rw [hR.rs, show numV g - c.reg rR = (numV g - (c.reg rR + 1)) + 1 by omega, List.range'_succ]
  have hpre : c.mem (c.reg gPRE + c.reg rR) = s.pre (c.reg rR) := by
    rw [hR.glob.pre]; exact hR.mem.pre.get hr
  have hR₁ : DfsRep g c₀ s (run (ld rX gPRE rR) c) := by
    rw [run_ld]; exact (DfsRep.indep g c₀ s).setReg (by decide) _ hR
  have hX₁ : (run (ld rX gPRE rR) c).reg rX = s.pre (c.reg rR) := by simp [hpre]
  have hr₁ : (run (ld rX gPRE rR) c).reg rR = c.reg rR := by simp +decide
  simp only [rootStep, run_seq', run_ifz', hX₁, run_skip]
  by_cases h0 : s.pre (c.reg rR) = 0
  · rw [step_root hst hrs h0]
    simp only [h0, ↓reduceIte]
    obtain ⟨hV, hreg⟩ := visit_run (Or.inl ⟨rfl, rfl⟩) hR₁ hr₁ hr₁ hr hO.cnt_eq
      (length_ord_lt hI hO hr h0) (by rw [hst]; simp; omega)
    have hr₂ := hreg rR (by decide) (by decide) (by decide)
    have := incRoot_run hV (by rw [hr₂, hr₁]; exact hr)
    rwa [hr₂, hr₁] at this
  · rw [step_skip hst hrs h0]
    simp only [h0, ↓reduceIte]
    have := incRoot_run hR₁ (by rw [hr₁]; exact hr)
    rwa [hr₁] at this

/-- Reading the top `v` of the stack, its next position `OFF[v] + PTR[v]` and its end. -/
theorem topRead_run (hR : DfsRep g c₀ s c) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest)
    (hv : v < numV g) :
    (run topRead c).reg rV = v ∧ (run topRead c).reg rA = ps (idEdges g) v + s.ptr v ∧
      (run topRead c).reg rX = s.ptr v ∧
      (run topRead c).reg rB = ps (idEdges g) v + (nbOf (idEdges g) v).length ∧
      Agree [rP, rV, rA, rX, rB, rT] c (run topRead c) := by
  have hG := hR.glob
  have hsp : c.reg gSP = rest.length + 1 := by rw [hR.sp, hst]; rfl
  have hstkv : c.mem (bSTK g (c₀.reg rFREE) + rest.length) = v := by
    have hs := hR.mem.stk
    rw [hst, List.reverse_cons, arr_append] at hs
    simpa using hs.2
  have hoff : c.mem (bOFF g (c₀.reg rFREE) + v) = ps (idEdges g) v := hR.mem.csr.off.get (by omega)
  have hoff1 : c.mem (bOFF g (c₀.reg rFREE) + (v + 1)) =
      ps (idEdges g) v + (nbOf (idEdges g) v).length := by
    rw [hR.mem.csr.off.get (by omega), ps_succ]
  have hptr : c.mem (bPTR g (c₀.reg rFREE) + v) = s.ptr v := hR.mem.ptr.get hv
  refine ⟨?_, ?_, ?_, ?_, agree_run (by decide) rfl rfl (by decide) c⟩ <;>
    simp +decide [topRead, run_subc, run_addc, hG.stk, hG.off, hG.ptr, hsp, hstkv, hoff, hoff1,
      hptr]

/-- The next neighbour `w` of the top `v`: `PTR[v]++`, `rW := w`, `rY := PRE[w]`. -/
theorem advRead_run (hR : DfsRep g c₀ s c) {v : ℕ} (hv : v < numV g) (hV : c.reg rV = v)
    (hA : c.reg rA = ps (idEdges g) v + s.ptr v) (hX : c.reg rX = s.ptr v)
    (hlt : s.ptr v < (nbOf (idEdges g) v).length) :
    DfsRep g c₀ (bumpS s v) (run advRead c) ∧
      (run advRead c).reg rW = (nbOf (idEdges g) v).getD (s.ptr v) 0 ∧
      (run advRead c).reg rY = s.pre ((nbOf (idEdges g) v).getD (s.ptr v) 0) ∧
      (run advRead c).reg rV = v := by
  have hG := hR.glob
  have hL := layout_eqs g (c₀.reg rFREE)
  set w := (nbOf (idEdges g) v).getD (s.ptr v) 0 with hw_def
  have hw : w < numV g := lt_of_mem_nbOf (DFS.getD_mem_nb hlt)
  have hadj : c.mem (bADJ g (c₀.reg rFREE) + (ps (idEdges g) v + s.ptr v)) = w := by
    rw [← Nat.add_assoc]; exact (hR.mem.csr.adj v hv).getD hlt
  have hpre : c.mem (bPRE g (c₀.reg rFREE) + w) = s.pre w := hR.mem.pre.get hw
  have hne : bPRE g (c₀.reg rFREE) + w ≠ bPTR g (c₀.reg rFREE) + v := by omega
  refine ⟨⟨(Glob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · simp +decide [advRead, run_inc, run_st, hR.sp, bumpS]
  · simp +decide [advRead, run_inc, run_st, hR.cnt, bumpS]
  · simpa +decide [advRead, run_inc, run_st] using hR.root
  · simpa +decide [advRead, run_inc, run_st, bumpS] using hR.rs
  · simpa +decide [advRead, run_inc, run_st, hG.adj, hG.ptr, hA, hX, hV, hadj] using
      hR.mem.bump hv
  · simp +decide [advRead, run_inc, run_st, hG.adj, hA, hadj]
  · simp +decide [advRead, run_inc, run_st, hG.adj, hG.ptr, hG.pre, hA, hX, hV, hadj, hpre, hne]
  · simp +decide [advRead, run_inc, run_st, hV]

/-- Popping the top. -/
theorem pop_run (hR : DfsRep g c₀ s c) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest) :
    DfsRep g c₀ { s with stk := rest } (run (dec gSP) c) := by
  rw [run_dec (by decide)]
  refine ⟨(Glob.regIndep g c₀).setReg (by decide) _ ((Glob.regIndep g c₀).setReg (by decide) _
    hR.glob), ?_, ?_, ?_, ?_, by simp only [setReg_mem]; exact hR.mem.pop hst⟩
  · simp +decide [hR.sp, hst]
  · simp +decide [hR.cnt]
  · simpa +decide using hR.root
  · simpa +decide using hR.rs

/-- Non-empty stack: the next neighbour of the top, or a pop. -/
theorem topStep_run (hR : DfsRep g c₀ s c)
    (hI : DFS.Inv (List.range (numV g)) (nbOf (idEdges g)) s) (hO : DFS.OrdInv s)
    {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest) :
    DfsRep g c₀ (DFS.step (nbOf (idEdges g)) s) (run topStep c) := by
  have hv : v < numV g := lt_of_mem_stk hI (by rw [hst]; simp)
  obtain ⟨hV, hA, hX, hB, hAg⟩ := topRead_run hR hst hv
  have hR₁ : DfsRep g c₀ s (run topRead c) := (DfsRep.indep g c₀ s).mono (by decide) _ _ hAg hR
  simp only [topStep, run_seq', run_ifLt, hA, hB]
  by_cases hlt : s.ptr v < (nbOf (idEdges g) v).length
  · have hlt' : ps (idEdges g) v + s.ptr v < ps (idEdges g) v + (nbOf (idEdges g) v).length := by
      omega
    simp only [hlt', ↓reduceIte]
    have hR₂ := (DfsRep.indep g c₀ s).setReg (d := rT) (by decide)
      (ps (idEdges g) v + (nbOf (idEdges g) v).length - (ps (idEdges g) v + s.ptr v)) hR₁
    obtain ⟨hR₃, hW₃, hY₃, hV₃⟩ := advRead_run hR₂ hv (by simp +decide [hV])
      (by simp +decide [hA]) (by simp +decide [hX]) hlt
    have hw : (nbOf (idEdges g) v).getD (s.ptr v) 0 < numV g :=
      lt_of_mem_nbOf (DFS.getD_mem_nb hlt)
    simp only [advance, run_seq', run_ifz', hY₃]
    by_cases h0 : s.pre ((nbOf (idEdges g) v).getD (s.ptr v) 0) = 0
    · rw [step_push hst hlt h0]
      simp only [h0, ↓reduceIte]
      have hord : s.ord.length < numV g := length_ord_lt hI hO hw h0
      have hstk : s.stk.length < numV g := length_stk_lt hI hw h0
      exact (visit_run (Or.inr ⟨rfl, rfl⟩) hR₃ hW₃ hV₃ hw hO.cnt_eq hord hstk).1
    · rw [step_exam hst hlt h0]
      simp only [h0, ↓reduceIte, run_skip]
      exact hR₃
  · have hlt' : ¬ ps (idEdges g) v + s.ptr v < ps (idEdges g) v + (nbOf (idEdges g) v).length := by
      omega
    simp only [hlt', ↓reduceIte]
    rw [step_pop hst hlt]
    exact pop_run ((DfsRep.indep g c₀ s).setReg (by decide) _ hR₁) hst

/-- **One step of the search.** -/
theorem dfsBody_run (hR : DfsRep g c₀ s c)
    (hI : DFS.Inv (List.range (numV g)) (nbOf (idEdges g)) s) (hO : DFS.OrdInv s)
    (hh : ¬ DFS.Halted s) : DfsRep g c₀ (DFS.step (nbOf (idEdges g)) s) (run dfsBody c) := by
  simp only [dfsBody, run_ifz', hR.sp]
  cases hst : s.stk with
  | nil => simpa using rootStep_run hR hI hO hst hh
  | cons v rest => simpa using topStep_run hR hI hO hst

/-- The loop test: `rT = |rs| + |stk|`. -/
theorem dfsCond_run (hR : DfsRep g c₀ s c) :
    DfsRep g c₀ s (run dfsCond c) ∧ (run dfsCond c).reg rT = s.rs.length + s.stk.length := by
  refine ⟨(DfsRep.indep g c₀ s).mono (W' := [rT]) (by decide) _ _
    (agree_run (by decide) rfl rfl (by decide) c) hR, ?_⟩
  simp +decide [dfsCond, hR.rs, hR.sp, hR.glob.n]

/-- The addresses of `visit x p` (hypotheses of `visit_run`). -/
theorem visit_addrOK {x p w : ℕ} (hxp : x = rR ∧ p = rR ∨ x = rW ∧ p = rV) (hR : DfsRep g c₀ s c)
    (hx : c.reg x = w) (hw : w < numV g) (hcnt : s.cnt = s.ord.length)
    (hord : s.ord.length < numV g) (hstk : s.stk.length < numV g) (hS : endL g (c₀.reg rFREE) ≤ S) :
    AddrOK S (visit x p) c := by
  have hG := hR.glob
  have := fits g hS
  rcases hxp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    addr_ok [visit, hG.ord, hG.pre, hG.par, hG.stk, hR.cnt, hR.sp, hx]

/-- Empty stack: the addresses of the root step (the case analysis of `rootStep_run`). -/
theorem rootStep_addrOK (hR : DfsRep g c₀ s c)
    (hI : DFS.Inv (List.range (numV g)) (nbOf (idEdges g)) s) (hO : DFS.OrdInv s)
    (hst : s.stk = []) (hh : ¬ DFS.Halted s) (hS : endL g (c₀.reg rFREE) ≤ S) :
    AddrOK S rootStep c := by
  have hr : c.reg rR < numV g := by
    by_contra h
    apply hh
    refine ⟨hst, ?_⟩
    rw [hR.rs, show numV g - c.reg rR = 0 by omega]; rfl
  have hpre : c.mem (c.reg gPRE + c.reg rR) = s.pre (c.reg rR) := by
    rw [hR.glob.pre]; exact hR.mem.pre.get hr
  have hR₁ : DfsRep g c₀ s (run (ld rX gPRE rR) c) := by
    rw [run_ld]; exact (DfsRep.indep g c₀ s).setReg (by decide) _ hR
  have hr₁ : (run (ld rX gPRE rR) c).reg rR = c.reg rR := by simp +decide
  have := fits g hS
  refine AddrOK.seq (by addr_ok [hR.glob.pre]) (AddrOK.seq (AddrOK.ifz (fun h0 => ?_)
    fun _ => trivial) (by simp))
  simp only [run_ld, setReg_reg, ↓reduceIte, hpre] at h0
  exact visit_addrOK (Or.inl ⟨rfl, rfl⟩) hR₁ hr₁ hr hO.cnt_eq (length_ord_lt hI hO hr h0)
    (by rw [hst]; simp; omega) hS

/-- A bound the `HT` proof did not need: the stack is no longer than the number of vertices
(it holds distinct vertices), so its cells are below `endL`. -/
theorem length_stk_le (hI : DFS.Inv (List.range (numV g)) (nbOf (idEdges g)) s) :
    s.stk.length ≤ numV g := by
  have hsub : s.stk ⊆ List.range (numV g) := fun x hx => List.mem_range.mpr (lt_of_mem_stk hI hx)
  simpa using (hI.stk_nodup.subperm hsub).length_le

/-- The addresses of `topRead` (hypotheses of `topRead_run`, and the invariant). -/
theorem topRead_addrOK (hR : DfsRep g c₀ s c) (hI : DFS.Inv (List.range (numV g)) (nbOf (idEdges g)) s)
    {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest) (hv : v < numV g)
    (hS : endL g (c₀.reg rFREE) ≤ S) : AddrOK S topRead c := by
  have hG := hR.glob
  have := fits g hS
  have hsp : c.reg gSP = rest.length + 1 := by rw [hR.sp, hst]; rfl
  have hlen := length_stk_le hI
  rw [hst, List.length_cons] at hlen
  have hstkv : c.mem (bSTK g (c₀.reg rFREE) + rest.length) = v := by
    have hs := hR.mem.stk
    rw [hst, List.reverse_cons, arr_append] at hs
    simpa using hs.2
  addr_ok [topRead, hG.stk, hG.off, hG.ptr, hsp, hstkv]

/-- The addresses of `advRead` (hypotheses of `advRead_run`). -/
theorem advRead_addrOK (hR : DfsRep g c₀ s c) {v : ℕ} (hv : v < numV g) (hV : c.reg rV = v)
    (hA : c.reg rA = ps (idEdges g) v + s.ptr v) (hlt : s.ptr v < (nbOf (idEdges g) v).length)
    (hS : endL g (c₀.reg rFREE) ≤ S) : AddrOK S advRead c := by
  have hG := hR.glob
  have := fits g hS
  have hw : (nbOf (idEdges g) v).getD (s.ptr v) 0 < numV g := lt_of_mem_nbOf (DFS.getD_mem_nb hlt)
  have hadj : c.mem (bADJ g (c₀.reg rFREE) + (ps (idEdges g) v + s.ptr v)) =
      (nbOf (idEdges g) v).getD (s.ptr v) 0 := by
    rw [← Nat.add_assoc]; exact (hR.mem.csr.adj v hv).getD hlt
  have hps := idEdges_ps g
  have hvN := ps_mono (idEdges g) (show v + 1 ≤ numV g by omega)
  rw [ps_succ] at hvN
  addr_ok [advRead, hG.adj, hG.ptr, hG.pre, hA, hV, hadj]

/-- Non-empty stack: the addresses of the step (the case analysis of `topStep_run`). -/
theorem topStep_addrOK (hR : DfsRep g c₀ s c)
    (hI : DFS.Inv (List.range (numV g)) (nbOf (idEdges g)) s) (hO : DFS.OrdInv s)
    {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest) (hS : endL g (c₀.reg rFREE) ≤ S) :
    AddrOK S topStep c := by
  have hv : v < numV g := lt_of_mem_stk hI (by rw [hst]; simp)
  obtain ⟨hV, hA, hX, hB, hAg⟩ := topRead_run hR hst hv
  have hR₁ : DfsRep g c₀ s (run topRead c) := (DfsRep.indep g c₀ s).mono (by decide) _ _ hAg hR
  refine AddrOK.seq (topRead_addrOK hR hI hst hv hS) (AddrOK.ifLt (fun hlt' => ?_) fun _ => by simp)
  have hlt : s.ptr v < (nbOf (idEdges g) v).length := by rw [hA, hB] at hlt'; omega
  have hR₂ := (DfsRep.indep g c₀ s).setReg (d := rT) (by decide)
    ((run topRead c).reg rB - (run topRead c).reg rA) hR₁
  obtain ⟨hR₃, hW₃, hY₃, hV₃⟩ := advRead_run hR₂ hv (by simp +decide [hV])
    (by simp +decide [hA]) (by simp +decide [hX]) hlt
  have hw : (nbOf (idEdges g) v).getD (s.ptr v) 0 < numV g := lt_of_mem_nbOf (DFS.getD_mem_nb hlt)
  refine AddrOK.seq (advRead_addrOK hR₂ hv (by simp +decide [hV]) (by simp +decide [hA]) hlt hS)
    (AddrOK.ifz (fun h0 => ?_) fun _ => trivial)
  rw [hY₃] at h0
  have hord : s.ord.length < numV g := length_ord_lt hI hO hw h0
  have hstk : s.stk.length < numV g := length_stk_lt hI hw h0
  exact visit_addrOK (Or.inr ⟨rfl, rfl⟩) hR₃ hW₃ hw hO.cnt_eq hord hstk hS

/-- **The addresses of one step of the search.** -/
theorem dfsBody_addrOK (hR : DfsRep g c₀ s c)
    (hI : DFS.Inv (List.range (numV g)) (nbOf (idEdges g)) s) (hO : DFS.OrdInv s)
    (hh : ¬ DFS.Halted s) (hS : endL g (c₀.reg rFREE) ≤ S) : AddrOK S dfsBody c := by
  refine AddrOK.ifz (fun h => rootStep_addrOK hR hI hO ?_ hh hS) fun h => ?_
  · exact List.length_eq_zero_iff.mp (hR.sp ▸ h)
  · obtain ⟨v, rest, hst⟩ := List.exists_cons_of_length_pos (by rw [← hR.sp]; omega)
    exact topStep_addrOK hR hI hO hst hS

end step

/-! ### The loop -/

/-- The machine's view of the parts of the state that the measure reads. -/
def absOf (g : Graph) (c₀ c : Config) : DFS.State :=
  ⟨fun v => c.mem (bPRE g (c₀.reg rFREE) + v), fun _ => 0, fun v => c.mem (bPTR g (c₀.reg rFREE) + v),
    List.replicate (c.reg gSP) 0, List.replicate (numV g - c.reg rR) 0, 0, []⟩

/-- The measure of the search, read off the machine. -/
def muC (g : Graph) (c₀ c : Config) : ℕ :=
  DFS.mu (List.range (numV g)) (nbOf (idEdges g)) (absOf g c₀ c)

theorem muC_eq {g : Graph} {c₀ c : Config} {s : DFS.State} (hR : DfsRep g c₀ s c) :
    muC g c₀ c = DFS.mu (List.range (numV g)) (nbOf (idEdges g)) s :=
  mu_congr (fun v hv => hR.mem.pre.get (List.mem_range.mp hv))
    (fun v hv => hR.mem.ptr.get (List.mem_range.mp hv)) (by simp [absOf, hR.sp])
    (by simp [absOf, hR.rs])

/-- The invariant of the loop: the machine represents a state reached from `init`, and the
test register holds `|rs| + |stk|`. -/
def LoopInv (g : Graph) (c₀ c : Config) : Prop :=
  ∃ k, DfsRep g c₀ (DFS.run (nbOf (idEdges g)) k (DFS.init (List.range (numV g)))) c ∧
    c.reg rT = (DFS.run (nbOf (idEdges g)) k (DFS.init (List.range (numV g)))).rs.length +
      (DFS.run (nbOf (idEdges g)) k (DFS.init (List.range (numV g)))).stk.length

theorem dfsRound_spec (g : Graph) (c₀ : Config) (hS : endL g (c₀.reg rFREE) ≤ S) (v : ℕ) :
    HTB S (.seq dfsBody dfsCond) (fun c => LoopInv g c₀ c ∧ c.reg rT ≠ 0 ∧ muC g c₀ c = v)
      (fun c => LoopInv g c₀ c ∧ muC g c₀ c < v) 60 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨⟨k, hR, hT⟩, hne, _⟩ => by
    have hI := DFS.inv_run (ok_idEdges g) k (DFS.inv_init _ _)
    have hO := DFS.ordInv_run (nb := nbOf (idEdges g)) k (DFS.ordInv_init (List.range (numV g)))
    have hh : ¬ DFS.Halted (DFS.run (nbOf (idEdges g)) k (DFS.init (List.range (numV g)))) :=
      fun h => hne (by rw [hT, h.1, h.2]; rfl)
    exact (dfsBody_addrOK hR hI hO hh hS).seq (.of_memFree rfl)) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨k, hR, hT⟩, hne, hμ⟩ => ?_
  have hok := ok_idEdges g
  have hI := DFS.inv_run hok k (DFS.inv_init _ _)
  have hO := DFS.ordInv_run (nb := nbOf (idEdges g)) k (DFS.ordInv_init (List.range (numV g)))
  have hh : ¬ DFS.Halted (DFS.run (nbOf (idEdges g)) k (DFS.init (List.range (numV g)))) :=
    fun h => hne (by rw [hT, h.1, h.2]; rfl)
  obtain ⟨h2, hT2⟩ := dfsCond_run (dfsBody_run hR hI hO hh)
  rw [← drun_succ] at h2 hT2
  refine ⟨⟨k + 1, h2, hT2⟩, ?_⟩
  rw [run_seq', muC_eq h2, ← hμ, muC_eq hR, drun_succ]
  exact DFS.mu_step hok hI hh

theorem dfsInit_spec (g : Graph) (c₀ : Config) :
    HTB S dfsInit (fun c => Glob g c₀ c ∧ CsrMem g c₀ c.mem ∧ ZeroFrom c.mem (bPRE g (c₀.reg rFREE)))
      (DfsRep g c₀ (DFS.init (List.range (numV g)))) 3 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hG, hC, hZ⟩ => ?_
  have hL := layout_eqs g (c₀.reg rFREE)
  simp only [dfsInit, run_seq', run_const]
  refine ⟨(Glob.regIndep g c₀).setReg (by decide) _ ((Glob.regIndep g c₀).setReg (by decide) _
    ((Glob.regIndep g c₀).setReg (by decide) _ hG)), ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [DFS.init]
  · simp +decide [DFS.init]
  · simp +decide
  · simp +decide [DFS.init, List.range_eq_range']
  · simp only [setReg_mem]
    exact ⟨hC, hZ.tab le_rfl _, hZ.tab (by omega) _, hZ.tab (by omega) _, arr_nil _ _,
      arr_nil _ _, hZ.mono (by omega)⟩

/-- **Step 5: the depth-first search.** At most `3 N + 2 |E|` rounds of at most `60` steps. -/
theorem stepDfs_spec (g : Graph) (c₀ : Config) (hS : endL g (c₀.reg rFREE) ≤ S) :
    HTB S stepDfs (fun c => Glob g c₀ c ∧ CsrMem g c₀ c.mem ∧ ZeroFrom c.mem (bPRE g (c₀.reg rFREE)))
      (DfsRep g c₀ (dfsOf g)) (3 + (2 + ((3 * numV g + 2 * (idEdges g).length) * (60 + 1) + 1))) := by
  have hinit : HTB S dfsCond (DfsRep g c₀ (DFS.init (List.range (numV g))))
      (fun c => LoopInv g c₀ c ∧ muC g c₀ c ≤ 3 * numV g + 2 * (idEdges g).length) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hR => by
      obtain ⟨h1, h2⟩ := dfsCond_run hR
      refine ⟨⟨0, h1, h2⟩, ?_⟩
      rw [muC_eq h1, mu_init, List.length_range, ← idEdges_ps g]
      exact le_rfl
  have hl := HTB.whileC (muC g c₀) hinit (dfsRound_spec g c₀ hS)
  refine (dfsInit_spec g c₀).seq (hl.post fun c ⟨⟨k, hR, hT⟩, h0⟩ => ?_)
  have hH : DFS.Halted (DFS.run (nbOf (idEdges g)) k (DFS.init (List.range (numV g)))) := by
    rw [h0] at hT
    exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
  rwa [drun_eq_final (ok_idEdges g) hH] at hR

end STACS2027.RAM.R1
