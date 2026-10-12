module

public import Runtimes.TwoSatCsr
import Mathlib.Tactic

/-!
# Linear-time 2-SAT on the RAM: the path-based search, representation and one step

The machine simulates `Scc.step` for the implication graph `nbOf cl` on `N = 2n` nodes.

* Representation (`SrchRep n m cl c₀ s c`): `LAB`, `PTR` hold `s.lab`, `s.ptr` on `[0, N)`;
  `STK` holds `s.stk` reversed (top last) with `tSP = |s.stk|`; `SS` holds `s.S` with
  `tSSP = |s.S|`; `BB` holds `s.B` reversed with `tBP = |s.B|`; `tNXT = s.nxt`;
  `tVAL = N + 1 + s.nc`; the CSR arrays (`CsrMem`) are unchanged and the output array is
  still zero.
* Memory steps (`SrchMem.push`, `SrchMem.bump`, `SrchMem.popOne`, …), loop-free blocks with
  their `run` lemmas (`visitT_run`, `rootStep_run`, `topRead_run`, `advance_run`,
  `finRead_run`), and the inner loop popping a component (`popComp_spec`, through the
  intermediate states `mid N s k`).
* One round (`sccBody_spec`): from a reachable non-halted state `s`, the round yields a
  representation of `Scc.step s` within `60 + 10 p` steps, where `p` is the number of
  vertices the step pops from `S`.

Space: every block is address-safe within any `S ≥ endL n m F` (`F` the initial `rFREE`): the
`foo_addrOK` lemmas (and the `AddrOK` conjunct of `rootStep_run`, `advance_run`) bound the
addresses by the regions of the layout (`fits`) and the sizes of the stacks (`Scc.Inv.stk_len`,
`Scc.Inv.B_len`, `Scc.Inv.S_len`).
-/

@[expose] public section

namespace STACS2027.Runtimes.TwoSat

open STACS2027.RAM Scc

variable {S : ℕ}

/-! ### The steps of the search, case by case -/

section steps

variable {N : ℕ} {nb : ℕ → List ℕ} {s : State} {v : ℕ} {rest : List ℕ}

theorem step_nil_visit (hst : s.stk = []) (hlt : s.nxt < N) (h0 : s.lab s.nxt = 0) :
    step N nb s = { push s s.nxt with nxt := s.nxt + 1 } := by
  simp [step, hst, hlt, h0]

theorem step_nil_skip (hst : s.stk = []) (hlt : s.nxt < N) (h0 : s.lab s.nxt ≠ 0) :
    step N nb s = { s with nxt := s.nxt + 1 } := by
  simp [step, hst, hlt, h0]

theorem step_visit (hst : s.stk = v :: rest) (hlt : s.ptr v < (nb v).length)
    (h0 : s.lab ((nb v).getD (s.ptr v) 0) = 0) :
    step N nb s = push (bump s v) ((nb v).getD (s.ptr v) 0) := by
  simp only [step, hst, hlt, h0, ↓reduceIte]

theorem step_merge (hst : s.stk = v :: rest) (hlt : s.ptr v < (nb v).length)
    (h0 : s.lab ((nb v).getD (s.ptr v) 0) ≠ 0)
    (hl : s.lab ((nb v).getD (s.ptr v) 0) < s.B.headD 0) :
    step N nb s = { s with B := s.B.tail } := by
  simp only [step, hst, hlt, h0, hl, ↓reduceIte]

theorem step_adv (hst : s.stk = v :: rest) (hlt : s.ptr v < (nb v).length)
    (h0 : s.lab ((nb v).getD (s.ptr v) 0) ≠ 0)
    (hl : ¬ s.lab ((nb v).getD (s.ptr v) 0) < s.B.headD 0) :
    step N nb s = bump s v := by
  simp only [step, hst, hlt, h0, hl, ↓reduceIte]

theorem step_popc (hst : s.stk = v :: rest) (hlt : ¬ s.ptr v < (nb v).length)
    (hr : s.lab v = s.B.headD 0) : step N nb s = popc N s v rest := by
  simp [step, hst, hlt, hr]

theorem step_pop (hst : s.stk = v :: rest) (hlt : ¬ s.ptr v < (nb v).length)
    (hr : s.lab v ≠ s.B.headD 0) : step N nb s = { s with stk := rest } := by
  simp only [step, hst, hlt, hr, ↓reduceIte]

end steps

/-- The state while the top group is popped: `S` cut to its first `k` entries, the vertices
above relabelled `N + 1 + nc`. -/
def mid (N : ℕ) (s : State) (k : ℕ) : State :=
  { s with
    lab := relab s.lab (s.S.drop k) (N + 1 + s.nc)
    S := s.S.take k }

theorem popc_eq (N : ℕ) (s : State) (v : ℕ) (rest : List ℕ) :
    popc N s v rest = { mid N s (s.lab v - 1) with B := s.B.tail, stk := rest, nc := s.nc + 1 } :=
  rfl

/-- Room on the stacks for an unvisited vertex. -/
theorem Scc.Inv.room {N : ℕ} {nb : ℕ → List ℕ} {s : State} (hI : Scc.Inv N nb s) {w : ℕ} (hw0 : s.lab w = 0)
    (hwN : w < N) : s.S.length < N ∧ s.stk.length < N ∧ s.B.length < N := by
  have hwS : w ∉ s.S := fun h => by have := hI.lab_S h; omega
  have hnd : (w :: s.S).Nodup := List.nodup_cons.mpr ⟨hwS, hI.nodup⟩
  have := nodup_range_length hnd (fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hwN
    · exact hI.S_lt hx)
  simp only [List.length_cons] at this
  have := hI.stk_len; have := hI.B_len
  omega

/-! ### Representation -/

section rep

variable (n m : ℕ) (cl : List ℕ) (c₀ : Config)

/-- The memory during the search, for the abstract state `s`. -/
structure SrchMem (s : State) (mm : ℕ → ℕ) : Prop where
  csr : CsrMem n m cl c₀ mm
  tlab : Tab mm (bLAB n m (c₀.reg rFREE)) (2 * n) s.lab
  tptr : Tab mm (bPTR n m (c₀.reg rFREE)) (2 * n) s.ptr
  stk : Arr mm (bSTK n m (c₀.reg rFREE)) s.stk.reverse
  ss : Arr mm (bSS n m (c₀.reg rFREE)) s.S
  bb : Arr mm (bBB n m (c₀.reg rFREE)) s.B.reverse
  zero : ZeroFrom mm (bAS n m (c₀.reg rFREE))

/-- The machine represents the state `s` of the search. -/
@[mk_iff] structure SrchRep (s : State) (c : Config) : Prop where
  glob : Glob n m c₀ c
  sp : c.reg tSP = s.stk.length
  ssp : c.reg tSSP = s.S.length
  bp : c.reg tBP = s.B.length
  nxt : c.reg tNXT = s.nxt
  val : c.reg tVAL = 2 * n + 1 + s.nc
  mem : SrchMem n m cl c₀ s c.mem

/-- The scratch registers of the search. -/
def WS : List ℕ := [rT, sI, sX, sY, sU, sV, sP, sA, sB, sW, sH, sAcc, sQ]

theorem SrchRep.indep (s : State) : Indep WS (SrchRep n m cl c₀ s) := by
  indep [srchRep_iff, glob_iff]

end rep

/-! ### Memory steps -/

section mem

variable {n m : ℕ} {cl : List ℕ} {c₀ : Config} {s : State} {mm : ℕ → ℕ}

/-- Visiting `w`: four stores. -/
theorem SrchMem.push (h : SrchMem n m cl c₀ s mm) (hcl : cl.length = 2 * m) (hok : CodesOk n cl)
    {w : ℕ} (hw : w < 2 * n) (hS : s.S.length < 2 * n) (hB : s.B.length < 2 * n)
    (hstk : s.stk.length < 2 * n) :
    SrchMem n m cl c₀ (Scc.push s w)
      (upd (upd (upd (upd mm (bSS n m (c₀.reg rFREE) + s.S.length) w)
        (bLAB n m (c₀.reg rFREE) + w) (s.S.length + 1))
        (bBB n m (c₀.reg rFREE) + s.B.length) (s.S.length + 1))
        (bSTK n m (c₀.reg rFREE) + s.stk.length) w) := by
  have hL := layout_eqs n m (c₀.reg rFREE)
  refine ⟨(((h.csr.upd hcl hok (by omega) _).upd hcl hok (by omega) _).upd hcl hok (by omega) _).upd
    hcl hok (by omega) _, ?_, ?_, ?_, ?_, ?_,
    (((h.zero.upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)⟩
  · exact (((h.tlab.upd_of_disjoint (by omega)).upd rfl).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)
  · exact (((h.tptr.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint
      (by omega)).upd_of_disjoint (by omega)
  · show Arr _ _ (w :: s.stk).reverse
    rw [List.reverse_cons]
    exact (((h.stk.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega)).upd_of_disjoint
      (by simp; omega)).upd_snoc (by simp)
  · exact (((h.ss.upd_snoc rfl).upd_of_disjoint (by simp; omega)).upd_of_disjoint
      (by simp; omega)).upd_of_disjoint (by simp; omega)
  · show Arr _ _ ((s.S.length + 1) :: s.B).reverse
    rw [List.reverse_cons]
    exact (((h.bb.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega)).upd_snoc
      (by simp)).upd_of_disjoint (by simp; omega)

/-- Advancing the pointer of `v`. -/
theorem SrchMem.bump (h : SrchMem n m cl c₀ s mm) (hcl : cl.length = 2 * m) (hok : CodesOk n cl)
    {v : ℕ} (hv : v < 2 * n) :
    SrchMem n m cl c₀ (Scc.bump s v) (upd mm (bPTR n m (c₀.reg rFREE) + v) (s.ptr v + 1)) := by
  have hL := layout_eqs n m (c₀.reg rFREE)
  exact ⟨h.csr.upd hcl hok (by omega) _, h.tlab.upd_of_disjoint (by omega), h.tptr.upd rfl,
    h.stk.upd_of_disjoint (by simp; omega), h.ss.upd_of_disjoint (by omega),
    h.bb.upd_of_disjoint (by omega), h.zero.upd (by omega)⟩

theorem SrchMem.tailB (h : SrchMem n m cl c₀ s mm) : SrchMem n m cl c₀ { s with B := s.B.tail } mm := by
  refine ⟨h.csr, h.tlab, h.tptr, h.stk, h.ss, ?_, h.zero⟩
  have hb := h.bb
  cases hB : s.B with
  | nil => simp
  | cons b t => rw [hB, List.reverse_cons] at hb; exact hb.prefix

theorem SrchMem.popStk (h : SrchMem n m cl c₀ s mm) {v : ℕ} {rest : List ℕ}
    (hst : s.stk = v :: rest) : SrchMem n m cl c₀ { s with stk := rest } mm := by
  have hs := h.stk
  rw [hst, List.reverse_cons] at hs
  exact ⟨h.csr, h.tlab, h.tptr, hs.prefix, h.ss, h.bb, h.zero⟩

theorem SrchMem.setNxt (h : SrchMem n m cl c₀ s mm) (k : ℕ) :
    SrchMem n m cl c₀ { s with nxt := k } mm := ⟨h.csr, h.tlab, h.tptr, h.stk, h.ss, h.bb, h.zero⟩

/-- The start of the popping of a component. -/
theorem SrchMem.toMid (h : SrchMem n m cl c₀ s mm) (N : ℕ) :
    SrchMem n m cl c₀ (mid N s s.S.length) mm := by
  refine ⟨h.csr, h.tlab.congr_fun fun i _ => ?_, h.tptr, h.stk, by simpa [mid] using h.ss, h.bb,
    h.zero⟩
  simp [mid, relab]

/-- Popping one vertex of the top group. -/
theorem SrchMem.popOne {k : ℕ} (h : SrchMem n m cl c₀ (mid (2 * n) s k) mm) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) (hk : 0 < k) (hkS : k ≤ s.S.length) (hx : s.S[k - 1] < 2 * n) :
    SrchMem n m cl c₀ (mid (2 * n) s (k - 1))
      (upd mm (bLAB n m (c₀.reg rFREE) + s.S[k - 1]) (2 * n + 1 + s.nc)) := by
  have hL := layout_eqs n m (c₀.reg rFREE)
  refine ⟨h.csr.upd hcl hok (by omega) _, ?_, h.tptr.upd_of_disjoint (by omega),
    h.stk.upd_of_disjoint (by simp; omega), ?_, h.bb.upd_of_disjoint (by simp; omega),
    h.zero.upd (by omega)⟩
  · refine (h.tlab.upd rfl).congr_fun fun i _ => ?_
    have hd : s.S.drop (k - 1) = s.S[k - 1] :: s.S.drop k := by
      rw [List.drop_eq_getElem_cons (by omega)]
      congr 2; omega
    simp only [mid, relab, hd, List.mem_cons]
    by_cases hi : i = s.S[k - 1]
    · rw [hi]; simp
    · rw [Function.update_of_ne hi]; simp [relab, hi]
  · have h1 := h.ss
    simp only [mid] at h1 ⊢
    have := (h1.take (k - 1)).upd_of_disjoint (a := bLAB n m (c₀.reg rFREE) + s.S[k - 1])
      (v := 2 * n + 1 + s.nc) (by simp; omega)
    simpa [List.take_take, show min (k - 1) k = k - 1 by omega] using this

end mem

/-! ### The program -/

/-- Visit the vertex in register `x`: `SS[|S|] := x`, `|S|++`, `LAB[x] := |S|`,
`BB[|B|] := |S|`, `|B|++`, `STK[|stk|] := x`, `|stk|++`. -/
def visitT (x : ℕ) : Stmt :=
  .seq (st tSS tSSP x) (.seq (inc tSSP) (.seq (st tLAB x tSSP) (.seq (st tBB tBP tSSP)
    (.seq (inc tBP) (.seq (st tSTK tSP x) (inc tSP))))))

/-- Empty search stack: the next root candidate. -/
def rootStep : Stmt := .seq (ld sX tLAB tNXT) (.seq (.ifz sX (visitT tNXT) .skip) (inc tNXT))

/-- The top `v` of the search stack (`sV`), `sA := OFF[v] + PTR[v]`, `sX := PTR[v]`,
`sB := OFF[v + 1]`. -/
def topRead : Stmt :=
  .seq (subc sP tSP 1) (.seq (ld sV tSTK sP) (.seq (ld sA tOFF sV) (.seq (ld sX tPTR sV)
    (.seq (.add sA sA sX) (.seq (addc sP sV 1) (ld sB tOFF sP))))))

/-- `PTR[v] := sX + 1`. -/
def bumpV : Stmt := .seq (inc sX) (st tPTR sV sX)

/-- `sH := BB[|B| - 1]`, the head of `B`. -/
def headRead : Stmt := .seq (subc sP tBP 1) (ld sH tBB sP)

/-- The next arc `v → w` (`w := ADJ[sA]`, `sY := LAB[w]`): visit `w` if new; merge the two top
groups if `w` is in a lower group; otherwise advance. -/
def advance : Stmt :=
  .seq (ld sW tADJ sA) (.seq (ld sY tLAB sW)
    (.ifz sY (.seq bumpV (visitT sW)) (.seq headRead (ifLt sY sH (dec tBP) bumpV))))

/-- The test of the popping loop: `rT := |S| + 1 - sY` (`sY = lab v`). -/
def popCond : Stmt := .seq (addc rT tSSP 1) (.sub rT rT sY)

/-- Pop the top `x` of `S`: `LAB[x] := tVAL`. -/
def popBody : Stmt := .seq (dec tSSP) (.seq (ld sX tSS tSSP) (st tLAB sX tVAL))

/-- Pop the top group as a component. -/
def popComp : Stmt := .seq (whileC popCond popBody) (.seq (inc tVAL) (.seq (dec tBP) (dec tSP)))

/-- `sY := LAB[v]`, `sH := ` the head of `B`. -/
def finRead : Stmt := .seq (ld sY tLAB sV) headRead

/-- All arcs of the top `v` done: pop its group if it is the root, else pop `v`. -/
def finish : Stmt := .seq finRead (ifEq sY sH popComp (dec tSP))

/-- Non-empty search stack. -/
def topStep : Stmt := .seq topRead (ifLt sA sB advance finish)

/-- One step of the search. -/
def sccBody : Stmt := .ifz tSP rootStep topStep

/-- The loop test: `rT := (N - nxt) + |stk|` (zero iff the search has halted). -/
def sccCond : Stmt := .seq (.sub rT tN2 tNXT) (.add rT rT tSP)

/-- The initial state: empty stacks, `nxt := 0`, `tVAL := N + 1`. -/
def sccInit : Stmt :=
  .seq (.const tSP 0) (.seq (.const tSSP 0) (.seq (.const tBP 0) (.seq (.const tNXT 0)
    (addc tVAL tN2 1))))

/-- Step 5: the search. -/
def stepScc : Stmt := .seq sccInit (whileC sccCond sccBody)

/-! ### Loop-free blocks -/

section blocks

variable {n m : ℕ} {cl : List ℕ} {c₀ : Config} {s : State} {c : Config}

theorem wregs_visitT (x : ℕ) : wregs (visitT x) = [rT, rT, tSSP, rT, rT, rT, tBP, rT, rT, tSP] :=
  rfl
theorem loopFree_visitT (x : ℕ) : LoopFree (visitT x) := by simp [visitT, LoopFree]

/-- Visiting the vertex in register `x`. -/
theorem visitT_run (hcl : cl.length = 2 * m) (hok : CodesOk n cl) {x w : ℕ}
    (hx : x = tNXT ∨ x = sW) (hR : SrchRep n m cl c₀ s c) (hxw : c.reg x = w) (hw : w < 2 * n)
    (hS : s.S.length < 2 * n) (hB : s.B.length < 2 * n) (hstk : s.stk.length < 2 * n) :
    SrchRep n m cl c₀ (Scc.push s w) (run (visitT x) c) ∧
      ∀ r, r ≠ tSSP → r ≠ tBP → r ≠ tSP → r ≠ rT → (run (visitT x) c).reg r = c.reg r := by
  have hreg : ∀ r, r ≠ tSSP → r ≠ tBP → r ≠ tSP → r ≠ rT → (run (visitT x) c).reg r = c.reg r :=
    fun r h1 h2 h3 h4 => run_reg_of_not_mem (loopFree_visitT _)
      (by rw [wregs_visitT]; simp [h1, h2, h3, h4]) c
  have hx' : x ≠ rT ∧ x ≠ tSSP ∧ x ≠ tBP ∧ x ≠ tSP := by
    rcases hx with rfl | rfl <;> decide
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx'
  have hG := hR.glob
  refine ⟨⟨(Glob.regIndep n m c₀).run_of_sub (loopFree_visitT _) (by rw [wregs_visitT]; decide) hG,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, hreg⟩
  · simp +decide [visitT, run_inc, run_st, hR.sp, Scc.push, hx1]
  · simp +decide [visitT, run_inc, run_st, hR.ssp, Scc.push, hx1, hx2]
  · simp +decide [visitT, run_inc, run_st, hR.bp, Scc.push, hx1, hx2]
  · rw [hreg _ (by decide) (by decide) (by decide) (by decide)]; exact hR.nxt
  · rw [hreg _ (by decide) (by decide) (by decide) (by decide)]; exact hR.val
  · have := hR.mem.push hcl hok hw hS hB hstk
    simpa +decide [visitT, run_inc, run_st, hG.rss, hG.rlab, hG.rbb, hG.rstk, hR.sp, hR.ssp, hR.bp,
      hxw, hx1, hx2, hx3, hx4] using this

/-- The addresses of a visit: `SS + |S|`, `LAB + w`, `BB + |B|`, `STK + |stk|`. -/
theorem visitT_addrOK (hSp : endL n m (c₀.reg rFREE) ≤ S) {x w : ℕ} (hx : x = tNXT ∨ x = sW)
    (hR : SrchRep n m cl c₀ s c) (hxw : c.reg x = w) (hw : w < 2 * n)
    (hS : s.S.length < 2 * n) (hB : s.B.length < 2 * n) (hstk : s.stk.length < 2 * n) :
    AddrOK S (visitT x) c := by
  have := fits hSp
  have hG := hR.glob
  rcases hx with rfl | rfl <;>
    addr_ok [visitT, hG.rss, hG.rlab, hG.rbb, hG.rstk, hR.sp, hR.ssp, hR.bp, hxw]

/-- `tNXT++`. -/
theorem incNxt_run (hR : SrchRep n m cl c₀ s c) :
    SrchRep n m cl c₀ { s with nxt := s.nxt + 1 } (run (inc tNXT) c) := by
  rw [run_inc (by decide)]
  refine ⟨(Glob.regIndep n m c₀).setReg (by decide) _ ((Glob.regIndep n m c₀).setReg (by decide) _
    hR.glob), ?_, ?_, ?_, ?_, ?_, by simp only [setReg_mem]; exact hR.mem.setNxt _⟩
  · simp +decide [hR.sp]
  · simp +decide [hR.ssp]
  · simp +decide [hR.bp]
  · simp +decide [hR.nxt]
  · simp +decide [hR.val]

/-- Empty search stack: the next root candidate. -/
theorem rootStep_run (hSp : endL n m (c₀.reg rFREE) ≤ S) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) (hR : SrchRep n m cl c₀ s c)
    (hI : Scc.Inv (2 * n) (nbOf cl) s) (hst : s.stk = []) (hlt : s.nxt < 2 * n) :
    SrchRep n m cl c₀ (step (2 * n) (nbOf cl) s) (run rootStep c) ∧ AddrOK S rootStep c := by
  have hlab : c.mem (c.reg tLAB + c.reg tNXT) = s.lab s.nxt := by
    rw [hR.glob.rlab, hR.nxt]; exact hR.mem.tlab.get hlt
  have hR₁ : SrchRep n m cl c₀ s (run (ld sX tLAB tNXT) c) := by
    rw [run_ld]; exact (SrchRep.indep n m cl c₀ s).setReg (by decide) _ hR
  have hX₁ : (run (ld sX tLAB tNXT) c).reg sX = s.lab s.nxt := by simp [hlab]
  have hN₁ : (run (ld sX tLAB tNXT) c).reg tNXT = s.nxt := by simp +decide [hR.nxt]
  have hA₀ : AddrOK S (ld sX tLAB tNXT) c := by
    have := fits hSp
    addr_ok [hR.glob.rlab, hR.nxt]
  by_cases h0 : s.lab s.nxt = 0
  · obtain ⟨hS, hstk, hB⟩ := hI.room h0 hlt
    obtain ⟨hV, _⟩ := visitT_run hcl hok (Or.inl rfl) hR₁ hN₁ hlt hS hB hstk
    refine ⟨?_, hA₀.seq (AddrOK.seq (AddrOK.ifz (fun _ =>
      visitT_addrOK hSp (Or.inl rfl) hR₁ hN₁ hlt hS hB hstk) (fun h => absurd (hX₁ ▸ h) (by
        simp [h0]))) (AddrOK.of_memFree rfl))⟩
    simp only [rootStep, run_seq', run_ifz', hX₁, run_skip]
    rw [step_nil_visit hst hlt h0]
    simp only [h0, ↓reduceIte]
    exact incNxt_run hV
  · refine ⟨?_, hA₀.seq (AddrOK.seq (AddrOK.ifz (fun h => absurd (hX₁ ▸ h) h0) (fun _ => trivial))
      (AddrOK.of_memFree rfl))⟩
    simp only [rootStep, run_seq', run_ifz', hX₁, run_skip]
    rw [step_nil_skip hst hlt h0]
    simp only [h0, ↓reduceIte]
    exact incNxt_run hR₁

/-- The top of the search stack and its arc pointers. -/
theorem topRead_run (hR : SrchRep n m cl c₀ s c) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest)
    (hv : v < 2 * n) :
    (run topRead c).reg sV = v ∧
      (run topRead c).reg sA = ps (arcsOfCodes cl) v + s.ptr v ∧
      (run topRead c).reg sX = s.ptr v ∧
      (run topRead c).reg sB = ps (arcsOfCodes cl) v + (nbOf cl v).length ∧
      Agree [sP, sV, sA, sX, sB, rT] c (run topRead c) := by
  have hG := hR.glob
  have hsp : c.reg tSP = rest.length + 1 := by rw [hR.sp, hst]; rfl
  have hstkv : c.mem (bSTK n m (c₀.reg rFREE) + rest.length) = v := by
    have hs := hR.mem.stk
    rw [hst, List.reverse_cons, arr_append] at hs
    simpa using hs.2
  have hoff : c.mem (bOFF n m (c₀.reg rFREE) + v) = ps (arcsOfCodes cl) v :=
    hR.mem.csr.toff.get (by omega)
  have hoff1 : c.mem (bOFF n m (c₀.reg rFREE) + (v + 1)) =
      ps (arcsOfCodes cl) v + (nbOf cl v).length := by
    rw [hR.mem.csr.toff.get (by omega), ps_succ]; rfl
  have hptr : c.mem (bPTR n m (c₀.reg rFREE) + v) = s.ptr v := hR.mem.tptr.get hv
  refine ⟨?_, ?_, ?_, ?_, agree_run (by decide) rfl rfl (by decide) c⟩ <;>
    simp +decide [topRead, run_subc, run_addc, hG.rstk, hG.roff, hG.rptr, hsp, hstkv, hoff, hoff1,
      hptr]

/-- The addresses of `topRead`: `STK + |stk| - 1`, `OFF + v`, `PTR + v`, `OFF + v + 1`. -/
theorem topRead_addrOK (hSp : endL n m (c₀.reg rFREE) ≤ S) (hR : SrchRep n m cl c₀ s c)
    (hI : Scc.Inv (2 * n) (nbOf cl) s) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest)
    (hv : v < 2 * n) : AddrOK S topRead c := by
  have hG := hR.glob
  have hsp : c.reg tSP = rest.length + 1 := by rw [hR.sp, hst]; rfl
  have hstkv : c.mem (bSTK n m (c₀.reg rFREE) + rest.length) = v := by
    have hs := hR.mem.stk
    rw [hst, List.reverse_cons, arr_append] at hs
    simpa using hs.2
  have hl : rest.length + 1 ≤ s.S.length := by have := hI.stk_len; rw [hst] at this; simpa using this
  have := hI.S_len
  have := fits hSp
  addr_ok [topRead, hG.rstk, hG.roff, hG.rptr, hsp, hstkv]

theorem wregs_bumpV : wregs bumpV = [rT, sX, rT] := rfl

/-- The address of `bumpV`: `PTR + v`. -/
theorem bumpV_addrOK (hSp : endL n m (c₀.reg rFREE) ≤ S) (hR : SrchRep n m cl c₀ s c) {v : ℕ}
    (hv : v < 2 * n) (hV : c.reg sV = v) : AddrOK S bumpV c := by
  have := fits hSp
  addr_ok [bumpV, hR.glob.rptr, hV]

/-- `PTR[v]++`. -/
theorem bumpV_run (hcl : cl.length = 2 * m) (hok : CodesOk n cl) (hR : SrchRep n m cl c₀ s c)
    {v : ℕ} (hv : v < 2 * n) (hV : c.reg sV = v) (hX : c.reg sX = s.ptr v) :
    SrchRep n m cl c₀ (Scc.bump s v) (run bumpV c) ∧
      ∀ r, r ≠ sX → r ≠ rT → (run bumpV c).reg r = c.reg r := by
  have hreg : ∀ r, r ≠ sX → r ≠ rT → (run bumpV c).reg r = c.reg r := fun r h1 h2 =>
    run_reg_of_not_mem (by decide) (by rw [wregs_bumpV]; simp [h1, h2]) c
  have hG := hR.glob
  refine ⟨⟨(Glob.regIndep n m c₀).run_of_sub (by decide) (by decide) hG, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hreg⟩
  · rw [hreg _ (by decide) (by decide)]; exact hR.sp
  · rw [hreg _ (by decide) (by decide)]; exact hR.ssp
  · rw [hreg _ (by decide) (by decide)]; exact hR.bp
  · rw [hreg _ (by decide) (by decide)]; exact hR.nxt
  · rw [hreg _ (by decide) (by decide)]; exact hR.val
  · simpa +decide [bumpV, run_inc, run_st, hG.rptr, hV, hX] using hR.mem.bump hcl hok hv

theorem headD_eq_getLast {B : List ℕ} (hB : B ≠ []) :
    ∃ t, B.reverse = t ++ [B.headD 0] ∧ t.length + 1 = B.length := by
  cases B with
  | nil => exact absurd rfl hB
  | cons h t => exact ⟨t.reverse, by simp, by simp⟩

/-- The head of `B`. -/
theorem headRead_run (hR : SrchRep n m cl c₀ s c) (hB : s.B ≠ []) :
    (run headRead c).reg sH = s.B.headD 0 ∧ Agree [sP, sH, rT] c (run headRead c) := by
  have hG := hR.glob
  obtain ⟨t, ht, htl⟩ := headD_eq_getLast hB
  have hbb : c.mem (bBB n m (c₀.reg rFREE) + t.length) = s.B.headD 0 := by
    have hs := hR.mem.bb
    rw [ht, arr_append] at hs
    simpa using hs.2
  have hbp : c.reg tBP = t.length + 1 := by rw [hR.bp]; omega
  refine ⟨?_, agree_run (by decide) rfl rfl (by decide) c⟩
  simp +decide [headRead, run_subc, hG.rbb, hbp, hbb]

/-- The address of `headRead`: `BB + |B| - 1`. -/
theorem headRead_addrOK (hSp : endL n m (c₀.reg rFREE) ≤ S) (hR : SrchRep n m cl c₀ s c)
    (hI : Scc.Inv (2 * n) (nbOf cl) s) (hB : s.B ≠ []) : AddrOK S headRead c := by
  have hB1 : 1 ≤ s.B.length := List.length_pos_iff.mpr hB
  have := hI.B_len
  have := hI.S_len
  have := fits hSp
  addr_ok [headRead, hR.glob.rbb, hR.bp]

/-- The next arc of the top `v`. -/
theorem advance_run (hSp : endL n m (c₀.reg rFREE) ≤ S) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) (hR : SrchRep n m cl c₀ s c)
    (hI : Scc.Inv (2 * n) (nbOf cl) s) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest)
    (hv : v < 2 * n) (hV : c.reg sV = v) (hA : c.reg sA = ps (arcsOfCodes cl) v + s.ptr v)
    (hX : c.reg sX = s.ptr v) (hlt : s.ptr v < (nbOf cl v).length) :
    SrchRep n m cl c₀ (step (2 * n) (nbOf cl) s) (run advance c) ∧ AddrOK S advance c := by
  have hG := hR.glob
  set w := (nbOf cl v).getD (s.ptr v) 0 with hw_def
  have hwnb : w ∈ nbOf cl v := getD_mem hlt
  have hw : w < 2 * n := closed_nbOf hok v hv w hwnb
  have hadj : c.mem (c.reg tADJ + c.reg sA) = w := by
    rw [hG.radj, hA, ← Nat.add_assoc]; exact (hR.mem.csr.adj v hv).getD hlt
  have hlabw : c.mem (bLAB n m (c₀.reg rFREE) + w) = s.lab w := hR.mem.tlab.get hw
  -- after the two loads
  set c₂ := run (.seq (ld sW tADJ sA) (ld sY tLAB sW)) c with hc₂
  have hAg : Agree WS c c₂ := agree_run (by decide) rfl rfl (by decide) c
  have hR₂ : SrchRep n m cl c₀ s c₂ := (SrchRep.indep n m cl c₀ s) c c₂ hAg hR
  have hW₂ : c₂.reg sW = w := by simp +decide [hc₂, hadj]
  have hY₂ : c₂.reg sY = s.lab w := by simp +decide [hc₂, hadj, hG.rlab, hlabw]
  have hV₂ : c₂.reg sV = v := by simp +decide [hc₂, hV]
  have hX₂ : c₂.reg sX = s.ptr v := by simp +decide [hc₂, hX]
  have hlab₂ : c.mem (bADJ n m (c₀.reg rFREE) + (ps (arcsOfCodes cl) v + s.ptr v)) = w := by
    rw [← Nat.add_assoc]; exact (hR.mem.csr.adj v hv).getD hlt
  have hA₀ : AddrOK S (.seq (ld sW tADJ sA) (ld sY tLAB sW)) c := by
    have := fits hSp
    have hAl := length_arcsOfCodes m cl hcl
    have hps : ps (arcsOfCodes cl) (2 * n) = 2 * m := by
      rw [ps_total (fun e he => (mem_arcsOfCodes hok e he).1), hAl]
    have hu1 := ps_mono (arcsOfCodes cl) (show v + 1 ≤ 2 * n by omega)
    rw [ps_succ] at hu1
    have : (nbOf cl v).length = (outOf (arcsOfCodes cl) v).length := rfl
    addr_ok [hG.radj, hG.rlab, hA, hlab₂]
  have hrun : run advance c = run (.ifz sY (.seq bumpV (visitT sW))
      (.seq headRead (ifLt sY sH (dec tBP) bumpV))) c₂ := by
    simp only [advance, run_seq', hc₂]
  have hv' : v ∈ s.stk := by rw [hst]; exact List.mem_cons_self
  -- the address obligations of the branches, at `c₂`
  have hArest : AddrOK S (.ifz sY (.seq bumpV (visitT sW))
      (.seq headRead (ifLt sY sH (dec tBP) bumpV))) c₂ := by
    refine AddrOK.ifz (fun h0 => ?_) (fun h0 => ?_)
    · have h0' : s.lab w = 0 := by rw [← hY₂]; exact h0
      obtain ⟨hR₃, hr₃⟩ := bumpV_run hcl hok hR₂ hv hV₂ hX₂
      obtain ⟨hS, hstk, hB⟩ := hI.room h0' hw
      exact (bumpV_addrOK hSp hR₂ hv hV₂).seq (visitT_addrOK hSp (Or.inr rfl) hR₃
        (by rw [hr₃ _ (by decide) (by decide), hW₂]) hw hS hB hstk)
    · have hBne := hI.B_ne_of_stk hv'
      obtain ⟨hH, hAg₃⟩ := headRead_run hR₂ hBne
      have hR₃ : SrchRep n m cl c₀ s (run headRead c₂) :=
        (SrchRep.indep n m cl c₀ s).mono (by decide) _ _ hAg₃ hR₂
      refine (headRead_addrOK hSp hR₂ hI hBne).seq (AddrOK.ifLt (fun _ => AddrOK.of_memFree rfl)
        (fun _ => bumpV_addrOK hSp ((SrchRep.indep n m cl c₀ s).setReg (by decide) _ hR₃) hv ?_))
      simp +decide [hAg₃.reg sV (by decide), hV₂]
  have hAadv : AddrOK S advance c := by
    have h1 := hA₀
    simp only [addrOK_seq] at h1
    refine ⟨h1.1, h1.2, ?_⟩
    have : run (ld sY tLAB sW) (run (ld sW tADJ sA) c) = c₂ := by simp only [hc₂, run_seq']
    rw [this]; exact hArest
  refine ⟨?_, hAadv⟩
  rw [hrun, run_ifz', hY₂]
  by_cases h0 : s.lab w = 0
  · rw [step_visit hst hlt h0]
    simp only [h0, ↓reduceIte, run_seq']
    obtain ⟨hR₃, hr₃⟩ := bumpV_run hcl hok hR₂ hv hV₂ hX₂
    obtain ⟨hS, hstk, hB⟩ := hI.room h0 hw
    exact (visitT_run hcl hok (Or.inr rfl) hR₃ (by rw [hr₃ _ (by decide) (by decide), hW₂]) hw
      hS hB hstk).1
  · simp only [h0, ↓reduceIte, run_seq']
    have hBne := hI.B_ne_of_stk hv'
    obtain ⟨hH, hAg₃⟩ := headRead_run hR₂ hBne
    have hR₃ : SrchRep n m cl c₀ s (run headRead c₂) :=
      (SrchRep.indep n m cl c₀ s).mono (by decide) _ _ hAg₃ hR₂
    have hY₃ : (run headRead c₂).reg sY = s.lab w := by rw [hAg₃.reg _ (by decide), hY₂]
    rw [run_ifLt, hY₃, hH]
    by_cases hl : s.lab w < s.B.headD 0
    · rw [step_merge hst hlt h0 hl]
      simp only [hl, ↓reduceIte]
      have hR₄ := (SrchRep.indep n m cl c₀ s).setReg (d := rT) (by decide)
        (s.B.headD 0 - s.lab w) hR₃
      rw [run_dec (by decide)]
      refine ⟨(Glob.regIndep n m c₀).setReg (by decide) _ ((Glob.regIndep n m c₀).setReg
        (by decide) _ hR₄.glob), ?_, ?_, ?_, ?_, ?_, by simp only [setReg_mem]; exact
        hR₃.mem.tailB⟩
      · simp +decide [hR₃.sp]
      · simp +decide [hR₃.ssp]
      · simp +decide [hR₃.bp]
      · simp +decide [hR₃.nxt]
      · simp +decide [hR₃.val]
    · rw [step_adv hst hlt h0 hl]
      simp only [hl, ↓reduceIte]
      have hR₄ := (SrchRep.indep n m cl c₀ s).setReg (d := rT) (by decide)
        (s.B.headD 0 - s.lab w) hR₃
      exact (bumpV_run hcl hok hR₄ hv
        (by simp +decide [hAg₃.reg sV (by decide), hV₂])
        (by simp +decide [hAg₃.reg sX (by decide), hX₂])).1

/-- `sY := LAB[v]`, `sH := ` the head of `B`. -/
theorem finRead_run (hR : SrchRep n m cl c₀ s c) {v : ℕ} (hv : v < 2 * n) (hV : c.reg sV = v)
    (hB : s.B ≠ []) :
    (run finRead c).reg sY = s.lab v ∧ (run finRead c).reg sH = s.B.headD 0 ∧
      Agree [sY, sP, sH, rT] c (run finRead c) := by
  have hG := hR.glob
  have hlab : c.mem (bLAB n m (c₀.reg rFREE) + v) = s.lab v := hR.mem.tlab.get hv
  have hR₁ : SrchRep n m cl c₀ s (run (ld sY tLAB sV) c) := by
    rw [run_ld]; exact (SrchRep.indep n m cl c₀ s).setReg (by decide) _ hR
  obtain ⟨hH, hAg⟩ := headRead_run hR₁ hB
  refine ⟨?_, ?_, ?_⟩
  · simp only [finRead, run_seq']
    rw [hAg.reg sY (by decide)]
    simp [hG.rlab, hV, hlab]
  · simp only [finRead, run_seq']; exact hH
  · exact agree_run (by decide) rfl rfl (by decide) c

/-- The addresses of `finRead`: `LAB + v`, then those of `headRead`. -/
theorem finRead_addrOK (hSp : endL n m (c₀.reg rFREE) ≤ S) (hR : SrchRep n m cl c₀ s c)
    (hI : Scc.Inv (2 * n) (nbOf cl) s) {v : ℕ} (hv : v < 2 * n) (hV : c.reg sV = v)
    (hB : s.B ≠ []) : AddrOK S finRead c := by
  have hR₁ : SrchRep n m cl c₀ s (run (ld sY tLAB sV) c) := by
    rw [run_ld]; exact (SrchRep.indep n m cl c₀ s).setReg (by decide) _ hR
  refine AddrOK.seq ?_ (headRead_addrOK hSp hR₁ hI hB)
  have := fits hSp
  addr_ok [hR.glob.rlab, hV]

/-- Popping a finished non-root vertex. -/
theorem popStk_run (hR : SrchRep n m cl c₀ s c) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest) :
    SrchRep n m cl c₀ { s with stk := rest } (run (dec tSP) c) := by
  rw [run_dec (by decide)]
  refine ⟨(Glob.regIndep n m c₀).setReg (by decide) _ ((Glob.regIndep n m c₀).setReg (by decide) _
    hR.glob), ?_, ?_, ?_, ?_, ?_, by simp only [setReg_mem]; exact hR.mem.popStk hst⟩
  · simp +decide [hR.sp, hst]
  · simp +decide [hR.ssp]
  · simp +decide [hR.bp]
  · simp +decide [hR.nxt]
  · simp +decide [hR.val]

end blocks

/-! ### Popping a component -/

section pop

variable {n m : ℕ} {cl : List ℕ} {c₀ : Config} {s : State}

theorem SrchRep.toMid {c : Config} (hR : SrchRep n m cl c₀ s c) :
    SrchRep n m cl c₀ (mid (2 * n) s s.S.length) c :=
  ⟨hR.glob, hR.sp, by simp [mid, hR.ssp], hR.bp, hR.nxt, hR.val, hR.mem.toMid _⟩

/-- The invariant of the popping loop for the root label `h`: the machine represents
`mid N s k` for some `k ≥ h - 1`, and `rT = k + 1 - h`. -/
def PopInv (n m : ℕ) (cl : List ℕ) (c₀ : Config) (s : State) (h : ℕ) (c : Config) : Prop :=
  ∃ k, h - 1 ≤ k ∧ k ≤ s.S.length ∧ SrchRep n m cl c₀ (mid (2 * n) s k) c ∧ c.reg sY = h ∧
    c.reg rT = k + 1 - h

theorem popInit_spec (h : ℕ) (hh : h - 1 ≤ s.S.length) :
    HTB S popCond (fun c => SrchRep n m cl c₀ s c ∧ c.reg sY = h)
      (fun c => PopInv n m cl c₀ s h c ∧ c.reg tSSP - (h - 1) ≤ s.S.length - (h - 1)) 3 :=
    HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hR, hY⟩ => ?_
  have hR' := hR.toMid
  have hAg : Agree [rT] c (run popCond c) := agree_run (by decide) rfl rfl (by decide) c
  refine ⟨⟨s.S.length, hh, le_rfl, (SrchRep.indep n m cl c₀ _).mono (by decide) c _ hAg hR', ?_, ?_⟩,
    ?_⟩
  · rw [hAg.reg sY (by decide), hY]
  · simp +decide [popCond, run_addc, hR.ssp, hY]
  · rw [hAg.reg tSSP (by decide), hR.ssp]

theorem popRound_spec (hSp : endL n m (c₀.reg rFREE) ≤ S) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) (hI : Scc.Inv (2 * n) (nbOf cl) s) (h : ℕ) (hh1 : 1 ≤ h) (μ₀ : ℕ) :
    HTB S (.seq popBody popCond)
      (fun c => PopInv n m cl c₀ s h c ∧ c.reg rT ≠ 0 ∧ c.reg tSSP - (h - 1) = μ₀)
      (fun c => PopInv n m cl c₀ s h c ∧ c.reg tSSP - (h - 1) < μ₀) 9 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨k, hk1, hk2, hR, hY, hT⟩, hne, hμ⟩ => ?_
  have hkh : h ≤ k := by omega
  have hG := hR.glob
  have hssp : c.reg tSSP = k := by rw [hR.ssp]; simp [mid]; omega
  have hk0 : 0 < k := by omega
  have hxS : s.S[k - 1] ∈ s.S := List.getElem_mem _
  have hx : s.S[k - 1] < 2 * n := hI.S_lt hxS
  have hss : c.mem (bSS n m (c₀.reg rFREE) + (k - 1)) = s.S[k - 1] := by
    have := hR.mem.ss.get (i := k - 1) (by simp [mid]; omega)
    simpa [mid] using this
  have hval : c.reg tVAL = 2 * n + 1 + s.nc := by rw [hR.val]; rfl
  have hM := hR.mem.popOne hcl hok hk0 hk2 hx
  rw [hval.symm] at hM
  refine ⟨by
    have := hI.S_len
    have := fits hSp
    addr_ok [popBody, popCond, hG.rss, hG.rlab, hssp, hss], ?_⟩
  refine ⟨⟨k - 1, by omega, by omega, ⟨(Glob.regIndep n m c₀).run_of_sub (by decide) (by decide) hG,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simp +decide [popBody, popCond, run_dec, run_addc, run_st, hR.sp, mid]
  · simp +decide [popBody, popCond, run_dec, run_addc, run_st, hssp, mid]; omega
  · simp +decide [popBody, popCond, run_dec, run_addc, run_st, hR.bp, mid]
  · simp +decide [popBody, popCond, run_dec, run_addc, run_st, hR.nxt, mid]
  · simp +decide [popBody, popCond, run_dec, run_addc, run_st, hR.val, mid]
  · simpa +decide [popBody, popCond, run_dec, run_addc, run_st, hssp, hG.rss, hG.rlab, hss] using hM
  · simp +decide [popBody, popCond, run_dec, run_addc, run_st, hY]
  · simp +decide [popBody, popCond, run_dec, run_addc, run_st, hY, hssp]
  · simp +decide [popBody, popCond, run_dec, run_addc, run_st, hssp]; omega

theorem popTail_run {c : Config} {v : ℕ} {rest : List ℕ}
    (hR : SrchRep n m cl c₀ (mid (2 * n) s (s.lab v - 1)) c) (hst : s.stk = v :: rest)
    (hB : s.B ≠ []) :
    SrchRep n m cl c₀ (popc (2 * n) s v rest) (run (.seq (inc tVAL) (.seq (dec tBP) (dec tSP))) c) := by
  have hG := hR.glob
  rw [popc_eq]
  have hBl : s.B.length ≠ 0 := fun h => hB (List.length_eq_zero_iff.mp h)
  refine ⟨(Glob.regIndep n m c₀).run_of_sub (by decide) (by decide) hG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [run_inc, run_dec, hR.sp, mid, hst]
  · simp +decide [run_inc, run_dec, hR.ssp, mid]
  · simp +decide [run_inc, run_dec, hR.bp, mid]
  · simp +decide [run_inc, run_dec, hR.nxt, mid]
  · simp +decide [run_inc, run_dec, hR.val, mid]; ring
  · simp only [run_seq', run_inc (show tVAL ≠ rT by decide), run_dec (show tBP ≠ rT by decide),
      run_dec (show tSP ≠ rT by decide), setReg_mem]
    have h1 := hR.mem.tailB
    have h2 := h1.popStk (v := v) (rest := rest) (by simp [mid, hst])
    exact ⟨h2.csr, h2.tlab, h2.tptr, h2.stk, h2.ss, h2.bb, h2.zero⟩

/-- **Popping the top group** whose root `v` is finished: at most `10 p + 10` steps for the
`p = |S| - (lab v - 1)` vertices popped. -/
theorem popComp_spec (hSp : endL n m (c₀.reg rFREE) ≤ S) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl)
    (hI : Scc.Inv (2 * n) (nbOf cl) s) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest) :
    HTB S popComp (fun c => SrchRep n m cl c₀ s c ∧ c.reg sY = s.lab v)
      (SrchRep n m cl c₀ (popc (2 * n) s v rest)) (10 * (s.S.length - (s.lab v - 1)) + 10) := by
  have hv : v ∈ s.stk := by rw [hst]; exact List.mem_cons_self
  have hvl := hI.stk_S_lab hv
  have hB := hI.B_ne_of_stk hv
  have hl := HTB.whileC (cond := popCond) (body := popBody)
    (fun c => c.reg tSSP - (s.lab v - 1)) (popInit_spec (c₀ := c₀) (s.lab v) (by omega))
    (popRound_spec (c₀ := c₀) hSp hcl hok hI (s.lab v) hvl.1)
  have ht : HTB S (.seq (inc tVAL) (.seq (dec tBP) (dec tSP)))
      (fun c => PopInv n m cl c₀ s (s.lab v) c ∧ c.reg rT = 0)
      (SrchRep n m cl c₀ (popc (2 * n) s v rest)) 6 := HTB.of_HT rfl <|
    HT.run_le (by decide) (by decide) fun c ⟨⟨k, hk1, _, hR, _, hT⟩, h0⟩ => by
      obtain rfl : k = s.lab v - 1 := by omega
      exact popTail_run hR hst hB
  exact (hl.seq ht).weaken (by omega)

end pop

/-! ### One round -/

section round

variable {n m : ℕ} {cl : List ℕ} {c₀ : Config}

/-- The state after reading the top `v` of the search stack. -/
def TopP (n m : ℕ) (cl : List ℕ) (c₀ : Config) (s : State) (v : ℕ) (c : Config) : Prop :=
  SrchRep n m cl c₀ s c ∧ c.reg sV = v ∧ c.reg sA = ps (arcsOfCodes cl) v + s.ptr v ∧
    c.reg sX = s.ptr v ∧ c.reg sB = ps (arcsOfCodes cl) v + (nbOf cl v).length

theorem finish_spec (hSp : endL n m (c₀.reg rFREE) ≤ S) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) {s : State}
    (hI : Scc.Inv (2 * n) (nbOf cl) s) {v : ℕ} {rest : List ℕ} (hst : s.stk = v :: rest)
    (hv : v < 2 * n) (hlt : ¬ s.ptr v < (nbOf cl v).length) :
    HTB S finish (fun c => TopP n m cl c₀ s v c ∧ c.reg sB ≤ c.reg sA)
      (SrchRep n m cl c₀ (step (2 * n) (nbOf cl) s))
      (10 * (s.S.length - (step (2 * n) (nbOf cl) s).S.length) + 20) := by
  have hvs : v ∈ s.stk := by rw [hst]; exact List.mem_cons_self
  have hvl := hI.stk_S_lab hvs
  have hB := hI.B_ne_of_stk hvs
  have h1 : HTB S finRead (fun c => TopP n m cl c₀ s v c ∧ c.reg sB ≤ c.reg sA)
      (fun c => SrchRep n m cl c₀ s c ∧ c.reg sY = s.lab v ∧ c.reg sH = s.B.headD 0) 6 :=
    HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hV, _⟩, _⟩ => by
      obtain ⟨hY, hH, hAg⟩ := finRead_run hR hv hV hB
      exact ⟨finRead_addrOK hSp hR hI hv hV hB,
        (SrchRep.indep n m cl c₀ s).mono (by decide) _ _ hAg hR, hY, hH⟩
  by_cases hr : s.lab v = s.B.headD 0
  · rw [step_popc hst hlt hr]
    have hlen : (popc (2 * n) s v rest).S.length = s.lab v - 1 := by
      simp only [popc, List.length_take]; omega
    rw [hlen]
    refine (h1.seq (HTB.ifEq (B := 10 * (s.S.length - (s.lab v - 1)) + 10) (by decide) (by decide)
      (by indep [srchRep_iff, glob_iff]) ?_ (HTB.of_false fun c ⟨⟨_, hY, hH⟩, hne⟩ => hne
        (by rw [hY, hH, hr])))).weaken (by omega)
    exact (popComp_spec hSp hcl hok hI hst).pre fun c ⟨⟨hR, hY, _⟩, _⟩ => ⟨hR, hY⟩
  · rw [step_pop hst hlt hr]
    refine (h1.seq (HTB.ifEq (B := 2) (by decide) (by decide) (by indep [srchRep_iff, glob_iff])
      (HTB.of_false fun c ⟨⟨_, hY, hH⟩, he⟩ => hr (by rw [← hY, ← hH, he])) ?_)).weaken (by omega)
    exact HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hR, _, _⟩, _⟩ => popStk_run hR hst

/-- **One round of the search**: from a reachable non-halted state `s`, `sccBody` yields a
representation of `step s`, within `60` steps plus `10` per vertex popped from `S`. -/
theorem sccBody_spec (hSp : endL n m (c₀.reg rFREE) ≤ S) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) (s : State)
    (hI : Scc.Inv (2 * n) (nbOf cl) s) (hh : ¬ Halted (2 * n) s) :
    HTB S sccBody (SrchRep n m cl c₀ s) (SrchRep n m cl c₀ (step (2 * n) (nbOf cl) s))
      (60 + 10 * (s.S.length - (step (2 * n) (nbOf cl) s).S.length)) := by
  refine (HTB.ifz (b := 59 + 10 * (s.S.length - (step (2 * n) (nbOf cl) s).S.length))
    ?_ ?_).weaken (by omega)
  · by_cases hst : s.stk = []
    · have hlt : s.nxt < 2 * n := by
        by_contra h; exact hh ⟨hst, by omega⟩
      exact (HTB.run_le (by decide) (by decide : size rootStep ≤ 20) fun c ⟨hR, _⟩ =>
        (rootStep_run hSp hcl hok hR hI hst hlt).symm).weaken (by omega)
    · exact HTB.of_false fun c ⟨hR, h0⟩ =>
        hst (List.length_eq_zero_iff.mp (by rw [← hR.sp]; exact h0))
  · cases hst : s.stk with
    | nil => exact HTB.of_false fun c ⟨hR, h0⟩ => h0 (by rw [hR.sp, hst]; rfl)
    | cons v rest =>
      have hvs : v ∈ s.stk := by rw [hst]; exact List.mem_cons_self
      have hv : v < 2 * n := hI.S_lt (hI.stk_S v hvs)
      have h1 : HTB S topRead (fun c => SrchRep n m cl c₀ s c ∧ c.reg tSP ≠ 0)
          (TopP n m cl c₀ s v) 13 :=
        HTB.run_le (by decide) (by decide) fun c ⟨hR, _⟩ => by
          obtain ⟨hV, hA, hX, hB, hAg⟩ := topRead_run hR hst hv
          exact ⟨topRead_addrOK hSp hR hI hst hv,
            (SrchRep.indep n m cl c₀ s).mono (by decide) _ _ hAg hR, hV, hA, hX, hB⟩
      refine (h1.seq (HTB.ifLt (B := 44 + 10 * (s.S.length - (step (2 * n) (nbOf cl) s).S.length))
        (by decide) (by decide) (by indep [TopP, srchRep_iff, glob_iff]) ?_ ?_)).weaken (by omega)
      · by_cases hlt : s.ptr v < (nbOf cl v).length
        · exact (HTB.run_le (by decide) (by decide : size advance ≤ 35)
            fun c ⟨⟨hR, hV, hA, hX, _⟩, _⟩ =>
              (advance_run hSp hcl hok hR hI hst hv hV hA hX hlt).symm).weaken (by omega)
        · exact HTB.of_false fun c ⟨⟨_, _, hA, _, hB⟩, hab⟩ => hlt (by rw [hA, hB] at hab; omega)
      · by_cases hlt : s.ptr v < (nbOf cl v).length
        · exact HTB.of_false fun c ⟨⟨_, _, hA, _, hB⟩, hab⟩ => by rw [hA, hB] at hab; omega
        · exact (finish_spec hSp hcl hok hI hst hv hlt).weaken (by omega)

end round

end STACS2027.Runtimes.TwoSat
