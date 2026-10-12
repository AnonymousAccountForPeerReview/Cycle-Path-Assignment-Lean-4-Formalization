module

public import Outerplanar.RAM.EarScan
import Mathlib.Tactic

/-!
# The ear-elimination machine: the peeling, and the whole initialization

The peeling `peelProg` (`EarProg.lean`) runs the abstract peeling of
`Outerplanar/Algo/EarPeel.lean` on the adjacency lists `initAdj L` built by the initialization,
within any bound `S ≥ bEND F N |L|`; its regions (`PD`, `PRM`, `PSTK`, `OUT1`, `OUT2`) lie between
`F` and `bHD`, below the regions of the elimination, which it does not touch.

* `PMem`, `PRep`: the memory and the machine holding a state `p` of the peeling (with the state
  `Ear.init N L` of the elimination from `bHD` on); one lemma per kind of store
  (`PMem.setPD`, `PMem.setRM`, `PMem.push`, `PMem.setO1`, `PMem.setO2`);
* `pInitBody_spec`: the loop `PD[i] := DEG[i]`, stacking the vertices of degree at most two,
  builds `Ear.pinit N (initAdj L)`;
* `pScanStep`, `pScan_spec`: the scan of the list of the removed vertex `x` (lowering the degrees
  of its alive neighbours, recording the first two);
* `pRound_spec`, `peel_spec`: one round is `Ear.premove` (for every input: the invariant
  `Ear.PInv` holds, so the stack has at most `N` entries), it costs at most `38` times the drop of
  the potential `Ear.ppot`; the peeling ends with an empty stack in at most
  `38 (N + 2 |L|) + 2` steps. With the hypothesis that `L` has an outerplanar Hamiltonian cycle,
  `Ear.peel_orient` turns the result into the orientation the elimination reads;
* `init_spec`: the whole initialization (allocations, edges, stack, peeling).
-/

@[expose] public section

namespace STACS2027.RAM.EarR

open STACS2027 STACS2027.Ear

variable {N : ℕ} {L : List Edge} {F : ℕ} {S : ℕ}

/-! ### The memory of the peeling -/

/-- The memory during the peeling: the initial state of the elimination from `bHD` on (`EMem`
with the current memory frozen below `bHD`), the regions of the peeling holding `p`, the memory
below `F` that of `mi`. -/
structure PMem (N : ℕ) (L : List Edge) (F : ℕ) (mi : ℕ → ℕ) (np : ℕ) (p : PState) (m : ℕ → ℕ) :
    Prop where
  em : EMem N L.length F m (init N L) (fun _ => 0) [] np m
  pd : Tab m (bPD F) N p.pd
  rm : Tab m (bPRM F N) N (fun x => if p.rm x = true then 1 else 0)
  stk : Arr m (bPSTK F N) p.stack.reverse
  stkS : p.stack.length ≤ N
  o1 : Tab m (bO1 F N) N p.o1
  o2 : Tab m (bO2 F N) N p.o2
  low : SameOn (· < F) mi m

/-- The machine during the peeling, in the state `p`. -/
@[mk_iff] structure PRep (N : ℕ) (L : List Edge) (F : ℕ) (mi : ℕ → ℕ) (p : PState) (c : Config) :
    Prop where
  glob : Glob N L.length F c
  sp : c.reg rSP = (init N L).stack.length
  cnt : c.reg rCNT = N
  lc : c.reg rLC = 0
  np1 : 1 ≤ c.reg rNP
  npb : c.reg rNP + 2 * N ≤ poolSz N L.length
  psp : c.reg rPSP = p.stack.length
  mem : PMem N L F mi (c.reg rNP) p c.mem

theorem PRep.indep (N : ℕ) (L : List Edge) (F : ℕ) (mi : ℕ → ℕ) (p : PState) :
    Indep [rT, rI, rA, rB, rV, rU, rW, rX, rK, rP, rQ, rZ, rD, rY, rC] (PRep N L F mi p) := by
  indep [pRep_iff, glob_iff]

/-- The machine holds the initial state of the elimination. -/
theorem PRep.lrep {mi : ℕ → ℕ} {p : PState} {c : Config} (h : PRep N L F mi p c) :
    LRep N L F c.mem (init N L) c :=
  ⟨h.glob, h.sp, h.cnt, h.lc, h.np1, h.npb, h.mem.em⟩

/-- The registers the peeling writes. -/
def WP : List ℕ := [rT, rI, rA, rB, rV, rU, rW, rX, rK, rP, rQ, rZ, rD, rY, rC, rPSP]

/-- A step of the machine that keeps the registers outside `WP`. -/
theorem PRep.step {mi : ℕ → ℕ} {p p' : PState} {c c' : Config} (h : PRep N L F mi p c)
    (hreg : ∀ r, r ∉ WP → c'.reg r = c.reg r) (hpsp : c'.reg rPSP = p'.stack.length)
    (hm : PMem N L F mi (c.reg rNP) p' c'.mem) : PRep N L F mi p' c' := by
  have hsub : ∀ r ∈ WP, r ∈ WV := by decide
  have hnp := hreg rNP (by decide)
  refine ⟨(Glob.regIndep _ _ _) c c' (fun r hr => hreg r fun h' => hr (hsub r h')) h.glob,
    (hreg rSP (by decide)).trans h.sp, (hreg rCNT (by decide)).trans h.cnt,
    (hreg rLC (by decide)).trans h.lc, by rw [hnp]; exact h.np1, by rw [hnp]; exact h.npb, hpsp,
    by rw [hnp]; exact hm⟩

theorem reg_of_WP {s : Stmt} (hs : LoopFree s) (hW : ∀ r ∈ wregs s, r ∈ WP) (c : Config) :
    ∀ r, r ∉ WP → (run s c).reg r = c.reg r :=
  fun r hr => run_reg_of_not_mem hs (fun h => hr (hW r h)) c

namespace PMem

variable {mi m : ℕ → ℕ} {np : ℕ} {p : PState}

theorem congr (h : PMem N L F mi np p m) {p' : PState} (h1 : p'.pd = p.pd) (h2 : p'.rm = p.rm)
    (h3 : p'.stack = p.stack) (h4 : p'.o1 = p.o1) (h5 : p'.o2 = p.o2) : PMem N L F mi np p' m :=
  ⟨h.em, h1 ▸ h.pd, h2 ▸ h.rm, h3 ▸ h.stk, h3 ▸ h.stkS, h4 ▸ h.o1, h5 ▸ h.o2, h.low⟩

theorem setPD (h : PMem N L F mi np p m) {x : ℕ} (hx : x < N) (d : ℕ) :
    PMem N L F mi np { p with pd := Function.update p.pd x d } (upd m (bPD F + x) d) :=
  have := h.stkS
  ⟨h.em.updLow (by lomega) _, h.pd.upd rfl, h.rm.upd_of_disjoint (by lomega),
    h.stk.upd_of_disjoint (by simp; lomega), h.stkS, h.o1.upd_of_disjoint (by lomega),
    h.o2.upd_of_disjoint (by lomega), h.low.upd_of_ge (by lomega) _⟩

theorem setRM (h : PMem N L F mi np p m) {x : ℕ} (hx : x < N) :
    PMem N L F mi np { p with rm := Function.update p.rm x true } (upd m (bPRM F N + x) 1) := by
  have := h.stkS
  refine ⟨h.em.updLow (by lomega) _, h.pd.upd_of_disjoint (by lomega), ?_,
    h.stk.upd_of_disjoint (by simp; lomega), h.stkS, h.o1.upd_of_disjoint (by lomega),
    h.o2.upd_of_disjoint (by lomega), h.low.upd_of_ge (by lomega) _⟩
  refine (h.rm.upd (i := x) (v := 1) rfl).congr_fun fun y _ => ?_
  by_cases hy : y = x
  · subst hy; simp
  · simp [Function.update_of_ne hy]

theorem push (h : PMem N L F mi np p m) (y : ℕ) (hS : p.stack.length + 1 ≤ N) :
    PMem N L F mi np { p with stack := y :: p.stack } (upd m (bPSTK F N + p.stack.length) y) := by
  refine ⟨h.em.updLow (by lomega) _, h.pd.upd_of_disjoint (by lomega),
    h.rm.upd_of_disjoint (by lomega), ?_, by simpa using hS, h.o1.upd_of_disjoint (by lomega),
    h.o2.upd_of_disjoint (by lomega), h.low.upd_of_ge (by lomega) _⟩
  simpa using h.stk.upd_snoc (x := y) (by simp)

theorem pop (h : PMem N L F mi np p m) {x : ℕ} {rest : List ℕ} (hs : p.stack = x :: rest) :
    PMem N L F mi np { p with stack := rest } m := by
  have hstk := h.stk
  rw [hs, List.reverse_cons] at hstk
  have hS := h.stkS
  rw [hs] at hS
  exact ⟨h.em, h.pd, h.rm, hstk.prefix, by simp at hS ⊢; omega, h.o1, h.o2, h.low⟩

theorem setO1 (h : PMem N L F mi np p m) {x : ℕ} (hx : x < N) (y : ℕ) :
    PMem N L F mi np { p with o1 := Function.update p.o1 x y } (upd m (bO1 F N + x) y) :=
  have := h.stkS
  ⟨h.em.updLow (by lomega) _, h.pd.upd_of_disjoint (by lomega), h.rm.upd_of_disjoint (by lomega),
    h.stk.upd_of_disjoint (by simp; lomega), h.stkS, h.o1.upd rfl,
    h.o2.upd_of_disjoint (by lomega), h.low.upd_of_ge (by lomega) _⟩

theorem setO2 (h : PMem N L F mi np p m) {x : ℕ} (hx : x < N) (y : ℕ) :
    PMem N L F mi np { p with o2 := Function.update p.o2 x y } (upd m (bO2 F N + x) y) :=
  have := h.stkS
  ⟨h.em.updLow (by lomega) _, h.pd.upd_of_disjoint (by lomega), h.rm.upd_of_disjoint (by lomega),
    h.stk.upd_of_disjoint (by simp; lomega), h.stkS, h.o1.upd_of_disjoint (by lomega),
    h.o2.upd rfl, h.low.upd_of_ge (by lomega) _⟩

end PMem

/-! ### The degrees of the peeling -/

/-- The state of the peeling after the first `j` rounds of the degree loop. -/
def pPre (adj : ℕ → List ℕ) (j : ℕ) : PState where
  rm := fun _ => false
  pd := fun x => if x < j then (adj x).length else 0
  stack := (pstackPre adj j).reverse
  o1 := fun _ => 0
  o2 := fun _ => 0

theorem pPre_N (adj : ℕ → List ℕ) (m : ℕ → ℕ) {mi : ℕ → ℕ} {np : ℕ}
    (h : PMem N L F mi np (pPre adj N) m) : PMem N L F mi np (pinit N adj) m := by
  refine ⟨h.em, h.pd.congr_fun fun i hi => ?_, h.rm, h.stk, h.stkS, h.o1, h.o2, h.low⟩
  simp [pPre, pinit, hi]

theorem pstackPre_succ (adj : ℕ → List ℕ) (j : ℕ) :
    pstackPre adj (j + 1) = pstackPre adj j ++ (if (adj j).length ≤ 2 then [j] else []) := by
  simp only [pstackPre, List.range_succ, List.filter_append, List.filter_singleton]
  split_ifs with h <;> simp [h]

theorem length_pstackPre_le (adj : ℕ → List ℕ) (j : ℕ) : (pstackPre adj j).length ≤ j := by
  have := List.length_filter_le (fun x => decide ((adj x).length ≤ 2)) (List.range j)
  simpa [pstackPre] using this

theorem ppush_mem {x : ℕ} (hx : x ≠ rT) (c : Config) :
    (run (ppush x) c).mem = upd c.mem (c.reg rPSTK + c.reg rPSP) (c.reg x) := by
  simp +decide only [ppush, run_seq', run_st hx, run_inc (show rPSP ≠ rT by decide), setReg_mem,
    setMem_mem_upd]

theorem ppush_psp {x : ℕ} (hx : x ≠ rT) (c : Config) :
    (run (ppush x) c).reg rPSP = c.reg rPSP + 1 := by
  simp +decide only [ppush, run_seq', run_st hx, run_inc (show rPSP ≠ rT by decide), setReg_reg,
    setMem_reg, ↓reduceIte]

theorem pInitBody_spec {mi : ℕ → ℕ} (hS : bEND F N L.length ≤ S) (j : ℕ) (hj : j < N) :
    HTB S pInitBody (fun c => PRep N L F mi (pPre (initAdj L) j) c ∧ c.reg rI = j ∧ c.reg gVN = N)
      (fun c => PRep N L F mi (pPre (initAdj L) (j + 1)) c ∧ c.reg rI = j ∧ c.reg gVN = N) 12 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hi, hn⟩ => ?_
  have hg := hR.glob
  have hlen := length_pstackPre_le (initAdj L) j
  have hpsp := hR.psp
  simp only [pPre, List.length_reverse] at hpsp
  have hd : c.mem (bDEG F N + j) = (initAdj L j).length := hR.mem.em.deg.get hj
  refine ⟨by ear_addr [pInitBody, ppush, hg.deg, hg.pd, hg.pstk, hi, hpsp], ?_⟩
  have hreg := reg_of_WP (s := pInitBody) (by decide) (by decide) c
  have hfr : ∀ r, r ∉ wregs pInitBody → (run pInitBody c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (by decide) hr c
  set d := (initAdj L j).length with hdd
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = run (.seq (ld rD rDEG rI) (st rPD rI rD)) c := ⟨_, rfl⟩
  have hD₁ : c₁.reg rD = d := by rw [hc₁]; simp +decide [run_st, hg.deg, hi, hd]
  have hm₁ : c₁.mem = upd c.mem (bPD F + j) d := by
    rw [hc₁]; simp +decide [run_st, hg.deg, hi, hd, hg.pd]
  have hr₁ : ∀ r, r ≠ rD → r ≠ rT → c₁.reg r = c.reg r := fun r h1 h2 => by
    rw [hc₁]; exact run_reg_of_not_mem (by decide) (by simp [h1, h2]) c
  have hM₁ := hR.mem.setPD hj d
  rw [← hm₁] at hM₁
  have hrun : run pInitBody c = if d ≤ 2 then run (ppush rI) (c₁.setReg rT (d - 2))
      else c₁.setReg rT (d - 2) := by
    rw [show run pInitBody c = run (ifLe rD rTWO (ppush rI) .skip) c₁ by rw [hc₁]; rfl, run_ifLe,
      hD₁, hr₁ rTWO (by decide) (by decide), hg.two, run_skip]
  have hpd : Function.update (pPre (initAdj L) j).pd j d = (pPre (initAdj L) (j + 1)).pd := by
    funext y
    by_cases hy : y = j
    · subst hy; simp [pPre, hdd]
    · simp only [pPre, Function.update_of_ne hy]
      split_ifs <;> first | rfl | omega
  have hsucc : pstackPre (initAdj L) (j + 1) =
      pstackPre (initAdj L) j ++ (if d ≤ 2 then [j] else []) := pstackPre_succ _ _
  refine ⟨hR.step hreg ?_ ?_, (hfr rI (by decide)).trans hi, (hfr gVN (by decide)).trans hn⟩
  · rw [hrun]
    by_cases h2 : d ≤ 2
    · simp only [h2, ↓reduceIte] at hsucc ⊢
      rw [ppush_psp (by decide)]
      simp +decide [hr₁, hpsp, pPre, hsucc]
    · simp only [h2, ↓reduceIte, List.append_nil] at hsucc ⊢
      simp +decide [hr₁, hpsp, pPre, hsucc]
  · rw [hrun]
    by_cases h2 : d ≤ 2
    · simp only [h2, ↓reduceIte] at hsucc ⊢
      have hM₂ := hM₁.push j (by simp [pPre]; omega)
      rw [ppush_mem (by decide)]
      simp only [setReg_mem, setReg_reg, show rPSTK ≠ rT by decide, show rPSP ≠ rT by decide,
        show rI ≠ rT by decide, ↓reduceIte]
      rw [hr₁ rPSTK (by decide) (by decide), hr₁ rPSP (by decide) (by decide),
        hr₁ rI (by decide) (by decide), hg.pstk, hpsp, hi]
      simp only [pPre, List.length_reverse] at hM₂
      exact hM₂.congr hpd.symm rfl (by simp [pPre, hsucc]) rfl rfl
    · simp only [h2, ↓reduceIte, List.append_nil] at hsucc ⊢
      simp only [setReg_mem]
      exact hM₁.congr hpd.symm rfl (by simp [pPre, hsucc]) rfl rfl

/-! ### The scan of the list of the removed vertex -/

/-- The state after popping and removing `x`. -/
def pTop (p : PState) (x : ℕ) (rest : List ℕ) : PState :=
  { p with stack := rest, rm := Function.update p.rm x true }

theorem premove_eq (adj : ℕ → List ℕ) (p : PState) (x : ℕ) (rest : List ℕ) :
    premove adj { p with stack := rest } x =
      { (alive (pTop p x rest).rm (adj x)).foldl pdec (pTop p x rest) with
        o1 := Function.update p.o1 x ((alive (pTop p x rest).rm (adj x)).getD 0 x),
        o2 := Function.update p.o2 x ((alive (pTop p x rest).rm (adj x)).getD 1 x) } := rfl

/-- During the scan of the list of `x` the stack stays within the final one, which has at most
`N` entries (`PInv`). -/
theorem stack_take_le {adj : ℕ → List ℕ} (hA : AdjOK N adj) {p : PState} (hP : PInv N adj p)
    {x : ℕ} {rest : List ℕ} (hs : p.stack = x :: rest) (k : ℕ) :
    ((alive (pTop p x rest).rm ((adj x).take k)).foldl pdec (pTop p x rest)).stack.length ≤ N := by
  have hfin := (hP.step hA hs).length_le
  have hnd : (alive (pTop p x rest).rm (adj x)).Nodup := (hA.nodup x).filter _
  have hsub : (alive (pTop p x rest).rm ((adj x).take k)).Sublist
      (alive (pTop p x rest).rm (adj x)) := (List.take_sublist _ _).filter _
  have hfinst : (premove adj { p with stack := rest } x).stack =
      ((alive (pTop p x rest).rm (adj x)).filter fun y => (pTop p x rest).pd y - 1 = 2).reverse ++
        (pTop p x rest).stack := foldl_pdec_stack hnd _
  rw [foldl_pdec_stack (hnd.sublist hsub)]
  rw [hfinst] at hfin
  simp only [List.length_append, List.length_reverse] at hfin ⊢
  have := (hsub.filter (fun y => decide ((pTop p x rest).pd y - 1 = 2))).length_le
  omega

/-- An alive entry `y` (in `rX`) of the list of the removed vertex: `pUpd` records it, lowers
its degree, stacks it at two (`Ear.pdec`). -/
theorem pUpd_run {mi : ℕ → ℕ} {q : PState} {c : Config} (hR : PRep N L F mi q c) {y : ℕ}
    (hX : c.reg rX = y) (hy : y < N) (hpush : q.pd y - 1 = 2 → q.stack.length + 1 ≤ N)
    (hS : bEND F N L.length ≤ S) :
    AddrOK S pUpd c ∧ PRep N L F mi (pdec q y) (run pUpd c) ∧
      (run pUpd c).reg rK = c.reg rK + 1 ∧
      (run pUpd c).reg rU = (if c.reg rK = 0 then y else c.reg rU) ∧
      (run pUpd c).reg rW = (if c.reg rK = 1 then y else c.reg rW) ∧
      (∀ r, r ∉ [rU, rW, rQ, rT, rK, rD, rPSP] → (run pUpd c).reg r = c.reg r) ∧
      (∀ a, bHD F N ≤ a → (run pUpd c).mem a = c.mem a) := by
  have hg := hR.glob
  have hpdy : c.mem (bPD F + y) = q.pd y := hR.mem.pd.get hy
  have hpsp := hR.psp
  have hreg := reg_of_WP (s := pUpd) (by decide) (by decide) c
  refine ⟨by ear_addr [pUpd, scanUpd, ppush, hg.pd, hg.pstk, hg.two, hX, hpdy, hpsp], ?_⟩
  obtain ⟨c₃, hc₃⟩ : ∃ c₃, c₃ = run scanUpd c := ⟨_, rfl⟩
  have hr₃ : ∀ r, r ∉ [rU, rW, rQ, rT, rK] → c₃.reg r = c.reg r := fun r hr => by
    rw [hc₃]; exact scanUpd_reg c hr
  have hm₃ : c₃.mem = c.mem := by rw [hc₃]; exact run_mem_of_stores (by decide) (by decide) c
  obtain ⟨c₄, hc₄⟩ : ∃ c₄, c₄ = run (.seq (ld rD rPD rX) (.seq (dec rD) (st rPD rX rD))) c₃ :=
    ⟨_, rfl⟩
  have hX₃ : c₃.reg rX = y := (hr₃ rX (by decide)).trans hX
  have hPD₃ : c₃.reg rPD = bPD F := (hr₃ rPD (by decide)).trans hg.pd
  have hD₄ : c₄.reg rD = q.pd y - 1 := by
    rw [hc₄]; simp +decide [run_st, run_dec, hX₃, hPD₃, hm₃, hpdy]
  have hm₄ : c₄.mem = upd c.mem (bPD F + y) (q.pd y - 1) := by
    rw [hc₄]; simp +decide [run_st, run_dec, hX₃, hPD₃, hm₃, hpdy]
  have hr₄ : ∀ r, r ≠ rD → r ≠ rT → c₄.reg r = c₃.reg r := fun r h1 h2 => by
    rw [hc₄]; exact run_reg_of_not_mem (by decide) (by simp [h1, h2]) c₃
  have hrun : run pUpd c = run (ifEq rD rTWO (ppush rX) .skip) c₄ := by rw [hc₄, hc₃]; rfl
  have hM₄ := hR.mem.setPD hy (q.pd y - 1)
  rw [← hm₄] at hM₄
  have hsp₄ : c₄.reg rPSP = q.stack.length := by
    rw [hr₄ _ (by decide) (by decide), hr₃ _ (by decide), hpsp]
  have hK₄ : c₄.reg rK = c.reg rK + 1 := by
    rw [hr₄ _ (by decide) (by decide), hc₃, scanUpd_K]
  have hU₄ : c₄.reg rU = (if c.reg rK = 0 then y else c.reg rU) := by
    rw [hr₄ _ (by decide) (by decide), hc₃, scanUpd_U, hX]
  have hW₄ : c₄.reg rW = (if c.reg rK = 1 then y else c.reg rW) := by
    rw [hr₄ _ (by decide) (by decide), hc₃, scanUpd_W, hX]
  have hhd : ∀ a, bHD F N ≤ a → c₄.mem a = c.mem a := fun a ha => by
    rw [hm₄, upd_apply, ite_eq_right_iff.mpr (fun h => absurd h (by lomega))]
  rw [hrun, run_ifEq (by decide) (by decide), hD₄, hr₄ rTWO (by decide) (by decide),
    hr₃ rTWO (by decide), hg.two]
  have hst : (pdec q y).stack = if q.pd y - 1 = 2 then y :: q.stack else q.stack := rfl
  by_cases h2 : q.pd y - 1 = 2
  · simp only [h2, ↓reduceIte]
    have hM₅ := hM₄.push y (by simpa using hpush h2)
    have hregs : ∀ r, r ≠ rT → r ≠ rPSP → (run (ppush rX) (c₄.setReg rT 0)).reg r = c₄.reg r :=
      fun r h1 h2 => by
        rw [run_reg_of_not_mem (by decide) (by simp [ppush, h1, h2]) (c₄.setReg rT 0)]
        simp [h1]
    have hmem5 : (run (ppush rX) (c₄.setReg rT 0)).mem =
        upd c₄.mem (bPSTK F N + q.stack.length) y := by
      rw [ppush_mem (by decide)]
      simp only [setReg_mem, setReg_reg, show rPSTK ≠ rT by decide, show rPSP ≠ rT by decide,
        show rX ≠ rT by decide, ↓reduceIte]
      rw [hr₄ _ (by decide) (by decide), hr₃ _ (by decide), hg.pstk, hsp₄,
        hr₄ _ (by decide) (by decide), hX₃]
    refine ⟨hR.step (fun r hr => ?_) ?_ ?_, ?_, ?_, ?_, fun r hr => ?_, fun a ha => ?_⟩
    · have := hreg r hr; rwa [hrun, run_ifEq (by decide) (by decide), hD₄,
        hr₄ rTWO (by decide) (by decide), hr₃ rTWO (by decide), hg.two, ite_eq_left h2] at this
    · rw [ppush_psp (by decide)]
      simp +decide [hsp₄, hst, h2]
    · rw [hmem5]
      exact hM₅.congr rfl rfl (by simp [hst, h2]) rfl rfl
    · rw [hregs _ (by decide) (by decide), hK₄]
    · rw [hregs _ (by decide) (by decide), hU₄]
    · rw [hregs _ (by decide) (by decide), hW₄]
    · have hr' : r ≠ rT ∧ r ≠ rPSP ∧ r ≠ rD ∧ r ∉ [rU, rW, rQ, rT, rK] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; omega
      rw [hregs _ hr'.1 hr'.2.1, hr₄ _ hr'.2.2.1 hr'.1, hr₃ _ hr'.2.2.2]
    · rw [hmem5, upd_apply, ite_eq_right_iff.mpr (fun h => absurd h (by lomega)), hhd a ha]
  · simp only [h2, ↓reduceIte, run_skip]
    refine ⟨hR.step (fun r hr => ?_) ?_ ?_, ?_, ?_, ?_, fun r hr => ?_, fun a ha => ?_⟩
    · have := hreg r hr; rwa [hrun, run_ifEq (by decide) (by decide), hD₄,
        hr₄ rTWO (by decide) (by decide), hr₃ rTWO (by decide), hg.two, ite_eq_right h2,
        run_skip] at this
    · simp +decide [hsp₄, hst, h2]
    · simp only [setReg_mem]
      exact hM₄.congr rfl rfl (by simp [hst, h2]) rfl rfl
    · simp +decide [hK₄]
    · simp +decide [hU₄]
    · simp +decide [hW₄]
    · have hr' : r ≠ rT ∧ r ≠ rD ∧ r ∉ [rU, rW, rQ, rT, rK] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; omega
      simp only [setReg_reg, hr'.1, ↓reduceIte]
      rw [hr₄ _ hr'.2.1 hr'.1, hr₃ _ hr'.2.2]
    · simp only [setReg_mem]; exact hhd a ha

theorem getD_snoc_d (l : List ℕ) (a i d : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp only [Option.getD_none]

/-- The first two entries of a list grown by one entry, recorded as `scanUpd` does. -/
theorem first_two_snoc (l : List ℕ) (a d : ℕ) :
    (l ++ [a]).getD 0 d = (if l.length = 0 then a else l.getD 0 d) ∧
      (l ++ [a]).getD 1 d = (if l.length = 1 then a else l.getD 1 d) := by
  rw [getD_snoc_d, getD_snoc_d]
  constructor
  · by_cases h : l.length = 0
    · simp [h]
    · simp [h, Nat.pos_of_ne_zero h]
  · by_cases h0 : l.length = 0
    · have : l = [] := List.length_eq_zero_iff.mp h0
      simp [this]
    · by_cases h1 : l.length = 1
      · simp [h1]
      · have : 1 < l.length := by omega
        simp [h1, this]

/-- The invariant of the scan of the list `initAdj L x` of the removed vertex `x` after `j`
entries, from the state `p1` (just after the removal). -/
def PScanInv (N : ℕ) (L : List Edge) (F : ℕ) (mi : ℕ → ℕ) (p1 : PState) (x j : ℕ) (c : Config) :
    Prop :=
  PRep N L F mi ((alive p1.rm ((initAdj L x).take j)).foldl pdec p1) c ∧ c.reg rV = x ∧
    j ≤ (initAdj L x).length ∧
    LL c.mem (bVAL F N) (bNXT F N L.length) (c.reg rNP) (c.reg rP) ((initAdj L x).drop j) ∧
    c.reg rT = c.reg rP ∧ c.reg rK = (alive p1.rm ((initAdj L x).take j)).length ∧
    c.reg rU = (alive p1.rm ((initAdj L x).take j)).getD 0 x ∧
    c.reg rW = (alive p1.rm ((initAdj L x).take j)).getD 1 x

/-- One entry of the scan of the list of the removed vertex. -/
theorem pScanStep (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) (hnd : L.Nodup)
    (hS : bEND F N L.length ≤ S) {mi : ℕ → ℕ} {p : PState} (hP : PInv N (initAdj L) p)
    {x : ℕ} {rest : List ℕ} (hs : p.stack = x :: rest) (j : ℕ) :
    HTB S (.seq pScanBody scanCond)
      (fun c => PScanInv N L F mi (pTop p x rest) x j c ∧ c.reg rT ≠ 0)
      (PScanInv N L F mi (pTop p x rest) x (j + 1)) 36 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hV, hj, hll, hT, hK, hU, hW⟩, hT0⟩ => ?_
  have hA := adjOK_initAdj hL hnd
  have hg := hR.glob
  have hP0 : c.reg rP ≠ 0 := by rw [← hT]; exact hT0
  have hjl : j < (initAdj L x).length := by
    by_contra h
    rw [List.drop_eq_nil_of_le (by omega)] at hll
    exact hP0 hll
  rw [List.drop_eq_getElem_cons hjl] at hll
  obtain ⟨_, hpn, hval, hnext⟩ := hll
  set y := (initAdj L x)[j] with hydef
  set p1 := pTop p x rest with hp1
  set q := (alive p1.rm ((initAdj L x).take j)).foldl pdec p1 with hq
  have hy : y < N := hA.lt x _ (List.getElem_mem hjl)
  have hqrm : q.rm = p1.rm := foldl_pdec_rm _ _
  have hrmy := hR.mem.rm.get hy
  rw [hqrm] at hrmy
  have hnpS := hR.mem.em.npS
  have hsucc := alive_take_succ p1.rm (initAdj L x) j hjl
  have hfr : ∀ r, r ∉ wregs (.seq pScanBody scanCond) →
      (run (.seq pScanBody scanCond) c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (by decide) hr c
  have hfst := first_two_snoc (alive p1.rm ((initAdj L x).take j)) y x
  -- the two reads
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = run (.seq (ld rX rVAL rP) (ld rQ rPRM rX)) c := ⟨_, rfl⟩
  have hX₂ : c₂.reg rX = y := by rw [hc₂]; simp +decide [hg.val, hval]
  have hQ₂ : c₂.reg rQ = if p1.rm y = true then 1 else 0 := by
    rw [hc₂]; simp +decide [hg.val, hval, hg.prm, hrmy]
  have hm₂ : c₂.mem = c.mem := by rw [hc₂]; exact run_mem_of_stores (by decide) (by decide) c
  have hr₂ : ∀ r, r ≠ rX → r ≠ rQ → c₂.reg r = c.reg r := fun r h1 h2 => by
    rw [hc₂]; simp [h1, h2]
  have hR₂ : PRep N L F mi q c₂ :=
    hR.step (fun r hr => by rw [hc₂]; exact reg_of_WP (by decide) (by decide) c r hr)
      (by rw [hr₂ _ (by decide) (by decide)]; exact hR.psp) (by rw [hm₂]; exact hR.mem)
  have hc2 : run (ld rQ rPRM rX) (run (ld rX rVAL rP) c) = c₂ := by rw [hc₂]; rfl
  have hAB : AddrOK S (ld rX rVAL rP) c ∧ AddrOK S (ld rQ rPRM rX) (run (ld rX rVAL rP) c) := by
    constructor
    · ear_addr [hg.val]
    · ear_addr [hg.val, hg.prm, hval]
  have hrun : run (.seq pScanBody scanCond) c =
      run scanCond (run (ld rP rNXT rP) (run (.ifz rQ pUpd .skip) c₂)) := by rw [hc₂]; rfl
  by_cases hdy : p1.rm y = true
  · -- a removed entry: skipped
    have hQ0 : c₂.reg rQ ≠ 0 := by rw [hQ₂, hdy]; decide
    have hifz : run (.ifz rQ pUpd .skip) c₂ = c₂ := by rw [run_ifz', ite_eq_right hQ0]; rfl
    have hsucc' : alive p1.rm ((initAdj L x).take (j + 1)) = alive p1.rm ((initAdj L x).take j) := by
      rw [hsucc, hdy]; simp
    have hD : AddrOK S (ld rP rNXT rP) c₂ := (addrOK_ld _ _ _).mpr (by
      rw [hr₂ _ (by decide) (by decide), hr₂ _ (by decide) (by decide), hg.nxt]; lomega)
    refine ⟨AddrOK.seq (AddrOK.seq hAB.1 (AddrOK.seq hAB.2 (by
      rw [hc2]; exact AddrOK.seq (AddrOK.ifz (fun h => absurd h hQ0) (fun _ => trivial))
        (by rw [hifz]; exact hD)))) (AddrOK.of_memFree rfl), ?_⟩
    rw [hrun, hifz]
    have hm7 : (run scanCond (run (ld rP rNXT rP) c₂)).mem = c.mem := by
      simp [scanCond, hm₂]
    have hreg7 : ∀ r, r ≠ rP → r ≠ rT → (run scanCond (run (ld rP rNXT rP) c₂)).reg r = c₂.reg r :=
      fun r h1 h2 => by simp [scanCond, h1, h2]
    have hP7 : (run scanCond (run (ld rP rNXT rP) c₂)).reg rP = c.mem (bNXT F N L.length + c.reg rP) := by
      simp +decide [scanCond, hm₂, hr₂ rNXT (by decide) (by decide), hr₂ rP (by decide) (by decide),
        hg.nxt]
    refine ⟨?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsucc']
      refine hR.step (fun r hr => ?_) ?_ (by rw [hm7]; exact hR.mem)
      · rw [← hifz, ← hrun]; exact reg_of_WP (by decide) (by decide) c r hr
      · rw [hreg7 _ (by decide) (by decide), hr₂ _ (by decide) (by decide)]; exact hR.psp
    · rw [hreg7 _ (by decide) (by decide), hr₂ _ (by decide) (by decide)]; exact hV
    · rw [hm7, hP7, hreg7 _ (by decide) (by decide), hr₂ _ (by decide) (by decide)]
      exact hnext
    · simp [scanCond, hg.zero, hr₂]
    · rw [hreg7 _ (by decide) (by decide), hr₂ _ (by decide) (by decide), hsucc']; exact hK
    · rw [hreg7 _ (by decide) (by decide), hr₂ _ (by decide) (by decide), hsucc']; exact hU
    · rw [hreg7 _ (by decide) (by decide), hr₂ _ (by decide) (by decide), hsucc']; exact hW
  · -- an alive entry: `pUpd`
    have hdy' : p1.rm y = false := by simpa using hdy
    have hQ0 : c₂.reg rQ = 0 := by rw [hQ₂, hdy']; rfl
    have hifz : run (.ifz rQ pUpd .skip) c₂ = run pUpd c₂ := by rw [run_ifz', ite_eq_left hQ0]
    have hsucc' : alive p1.rm ((initAdj L x).take (j + 1)) =
        alive p1.rm ((initAdj L x).take j) ++ [y] := by rw [hsucc, hdy']; simp [hydef]
    have hfold : (alive p1.rm ((initAdj L x).take (j + 1))).foldl pdec p1 = pdec q y := by
      rw [hsucc', List.foldl_append]; rfl
    have hpush : q.pd y - 1 = 2 → q.stack.length + 1 ≤ N := fun h2 => by
      have := stack_take_le hA hP hs (j + 1)
      rw [hfold] at this
      simpa [pdec, h2] using this
    obtain ⟨hAU, hR₃, hK₃, hU₃, hW₃, hr₃, hm₃⟩ := pUpd_run hR₂ hX₂ hy hpush hS
    set c₃ := run pUpd c₂ with hc₃
    have hP₃ : c₃.reg rP = c.reg rP := by
      rw [hr₃ rP (by decide), hr₂ _ (by decide) (by decide)]
    have hNXT₃ : c₃.reg rNXT = bNXT F N L.length := by
      rw [hr₃ rNXT (by decide), hr₂ _ (by decide) (by decide), hg.nxt]
    have hD : AddrOK S (ld rP rNXT rP) c₃ := (addrOK_ld _ _ _).mpr (by
      rw [hP₃, hNXT₃]; lomega)
    refine ⟨AddrOK.seq (AddrOK.seq hAB.1 (AddrOK.seq hAB.2 (by
      rw [hc2]; exact AddrOK.seq (AddrOK.ifz (fun _ => hAU) (fun h => absurd hQ0 h))
        (by rw [hifz]; exact hD)))) (AddrOK.of_memFree rfl), ?_⟩
    rw [hrun, hifz]
    have hm7 : (run scanCond (run (ld rP rNXT rP) c₃)).mem = c₃.mem := by simp [scanCond]
    have hreg7 : ∀ r, r ≠ rP → r ≠ rT → (run scanCond (run (ld rP rNXT rP) c₃)).reg r = c₃.reg r :=
      fun r h1 h2 => by simp [scanCond, h1, h2]
    have hnx : c₃.mem (bNXT F N L.length + c.reg rP) = c.mem (bNXT F N L.length + c.reg rP) := by
      rw [hm₃ _ (by lomega), hm₂]
    have hP7 : (run scanCond (run (ld rP rNXT rP) c₃)).reg rP =
        c.mem (bNXT F N L.length + c.reg rP) := by
      simp +decide [scanCond, hP₃, hNXT₃, hnx]
    have hK₂ : c₂.reg rK = c.reg rK := hr₂ _ (by decide) (by decide)
    have hU₂ : c₂.reg rU = c.reg rU := hr₂ _ (by decide) (by decide)
    have hW₂ : c₂.reg rW = c.reg rW := hr₂ _ (by decide) (by decide)
    refine ⟨?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfold]
      refine hR₃.step (fun r hr => ?_) ?_ (by rw [hm7]; exact hR₃.mem)
      · exact reg_of_WP (s := .seq (ld rP rNXT rP) scanCond) (by decide) (by decide) c₃ r hr
      · rw [hreg7 _ (by decide) (by decide)]; exact hR₃.psp
    · rw [hreg7 _ (by decide) (by decide), hr₃ _ (by decide), hr₂ _ (by decide) (by decide)]
      exact hV
    · rw [hm7, hP7, hreg7 _ (by decide) (by decide), hr₃ _ (by decide),
        hr₂ _ (by decide) (by decide)]
      refine hnext.congr fun q' hq0 hqn => ⟨?_, ?_⟩
      · rw [hm₃ _ (by lomega), hm₂]
      · rw [hm₃ _ (by lomega), hm₂]
    · simp [scanCond, hg.zero, hr₃, hr₂]
    · rw [hreg7 _ (by decide) (by decide), hK₃, hK₂, hsucc', List.length_append, hK]; rfl
    · rw [hreg7 _ (by decide) (by decide), hU₃, hK₂, hU₂, hsucc', hfst.1, ← hK, hU]
    · rw [hreg7 _ (by decide) (by decide), hW₃, hK₂, hW₂, hsucc', hfst.2, ← hK, hW]

/-- **The scan** of the list of the removed vertex `x`: the alive neighbours lose a degree (the
fold of `Ear.pdec`), the first two are left in `rU`, `rW` (`x` if missing). -/
theorem pScan_spec (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) (hnd : L.Nodup)
    (hS : bEND F N L.length ≤ S) {mi : ℕ → ℕ} {p : PState} (hP : PInv N (initAdj L) p)
    {x : ℕ} {rest : List ℕ} (hs : p.stack = x :: rest) :
    HTB S pScan (fun c => PRep N L F mi (pTop p x rest) c ∧ c.reg rV = x)
      (fun c => PRep N L F mi ((alive (pTop p x rest).rm (initAdj L x)).foldl pdec (pTop p x rest))
          c ∧ c.reg rV = x ∧ c.reg rU = (alive (pTop p x rest).rm (initAdj L x)).getD 0 x ∧
        c.reg rW = (alive (pTop p x rest).rm (initAdj L x)).getD 1 x)
      (7 + (1 + (37 * (initAdj L x).length + 1))) := by
  have hxN : x < N := hP.lt x (by rw [hs]; exact List.mem_cons_self ..)
  have hinit : HTB S pScanInit (fun c => PRep N L F mi (pTop p x rest) c ∧ c.reg rV = x)
      (fun c => PRep N L F mi (pTop p x rest) c ∧ c.reg rV = x ∧ c.reg rK = 0 ∧ c.reg rU = x ∧
        c.reg rW = x ∧ c.reg rP = c.mem (bHD F N + x)) 7 :=
    HTB.run_le (by decide) (by decide) fun c ⟨hR, hV⟩ => by
      refine ⟨by ear_addr [pScanInit, hR.glob.hd, hV],
        ((PRep.indep N L F mi _).mono (by decide)).run (by decide) (by decide) (by decide) hR, ?_⟩
      simp +decide [pScanInit, run_mov, hV, hR.glob.hd]
  have hcond : HTB S scanCond (fun c => PRep N L F mi (pTop p x rest) c ∧ c.reg rV = x ∧
      c.reg rK = 0 ∧ c.reg rU = x ∧ c.reg rW = x ∧ c.reg rP = c.mem (bHD F N + x))
      (PScanInv N L F mi (pTop p x rest) x 0) 1 :=
    HTB.run_le (by decide) (by decide) fun c ⟨hR, hV, hK, hU, hW, hPP⟩ => by
      refine ⟨trivial, ?_⟩
      have hll := hR.mem.em.adj x hxN
      have hR' : PRep N L F mi (pTop p x rest) (run scanCond c) :=
        ((PRep.indep N L F mi _).mono (by decide)).run (by decide) (by decide) (by decide) hR
      refine ⟨by simpa [alive] using hR', by simp +decide [scanCond, hV], Nat.zero_le _, ?_, ?_, ?_, ?_,
        ?_⟩
      · simp +decide only [scanCond, run_add, setReg_reg, setReg_mem, ↓reduceIte, List.drop_zero, hPP]
        exact hll
      · simp +decide [scanCond, hR.glob.zero]
      · simp +decide [scanCond, hK, alive]
      · simp +decide [scanCond, hU, alive]
      · simp +decide [scanCond, hW, alive]
  have hloop := HTB.whileG (cond := scanCond) (body := pScanBody)
    (PScanInv N L F mi (pTop p x rest) x) (fun j => 37 * ((initAdj L x).length - j)) 0 hcond
    fun j c ⟨hI, hT0⟩ => by
      have hjl : j < (initAdj L x).length := by
        obtain ⟨_, _, hj, hll, hT, _⟩ := hI
        by_contra h
        rw [List.drop_eq_nil_of_le (by omega)] at hll
        exact hT0 (by rw [hT]; exact hll)
      exact HTB.toG (pScanStep hL hnd hS hP hs j) (by omega) c ⟨hI, hT0⟩
  refine (hinit.seq hloop).mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨j, ⟨hR, hV, hj, hll, hT, _, hU, hW⟩, hT0⟩
  have hjl : j = (initAdj L x).length := by
    rw [hT] at hT0
    rw [hT0] at hll
    have := hll.eq_zero_iff.mp rfl
    rw [List.drop_eq_nil_iff] at this
    omega
  subst hjl
  rw [List.take_length] at hR hU hW
  exact ⟨hR, hV, hU, hW⟩

/-- Pop `x` and remove it. -/
theorem pPop_spec (hS : bEND F N L.length ≤ S) {mi : ℕ → ℕ} {p : PState}
    (hP : PInv N (initAdj L) p) {x : ℕ} {rest : List ℕ} (hs : p.stack = x :: rest) :
    HTB S pPop (PRep N L F mi p) (fun c => PRep N L F mi (pTop p x rest) c ∧ c.reg rV = x) 6 := by
  refine HTB.run_le (by decide) (by decide) fun c hR => ?_
  have hg := hR.glob
  have hxN : x < N := hP.lt x (by rw [hs]; exact List.mem_cons_self ..)
  have hstk := hR.mem.stk
  rw [hs, List.reverse_cons] at hstk
  have hpsp : c.reg rPSP = rest.length + 1 := by rw [hR.psp, hs, List.length_cons]
  have hrv : c.mem (bPSTK F N + rest.length) = x := by
    have := hstk.get (i := rest.length) (by simp)
    rw [this, List.getElem_append_right (by simp)]
    simp
  have hS' := hR.mem.stkS
  rw [hs, List.length_cons] at hS'
  refine ⟨by ear_addr [pPop, hg.pstk, hg.prm, hpsp, hrv], ?_⟩
  have hV : (run pPop c).reg rV = x := by
    simp +decide [pPop, run_st, run_dec, hpsp, hg.pstk, hrv]
  have hmem : (run pPop c).mem = upd c.mem (bPRM F N + x) 1 := by
    simp +decide [pPop, run_st, run_dec, hpsp, hg.pstk, hrv, hg.prm, hg.one]
  have hpsp' : (run pPop c).reg rPSP = rest.length := by
    simp +decide [pPop, run_st, run_dec, hpsp]
  refine ⟨hR.step (reg_of_WP (by decide) (by decide) c) hpsp' ?_, hV⟩
  rw [hmem]
  exact (hR.mem.pop hs).setRM hxN

/-- Record the two out-neighbours `u`, `w` of `x`. -/
theorem pOut_spec (hS : bEND F N L.length ≤ S) {mi : ℕ → ℕ} {q : PState} {x u w : ℕ}
    (hxN : x < N) :
    HTB S (.seq (st rO1 rV rU) (st rO2 rV rW))
      (fun c => PRep N L F mi q c ∧ c.reg rV = x ∧ c.reg rU = u ∧ c.reg rW = w)
      (PRep N L F mi { q with o1 := Function.update q.o1 x u, o2 := Function.update q.o2 x w })
      4 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hV, hU, hW⟩ => ?_
  have hg := hR.glob
  refine ⟨by ear_addr [hg.o1, hg.o2, hV], ?_⟩
  have hmem : (run (.seq (st rO1 rV rU) (st rO2 rV rW)) c).mem =
      upd (upd c.mem (bO1 F N + x) u) (bO2 F N + x) w := by
    simp +decide [run_st, hg.o1, hg.o2, hV, hU, hW]
  refine hR.step (reg_of_WP (by decide) (by decide) c) ?_ ?_
  · simp +decide [run_st, hR.psp]
  · rw [hmem]
    exact (hR.mem.setO1 hxN u).setO2 hxN w

/-- The test of the peeling loop. -/
theorem pCond_spec {mi : ℕ → ℕ} {q : PState} :
    HTB S pCond (PRep N L F mi q) (fun c => PRep N L F mi q c ∧ (c.reg rT = 0 ↔ q.stack = [])) 1 :=
  HTB.run_le (by decide) (by decide) fun c hR => by
    refine ⟨trivial, ((PRep.indep N L F mi q).mono (by decide)).run (by decide) (by decide)
      (by decide) hR, ?_⟩
    simp +decide [pCond, hR.glob.zero, hR.psp, List.length_eq_zero_iff]

/-- **One round of the peeling**: `Ear.premove` (for every input). -/
theorem pRound_spec (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) (hnd : L.Nodup)
    (hS : bEND F N L.length ≤ S) {mi : ℕ → ℕ} {p : PState} (hP : PInv N (initAdj L) p)
    {x : ℕ} {rest : List ℕ} (hs : p.stack = x :: rest) :
    HTB S (.seq pBody pCond) (PRep N L F mi p)
      (fun c => PRep N L F mi (premove (initAdj L) { p with stack := rest } x) c ∧
        (c.reg rT = 0 ↔ (premove (initAdj L) { p with stack := rest } x).stack = []))
      (6 + (7 + (1 + (37 * (initAdj L x).length + 1)) + 4) + 1) := by
  have hxN : x < N := hP.lt x (by rw [hs]; exact List.mem_cons_self ..)
  have hO := pOut_spec (L := L) (mi := mi) (S := S) hS
    (q := (alive (pTop p x rest).rm (initAdj L x)).foldl pdec (pTop p x rest))
    (u := (alive (pTop p x rest).rm (initAdj L x)).getD 0 x)
    (w := (alive (pTop p x rest).rm (initAdj L x)).getD 1 x) hxN
  have hO' := hO.post (Q' := PRep N L F mi (premove (initAdj L) { p with stack := rest } x))
    fun c hc => by
      refine ⟨hc.glob, hc.sp, hc.cnt, hc.lc, hc.np1, hc.npb, hc.psp, hc.mem.congr rfl rfl rfl ?_ ?_⟩
      · rw [premove_eq]; simp [foldl_pdec_o1, pTop]
      · rw [premove_eq]; simp [foldl_pdec_o2, pTop]
  have h := (pPop_spec hS hP hs).seq ((pScan_spec hL hnd hS hP hs).seq hO')
  exact h.seq pCond_spec

/-- The invariant of the peeling loop, after each test. -/
def PLInv (N : ℕ) (L : List Edge) (F : ℕ) (mi : ℕ → ℕ) (p : PState) (c : Config) : Prop :=
  PRep N L F mi p c ∧ PInv N (initAdj L) p ∧ (c.reg rT = 0 ↔ p.stack = [])

/-- **The peeling loop** stops with an empty stack, in at most `38 ppot + 2` steps (for every
input). -/
theorem peelLoop_spec (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) (hnd : L.Nodup)
    (hS : bEND F N L.length ≤ S) (mi : ℕ → ℕ) :
    HTB S (whileC pCond pBody) (PRep N L F mi (pinit N (initAdj L)))
      (fun c => ∃ p, PRep N L F mi p c ∧ PInv N (initAdj L) p ∧ p.stack = [])
      (1 + (38 * ppot N (initAdj L) (pinit N (initAdj L)) + 1)) := by
  have hA := adjOK_initAdj hL hnd
  have hinit : HTB S pCond (PRep N L F mi (pinit N (initAdj L)))
      (PLInv N L F mi (pinit N (initAdj L))) 1 :=
    pCond_spec.post fun c ⟨hR, hT⟩ => ⟨hR, pinv_init, hT⟩
  have hl := HTB.whileG (cond := pCond) (body := pBody) (PLInv N L F mi)
    (fun p => 38 * ppot N (initAdj L) p) (pinit N (initAdj L)) hinit fun p c ⟨⟨hR, hP, hT⟩, hT0⟩ => by
      have hne : p.stack ≠ [] := fun h => hT0 (hT.mpr h)
      obtain ⟨x, rest, hs⟩ := List.exists_cons_of_ne_nil hne
      have hpot := ppot_step hP hs
      exact HTB.toG (y := premove (initAdj L) { p with stack := rest } x)
        (((pRound_spec hL hnd hS hP hs).post fun c' ⟨hR', hT'⟩ =>
          ⟨hR', hP.step hA hs, hT'⟩).pre (P' := fun c => PLInv N L F mi p c ∧ c.reg rT ≠ 0)
          fun c' h => h.1.1) (by omega) c ⟨⟨hR, hP, hT⟩, hT0⟩
  exact hl.post fun c ⟨p, ⟨hR, hP, hT⟩, hT0⟩ => ⟨p, hR, hP, hT.mp hT0⟩

theorem sum_adj_succ {N : ℕ} {L : List Edge} (hL : ∀ e ∈ L, e.1 < N ∧ e.2 < N) :
    ∑ x ∈ Finset.range N, ((initAdj L x).length + 1) = 2 * L.length + N := by
  rw [Finset.sum_add_distrib, sum_initAdj hL]
  simp

/-- **The peeling** (degrees, then the loop), for every input, in at most
`16 N + 3 + 38 (N + 2 |L|) + 2` steps. -/
theorem peel_spec (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) (hnd : L.Nodup)
    (hS : bEND F N L.length ≤ S) (mi : ℕ → ℕ) :
    HTB S peelProg (fun c => PRep N L F mi (pPre (initAdj L) 0) c ∧ c.reg gVN = N)
      (fun c => ∃ p, PRep N L F mi p c ∧ PInv N (initAdj L) p ∧ p.stack = [])
      (N * (12 + 4) + 3 + (1 + (38 * (N + 2 * L.length) + 1))) := by
  have hL' : ∀ e ∈ L, e.1 < N ∧ e.2 < N := fun e he => ⟨by have := hL e he; omega, (hL e he).2⟩
  have h1 := HTB.forUpC (S := S) (i := rI) (n := gVN) (N := N) (body := pInitBody)
    (fun j => PRep N L F mi (pPre (initAdj L) j)) 12 (by decide) (by decide) (by decide)
    (fun j => (PRep.indep N L F mi _).mono (by decide))
    (fun j hj => pInitBody_spec (mi := mi) hS j hj)
  have h2 := (peelLoop_spec hL hnd hS mi).pre (P' := fun c => PRep N L F mi (pPre (initAdj L) N) c ∧
    c.reg rI = N ∧ c.reg gVN = N) fun c ⟨hR, _, _⟩ =>
      ⟨hR.glob, hR.sp, hR.cnt, hR.lc, hR.np1, hR.npb, hR.psp, pPre_N _ _ hR.mem⟩
  have hp := ppot_le N (initAdj L) (pinit N (initAdj L))
  rw [sum_adj_succ hL'] at hp
  exact (h1.seq h2).weaken (by omega)

/-- **The initialization** with the peeling: from `EarIn N L`, the machine holds `Ear.init N L`
(the memory below `bHD` being the one left by the peeling), the memory below `F` is the initial
one, and a stopped peeling state (stack empty) is stored in `OUT1`, `OUT2` (for every input). -/
theorem init_spec (N : ℕ) (L : List Edge) (c₀ : Config) (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N)
    (hnd : L.Nodup) (hS : bEND (c₀.reg rFREE) N L.length ≤ S) :
    HTB S initProg (fun c => EarIn N L c ∧ c = c₀)
      (fun c => LRep N L (c₀.reg rFREE) c.mem (init N L) c ∧
        SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        ∃ p, PInv N (initAdj L) p ∧ p.stack = [] ∧ Tab c.mem (bO1 (c₀.reg rFREE) N) N p.o1 ∧
          Tab c.mem (bO2 (c₀.reg rFREE) N) N p.o2)
      (64 + (L.length * (40 + 4) + 3 + (N * (12 + 4) + 3)) +
        (N * (12 + 4) + 3 + (1 + (38 * (N + 2 * L.length) + 1)))) := by
  refine HTB.of_forall fun c₁ ⟨hE, hc⟩ => ?_
  subst hc
  have h0 := (init0_spec N L c₁ hL hS).pre (P' := fun c => c = c₁) fun c hc => by
    subst hc; exact ⟨hE, rfl⟩
  have hz : ZeroFrom c₁.mem (c₁.reg rFREE) := hE.free
  have hp := (peel_spec hL hnd hS c₁.mem).pre (P' := fun c => LRep N L (c₁.reg rFREE) c₁.mem
    (init N L) c ∧ c.reg rPSP = 0) fun c ⟨hR, hpsp⟩ => by
      have hlow : ∀ a, c₁.reg rFREE ≤ a → a < bHD (c₁.reg rFREE) N → c.mem a = 0 := fun a h1 h2 => by
        rw [hR.mem.same a h2]; exact hz a h1
      refine ⟨⟨hR.glob, hR.sp, hR.cnt, hR.lc, hR.np1, hR.npb, by simp [hpsp, pPre, pstackPre], ?_⟩,
        hR.glob.vn⟩
      refine ⟨hR.mem.rebase, fun i hi => ?_, fun i hi => ?_, by simp [pPre, pstackPre], by
        simp [pPre, pstackPre], fun i hi => ?_, fun i hi => ?_,
        hR.mem.same.mono fun a (ha : a < c₁.reg rFREE) => show a < bHD (c₁.reg rFREE) N by lomega⟩
      · simp only [pPre, Nat.not_lt_zero, ↓reduceIte]; exact hlow _ (by lomega) (by lomega)
      · simp only [pPre, Bool.false_eq_true, ↓reduceIte]; exact hlow _ (by lomega) (by lomega)
      · exact hlow _ (by lomega) (by lomega)
      · exact hlow _ (by lomega) (by lomega)
  refine (h0.seq hp).post fun c ⟨p, hR, hP, hs⟩ => ⟨hR.lrep, hR.mem.low, p, hP, hs, hR.mem.o1,
    hR.mem.o2⟩

end STACS2027.RAM.EarR
