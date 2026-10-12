module

public import Runtimes.C4.RamBase
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Phase ORIENT: the out-lists of the peeling orientation

From a `PeelPost g` configuration `c₀` (first free address `F`), the program `orient`

1. allocates `ODEG` (`N` cells at `F`) and `OADJ` (`2 |E|` cells at `F + N`);
2. for every vertex `v < N` (`forUp xV gN orientBody`): scans the neighbours `w = ADJ[i]`,
   `i ∈ [OFF[v], OFF[v + 1])` (`forRange xI xOv xB orientInner`), appends `w` to the segment
   `OADJ[OFF[v] + ·]` when `POS[v] < POS[w]`, and stores the count in `ODEG[v]`.

The segment of `v` then holds `outL g (peelPos g) v` (`R1.ps E v = OFF[v]`, the segments
lie inside the CSR segments since `|outL v| ≤ |nb v|`). **`orient_spec`**: `OrientPost g`
within `CO · (m + 1)` steps, without output, storing only at or above `F`, accessing only the
addresses below any `S ≥ orientEnd g F = F + N + 2 |E|`.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM Finset

/-! ### The program -/

/-- Allocation of `ODEG` and `OADJ`. -/
def orientAlloc : Stmt := .seq (alloc gODEG gN) (.seq (.add xA gNE gNE) (alloc gOADJ xA))

/-- One neighbour `w = ADJ[xI]` of `v = xV`: append it to the out-list if it is later. -/
def orientInner : Stmt :=
  .seq (ld xW gADJ xI) (.seq (ld xX gPOS xV) (.seq (ld xY gPOS xW)
    (ifLt xX xY (.seq (.add xQ xOv xS) (.seq (st gOADJ xQ xW) (inc xS))) .skip)))

/-- `xOv := OFF[v]`, `xB := OFF[v + 1]`, `xS := 0`. -/
def orientPre : Stmt :=
  .seq (ld xOv gOFF xV) (.seq (addc xQ xV 1) (.seq (ld xB gOFF xQ) (.const xS 0)))

/-- One vertex `v = xV`. -/
def orientBody : Stmt :=
  .seq orientPre (.seq (forRange xI xOv xB orientInner) (st gODEG xV xS))

/-- **Phase ORIENT.** -/
def orient : Stmt := .seq orientAlloc (forUp xV gN orientBody)

/-! ### Representation -/

/-- The registers fixed during ORIENT (after the allocation). -/
@[mk_iff] structure OGlob (g : Graph) (c₀ c : Config) : Prop where
  n : c.reg gN = numV g
  off : c.reg gOFF = c₀.reg gOFF
  adj : c.reg gADJ = c₀.reg gADJ
  pos : c.reg gPOS = c₀.reg gPOS
  odeg : c.reg gODEG = c₀.reg rFREE
  oadj : c.reg gOADJ = c₀.reg rFREE + numV g
  free : c.reg rFREE = c₀.reg rFREE + numV g + 2 * (idEdges g).length

/-- The end of ORIENT's memory. -/
def orientEnd (g : Graph) (F : ℕ) : ℕ := F + numV g + 2 * (idEdges g).length

/-- The memory after the vertices `u < v`. -/
structure OMem (g : Graph) (c₀ : Config) (v : ℕ) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  odeg : Tab m (c₀.reg rFREE) v fun u => (outL g (peelPos g) u).length
  oadj : ∀ u < v, Arr m (c₀.reg rFREE + numV g + R1.ps (idEdges g) u) (outL g (peelPos g) u)
  zero : ZeroFrom m (c₀.reg rFREE + numV g + 2 * (idEdges g).length)

/-- The machine after the vertices `u < v`. -/
@[mk_iff] structure ORep (g : Graph) (c₀ : Config) (v : ℕ) (c : Config) : Prop where
  glob : OGlob g c₀ c
  mem : OMem g c₀ v c.mem

theorem ORep.indep (g : Graph) (c₀ : Config) (v : ℕ) :
    Indep [rT, xI, xA, xB, xV, xW, xX, xY, xQ, xS, xOv] (ORep g c₀ v) := by
  indep [oRep_iff, oGlob_iff]

/-- The partial out-list of `v` after `a` neighbours. -/
def outPre (g : Graph) (v a : ℕ) : List ℕ :=
  ((nb g v).take a).filter fun u => peelPos g v < peelPos g u

theorem outPre_full (g : Graph) (v : ℕ) : outPre g v (nb g v).length = outL g (peelPos g) v := by
  simp [outPre, outL]

theorem outPre_succ (g : Graph) (v : ℕ) {a : ℕ} (ha : a < (nb g v).length) :
    outPre g v (a + 1) = outPre g v a ++
      (if peelPos g v < peelPos g ((nb g v).getD a 0) then [(nb g v).getD a 0] else []) := by
  rw [outPre, List.take_succ_eq_append_getElem ha, List.filter_append, getD_eq_getElem' ha]
  by_cases h : peelPos g v < peelPos g (nb g v)[a] <;> simp [h, outPre]

theorem length_outPre_le (g : Graph) (v a : ℕ) : (outPre g v a).length ≤ a :=
  (List.length_filter_le _ _).trans (List.length_take_le _ _)

/-- The inner invariant: vertex `v`, after the neighbours up to the CSR index `j`. -/
def IInv (g : Graph) (c₀ : Config) (v j : ℕ) (c : Config) : Prop :=
  ORep g c₀ v c ∧
    Arr c.mem (c₀.reg rFREE + numV g + R1.ps (idEdges g) v)
      (outPre g v (j - R1.ps (idEdges g) v)) ∧
    c.reg xS = (outPre g v (j - R1.ps (idEdges g) v)).length ∧
    c.reg xOv = R1.ps (idEdges g) v ∧ c.reg xV = v

section

variable {g : Graph} {c₀ : Config} {S : ℕ}

theorem PeelPost.posR (h : PeelPost g c₀) {m : ℕ → ℕ} (hS : SameOn (· < c₀.reg rFREE) c₀.mem m)
    {v : ℕ} (hv : v < numV g) : m (c₀.reg gPOS + v) = peelPos g v :=
  (h.pos.of_below hS h.below).get hv

/-- Appending to the segment of `v` keeps the other segments. -/
theorem OMem.app {v : ℕ} {m : ℕ → ℕ} (h : OMem g c₀ v m) (hv : v < numV g) {a : ℕ}
    (ha : a < (nb g v).length) (x : ℕ) :
    OMem g c₀ v (RAM.upd m (c₀.reg rFREE + numV g + (R1.ps (idEdges g) v + a)) x) := by
  have h1 := R1.ps_add_le (idEdges g) (show v < numV g from hv)
  have h2 := R1.idEdges_ps g
  have ha' : a < (nbOf (idEdges g) v).length := ha
  refine ⟨h.same.upd_of_ge (by omega) _, h.odeg.upd_of_disjoint (by omega), fun u hu => ?_,
    h.zero.upd (by omega)⟩
  have h3 := R1.ps_add_le (idEdges g) (show u < v from hu)
  have h4 : (outL g (peelPos g) u).length ≤ (nbOf (idEdges g) u).length := length_outL_le _ _ _
  exact (h.oadj u hu).upd_of_disjoint (by omega)

theorem OGlob.regIndep (g : Graph) (c₀ : Config) :
    RegIndep [rT, xI, xA, xB, xV, xW, xX, xY, xQ, xS, xOv] (OGlob g c₀) := by
  indep [oGlob_iff]

/-- One neighbour of `v`. -/
theorem orientInner_run (hP : PeelPost g c₀) {v j : ℕ} {c : Config} (hI : IInv g c₀ v j c)
    (hv : v < numV g) (hj1 : R1.ps (idEdges g) v ≤ j)
    (hj2 : j < R1.ps (idEdges g) v + (nb g v).length) (hi : c.reg xI = j)
    (hSp : orientEnd g (c₀.reg rFREE) ≤ S) :
    IInv g c₀ v (j + 1) (run orientInner c) ∧
      (∀ r, r ≠ xW → r ≠ xX → r ≠ xY → r ≠ xQ → r ≠ xS → r ≠ rT →
        (run orientInner c).reg r = c.reg r) ∧ AddrOK S orientInner c := by
  obtain ⟨hR, hA, hS, hOv, hV⟩ := hI
  have hG := hR.glob
  set a := j - R1.ps (idEdges g) v with ha_def
  have ha : a < (nb g v).length := by omega
  set w := (nb g v).getD a 0 with hw_def
  have hwN : w < numV g := (nbOk g).lt v w (by rw [hw_def, getD_eq_getElem' ha]; simp)
  have hadj : c.mem (c₀.reg gADJ + (R1.ps (idEdges g) v + a)) = w :=
    hP.base.adjR hR.mem.same hv ha
  have hpv : c.mem (c₀.reg gPOS + v) = peelPos g v := hP.posR hR.mem.same hv
  have hpw : c.mem (c₀.reg gPOS + w) = peelPos g w := hP.posR hR.mem.same hwN
  have hj : j = R1.ps (idEdges g) v + a := by omega
  have hj' : j + 1 - R1.ps (idEdges g) v = a + 1 := by omega
  have hreg : ∀ r, r ≠ xW → r ≠ xX → r ≠ xY → r ≠ xQ → r ≠ xS → r ≠ rT →
      (run orientInner c).reg r = c.reg r := fun r h1 h2 h3 h4 h5 h6 =>
    run_reg_of_not_mem (by decide) (by simp [orientInner, wregs, h1, h2, h3, h4, h5, h6]) c
  have hglob : OGlob g c₀ (run orientInner c) :=
    (OGlob.regIndep g c₀).run_of_sub (by decide) (by decide) hG
  have hlen := length_outPre_le g v a
  have hAd : AddrOK S orientInner c := by
    have hb := hP.base.bounds
    have hpb := hP.below
    have h1 : R1.ps (idEdges g) v + (nb g v).length ≤ R1.ps (idEdges g) (numV g) :=
      R1.ps_add_le (idEdges g) hv
    rw [R1.idEdges_ps] at h1
    unfold orientEnd at hSp
    addr_ok [orientInner, hG.adj, hG.pos, hG.oadj, hOv, hS, hi, hV, hj, hadj]
  set c₁ := run (.seq (ld xW gADJ xI) (.seq (ld xX gPOS xV) (ld xY gPOS xW))) c with hc₁
  have hX₁ : c₁.reg xX = peelPos g v := by simp +decide [hc₁, hG.pos, hV, hpv]
  have hY₁ : c₁.reg xY = peelPos g w := by simp +decide [hc₁, hG.pos, hG.adj, hi, hj, hadj, hpw]
  have hW₁ : c₁.reg xW = w := by simp +decide [hc₁, hG.adj, hi, hj, hadj]
  have hm₁ : c₁.mem = c.mem := by simp [hc₁]
  have hS₁ : c₁.reg xS = (outPre g v a).length := by simp +decide [hc₁, hS, ha_def]
  have hOv₁ : c₁.reg xOv = R1.ps (idEdges g) v := by simp +decide [hc₁, hOv]
  have hG₁ : OGlob g c₀ c₁ := (OGlob.regIndep g c₀).run_of_sub (by decide) (by decide) hG
  have hrun : run orientInner c = run (ifLt xX xY (.seq (.add xQ xOv xS)
      (.seq (st gOADJ xQ xW) (inc xS))) .skip) c₁ := by simp [orientInner, hc₁]
  unfold IInv
  rw [hj', outPre_succ g v ha, ← hw_def]
  refine ⟨⟨⟨hglob, ?_⟩, ?_, ?_, by rw [hreg _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), hOv], by rw [hreg _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), hV]⟩, hreg, hAd⟩
  all_goals rw [hrun, run_ifLt, hX₁, hY₁]
  all_goals by_cases hlt : peelPos g v < peelPos g w
  · simp only [hlt, ↓reduceIte]
    have hm := hR.mem.app hv (a := (outPre g v a).length) (by omega) w
    simpa +decide [run_st, run_inc, hG₁.oadj, hOv₁, hS₁, hW₁, hm₁] using hm
  · simp only [hlt, ↓reduceIte, run_skip, setReg_mem, hm₁]
    exact hR.mem
  · simp only [hlt, ↓reduceIte]
    have := hA.upd_snoc (x := w) (a := c₀.reg rFREE + numV g + (R1.ps (idEdges g) v +
      (outPre g v a).length)) (by omega)
    simpa +decide [run_st, run_inc, hG₁.oadj, hOv₁, hS₁, hW₁, hm₁] using this
  · simp only [hlt, ↓reduceIte, List.append_nil, run_skip, setReg_mem, hm₁]
    exact hA
  · simp only [hlt, ↓reduceIte]
    simp +decide [run_st, run_inc, hS₁]
  · simp only [hlt, ↓reduceIte, List.append_nil, run_skip]
    simp +decide [hS₁]

theorem IInv.indep (g : Graph) (c₀ : Config) (v j : ℕ) : Indep [xI, rT] (IInv g c₀ v j) := by
  unfold IInv
  exact ((ORep.indep g c₀ v).mono (by decide)).and ((Indep.mem (fun m => Arr m
    (c₀.reg rFREE + numV g + R1.ps (idEdges g) v) (outPre g v (j - R1.ps (idEdges g) v)))).and
    ((Indep.reg (W := [xI, rT]) (r := xS) (by decide)
      (· = (outPre g v (j - R1.ps (idEdges g) v)).length)).and
      ((Indep.reg (W := [xI, rT]) (r := xOv) (by decide) (· = R1.ps (idEdges g) v)).and
        (Indep.reg (W := [xI, rT]) (r := xV) (by decide) (· = v)))))

/-- One vertex `v`. -/
theorem orientBody_spec (hP : PeelPost g c₀) (hSp : orientEnd g (c₀.reg rFREE) ≤ S) {v : ℕ}
    (hv : v < numV g) :
    HTB S orientBody (fun c => ORep g c₀ v c ∧ c.reg xV = v ∧ c.reg gN = numV g)
      (fun c => ORep g c₀ (v + 1) c ∧ c.reg xV = v ∧ c.reg gN = numV g)
      (13 + 18 * (nb g v).length) := by
  set A := R1.ps (idEdges g) v with hA
  have hAB : R1.ps (idEdges g) (v + 1) = A + (nb g v).length := by rw [R1.ps_succ]
  -- the prefix
  have h₁ : HTB S orientPre (fun c => ORep g c₀ v c ∧ c.reg xV = v ∧ c.reg gN = numV g)
      (fun c => IInv g c₀ v A c ∧ c.reg xOv = A ∧ c.reg xB = A + (nb g v).length ∧
        A ≤ A + (nb g v).length) 7 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hV, _⟩ => ?_
    have hG := hR.glob
    have hb := hP.base.bounds
    have hAd : AddrOK S orientPre c := by
      unfold orientEnd at hSp
      addr_ok [orientPre, hG.off, hV]
    refine ⟨hAd, ?_⟩
    have ho0 : c.mem (c₀.reg gOFF + v) = A := hP.base.offR hR.mem.same (by omega)
    have ho1 : c.mem (c₀.reg gOFF + (v + 1)) = A + (nb g v).length := by
      rw [hP.base.offR hR.mem.same (by omega), hAB]
    have hR' : ORep g c₀ v (run orientPre c) :=
      (ORep.indep g c₀ v).mono (W' := [xOv, xQ, rT, xB, xS]) (by decide) c _
        (agree_run (by decide) rfl rfl (by decide) c) hR
    refine ⟨⟨hR', ?_, ?_, ?_, ?_⟩, ?_, ?_, by omega⟩
    · simp [orientPre, outPre, hA]
    · simp +decide [orientPre, outPre, hA]
    · simp +decide [orientPre, run_addc, hG.off, hV, ho0, hA]
    · simp +decide [orientPre, run_addc, hV]
    · simp +decide [orientPre, run_addc, hG.off, hV, ho0]
    · simp +decide [orientPre, run_addc, hG.off, hV, ho1]
  -- the scan of the neighbours
  have h₂ := HTB.forRange (S := S) (i := xI) (a := xOv) (n := xB) (A := A)
    (N := A + (nb g v).length)
    (body := orientInner) (IInv g c₀ v) (fun _ => 14) (by decide) (by decide) (by decide)
    (by decide) (fun j => IInv.indep g c₀ v j)
    (fun j hAj hjN => HTB.run_le (by decide) (by decide) fun c ⟨hI, hi, hb⟩ => by
      obtain ⟨hI', hreg, hAd⟩ := orientInner_run hP hI hv hAj hjN hi hSp
      refine ⟨hAd, hI', ?_, ?_⟩
      · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi]
      · rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hb])
  -- the out-degree
  have h₃ : HTB S (st gODEG xV xS) (fun c => IInv g c₀ v (A + (nb g v).length) c ∧
        c.reg xI = A + (nb g v).length ∧ c.reg xB = A + (nb g v).length)
      (fun c => ORep g c₀ (v + 1) c ∧ c.reg xV = v ∧ c.reg gN = numV g) 2 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hA', hS, _, hV⟩, _, _⟩ => ?_
    have hG := hR.glob
    refine ⟨by unfold orientEnd at hSp; addr_ok [hG.odeg, hV], ?_⟩
    have hfull : A + (nb g v).length - A = (nb g v).length := by omega
    rw [hfull, outPre_full] at hA' hS
    have h1 := R1.ps_add_le (idEdges g) (show v < numV g from hv)
    have h2 := R1.idEdges_ps g
    have hm := hR.mem
    rw [run_st (by decide)]
    refine ⟨⟨(OGlob.regIndep g c₀).setReg (by decide) _ ?_, ?_⟩, by simp +decide [hV],
      by simp +decide [hG.n]⟩
    · exact (OGlob.regIndep g c₀).setMem _ _ hG
    · simp only [setReg_mem, setMem_mem_upd, hG.odeg, hV, hS]
      refine ⟨hm.same.upd_of_ge (by omega) _, (hm.odeg.upd_of_disjoint (by omega)).snoc (by simp),
        fun u hu => ?_, hm.zero.upd (by omega)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
      · have h3 := R1.ps_add_le (idEdges g) (show u < numV g by omega)
        exact (hm.oadj u hu).upd_of_disjoint (by omega)
      · exact hA'.upd_of_disjoint (by omega)
  refine (h₁.seq (h₂.seq h₃)).weaken (le_of_eq ?_)
  simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  omega

theorem orientAlloc_spec (hP : PeelPost g c₀) :
    HTB S orientAlloc (fun c => c = c₀) (fun c => ORep g c₀ 0 c ∧ c.reg gN = numV g) 7 := by
  refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  have hB := hP.base.r1.base
  simp only [orientAlloc, run_seq', run_alloc (show gN ≠ rT by decide) (show gODEG ≠ gN by decide),
    run_add, run_alloc (show xA ≠ rT by decide) (show gOADJ ≠ xA by decide)]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, SameOn.refl _ _, tab_zero _ _ _, fun u hu => absurd hu
    (Nat.not_lt_zero _), hB.free.mono (by omega)⟩, ?_⟩
  all_goals simp +decide [hB.n, hB.ne]
  omega

/-- The constant of the running time of ORIENT. -/
def CO : ℕ := 100

theorem orient_wregs : ∀ r ∈ wregs orient, r = rT ∨ r = rFREE ∨ (34 ≤ r ∧ r < 50) ∨
    (100 ≤ r ∧ r < 150) := by decide

theorem orient_writes : writes orient = false := by decide

/-- **Phase ORIENT**: from a `PeelPost g` configuration, `orient` stores the out-degrees and
the out-lists of the peeling orientation (`OrientPost g`), within `CO · (m + 1)` steps,
without output, storing only at or above the initial `rFREE`, accessing only the addresses below
any `S ≥ orientEnd g F`, and ending with `rFREE = orientEnd g F`. -/
theorem orient_spec (g : Graph) (c₀ : Config) (hSp : orientEnd g (c₀.reg rFREE) ≤ S) :
    HTB S orient (fun c => PeelPost g c ∧ c = c₀)
      (fun c => OrientPost g c ∧ c.out = c₀.out ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE ≤ orientEnd g (c₀.reg rFREE))
      (CO * (g.length + 1)) := by
  intro c ⟨hP, hc⟩
  subst hc
  have hl := HTB.forUp (S := S) (i := xV) (n := gN) (N := numV g) (body := orientBody) (ORep g c)
    (fun v => 13 + 18 * (nb g v).length) (by decide) (by decide) (by decide)
    (fun v => (ORep.indep g c v).mono (by decide))
    (fun v hv => orientBody_spec hP hSp hv)
  have h := (orientAlloc_spec hP).seq hl
  obtain ⟨c', t, he, ⟨⟨hR, _, _⟩, hfr⟩, ht⟩ := h.withFrame c c ⟨rfl, rfl⟩
  have hG := hR.glob
  have hreg : ∀ r, r < 34 → r ≠ rT → r ≠ rFREE → c'.reg r = c.reg r := fun r hr h1 h2 =>
    hfr.reg r fun hm => by rcases orient_wregs r hm with h | h | h | h <;> omega
  refine ⟨c', t, he, ⟨⟨hP.transfer hreg hR.mem.same (by rw [hG.free]; omega)
    (by rw [hG.free]; exact hR.mem.zero), ?_, ?_, ?_⟩, hfr.out orient_writes, hR.mem.same,
    by rw [hG.free]; omega, by rw [hG.free]; rfl⟩, ?_⟩
  · rw [hG.odeg]; exact hR.mem.odeg
  · intro v hv; rw [hG.oadj]; exact hR.mem.oadj v hv
  · rw [hG.odeg, hG.oadj, hG.free]; omega
  · have hs : ∑ v ∈ Finset.range (numV g), (13 + 18 * (nb g v).length + 4) =
        17 * numV g + 18 * (2 * (idEdges g).length) := by
      rw [← sum_length_nb, ← sum_affine]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hs] at ht
    have h1 := numV_le g
    have h2 := length_idEdges_le g
    simp only [CO]
    omega

end

end STACS2027.Runtimes.C4
