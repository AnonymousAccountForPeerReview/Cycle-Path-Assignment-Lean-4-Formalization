module

public import Outerplanar.RAM.Poly1Grow
public import Outerplanar.RAM.Poly1Spec
import Mathlib.Tactic

/-!
# Phase P1 of the polygon solver, stage A: the sorted neighbour lists

From the edge arrays `gPU`, `gPV` of the polygon, stage A (`stageA`) computes the sorted
neighbour lists `nbP pg n p` of all positions, concatenated (`nbCat`, at `rNB`), with their
starts (`nbOff`, `n + 1` cells at `rOFF`), in `O(n + |pg|)` steps and `O(n + |pg|)` fresh cells (`stageA_spec`):

1. `arcStep`: the arcs (each edge in both directions, `arcs pg`), sources at `rASRC`, targets at
   `rATGT`;
2. `sort1`, `gath1`, `gath2`: a stable counting sort of the arcs by target, giving the arcs
   grouped by target (`arcs1 pg n`: sources at `rS1`, targets at `rT1`);
3. `sort2`, `gath3`: a stable counting sort of these by source; the group of `p` lists the
   neighbours of `p` in increasing order (`map_bucketIdx_arcs1`).
-/

@[expose] public section

namespace STACS2027.RAM.P1

open STACS2027.Poly

/-! ### Registers and program -/

/-- The number of arcs `2 |pg|`. -/
abbrev rL : ℕ := 84
/-- Base of the arc sources. -/
abbrev rASRC : ℕ := 85
/-- Base of the arc targets. -/
abbrev rATGT : ℕ := 86
/-- Base of the sources of the arcs grouped by target. -/
abbrev rS1 : ℕ := 87
/-- Base of the targets of the arcs grouped by target. -/
abbrev rT1 : ℕ := 88
/-- Base of the starts of the neighbour lists (`n + 1` cells). -/
abbrev rOFF : ℕ := 89
/-- Base of the sorted neighbour lists, concatenated. -/
abbrev rNB : ℕ := 90
/-- Loop counter of the arc loop. -/
abbrev rAI : ℕ := 120
/-- Temporary. -/
abbrev rAX : ℕ := 121
/-- Temporary. -/
abbrev rAY : ℕ := 122
/-- Temporary. -/
abbrev rAZ : ℕ := 123

/-- `rL := 2m`; allocate the arc arrays. -/
def arcInit : Stmt := .seq (.add rL gPE gPE) (.seq (alloc rASRC rL) (alloc rATGT rL))
/-- The arcs of edge `i`: `(u, v)` at `i` and `(v, u)` at `m + i`. -/
def arcBody : Stmt :=
  .seq (ld rAX gPU rAI) (.seq (ld rAY gPV rAI) (.seq (st rASRC rAI rAX) (.seq (st rATGT rAI rAY)
    (.seq (.add rAZ rAI gPE) (.seq (st rASRC rAZ rAY) (st rATGT rAZ rAX))))))
/-- Step 1: the arcs. -/
def arcStep : Stmt := .seq arcInit (forUp rAI gPE arcBody)
/-- The arguments of the first sort. -/
def sort1Args : Stmt := .seq (mov rKB rATGT) (.seq (mov rKL rL) (mov rKN gPN))
/-- Step 2: sort the arcs by target. -/
def sort1 : Stmt := .seq sort1Args csort
/-- The arguments of the first gather. -/
def gath1Args : Stmt := .seq (mov rGI rKO) (.seq (mov rGF rASRC) (mov rGL rL))
/-- Step 3: the sources of the arcs grouped by target. -/
def gath1 : Stmt := .seq gath1Args (.seq gather (mov rS1 rGO))
/-- The arguments of the second gather. -/
def gath2Args : Stmt := .seq (mov rGI rKO) (.seq (mov rGF rATGT) (mov rGL rL))
/-- Step 4: the targets of the arcs grouped by target. -/
def gath2 : Stmt := .seq gath2Args (.seq gather (mov rT1 rGO))
/-- The arguments of the second sort. -/
def sort2Args : Stmt := .seq (mov rKB rS1) (.seq (mov rKL rL) (mov rKN gPN))
/-- Step 5: sort these by source. -/
def sort2 : Stmt := .seq sort2Args csort
/-- The arguments of the third gather. -/
def gath3Args : Stmt := .seq (mov rGI rKO) (.seq (mov rGF rT1) (mov rGL rL))
/-- The results of stage A. -/
def gath3Res : Stmt := .seq (mov rNB rGO) (mov rOFF rKF)
/-- Step 6: the targets, grouped by source: the sorted neighbour lists. -/
def gath3 : Stmt := .seq gath3Args (.seq gather gath3Res)
/-- **Stage A**: the sorted neighbour lists. -/
def stageA : Stmt := .seq arcStep (.seq sort1 (.seq gath1 (.seq gath2 (.seq sort2 gath3))))

/-- The registers written by stage A. -/
abbrev WA : List ℕ := wregs stageA

/-! ### The states -/

/-- The free memory invariant. -/
def Zf (c : Config) : Prop := ZeroFrom c.mem (c.reg rFREE)

/-- After the arcs. -/
def ArcSt (pg : Graph) (n : ℕ) (c : Config) : Prop :=
  c.reg gPN = n ∧ c.reg rL = 2 * pg.length ∧ ArrAt rASRC ((arcs pg).map Prod.fst) c ∧
    ArrAt rATGT ((arcs pg).map Prod.snd) c

/-- **The sorted neighbour lists** (the result of stage A). -/
def Csr (pg : Graph) (n : ℕ) (c : Config) : Prop :=
  ArrAt rNB (nbCat pg n) c ∧ TabAt rOFF (n + 1) (nbOff pg n) c

theorem stable_arcSt {pg : Graph} {n : ℕ} {W : List ℕ}
    (h : gPN ∉ W ∧ rL ∉ W ∧ rASRC ∉ W ∧ rATGT ∉ W) : Stable W (ArcSt pg n) :=
  (Stable.regEq h.1 _).and ((Stable.regEq h.2.1 _).and ((Stable.arrAt h.2.2.1 _).and
    (Stable.arrAt h.2.2.2 _)))

theorem stable_csOut {keys : List ℕ} {K : ℕ} {W : List ℕ} (h : rKO ∉ W ∧ rKF ∉ W) :
    Stable W (CsOut keys K) :=
  (Stable.arrAt h.1 _).and (Stable.tabAt h.2 _)

theorem stable_csr {pg : Graph} {n : ℕ} {W : List ℕ} (h : rNB ∉ W ∧ rOFF ∉ W) :
    Stable W (Csr pg n) :=
  (Stable.arrAt h.1 _).and (Stable.tabAt h.2 _)

/-- A mov-only block is a growth with its written registers. -/
theorem grow_movs {s : Stmt} (hs : LoopFree s) (hst : stores s = false) (hw : writes s = false)
    (hF : rFREE ∉ wregs s) {W : List ℕ} (hW : ∀ r ∈ wregs s, r ∈ W) (c : Config) :
    Grow W c (RAM.run s c) := (grow_run hs hst hw hF c).mono hW

/-- A mov-only block keeps the memory and the free pointer. -/
theorem movs_mem {s : Stmt} (hs : LoopFree s) (hst : stores s = false) (hF : rFREE ∉ wregs s)
    (c : Config) : (RAM.run s c).mem = c.mem ∧ (RAM.run s c).reg rFREE = c.reg rFREE :=
  ⟨run_mem_of_stores hs hst c, run_reg_of_not_mem hs hF c⟩

variable {pg : Graph} {n : ℕ} {S : ℕ}

/-! ### Step 1: the arcs -/

/-- The memory of the arc loop after `j` edges. -/
structure ArcMem (pg : Graph) (F₀ j : ℕ) (m : ℕ → ℕ) : Prop where
  a1 : Arr m F₀ ((pg.map Prod.fst).take j)
  a2 : Arr m (F₀ + pg.length) ((pg.map Prod.snd).take j)
  a3 : Arr m (F₀ + 2 * pg.length) ((pg.map Prod.snd).take j)
  a4 : Arr m (F₀ + 2 * pg.length + pg.length) ((pg.map Prod.fst).take j)
  zero : ZeroFrom m (F₀ + 4 * pg.length)

/-- The invariant of the arc loop after `j` edges. -/
@[mk_iff] structure ArcInv (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (j : ℕ) (c : Config) : Prop where
  pn : c.reg gPN = n
  pe : c.reg gPE = pg.length
  l : c.reg rL = 2 * pg.length
  src : c.reg rASRC = F₀
  tgt : c.reg rATGT = F₀ + 2 * pg.length
  free : c.reg rFREE = F₀ + 4 * pg.length
  pu : Arr c.mem (c.reg gPU) (pg.map Prod.fst)
  pv : Arr c.mem (c.reg gPV) (pg.map Prod.snd)
  bu : c.reg gPU + pg.length ≤ F₀
  bv : c.reg gPV + pg.length ≤ F₀
  mem : ArcMem pg F₀ j c.mem
  same : SameOn (· < F₀) m₀ c.mem

theorem take_succ_map {l : List (ℕ × ℕ)} {j : ℕ} (hj : j < l.length) (f : ℕ × ℕ → ℕ) :
    (l.map f).take (j + 1) = (l.map f).take j ++ [f l[j]] := by
  rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl

theorem ArcMem.step {F₀ j : ℕ} {m : ℕ → ℕ} (h : ArcMem pg F₀ j m) (hj : j < pg.length) :
    ArcMem pg F₀ (j + 1) (upd (upd (upd (upd m (F₀ + j) pg[j].1) (F₀ + 2 * pg.length + j) pg[j].2)
      (F₀ + (j + pg.length)) pg[j].2) (F₀ + 2 * pg.length + (j + pg.length)) pg[j].1) := by
  have hl : ∀ f : ℕ × ℕ → ℕ, ((pg.map f).take j).length = j := fun f => by simp; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [take_succ_map hj]
    exact (((h.a1.upd_snoc (by rw [hl])).upd_of_disjoint (by simp; omega)).upd_of_disjoint
      (by simp; omega)).upd_of_disjoint (by simp; omega)
  · rw [take_succ_map hj]
    exact (((h.a2.upd_of_disjoint (by rw [hl]; omega)).upd_of_disjoint (by rw [hl]; omega)).upd_snoc
      (by rw [hl]; omega)).upd_of_disjoint (by simp; omega)
  · rw [take_succ_map hj]
    exact (((h.a3.upd_of_disjoint (by rw [hl]; omega)).upd_snoc (by rw [hl])).upd_of_disjoint
      (by simp; omega)).upd_of_disjoint (by simp; omega)
  · rw [take_succ_map hj]
    exact (((h.a4.upd_of_disjoint (by rw [hl]; omega)).upd_of_disjoint (by rw [hl]; omega)).upd_of_disjoint
      (by rw [hl]; omega)).upd_snoc (by rw [hl]; omega)
  · exact (((h.zero.upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)

theorem arcBody_spec (F₀ : ℕ) (m₀ : ℕ → ℕ) (hS : F₀ + 4 * pg.length ≤ S) (j : ℕ)
    (hj : j < pg.length) :
    HTB S arcBody (fun c => ArcInv pg n F₀ m₀ j c ∧ c.reg rAI = j ∧ c.reg gPE = pg.length)
      (fun c => ArcInv pg n F₀ m₀ (j + 1) c ∧ c.reg rAI = j ∧ c.reg gPE = pg.length) 13 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  obtain ⟨hI, hj', hpe⟩ := hc
  refine ⟨by have := hI.bu; have := hI.bv; addr_ok [arcBody, hj', hI.src, hI.tgt, hpe], ?_⟩
  have hu : c.mem (c.reg gPU + j) = pg[j].1 := by rw [hI.pu.get (by simpa using hj)]; simp
  have hv : c.mem (c.reg gPV + j) = pg[j].2 := by rw [hI.pv.get (by simpa using hj)]; simp
  have hrr : ∀ r, r ∉ wregs arcBody → (RAM.run arcBody c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hmem : (RAM.run arcBody c).mem =
      upd (upd (upd (upd c.mem (F₀ + j) pg[j].1) (F₀ + 2 * pg.length + j) pg[j].2)
        (F₀ + (j + pg.length)) pg[j].2) (F₀ + 2 * pg.length + (j + pg.length)) pg[j].1 := by
    simp +decide only [arcBody, run_seq', run_ld, run_add, run_st (show rAX ≠ rT by decide),
      run_st (show rAY ≠ rT by decide), setReg_reg, ↓reduceIte, setReg_mem, setMem_reg,
      setMem_mem_upd, hj', hu, hv, hI.src, hI.tgt, hpe]
  have hm := hI.mem.step hj
  rw [← hmem] at hm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm, ?_⟩, ?_, ?_⟩
  all_goals try rw [hrr _ (by decide)]
  all_goals try rw [hmem]
  · exact hI.pn
  · exact hI.pe
  · exact hI.l
  · exact hI.src
  · exact hI.tgt
  · exact hI.free
  · exact (((hI.pu.upd_of_disjoint (by simp; have := hI.bu; omega)).upd_of_disjoint
      (by simp; have := hI.bu; omega)).upd_of_disjoint (by simp; have := hI.bu; omega)).upd_of_disjoint
      (by simp; have := hI.bu; omega)
  · exact (((hI.pv.upd_of_disjoint (by simp; have := hI.bv; omega)).upd_of_disjoint
      (by simp; have := hI.bv; omega)).upd_of_disjoint (by simp; have := hI.bv; omega)).upd_of_disjoint
      (by simp; have := hI.bv; omega)
  · exact hI.bu
  · exact hI.bv
  · exact (((hI.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge
      (by omega) _
  · exact hj'
  · exact hpe

theorem arcInit_spec (omap : List ℕ) (F₀ : ℕ) (m₀ : ℕ → ℕ) :
    HT arcInit (fun c => PolyIn pg n omap c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => ArcInv pg n F₀ m₀ 0 c ∧ c.reg gPE = pg.length) 7 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨hc, hF, hm⟩ => ?_
  simp only [arcInit, run_seq', run_add, run_alloc (show rL ≠ rT by decide)
    (show rASRC ≠ rL by decide), run_alloc (show rL ≠ rT by decide) (show rATGT ≠ rL by decide)]
  have hb := hc.below
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  all_goals simp +decide only [setReg_reg, ↓reduceIte, setReg_mem, hF, hc.pn, hc.pe, List.take_zero,
    arr_nil]
  all_goals try omega
  · exact hc.pu
  · exact hc.pv
  · exact hc.free.mono (by omega)
  · rw [hm]; exact SameOn.refl _ _

/-- **Step 1**: the arcs. -/
theorem arcStep_spec (omap : List ℕ) :
    HGMB S arcStep WA (PolyIn pg n omap) (fun c => ArcSt pg n c ∧ Zf c) (17 * pg.length + 10)
      (4 * pg.length) := by
  refine HGMB.ofGhost (by decide) (by decide) fun F₀ m₀ hS => ?_
  have hl := HTB.forUpC (i := rAI) (n := gPE) (N := pg.length) (body := arcBody)
    (ArcInv pg n F₀ m₀) 13 (by decide) (by decide) (by decide)
    (fun j => by indep [arcInv_iff]) (fun j hj => arcBody_spec F₀ m₀ hS j hj)
  refine ((HTB.of_HT rfl (arcInit_spec omap F₀ m₀)).seq hl).mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨hI, -, -⟩
  have hM := hI.mem
  have hlen : ∀ f : ℕ × ℕ → ℕ, (pg.map f).length = pg.length := fun f => List.length_map _
  have ht : ∀ f : ℕ × ℕ → ℕ, (pg.map f).take pg.length = pg.map f :=
    fun f => List.take_of_length_le (by rw [hlen])
  have a1 := hM.a1
  have a2 := hM.a2
  have a3 := hM.a3
  have a4 := hM.a4
  rw [ht] at a1 a2 a3 a4
  refine ⟨⟨⟨hI.pn, hI.l, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩, hI.same, by rw [hI.free]; omega,
    by rw [hI.free]⟩
  · rw [hI.src, arcs, List.map_append, List.map_map, arr_append]
    exact ⟨a1, by rw [hlen]; exact a2⟩
  · rw [hI.src, hI.free, List.length_map, length_arcs]; omega
  · rw [hI.tgt, arcs, List.map_append, List.map_map, arr_append]
    exact ⟨a3, by rw [hlen]; exact a4⟩
  · rw [hI.tgt, hI.free, List.length_map, length_arcs]; omega
  · unfold Zf; rw [hI.free]; exact hM.zero

/-! ### Steps 2–6: two sorts and three gathers -/

theorem keys_arcs_lt (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) :
    ∀ x ∈ (arcs pg).map Prod.snd, x < n := by
  intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact (lt_of_mem_arcs hP hlt hy).2

theorem keys_arcs1_lt (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) :
    ∀ x ∈ (arcs1 pg n).map Prod.fst, x < n := by
  intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact (lt_of_mem_arcs hP hlt (mem_arcs_of_mem_arcs1 hy)).1

theorem length_bucketIdx_arcs (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) :
    (bucketIdx ((arcs pg).map Prod.snd) n).length = 2 * pg.length := by
  rw [length_bucketIdx _ _ (keys_arcs_lt hP hlt), List.length_map, length_arcs]

theorem length_bucketIdx_arcs1 (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) :
    (bucketIdx ((arcs1 pg n).map Prod.fst) n).length = 2 * pg.length := by
  rw [length_bucketIdx _ _ (keys_arcs1_lt hP hlt), List.length_map, length_arcs1 hP hlt]

/-- **Step 2**: sorting the arcs by target. -/
theorem sort1_spec (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) :
    HGMB S sort1 WA (fun c => ArcSt pg n c ∧ Zf c)
      (fun c => (CsOut ((arcs pg).map Prod.snd) n c ∧ Zf c) ∧ ArcSt pg n c)
      (56 * pg.length + 15 * n + 26) (2 * n + 1 + 2 * pg.length) := by
  have h₁ : HGMB S sort1Args WA (fun c => ArcSt pg n c ∧ Zf c)
      (fun c => CsIn ((arcs pg).map Prod.snd) n c ∧ ArcSt pg n c) 6 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨hA, hZ⟩ =>
      ⟨?_, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    obtain ⟨hm, hf⟩ := movs_mem (s := sort1Args) (by decide) rfl (by decide) c
    refine ⟨⟨?_, ?_, hA.2.2.2.of_reg ?_ hm hf, by unfold Zf at hZ; rw [hm, hf]; exact hZ⟩,
      stable_arcSt (by decide) c _ hA
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)⟩
    · simp +decide [sort1Args, run_mov, hA.2.1, length_arcs]
    · simp +decide [sort1Args, run_mov, hA.1]
    · simp +decide [sort1Args, run_mov]
  have h₂ := ((csort_specMB (S := S) _ n (keys_arcs_lt hP hlt)).frame (F := ArcSt pg n)
    (stable_arcSt (by decide))).mono (W' := WA) (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    le_rfl
  refine (h₁.seq h₂).weaken ?_ ?_
  all_goals simp only [List.length_map, length_arcs]; omega

/-- The sorted indices of the arcs by target. -/
abbrev idx1 (pg : Graph) (n : ℕ) : List ℕ := bucketIdx ((arcs pg).map Prod.snd) n

/-- The sorted indices of the arcs grouped by target, by source. -/
abbrev idx2 (pg : Graph) (n : ℕ) : List ℕ := bucketIdx ((arcs1 pg n).map Prod.fst) n

/-- **Step 3**: the sources of the arcs grouped by target. -/
theorem gath1_spec (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) :
    HGMB S gath1 WA (fun c => (CsOut ((arcs pg).map Prod.snd) n c ∧ Zf c) ∧ ArcSt pg n c)
      (fun c => (ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ Zf c) ∧
        (CsOut ((arcs pg).map Prod.snd) n c ∧ ArcSt pg n c)) (20 * pg.length + 14)
      (2 * pg.length) := by
  have hidx : ∀ i ∈ idx1 pg n, i < ((arcs pg).map Prod.fst).length := fun i hi => by
    have := lt_of_mem_bucketIdx hi; simpa using this
  have h₁ : HGMB S gath1Args WA (fun c => (CsOut ((arcs pg).map Prod.snd) n c ∧ Zf c) ∧ ArcSt pg n c)
      (fun c => GaIn (idx1 pg n) ((arcs pg).map Prod.fst) c ∧
        (CsOut ((arcs pg).map Prod.snd) n c ∧ ArcSt pg n c)) 6 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hO, hZ⟩, hA⟩ =>
      ⟨?_, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    obtain ⟨hm, hf⟩ := movs_mem (s := gath1Args) (by decide) rfl (by decide) c
    refine ⟨⟨?_, hO.1.of_reg ?_ hm hf, hA.2.2.1.of_reg ?_ hm hf,
      by unfold Zf at hZ; rw [hm, hf]; exact hZ⟩,
      ((stable_csOut (by decide)).and (stable_arcSt (by decide))) c _ ⟨hO, hA⟩
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)⟩
    · simp +decide [gath1Args, run_mov, hA.2.1, length_bucketIdx_arcs hP hlt]
    · simp +decide [gath1Args, run_mov]
    · simp +decide [gath1Args, run_mov]
  have h₂ := ((gather_spec (S := S) (idx1 pg n) _ hidx).frame
    (F := fun c => CsOut ((arcs pg).map Prod.snd) n c ∧ ArcSt pg n c)
    ((stable_csOut (by decide)).and (stable_arcSt (by decide)))).mono (W' := WA) (by decide) (fun _ h => h) (fun _ h => h)
    le_rfl le_rfl
  have h₃ : HGMB S (mov rS1 rGO) WA
      (fun c => (ArrAt rGO ((idx1 pg n).map fun i => ((arcs pg).map Prod.fst).getD i 0) c ∧
        ZeroFrom c.mem (c.reg rFREE)) ∧ (CsOut ((arcs pg).map Prod.snd) n c ∧ ArcSt pg n c))
      (fun c => (ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ Zf c) ∧
        (CsOut ((arcs pg).map Prod.snd) n c ∧ ArcSt pg n c)) 2 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hG, hZ⟩, hF⟩ =>
      ⟨⟨⟨?_, ?_⟩, ?_⟩, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    · rw [← map_bucketIdx_arcs]
      exact hG.of_reg (by simp +decide [run_mov]) (by simp [run_mov]) (by simp +decide [run_mov])
    · unfold Zf; simpa +decide [run_mov] using hZ
    · exact ((stable_csOut (by decide)).and (stable_arcSt (by decide))) c _ hF
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)
  refine (h₁.seq (h₂.seq h₃)).weaken ?_ ?_
  all_goals rw [length_bucketIdx_arcs hP hlt]; omega

/-- **Step 4**: the targets of the arcs grouped by target. -/
theorem gath2_spec (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) :
    HGMB S gath2 WA (fun c => (ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ Zf c) ∧
        (CsOut ((arcs pg).map Prod.snd) n c ∧ ArcSt pg n c))
      (fun c => (ArrAt rT1 ((arcs1 pg n).map Prod.snd) c ∧ Zf c) ∧
        (ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ ArcSt pg n c)) (20 * pg.length + 14)
      (2 * pg.length) := by
  have hidx : ∀ i ∈ idx1 pg n, i < ((arcs pg).map Prod.snd).length := fun i hi => by
    have := lt_of_mem_bucketIdx hi; simpa using this
  have h₁ : HGMB S gath2Args WA (fun c => (ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ Zf c) ∧
        (CsOut ((arcs pg).map Prod.snd) n c ∧ ArcSt pg n c))
      (fun c => GaIn (idx1 pg n) ((arcs pg).map Prod.snd) c ∧
        (ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ ArcSt pg n c)) 6 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hS, hZ⟩, hO, hA⟩ =>
      ⟨?_, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    obtain ⟨hm, hf⟩ := movs_mem (s := gath2Args) (by decide) rfl (by decide) c
    refine ⟨⟨?_, hO.1.of_reg ?_ hm hf, hA.2.2.2.of_reg ?_ hm hf,
      by unfold Zf at hZ; rw [hm, hf]; exact hZ⟩,
      ((Stable.arrAt (by decide) _).and (stable_arcSt (by decide))) c _ ⟨hS, hA⟩
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)⟩
    · simp +decide [gath2Args, run_mov, hA.2.1, length_bucketIdx_arcs hP hlt]
    · simp +decide [gath2Args, run_mov]
    · simp +decide [gath2Args, run_mov]
  have h₂ := ((gather_spec (S := S) (idx1 pg n) _ hidx).frame
    (F := fun c => ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ ArcSt pg n c)
    ((Stable.arrAt (by decide) _).and (stable_arcSt (by decide)))).mono (W' := WA) (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    le_rfl
  have h₃ : HGMB S (mov rT1 rGO) WA
      (fun c => (ArrAt rGO ((idx1 pg n).map fun i => ((arcs pg).map Prod.snd).getD i 0) c ∧
        ZeroFrom c.mem (c.reg rFREE)) ∧ (ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ ArcSt pg n c))
      (fun c => (ArrAt rT1 ((arcs1 pg n).map Prod.snd) c ∧ Zf c) ∧
        (ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ ArcSt pg n c)) 2 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hG, hZ⟩, hF⟩ =>
      ⟨⟨⟨?_, ?_⟩, ?_⟩, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    · rw [← map_bucketIdx_arcs]
      exact hG.of_reg (by simp +decide [run_mov]) (by simp [run_mov]) (by simp +decide [run_mov])
    · unfold Zf; simpa +decide [run_mov] using hZ
    · exact ((Stable.arrAt (by decide) _).and (stable_arcSt (by decide))) c _ hF
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)
  refine (h₁.seq (h₂.seq h₃)).weaken ?_ ?_
  all_goals rw [length_bucketIdx_arcs hP hlt]; omega

/-- **Step 5**: sorting the arcs grouped by target, by source. -/
theorem sort2_spec (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) :
    HGMB S sort2 WA (fun c => (ArrAt rT1 ((arcs1 pg n).map Prod.snd) c ∧ Zf c) ∧
        (ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ ArcSt pg n c))
      (fun c => (CsOut ((arcs1 pg n).map Prod.fst) n c ∧ Zf c) ∧
        (ArrAt rT1 ((arcs1 pg n).map Prod.snd) c ∧ ArcSt pg n c))
      (56 * pg.length + 15 * n + 26) (2 * n + 1 + 2 * pg.length) := by
  have h₁ : HGMB S sort2Args WA (fun c => (ArrAt rT1 ((arcs1 pg n).map Prod.snd) c ∧ Zf c) ∧
        (ArrAt rS1 ((arcs1 pg n).map Prod.fst) c ∧ ArcSt pg n c))
      (fun c => CsIn ((arcs1 pg n).map Prod.fst) n c ∧
        (ArrAt rT1 ((arcs1 pg n).map Prod.snd) c ∧ ArcSt pg n c)) 6 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hT, hZ⟩, hS, hA⟩ =>
      ⟨?_, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    obtain ⟨hm, hf⟩ := movs_mem (s := sort2Args) (by decide) rfl (by decide) c
    refine ⟨⟨?_, ?_, hS.of_reg ?_ hm hf, by unfold Zf at hZ; rw [hm, hf]; exact hZ⟩,
      ((Stable.arrAt (by decide) _).and (stable_arcSt (by decide))) c _ ⟨hT, hA⟩
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)⟩
    · simp +decide [sort2Args, run_mov, hA.2.1, length_arcs1 hP hlt]
    · simp +decide [sort2Args, run_mov, hA.1]
    · simp +decide [sort2Args, run_mov]
  have h₂ := ((csort_specMB (S := S) _ n (keys_arcs1_lt hP hlt)).frame
    (F := fun c => ArrAt rT1 ((arcs1 pg n).map Prod.snd) c ∧ ArcSt pg n c)
    ((Stable.arrAt (by decide) _).and (stable_arcSt (by decide)))).mono (W' := WA) (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    le_rfl
  refine (h₁.seq h₂).weaken ?_ ?_
  all_goals simp only [List.length_map, length_arcs1 hP hlt]; omega

/-- **Step 6**: the sorted neighbour lists. -/
theorem gath3_spec (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) :
    HGMB S gath3 WA (fun c => (CsOut ((arcs1 pg n).map Prod.fst) n c ∧ Zf c) ∧
        (ArrAt rT1 ((arcs1 pg n).map Prod.snd) c ∧ ArcSt pg n c))
      (fun c => (Csr pg n c ∧ Zf c) ∧ ArcSt pg n c) (20 * pg.length + 16) (2 * pg.length) := by
  have hidx : ∀ i ∈ idx2 pg n, i < ((arcs1 pg n).map Prod.snd).length := fun i hi => by
    have := lt_of_mem_bucketIdx hi; simpa using this
  have h₁ : HGMB S gath3Args WA (fun c => (CsOut ((arcs1 pg n).map Prod.fst) n c ∧ Zf c) ∧
        (ArrAt rT1 ((arcs1 pg n).map Prod.snd) c ∧ ArcSt pg n c))
      (fun c => GaIn (idx2 pg n) ((arcs1 pg n).map Prod.snd) c ∧
        (CsOut ((arcs1 pg n).map Prod.fst) n c ∧ ArcSt pg n c)) 6 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hO, hZ⟩, hT, hA⟩ =>
      ⟨?_, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    obtain ⟨hm, hf⟩ := movs_mem (s := gath3Args) (by decide) rfl (by decide) c
    refine ⟨⟨?_, hO.1.of_reg ?_ hm hf, hT.of_reg ?_ hm hf,
      by unfold Zf at hZ; rw [hm, hf]; exact hZ⟩,
      ((stable_csOut (by decide)).and (stable_arcSt (by decide))) c _ ⟨hO, hA⟩
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)⟩
    · simp +decide [gath3Args, run_mov, hA.2.1, length_bucketIdx_arcs1 hP hlt]
    · simp +decide [gath3Args, run_mov]
    · simp +decide [gath3Args, run_mov]
  have h₂ := ((gather_spec (S := S) (idx2 pg n) _ hidx).frame
    (F := fun c => CsOut ((arcs1 pg n).map Prod.fst) n c ∧ ArcSt pg n c)
    ((stable_csOut (by decide)).and (stable_arcSt (by decide)))).mono (W' := WA) (by decide) (fun _ h => h) (fun _ h => h)
    le_rfl le_rfl
  have h₃ : HGMB S gath3Res WA
      (fun c => (ArrAt rGO ((idx2 pg n).map fun i => ((arcs1 pg n).map Prod.snd).getD i 0) c ∧
        ZeroFrom c.mem (c.reg rFREE)) ∧ (CsOut ((arcs1 pg n).map Prod.fst) n c ∧ ArcSt pg n c))
      (fun c => (Csr pg n c ∧ Zf c) ∧ ArcSt pg n c) 4 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hG, hZ⟩, hO, hA⟩ =>
      ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    · rw [← map_bucketIdx_arcs1 hlt hnd]
      exact hG.of_reg (by simp +decide [gath3Res, run_mov]) (by simp [gath3Res, run_mov])
        (by simp +decide [gath3Res, run_mov])
    · have := hO.2.of_reg (r' := rOFF) (c' := RAM.run gath3Res c)
        (by simp +decide [gath3Res, run_mov]) (by simp [gath3Res, run_mov])
        (by simp +decide [gath3Res, run_mov])
      exact ⟨this.1.congr_fun fun p _ => offOf_arcs1 hlt hnd p, this.2⟩
    · unfold Zf; simpa +decide [gath3Res, run_mov] using hZ
    · exact stable_arcSt (by decide) c _ hA
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)
  refine (h₁.seq (h₂.seq h₃)).weaken ?_ ?_
  all_goals rw [length_bucketIdx_arcs1 hP hlt]; omega

/-- **Stage A**: the sorted neighbour lists, in `O(n + |pg|)` steps. -/
theorem stageA_spec (omap : List ℕ) (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2)
    (hnd : pg.Nodup) :
    HGMB S stageA WA (PolyIn pg n omap) (fun c => (Csr pg n c ∧ Zf c) ∧ ArcSt pg n c)
      (189 * pg.length + 30 * n + 106) (14 * pg.length + 4 * n + 2) := by
  refine ((arcStep_spec omap).seq ((sort1_spec hP hlt).seq ((gath1_spec hP hlt).seq
    ((gath2_spec hP hlt).seq ((sort2_spec hP hlt).seq (gath3_spec hP hlt hnd)))))).weaken ?_ ?_
  all_goals omega

end STACS2027.RAM.P1
