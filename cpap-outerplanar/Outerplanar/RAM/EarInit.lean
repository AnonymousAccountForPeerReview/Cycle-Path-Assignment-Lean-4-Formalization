module

public import Outerplanar.RAM.EarBlocks
import Mathlib.Tactic

/-!
# The ear-elimination machine: initialization (before the peeling)

From `EarIn N L` (initial free address `F`, memory `m₀`), within any bound `S ≥ bEND F N |L|`:

1. the allocations (`allocs_spec`): all regions fresh, i.e. the empty graph `eSt N [] []`;
2. the edge loop (`edgeBody_spec`): after `j` edges the state `eSt N (L.take j) []` (lists and
   degrees of the first `j` edges, `1 + 2 j` nodes);
3. the stack loop (`stkBody_spec`): after `j` vertices the stack `stackPre L j`.

The memory below `bHD` (the input and the regions of the peeling) stays that of `m₀`. The
peeling and the whole initialization: `EarPeelR.lean`.
-/

@[expose] public section

namespace STACS2027.RAM.EarR

open STACS2027 STACS2027.Ear

variable {S : ℕ}

/-- The registers written by the program. -/
def WE : List ℕ := [rT, rFREE, gHAM] ++ (List.range 36).map (· + 100)

/-- The input registers (never written). -/
@[mk_iff] structure Inp (N M U V : ℕ) (c : Config) : Prop where
  zero : c.reg rZERO = 0
  one : c.reg rONE = 1
  vn : c.reg gVN = N
  ln : c.reg gLN = M
  lu : c.reg gLU = U
  lv : c.reg gLV = V

theorem Inp.regIndep (N M U V : ℕ) : RegIndep WE (Inp N M U V) := by indep [inp_iff]

/-- The empty graph with the edges `l` added and the stack `stk`. -/
def eSt (N : ℕ) (l : List Edge) (stk : List ℕ) : State :=
  { adj := initAdj l, mat := matInit l, deg := fun v => (initAdj l v).length, dead := fun _ => false,
    stack := stk, log := [], cnt := N }

theorem init_eq_eSt (N : ℕ) (L : List Edge) : init N L = eSt N L (stackPre L N).reverse := rfl

/-- `EMem` only depends on the fields of the state that are in memory (not on `mat`). -/
theorem EMem.congr {N M F : ℕ} {m₀ m : ℕ → ℕ} {s s' : State} {succ : ℕ → ℕ} {ham : List ℕ} {np : ℕ}
    (h : EMem N M F m₀ s succ ham np m) (h1 : s'.adj = s.adj) (h3 : s'.deg = s.deg)
    (h4 : s'.dead = s.dead) (h5 : s'.stack = s.stack) (h6 : s'.log = s.log) :
    EMem N M F m₀ s' succ ham np m :=
  ⟨h1 ▸ h.adj, h3 ▸ h.deg, h4 ▸ h.dead, h5 ▸ h.stk, h6 ▸ h.lgv, h6 ▸ h.lgu,
    h6 ▸ h.lgw, h.sucT, h.hamA, h.same, h.zero, h.npS, h5 ▸ h.stkS, h6 ▸ h.logS, h.hamS⟩

/-! ### Step 1: allocations -/

/-- The state after the allocations, before the edges. -/
def AllocPost (N M U V F : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop :=
  Glob N M F c ∧ Inp N M U V c ∧ c.reg rNP = 1 ∧ c.reg rSP = 0 ∧ c.reg rCNT = N ∧ c.reg rLC = 0 ∧
    c.reg rPSP = 0 ∧ EMem N M F m₀ (eSt N [] []) (fun _ => 0) [] 1 c.mem

theorem allocs_spec (N M U V F : ℕ) (m₀ : ℕ → ℕ) (hz : ZeroFrom m₀ F) :
    HTB S (.seq allocs1 allocs2) (fun c => Inp N M U V c ∧ c.mem = m₀ ∧ c.reg rFREE = F)
      (fun c => AllocPost N M U V F m₀ c) 64 := by
  refine HTB.of_HT rfl (HT.run_le (by decide) (by decide) fun c ⟨hin, hm, hfree⟩ => ?_)
  have hin' : Inp N M U V (run (.seq allocs1 allocs2) c) :=
    (Inp.regIndep N M U V).run_of_sub (by decide) (by decide) hin
  have hmem : (run (.seq allocs1 allocs2) c).mem = c.mem :=
    run_mem_of_stores (by decide) (by decide) c
  have hvn := hin.vn
  have hln := hin.ln
  have hz0 := hin.zero
  have h1 := hin.one
  unfold AllocPost
  rw [hmem, hm]
  simp only [allocs1, allocs2, run_seq',
    run_alloc (show gVN ≠ rT by decide) (show rPD ≠ gVN by decide),
    run_alloc (show gVN ≠ rT by decide) (show rPRM ≠ gVN by decide),
    run_alloc (show gVN ≠ rT by decide) (show rPSTK ≠ gVN by decide),
    run_alloc (show gVN ≠ rT by decide) (show rO1 ≠ gVN by decide),
    run_alloc (show gVN ≠ rT by decide) (show rO2 ≠ gVN by decide),
    run_alloc (show gVN ≠ rT by decide) (show rHD ≠ gVN by decide),
    run_alloc (show gVN ≠ rT by decide) (show rDEG ≠ gVN by decide),
    run_alloc (show gVN ≠ rT by decide) (show rDEAD ≠ gVN by decide),
    run_alloc (show rSZ ≠ rT by decide) (show rSTK ≠ rSZ by decide),
    run_alloc (show gVN ≠ rT by decide) (show rLGV ≠ gVN by decide),
    run_alloc (show gVN ≠ rT by decide) (show rLGU ≠ gVN by decide),
    run_alloc (show gVN ≠ rT by decide) (show rLGW ≠ gVN by decide),
    run_alloc (show rSZ ≠ rT by decide) (show rVAL ≠ rSZ by decide),
    run_alloc (show rSZ ≠ rT by decide) (show rNXT ≠ rSZ by decide),
    run_alloc (show gVN ≠ rT by decide) (show rSUCC ≠ gVN by decide),
    run_alloc (show gVN ≠ rT by decide) (show gHAM ≠ gVN by decide),
    run_add, run_inc (show rSZ ≠ rT by decide), run_const, run_mov (show gVN ≠ rT by decide)] at hin' ⊢
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hin', ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp +decide [hfree, hvn, hln, hz0, h1, bPD, bPRM, bPSTK, bO1, bO2, bHD, bDEG,
    bDEAD, bSTK, bLGV, bLGU, bLGW, bVAL, bNXT, bSUCC, bHAM, bEND, poolSz] <;> omega)
  have hz' : ZeroFrom m₀ (bHD F N) := hz.mono (by lomega)
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, by simp [eSt], by simp [eSt],
    by simp [eSt], by simp [eSt], hz'.tab (by lomega) N, by simp, SameOn.refl _ _,
    hz.mono (by lomega), by lomega, by simp [eSt], by simp [eSt], by simp⟩
  · simp only [eSt, initAdj_nil, LL_nil]
    exact hz' _ (by lomega)
  · simp only [eSt, initAdj_nil, List.length_nil]
    exact hz' _ (by lomega)
  · simp only [eSt, Bool.false_eq_true, ↓reduceIte]
    exact hz' _ (by lomega)

/-! ### Step 2: the edges -/

/-- The invariant of the edge loop after `j` edges. -/
def EdgeInv (N : ℕ) (L : List Edge) (U V F : ℕ) (m₀ : ℕ → ℕ) (j : ℕ) (c : Config) : Prop :=
  Glob N L.length F c ∧ Inp N L.length U V c ∧ c.reg rNP = 1 + 2 * j ∧ c.reg rSP = 0 ∧
    c.reg rCNT = N ∧ c.reg rLC = 0 ∧ c.reg rPSP = 0 ∧
    EMem N L.length F m₀ (eSt N (L.take j) []) (fun _ => 0) [] (1 + 2 * j) c.mem

theorem deg_take_succ (L : List Edge) (j : ℕ) (hj : j < L.length) (hab : L[j].1 ≠ L[j].2) :
    (fun v => (initAdj (L.take (j + 1)) v).length) =
      Function.update (Function.update (fun v => (initAdj (L.take j) v).length) L[j].1
        ((initAdj (L.take j) L[j].1).length + 1)) L[j].2
        (Function.update (fun v => (initAdj (L.take j) v).length) L[j].1
          ((initAdj (L.take j) L[j].1).length + 1) L[j].2 + 1) := by
  funext v
  rw [initAdj_take_succ L j hj]
  simp only [Function.update_apply, Ne.symm hab, ↓reduceIte]
  split_ifs <;> simp

theorem edgeBody_spec (N : ℕ) (L : List Edge) (U V F : ℕ) (m₀ : ℕ → ℕ)
    (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) (hU : Arr m₀ U (L.map Prod.fst))
    (hV : Arr m₀ V (L.map Prod.snd)) (hUF : U + L.length ≤ F) (hVF : V + L.length ≤ F)
    (hS : bEND F N L.length ≤ S) (j : ℕ) (hj : j < L.length) :
    HTB S edgeBody (fun c => EdgeInv N L U V F m₀ j c ∧ c.reg rI = j ∧ c.reg gLN = L.length)
      (fun c => EdgeInv N L U V F m₀ (j + 1) c ∧ c.reg rI = j ∧ c.reg gLN = L.length) 40 := by
  refine HTB.run_le (by decide) (by decide)
    fun c ⟨⟨hg, hin, hnp, hsp, hcnt, hlc, hpsp, hm⟩, hi, hln⟩ => ?_
  have hab := hL L[j] (List.getElem_mem hj)
  have hra : c.mem (U + j) = L[j].1 := by
    rw [hm.same (U + j) (show U + j < bHD F N by lomega)]
    rw [hU.get (i := j) (by simp; omega), List.getElem_map]
  have hrb : c.mem (V + j) = L[j].2 := by
    rw [hm.same (V + j) (show V + j < bHD F N by lomega)]
    rw [hV.get (i := j) (by simp; omega), List.getElem_map]
  refine ⟨by ear_addr [edgeBody, prepend, incDeg, hin.lu, hin.lv, hi, hra, hrb, hg.hd, hg.val,
    hg.nxt, hg.deg, hnp], ?_⟩
  -- the two reads
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = run (.seq (ld rA gLU rI) (ld rB gLV rI)) c := ⟨_, rfl⟩
  have hA₂ : c₂.reg rA = L[j].1 := by rw [hc₂]; simp +decide [hin.lu, hi, hra]
  have hB₂ : c₂.reg rB = L[j].2 := by rw [hc₂]; simp +decide [hin.lv, hi, hrb]
  have hg₂ : Glob N L.length F c₂ := by
    rw [hc₂]; exact (Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg
  have hnp₂ : c₂.reg rNP = 1 + 2 * j := by rw [hc₂]; simp +decide [hnp]
  have hm₂ : c₂.mem = c.mem := by rw [hc₂]; exact run_mem_of_stores (by decide) (by decide) c
  rw [← hm₂, ← hnp₂] at hm
  -- the lists
  obtain ⟨c₅, hc₅⟩ : ∃ c₅, c₅ = run (prepend rA rB) c₂ := ⟨_, rfl⟩
  have hm₅ := prepend_emem (x := rA) (y := rB) (by decide) (by decide) hg₂ hm
    (by rw [hA₂]; omega) (by rw [hnp₂]; omega) (by rw [hnp₂]; lomega)
  rw [← hc₅, hA₂, hB₂] at hm₅
  have hg₅ : Glob N L.length F c₅ := by
    rw [hc₅]; exact (Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg₂
  have hA₅ : c₅.reg rA = L[j].1 := by rw [hc₅, prepend_reg _ _ (by decide)]; exact hA₂
  have hB₅ : c₅.reg rB = L[j].2 := by rw [hc₅, prepend_reg _ _ (by decide)]; exact hB₂
  obtain ⟨c₆, hc₆⟩ : ∃ c₆, c₆ = run (prepend rB rA) c₅ := ⟨_, rfl⟩
  have hnp₅ : c₅.reg rNP = 2 + 2 * j := by rw [hc₅, prepend_np (by decide), hnp₂]; omega
  have hm₆ := prepend_emem (x := rB) (y := rA) (by decide) (by decide) hg₅ hm₅
    (by rw [hB₅]; omega) (by rw [hnp₅]; omega) (by rw [hnp₅]; lomega)
  rw [← hc₆, hA₅, hB₅] at hm₆
  have hg₆ : Glob N L.length F c₆ := by
    rw [hc₆]; exact (Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg₅
  have hA₆ : c₆.reg rA = L[j].1 := by rw [hc₆, prepend_reg _ _ (by decide)]; exact hA₅
  have hB₆ : c₆.reg rB = L[j].2 := by rw [hc₆, prepend_reg _ _ (by decide)]; exact hB₅
  have hnp₆ : c₆.reg rNP = 1 + 2 * (j + 1) := by rw [hc₆, prepend_np (by decide), hnp₅]; omega
  rw [hnp₆] at hm₆
  -- the degrees
  obtain ⟨c₇, hc₇⟩ : ∃ c₇, c₇ = run (incDeg rA) c₆ := ⟨_, rfl⟩
  have hm₇ := incDeg_emem (x := rA) (by decide) hg₆ hm₆ (by rw [hA₆]; omega)
  rw [← hc₇, hA₆] at hm₇
  have hg₇ : Glob N L.length F c₇ := by
    rw [hc₇]; exact (Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg₆
  have hB₇ : c₇.reg rB = L[j].2 := by rw [hc₇, incDeg_reg _ (by decide)]; exact hB₆
  have hm₈ := incDeg_emem (x := rB) (by decide) hg₇ hm₇ (by rw [hB₇]; omega)
  rw [hB₇] at hm₈
  have hrun : run edgeBody c = run (incDeg rB) c₇ := by
    rw [hc₇, hc₆, hc₅, hc₂]; rfl
  have hfr : ∀ r, r ∉ wregs edgeBody → (run edgeBody c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (by decide) hr c
  refine ⟨⟨(Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg,
    (Inp.regIndep _ _ _ _).run_of_sub (by decide) (by decide) hin, ?_,
    (hfr rSP (by decide)).trans hsp, (hfr rCNT (by decide)).trans hcnt,
    (hfr rLC (by decide)).trans hlc, (hfr rPSP (by decide)).trans hpsp, ?_⟩,
    (hfr rI (by decide)).trans hi, (hfr gLN (by decide)).trans hln⟩
  · rw [hrun, incDeg_reg _ (by decide), hc₇, incDeg_reg _ (by decide), hnp₆]
  · rw [hrun]
    refine hm₈.congr ?_ ?_ rfl rfl rfl
    · simp only [eSt, initAdj_take_succ L j hj]
    · simp only [eSt]
      rw [deg_take_succ L j hj (by omega)]

/-- **Step 2**: the edge loop. -/
theorem edges_spec (N : ℕ) (L : List Edge) (U V F : ℕ) (m₀ : ℕ → ℕ)
    (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) (hU : Arr m₀ U (L.map Prod.fst))
    (hV : Arr m₀ V (L.map Prod.snd)) (hUF : U + L.length ≤ F) (hVF : V + L.length ≤ F)
    (hS : bEND F N L.length ≤ S) :
    HTB S (forUp rI gLN edgeBody) (fun c => EdgeInv N L U V F m₀ 0 c ∧ c.reg gLN = L.length)
      (fun c => EdgeInv N L U V F m₀ L.length c ∧ c.reg rI = L.length ∧ c.reg gLN = L.length)
      (L.length * (40 + 4) + 3) :=
  HTB.forUpC (i := rI) (n := gLN) (N := L.length) (body := edgeBody) (EdgeInv N L U V F m₀) 40
    (by decide) (by decide) (by decide) (fun j => by indep [EdgeInv, glob_iff, inp_iff])
    (fun j hj => edgeBody_spec N L U V F m₀ hL hU hV hUF hVF hS j hj)

/-! ### Step 3: the stack -/

/-- The invariant of the stack loop after `j` vertices. -/
def StkInv (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (j : ℕ) (c : Config) : Prop :=
  Glob N L.length F c ∧ c.reg rNP = 1 + 2 * L.length ∧ c.reg rSP = (stackPre L j).length ∧
    c.reg rCNT = N ∧ c.reg rLC = 0 ∧ c.reg rPSP = 0 ∧
    EMem N L.length F m₀ (eSt N L (stackPre L j).reverse) (fun _ => 0) [] (1 + 2 * L.length) c.mem

theorem stkBody_spec (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (hS : bEND F N L.length ≤ S)
    (j : ℕ) (hj : j < N) :
    HTB S stkBody (fun c => StkInv N L F m₀ j c ∧ c.reg rI = j ∧ c.reg gVN = N)
      (fun c => StkInv N L F m₀ (j + 1) c ∧ c.reg rI = j ∧ c.reg gVN = N) 12 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hg, hnp, hsp, hcnt, hlc, hpsp, hm⟩, hi, hn⟩ => ?_
  have hlen := length_stackPre_le L j
  refine ⟨by ear_addr [stkBody, push, hg.deg, hg.stk, hi, hsp], ?_⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = run (ld rD rDEG rI) c := ⟨_, rfl⟩
  have hd₁ : c₁.reg rD = (initAdj L j).length := by
    rw [hc₁, run_ld]
    simp +decide only [setReg_reg, ↓reduceIte, hg.deg, hi, hm.deg.get hj, eSt]
  have hfr : ∀ r, r ≠ rD → c₁.reg r = c.reg r := fun r hr => by
    rw [hc₁, run_ld]; simp [hr]
  have hm₁ : c₁.mem = c.mem := by rw [hc₁, run_ld, setReg_mem]
  have hg₁ : Glob N L.length F c₁ := by
    rw [hc₁]; exact (Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg
  have hrun : run stkBody c = run (ifEq rD rTWO (push rI) .skip) c₁ := by rw [hc₁]; rfl
  rw [hrun, run_ifEq (by decide) (by decide), hd₁, hfr rTWO (by decide), hg.two]
  rw [← hm₁] at hm
  have hsucc := stackPre_succ L j
  by_cases h2 : (initAdj L j).length = 2
  · simp only [h2, ↓reduceIte] at hsucc ⊢
    have hg₂ := (Glob.regIndep N L.length F).setReg (d := rT) (by decide) 0 hg₁
    have hm₂ := push_emem (x := rI) (c := c₁.setReg rT 0) (by decide) hg₂ hm
      (by simp +decide [hfr, hsp, eSt]) (by simp [eSt]; omega)
    have hfr₂ : ∀ r, r ≠ rT → r ≠ rSP → r ≠ rD →
        (run (push rI) (c₁.setReg rT 0)).reg r = c.reg r := fun r h1 h2 h3 => by
      rw [push_reg _ ⟨h1, h2⟩]; simp [h1, hfr r h3]
    refine ⟨⟨(Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg₂, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ?_, ?_⟩
    · rw [hfr₂ rNP (by decide) (by decide) (by decide), hnp]
    · rw [push_sp (by decide)]; simp +decide [hfr, hsp, hsucc]
    · rw [hfr₂ rCNT (by decide) (by decide) (by decide), hcnt]
    · rw [hfr₂ rLC (by decide) (by decide) (by decide), hlc]
    · rw [hfr₂ rPSP (by decide) (by decide) (by decide), hpsp]
    · refine hm₂.congr rfl rfl rfl ?_ rfl
      simp +decide [eSt, hsucc, hfr, hi]
    · rw [hfr₂ rI (by decide) (by decide) (by decide), hi]
    · rw [hfr₂ gVN (by decide) (by decide) (by decide), hn]
  · simp only [h2, ↓reduceIte, run_skip, List.append_nil] at hsucc ⊢
    refine ⟨⟨(Glob.regIndep _ _ _).setReg (by decide) _ hg₁, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp +decide [hfr, hnp]
    · simp +decide [hfr, hsp, hsucc]
    · simp +decide [hfr, hcnt]
    · simp +decide [hfr, hlc]
    · simp +decide [hfr, hpsp]
    · rw [hsucc]; exact hm
    · simp +decide [hfr, hi]
    · simp +decide [hfr, hn]

/-- **Step 3**: the stack loop. -/
theorem stk_spec (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (hS : bEND F N L.length ≤ S) :
    HTB S (forUp rI gVN stkBody) (fun c => StkInv N L F m₀ 0 c ∧ c.reg gVN = N)
      (fun c => StkInv N L F m₀ N c ∧ c.reg rI = N ∧ c.reg gVN = N) (N * (12 + 4) + 3) :=
  HTB.forUpC (i := rI) (n := gVN) (N := N) (body := stkBody) (StkInv N L F m₀) 12
    (by decide) (by decide) (by decide) (fun j => by indep [StkInv, glob_iff])
    (fun j hj => stkBody_spec N L F m₀ hS j hj)

/-- **Steps 1–3**: from `EarIn N L`, the machine holds `Ear.init N L` (the memory below `bHD`
being the initial one). -/
theorem init0_spec (N : ℕ) (L : List Edge) (c₀ : Config) (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N)
    (hS : bEND (c₀.reg rFREE) N L.length ≤ S) :
    HTB S (.seq (.seq allocs1 allocs2) (.seq (forUp rI gLN edgeBody) (forUp rI gVN stkBody)))
      (fun c => EarIn N L c ∧ c = c₀)
      (fun c => LRep N L (c₀.reg rFREE) c₀.mem (init N L) c ∧ c.reg rPSP = 0)
      (64 + (L.length * (40 + 4) + 3 + (N * (12 + 4) + 3))) := by
  refine HTB.of_forall fun c₁ ⟨hE, hc⟩ => ?_
  subst hc
  have h2 := allocs_spec (S := S) N L.length (c₁.reg gLU) (c₁.reg gLV) (c₁.reg rFREE) c₁.mem hE.free
  have h3 := (edges_spec N L (c₁.reg gLU) (c₁.reg gLV) (c₁.reg rFREE) c₁.mem hL hE.lu hE.lv
    hE.below.1 hE.below.2 hS).pre
    (P' := fun c => AllocPost N L.length (c₁.reg gLU) (c₁.reg gLV) (c₁.reg rFREE) c₁.mem c)
    fun c ⟨hg, hin, hnp, hsp, hcnt, hlc, hpsp, hm⟩ =>
      ⟨⟨hg, hin, by simp [hnp], hsp, hcnt, hlc, hpsp, by simpa using hm⟩, hin.ln⟩
  have h4 := (stk_spec N L (c₁.reg rFREE) c₁.mem hS).pre
    (P' := fun c => EdgeInv N L (c₁.reg gLU) (c₁.reg gLV) (c₁.reg rFREE) c₁.mem L.length c ∧
      c.reg rI = L.length ∧ c.reg gLN = L.length)
    fun c ⟨⟨hg, hin, hnp, hsp, hcnt, hlc, hpsp, hm⟩, _, _⟩ =>
      ⟨⟨hg, hnp, by simp [hsp, stackPre], hcnt, hlc, hpsp, by simpa [stackPre] using hm⟩, hin.vn⟩
  refine ((h2.seq (h3.seq h4)).post fun c ⟨⟨hg, hnp, hsp, hcnt, hlc, hpsp, hm⟩, _, _⟩ => ?_).pre
    fun c hc => by subst hc; exact ⟨⟨hE.zero, hE.one, hE.vn, hE.ln, rfl, rfl⟩, rfl, rfl⟩
  rw [init_eq_eSt]
  refine ⟨⟨hg, by simp [eSt, hsp], hcnt, by simp [eSt, hlc], by omega, ?_, by rw [hnp]; exact hm⟩,
    hpsp⟩
  simp only [eSt, hnp, poolSz]
  omega

end STACS2027.RAM.EarR
