module

public import Outerplanar.RAM.EarLoop
import Mathlib.Tactic

/-!
# The ear-elimination machine: the reconstruction

From the final state `S = loop (4 N + 1) (init N L)` of the elimination:

1. the search for the first three alive vertices `x`, `y`, `z` (`triBody_spec`: after `j`
   vertices, `rX`, `rY`, `rZ` are the entries `0, 1, 2` of the alive vertices below `j`);
2. the successors of the triangle (`succInit_spec`): the table `succ0Of S N`;
3. the reinsertion of the logged vertices, last eliminated first (`reinsBody_spec`: after `i`
   entries the table `(S.log.take i).foldl reinsert (succ0Of S N)`; the log is stored in
   elimination order and read backwards);
4. the walk (`walkBody_spec`): after `i` steps the output holds the first `i` entries of
   `walk succ N x`.

`recon_spec`: the output array `gHAM` holds `Ear.earHam N L` (`earHam_eq`). The triples are
`HTB S` triples, for any bound `S ≥ bEND F N |L|` of the layout.
-/

@[expose] public section

namespace STACS2027.RAM.EarR

open STACS2027 STACS2027.Ear

variable {N : ℕ} {L : List Edge} {F : ℕ} {m₀ : ℕ → ℕ} {S : ℕ}

/-! ### Abstract side -/

/-- The alive vertices below `j`. -/
def triPre (s : State) (j : ℕ) : List ℕ := (List.range j).filter fun v => s.dead v = false

/-- The successors of the triangle of the first three alive vertices. -/
def succ0Of (s : State) (N : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (fun _ => 0) ((triPre s N).getD 0 0)
    ((triPre s N).getD 1 0)) ((triPre s N).getD 1 0) ((triPre s N).getD 2 0))
    ((triPre s N).getD 2 0) ((triPre s N).getD 0 0)

theorem earHam_eq (N : ℕ) (L : List Edge) :
    earHam N L = walk ((loop (4 * N + 1) (init N L)).log.foldl reinsert
      (succ0Of (loop (4 * N + 1) (init N L)) N)) N
      ((triPre (loop (4 * N + 1) (init N L)) N).getD 0 0) := rfl

theorem triPre_succ (s : State) (j : ℕ) :
    triPre s (j + 1) = triPre s j ++ (if s.dead j = false then [j] else []) := by
  simp only [triPre, List.range_succ, List.filter_append, List.filter_singleton]
  split_ifs with h <;> simp [h]

theorem triPre_lt (s : State) (j : ℕ) : ∀ x ∈ triPre s j, x < j := fun x hx => by
  simp only [triPre, List.mem_filter, List.mem_range] at hx
  exact hx.1

theorem good_loop {N : ℕ} (hN : 0 < N) : ∀ (f : ℕ) {s : State}, Good N s → Good N (loop f s)
  | 0, _, h => h
  | f + 1, s, h => by
    unfold loop
    split
    · next hc => exact good_loop hN f (good_step h hN hc)
    · exact h

theorem rev_map_get {α : Type*} (f : α → ℕ) (l : List α) (i : ℕ) (hi : i < l.length) :
    (l.reverse.map f)[l.length - 1 - i]'(by simp; omega) = f l[i] := by
  rw [List.getElem_map, List.getElem_reverse]
  congr 2
  omega

/-! ### The representation during the reconstruction -/

/-- The machine during the reconstruction: the final state `s`, the successor table `succ`, the
output prefix `ham`. -/
@[mk_iff] structure RRep (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (s : State) (succ : ℕ → ℕ)
    (ham : List ℕ) (c : Config) : Prop where
  glob : Glob N L.length F c
  lc : c.reg rLC = s.log.length
  mem : EMem N L.length F m₀ s succ ham (c.reg rNP) c.mem

theorem RRep.indep (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (s : State) (succ : ℕ → ℕ)
    (ham : List ℕ) :
    Indep [rT, rI, rA, rB, rV, rU, rW, rX, rK, rP, rQ, rZ, rD, rY, rC] (RRep N L F m₀ s succ ham) := by
  indep [rRep_iff, glob_iff]

/-! ### Step 1: the three surviving vertices -/

theorem triUpd_K (c : Config) : (run triUpd c).reg rK = c.reg rK + 1 := by
  simp +decide only [triUpd, run_seq', run_ifz', run_mov (show rI ≠ rT by decide),
    run_subc (show rK ≠ rT by decide), run_inc (show rK ≠ rT by decide), run_skip, setReg_reg,
    ↓reduceIte]
  split_ifs <;> simp +decide

theorem triUpd_X (c : Config) :
    (run triUpd c).reg rX = if c.reg rK = 0 then c.reg rI else c.reg rX := by
  simp +decide only [triUpd, run_seq', run_ifz', run_mov (show rI ≠ rT by decide),
    run_subc (show rK ≠ rT by decide), run_inc (show rK ≠ rT by decide), run_skip, setReg_reg,
    ↓reduceIte]
  split_ifs <;> simp +decide

theorem triUpd_Y (c : Config) :
    (run triUpd c).reg rY = if c.reg rK = 1 then c.reg rI else c.reg rY := by
  simp +decide only [triUpd, run_seq', run_ifz', run_mov (show rI ≠ rT by decide),
    run_subc (show rK ≠ rT by decide), run_inc (show rK ≠ rT by decide), run_skip, setReg_reg,
    ↓reduceIte]
  split_ifs <;> simp +decide <;> omega

theorem triUpd_Z (c : Config) :
    (run triUpd c).reg rZ = if c.reg rK = 2 then c.reg rI else c.reg rZ := by
  simp +decide only [triUpd, run_seq', run_ifz', run_mov (show rI ≠ rT by decide),
    run_subc (show rK ≠ rT by decide), run_inc (show rK ≠ rT by decide), run_skip, setReg_reg,
    ↓reduceIte]
  split_ifs <;> simp +decide <;> omega

theorem triUpd_reg (c : Config) {r : ℕ} (hr : r ∉ [rX, rY, rZ, rQ, rT, rK]) :
    (run triUpd c).reg r = c.reg r := by
  have h : ∀ r ∈ wregs triUpd, r ∈ [rX, rY, rZ, rQ, rT, rK] := by decide
  exact run_reg_of_not_mem (by decide) (fun h' => hr (h r h')) c

/-- The invariant of the search after `j` vertices. -/
def TriInv (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (s : State) (j : ℕ) (c : Config) : Prop :=
  LRep N L F m₀ s c ∧ c.reg rK = (triPre s j).length ∧ c.reg rX = (triPre s j).getD 0 0 ∧
    c.reg rY = (triPre s j).getD 1 0 ∧ c.reg rZ = (triPre s j).getD 2 0

theorem triBody_spec (s : State) (hS : bEND F N L.length ≤ S) (j : ℕ) (hj : j < N) :
    HTB S triBody (fun c => TriInv N L F m₀ s j c ∧ c.reg rI = j ∧ c.reg gVN = N)
      (fun c => TriInv N L F m₀ s (j + 1) c ∧ c.reg rI = j ∧ c.reg gVN = N) 20 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hK, hX, hY, hZ⟩, hi, hn⟩ => ?_
  refine ⟨by ear_addr [triBody, triUpd, hR.glob.dead, hi], ?_⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = run (ld rA rDEAD rI) c := ⟨_, rfl⟩
  have hA₁ : c₁.reg rA = if s.dead j = true then 1 else 0 := by
    rw [hc₁, run_ld]
    simp +decide only [setReg_reg, ↓reduceIte, hR.glob.dead, hi]
    exact hR.mem.dead.get hj
  have hr₁ : ∀ r, r ≠ rA → c₁.reg r = c.reg r := fun r h => by rw [hc₁, run_ld]; simp [h]
  have hrun : run triBody c = if s.dead j = false then run triUpd c₁ else c₁ := by
    show run (.ifz rA triUpd .skip) (run (ld rA rDEAD rI) c) = _
    rw [← hc₁, run_ifz', hA₁]
    cases s.dead j <;> simp
  have hfr : ∀ r, r ∉ wregs triBody → (run triBody c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (by decide) hr c
  have hsucc := triPre_succ s j
  have hK' : (triPre s j).length = c.reg rK := hK.symm
  refine ⟨⟨((LRep.indep N L F m₀ s).mono (by decide)).run (by decide) (by decide) (by decide) hR,
    ?_, ?_, ?_, ?_⟩, (hfr rI (by decide)).trans hi, (hfr gVN (by decide)).trans hn⟩
  · rw [hrun, hsucc]
    cases hd : s.dead j <;> simp [triUpd_K, hr₁ rK (by decide), hK]
  · rw [hrun, hsucc]
    cases hd : s.dead j
    · simp only [↓reduceIte, triUpd_X, hr₁ rK (by decide), hr₁ rI (by decide),
        hr₁ rX (by decide), hi, getD_snoc, hK']
      by_cases hk0 : c.reg rK = 0
      · simp [hk0]
      · simp [hk0, hX, Nat.pos_of_ne_zero hk0]
    · simp [hr₁ rX (by decide), hX]
  · rw [hrun, hsucc]
    cases hd : s.dead j
    · simp only [↓reduceIte, triUpd_Y, hr₁ rK (by decide), hr₁ rI (by decide),
        hr₁ rY (by decide), hi, getD_snoc, hK']
      by_cases hk0 : c.reg rK = 0
      · have h0 : triPre s j = [] := List.length_eq_zero_iff.mp (by omega)
        simp [hk0, hY, h0]
      · by_cases hk1 : c.reg rK = 1
        · simp [hk1]
        · have h2 : 1 < c.reg rK := by omega
          simp [hk1, hY, h2]
    · simp [hr₁ rY (by decide), hY]
  · rw [hrun, hsucc]
    cases hd : s.dead j
    · simp only [↓reduceIte, triUpd_Z, hr₁ rK (by decide), hr₁ rI (by decide),
        hr₁ rZ (by decide), hi, getD_snoc, hK']
      by_cases hk2 : c.reg rK = 2
      · simp [hk2]
      · by_cases hk3 : 2 < c.reg rK
        · simp [hk2, hZ, hk3]
        · have h2 : (triPre s j).getD 2 0 = 0 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
          simp only [hk2, hk3, ↓reduceIte, show ¬ (2 = c.reg rK) by omega, hZ, h2]
    · simp [hr₁ rZ (by decide), hZ]

/-! ### Step 2: the triangle -/

theorem succInit_spec (s : State) (hN : 0 < N) (hS : bEND F N L.length ≤ S) :
    HTB S succInit (fun c => TriInv N L F m₀ s N c)
      (fun c => RRep N L F m₀ s (succ0Of s N) [] c ∧ c.reg rX = (triPre s N).getD 0 0) 6 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hR, _, hX, hY, hZ⟩ => ?_
  have hlt := fun i => getD_lt (triPre_lt s N) hN i
  have h0 := hlt 0
  have h1 := hlt 1
  have h2 := hlt 2
  refine ⟨by ear_addr [succInit, hR.glob.succ, hX, hY, hZ], ?_⟩
  have hm := hR.mem
  have hg := hR.glob
  have hfr : ∀ r, r ∉ wregs succInit → (run succInit c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (by decide) hr c
  have hmem : (run succInit c).mem = upd (upd (upd c.mem (bSUCC F N L.length + c.reg rX) (c.reg rY))
      (bSUCC F N L.length + c.reg rY) (c.reg rZ)) (bSUCC F N L.length + c.reg rZ) (c.reg rX) := by
    simp +decide only [succInit, run_seq', run_st (show rY ≠ rT by decide),
      run_st (show rZ ≠ rT by decide), run_st (show rX ≠ rT by decide), setReg_reg, setReg_mem,
      setMem_mem_upd, setMem_reg, ↓reduceIte, hg.succ]
  refine ⟨⟨(Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg,
    (hfr rLC (by decide)).trans hR.lc, ?_⟩, (hfr rX (by decide)).trans hX⟩
  rw [hfr rNP (by decide), hmem, hX, hY, hZ]
  exact ((hm.setSucc _ (hlt 0)).setSucc _ (hlt 1)).setSucc _ (hlt 2)

/-! ### Step 3: the reinsertions -/

/-- The invariant of the reinsertions after `i` log entries. -/
def ReInv (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (s : State) (x : ℕ) (i : ℕ) (c : Config) :
    Prop :=
  RRep N L F m₀ s ((s.log.take i).foldl reinsert (succ0Of s N)) [] c ∧ c.reg rX = x

theorem reinsBody_spec (s : State) (hG : Good N s) (x : ℕ) (hS : bEND F N L.length ≤ S) (i : ℕ)
    (hi : i < s.log.length) :
    HTB S reinsBody (fun c => ReInv N L F m₀ s x i c ∧ c.reg rI = i ∧ c.reg rLC = s.log.length)
      (fun c => ReInv N L F m₀ s x (i + 1) c ∧ c.reg rI = i ∧ c.reg rLC = s.log.length) 27 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hX⟩, hI, hLC⟩ => ?_
  have hm := hR.mem
  have hg := hR.glob
  have he := hG.log_lt s.log[i] (List.getElem_mem hi)
  set f := (s.log.take i).foldl reinsert (succ0Of s N) with hf
  have hV : c.mem (bLGV F N + (s.log.length - i - 1)) = s.log[i].1 := by
    rw [hm.lgv.get' (i := s.log.length - 1 - i) (by simp; omega) (by omega), rev_map_get _ _ _ hi]
  have hU : c.mem (bLGU F N + (s.log.length - i - 1)) = s.log[i].2.1 := by
    rw [hm.lgu.get' (i := s.log.length - 1 - i) (by simp; omega) (by omega), rev_map_get _ _ _ hi]
  have hW : c.mem (bLGW F N + (s.log.length - i - 1)) = s.log[i].2.2 := by
    rw [hm.lgw.get' (i := s.log.length - 1 - i) (by simp; omega) (by omega), rev_map_get _ _ _ hi]
  have hSu : c.mem (bSUCC F N L.length + s.log[i].2.1) = f s.log[i].2.1 := hm.sucT.get he.2.1
  have hlog := hm.logS
  refine ⟨by ear_addr [reinsBody, hg.lgv, hg.lgu, hg.lgw, hg.succ, hLC, hI, hV, hU, hW], ?_⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = run (.seq (.sub rP rLC rI) (.seq (dec rP) (.seq (ld rV rLGV rP)
      (.seq (ld rU rLGU rP) (.seq (ld rW rLGW rP) (ld rQ rSUCC rU)))))) c := ⟨_, rfl⟩
  have hV₁ : c₁.reg rV = s.log[i].1 := by
    rw [hc₁]; simp +decide [run_dec, hLC, hI, hg.lgv, hV]
  have hU₁ : c₁.reg rU = s.log[i].2.1 := by
    rw [hc₁]; simp +decide [run_dec, hLC, hI, hg.lgu, hU]
  have hW₁ : c₁.reg rW = s.log[i].2.2 := by
    rw [hc₁]; simp +decide [run_dec, hLC, hI, hg.lgw, hW]
  have hQ₁ : c₁.reg rQ = f s.log[i].2.1 := by
    rw [hc₁]; simp +decide [run_dec, hLC, hI, hg.lgu, hU, hg.succ, hSu]
  have hm₁ : c₁.mem = c.mem := by rw [hc₁]; exact run_mem_of_stores (by decide) (by decide) c
  have hr₁ : ∀ r, r ∉ [rP, rT, rV, rU, rW, rQ] → c₁.reg r = c.reg r := fun r hr => by
    have h : ∀ r ∈ wregs (.seq (.sub rP rLC rI) (.seq (dec rP) (.seq (ld rV rLGV rP)
        (.seq (ld rU rLGU rP) (.seq (ld rW rLGW rP) (ld rQ rSUCC rU)))))), r ∈ [rP, rT, rV, rU, rW, rQ] := by
      decide
    rw [hc₁]; exact run_reg_of_not_mem (by decide) (fun h' => hr (h r h')) c
  have hrun : run reinsBody c = run (ifEq rQ rW (.seq (st rSUCC rU rV) (st rSUCC rV rW))
      (.seq (st rSUCC rW rV) (st rSUCC rV rU))) c₁ := by rw [hc₁]; rfl
  have hfold := foldl_take_succ reinsert (succ0Of s N) s.log i hi
  rw [← hf] at hfold
  have hfr : ∀ r, r ∉ wregs reinsBody → (run reinsBody c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (by decide) hr c
  refine ⟨⟨⟨(Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg,
    (hfr rLC (by decide)).trans hR.lc, ?_⟩, (hfr rX (by decide)).trans hX⟩,
    (hfr rI (by decide)).trans hI, (hfr rLC (by decide)).trans hLC⟩
  rw [hfr rNP (by decide), hrun, run_ifEq (by decide) (by decide), hQ₁, hW₁, hfold]
  rw [← hm₁] at hm
  have hS₁ : c₁.reg rSUCC = bSUCC F N L.length := (hr₁ rSUCC (by decide)).trans hg.succ
  have hre : reinsert f s.log[i] = if f s.log[i].2.1 = s.log[i].2.2 then
      Function.update (Function.update f s.log[i].2.1 s.log[i].1) s.log[i].1 s.log[i].2.2
      else Function.update (Function.update f s.log[i].2.2 s.log[i].1) s.log[i].1 s.log[i].2.1 := rfl
  rw [hre]
  by_cases hfu : f s.log[i].2.1 = s.log[i].2.2
  · simp +decide only [hfu, ↓reduceIte, run_seq', run_st (show rV ≠ rT by decide),
      run_st (show rW ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd, setMem_reg,
      hS₁, hU₁, hV₁, hW₁]
    exact (hm.setSucc _ he.2.1).setSucc _ he.1
  · simp +decide only [hfu, ↓reduceIte, run_seq', run_st (show rV ≠ rT by decide),
      run_st (show rU ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd, setMem_reg,
      hS₁, hU₁, hV₁, hW₁]
    exact (hm.setSucc _ he.2.2).setSucc _ he.1

/-! ### Step 4: the walk -/

/-- The invariant of the walk after `i` steps. -/
def WInv (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (s : State) (succ : ℕ → ℕ) (x : ℕ) (i : ℕ)
    (c : Config) : Prop :=
  RRep N L F m₀ s succ ((walk succ N x).take i) c ∧ c.reg rC = succ^[i] x

theorem walkBody_spec (s : State) (succ : ℕ → ℕ) (hsucc : ∀ y, succ y < N) (x : ℕ) (hx : x < N)
    (hS : bEND F N L.length ≤ S) (i : ℕ) (hi : i < N) :
    HTB S walkBody (fun c => WInv N L F m₀ s succ x i c ∧ c.reg rI = i ∧ c.reg gVN = N)
      (fun c => WInv N L F m₀ s succ x (i + 1) c ∧ c.reg rI = i ∧ c.reg gVN = N) 4 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hC⟩, hI, hn⟩ => ?_
  have hm := hR.mem
  have hg := hR.glob
  have hlen : ((walk succ N x).take i).length = i := by simp; omega
  have hCi := iterate_lt hsucc hx i
  refine ⟨by ear_addr [walkBody, hg.ham, hg.succ, hI, hC], ?_⟩
  have hfr : ∀ r, r ∉ wregs walkBody → (run walkBody c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (by decide) hr c
  have hmem : (run walkBody c).mem = upd c.mem (bHAM F N L.length + i) (succ^[i] x) := by
    simp +decide only [walkBody, run_seq', run_st (show rC ≠ rT by decide), run_ld, setReg_mem,
      setMem_mem_upd, setReg_reg, ↓reduceIte, hg.ham, hI, hC]
  have hm' := hm.hamSnoc (succ^[i] x) (by omega)
  rw [hlen] at hm'
  have htake : (walk succ N x).take (i + 1) = (walk succ N x).take i ++ [succ^[i] x] := by
    rw [take_succ_eq _ i (by simp; omega), walk_getElem]
  refine ⟨⟨⟨(Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg,
    (hfr rLC (by decide)).trans hR.lc, ?_⟩, ?_⟩, (hfr rI (by decide)).trans hI,
    (hfr gVN (by decide)).trans hn⟩
  · rw [hfr rNP (by decide), hmem, htake]; exact hm'
  · have hRC : (run walkBody c).reg rC = upd c.mem (bHAM F N L.length + i) (succ^[i] x)
        (bSUCC F N L.length + succ^[i] x) := by
      simp +decide only [walkBody, run_seq', run_st (show rC ≠ rT by decide), run_ld, setReg_mem,
        setMem_mem_upd, setReg_reg, ↓reduceIte, hg.ham, hI, hC, setMem_reg, hg.succ]
    rw [hRC, Function.iterate_succ_apply', ← hm'.sucT.get hCi, ← hmem]

end STACS2027.RAM.EarR
