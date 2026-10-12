module

public import Outerplanar.RAM.PairIds
import Mathlib.Tactic

/-!
# First-occurrence identifiers: ranks from leaders

`rankIds` turns a **leader array** `LEAD = ps.map (ps.idxOf ·)` (at `rLD`, `L = |ps|` cells,
`rPL = L`) into the identifiers in order of first appearance, for a list `ps` of elements of
any type (the machine never reads the elements, only their leaders):

* `EID = eids ps` (`EID[q] = ps.eraseDups.idxOf ps[q]`, at `rID`, `L` cells),
* `NE = |ps.eraseDups|` (in `rNE`),
* `CNT[e] = (eids ps).count e` (the size of the class `e`, at `rCT`, `L` cells),

in `O(L)` steps and `2L` fresh cells (`rankIds_spec`):

1. `rankAlloc`: `EID`, `CNT` (`L` cells each), `NE := 0`;
2. `stepRnk`: for `q < L`: `EID[q] := (LEAD[q] = q) ? NE++ : EID[LEAD[q]]`
   (`idxOf_eraseDups_of_not_mem`, `eraseDups_take_succ`);
3. `stepCnt`: for `q < L`: `CNT[EID[q]]++`.

`pairIds = pairLeads; rankIds` (`pairIds_spec`) computes all of them for a list of pairs with
components below `N`, in `O(N + L)` steps and space. Any other way of producing the leaders
(e.g. a leader pass over a list sorted by labels) can be followed by `rankIds`.
-/

@[expose] public section

namespace STACS2027.RAM.PairIds

open STACS2027.Algo

variable {S : ℕ}

/-! ### The program -/

/-- `EID`, `CNT` (`L` cells each), `NE := 0`. -/
def rankAlloc : Stmt := .seq (alloc rID rPL) (.seq (alloc rCT rPL) (.const rNE 0))
/-- A first occurrence: `EID[q] := NE`, `NE++`. -/
def rnkNew : Stmt := .seq (st rID rJ rNE) (inc rNE)
/-- A later occurrence: `EID[q] := EID[LEAD[q]]`. -/
def rnkOld : Stmt := .seq (ld rY rID rX) (st rID rJ rY)
/-- One index of the rank pass. -/
def rnkBody : Stmt := .seq (ld rX rLD rJ) (ifEq rX rJ rnkNew rnkOld)
/-- The rank pass. -/
def stepRnk : Stmt := forUp rJ rPL rnkBody
/-- `CNT[EID[q]]++`. -/
def cntBody : Stmt := .seq (ld rY rID rJ) (.seq (ld rX rCT rY) (.seq (inc rX) (st rCT rY rX)))
/-- The class sizes. -/
def stepCnt : Stmt := forUp rJ rPL cntBody

/-- **The identifiers in order of first appearance, from the leaders.** -/
def rankIds : Stmt := .seq rankAlloc (.seq stepRnk stepCnt)

/-- **First-occurrence identifiers of pairs.** -/
def pairIds : Stmt := .seq pairLeads rankIds

/-! ### The abstract side -/

section abs

variable {α : Type} [BEq α] [LawfulBEq α]

/-- The identifiers: the index of each element among the distinct elements. -/
def eids (ps : List α) : List ℕ := ps.map (ps.eraseDups.idxOf ·)

omit [LawfulBEq α] in
@[simp] theorem length_eids (ps : List α) : (eids ps).length = ps.length := by simp [eids]

theorem eids_lt (ps : List α) {q : ℕ} (hq : q < ps.length) :
    (eids ps)[q]'(by simpa using hq) < ps.eraseDups.length := by
  simp only [eids, List.getElem_map]
  exact idxOf_eraseDups_lt ps hq

theorem count_take_succ (l : List ℕ) {q : ℕ} (hq : q < l.length) (e : ℕ) :
    (l.take (q + 1)).count e = (l.take q).count e + if l[q] = e then 1 else 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hq, Option.toList_some, List.count_append,
    List.count_singleton]
  split <;> simp_all

end abs

/-! ### The rank pass -/

section rank

variable {α : Type} [BEq α] [LawfulBEq α] {ps : List α}

/-- The input of `rankIds`: the leaders of `ps` below the free address. -/
structure RIn (ps : List α) (c : Config) : Prop where
  pl : c.reg rPL = ps.length
  ld : Arr c.mem (c.reg rLD) (ps.map (ps.idxOf ·))
  below : c.reg rLD + ps.length ≤ c.reg rFREE
  free : ZeroFrom c.mem (c.reg rFREE)

/-- The registers fixed by the passes, for `L` elements (`c₀`: the configuration on entry). -/
@[mk_iff] structure RGlob (L : ℕ) (c₀ c : Config) : Prop where
  pl : c.reg rPL = L
  ld : c.reg rLD = c₀.reg rLD
  id : c.reg rID = c₀.reg rFREE
  ct : c.reg rCT = c₀.reg rFREE + L
  free : c.reg rFREE = c₀.reg rFREE + L + L

/-- The registers written by the passes. -/
def WR : List ℕ := [rT, rJ, rX, rY, rNE]

theorem RGlob.regIndep (L : ℕ) (c₀ : Config) : RegIndep WR (RGlob L c₀) := by
  indep [rGlob_iff]

/-- The invariant of the rank pass after `q` indices. -/
def RnkInv (ps : List α) (c₀ : Config) (q : ℕ) (c : Config) : Prop :=
  RGlob ps.length c₀ c ∧ c.reg rNE = (ps.take q).eraseDups.length ∧
    SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧ Arr c.mem (c₀.reg rFREE) ((eids ps).take q) ∧
    ZeroFrom c.mem (c₀.reg rFREE + ps.length)

theorem rnkBody_spec (c₀ : Config) (hIn : RIn ps c₀)
    (hS : c₀.reg rFREE + ps.length + ps.length ≤ S) (q : ℕ) (hq : q < ps.length) :
    HTB S rnkBody (fun c => RnkInv ps c₀ q c ∧ c.reg rJ = q ∧ c.reg rPL = ps.length)
      (fun c => RnkInv ps c₀ (q + 1) c ∧ c.reg rJ = q ∧ c.reg rPL = ps.length) 18 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hne, hsame, hA, hZ⟩, hj, hl⟩ => ?_
  have hb := hIn.below
  have hlq := idxOf_getElem_le ps hq
  have hx : c.mem (c₀.reg rLD + q) = ps.idxOf ps[q] := by
    rw [(hIn.ld.of_below hsame (by simpa using hb)).get (by simpa using hq), List.getElem_map]
  have heq : (eids ps).take (q + 1) = (eids ps).take q ++ [ps.eraseDups.idxOf ps[q]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hq), Option.toList_some]
    simp [eids]
  have hlen : ((eids ps).take q).length = q := by simp; omega
  have hlt := idxOf_eraseDups_lt ps hq
  have hle := R0.length_eraseDups_le ps
  by_cases hfirst : ps.idxOf ps[q] = q
  · -- a first occurrence
    have hnot := (idxOf_getElem_eq_self_iff ps hq).mp hfirst
    have hid := idxOf_eraseDups_of_not_mem ps hq hnot
    have hrun : run rnkBody c = (((c.setReg rX q).setReg rT 0).setMem (c₀.reg rFREE + q)
        (ps.take q).eraseDups.length |>.setReg rT (c₀.reg rFREE + q) |>.setReg rT 1).setReg rNE
          ((ps.take q).eraseDups.length + 1) := by
      simp +decide only [rnkBody, rnkNew, run_seq', run_ld, run_ifEq (show rX ≠ rT by decide)
        (show rJ ≠ rT by decide), run_st (show rNE ≠ rT by decide), run_inc (show rNE ≠ rT by decide),
        setReg_reg, setMem_reg, ↓reduceIte, hG.ld, hG.id, hj, hx, hfirst, hne]
    refine ⟨by addr_ok [rnkBody, rnkNew, rnkOld, hG.ld, hG.id, hj, hx, hfirst], ?_⟩
    rw [hrun]
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide only [setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte]
    · exact hG.pl
    · exact hG.ld
    · exact hG.id
    · exact hG.ct
    · exact hG.free
    · rw [eraseDups_take_succ ps hq]
      simp only [hfirst, ↓reduceIte, List.length_append, List.length_singleton]
    · exact hsame.upd_of_ge (by omega) _
    · rw [heq, ← hid]; exact hA.upd_snoc (by omega)
    · exact hZ.upd (by omega)
    · exact hj
    · exact hl
  · -- a later occurrence: the identifier of the leader
    have hy : c.mem (c₀.reg rFREE + ps.idxOf ps[q]) = ps.eraseDups.idxOf ps[q] := by
      rw [hA.get (by omega), List.getElem_take]
      simp only [eids, List.getElem_map]
      rw [getElem_idxOf_getElem ps hq]
    have hrun : run rnkBody c = ((((c.setReg rX (ps.idxOf ps[q])).setReg rT
        (ps.idxOf ps[q] - q + (q - ps.idxOf ps[q]))).setReg rY (ps.eraseDups.idxOf ps[q])).setMem
          (c₀.reg rFREE + q) (ps.eraseDups.idxOf ps[q])).setReg rT (c₀.reg rFREE + q) := by
      simp +decide only [rnkBody, rnkOld, run_seq', run_ld, run_ifEq (show rX ≠ rT by decide)
        (show rJ ≠ rT by decide), run_st (show rY ≠ rT by decide), setReg_reg, setReg_mem,
        ↓reduceIte, hG.ld, hG.id, hj, hx, hfirst, hy]
    refine ⟨by addr_ok [rnkBody, rnkNew, rnkOld, hG.ld, hG.id, hj, hx, hfirst], ?_⟩
    rw [hrun]
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide only [setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte]
    · exact hG.pl
    · exact hG.ld
    · exact hG.id
    · exact hG.ct
    · exact hG.free
    · rw [eraseDups_take_succ ps hq]
      simp only [hfirst, ↓reduceIte]; exact hne
    · exact hsame.upd_of_ge (by omega) _
    · rw [heq]; exact hA.upd_snoc (by omega)
    · exact hZ.upd (by omega)
    · exact hj
    · exact hl

/-- **The rank pass**, in `22 L + 3` steps. -/
theorem stepRnk_spec (c₀ : Config) (hIn : RIn ps c₀)
    (hS : c₀.reg rFREE + ps.length + ps.length ≤ S) :
    HTB S stepRnk (fun c => RnkInv ps c₀ 0 c ∧ c.reg rPL = ps.length)
      (fun c => RnkInv ps c₀ ps.length c ∧ c.reg rJ = ps.length ∧ c.reg rPL = ps.length)
      (ps.length * 22 + 3) :=
  HTB.forUpC (i := rJ) (n := rPL) (N := ps.length) (body := rnkBody) (RnkInv ps c₀) 18
    (by decide) (by decide) (by decide) (fun j => by indep [RnkInv, rGlob_iff])
    (fun j hj => rnkBody_spec c₀ hIn hS j hj)

/-- The invariant of the counting pass after `q` indices. -/
def CtInv (ps : List α) (c₀ : Config) (q : ℕ) (c : Config) : Prop :=
  RGlob ps.length c₀ c ∧ c.reg rNE = ps.eraseDups.length ∧
    SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧ Arr c.mem (c₀.reg rFREE) (eids ps) ∧
    Tab c.mem (c₀.reg rFREE + ps.length) ps.length (fun e => ((eids ps).take q).count e) ∧
    ZeroFrom c.mem (c₀.reg rFREE + ps.length + ps.length)

theorem cntBody_spec (c₀ : Config) (hS : c₀.reg rFREE + ps.length + ps.length ≤ S) (q : ℕ)
    (hq : q < ps.length) :
    HTB S cntBody (fun c => CtInv ps c₀ q c ∧ c.reg rJ = q ∧ c.reg rPL = ps.length)
      (fun c => CtInv ps c₀ (q + 1) c ∧ c.reg rJ = q ∧ c.reg rPL = ps.length) 8 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hne, hsame, hA, hT, hZ⟩, hj, hl⟩ => ?_
  have hq' : q < (eids ps).length := by simpa using hq
  have hy : c.mem (c₀.reg rFREE + q) = (eids ps)[q] := hA.get hq'
  have hyl := eids_lt ps hq
  have hle := R0.length_eraseDups_le ps
  have hx : c.mem (c₀.reg rFREE + ps.length + (eids ps)[q]) = ((eids ps).take q).count (eids ps)[q] :=
    hT.get (by omega)
  have hrun : run cntBody c = ((((c.setReg rY (eids ps)[q]).setReg rX
      (((eids ps).take q).count (eids ps)[q])).setReg rT 1).setReg rX
        (((eids ps).take q).count (eids ps)[q] + 1) |>.setMem (c₀.reg rFREE + ps.length + (eids ps)[q])
          (((eids ps).take q).count (eids ps)[q] + 1)).setReg rT
        (c₀.reg rFREE + ps.length + (eids ps)[q]) := by
    simp +decide only [cntBody, run_seq', run_ld, run_inc (show rX ≠ rT by decide),
      run_st (show rX ≠ rT by decide), setReg_reg, setReg_mem, ↓reduceIte, hG.id, hG.ct, hj, hy, hx]
  refine ⟨by addr_ok [cntBody, hG.id, hG.ct, hj, hy], ?_⟩
  rw [hrun]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp +decide only [setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte]
  · exact hG.pl
  · exact hG.ld
  · exact hG.id
  · exact hG.ct
  · exact hG.free
  · exact hne
  · exact hsame.upd_of_ge (by omega) _
  · exact hA.upd_of_disjoint (by simp only [length_eids]; omega)
  · refine (hT.upd rfl).congr_fun fun e _ => ?_
    rw [count_take_succ _ hq']
    by_cases he : e = (eids ps)[q]
    · subst he; simp
    · rw [Function.update_of_ne he]; simp [Ne.symm he]
  · exact hZ.upd (by omega)
  · exact hj
  · exact hl

/-- **The counting pass**, in `12 L + 3` steps. -/
theorem stepCnt_spec (c₀ : Config) (hS : c₀.reg rFREE + ps.length + ps.length ≤ S) :
    HTB S stepCnt (fun c => CtInv ps c₀ 0 c ∧ c.reg rPL = ps.length)
      (fun c => CtInv ps c₀ ps.length c ∧ c.reg rJ = ps.length ∧ c.reg rPL = ps.length)
      (ps.length * 12 + 3) :=
  HTB.forUpC (i := rJ) (n := rPL) (N := ps.length) (body := cntBody) (CtInv ps c₀) 8
    (by decide) (by decide) (by decide) (fun j => by indep [CtInv, rGlob_iff])
    (fun j hj => cntBody_spec c₀ hS j hj)

/-- The result of `rankIds` (`c₀`: the configuration on entry). -/
structure ROut (ps : List α) (c₀ c : Config) : Prop where
  id : Arr c.mem (c.reg rID) (eids ps)
  ct : Tab c.mem (c.reg rCT) ps.length fun e => (eids ps).count e
  ne : c.reg rNE = ps.eraseDups.length
  rid : c.reg rID = c₀.reg rFREE
  rct : c.reg rCT = c₀.reg rFREE + ps.length
  free : c.reg rFREE = c₀.reg rFREE + ps.length + ps.length
  zero : ZeroFrom c.mem (c.reg rFREE)
  same : SameOn (· < c₀.reg rFREE) c₀.mem c.mem

/-- The constant of the running time of `rankIds`. -/
def CR : ℕ := 34

theorem rankIds_core (c₀ : Config) (hIn : RIn ps c₀) (hS : c₀.reg rFREE + ps.length + ps.length ≤ S) :
    HTB S rankIds (fun c => c = c₀) (fun c => CtInv ps c₀ ps.length c)
      (7 + ((ps.length * 22 + 3) + (ps.length * 12 + 3))) := by
  have h₁ : HTB S rankAlloc (fun c => c = c₀) (fun c => RnkInv ps c₀ 0 c ∧ c.reg rPL = ps.length) 7 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      simp only [rankAlloc, run_seq', run_alloc (show rPL ≠ rT by decide) (show rID ≠ rPL by decide),
        run_alloc (show rPL ≠ rT by decide) (show rCT ≠ rPL by decide), run_const]
      refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals simp +decide only [setReg_reg, setReg_mem, ↓reduceIte, hIn.pl, List.take_zero,
        List.eraseDups_nil, List.length_nil]
      · exact SameOn.refl _ _
      · exact arr_nil _ _
      · exact hIn.free.mono (by omega)
  have h₂ := (stepRnk_spec c₀ hIn hS).post (Q' := fun c => CtInv ps c₀ 0 c ∧ c.reg rPL = ps.length)
    fun c ⟨⟨hG, hne, hsame, hA, hZ⟩, _, hl⟩ => by
      rw [List.take_of_length_le (by simp)] at hA
      rw [List.take_length] at hne
      refine ⟨⟨hG, hne, hsame, hA, ?_, hZ.mono (by omega)⟩, hl⟩
      simpa using hZ.tab le_rfl ps.length
  exact h₁.seq (h₂.seq ((stepCnt_spec c₀ hS).post fun c h => h.1))

/-- **The identifiers in order of first appearance, from the leaders.** Given the leaders
`ps.map (ps.idxOf ·)` of a list `ps` (of any type) below the free address `F` (`RIn`),
`rankIds` stores `EID = eids ps` at `rID = F`, `CNT[e] = (eids ps).count e` at `rCT = F + L`
and `NE = |ps.eraseDups|` in `rNE`, within `CR * (L + 1)` steps, accessing only addresses below
any `S ≥ F + 2L`, allocating fresh memory only, without output. -/
theorem rankIds_spec (ps : List α) (c₀ : Config) (hS : c₀.reg rFREE + ps.length + ps.length ≤ S) :
    HTB S rankIds (fun c => RIn ps c ∧ c = c₀) (fun c => ROut ps c₀ c ∧ Frame rankIds c₀ c)
      (CR * (ps.length + 1)) := by
  intro c ⟨hIn, hc⟩
  subst hc
  obtain ⟨c', t, he, ⟨hG, hne, hsame, hA, hT, hZ⟩, ht⟩ := rankIds_core c hIn hS c rfl
  rw [List.take_of_length_le (by simp)] at hT
  refine ⟨c', t, he, ⟨⟨by rw [hG.id]; exact hA, by rw [hG.ct]; exact hT, hne, hG.id, hG.ct,
    hG.free, by rw [hG.free]; exact hZ, hsame⟩, he.frame⟩, by simp only [CR]; omega⟩

/-- The registers written by `rankIds`. -/
theorem rankIds_wregs : ∀ r ∈ wregs rankIds, r = rT ∨ r = rFREE ∨ (rID ≤ r ∧ r < 138) := by decide

/-- `rankIds` does not write output. -/
theorem rankIds_writes : writes rankIds = false := by decide

end rank

/-! ### The identifiers of pairs -/

/-- The end of the memory of `pairIds`. -/
def idsEnd (N L F : ℕ) : ℕ := leadsEnd N L F + L + L

/-- The memory of `pairIds` is linear. -/
theorem idsEnd_le (N L F : ℕ) : idsEnd N L F ≤ F + 6 * (N + L + 1) := by
  have := leads_eqs N L F; unfold idsEnd; omega

/-- The result of `pairIds` (`c₀`: the configuration on entry). -/
structure IOut (ps : List (ℕ × ℕ)) (N : ℕ) (c₀ c : Config) : Prop where
  ld : Arr c.mem (c.reg rLD) (ps.map (ps.idxOf ·))
  id : Arr c.mem (c.reg rID) (eids ps)
  ct : Tab c.mem (c.reg rCT) ps.length fun e => (eids ps).count e
  ne : c.reg rNE = ps.eraseDups.length
  rld : c.reg rLD = bLD N ps.length (c₀.reg rFREE)
  rid : c.reg rID = leadsEnd N ps.length (c₀.reg rFREE)
  rct : c.reg rCT = leadsEnd N ps.length (c₀.reg rFREE) + ps.length
  free : c.reg rFREE = idsEnd N ps.length (c₀.reg rFREE)
  zero : ZeroFrom c.mem (c.reg rFREE)
  same : SameOn (· < c₀.reg rFREE) c₀.mem c.mem

/-- The constant of the running time of `pairIds`. -/
def CI : ℕ := CL + CR

/-- **First-occurrence identifiers of pairs.** Given the `L` pairs `ps` with components
below `N` as two arrays below the free address `F` (`PIn`), `pairIds` stores the leaders
`LEAD = ps.map (ps.idxOf ·)` at `rLD`, the identifiers `EID = eids ps` (`EID[q]` is the index of
`ps[q]` in `ps.eraseDups`) at `rID`, the class sizes `CNT[e] = (eids ps).count e` at `rCT`, and
`NE = |ps.eraseDups|` in `rNE`, within `CI * (N + L + 1)` steps, accessing only the addresses
below any `S ≥ idsEnd N L F` (`idsEnd_le`: `≤ F + 6 (N + L + 1)`), allocating fresh memory only,
writing only the registers of `wregs pairIds` (not the inputs `rPU rPV rPL rPN`), without
output. -/
theorem pairIds_spec (ps : List (ℕ × ℕ)) (N : ℕ) (hN : ∀ p ∈ ps, p.1 < N ∧ p.2 < N)
    (c₀ : Config) (hS : idsEnd N ps.length (c₀.reg rFREE) ≤ S) :
    HTB S pairIds (fun c => PIn ps N c ∧ c = c₀)
      (fun c => IOut ps N c₀ c ∧ Frame pairIds c₀ c) (CI * (N + ps.length + 1)) := by
  intro c ⟨hIn, hc⟩
  subst hc
  have hS₁ : leadsEnd N ps.length (c.reg rFREE) ≤ S := by unfold idsEnd at hS; omega
  obtain ⟨c₁, t₁, he₁, ⟨hL, hfr₁⟩, ht₁⟩ := pairLeads_spec ps N hN c hS₁ c ⟨hIn, rfl⟩
  have hL' := leads_eqs N ps.length (c.reg rFREE)
  have hR : RIn ps c₁ :=
    ⟨(hfr₁.reg rPL (by decide)).trans hIn.pl, hL.ld, by rw [hL.rld, hL.free]; omega, hL.zero⟩
  obtain ⟨c₂, t₂, he₂, ⟨hO, hfr₂⟩, ht₂⟩ :=
    rankIds_spec (S := S) ps c₁ (by rw [hL.free]; unfold idsEnd at hS; omega) c₁ ⟨hR, rfl⟩
  have hld : c₂.reg rLD = c₁.reg rLD := hfr₂.reg rLD (by decide)
  refine ⟨c₂, t₁ + t₂, ExecB.seq he₁ he₂, ⟨⟨?_, hO.id, hO.ct, hO.ne, by rw [hld, hL.rld],
    by rw [hO.rid, hL.free], by rw [hO.rct, hL.free], by rw [hO.free, hL.free]; rfl, hO.zero,
    hL.same.trans (hO.same.mono fun a (ha : a < _) => show a < _ by rw [hL.free]; omega)⟩,
    (ExecB.seq he₁ he₂).frame⟩, ?_⟩
  · rw [hld]
    exact hL.ld.of_below hO.same (by simp only [List.length_map]; rw [hL.rld, hL.free]; omega)
  · simp only [CI, CL, CR] at ht₁ ht₂ ⊢
    nlinarith

/-- The registers written by `pairIds`: `rT`, `rFREE`, the sort's `100–109` and `124–137`
(not the inputs `120–123`). -/
theorem pairIds_wregs : ∀ r ∈ wregs pairIds,
    r = rT ∨ r = rFREE ∨ (100 ≤ r ∧ r < 110) ∨ (rLD ≤ r ∧ r < 138) := by
  intro r hr
  simp only [pairIds, wregs_seq, List.mem_append] at hr
  rcases hr with h | h
  · exact pairLeads_wregs r h
  · rcases rankIds_wregs r h with h | h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr ⟨le_trans (by decide) h1, h2⟩))

/-- `pairIds` does not write output. -/
theorem pairIds_writes : writes pairIds = false := by
  rw [pairIds, writes_seq, pairLeads_writes, rankIds_writes]; rfl

end STACS2027.RAM.PairIds
