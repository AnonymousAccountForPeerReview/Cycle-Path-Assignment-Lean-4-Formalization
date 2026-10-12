module

public import Outerplanar.RAM.PairIdsSpec
public import Outerplanar.RAM.Poly1Sort
import Mathlib.Tactic

/-!
# First-occurrence identifiers of pairs: the leaders

A reusable module. Given `L` pairs `ps` with components below `N`, stored
as two arrays (`PU` at `rPU`, `PV` at `rPV`, below the free address `F`; `rPL = L`, `rPN = N`),
the program `pairLeads` computes the **leaders** `LEAD[q] = ps.idxOf ps[q]` (the first index of
the pair class of `q`; `LEAD[q] = q` iff `q` is a first occurrence) in `O(N + L)` steps and
`2N + 1 + L` (sort) `+ 2N + L` cells above `F`, without an `N × N` table and without unmarking:

1. `sortArgs`, `P1.csort`: the indices sorted stably by first component (`ORD`, at `rKO`);
2. `leadAlloc`: the stamps `STAMP` (`N` cells), the first indices `LEADQ` (`N`), `LEAD` (`L`);
3. `stepGrp`: for `j < L`, `q = ORD[j]`, `(u, v) = (PU[q], PV[q])`: if `STAMP[v] = u + 1` then
   `LEAD[q] := LEADQ[v]`, else `STAMP[v] := u + 1`, `LEADQ[v] := q`, `LEAD[q] := q` (the
   abstract scan `PairIds.grun`; correctness `grun_lead`).

`pairLeads_spec` is the triple within any bound `S ≥ leadsEnd N L F` (`leadsEnd_le`:
`≤ F + 4 (N + L + 1)`). The identifiers in order of first appearance (`EID`, `NE`, `CNT`) are
computed from the leaders by `rankIds` (`PairIdsRank.lean`), and `pairIds = pairLeads; rankIds`.

Registers: the interface `120–127` (`rPU rPV rPL rPN` are inputs and are not written; `rLD rID
rCT rNE` are outputs), scratch `130–137`, and those of `P1.csort` (`100–109`).
-/

@[expose] public section

namespace STACS2027.RAM.PairIds

open STACS2027.Algo

variable {S : ℕ}

/-! ### Registers -/

/-- Input: base of the first components `PU` (`L` cells). -/
abbrev rPU : ℕ := 120
/-- Input: base of the second components `PV` (`L` cells). -/
abbrev rPV : ℕ := 121
/-- Input: the number of pairs `L`. -/
abbrev rPL : ℕ := 122
/-- Input: the bound `N` on the components. -/
abbrev rPN : ℕ := 123
/-- Output: base of the leaders `LEAD` (`L` cells). -/
abbrev rLD : ℕ := 124
/-- Output: base of the identifiers `EID` (`L` cells). -/
abbrev rID : ℕ := 125
/-- Output: base of the class sizes `CNT` (`L` cells). -/
abbrev rCT : ℕ := 126
/-- Output: the number of classes `NE`. -/
abbrev rNE : ℕ := 127
/-- Base of the stamps `STAMP` (`N` cells). -/
abbrev rST : ℕ := 130
/-- Base of the first indices `LEADQ` (`N` cells). -/
abbrev rLQ : ℕ := 131
/-- Loop counter. -/
abbrev rJ : ℕ := 132
/-- The current index `q`. -/
abbrev rQ : ℕ := 133
/-- `u + 1` for the current pair `(u, v)`. -/
abbrev rU : ℕ := 134
/-- `v` for the current pair `(u, v)`. -/
abbrev rV : ℕ := 135
/-- A value read from memory. -/
abbrev rX : ℕ := 136
/-- A second value read from memory. -/
abbrev rY : ℕ := 137

/-! ### The program -/

/-- The arguments of the sort: the keys `PU`, `L` keys below `N`. -/
def sortArgs : Stmt := .seq (mov P1.rKB rPU) (.seq (mov P1.rKL rPL) (mov P1.rKN rPN))
/-- `STAMP`, `LEADQ` (`N` cells each), `LEAD` (`L` cells). -/
def leadAlloc : Stmt := .seq (alloc rST rPN) (.seq (alloc rLQ rPN) (alloc rLD rPL))
/-- `q := ORD[j]`, `rU := PU[q] + 1`, `rV := PV[q]`, `rX := STAMP[v]`. -/
def grpRead : Stmt :=
  .seq (ld rQ P1.rKO rJ) (.seq (ld rU rPU rQ) (.seq (ld rV rPV rQ) (.seq (ld rX rST rV) (inc rU))))
/-- The pair was seen in this group: `LEAD[q] := LEADQ[v]`. -/
def grpHit : Stmt := .seq (ld rY rLQ rV) (st rLD rQ rY)
/-- A new pair: `STAMP[v] := u + 1`, `LEADQ[v] := q`, `LEAD[q] := q`. -/
def grpNew : Stmt := .seq (st rST rV rU) (.seq (st rLQ rV rQ) (st rLD rQ rQ))
/-- One index of the scan. -/
def grpBody : Stmt := .seq grpRead (ifEq rX rU grpHit grpNew)
/-- The scan in the order of the sort. -/
def stepGrp : Stmt := forUp rJ rPL grpBody

/-- **The leaders of the pair classes.** -/
def pairLeads : Stmt := .seq sortArgs (.seq P1.csort (.seq leadAlloc stepGrp))

/-! ### The layout -/

section layout

variable (N L F : ℕ)

/-- The sorted indices `ORD` (`L` cells; the sort's `OFF`, `PTR` are at `F`). -/
def bORD : ℕ := F + (N + 1) + N
/-- The stamps `STAMP` (`N` cells). -/
def bST : ℕ := bORD N F + L
/-- The first indices `LEADQ` (`N` cells). -/
def bLQ : ℕ := bST N L F + N
/-- The leaders `LEAD` (`L` cells). -/
def bLD : ℕ := bLQ N L F + N
/-- The end of the memory of `pairLeads`. -/
def leadsEnd : ℕ := bLD N L F + L

theorem leads_eqs : bORD N F = F + (N + 1) + N ∧ bST N L F = bORD N F + L ∧ bLQ N L F = bST N L F + N ∧
    bLD N L F = bLQ N L F + N ∧ leadsEnd N L F = bLD N L F + L := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The memory of `pairLeads` is linear. -/
theorem leadsEnd_le : leadsEnd N L F ≤ F + 4 * (N + L + 1) := by
  have := leads_eqs N L F; omega

/-- The regions of `pairLeads` fit below `S` (one inequality per region). -/
theorem fits {S : ℕ} (hS : leadsEnd N L F ≤ S) :
    F + (N + 1) + N + L ≤ S ∧ bORD N F + L ≤ S ∧ bST N L F + N ≤ S ∧ bLQ N L F + N ≤ S ∧
      bLD N L F + L ≤ S := by
  have := leads_eqs N L F; omega

end layout

/-! ### The input -/

/-- The input of `pairLeads`: the `L` pairs `ps` as two arrays below the free address. -/
structure PIn (ps : List (ℕ × ℕ)) (N : ℕ) (c : Config) : Prop where
  pl : c.reg rPL = ps.length
  pn : c.reg rPN = N
  pu : Arr c.mem (c.reg rPU) (ps.map Prod.fst)
  pv : Arr c.mem (c.reg rPV) (ps.map Prod.snd)
  below : c.reg rPU + ps.length ≤ c.reg rFREE ∧ c.reg rPV + ps.length ≤ c.reg rFREE
  free : ZeroFrom c.mem (c.reg rFREE)

/-! ### The scan -/

section scan

variable {ps : List (ℕ × ℕ)} {N : ℕ}

/-- The registers fixed during the scan (`c₀`: the configuration on entry). -/
@[mk_iff] structure GGlob (ps : List (ℕ × ℕ)) (N : ℕ) (c₀ c : Config) : Prop where
  pu : c.reg rPU = c₀.reg rPU
  pv : c.reg rPV = c₀.reg rPV
  pl : c.reg rPL = ps.length
  pn : c.reg rPN = N
  ko : c.reg P1.rKO = bORD N (c₀.reg rFREE)
  st : c.reg rST = bST N ps.length (c₀.reg rFREE)
  lq : c.reg rLQ = bLQ N ps.length (c₀.reg rFREE)
  ld : c.reg rLD = bLD N ps.length (c₀.reg rFREE)
  free : c.reg rFREE = leadsEnd N ps.length (c₀.reg rFREE)

/-- The registers written by the scan. -/
def WG : List ℕ := [rT, rJ, rQ, rU, rV, rX, rY]

theorem GGlob.regIndep (ps : List (ℕ × ℕ)) (N : ℕ) (c₀ : Config) : RegIndep WG (GGlob ps N c₀) := by
  indep [gGlob_iff]

/-- The memory during the scan, with the abstract state `s`. -/
structure GMem (ps : List (ℕ × ℕ)) (N : ℕ) (c₀ : Config) (s : GS) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  ord : Arr m (bORD N (c₀.reg rFREE)) (ordOf ps N)
  st : Tab m (bST N ps.length (c₀.reg rFREE)) N s.stamp
  lq : Tab m (bLQ N ps.length (c₀.reg rFREE)) N s.lq
  ld : Tab m (bLD N ps.length (c₀.reg rFREE)) ps.length s.lead
  zero : ZeroFrom m (leadsEnd N ps.length (c₀.reg rFREE))

/-- The invariant of the scan after `p` indices. -/
def GrpInv (ps : List (ℕ × ℕ)) (N : ℕ) (c₀ : Config) (p : ℕ) (c : Config) : Prop :=
  GGlob ps N c₀ c ∧ GMem ps N c₀ (grun ps ((ordOf ps N).take p)) c.mem


/-- The sorted indices have the length of the pairs. -/
theorem length_ord (hN : ∀ p ∈ ps, p.1 < N ∧ p.2 < N) : (ordOf ps N).length = ps.length :=
  length_ordOf fun x hx => (hN x hx).1

/-- A pair already seen: one store. -/
theorem GMem.hit {c₀ : Config} {s : GS} {m : ℕ → ℕ} (h : GMem ps N c₀ s m)
    (hN : ∀ p ∈ ps, p.1 < N ∧ p.2 < N) {q : ℕ} (hq : q < ps.length) (x : ℕ) :
    GMem ps N c₀ { s with lead := Function.update s.lead q x }
      (upd m (bLD N ps.length (c₀.reg rFREE) + q) x) := by
  have := leads_eqs N ps.length (c₀.reg rFREE)
  have hl := length_ord hN
  exact ⟨h.same.upd_of_ge (by omega) _, h.ord.upd_of_disjoint (by omega),
    h.st.upd_of_disjoint (by omega), h.lq.upd_of_disjoint (by omega), h.ld.upd rfl,
    h.zero.upd (by omega)⟩

/-- A new pair: three stores. -/
theorem GMem.new {c₀ : Config} {s : GS} {m : ℕ → ℕ} (h : GMem ps N c₀ s m)
    (hN : ∀ p ∈ ps, p.1 < N ∧ p.2 < N) {q v : ℕ} (hq : q < ps.length) (hv : v < N) (a : ℕ) :
    GMem ps N c₀ ⟨Function.update s.stamp v a, Function.update s.lq v q, Function.update s.lead q q⟩
      (upd (upd (upd m (bST N ps.length (c₀.reg rFREE) + v) a) (bLQ N ps.length (c₀.reg rFREE) + v) q)
        (bLD N ps.length (c₀.reg rFREE) + q) q) := by
  have := leads_eqs N ps.length (c₀.reg rFREE)
  have hl := length_ord hN
  refine ⟨((h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge (by omega) _,
    ((h.ord.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    ((h.st.upd rfl).upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    ((h.lq.upd_of_disjoint (by omega)).upd rfl).upd_of_disjoint (by omega),
    ((h.ld.upd_of_disjoint (by omega)).upd_of_disjoint (by omega)).upd rfl,
    ((h.zero.upd (by omega)).upd (by omega)).upd (by omega)⟩

/-- **One index of the scan.** -/
theorem grpBody_spec (hN : ∀ p ∈ ps, p.1 < N ∧ p.2 < N) (c₀ : Config) (hIn : PIn ps N c₀)
    (hS : leadsEnd N ps.length (c₀.reg rFREE) ≤ S) (p : ℕ) (hp : p < ps.length) :
    HTB S grpBody (fun c => GrpInv ps N c₀ p c ∧ c.reg rJ = p ∧ c.reg rPL = ps.length)
      (fun c => GrpInv ps N c₀ (p + 1) c ∧ c.reg rJ = p ∧ c.reg rPL = ps.length) 30 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hj, hl⟩ => ?_
  have hlen := length_ord hN
  have hpo : p < (ordOf ps N).length := by omega
  have hqL : (ordOf ps N)[p] < ps.length := lt_of_mem_ordOf (List.getElem_mem hpo)
  have hpr := pr_eq ps hqL
  have hvN : (pr ps (ordOf ps N)[p]).2 < N := by
    rw [hpr]; exact (hN _ (List.getElem_mem hqL)).2
  have hq : c.mem (bORD N (c₀.reg rFREE) + p) = (ordOf ps N)[p] := hM.ord.get hpo
  have hu : c.mem (c₀.reg rPU + (ordOf ps N)[p]) = (pr ps (ordOf ps N)[p]).1 := by
    rw [(hIn.pu.of_below hM.same (by simpa using hIn.below.1)).getD (by simpa using hqL), getD_map_fst]
  have hv : c.mem (c₀.reg rPV + (ordOf ps N)[p]) = (pr ps (ordOf ps N)[p]).2 := by
    rw [(hIn.pv.of_below hM.same (by simpa using hIn.below.2)).getD (by simpa using hqL), getD_map_snd]
  have hx : c.mem (bST N ps.length (c₀.reg rFREE) + (pr ps (ordOf ps N)[p]).2) =
      (grun ps ((ordOf ps N).take p)).stamp (pr ps (ordOf ps N)[p]).2 := hM.st.get hvN
  have hy : c.mem (bLQ N ps.length (c₀.reg rFREE) + (pr ps (ordOf ps N)[p]).2) =
      (grun ps ((ordOf ps N).take p)).lq (pr ps (ordOf ps N)[p]).2 := hM.lq.get hvN
  have hb := hIn.below
  have := fits N ps.length (c₀.reg rFREE) hS
  refine ⟨by addr_ok [grpBody, grpRead, grpHit, grpNew, hG.ko, hG.pu, hG.pv, hG.st, hG.lq, hG.ld,
    hj, hq, hu, hv, hx], ?_⟩
  refine ⟨⟨(GGlob.regIndep ps N c₀).run_of_sub (by decide) (by decide) hG, ?_⟩,
    by rw [run_reg_of_not_mem (s := grpBody) (r := rJ) (by decide) (by decide) c, hj],
    by rw [run_reg_of_not_mem (s := grpBody) (r := rPL) (by decide) (by decide) c, hl]⟩
  rw [grun_take_succ hpo]
  unfold gstep
  simp +decide only [grpBody, grpRead, run_seq', run_ld, run_inc (show rU ≠ rT by decide),
    run_ifEq (show rX ≠ rT by decide) (show rU ≠ rT by decide), setReg_reg, setReg_mem,
    ↓reduceIte, hG.ko, hG.pu, hG.pv, hG.st, hj, hq, hu, hv, hx]
  by_cases hs : (grun ps ((ordOf ps N).take p)).stamp (pr ps (ordOf ps N)[p]).2 =
      (pr ps (ordOf ps N)[p]).1 + 1
  · simp +decide only [hs, ↓reduceIte, grpHit, run_seq', run_ld, run_st (show rY ≠ rT by decide),
      setReg_reg, setReg_mem, setMem_mem_upd, hG.lq, hG.ld, hy]
    exact hM.hit hN hqL _
  · simp +decide only [hs, ↓reduceIte, grpNew, run_seq', run_st (show rU ≠ rT by decide),
      run_st (show rQ ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd, setMem_reg,
      hG.st, hG.lq, hG.ld]
    exact hM.new hN hqL hvN _

/-- **The scan**, in `34 L + 3` steps. -/
theorem stepGrp_spec (hN : ∀ p ∈ ps, p.1 < N ∧ p.2 < N) (c₀ : Config) (hIn : PIn ps N c₀)
    (hS : leadsEnd N ps.length (c₀.reg rFREE) ≤ S) :
    HTB S stepGrp (fun c => GrpInv ps N c₀ 0 c ∧ c.reg rPL = ps.length)
      (fun c => GrpInv ps N c₀ ps.length c ∧ c.reg rJ = ps.length ∧ c.reg rPL = ps.length)
      (ps.length * 34 + 3) :=
  HTB.forUpC (i := rJ) (n := rPL) (N := ps.length) (body := grpBody) (GrpInv ps N c₀) 30
    (by decide) (by decide) (by decide) (fun j => by indep [GrpInv, gGlob_iff])
    (fun j hj => grpBody_spec hN c₀ hIn hS j hj)

end scan

/-! ### The leaders -/

/-- The result of `pairLeads` (`c₀`: the configuration on entry). -/
structure LOut (ps : List (ℕ × ℕ)) (N : ℕ) (c₀ c : Config) : Prop where
  ld : Arr c.mem (c.reg rLD) (ps.map (ps.idxOf ·))
  rld : c.reg rLD = bLD N ps.length (c₀.reg rFREE)
  free : c.reg rFREE = leadsEnd N ps.length (c₀.reg rFREE)
  zero : ZeroFrom c.mem (c.reg rFREE)
  same : SameOn (· < c₀.reg rFREE) c₀.mem c.mem

/-- The constant of the running time of `pairLeads`. -/
def CL : ℕ := 62

/-- The input registers kept by the sort. -/
def KeepIn (ps : List (ℕ × ℕ)) (N : ℕ) (c₀ c : Config) : Prop :=
  c.reg rPU = c₀.reg rPU ∧ c.reg rPV = c₀.reg rPV ∧ c.reg rPL = ps.length ∧ c.reg rPN = N

theorem pairLeads_core {ps : List (ℕ × ℕ)} {N : ℕ} (hN : ∀ p ∈ ps, p.1 < N ∧ p.2 < N)
    (c₀ : Config) (hIn : PIn ps N c₀) (hS : leadsEnd N ps.length (c₀.reg rFREE) ≤ S) :
    HTB S pairLeads (fun c => c = c₀)
      (fun c => GrpInv ps N c₀ ps.length c ∧ c.out = c₀.out)
      (6 + ((28 * (ps.map Prod.fst).length + 15 * N + 20) + (9 + (ps.length * 34 + 3)))) := by
  have hK : ∀ x ∈ ps.map Prod.fst, x < N := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (hN p hp).1
  have hfit := fits N ps.length (c₀.reg rFREE) hS
  -- the arguments of the sort
  have h₁ : HTB S sortArgs (fun c => c = c₀)
      (fun c => (P1.CsIn (ps.map Prod.fst) N c ∧ c.reg rFREE = c₀.reg rFREE ∧ c.mem = c₀.mem) ∧
        KeepIn ps N c₀ c ∧ c.out = c₀.out) 6 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      have hb := hIn.below
      have hAg : Agree [rT, P1.rKB, P1.rKL, P1.rKN] c (run sortArgs c) :=
        agree_run (by decide) rfl rfl (by decide) c
      have hkb : (run sortArgs c).reg P1.rKB = c.reg rPU := by
        simp +decide [sortArgs, run_mov]
      have hkl : (run sortArgs c).reg P1.rKL = c.reg rPL := by
        simp +decide [sortArgs, run_mov]
      have hkn : (run sortArgs c).reg P1.rKN = c.reg rPN := by
        simp +decide [sortArgs, run_mov]
      have hF : (run sortArgs c).reg rFREE = c.reg rFREE := hAg.reg _ (by decide)
      refine ⟨⟨⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩, hF, hAg.mem⟩, ⟨hAg.reg _ (by decide), hAg.reg _ (by decide),
        (hAg.reg _ (by decide)).trans hIn.pl, (hAg.reg _ (by decide)).trans hIn.pn⟩, hAg.out⟩
      · rw [hkl, hIn.pl, List.length_map]
      · rw [hkn, hIn.pn]
      · rw [hkb, hAg.mem]; exact hIn.pu
      · rw [hkb, hF, List.length_map]; exact hb.1
      · rw [hF, hAg.mem]; exact hIn.free
  -- the sort, with the frame of the input registers and the output
  have h₂ := ((P1.csort_specB (S := S) (ps.map Prod.fst) N hK (c₀.reg rFREE) c₀.mem
    (by simpa using hfit.1)).frame (F := fun c => KeepIn ps N c₀ c ∧ c.out = c₀.out)
    fun c c' hfr ⟨⟨h1, h2, h3, h4⟩, ho⟩ => ⟨⟨(hfr.reg rPU (by decide)).trans h1,
      (hfr.reg rPV (by decide)).trans h2, (hfr.reg rPL (by decide)).trans h3,
      (hfr.reg rPN (by decide)).trans h4⟩, (hfr.out (by decide)).trans ho⟩)
  -- the allocation
  have h₃ : HTB S leadAlloc (fun c => (((P1.CsOut (ps.map Prod.fst) N c ∧ ZeroFrom c.mem (c.reg rFREE)) ∧
        SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c.reg rFREE = c₀.reg rFREE + (N + 1) + N + (ps.map Prod.fst).length ∧
        c.reg P1.rKF = c₀.reg rFREE ∧ c.reg P1.rKO = c₀.reg rFREE + (N + 1) + N) ∧
        KeepIn ps N c₀ c ∧ c.out = c₀.out))
      (fun c => (GrpInv ps N c₀ 0 c ∧ c.reg rPL = ps.length) ∧ c.out = c₀.out) 9 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨⟨⟨hO, _⟩, hZ⟩, hsame, hF, _, hko⟩, ⟨h1, h2, h3, h4⟩, ho⟩ => by
      have hL := leads_eqs N ps.length (c₀.reg rFREE)
      simp only [List.length_map] at hF
      simp only [leadAlloc, run_seq', run_alloc (show rPN ≠ rT by decide) (show rST ≠ rPN by decide),
        run_alloc (show rPN ≠ rT by decide) (show rLQ ≠ rPN by decide),
        run_alloc (show rPL ≠ rT by decide) (show rLD ≠ rPL by decide)]
      refine ⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      all_goals try (simp +decide [h1, h2, h3, h4, hko, hF, hL] <;> omega)
      · simp only [setReg_mem, grun, List.take_zero, List.foldl_nil, gs0]
        refine ⟨hsame, ?_, hZ.tab (by omega) _, hZ.tab (by omega) _, hZ.tab (by omega) _,
          hZ.mono (by omega)⟩
        rw [hL.1, ← hko]; exact hO.1
  have h₄ := (stepGrp_spec hN c₀ hIn hS).frame (F := fun c => c.out = c₀.out)
    fun c c' hfr ho => (hfr.out (by decide)).trans ho
  exact (h₁.seq (h₂.seq (h₃.seq h₄))).post fun c ⟨⟨h, _⟩, ho⟩ => ⟨h, ho⟩

/-- **The leaders of the pair classes.** Given the `L` pairs `ps` with
components below `N` as two arrays below the free address `F` (`PIn`), `pairLeads` stores
`LEAD = ps.map (ps.idxOf ·)` (the first index of the pair of each `q`) at `rLD`, within
`CL * (N + L + 1)` steps, accessing only the addresses below any `S ≥ leadsEnd N L F`
(`leadsEnd_le`: `≤ F + 4 (N + L + 1)`); it allocates fresh memory only (`LOut.same`) and writes
only the registers of `wregs pairLeads` (`Frame`; not the inputs `rPU rPV rPL rPN`), without
output. -/
theorem pairLeads_spec (ps : List (ℕ × ℕ)) (N : ℕ) (hN : ∀ p ∈ ps, p.1 < N ∧ p.2 < N)
    (c₀ : Config) (hS : leadsEnd N ps.length (c₀.reg rFREE) ≤ S) :
    HTB S pairLeads (fun c => PIn ps N c ∧ c = c₀)
      (fun c => LOut ps N c₀ c ∧ Frame pairLeads c₀ c) (CL * (N + ps.length + 1)) := by
  intro c ⟨hIn, hc⟩
  subst hc
  obtain ⟨c', t, he, ⟨⟨hG, hM⟩, -⟩, ht⟩ := pairLeads_core hN c hIn hS c rfl
  have hl := length_ord hN
  rw [List.take_of_length_le (by omega)] at hM
  refine ⟨c', t, he, ⟨⟨?_, hG.ld, hG.free, by rw [hG.free]; exact hM.zero, hM.same⟩, he.frame⟩, ?_⟩
  · intro i hi
    simp only [List.length_map] at hi
    rw [List.getElem_map, ← grun_lead (fun x hx => (hN x hx).1) hi, hG.ld]
    exact hM.ld.get hi
  · simp only [List.length_map, CL] at ht ⊢
    nlinarith

/-- The registers written by `pairLeads`: `rT`, `rFREE`, the sort's `100–109` and `124–137`
(not the inputs `120–123`). -/
theorem pairLeads_wregs : ∀ r ∈ wregs pairLeads,
    r = rT ∨ r = rFREE ∨ (100 ≤ r ∧ r < 110) ∨ (rLD ≤ r ∧ r < 138) := by
  decide

/-- `pairLeads` does not write output. -/
theorem pairLeads_writes : writes pairLeads = false := by decide

/-- The registers kept by `pairLeads`: all below `100` other than `rT`, `rFREE`, and the inputs. -/
theorem not_mem_wregs_pairLeads {r : ℕ} (h1 : r ≠ rT) (h2 : r ≠ rFREE)
    (h3 : r < 100 ∨ (120 ≤ r ∧ r < 124)) : r ∉ wregs pairLeads := fun h => by
  have e : rLD = 124 := rfl
  rcases pairLeads_wregs r h with h | h | ⟨h4, h5⟩ | ⟨h4, h5⟩
  · exact h1 h
  · exact h2 h
  · omega
  · omega

end STACS2027.RAM.PairIds
