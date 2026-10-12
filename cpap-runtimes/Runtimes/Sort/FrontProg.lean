module

public import Runtimes.Sort.Merge
public import Runtimes.ZeroCostEdges
public import Outerplanar.RAM.PairIdsSorted
import Mathlib.Tactic

/-!
# The sorting front end: layout, program, and the vertex identifiers

A front end for inputs in Corollary 5's format (`zeroCostInput g k`: the graph, `k`, `t` and the
`kt` vertices of the enumerated cycles at `bV g`) that computes **the same data as
Corollary 5's phases 2–4** (`EdgesPost`: the edge identifier `EID[q] = eidOf g k q` of every
occurrence, the class sizes `CNT`, the number `NE` of distinct edges) **without any memory
indexed by a vertex label**:

1. `fSort`: the stable merge sort `msort` (`Merge.lean`) of the occurrences by label
   (`sortKey (verts g k)`, `O(kt log kt)` steps);
2. `fVids`: outerplanar package's `sortedLeads` and `rankIds` (`PairIdsSorted.lean`): the first-appearance
   identifier of the label of every occurrence, `ID[q] = (eids (verts g k))[q] = idv g k verts[q]`
   — the same ids as Corollary 5's dictionary (`eids_verts`) — and their number `gN = nV g k`;
3. `fPairs`: for every occurrence `q = ik + j`, the ids `ID[q]`, `ID[ik + next k j]` of the ends
   of its edge, ordered by **comparing the labels** (`ifLt`), stored as `(PU[q], PV[q]) = idPr`
   (`Front.lean`);
4. `fEids`: outerplanar package's `pairIds` on these pairs (as in Corollary 5's `stepEdges`).

Registers: Corollary 5's globals (`gK gT gV gKT gNV`, kept; `gN gPU gPV gEID gCNT gNE` written)
and scratch, the sort's `800–816`, `PairIds`' `100–109`, `120–137`, and `fID = 830` (the base of
the vertex ids).

**Layout** from the free address `F` (`L = kt`, `N = nV g k ≤ L`): the sort's buffers `[F, F + 2L)`,
the leaders `[F + 2L, F + 3L)`, the ids `ID` at `fIDb = F + 3L`, their class sizes, `PU` at
`F + 5L`, `PV` at `F + 6L`, then `pairIds` from `fPI = F + 7L`: `EID` at `fEID`, `CNT` at `fCNT`,
the end `fEnd ≤ F + 15 L + 1` (`fEnd_le`).

This file: layout, program, the phases `fSort` (`fSort_spec`) and `fVids` (`fVids_spec`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Sort

open STACS2027 STACS2027.RAM STACS2027.RAM.R0 STACS2027.Runtimes.ZeroCost
open scoped List

variable {S : ℕ}

/-! ### Registers and layout -/

/-- The base of the vertex identifiers `ID` (`kt` cells). -/
abbrev fID : ℕ := 830

section layout

variable (g : Graph) (k F : ℕ)

/-- `L = kt`, the number of occurrences. -/
abbrev fL : ℕ := k * (cycles g k).length

/-- The vertex identifiers `ID`. -/
def fIDb : ℕ := F + 3 * fL g k
/-- The first ids `PU` of the pairs. -/
def fPU : ℕ := F + 5 * fL g k
/-- The second ids `PV` of the pairs. -/
def fPV : ℕ := F + 6 * fL g k
/-- The free address at the call of `pairIds`. -/
def fPI : ℕ := F + 7 * fL g k
/-- The edge identifiers `EID` (`kt` cells). -/
def fEID : ℕ := PairIds.leadsEnd (nV g k) (fL g k) (fPI g k F)
/-- The class sizes `CNT` (`kt` cells). -/
def fCNT : ℕ := fEID g k F + fL g k
/-- The end of the memory of the front end. -/
def fEnd : ℕ := fCNT g k F + fL g k

theorem fEnd_eq : fEnd g k F = PairIds.idsEnd (nV g k) (fL g k) (fPI g k F) := rfl

theorem fEID_eq : fEID g k F = F + 4 * nV g k + 9 * fL g k + 1 := by
  unfold fEID fPI
  have := PairIds.leads_eqs (nV g k) (fL g k) (F + 7 * fL g k)
  omega

/-- **The memory of the front end is linear**: `fEnd ≤ F + 15 kt + 1`. -/
theorem fEnd_le : fEnd g k F ≤ F + 15 * fL g k + 1 := by
  have := fEID_eq g k F
  have : nV g k ≤ fL g k := nV_le
  unfold fEnd fCNT; omega

/-- The regions of the front end fit below `S ≥ fEnd` (one inequality per region). -/
theorem ffits {S : ℕ} (hS : fEnd g k F ≤ S) :
    F + 2 * fL g k ≤ S ∧ fIDb g k F + fL g k ≤ S ∧ fPU g k F + fL g k ≤ S ∧
      fPV g k F + fL g k ≤ S ∧ fPI g k F ≤ S ∧ fEID g k F + fL g k ≤ S ∧
      fCNT g k F + fL g k ≤ S := by
  have := fEID_eq g k F
  unfold fEnd fCNT fIDb fPU fPV fPI at *; omega

end layout

/-! ### The program -/

/-- Phase 1: sort the occurrences by label (`msort` with the keys `verts` at `gV`). -/
def fSort : Stmt := .seq (mov oKB gV) (.seq (mov oL gKT) msort)

/-- The arguments of `sortedIds`: the sorted indices, the keys `verts`, `kt`. -/
def vArgs : Stmt := .seq (mov PairIds.rSQ oSQ) (.seq (mov PairIds.rKY gV) (mov PairIds.rPL gKT))
/-- The results of `sortedIds`: `fID := ID`, `gN := nV`. -/
def vBack : Stmt := .seq (mov fID PairIds.rID) (mov ZeroCost.gN PairIds.rNE)
/-- Phase 2: the vertex identifiers (leaders from the sorted order, then ranks). -/
def fVids : Stmt := .seq vArgs (.seq PairIds.sortedLeads (.seq PairIds.rankIds vBack))

/-- The ids of the ends of the edge of occurrence `sQ` (second end at `sP`). -/
def pIds : Stmt := .seq (ld sU fID sQ) (ld sV fID sP)
/-- Ordered by the labels `sX`, `sY` of the ends. -/
def pOrd : Stmt := ifLt sY sX (swap sU sV) .skip
/-- Reading occurrence `q = sBase + sJ`: its ends and their ids, ordered by label. -/
def pRead : Stmt := .seq edgeA (.seq nextPos (.seq (ld sY gV sP) (.seq pIds pOrd)))
/-- One occurrence of the pair pass: `PU[q], PV[q]`. -/
def pBody : Stmt := .seq pRead edgePut
/-- One cycle of the pair pass. -/
def pRow : Stmt := .seq (forUp sJ gK pBody) (.add sBase sBase gK)
/-- Phase 3: the ordered id pairs of the occurrences. -/
def fPairs : Stmt :=
  .seq (alloc gPU gKT) (.seq (alloc gPV gKT) (.seq (.const sBase 0) (forUp sI gT pRow)))

/-- Phase 4: the edge identifiers and their counts (`PairIds.pairIds`, B2). -/
def fEids : Stmt := .seq idsArgs (.seq PairIds.pairIds idsBack)

/-- **The sorting front end.** -/
def front : Stmt := .seq fSort (.seq fVids (.seq fPairs fEids))

/-! ### The input -/

/-- The input of the front end: Corollary 5's registers of phase 1 (`GA`), the vertices of
the cycles at `bV g` below the free address, zero memory from the free address on. -/
structure FrontIn (g : Graph) (k : ℕ) (c : Config) : Prop where
  ga : GA g k c
  mverts : Arr c.mem (bV g) (verts g k)
  below : bV g + fL g k ≤ c.reg rFREE
  zero : ZeroFrom c.mem (c.reg rFREE)

theorem frontIn_of_initPost {g : Graph} {k : ℕ} {c : Config} (h : InitPost g k c) : FrontIn g k c :=
  ⟨h.ga, h.mverts, by rw [h.rfree]; rfl, by rw [h.rfree]; exact h.mzero⟩

/-! ### The abstract side: the vertex identifiers -/

/-- **The first-appearance ids of the labels are Corollary 5's dictionary ids.** -/
theorem eids_verts (g : Graph) (k : ℕ) :
    PairIds.eids (verts g k) = (verts g k).map (idv g k) := rfl

theorem length_verts' (g : Graph) (k : ℕ) : (verts g k).length = fL g k := length_verts g k

/-! ### Phase 1: sorting -/

/-- The registers of `GA` are not written by the sort. -/
theorem ga_of_frame_msort {g : Graph} {k : ℕ} {c c' : Config} (h : Frame msort c c')
    (hga : GA g k c) : GA g k c' := by
  have hk : ∀ r, 250 ≤ r → r < 300 → c'.reg r = c.reg r := fun r h1 h2 =>
    h.reg r fun hr => by
      rcases msort_wregs r hr with rfl | rfl | ⟨h3, h4⟩
      · exact absurd h1 (by decide)
      · exact absurd h1 (by decide)
      · have e1 : oSQ = 802 := rfl
        have e2 : oKY = 816 := rfl
        omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := hga
  exact ⟨(hk _ (by decide) (by decide)).trans h1, (hk _ (by decide) (by decide)).trans h2,
    (hk _ (by decide) (by decide)).trans h3, (hk _ (by decide) (by decide)).trans h4,
    (hk _ (by decide) (by decide)).trans h5⟩

/-- The state after the sort (`F`: the free address at the start). -/
structure SortedPost (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  vb : bV g + fL g k ≤ F
  ga : GA g k c
  rfree : c.reg rFREE = F + 2 * fL g k
  rsq : F ≤ c.reg oSQ ∧ c.reg oSQ + fL g k ≤ c.reg rFREE
  sq : Arr c.mem (c.reg oSQ) (sortKey (verts g k))
  mverts : Arr c.mem (bV g) (verts g k)
  zero : ZeroFrom c.mem (c.reg rFREE)
  same : SameOn (· < F) m₀ c.mem

/-- **Phase 1**: the occurrences sorted by label. -/
theorem fSort_spec (g : Graph) (k : ℕ) (c₀ : Config) (hIn : FrontIn g k c₀)
    (hS : c₀.reg rFREE + 2 * fL g k ≤ S) :
    HTB S fSort (· = c₀) (fun c => SortedPost g k (c₀.reg rFREE) c₀.mem c ∧ c.out = c₀.out)
      (4 + CM * (fL g k * (Nat.clog 2 (fL g k) + 1) + 1)) := by
  have hl := length_verts' g k
  have h0 : HTB S (.seq (mov oKB gV) (mov oL gKT)) (· = c₀)
      (fun c => (SortIn (verts g k) c ∧ GA g k c ∧ c.reg rFREE = c₀.reg rFREE ∧ c.mem = c₀.mem ∧
        c.out = c₀.out)) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      have hAg : Agree [rT, oKB, oL] c (run (.seq (mov oKB gV) (mov oL gKT)) c) :=
        agree_run (by decide) rfl rfl (by decide) c
      have hkb : (run (.seq (mov oKB gV) (mov oL gKT)) c).reg oKB = bV g := by
        simp +decide [run_mov, hIn.ga.rv]
      refine ⟨⟨?_, ?_, ?_⟩, (show RegIndep [rT, oKB, oL] (GA g k) by indep [gA_iff]).indep _ _ hAg
        hIn.ga, hAg.reg _ (by decide), hAg.mem, hAg.out⟩
      · simp +decide [run_mov, hIn.ga.rkt, hl]
      · rw [hkb, hAg.mem]; exact hIn.mverts
      · rw [hkb, hAg.reg _ (by decide), hl]; exact hIn.below
  have h1 : HTB S msort (fun c => SortIn (verts g k) c ∧ GA g k c ∧ c.reg rFREE = c₀.reg rFREE ∧
        c.mem = c₀.mem ∧ c.out = c₀.out)
      (fun c => SortedPost g k (c₀.reg rFREE) c₀.mem c ∧ c.out = c₀.out)
      (CM * (fL g k * (Nat.clog 2 (fL g k) + 1) + 1)) :=
    HTB.of_forall fun c₁ ⟨hIn₁, hga₁, hF₁, hm₁, ho₁⟩ => by
      refine (msort_spec (S := S) (verts g k) c₁ hIn₁ (by rw [hF₁, hl]; exact hS)).mono
        (fun _ h => h) (fun c ⟨hO, hfr⟩ => ?_) (by rw [hl])
      have hF : c.reg rFREE = c₀.reg rFREE + 2 * fL g k := by rw [hO.free, hF₁, hl]
      refine ⟨⟨hIn.below, ga_of_frame_msort hfr hga₁, hF, ⟨by have := hO.rsq.1; omega,
        by have := hO.rsq.2; rw [hl] at this; exact this⟩, hO.sq, ?_, ?_, ?_⟩,
        by rw [hfr.out msort_writes, ho₁]⟩
      · refine hIn.mverts.congr fun i hi => ?_
        rw [hO.same _ (Or.inl (by have := hIn.below; rw [hF₁]; rw [length_verts'] at hi; omega)),
          hm₁]
      · intro x hx
        rw [hO.same x (Or.inr (by rw [hF₁, hl]; omega)), hm₁]
        exact hIn.zero x (by omega)
      · intro x hx
        rw [hO.same x (Or.inl (by rw [hF₁]; exact hx)), hm₁]
  exact (h0.seq h1).assoc

/-! ### Phase 2: the vertex identifiers -/

/-- The state after the vertex identifiers. -/
structure VidsPost (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  vb : bV g + fL g k ≤ F
  ga : GA g k c
  rid : c.reg fID = fIDb g k F
  rn : c.reg ZeroCost.gN = nV g k
  rfree : c.reg rFREE = F + 5 * fL g k
  mid : Arr c.mem (fIDb g k F) ((verts g k).map (idv g k))
  mverts : Arr c.mem (bV g) (verts g k)
  zero : ZeroFrom c.mem (c.reg rFREE)
  same : SameOn (· < F) m₀ c.mem

theorem ga_of_frame {g : Graph} {k : ℕ} {s : Stmt} {c c' : Config} (h : Frame s c c')
    (hw : ∀ r ∈ wregs s, r < 250 ∨ 300 ≤ r) (hga : GA g k c) : GA g k c' := by
  have hk : ∀ r, 250 ≤ r → r < 300 → c'.reg r = c.reg r := fun r h1 h2 =>
    h.reg r fun hr => by have := hw r hr; omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := hga
  exact ⟨(hk _ (by decide) (by decide)).trans h1, (hk _ (by decide) (by decide)).trans h2,
    (hk _ (by decide) (by decide)).trans h3, (hk _ (by decide) (by decide)).trans h4,
    (hk _ (by decide) (by decide)).trans h5⟩

theorem sortedLeads_wregs' : ∀ r ∈ wregs PairIds.sortedLeads, r < 250 ∨ 300 ≤ r := by decide
theorem rankIds_wregs' : ∀ r ∈ wregs PairIds.rankIds, r < 250 ∨ 300 ≤ r := by decide

/-- **Phase 2**: the first-appearance identifiers of the labels (`sortedLeads`, `rankIds` on the
sorted order), which are Corollary 5's dictionary ids `idv g k`. -/
theorem fVids_spec (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (hS : F + 5 * fL g k ≤ S) :
    HTB S fVids (SortedPost g k F m₀) (VidsPost g k F m₀)
      (6 + (24 * (fL g k + 1) + (PairIds.CR * (fL g k + 1) + 4))) := by
  refine HTB.pre_fact (p := bV g + fL g k ≤ F) (fun c h => h.vb) fun hvb => ?_
  have hl := length_verts' g k
  -- the arguments
  have h0 : HTB S vArgs (SortedPost g k F m₀)
      (fun c => PairIds.SIn (verts g k) (sortKey (verts g k)) c ∧ GA g k c ∧
        c.reg rFREE = F + 2 * fL g k ∧ Arr c.mem (bV g) (verts g k) ∧ SameOn (· < F) m₀ c.mem)
      6 := HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hP => by
    have hAg : Agree [rT, PairIds.rSQ, PairIds.rKY, PairIds.rPL] c (run vArgs c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hsq : (run vArgs c).reg PairIds.rSQ = c.reg oSQ := by simp +decide [vArgs, run_mov]
    have hky : (run vArgs c).reg PairIds.rKY = bV g := by
      simp +decide [vArgs, run_mov, hP.ga.rv]
    have hpl : (run vArgs c).reg PairIds.rPL = (verts g k).length := by
      simp +decide [vArgs, run_mov, hP.ga.rkt, hl]
    have hF : (run vArgs c).reg rFREE = F + 2 * fL g k := (hAg.reg _ (by decide)).trans hP.rfree
    refine ⟨⟨hpl, by rw [hsq, hAg.mem]; exact hP.sq, by rw [hky, hAg.mem]; exact hP.mverts,
      ⟨by rw [hsq, hF, hl]; have := hP.rsq; rw [hP.rfree] at this; omega,
        by rw [hky, hF, hl]; omega⟩, by rw [hF, hAg.mem, ← hP.rfree]; exact hP.zero⟩,
      (show RegIndep [rT, PairIds.rSQ, PairIds.rKY, PairIds.rPL] (GA g k) by
        indep [gA_iff]).indep _ _ hAg hP.ga, hF, by rw [hAg.mem]; exact hP.mverts,
      by rw [hAg.mem]; exact hP.same⟩
  -- the leaders
  have h1 : HTB S PairIds.sortedLeads
      (fun c => PairIds.SIn (verts g k) (sortKey (verts g k)) c ∧ GA g k c ∧
        c.reg rFREE = F + 2 * fL g k ∧ Arr c.mem (bV g) (verts g k) ∧ SameOn (· < F) m₀ c.mem)
      (fun c => PairIds.RIn (verts g k) c ∧ GA g k c ∧ c.reg rFREE = F + 3 * fL g k ∧
        Arr c.mem (bV g) (verts g k) ∧ SameOn (· < F) m₀ c.mem)
      (24 * (fL g k + 1)) :=
    HTB.of_forall fun c₁ ⟨hIn, hga, hF, hV, hsame⟩ => by
      refine (PairIds.sortedLeads_spec (S := S) (verts g k) (sortKey (verts g k))
        pairwise_sortKey length_sortKey (fun q hq => mem_sortKey hq)
        (fun q hq => lt_of_mem_sortKey hq) c₁ (by rw [hF, hl]; omega)).mono
        (fun c hc => ⟨hc ▸ hIn, hc⟩) (fun c ⟨⟨hld, hrld, hfree, hzero, hsame'⟩, hfr⟩ => ?_)
        (by rw [hl])
      have hF' : c.reg rFREE = F + 3 * fL g k := by rw [hfree, hF, hl]; ring
      refine ⟨⟨(hfr.reg PairIds.rPL (by decide)).trans hIn.pl, hld, by rw [hrld, hfree], hzero⟩,
        ga_of_frame hfr sortedLeads_wregs' hga, hF',
        hV.of_below hsame' (by rw [hF, length_verts']; omega), ?_⟩
      exact hsame.trans (hsame'.mono fun a (ha : a < F) => show a < _ by rw [hF]; omega)
  -- the ranks
  have h2 : HTB S PairIds.rankIds
      (fun c => PairIds.RIn (verts g k) c ∧ GA g k c ∧ c.reg rFREE = F + 3 * fL g k ∧
        Arr c.mem (bV g) (verts g k) ∧ SameOn (· < F) m₀ c.mem)
      (fun c => Arr c.mem (c.reg PairIds.rID) (PairIds.eids (verts g k)) ∧
        c.reg PairIds.rID = F + 3 * fL g k ∧ c.reg PairIds.rNE = nV g k ∧
        c.reg rFREE = F + 5 * fL g k ∧ ZeroFrom c.mem (c.reg rFREE) ∧ GA g k c ∧
        Arr c.mem (bV g) (verts g k) ∧ SameOn (· < F) m₀ c.mem)
      (PairIds.CR * (fL g k + 1)) :=
    HTB.of_forall fun c₁ ⟨hIn, hga, hF, hV, hsame⟩ => by
      refine (PairIds.rankIds_spec (S := S) (verts g k) c₁ (by rw [hF, hl]; omega)).mono
        (fun c hc => ⟨hc ▸ hIn, hc⟩) (fun c ⟨hO, hfr⟩ => ?_) (by rw [hl])
      refine ⟨hO.id, by rw [hO.rid, hF], hO.ne, by rw [hO.free, hF, hl]; ring, hO.zero,
        ga_of_frame hfr rankIds_wregs' hga,
        hV.of_below hO.same (by rw [hF, length_verts']; omega), ?_⟩
      exact hsame.trans (hO.same.mono fun a (ha : a < F) => show a < _ by rw [hF]; omega)
  -- the results
  have h3 : HTB S vBack
      (fun c => Arr c.mem (c.reg PairIds.rID) (PairIds.eids (verts g k)) ∧
        c.reg PairIds.rID = F + 3 * fL g k ∧ c.reg PairIds.rNE = nV g k ∧
        c.reg rFREE = F + 5 * fL g k ∧ ZeroFrom c.mem (c.reg rFREE) ∧ GA g k c ∧
        Arr c.mem (bV g) (verts g k) ∧ SameOn (· < F) m₀ c.mem)
      (VidsPost g k F m₀) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨hid, hrid, hne, hF, hZ, hga, hV, hsame⟩ => by
        have hAg : Agree [rT, fID, ZeroCost.gN] c (run vBack c) :=
          agree_run (by decide) rfl rfl (by decide) c
        refine ⟨hvb, (show RegIndep [rT, fID, ZeroCost.gN] (GA g k) by
            indep [gA_iff]).indep _ _ hAg hga,
          by simp +decide [vBack, run_mov, hrid, fIDb], by simp +decide [vBack, run_mov, hne],
          (hAg.reg _ (by decide)).trans hF, ?_, by rw [hAg.mem]; exact hV,
          by rw [hAg.mem, hAg.reg _ (by decide)]; exact hZ, by rw [hAg.mem]; exact hsame⟩
        rw [hAg.mem, fIDb, ← hrid]; exact hid
  exact h0.seq (h1.seq (h2.seq h3))

end STACS2027.Runtimes.Sort
