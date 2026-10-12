module

public import Runtimes.Sort.Merge
public import Runtimes.ZeroCostEdges
public import Runtimes.Flow.Front
public import Outerplanar.RAM.PairIdsSorted
import Mathlib.Tactic

/-!
# Sorting enumerated cycle lists

Layout and the sorting and vertex-identification phases for an arbitrary list of simple cycles.
These are the existing sorting-front-end proofs with the canonical cycle enumeration
replaced by a supplied list and an explicit proof that every entry is a simple cycle.
No step of the program depends on the order of that list or on a vertex-label dictionary.
-/

@[expose] public section

namespace STACS2027.Runtimes.EnumeratedSort

open STACS2027 STACS2027.RAM STACS2027.RAM.R0 STACS2027.Runtimes.ZeroCost
open STACS2027.Runtimes.Sort
open scoped List

variable {S : ℕ}

abbrev fID : ℕ := 830

section layout

variable (g : Graph) (cs : List Cycle) (k F : ℕ)

abbrev fL (_g : Graph) (cs : List Cycle) (k : ℕ) : ℕ := k * cs.length

def fIDb : ℕ := F + 3 * fL g cs k

def fPU : ℕ := F + 5 * fL g cs k

def fPV : ℕ := F + 6 * fL g cs k

def fPI : ℕ := F + 7 * fL g cs k

def fEID : ℕ := PairIds.leadsEnd (Flow.nV cs) (fL g cs k) (fPI g cs k F)

def fCNT : ℕ := fEID g cs k F + fL g cs k

def fEnd : ℕ := fCNT g cs k F + fL g cs k

theorem fEnd_eq (g : Graph) (cs : List Cycle) (k : ℕ) (_hcs : ∀ c ∈ cs, IsCycle g k c) (F : ℕ) : fEnd g cs k F = PairIds.idsEnd (Flow.nV cs) (fL g cs k) (fPI g cs k F) := rfl

theorem fEID_eq (g : Graph) (cs : List Cycle) (k : ℕ) (_hcs : ∀ c ∈ cs, IsCycle g k c) (F : ℕ) : fEID g cs k F = F + 4 * Flow.nV cs + 9 * fL g cs k + 1 := by
  unfold fEID fPI
  have := PairIds.leads_eqs (Flow.nV cs) (fL g cs k) (F + 7 * fL g cs k)
  omega

theorem fEnd_le (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) (F : ℕ) : fEnd g cs k F ≤ F + 15 * fL g cs k + 1 := by
  have := fEID_eq g cs k hcs F
  have : Flow.nV cs ≤ fL g cs k := (Flow.nV_le hcs)
  unfold fEnd fCNT; omega

theorem ffits (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) (F : ℕ) {S : ℕ} (hS : fEnd g cs k F ≤ S) :
    F + 2 * fL g cs k ≤ S ∧ fIDb g cs k F + fL g cs k ≤ S ∧ fPU g cs k F + fL g cs k ≤ S ∧
      fPV g cs k F + fL g cs k ≤ S ∧ fPI g cs k F ≤ S ∧ fEID g cs k F + fL g cs k ≤ S ∧
      fCNT g cs k F + fL g cs k ≤ S := by
  have := fEID_eq g cs k hcs F
  unfold fEnd fCNT fIDb fPU fPV fPI at *; omega

end layout

def fSort : Stmt := .seq (mov oKB gV) (.seq (mov oL gKT) msort)

def vArgs : Stmt := .seq (mov PairIds.rSQ oSQ) (.seq (mov PairIds.rKY gV) (mov PairIds.rPL gKT))

def vBack : Stmt := .seq (mov fID PairIds.rID) (mov ZeroCost.gN PairIds.rNE)

def fVids : Stmt := .seq vArgs (.seq PairIds.sortedLeads (.seq PairIds.rankIds vBack))

def pIds : Stmt := .seq (ld sU fID sQ) (ld sV fID sP)

def pOrd : Stmt := ifLt sY sX (swap sU sV) .skip

def pRead : Stmt := .seq edgeA (.seq nextPos (.seq (ld sY gV sP) (.seq pIds pOrd)))

def pBody : Stmt := .seq pRead edgePut

def pRow : Stmt := .seq (forUp sJ gK pBody) (.add sBase sBase gK)

def fPairs : Stmt :=
  .seq (alloc gPU gKT) (.seq (alloc gPV gKT) (.seq (.const sBase 0) (forUp sI gT pRow)))

def fEids : Stmt := .seq idsArgs (.seq PairIds.pairIds idsBack)

def front : Stmt := .seq fSort (.seq fVids (.seq fPairs fEids))

structure FrontIn (g : Graph) (cs : List Cycle) (k : ℕ) (c : Config) : Prop where
  ga : Flow.GA g cs k c
  mverts : Arr c.mem (bV g) (Flow.verts cs)
  below : bV g + fL g cs k ≤ c.reg rFREE
  zero : ZeroFrom c.mem (c.reg rFREE)

theorem frontIn_of_initPost {g : Graph} {cs : List Cycle} {k : ℕ} (_hcs : ∀ c ∈ cs, IsCycle g k c) {c : Config} (h : Flow.InitPost g cs k c) : FrontIn g cs k c :=
  ⟨h.ga, h.mverts, by rw [h.rfree]; rfl, by rw [h.rfree]; exact h.mzero⟩

theorem eids_verts (g : Graph) (cs : List Cycle) (k : ℕ) (_hcs : ∀ c ∈ cs, IsCycle g k c) :
    PairIds.eids (Flow.verts cs) = (Flow.verts cs).map (Flow.idv cs) := rfl

theorem length_verts' (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) : (Flow.verts cs).length = fL g cs k := Flow.length_verts hcs

theorem ga_of_frame_msort {g : Graph} {cs : List Cycle} {k : ℕ} (_hcs : ∀ c ∈ cs, IsCycle g k c) {c c' : Config} (h : Frame msort c c')
    (hga : Flow.GA g cs k c) : Flow.GA g cs k c' := by
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

structure SortedPost (g : Graph) (cs : List Cycle) (k F : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  vb : bV g + fL g cs k ≤ F
  ga : Flow.GA g cs k c
  rfree : c.reg rFREE = F + 2 * fL g cs k
  rsq : F ≤ c.reg oSQ ∧ c.reg oSQ + fL g cs k ≤ c.reg rFREE
  sq : Arr c.mem (c.reg oSQ) (sortKey (Flow.verts cs))
  mverts : Arr c.mem (bV g) (Flow.verts cs)
  zero : ZeroFrom c.mem (c.reg rFREE)
  same : SameOn (· < F) m₀ c.mem

theorem fSort_spec (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) (c₀ : Config) (hIn : FrontIn g cs k c₀)
    (hS : c₀.reg rFREE + 2 * fL g cs k ≤ S) :
    HTB S fSort (· = c₀) (fun c => SortedPost g cs k (c₀.reg rFREE) c₀.mem c ∧ c.out = c₀.out)
      (4 + CM * (fL g cs k * (Nat.clog 2 (fL g cs k) + 1) + 1)) := by
  have hl := length_verts' g cs k hcs
  have h0 : HTB S (.seq (mov oKB gV) (mov oL gKT)) (· = c₀)
      (fun c => (SortIn (Flow.verts cs) c ∧ Flow.GA g cs k c ∧ c.reg rFREE = c₀.reg rFREE ∧ c.mem = c₀.mem ∧
        c.out = c₀.out)) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      subst hc
      have hAg : Agree [rT, oKB, oL] c (run (.seq (mov oKB gV) (mov oL gKT)) c) :=
        agree_run (by decide) rfl rfl (by decide) c
      have hkb : (run (.seq (mov oKB gV) (mov oL gKT)) c).reg oKB = bV g := by
        simp +decide [run_mov, hIn.ga.rv, Flow.bV, bV]
      refine ⟨⟨?_, ?_, ?_⟩, (show RegIndep [rT, oKB, oL] (Flow.GA g cs k) by indep [Flow.gA_iff]).indep _ _ hAg
        hIn.ga, hAg.reg _ (by decide), hAg.mem, hAg.out⟩
      · simp +decide [run_mov, hIn.ga.rkt, hl]
      · rw [hkb, hAg.mem]; exact hIn.mverts
      · rw [hkb, hAg.reg _ (by decide), hl]; exact hIn.below
  have h1 : HTB S msort (fun c => SortIn (Flow.verts cs) c ∧ Flow.GA g cs k c ∧ c.reg rFREE = c₀.reg rFREE ∧
        c.mem = c₀.mem ∧ c.out = c₀.out)
      (fun c => SortedPost g cs k (c₀.reg rFREE) c₀.mem c ∧ c.out = c₀.out)
      (CM * (fL g cs k * (Nat.clog 2 (fL g cs k) + 1) + 1)) :=
    HTB.of_forall fun c₁ ⟨hIn₁, hga₁, hF₁, hm₁, ho₁⟩ => by
      refine (msort_spec (S := S) (Flow.verts cs) c₁ hIn₁ (by rw [hF₁, hl]; exact hS)).mono
        (fun _ h => h) (fun c ⟨hO, hfr⟩ => ?_) (by rw [hl])
      have hF : c.reg rFREE = c₀.reg rFREE + 2 * fL g cs k := by rw [hO.free, hF₁, hl]
      refine ⟨⟨hIn.below, ga_of_frame_msort hcs hfr hga₁, hF, ⟨by have := hO.rsq.1; omega,
        by have := hO.rsq.2; rw [hl] at this; exact this⟩, hO.sq, ?_, ?_, ?_⟩,
        by rw [hfr.out msort_writes, ho₁]⟩
      · refine hIn.mverts.congr fun i hi => ?_
        rw [hO.same _ (Or.inl (by have := hIn.below; rw [hF₁]; rw [length_verts' g cs k hcs] at hi; omega)),
          hm₁]
      · intro x hx
        rw [hO.same x (Or.inr (by rw [hF₁, hl]; omega)), hm₁]
        exact hIn.zero x (by omega)
      · intro x hx
        rw [hO.same x (Or.inl (by rw [hF₁]; exact hx)), hm₁]
  exact (h0.seq h1).assoc

structure VidsPost (g : Graph) (cs : List Cycle) (k F : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  vb : bV g + fL g cs k ≤ F
  ga : Flow.GA g cs k c
  rid : c.reg fID = fIDb g cs k F
  rn : c.reg ZeroCost.gN = Flow.nV cs
  rfree : c.reg rFREE = F + 5 * fL g cs k
  mid : Arr c.mem (fIDb g cs k F) ((Flow.verts cs).map (Flow.idv cs))
  mverts : Arr c.mem (bV g) (Flow.verts cs)
  zero : ZeroFrom c.mem (c.reg rFREE)
  same : SameOn (· < F) m₀ c.mem

theorem ga_of_frame {g : Graph} {cs : List Cycle} {k : ℕ} (_hcs : ∀ c ∈ cs, IsCycle g k c) {s : Stmt} {c c' : Config} (h : Frame s c c')
    (hw : ∀ r ∈ wregs s, r < 250 ∨ 300 ≤ r) (hga : Flow.GA g cs k c) : Flow.GA g cs k c' := by
  have hk : ∀ r, 250 ≤ r → r < 300 → c'.reg r = c.reg r := fun r h1 h2 =>
    h.reg r fun hr => by have := hw r hr; omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := hga
  exact ⟨(hk _ (by decide) (by decide)).trans h1, (hk _ (by decide) (by decide)).trans h2,
    (hk _ (by decide) (by decide)).trans h3, (hk _ (by decide) (by decide)).trans h4,
    (hk _ (by decide) (by decide)).trans h5⟩

theorem sortedLeads_wregs' : ∀ r ∈ wregs PairIds.sortedLeads, r < 250 ∨ 300 ≤ r := by decide
theorem rankIds_wregs' : ∀ r ∈ wregs PairIds.rankIds, r < 250 ∨ 300 ≤ r := by decide

theorem fVids_spec (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) (F : ℕ) (m₀ : ℕ → ℕ) (hS : F + 5 * fL g cs k ≤ S) :
    HTB S fVids (SortedPost g cs k F m₀) (VidsPost g cs k F m₀)
      (6 + (24 * (fL g cs k + 1) + (PairIds.CR * (fL g cs k + 1) + 4))) := by
  refine HTB.pre_fact (p := bV g + fL g cs k ≤ F) (fun c h => h.vb) fun hvb => ?_
  have hl := length_verts' g cs k hcs
  -- the arguments
  have h0 : HTB S vArgs (SortedPost g cs k F m₀)
      (fun c => PairIds.SIn (Flow.verts cs) (sortKey (Flow.verts cs)) c ∧ Flow.GA g cs k c ∧
        c.reg rFREE = F + 2 * fL g cs k ∧ Arr c.mem (bV g) (Flow.verts cs) ∧ SameOn (· < F) m₀ c.mem)
      6 := HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hP => by
    have hAg : Agree [rT, PairIds.rSQ, PairIds.rKY, PairIds.rPL] c (run vArgs c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hsq : (run vArgs c).reg PairIds.rSQ = c.reg oSQ := by simp +decide [vArgs, run_mov]
    have hky : (run vArgs c).reg PairIds.rKY = bV g := by
      simp +decide [vArgs, run_mov, hP.ga.rv, Flow.bV, bV]
    have hpl : (run vArgs c).reg PairIds.rPL = (Flow.verts cs).length := by
      simp +decide [vArgs, run_mov, hP.ga.rkt, hl]
    have hF : (run vArgs c).reg rFREE = F + 2 * fL g cs k := (hAg.reg _ (by decide)).trans hP.rfree
    refine ⟨⟨hpl, by rw [hsq, hAg.mem]; exact hP.sq, by rw [hky, hAg.mem]; exact hP.mverts,
      ⟨by rw [hsq, hF, hl]; have := hP.rsq; rw [hP.rfree] at this; omega,
        by rw [hky, hF, hl]; omega⟩, by rw [hF, hAg.mem, ← hP.rfree]; exact hP.zero⟩,
      (show RegIndep [rT, PairIds.rSQ, PairIds.rKY, PairIds.rPL] (Flow.GA g cs k) by
        indep [Flow.gA_iff]).indep _ _ hAg hP.ga, hF, by rw [hAg.mem]; exact hP.mverts,
      by rw [hAg.mem]; exact hP.same⟩
  -- the leaders
  have h1 : HTB S PairIds.sortedLeads
      (fun c => PairIds.SIn (Flow.verts cs) (sortKey (Flow.verts cs)) c ∧ Flow.GA g cs k c ∧
        c.reg rFREE = F + 2 * fL g cs k ∧ Arr c.mem (bV g) (Flow.verts cs) ∧ SameOn (· < F) m₀ c.mem)
      (fun c => PairIds.RIn (Flow.verts cs) c ∧ Flow.GA g cs k c ∧ c.reg rFREE = F + 3 * fL g cs k ∧
        Arr c.mem (bV g) (Flow.verts cs) ∧ SameOn (· < F) m₀ c.mem)
      (24 * (fL g cs k + 1)) :=
    HTB.of_forall fun c₁ ⟨hIn, hga, hF, hV, hsame⟩ => by
      refine (PairIds.sortedLeads_spec (S := S) (Flow.verts cs) (sortKey (Flow.verts cs))
        pairwise_sortKey length_sortKey (fun q hq => mem_sortKey hq)
        (fun q hq => lt_of_mem_sortKey hq) c₁ (by rw [hF, hl]; omega)).mono
        (fun c hc => ⟨hc ▸ hIn, hc⟩) (fun c ⟨⟨hld, hrld, hfree, hzero, hsame'⟩, hfr⟩ => ?_)
        (by rw [hl])
      have hF' : c.reg rFREE = F + 3 * fL g cs k := by rw [hfree, hF, hl]; ring
      refine ⟨⟨(hfr.reg PairIds.rPL (by decide)).trans hIn.pl, hld, by rw [hrld, hfree], hzero⟩,
        ga_of_frame hcs hfr sortedLeads_wregs' hga, hF',
        hV.of_below hsame' (by rw [hF, length_verts' g cs k hcs]; omega), ?_⟩
      exact hsame.trans (hsame'.mono fun a (ha : a < F) => show a < _ by rw [hF]; omega)
  -- the ranks
  have h2 : HTB S PairIds.rankIds
      (fun c => PairIds.RIn (Flow.verts cs) c ∧ Flow.GA g cs k c ∧ c.reg rFREE = F + 3 * fL g cs k ∧
        Arr c.mem (bV g) (Flow.verts cs) ∧ SameOn (· < F) m₀ c.mem)
      (fun c => Arr c.mem (c.reg PairIds.rID) (PairIds.eids (Flow.verts cs)) ∧
        c.reg PairIds.rID = F + 3 * fL g cs k ∧ c.reg PairIds.rNE = Flow.nV cs ∧
        c.reg rFREE = F + 5 * fL g cs k ∧ ZeroFrom c.mem (c.reg rFREE) ∧ Flow.GA g cs k c ∧
        Arr c.mem (bV g) (Flow.verts cs) ∧ SameOn (· < F) m₀ c.mem)
      (PairIds.CR * (fL g cs k + 1)) :=
    HTB.of_forall fun c₁ ⟨hIn, hga, hF, hV, hsame⟩ => by
      refine (PairIds.rankIds_spec (S := S) (Flow.verts cs) c₁ (by rw [hF, hl]; omega)).mono
        (fun c hc => ⟨hc ▸ hIn, hc⟩) (fun c ⟨hO, hfr⟩ => ?_) (by rw [hl])
      refine ⟨hO.id, by rw [hO.rid, hF], hO.ne, by rw [hO.free, hF, hl]; ring, hO.zero,
        ga_of_frame hcs hfr rankIds_wregs' hga,
        hV.of_below hO.same (by rw [hF, length_verts' g cs k hcs]; omega), ?_⟩
      exact hsame.trans (hO.same.mono fun a (ha : a < F) => show a < _ by rw [hF]; omega)
  -- the results
  have h3 : HTB S vBack
      (fun c => Arr c.mem (c.reg PairIds.rID) (PairIds.eids (Flow.verts cs)) ∧
        c.reg PairIds.rID = F + 3 * fL g cs k ∧ c.reg PairIds.rNE = Flow.nV cs ∧
        c.reg rFREE = F + 5 * fL g cs k ∧ ZeroFrom c.mem (c.reg rFREE) ∧ Flow.GA g cs k c ∧
        Arr c.mem (bV g) (Flow.verts cs) ∧ SameOn (· < F) m₀ c.mem)
      (VidsPost g cs k F m₀) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨hid, hrid, hne, hF, hZ, hga, hV, hsame⟩ => by
        have hAg : Agree [rT, fID, ZeroCost.gN] c (run vBack c) :=
          agree_run (by decide) rfl rfl (by decide) c
        refine ⟨hvb, (show RegIndep [rT, fID, ZeroCost.gN] (Flow.GA g cs k) by
            indep [Flow.gA_iff]).indep _ _ hAg hga,
          by simp +decide [vBack, run_mov, hrid, fIDb], by simp +decide [vBack, run_mov, hne],
          (hAg.reg _ (by decide)).trans hF, ?_, by rw [hAg.mem]; exact hV,
          by rw [hAg.mem, hAg.reg _ (by decide)]; exact hZ, by rw [hAg.mem]; exact hsame⟩
        rw [hAg.mem, fIDb, ← hrid]; exact hid
  exact h0.seq (h1.seq (h2.seq h3))

end STACS2027.Runtimes.EnumeratedSort
