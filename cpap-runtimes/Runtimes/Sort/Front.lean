module

public import Runtimes.Sort.FrontPairs
import Mathlib.Tactic

/-!
# The sorting front end: edge identifiers without label-indexed memory

**`front_spec`**: on an input in Corollary 5's format, after Corollary 5's phase 1 (`FrontIn`:
the registers `GA g k`, the `kt` vertices of the cycles at `bV g` below the free address `F`,
zero memory from `F` on), the program `front` (`FrontProg.lean`) computes **the data of
Corollary 5's `EdgesPost`** — `EID[q] = eidOf g k q` for every occurrence `q < kt`,
`CNT[e] = cntF g k (kt) e`, `NE = |edgesOnCycles g k|` in the registers `ZeroCost.gEID`,
`ZeroCost.gCNT`, `ZeroCost.gNE` —
in the layout `fEID`, `fCNT`, `fEnd` above `F` (`FrontPost`), within
`CF · (kt (⌈log₂ kt⌉ + 1) + 1)` steps, accessing only the addresses below any
`S ≥ fEnd g k F` (`fEnd_le`: `≤ F + 15 kt + 1`), leaving the memory below `F` unchanged, without
output — with no memory indexed by a vertex label (the labels are sorted by the stable merge
sort `msort` and only compared). The vertex identifiers are Corollary 5's dictionary ids
(`eids_verts`: both are first-appearance ids), so the edge identifiers are exactly Corollary
5's.

Phase 4 (`fEids_spec`): outerplanar package's `PairIds.pairIds` on the ordered id pairs `prs g k`, as in
Corollary 5's `stepEdges` (`eids_prs`, `count_eids_prs`, `length_eraseDups_prs`).

Theorem 4 and the convex QP machine (Lemma 16 of the paper) use this front end in place of Corollary
5's dictionary phases.
-/

@[expose] public section

namespace STACS2027.Runtimes.Sort

open STACS2027 STACS2027.RAM STACS2027.RAM.R0 STACS2027.Runtimes.ZeroCost
open scoped List

variable {S : ℕ}

/-- The state after the front end (`F`: the free address at its start): the data of
Corollary 5's `EdgesPost` in the layout of the front end. -/
@[mk_iff] structure FrontPost (g : Graph) (k F : ℕ) (c : Config) : Prop where
  ga : GA g k c
  reid : c.reg ZeroCost.gEID = fEID g k F
  rcnt : c.reg ZeroCost.gCNT = fCNT g k F
  rne : c.reg ZeroCost.gNE = (edgesOnCycles g k).length
  rfree : c.reg rFREE = fEnd g k F
  vb : bV g + fL g k ≤ F
  mverts : Arr c.mem (bV g) (verts g k)
  meid : Tab c.mem (fEID g k F) (fL g k) (eidOf g k)
  mcnt : Tab c.mem (fCNT g k F) (fL g k) (cntF g k (fL g k))
  mzero : ZeroFrom c.mem (fEnd g k F)

/-! ### Phase 4: the edge identifiers -/

/-- **Phase 4**: `PairIds.pairIds` on the ordered id pairs (B2), then the results in
Corollary 5's registers `ZeroCost.gEID`, `ZeroCost.gCNT`, `ZeroCost.gNE`. -/
theorem fEids_spec (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (hS : fEnd g k F ≤ S) :
    HTB S (.seq PairIds.pairIds idsBack) (PairsPost g k F m₀)
      (fun c => FrontPost g k F c ∧ SameOn (· < F) m₀ c.mem)
      (PairIds.CI * (nV g k + fL g k + 1) + 6) := by
  have hpi : HTB S PairIds.pairIds (PairsPost g k F m₀)
      (fun c => GA g k c ∧ c.reg PairIds.rID = fEID g k F ∧ c.reg PairIds.rCT = fCNT g k F ∧
        c.reg PairIds.rNE = (edgesOnCycles g k).length ∧ c.reg rFREE = fEnd g k F ∧
        bV g + fL g k ≤ F ∧ Arr c.mem (bV g) (verts g k) ∧
        Tab c.mem (fEID g k F) (fL g k) (eidOf g k) ∧
        Tab c.mem (fCNT g k F) (fL g k) (cntF g k (fL g k)) ∧ ZeroFrom c.mem (fEnd g k F) ∧
        SameOn (· < F) m₀ c.mem)
      (PairIds.CI * (nV g k + fL g k + 1)) := by
    refine HTB.of_forall fun c₀ hP => ?_
    have hF := hP.rfree
    have hS' : PairIds.idsEnd (nV g k) (prs g k).length (c₀.reg rFREE) ≤ S := by
      rw [length_prs, hF, ← fEnd_eq]; exact hS
    refine (PairIds.pairIds_spec (prs g k) (nV g k) prs_below c₀ hS').mono
      (fun c hc => ⟨hc ▸ hP.pin, hc⟩) (fun c ⟨hO, hfr⟩ => ?_) (by rw [length_prs])
    have hrid := hO.rid
    have hrct := hO.rct
    have hfree := hO.free
    have hsame := hO.same
    rw [length_prs, hF] at hrid hrct hfree
    rw [hF] at hsame
    have hfree' : c.reg rFREE = fEnd g k F := hfree.trans (fEnd_eq g k F).symm
    have hvb := hP.vb
    have e4 : fPI g k F = F + 7 * fL g k := rfl
    refine ⟨ga_of_frame hfr (fun r hr => by
        rcases PairIds.pairIds_wregs r hr with rfl | rfl | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inl (by decide)
        · exact Or.inl (by decide)
        · omega
        · have e : PairIds.rLD = 124 := rfl
          omega) hP.ga, hrid, hrct, ?_, hfree', hvb,
      hP.mverts.of_below hsame (by rw [length_verts']; omega), ?_, ?_,
      by rw [← hfree']; exact hO.zero, hP.same.trans (hsame.mono fun a (ha : a < F) =>
        show a < _ by omega)⟩
    · rw [hO.ne, length_eraseDups_prs]
    · have := hO.id
      rw [hrid, eids_prs] at this
      exact tab_of_arr_map_range this
    · have := hO.ct
      rw [hrct, length_prs] at this
      exact this.congr_fun fun e _ => count_eids_prs e
  have hb : HTB S idsBack
      (fun c => GA g k c ∧ c.reg PairIds.rID = fEID g k F ∧ c.reg PairIds.rCT = fCNT g k F ∧
        c.reg PairIds.rNE = (edgesOnCycles g k).length ∧ c.reg rFREE = fEnd g k F ∧
        bV g + fL g k ≤ F ∧ Arr c.mem (bV g) (verts g k) ∧
        Tab c.mem (fEID g k F) (fL g k) (eidOf g k) ∧
        Tab c.mem (fCNT g k F) (fL g k) (cntF g k (fL g k)) ∧ ZeroFrom c.mem (fEnd g k F) ∧
        SameOn (· < F) m₀ c.mem)
      (fun c => FrontPost g k F c ∧ SameOn (· < F) m₀ c.mem) 6 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨hga, hid, hct, hne, hF, hvb, hV, hE, hC, hZ, hsame⟩ => by
        have hAg : Agree [rT, ZeroCost.gEID, ZeroCost.gCNT, ZeroCost.gNE] c (run idsBack c) :=
          agree_run (by decide) rfl rfl (by decide) c
        refine ⟨⟨(show RegIndep [rT, ZeroCost.gEID, ZeroCost.gCNT, ZeroCost.gNE] (GA g k) by
            indep [gA_iff]).indep c _ hAg hga,
          ?_, ?_, ?_, (hAg.reg _ (by decide)).trans hF, hvb, by rw [hAg.mem]; exact hV,
          by rw [hAg.mem]; exact hE, by rw [hAg.mem]; exact hC, by rw [hAg.mem]; exact hZ⟩,
          by rw [hAg.mem]; exact hsame⟩
        · simp +decide [idsBack, run_mov, hid]
        · simp +decide [idsBack, run_mov, hct]
        · simp +decide [idsBack, run_mov, hne]
  exact hpi.seq hb

/-! ### The whole front end -/

theorem t_le_fL (g : Graph) (k : ℕ) : (cycles g k).length ≤ fL g k := by
  rcases Nat.eq_zero_or_pos (cycles g k).length with h | h
  · rw [h]; exact Nat.zero_le _
  · have hk := (kCycle_isCycle g (k := k) (i := 0) h).1
    exact Nat.le_mul_of_pos_left _ (by omega)

/-- The constant of the running time of the front end. -/
def CF : ℕ := CM + 400

/-- The registers written by the front end: `rT`, `rFREE`, outerplanar package's `100–137`, Corollary
5's `257–262` and scratch `270–291`, the sort's `800–816`, and `fID = 830`. -/
theorem front_wregs : ∀ r ∈ wregs front, r = rT ∨ r = rFREE ∨ (100 ≤ r ∧ r < 138) ∨
    (257 ≤ r ∧ r < 263) ∨ (270 ≤ r ∧ r < 292) ∨ (800 ≤ r ∧ r < 817) ∨ r = fID := by
  intro r hr
  simp only [front, fEids, wregs_seq, List.mem_append] at hr
  rcases hr with h | h | h | h | h | h
  · have : ∀ r ∈ wregs fSort, r = rT ∨ r = rFREE ∨ (800 ≤ r ∧ r < 817) := by decide
    rcases this r h with h | h | h <;> simp_all
  · simp only [fVids, wregs_seq, List.mem_append] at h
    rcases h with h | h | h | h
    · have : ∀ r ∈ wregs vArgs, r = rT ∨ (100 ≤ r ∧ r < 138) := by decide
      rcases this r h with h | h <;> simp_all
    · have := PairIds.sortedLeads_wregs r h
      have e : PairIds.rLD = 124 := rfl
      omega
    · have := PairIds.rankIds_wregs r h
      have e : PairIds.rID = 125 := rfl
      omega
    · have : ∀ r ∈ wregs vBack, r = rT ∨ r = fID ∨ (257 ≤ r ∧ r < 263) := by decide
      rcases this r h with h | h | h <;> simp_all
  · have : ∀ r ∈ wregs fPairs, r = rT ∨ r = rFREE ∨ (257 ≤ r ∧ r < 263) ∨ (270 ≤ r ∧ r < 292) := by
      decide
    rcases this r h with h | h | h | h <;> simp_all
  · have : ∀ r ∈ wregs idsArgs, r = rT ∨ (100 ≤ r ∧ r < 138) := by decide
    rcases this r h with h | h <;> simp_all
  · rcases PairIds.pairIds_wregs r h with h | h | h | h
    · simp_all
    · simp_all
    · omega
    · have e : PairIds.rLD = 124 := rfl
      omega
  · have : ∀ r ∈ wregs idsBack, r = rT ∨ (257 ≤ r ∧ r < 263) := by decide
    rcases this r h with h | h <;> simp_all

/-- The front end does not write output. -/
theorem front_writes : writes front = false := by
  simp only [front, fSort, fVids, vArgs, vBack, fPairs, fEids, writes_seq, msort_writes,
    PairIds.pairIds_writes, PairIds.rankIds_writes, Bool.or_false, Bool.false_or]
  decide

/-- **The sorting front end.** From Corollary 5's phase 1 (`FrontIn`, free address `F`), the
front end reaches `FrontPost g k F` — the edge identifiers `EID[q] = eidOf g k q`, the counts
`CNT`, `NE = |edgesOnCycles g k|` (Corollary 5's `EdgesPost` data) — within
`CF · (kt (⌈log₂ kt⌉ + 1) + 1)` steps, accessing only the addresses below any `S ≥ fEnd g k F`
(`≤ F + 15 kt + 1`), leaving the memory below `F` and the output unchanged; no memory is indexed
by a vertex label. -/
theorem front_spec (g : Graph) (k : ℕ) (c₀ : Config) (hIn : FrontIn g k c₀)
    (hS : fEnd g k (c₀.reg rFREE) ≤ S) :
    HTB S front (· = c₀)
      (fun c => FrontPost g k (c₀.reg rFREE) c ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c.out = c₀.out)
      (CF * (fL g k * (Nat.clog 2 (fL g k) + 1) + 1)) := by
  have hf := ffits g k (c₀.reg rFREE) hS
  have h1 := fSort_spec (S := S) g k c₀ hIn (by omega)
  have h2 := fVids_spec (S := S) g k (c₀.reg rFREE) c₀.mem (by unfold fPU at hf; omega)
  have h3 := fPairs_spec (S := S) g k (c₀.reg rFREE) c₀.mem hf.2.2.2.2.1
  have h4 := fEids_spec (S := S) g k (c₀.reg rFREE) c₀.mem hS
  have h := (h1.post fun _ h => h.1).seq (h2.seq ((h3.seq h4).assoc))
  refine (h.withFrame c₀).mono (fun c hc => ⟨hc, hc⟩) (fun c ⟨⟨hP, hsame⟩, hfr⟩ =>
    ⟨hP, hsame, hfr.out front_writes⟩) ?_
  have ht := t_le_fL g k
  have hn : nV g k ≤ fL g k := nV_le
  have e1 : (cycles g k).length * (k * 36 + 4 + 4) = 36 * fL g k + 8 * (cycles g k).length := by
    simp only [fL]; ring
  have e2 : CF * (fL g k * (Nat.clog 2 (fL g k) + 1) + 1) =
      CM * (fL g k * (Nat.clog 2 (fL g k) + 1) + 1) + 400 * (fL g k * Nat.clog 2 (fL g k)) +
        400 * fL g k + 400 := by
    generalize Nat.clog 2 (fL g k) = P
    generalize fL g k = Y
    rw [show CF = CM + 400 from rfl]
    ring
  have e3 : PairIds.CI = 96 := rfl
  have e4 : PairIds.CR = 34 := rfl
  rw [e1, e2, e3, e4]
  have := Nat.zero_le (fL g k * Nat.clog 2 (fL g k))
  omega


end STACS2027.Runtimes.Sort
