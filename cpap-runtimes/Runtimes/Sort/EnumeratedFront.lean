module

public import Runtimes.Sort.EnumeratedPairs
import Mathlib.Tactic

/-!
# Sorting enumerated cycle lists

The complete sorting front end for an arbitrary list of simple cycles.
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

@[mk_iff] structure FrontPost (g : Graph) (cs : List Cycle) (k F : ℕ) (c : Config) : Prop where
  ga : Flow.GA g cs k c
  reid : c.reg ZeroCost.gEID = fEID g cs k F
  rcnt : c.reg ZeroCost.gCNT = fCNT g cs k F
  rne : c.reg ZeroCost.gNE = (Flow.eList cs).length
  rfree : c.reg rFREE = fEnd g cs k F
  vb : bV g + fL g cs k ≤ F
  mverts : Arr c.mem (bV g) (Flow.verts cs)
  meid : Tab c.mem (fEID g cs k F) (fL g cs k) (Flow.eid cs)
  mcnt : Tab c.mem (fCNT g cs k F) (fL g cs k) (Flow.cntF cs (fL g cs k))
  mzero : ZeroFrom c.mem (fEnd g cs k F)

theorem fEids_spec (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) (F : ℕ) (m₀ : ℕ → ℕ) (hS : fEnd g cs k F ≤ S) :
    HTB S (.seq PairIds.pairIds idsBack) (PairsPost g cs k F m₀)
      (fun c => FrontPost g cs k F c ∧ SameOn (· < F) m₀ c.mem)
      (PairIds.CI * (Flow.nV cs + fL g cs k + 1) + 6) := by
  have hpi : HTB S PairIds.pairIds (PairsPost g cs k F m₀)
      (fun c => Flow.GA g cs k c ∧ c.reg PairIds.rID = fEID g cs k F ∧ c.reg PairIds.rCT = fCNT g cs k F ∧
        c.reg PairIds.rNE = (Flow.eList cs).length ∧ c.reg rFREE = fEnd g cs k F ∧
        bV g + fL g cs k ≤ F ∧ Arr c.mem (bV g) (Flow.verts cs) ∧
        Tab c.mem (fEID g cs k F) (fL g cs k) (Flow.eid cs) ∧
        Tab c.mem (fCNT g cs k F) (fL g cs k) (Flow.cntF cs (fL g cs k)) ∧ ZeroFrom c.mem (fEnd g cs k F) ∧
        SameOn (· < F) m₀ c.mem)
      (PairIds.CI * (Flow.nV cs + fL g cs k + 1)) := by
    refine HTB.of_forall fun c₀ hP => ?_
    have hF := hP.rfree
    have hS' : PairIds.idsEnd (Flow.nV cs) (Flow.prs cs).length (c₀.reg rFREE) ≤ S := by
      rw [(Flow.length_prs hcs), hF, ← fEnd_eq g cs k hcs F]; exact hS
    refine (PairIds.pairIds_spec (Flow.prs cs) (Flow.nV cs) Flow.prs_below c₀ hS').mono
      (fun c hc => ⟨hc ▸ hP.pin, hc⟩) (fun c ⟨hO, hfr⟩ => ?_) (by rw [(Flow.length_prs hcs)])
    have hrid := hO.rid
    have hrct := hO.rct
    have hfree := hO.free
    have hsame := hO.same
    rw [(Flow.length_prs hcs), hF] at hrid hrct hfree
    rw [hF] at hsame
    have hfree' : c.reg rFREE = fEnd g cs k F := hfree.trans (fEnd_eq g cs k hcs F).symm
    have hvb := hP.vb
    have e4 : fPI g cs k F = F + 7 * fL g cs k := rfl
    refine ⟨ga_of_frame hcs hfr (fun r hr => by
        rcases PairIds.pairIds_wregs r hr with rfl | rfl | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inl (by decide)
        · exact Or.inl (by decide)
        · omega
        · have e : PairIds.rLD = 124 := rfl
          omega) hP.ga, hrid, hrct, ?_, hfree', hvb,
      hP.mverts.of_below hsame (by rw [length_verts' g cs k hcs]; omega), ?_, ?_,
      by rw [← hfree']; exact hO.zero, hP.same.trans (hsame.mono fun a (ha : a < F) =>
        show a < _ by omega)⟩
    · rw [hO.ne, Flow.length_eraseDups_prs]
    · have := hO.id
      rw [hrid, (Flow.eids_prs hcs)] at this
      exact tab_of_arr_map_range this
    · have := hO.ct
      rw [hrct, (Flow.length_prs hcs)] at this
      exact this.congr_fun fun e _ => Flow.count_eids_prs hcs e
  have hb : HTB S idsBack
      (fun c => Flow.GA g cs k c ∧ c.reg PairIds.rID = fEID g cs k F ∧ c.reg PairIds.rCT = fCNT g cs k F ∧
        c.reg PairIds.rNE = (Flow.eList cs).length ∧ c.reg rFREE = fEnd g cs k F ∧
        bV g + fL g cs k ≤ F ∧ Arr c.mem (bV g) (Flow.verts cs) ∧
        Tab c.mem (fEID g cs k F) (fL g cs k) (Flow.eid cs) ∧
        Tab c.mem (fCNT g cs k F) (fL g cs k) (Flow.cntF cs (fL g cs k)) ∧ ZeroFrom c.mem (fEnd g cs k F) ∧
        SameOn (· < F) m₀ c.mem)
      (fun c => FrontPost g cs k F c ∧ SameOn (· < F) m₀ c.mem) 6 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨hga, hid, hct, hne, hF, hvb, hV, hE, hC, hZ, hsame⟩ => by
        have hAg : Agree [rT, ZeroCost.gEID, ZeroCost.gCNT, ZeroCost.gNE] c (run idsBack c) :=
          agree_run (by decide) rfl rfl (by decide) c
        refine ⟨⟨(show RegIndep [rT, ZeroCost.gEID, ZeroCost.gCNT, ZeroCost.gNE] (Flow.GA g cs k) by
            indep [Flow.gA_iff]).indep c _ hAg hga,
          ?_, ?_, ?_, (hAg.reg _ (by decide)).trans hF, hvb, by rw [hAg.mem]; exact hV,
          by rw [hAg.mem]; exact hE, by rw [hAg.mem]; exact hC, by rw [hAg.mem]; exact hZ⟩,
          by rw [hAg.mem]; exact hsame⟩
        · simp +decide [idsBack, run_mov, hid]
        · simp +decide [idsBack, run_mov, hct]
        · simp +decide [idsBack, run_mov, hne]
  exact hpi.seq hb

theorem t_le_fL (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) : (cs).length ≤ fL g cs k := by
  rcases Nat.eq_zero_or_pos (cs).length with h | h
  · rw [h]; exact Nat.zero_le _
  · have hk := (hcs cs[0] (List.getElem_mem (by omega))).1
    exact Nat.le_mul_of_pos_left _ (by omega)

def CF : ℕ := CM + 400

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

theorem front_writes : writes front = false := by
  simp only [front, fSort, fVids, vArgs, vBack, fPairs, fEids, writes_seq, msort_writes,
    PairIds.pairIds_writes, PairIds.rankIds_writes, Bool.or_false, Bool.false_or]
  decide

theorem front_spec (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) (c₀ : Config) (hIn : FrontIn g cs k c₀)
    (hS : fEnd g cs k (c₀.reg rFREE) ≤ S) :
    HTB S front (· = c₀)
      (fun c => FrontPost g cs k (c₀.reg rFREE) c ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c.out = c₀.out)
      (CF * (fL g cs k * (Nat.clog 2 (fL g cs k) + 1) + 1)) := by
  have hf := ffits g cs k hcs (c₀.reg rFREE) hS
  have h1 := fSort_spec (S := S) g cs k hcs c₀ hIn (by omega)
  have h2 := fVids_spec (S := S) g cs k hcs (c₀.reg rFREE) c₀.mem (by unfold fPU at hf; omega)
  have h3 := fPairs_spec (S := S) g cs k hcs (c₀.reg rFREE) c₀.mem hf.2.2.2.2.1
  have h4 := fEids_spec (S := S) g cs k hcs (c₀.reg rFREE) c₀.mem hS
  have h := (h1.post fun _ h => h.1).seq (h2.seq ((h3.seq h4).assoc))
  refine (h.withFrame c₀).mono (fun c hc => ⟨hc, hc⟩) (fun c ⟨⟨hP, hsame⟩, hfr⟩ =>
    ⟨hP, hsame, hfr.out front_writes⟩) ?_
  have ht := t_le_fL g cs k hcs
  have hn : Flow.nV cs ≤ fL g cs k := (Flow.nV_le hcs)
  have e1 : (cs).length * (k * 36 + 4 + 4) = 36 * fL g cs k + 8 * (cs).length := by
    simp only [fL]; ring
  have e2 : CF * (fL g cs k * (Nat.clog 2 (fL g cs k) + 1) + 1) =
      CM * (fL g cs k * (Nat.clog 2 (fL g cs k) + 1) + 1) + 400 * (fL g cs k * Nat.clog 2 (fL g cs k)) +
        400 * fL g cs k + 400 := by
    generalize Nat.clog 2 (fL g cs k) = P
    generalize fL g cs k = Y
    rw [show CF = CM + 400 from rfl]
    ring
  have e3 : PairIds.CI = 96 := rfl
  have e4 : PairIds.CR = 34 := rfl
  rw [e1, e2, e3, e4]
  have := Nat.zero_le (fL g cs k * Nat.clog 2 (fL g cs k))
  omega

end STACS2027.Runtimes.EnumeratedSort
